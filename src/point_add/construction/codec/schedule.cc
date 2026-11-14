// Global semantic dictionary. Input is a regular raw trace and a six-column
// boundary sidecar. The literal rows go to stdout; the expansion plan is separate.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <limits>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

using Bytes=std::vector<uint8_t>;
using Words=std::array<uint16_t,4>;
static void var(Bytes& b,uint64_t x){while(x>=128){b.push_back(uint8_t(x)|128);x>>=7;}b.push_back(uint8_t(x));}
static void u64le(Bytes& b,uint64_t x){for(unsigned j=0;j<8;j++)b.push_back(uint8_t(x>>(8*j)));}
static void put(FILE* f,const void* p,size_t n){if(n&&fwrite(p,1,n,f)!=n)throw std::runtime_error("schedule output");}
static int space(uint16_t k,unsigned j){
    // 0 quantum, 1 classical and 2 register. Unused fields remain literal.
    switch(k){
      case 1:return j==0?2:-1;case 2:return j==0?2:j==1?0:-1;case 18:return j==0?2:j==1?1:-1;
      case 3:case 4:case 5:return j<2?1:-1;
      case 6:case 7:case 12:return j==0?0:j==1?1:-1;
      case 8:case 9:return j<2?0:1;case 13:return 0;case 15:return j==0?1:-1;case 16:return -1;
      default:throw std::runtime_error("unsupported raw kind "+std::to_string(k));
    }
}
struct Mapped{
    const uint8_t* data=nullptr;size_t bytes=0,count=0;
    explicit Mapped(const char* p){int fd=open(p,O_RDONLY);if(fd<0)throw std::runtime_error("open trace");
        struct stat st{};if(fstat(fd,&st)||!S_ISREG(st.st_mode)||st.st_size<0||st.st_size%8)throw std::runtime_error("trace must be regular and complete");
        bytes=size_t(st.st_size);count=bytes/8;
        if(bytes){void* m=mmap(nullptr,bytes,PROT_READ,MAP_PRIVATE,fd,0);if(m==MAP_FAILED)throw std::runtime_error("mmap trace");data=static_cast<const uint8_t*>(m);}
        close(fd);}
    Words operator[](size_t i)const{const uint8_t* b=data+8*i;return{uint16_t(b[0]|(b[1]<<8)),uint16_t(b[2]|(b[3]<<8)),uint16_t(b[4]|(b[5]<<8)),uint16_t(b[6]|(b[7]<<8))};}
    ~Mapped(){if(bytes)munmap(const_cast<uint8_t*>(data),bytes);}
};
struct Span{size_t a,b;uint32_t name;size_t size()const{return b-a;}};
struct Candidate{size_t a,n;bool backwards;};
struct Entry{size_t start,length,source;uint32_t map;bool reversed,literal;};
class Canon {
    const Mapped& rows;
    std::vector<uint32_t> stamp,inverseStamp;std::vector<uint16_t> values;
    uint32_t epoch=0;
    void fresh(){if(++epoch==0){std::fill(stamp.begin(),stamp.end(),0);std::fill(inverseStamp.begin(),inverseStamp.end(),0);epoch=1;}}
public:
    explicit Canon(const Mapped& r):rows(r),stamp(3*65536),inverseStamp(3*65536),values(3*65536){}
    uint64_t key(const Span& s,bool reverse){
        fresh();uint32_t next[3]={0,0,0};uint64_t h=0xcbf29ce484222325ULL^s.size();
        auto add=[&](uint32_t x){h=(h^x)*0x100000001b3ULL;};
        auto sample=[&](size_t i){Words row=rows[reverse?s.b-1-i:s.a+i];add(row[0]);for(unsigned j=0;j<3;j++){
            uint16_t x=row[j+1];const int ns=space(row[0],j);if(ns<0||x==65535){add(0x40000u+x);continue;}
            const unsigned k=(unsigned(ns)<<16)|x;if(stamp[k]!=epoch){stamp[k]=epoch;values[k]=uint16_t(next[ns]++);}
            add((unsigned(ns)<<16)|values[k]);
        }};
        if(s.size()<=128){for(size_t i=0;i<s.size();i++)sample(i);}
        else for(size_t part=0;part<16;part++){const size_t pos=(s.size()-8)*part/15;for(size_t j=0;j<8;j++)sample(pos+j);}
        return h;
    }
    bool bind(const Candidate& old,const Span& now,Bytes& code){
        if(old.n!=now.size()||old.a+old.n>now.a)return false;
        fresh();std::array<std::vector<uint16_t>,3> used;
        for(size_t i=0;i<old.n;i++){
            const auto a=rows[old.backwards?old.a+old.n-1-i:old.a+i],b=rows[now.a+i];if(a[0]!=b[0])return false;
            for(unsigned j=0;j<3;j++){
                const int ns=space(a[0],j);const auto x=a[j+1],y=b[j+1];
                if(ns<0||x==65535||y==65535){if(x!=y)return false;continue;}
                const unsigned u=(unsigned(ns)<<16)|x,v=(unsigned(ns)<<16)|y;
                if(stamp[u]==epoch){if(values[u]!=y)return false;}
                else{if(inverseStamp[v]==epoch)return false;stamp[u]=inverseStamp[v]=epoch;values[u]=y;used[ns].push_back(x);}
            }
        }
        code.clear();
        for(unsigned ns=0;ns<3;ns++){
            auto& us=used[ns];std::sort(us.begin(),us.end());
            struct Piece{uint16_t x,b;bool minus;};std::vector<Piece> pcs;
            auto image=[&](uint16_t x){return values[(ns<<16)|x];};
            bool modified=false;for(auto x:us)if(x!=image(x)){modified=true;break;}
            for(size_t i=0;modified&&i<us.size();){
                const uint16_t x=us[i],y=image(x);const uint16_t off=uint16_t(y-x),sum=uint16_t(y+x);
                const bool neg=i+1<us.size()&&uint16_t(image(us[i+1])-us[i+1])!=off&&uint16_t(image(us[i+1])+us[i+1])==sum;
                pcs.push_back({uint16_t(i?x:0),neg?sum:off,neg});i++;
                while(i<us.size() && (neg?uint16_t(image(us[i])+us[i])==sum:uint16_t(image(us[i])-us[i])==off))i++;
            }
            var(code,pcs.size());unsigned prev=0;
            for(size_t i=0;i<pcs.size();i++){const auto p=pcs[i];if(i)var(code,p.x-prev);prev=p.x;
                const uint16_t z=uint16_t((p.b<<1)^(0u-(p.b>>15)));var(code,(uint32_t(z)<<1)|p.minus);}
        }
        return true;
    }
};
int main(int argc,char**argv){
  try{
    if(argc!=5){std::fprintf(stderr,"usage: schedule TRACE TSV PLAN REPORT >LITERAL_RAW\n");return 2;}
    Mapped rows(argv[1]);std::ifstream f(argv[2]);if(!f)throw std::runtime_error("open sidecar");
    size_t min=512;if(const char* x=std::getenv("GIR_SPAN_MIN"))min=std::max<size_t>(1,std::stoull(x));
    std::vector<Span> spans;std::unordered_map<std::string,uint32_t> ids;std::vector<std::string> names;
    std::string line;while(std::getline(f,line)){if(line.empty()||line[0]=='#')continue;
        std::array<std::string,6> fields;size_t p=0;for(unsigned j=0;j<6;j++){size_t q=line.find('\t',p);if(j<5&&q==std::string::npos)throw std::runtime_error("invalid sidecar fields");fields[j]=line.substr(p,q-p);p=q==std::string::npos?line.size():q+1;}
        if(fields[0]=="id")continue;const size_t a=std::stoull(fields[2]),b=std::stoull(fields[3]);
        if(b<a||b>rows.count)throw std::runtime_error("span exceeds trace");if(b-a<min)continue;
        auto z=ids.emplace(fields[4],uint32_t(names.size()));if(z.second)names.push_back(fields[4]);spans.push_back({a,b,z.first->second});}
    std::sort(spans.begin(),spans.end(),[](const Span& a,const Span& b){return a.a<b.a||(a.a==b.a&&a.b>b.b);});
    std::vector<uint64_t> nameUse(names.size());
    Canon canon(rows);std::unordered_map<uint64_t,std::vector<Candidate>> dict;std::unordered_map<std::string,uint32_t> mapIds;
    std::vector<Bytes> maps;std::vector<Entry> plan;size_t at=0,literal=0,nRef=0;uint64_t probes=0;
    auto gap=[&](size_t end){if(end>at){plan.push_back({at,end-at,0,0,false,true});literal+=end-at;at=end;}};
    for(const auto& s:spans){
        if(s.a<at)continue;
        const uint64_t key=canon.key(s,false);
        bool found=false;Bytes code;
        auto it=dict.find(key);if(it!=dict.end()){
            for(const auto& c:it->second){++probes;if(!canon.bind(c,s,code))continue;
                if(code.size()>std::max<size_t>(64,s.size()/6))continue;
                const std::string ms(reinterpret_cast<const char*>(code.data()),code.size());
                auto id=mapIds.emplace(ms,uint32_t(maps.size()));if(id.second)maps.push_back(code);
                gap(s.a);plan.push_back({s.a,s.size(),c.backwards?c.a+c.n-1:c.a,id.first->second,c.backwards,false});
                at=s.b;nRef++;nameUse[s.name]+=s.size();found=true;break;}
        }
        if(found)continue;
        auto keep=[&](uint64_t hash,bool back){auto& v=dict[hash];if(v.size()<8)v.push_back({s.a,s.size(),back});};
        keep(key,false);keep(canon.key(s,true),true);
    }
    gap(rows.count);Bytes raw={'G','I','R','P','L','A','N','1'};u64le(raw,rows.count);u64le(raw,literal);
    var(raw,maps.size());for(const auto& mp:maps)raw.insert(raw.end(),mp.begin(),mp.end());
    var(raw,plan.size());for(const auto& op:plan){raw.push_back(op.literal?0:op.reversed?2:1);var(raw,op.length);
        if(op.literal){put(stdout,rows.data+8*op.start,8*op.length);}
        else {var(raw,op.start-op.source);var(raw,op.map);}}
    if(std::fflush(stdout)!=0)throw std::runtime_error("flushing literal stream");
    FILE* out=std::fopen(argv[3],"wb");if(!out)throw std::runtime_error("open plan");put(out,raw.data(),raw.size());if(std::fclose(out))throw std::runtime_error("close plan");
    std::ofstream report(argv[4]);if(!report)throw std::runtime_error("open report");
    report<<"total "<<rows.count<<"\nliteral "<<literal<<"\ncopied "<<(rows.count-literal)<<"\nrefs "<<nRef<<"\nmaps "<<maps.size()<<"\nspans "<<spans.size()<<"\nverified_candidates "<<probes<<"\nplan_bytes "<<raw.size()<<"\n";
    for(size_t i=0;i<names.size();i++)if(nameUse[i])report<<"copied_stage "<<nameUse[i]<<" "<<names[i]<<"\n";
    std::fprintf(stderr,"sidecar coverage %llu/%llu records via %llu checked references, %llu wire maps\n",
        (unsigned long long)(rows.count-literal),(unsigned long long)rows.count,(unsigned long long)nRef,(unsigned long long)maps.size());
  }catch(const std::exception& e){std::fprintf(stderr,"schedule: %s\n",e.what());return 1;}
}
