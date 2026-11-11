#pragma once
struct RemapMatch {size_t length=0,source=0;bool reverse=false;std::vector<std::pair<uint16_t,uint16_t>> segments;};
class RemappedCopies {
    const std::vector<Row>& rows;
    static constexpr unsigned bits=18,k=6,ways=6;
    static constexpr uint32_t none=0xffffffffu;
    std::vector<uint32_t> fwd,rev;std::vector<std::array<uint32_t,ways>> slots;
    std::array<uint32_t,65536> stamp{};std::array<uint16_t,65536> shifted{};
    std::vector<uint16_t> touched;uint32_t epoch=0;size_t pending=0;
    static uint32_t mix(uint32_t z){z^=z>>16;z*=0x85ebca6bu;z^=z>>13;return z*0xc2b2ae35u;}
    static uint32_t edge(Row p,Row q){
        uint32_t h=lane(p,0)*23+lane(q,0);
        for(unsigned j=1;j<=3;j++){
            const int y=lane(q,j);unsigned rel=0;
            if(y==65535)rel=31;
            else for(unsigned a=1;a<=3;a++){
                const int x=lane(p,a),d=y-x;if(d==0)rel|=1u<<(a-1);
                if(x!=65535&&(d==1||d==-1))rel|=1u<<(a+2);
            }
            h=h*67+rel;
        }return mix(h);
    }
    void add(uint32_t key,uint32_t value){
        auto& p=slots[key>>(32-bits)];
        if(p[0]==none||((value*0x9e3779b9u)>>28)==0)p[ways-1]=p[ways-2];
        for(unsigned j=ways-2;j>0;j--)p[j]=p[j-1];p[0]=value;
    }
    void candidate(size_t i,size_t j,bool backwards,size_t threshold,RemapMatch& best){
        if(++epoch==0){stamp.fill(0);epoch=1;}touched.clear();
        size_t len=0,max=rows.size()-i;if(backwards)max=std::min(max,j+1);if(max<threshold)return;
        for(;len<max;len++){
            Row x=rows[backwards?j-len:j+len],y=rows[i+len];if(lane(x,0)!=lane(y,0))break;
            size_t old=touched.size();bool good=true;
            for(unsigned c=1;c<=3;c++){
                uint16_t from=lane(x,c),to=lane(y,c);
                if(from==65535||to==65535){if(from!=to)good=false;continue;}
                uint16_t d=uint16_t(to-from);
                if(stamp[from]==epoch){if(shifted[from]!=d)good=false;}
                else {stamp[from]=epoch;shifted[from]=d;touched.push_back(from);}
            }if(!good){touched.resize(old);break;}
        }
        if(len<threshold||len<=best.length||touched.empty())return;
        std::sort(touched.begin(),touched.end());std::vector<std::pair<uint16_t,uint16_t>> pieces;
        for(uint16_t x:touched){const auto d=shifted[x];if(pieces.empty()||pieces.back().second!=d)pieces.emplace_back(pieces.empty()?0:x,d);}
        if(pieces.size()>128||len<threshold+pieces.size()*6)return;
        best.length=len;best.source=j;best.reverse=backwards;best.segments=std::move(pieces);
    }
public:
    explicit RemappedCopies(const std::vector<Row>& a):rows(a),fwd(a.size()),rev(a.size()),slots(1u<<bits){
        for(auto& s:slots)s.fill(none);if(a.size()<=k)return;
        std::vector<uint32_t> e(a.size()),b(a.size());
        for(size_t i=0;i+1<a.size();i++){e[i]=edge(a[i],a[i+1]);b[i+1]=edge(a[i+1],a[i]);}
        for(size_t i=0;i+k<a.size();i++){
            uint32_t x=0,y=0;for(unsigned z=0;z<k;z++){x=x*0x19660du+e[i+z];y=y*0x19660du+b[i+k-z];}
            fwd[i]=mix(x);rev[i+k]=mix(y);
        }
    }
    RemapMatch match(size_t i,size_t existing){
        while(pending<i){const size_t j=pending++;if(j>=k)add(rev[j],uint32_t(j)<<1|1);if(j+k<rows.size())add(fwd[j],uint32_t(j)<<1);}
        RemapMatch best;if(i+k>=rows.size()||existing>=12000)return best;
        const size_t limit=std::max<size_t>(24,existing+8);
        for(uint32_t which:slots[fwd[i]>>(32-bits)]){
            if(which==none)break;const bool back=which&1;const size_t j=which>>1;if((back?rev[j]:fwd[j])!=fwd[i])continue;
            candidate(i,j,back,limit,best);if(best.length>=4096)break;
        }return best;
    }
};
