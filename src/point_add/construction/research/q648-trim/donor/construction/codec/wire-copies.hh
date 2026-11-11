#pragma once
// Rolling signatures ignore a uniform translation of any of the three wire
// fields. Missing operands and operation kinds remain part of the signature.
// Every candidate is checked against the complete original records.
struct CopyMatch {
    size_t length=0;
    uint32_t source=0;
    bool reverse=false;
    std::array<uint16_t,3> shift{};
};
class WireCopies {
    static constexpr unsigned table_bits=19,way=6,k=3;
    static constexpr uint32_t nil=0xffffffffu;
    const std::vector<Row>& a;
    std::vector<uint32_t> fwd,back,exactForward,exactBackward;
    std::vector<std::array<uint32_t,way>> recent;
    std::vector<std::array<uint32_t,2>> exact;
    size_t inserted=0;
    static uint32_t mix(uint32_t z) {
        z^=z>>16;z*=0x7feb352du;z^=z>>15;z*=0x846ca68bu;return z^(z>>16);
    }
    static uint32_t edge(Row p,Row q) {
        uint32_t h=uint32_t(lane(p,0))*31+lane(q,0);
        for(unsigned j=1;j<=3;j++){
            const unsigned x=lane(p,j), y=lane(q,j);
            const unsigned d=x==65535||y==65535 ? 65536 + unsigned(x==65535)*2 + unsigned(y==65535) : uint16_t(y-x);
            h=h*0x1000193u+d;
        }
        return mix(h);
    }
    void put(uint32_t hash,uint32_t v){
        auto& s=recent[hash>>(32-table_bits)];
        for(unsigned j=way-1;j>0;j--)s[j]=s[j-1];s[0]=v;
    }
    void putExact(uint32_t hash,uint32_t v){
        auto& bucket=exact[hash>>(32-table_bits)];
        bucket[1]=bucket[0];bucket[0]=v;
    }
    void extend(size_t i,size_t j,bool rev,CopyMatch& best) {
        const size_t limit=rev?std::min(a.size()-i,j+1):a.size()-i;
        if(limit<=best.length)return;
        std::array<uint16_t,3> shift{};unsigned set=0;size_t len=0;
        for(;len<limit;len++){
            const Row y=a[i+len], x=a[rev?j-len:j+len];
            if(lane(x,0)!=lane(y,0)) break;
            bool pass=true;
            for(unsigned c=0;c<3;c++){
                const unsigned prev=lane(x,c+1), now=lane(y,c+1);
                if(prev==65535||now==65535){if(prev!=now)pass=false;continue;}
                const uint16_t d=uint16_t(now-prev);const unsigned bit=1u<<c;
                if(set&bit){if(shift[c]!=d)pass=false;}
                else {set|=bit;shift[c]=d;}
            }
            if(!pass)break;
        }
        if(len>best.length){best.length=len;best.source=j;best.reverse=rev;best.shift=shift;}
    }
  public:
    explicit WireCopies(const std::vector<Row>& rows):a(rows),fwd(a.size()),back(a.size()),exactForward(a.size()),
        exactBackward(a.size()),recent(1u<<table_bits),exact(1u<<table_bits) {
        for(auto& x:recent)x.fill(nil);
        for(auto& x:exact)x.fill(nil);
        if(a.size()<k+1)return;
        std::vector<uint32_t> u(a.size()),v(a.size()),value(a.size());
        for(size_t i=0;i<a.size();i++)value[i]=mix(uint32_t(a[i])*0x85ebca6bu+uint32_t(a[i]>>32));
        for(size_t i=0;i+1<a.size();i++){u[i]=edge(a[i],a[i+1]);v[i+1]=edge(a[i+1],a[i]);}
        for(size_t i=0;i+k<a.size();i++){
            fwd[i]=mix(u[i]*0x0019660du*0x0019660du+u[i+1]*0x0019660du+u[i+2]);
            size_t j=i+k;back[j]=mix(v[j]*0x0019660du*0x0019660du+v[j-1]*0x0019660du+v[j-2]);
            exactForward[i]=mix(((value[i]*31+value[i+1])*31+value[i+2])*31+value[j]);
            exactBackward[j]=mix(((value[j]*31+value[j-1])*31+value[j-2])*31+value[i]);
        }
    }
    CopyMatch match(size_t i,size_t skipIfAtLeast) {
        while(inserted<i){
            size_t j=inserted++;
            if(j>=k){put(back[j],uint32_t(j)<<1|1);putExact(exactBackward[j],uint32_t(j)<<1|1);}
            if(j+k<a.size()){put(fwd[j],uint32_t(j)<<1);putExact(exactForward[j],uint32_t(j)<<1);}
        }
        CopyMatch result;
        if(i+k>=a.size())return result;
        for(uint32_t h:exact[exactForward[i]>>(32-table_bits)]){
            if(h==nil)break;
            const size_t j=h>>1;const bool rev=h&1;
            if((rev?exactBackward[j]:exactForward[j])!=exactForward[i])continue;
            const size_t max=rev?std::min(a.size()-i,j+1):a.size()-i;size_t count=0;
            while(count<max&&a[i+count]==a[rev?j-count:j+count])++count;
            if(count>result.length){result.length=count;result.source=j;result.reverse=rev;result.shift={};}
        }
        if(result.length>=512||skipIfAtLeast>=96)return result;
        const auto& hits=recent[fwd[i]>>(32-table_bits)];
        for(uint32_t h:hits){
            if(h==nil)break;
            const size_t j=h>>1;const bool rev=h&1;
            if((rev?back[j]:fwd[j])!=fwd[i])continue;
            extend(i,j,rev,result);
            if(result.length>=512)break;
        }
        return result;
    }
};
