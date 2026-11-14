// Stream input: four little-endian uint16 words per operation.
// Output is an uncompressed, lossless intermediate suited to zstd.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

using Bytes = std::vector<uint8_t>;
using Row = uint64_t;
static constexpr unsigned block_size = 1u << 20;
static constexpr unsigned periods[] = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,20,24,28,32,40,48,56,64,80,96,112,128,160,192,224,256};
static constexpr uint64_t even_lanes = 0x0000ffff0000ffffULL;

static bool affine(Row current, Row last, Row older) {
    // Compare independent sums modulo 2^16 with one guard lane between words.
    const Row even = (current & even_lanes) + (older & even_lanes) - 2*(last & even_lanes);
    const Row odd = ((current>>16) & even_lanes) + ((older>>16) & even_lanes) - 2*((last>>16) & even_lanes);
    static constexpr Row guard = 0x0002000000020000ULL;
    return (((even + guard) | (odd + guard)) & even_lanes) == 0;
}
static void varint(Bytes& b, size_t value) {
    while(value>=128){b.push_back(static_cast<uint8_t>(value)|128);value>>=7;}
    b.push_back(static_cast<uint8_t>(value));
}
static void writeBytes(const uint8_t *p,size_t n) {
    if(n && std::fwrite(p,1,n,stdout)!=n) throw std::runtime_error("writing compressed intermediate");
}
static void word32(uint32_t x) {
    const uint8_t b[]={uint8_t(x),uint8_t(x>>8),uint8_t(x>>16),uint8_t(x>>24)};
    writeBytes(b,4);
}
static Row fromLittle(const uint8_t* x) {
    Row value=0;
    for(unsigned i=0;i<8;i++)value|=Row(x[i])<<(8*i);
    return value;
}
static uint16_t lane(Row r,unsigned k){return uint16_t(r>>(16*k));}
static bool valid(Row r) {
    constexpr uint16_t no=65535;
    const uint16_t k=lane(r,0),a=lane(r,1),b=lane(r,2),c=lane(r,3);
    switch(k){
        case 1:case 15:return a!=no&&b==no&&c==no;
        case 2:case 18:return a!=no&&b!=no&&c==no;
        case 3:case 4:case 5:case 6:case 7:case 12:return a!=no&&c==no;
        case 8:case 9:return a!=no&&b!=no&&a!=b;
        case 13:return a!=no&&b!=no&&c!=no&&a!=b&&a!=c&&b!=c;
        case 16:return a==no&&b==no&&c==no;
        default:return false;
    }
}
#include "wire-copies.hh"
#include "wire-map.hh"

struct Stats{uint64_t rows=0,literals=0,runs=0,blocks=0,intermediate=8;};
static void block(const std::vector<Row>& rows,Stats& stats) {
    Bytes commands,kinds;
    std::array<Bytes,6> coords;
    uint16_t last[19][3]={};
    const size_t n=rows.size();
    WireCopies copies(rows);
    RemappedCopies maps(rows);
    for(size_t i=0;i<n;) {
        size_t best=0; unsigned periodCode=0;
        for(unsigned pi=0;pi<sizeof(periods)/sizeof(periods[0]);pi++){
            const size_t p=periods[pi];
            if(i<2*p)break;
            if(!affine(rows[i],rows[i-p],rows[i-2*p]))continue;
            size_t end=i+1;
            while(end<n && affine(rows[end],rows[end-p],rows[end-2*p]))++end;
            if(end-i>best){best=end-i;periodCode=pi+1;}
            if(best>=96)break;
        }
        const auto cp=copies.match(i,best);
        const auto mapped=maps.match(i,std::max(best,cp.length));
        if(mapped.length) {
            commands.push_back(mapped.reverse?81:80);
            varint(commands,i-mapped.source-1);varint(commands,mapped.length-4);
            varint(commands,mapped.segments.size());
            unsigned start=0;
            for(unsigned j=0;j<mapped.segments.size();j++){
                const auto s=mapped.segments[j];
                if(j)varint(commands,s.first-start);
                const uint16_t d=s.second;varint(commands,uint16_t((d<<1)^(0u-(d>>15))));
                start=s.first;
            }
            i+=mapped.length;stats.runs++;continue;
        }
        unsigned shiftMask=0;
        for(unsigned j=0;j<3;j++)if(cp.shift[j])shiftMask|=1u<<j;
        if(cp.length>=std::max<size_t>(shiftMask?15:8,best+(shiftMask?8:4))) {
            commands.push_back(uint8_t(64+8*unsigned(cp.reverse)+shiftMask));
            varint(commands,i-cp.source-1);varint(commands,cp.length-4);
            for(unsigned j=0;j<3;j++)if(shiftMask&(1u<<j)){
                const uint16_t d=cp.shift[j];
                varint(commands,uint16_t((d<<1)^(0u-(d>>15))));
            }
            i+=cp.length;stats.runs++;continue;
        }
        if(best>=3) {
            commands.push_back(uint8_t(periodCode));varint(commands,best-3);
            i+=best;stats.runs++;continue;
        }
        commands.push_back(0);const Row value=rows[i++];
        const unsigned kind=lane(value,0);
        if(kind>18)throw std::runtime_error("invalid literal operation kind");
        kinds.push_back(uint8_t(kind));
        for(unsigned j=0;j<3;j++){
            const uint16_t x=lane(value,j+1), d=uint16_t(x-last[kind][j]);
            last[kind][j]=x;
            const uint16_t z=uint16_t((d<<1) ^ (0u-(d>>15)));
            coords[2*j].push_back(uint8_t(z));coords[2*j+1].push_back(uint8_t(z>>8));
        }
    }
    word32(uint32_t(n));word32(uint32_t(commands.size()));word32(uint32_t(kinds.size()));
    writeBytes(commands.data(),commands.size());writeBytes(kinds.data(),kinds.size());
    for(const auto& x:coords)writeBytes(x.data(),x.size());
    stats.rows+=n;stats.literals+=kinds.size();stats.blocks++;
    stats.intermediate+=12+commands.size()+7*kinds.size();
}
int main(int argc,char**argv) {
    try {
        if(argc!=2){std::fprintf(stderr,"usage: encode COUNT_FILE <trace.u16le >trace.gir\n");return 2;}
        const uint8_t magic[]={'G','A','T','E','I','R','2','\n'};writeBytes(magic,8);
        Stats total;
        std::vector<uint8_t> raw(size_t(block_size)*8);
        std::vector<Row> rows;rows.reserve(block_size);
        while(true) {
            size_t got=0;
            while(got<raw.size()){
                const size_t n=std::fread(raw.data()+got,1,raw.size()-got,stdin);got+=n;
                if(n==0){if(std::ferror(stdin))throw std::runtime_error("reading input");break;}
            }
            if(got%8)throw std::runtime_error("partial eight-byte record");
            if(!got)break;
            rows.clear();for(size_t i=0;i<got;i+=8){
                const auto r=fromLittle(raw.data()+i);
                if(!valid(r))throw std::runtime_error("invalid operation at literal record "+std::to_string(total.rows+i/8));
                rows.push_back(r);
            }
            block(rows,total);
        }
        word32(0);
        if(std::fflush(stdout)!=0)throw std::runtime_error("flushing intermediate");
        FILE *count=std::fopen(argv[1],"wb");
        if(!count)throw std::runtime_error("opening count file");
        std::fprintf(count,"%llu\n",(unsigned long long)total.rows);
        if(std::fclose(count))throw std::runtime_error("writing count file");
        std::fprintf(stderr,"records=%llu blocks=%llu literal=%llu runs=%llu intermediate_bytes=%llu\n",
          (unsigned long long)total.rows,(unsigned long long)total.blocks,(unsigned long long)total.literals,
          (unsigned long long)total.runs,(unsigned long long)(total.intermediate+4));
    } catch(const std::exception& e){std::fprintf(stderr,"encoder: %s\n",e.what());return 1;}
}
