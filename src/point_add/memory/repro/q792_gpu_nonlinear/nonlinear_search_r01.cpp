#define CL_TARGET_OPENCL_VERSION 120
#include <CL/cl.h>
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <sstream>
#include <string>
#include <vector>
#include <omp.h>
using U=uint64_t;using Clock=std::chrono::steady_clock;
constexpr unsigned NC=262144,STRIDE=26;
constexpr U BIT[6]={0xaaaaaaaaaaaaaaaaULL,0xccccccccccccccccULL,0xf0f0f0f0f0f0f0f0ULL,0xff00ff00ff00ff00ULL,0xffff0000ffff0000ULL,0xffffffff00000000ULL};
struct Job{U truth;unsigned n,k;};
static_assert(sizeof(Job)==16);
struct Plan{uint16_t len,pol;std::array<uint16_t,24> gate{};};
static_assert(sizeof(Plan)==2*STRIDE);
U rnd(U&s){s+=0x9e3779b97f4a7c15ULL;U z=s;z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL;z=(z^(z>>27))*0x94d049bb133111ebULL;return z^(z>>31);}
U limit(unsigned n){return n==6?~U(0):((U(1)<<(1u<<n))-1);}

std::vector<Plan> plans(){
 std::vector<Plan>p(3*NC);
 for(unsigned n=4;n<=6;n++)for(unsigned c=0;c<NC;c++){
  auto&v=p[(n-4)*NC+c];U seed=0xb50c79220260912ULL^U(n)*0x1245ab123ULL^U(c)*0xf394765ULL;
  v.pol=c<(1u<<n)?c:rnd(seed)&((1u<<n)-1);v.len=c<(1u<<n)?0:1+(c%16);
  for(unsigned i=0;i<v.len;i++){
   unsigned a=rnd(seed)%n,b=rnd(seed)%(n-1);if(b>=a)b++;
   if(c%4!=0&&rnd(seed)%3==0){unsigned e;do{e=rnd(seed)%n;}while(e==a||e==b);if(a>e)std::swap(a,e);v.gate[i]=512|(a<<6)|(e<<3)|b;}
   else v.gate[i]=(a<<3)|b;
  }
 }return p;
}
U transformed(const Job&j,const Plan&p){U t=j.truth;
 for(unsigned i=0;i<p.len;i++){unsigned g=p.gate[i],d=g&7;U mask=g&512?BIT[(g>>6)&7]&BIT[(g>>3)&7]:BIT[g>>3];U z=(t^(t>>(1u<<d)))&mask&~BIT[d];t^=z^(z<<(1u<<d));}
 for(unsigned b=0;b<j.n;b++)if(p.pol>>b&1){unsigned sh=1u<<b;t=((t&~BIT[b])<<sh)|((t&BIT[b])>>sh);}return t&limit(j.n);
}
unsigned tcost(unsigned c){return c<2?0:c==2?1:4*c-8;}
using Cubes=std::vector<std::pair<unsigned,unsigned>>;
std::vector<uint8_t>choices;std::vector<unsigned>costs;
struct Cube{unsigned mask,value;uint16_t truth;};std::array<Cube,81>cube;
unsigned index4(unsigned k){return k==0?0:k==1?1:k==2?3:6+(4*k-12)/2;}
void load_tables(const char*path){std::ifstream f(path,std::ios::binary);assert(f);choices.assign(std::istreambuf_iterator<char>(f),{});assert(choices.size()==3997696);
 for(unsigned i=0;i<81;i++){unsigned v=i,m=0,b=0;for(unsigned d=0;d<4;d++){unsigned tr=v%3;v/=3;if(tr){m|=1<<d;if(tr==2)b|=1<<d;}}unsigned t=0;for(unsigned x=0;x<16;x++)if((x&m)==b)t|=1<<x;cube[i]={m,b,uint16_t(t)};}
 costs.resize(23*65536);
 for(unsigned k=0;k<=22;k++)for(unsigned t=0;t<65536;t++){unsigned at=t,T=0,N=0,steps=0;while(at){auto c=cube[choices[index4(k)*65536+at]];unsigned n=k+__builtin_popcount(c.mask),v=tcost(n);T+=v;N+=(n<=2?1:v)+2*__builtin_popcount(c.mask^c.value);at^=c.truth;assert(++steps<64);}assert(T<65536&&N<65536);costs[k*65536+t]=(T<<16)|N;}
}
unsigned esop(unsigned n,U t,unsigned k){if(n==4)return costs[k*65536+unsigned(t)];unsigned half=1u<<(n-1);U mask=(U(1)<<half)-1;U a=t&mask,b=t>>half;unsigned z=esop(n-1,a^b,k+1);return std::min({esop(n-1,a,k)+z,esop(n-1,b,k)+z,esop(n-1,a,k+1)+esop(n-1,b,k+1)});}
U anf(unsigned n,U t){for(unsigned b=0;b<n;b++)t^=(t<<(1u<<b))&BIT[b];return t&limit(n);}
unsigned anfcost(unsigned n,U t,unsigned k){U a=anf(n,t);unsigned T=0,N=0;while(a){unsigned m=__builtin_ctzll(a);a&=a-1;unsigned c=k+__builtin_popcount(m),v=tcost(c);T+=v;N+=c<=2?1:v;}return(T<<16)|N;}
unsigned framecost(const Plan&p){unsigned T=0;for(unsigned i=0;i<p.len;i++)T+=bool(p.gate[i]&512)*2;return(T<<16)|unsigned(2*p.len+2*__builtin_popcount(p.pol));}
unsigned score(const Job&j,const Plan&p){U t=transformed(j,p);return framecost(p)+std::min(esop(j.n,t,j.k),anfcost(j.n,t,j.k));}
Cubes solution(unsigned n,U t,unsigned k){if(n==4){Cubes c;while(t){auto a=cube[choices[index4(k)*65536+unsigned(t)]];c.emplace_back(a.mask,a.value);t^=a.truth;}return c;}
 unsigned half=1u<<(n-1);U mask=(U(1)<<half)-1,a=t&mask,b=t>>half;unsigned z=esop(n-1,a^b,k+1);std::array<unsigned,3>cost{esop(n-1,a,k)+z,esop(n-1,b,k)+z,esop(n-1,a,k+1)+esop(n-1,b,k+1)};unsigned mode=std::min_element(cost.begin(),cost.end())-cost.begin();Cubes out=solution(n-1,mode==1?b:a,k+(mode==2));if(mode==2)for(auto&c:out)c.first|=1u<<(n-1);auto other=solution(n-1,mode==2?b:a^b,k+1);for(auto c:other){c.first|=1u<<(n-1);if(mode!=1)c.second|=1u<<(n-1);out.push_back(c);}return out;
}
Cubes selected(const Job&j,const Plan&p){U t=transformed(j,p);if(anfcost(j.n,t,j.k)<esop(j.n,t,j.k)){U a=anf(j.n,t);Cubes cs;while(a){unsigned m=__builtin_ctzll(a);a&=a-1;cs.emplace_back(m,m);}return cs;}return solution(j.n,t,j.k);}
void exact(const Job&j,const Plan&p){auto cs=selected(j,p);for(unsigned x=0;x<(1u<<j.n);x++){unsigned y=x;for(unsigned i=0;i<p.len;i++){unsigned g=p.gate[i],bit=g&512?((y>>((g>>6)&7))&(y>>((g>>3)&7))&1):((y>>(g>>3))&1);y^=bit<<(g&7);}y^=p.pol;bool v=false;for(auto[m,b]:cs)v^=(y&m)==b;assert(v==bool(j.truth>>x&1));}}

const char*kernel=R"CLC(
constant ulong BIT[6]={0xaaaaaaaaaaaaaaaaUL,0xccccccccccccccccUL,0xf0f0f0f0f0f0f0f0UL,0xff00ff00ff00ff00UL,0xffff0000ffff0000UL,0xffffffff00000000UL};
typedef struct{ulong truth;uint n,k;} Job;
uint rd(global const ushort*p,uint r,uint f){
#if LAYOUT==1
 return p[f*(3*262144)+r];
#else
 return p[r*26+f];
#endif
}
uint s4(global const uint*cost,uint t,uint k){return cost[k*65536+t];}
uint s5(global const uint*cost,uint t,uint k){uint a=t&65535,b=t>>16,z=s4(cost,a^b,k+1);return min(min(s4(cost,a,k)+z,s4(cost,b,k)+z),s4(cost,a,k+1)+s4(cost,b,k+1));}
uint s6(global const uint*cost,ulong t,uint k){uint a=t,b=t>>32,z=s5(cost,a^b,k+1);return min(min(s5(cost,a,k)+z,s5(cost,b,k)+z),s5(cost,a,k+1)+s5(cost,b,k+1));}
kernel void assess(global const Job*jobs,global const ushort*plans,global uint*out,ulong start,ulong count,global const uint*cost){
 ulong lid=get_global_id(0);if(lid>=count)return;ulong gid=start+lid;uint ci=gid%262144;Job j=jobs[gid/262144];uint row=(j.n-4)*262144+ci;uint len=rd(plans,row,0),pol=rd(plans,row,1);ulong a=j.truth;uint ft=0;
 for(uint i=0;i<len;i++){uint g=rd(plans,row,2+i),d=g&7;ulong mask=g&512?BIT[(g>>6)&7]&BIT[(g>>3)&7]:BIT[g>>3];ft+=g&512?2:0;ulong z=(a^(a>>(1u<<d)))&mask&~BIT[d];a^=z^(z<<(1u<<d));}
 for(uint b=0;b<j.n;b++)if(pol>>b&1){uint sh=1u<<b;a=((a&~BIT[b])<<sh)|((a&BIT[b])>>sh);}if(j.n<6)a&=(1UL<<(1u<<j.n))-1;
 uint ec=j.n==4?s4(cost,a,j.k):j.n==5?s5(cost,a,j.k):s6(cost,a,j.k);
 for(uint b=0;b<j.n;b++)a^=(a<<(1u<<b))&BIT[b];if(j.n<6)a&=(1UL<<(1u<<j.n))-1;
 uint T=0,N=0;for(uint m=0;m<(1u<<j.n);m++)if(a>>m&1){uint c=j.k+popcount(m),v=c<2?0:c==2?1:4*c-8;T+=v;N+=c<=2?1:v;}out[lid]=((ft<<16)|(2*len+2*popcount(pol)))+min(ec,(T<<16)|N);
}
)CLC";
void ck(cl_int x,const char*w){if(x!=CL_SUCCESS){std::cerr<<"OPENCL_ERROR "<<w<<" "<<x<<std::endl;std::exit(2);}}
std::string info(cl_device_id d,cl_device_info key){size_t n=0;ck(clGetDeviceInfo(d,key,0,nullptr,&n),"info size");std::string v(n,'\0');ck(clGetDeviceInfo(d,key,n,v.data(),nullptr),"info");return v.c_str();}
struct Device{
 cl_device_id d;cl_context ctx;cl_command_queue q;std::array<cl_program,2>pr;std::array<cl_kernel,2>kn;std::array<cl_mem,2>pl;cl_mem jobs=nullptr,out=nullptr,ct=nullptr;size_t capacity=0;cl_event ev=nullptr;double lastms=0;unsigned index;
 Device(cl_device_id id,unsigned ix,const std::vector<Plan>&p):d(id),index(ix){cl_int e;cl_device_type type;ck(clGetDeviceInfo(d,CL_DEVICE_TYPE,sizeof(type),&type,nullptr),"type");assert(type==CL_DEVICE_TYPE_GPU);std::string name=info(d,CL_DEVICE_NAME);assert(name.find("B50")!=std::string::npos);std::cout<<"DEVICE "<<index<<" "<<name<<" driver="<<info(d,CL_DRIVER_VERSION)<<std::endl;ctx=clCreateContext(nullptr,1,&d,nullptr,nullptr,&e);ck(e,"context");q=clCreateCommandQueue(ctx,d,CL_QUEUE_PROFILING_ENABLE,&e);ck(e,"queue");
  std::vector<uint16_t>soa(p.size()*STRIDE);auto raw=reinterpret_cast<const uint16_t*>(p.data());for(size_t r=0;r<p.size();r++)for(size_t f=0;f<STRIDE;f++)soa[f*p.size()+r]=raw[r*STRIDE+f];
  for(unsigned l=0;l<2;l++){pr[l]=clCreateProgramWithSource(ctx,1,&kernel,nullptr,&e);ck(e,"program");std::string opts="-cl-std=CL1.2 -DLAYOUT="+std::to_string(l);e=clBuildProgram(pr[l],1,&d,opts.c_str(),nullptr,nullptr);if(e){size_t n;clGetProgramBuildInfo(pr[l],d,CL_PROGRAM_BUILD_LOG,0,nullptr,&n);std::string log(n,' ');clGetProgramBuildInfo(pr[l],d,CL_PROGRAM_BUILD_LOG,n,log.data(),nullptr);std::cerr<<log<<std::endl;}ck(e,"build");kn[l]=clCreateKernel(pr[l],"assess",&e);ck(e,"kernel");pl[l]=clCreateBuffer(ctx,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,p.size()*STRIDE*2,l?static_cast<void*>(soa.data()):const_cast<Plan*>(p.data()),&e);ck(e,"plans");}
 }
 void load(const std::vector<Job>&j,size_t count){cl_int ce;ct=clCreateBuffer(ctx,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,costs.size()*sizeof(unsigned),costs.data(),&ce);ck(ce,"costs");if(jobs)clReleaseMemObject(jobs);cl_int e;jobs=clCreateBuffer(ctx,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,j.size()*sizeof(Job),const_cast<Job*>(j.data()),&e);ck(e,"jobs");if(count>capacity){if(out)clReleaseMemObject(out);out=clCreateBuffer(ctx,CL_MEM_WRITE_ONLY,count*sizeof(unsigned),nullptr,&e);ck(e,"output");capacity=count;}}
 void launch(unsigned layout,size_t wg,U start,U count){auto k=kn[layout];ck(clSetKernelArg(k,0,sizeof(jobs),&jobs),"arg0");ck(clSetKernelArg(k,1,sizeof(pl[layout]),&pl[layout]),"arg1");ck(clSetKernelArg(k,2,sizeof(out),&out),"arg2");ck(clSetKernelArg(k,3,sizeof(start),&start),"arg3");ck(clSetKernelArg(k,4,sizeof(count),&count),"arg4");ck(clSetKernelArg(k,5,sizeof(ct),&ct),"arg5");size_t global=(count+wg-1)/wg*wg;ck(clEnqueueNDRangeKernel(q,k,1,nullptr,&global,&wg,0,nullptr,&ev),"enqueue");ck(clFlush(q),"flush");}
 void read(unsigned*dest,size_t count){ck(clEnqueueReadBuffer(q,out,CL_TRUE,0,count*sizeof(unsigned),dest,0,nullptr,nullptr),"read");cl_ulong a,b;ck(clGetEventProfilingInfo(ev,CL_PROFILING_COMMAND_START,sizeof(a),&a,nullptr),"profile start");ck(clGetEventProfilingInfo(ev,CL_PROFILING_COMMAND_END,sizeof(b),&b,nullptr),"profile end");lastms=(b-a)/1e6;clReleaseEvent(ev);ev=nullptr;}
};
double run(std::vector<Device*>&d,unsigned layout,size_t wg,unsigned cards,const std::vector<Job>&j,std::vector<unsigned>&out){size_t total=j.size()*NC;out.resize(total);auto start=Clock::now();size_t half=cards==2?total/2:total;d[0]->launch(layout,wg,0,half);if(cards==2)d[1]->launch(layout,wg,half,total-half);d[0]->read(out.data(),half);if(cards==2)d[1]->read(out.data()+half,total-half);return std::chrono::duration<double,std::milli>(Clock::now()-start).count();}

int main(int argc,char**argv){assert(argc==5);std::string prefix=argv[1];load_tables(argv[3]);auto p=plans();cl_uint np=0;ck(clGetPlatformIDs(0,nullptr,&np),"platforms");std::vector<cl_platform_id>platforms(np);ck(clGetPlatformIDs(np,platforms.data(),nullptr),"platform ids");std::vector<cl_device_id>ids;for(auto platform:platforms){cl_uint n=0;cl_int e=clGetDeviceIDs(platform,CL_DEVICE_TYPE_GPU,0,nullptr,&n);if(e==CL_DEVICE_NOT_FOUND)continue;ck(e,"device count");std::vector<cl_device_id>v(n);ck(clGetDeviceIDs(platform,CL_DEVICE_TYPE_GPU,n,v.data(),nullptr),"devices");for(auto id:v)if(info(id,CL_DEVICE_NAME).find("B50")!=std::string::npos)ids.push_back(id);}assert(ids.size()==2&&ids[0]!=ids[1]);Device a(ids[0],0,p),b(ids[1],1,p);std::vector<Device*>d{&a,&b};std::vector<Job>jobs;std::ifstream in(argv[2]),cfg(argv[4]);assert(in&&cfg);std::string truth;unsigned n,k;while(in>>n>>k>>truth){assert(n>=4&&n<=6&&k<=20);jobs.push_back({std::stoull(truth,nullptr,16),n,k});}assert(!jobs.empty());unsigned layout;size_t wg;cfg>>layout>>wg;assert(layout==1&&wg==256);for(auto dev:d)dev->load(jobs,jobs.size()*NC);std::vector<unsigned>out;double wall=run(d,layout,wg,2,jobs,out);std::cout<<"GPU_EVALUATED count="<<out.size()<<" wall_ms="<<wall<<" gpu0_ms="<<a.lastms<<" gpu1_ms="<<b.lastms<<" devices=2"<<std::endl;
 unsigned reference_checks=0;std::ofstream result(prefix+"-best.tsv");assert(result);result<<"n\tk\ttruth\tcandidate\tT\tN\tdepth\tpolarity\tgates\tcubes\n";
 for(size_t i=0;i<jobs.size();i++){auto&j=jobs[i];for(unsigned c=0;c<NC;c+=4093){assert(out[i*NC+c]==score(j,p[(j.n-4)*NC+c]));reference_checks++;}std::vector<unsigned>order(NC);std::iota(order.begin(),order.end(),0);std::partial_sort(order.begin(),order.begin()+8,order.end(),[&](unsigned x,unsigned y){return std::pair(out[i*NC+x],x)<std::pair(out[i*NC+y],y);});for(unsigned z=0;z<8;z++){unsigned c=order[z],v=out[i*NC+c];auto&pp=p[(j.n-4)*NC+c];assert(v==score(j,pp));exact(j,pp);reference_checks++;result<<j.n<<'\t'<<j.k<<'\t'<<std::hex<<j.truth<<std::dec<<'\t'<<c<<'\t'<<(v>>16)<<'\t'<<(v&65535)<<'\t'<<unsigned(pp.len)<<'\t'<<unsigned(pp.pol)<<'\t';for(unsigned g=0;g<pp.len;g++){if(g)result<<',';result<<pp.gate[g];}result<<'\t';bool first=true;for(auto[m,b]:selected(j,pp)){if(!first)result<<',';first=false;result<<m<<':'<<b;}result<<'\n';}}
 std::cout<<"GPU_NONLINEAR_ESOP_SEARCH_PASS jobs="<<jobs.size()<<" candidates="<<out.size()<<" CPU_reference_checks="<<reference_checks<<" selected_all_truths_exact=true both_B50=true"<<std::endl;
}
