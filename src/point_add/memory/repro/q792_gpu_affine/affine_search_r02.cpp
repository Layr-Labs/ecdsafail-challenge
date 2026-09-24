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
constexpr unsigned NC=65536,STRIDE=18;
constexpr U BIT[6]={0xaaaaaaaaaaaaaaaaULL,0xccccccccccccccccULL,0xf0f0f0f0f0f0f0f0ULL,0xff00ff00ff00ff00ULL,0xffff0000ffff0000ULL,0xffffffff00000000ULL};
struct Job{U truth;unsigned n,k;};
static_assert(sizeof(Job)==16);
struct Plan{uint8_t len,pol;std::array<uint8_t,16> gate{};};
static_assert(sizeof(Plan)==STRIDE);
U rnd(U&s){s+=0x9e3779b97f4a7c15ULL;U z=s;z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL;z=(z^(z>>27))*0x94d049bb133111ebULL;return z^(z>>31);}
U limit(unsigned n){return n==6?~U(0):((U(1)<<(1u<<n))-1);}
std::vector<Plan> plans(){std::vector<Plan>p(3*NC);for(unsigned n=4;n<=6;n++)for(unsigned c=0;c<NC;c++){auto&v=p[(n-4)*NC+c];U s=0xb50a79220260912ULL^U(n)*0x1245ab123ULL^U(c)*0xf394765ULL;v.pol=c<(1u<<n)?c:rnd(s)&((1u<<n)-1);v.len=c<(1u<<n)?0:4*(1+(c%4));for(unsigned i=0;i<v.len;i++){unsigned a=rnd(s)%n,b=rnd(s)%(n-1);if(b>=a)b++;v.gate[i]=a*8+b;}}return p;}
U anf(const Job&j,const Plan&p){U t=j.truth;for(unsigned i=0;i<p.len;i++){unsigned c=p.gate[i]>>3,d=p.gate[i]&7;U x=(t^(t>>(1u<<d)))&(BIT[c]&~BIT[d]);t^=x^(x<<(1u<<d));}for(unsigned b=0;b<j.n;b++)if(p.pol>>b&1){unsigned sh=1u<<b;t=((t&~BIT[b])<<sh)|((t&BIT[b])>>sh);}for(unsigned b=0;b<j.n;b++)t^=(t<<(1u<<b))&BIT[b];return t&limit(j.n);}
unsigned tcost(unsigned c){return c<2?0:c==2?1:4*c-8;}
unsigned score(const Job&j,const Plan&p){U a=anf(j,p);unsigned t=0,n=2*p.len+2*__builtin_popcount(p.pol);while(a){unsigned m=__builtin_ctzll(a);a&=a-1;unsigned c=j.k+__builtin_popcount(m),v=tcost(c);t+=v;n+=c<=2?1:v;}assert(t<65536&&n<65536);return(t<<16)|n;}
void exact(const Job&j,const Plan&p){U a=anf(j,p);for(unsigned x=0;x<(1u<<j.n);x++){unsigned y=x;for(unsigned i=0;i<p.len;i++)y^=((y>>(p.gate[i]>>3))&1)<<(p.gate[i]&7);y^=p.pol;bool v=false;for(unsigned m=0;m<(1u<<j.n);m++)if((a>>m&1)&&((y&m)==m))v=!v;assert(v==bool(j.truth>>x&1));} }
const char*kernel=R"CLC(
constant ulong BIT[6]={0xaaaaaaaaaaaaaaaaUL,0xccccccccccccccccUL,0xf0f0f0f0f0f0f0f0UL,0xff00ff00ff00ff00UL,0xffff0000ffff0000UL,0xffffffff00000000UL};
typedef struct{ulong truth;uint n,k;} Job;
uint rd(global const uchar*plans,uint row,uint field){
#if LAYOUT==1
 return plans[field*(3*65536)+row];
#else
 return plans[row*18+field];
#endif
}
kernel void assess(global const Job*jobs,global const uchar*plans,global uint*out,ulong start,ulong count){
 ulong localid=get_global_id(0);if(localid>=count)return;ulong gid=start+localid;uint ci=gid%65536;Job j=jobs[gid/65536];uint row=(j.n-4)*65536+ci;uint len=rd(plans,row,0),pol=rd(plans,row,1);ulong a=j.truth;
 for(uint i=0;i<len;i++){uint z=rd(plans,row,2+i),c=z>>3,d=z&7;ulong delta=(a^(a>>(1u<<d)))&(BIT[c]&~BIT[d]);a^=delta^(delta<<(1u<<d));}
 for(uint b=0;b<j.n;b++)if(pol>>b&1){uint sh=1u<<b;a=((a&~BIT[b])<<sh)|((a&BIT[b])>>sh);}
 for(uint b=0;b<j.n;b++)a^=(a<<(1u<<b))&BIT[b];if(j.n<6)a&=((1UL<<(1u<<j.n))-1);
 uint t=0,n=2*len+2*popcount(pol);for(uint m=0;m<(1u<<j.n);m++)if(a>>m&1){uint c=j.k+popcount(m);uint v=c<2?0:c==2?1:4*c-8;t+=v;n+=c<=2?1:v;}out[localid]=(t<<16)|n;
}
)CLC";
void ck(cl_int x,const char*w){if(x!=CL_SUCCESS){std::cerr<<"OPENCL_ERROR "<<w<<" "<<x<<std::endl;std::exit(2);}}
std::string info(cl_device_id d,cl_device_info key){size_t n=0;ck(clGetDeviceInfo(d,key,0,nullptr,&n),"info size");std::string v(n,'\0');ck(clGetDeviceInfo(d,key,n,v.data(),nullptr),"info");return v.c_str();}
struct Device{
 cl_device_id d;cl_context ctx;cl_command_queue q;std::array<cl_program,2>pr;std::array<cl_kernel,2>kn;std::array<cl_mem,2>pl;cl_mem jobs=nullptr,out=nullptr;size_t capacity=0;cl_event ev=nullptr;double lastms=0;unsigned index;
 Device(cl_device_id id,unsigned ix,const std::vector<Plan>&p):d(id),index(ix){cl_int e;cl_device_type type;ck(clGetDeviceInfo(d,CL_DEVICE_TYPE,sizeof(type),&type,nullptr),"type");assert(type==CL_DEVICE_TYPE_GPU);std::string name=info(d,CL_DEVICE_NAME);assert(name.find("B50")!=std::string::npos);std::cout<<"DEVICE "<<index<<" "<<name<<" driver="<<info(d,CL_DRIVER_VERSION)<<std::endl;ctx=clCreateContext(nullptr,1,&d,nullptr,nullptr,&e);ck(e,"context");q=clCreateCommandQueue(ctx,d,CL_QUEUE_PROFILING_ENABLE,&e);ck(e,"queue");
  std::vector<uint8_t>soa(p.size()*STRIDE);auto raw=reinterpret_cast<const uint8_t*>(p.data());for(size_t r=0;r<p.size();r++)for(size_t f=0;f<STRIDE;f++)soa[f*p.size()+r]=raw[r*STRIDE+f];
  for(unsigned l=0;l<2;l++){pr[l]=clCreateProgramWithSource(ctx,1,&kernel,nullptr,&e);ck(e,"program");std::string opts="-cl-std=CL1.2 -DLAYOUT="+std::to_string(l);e=clBuildProgram(pr[l],1,&d,opts.c_str(),nullptr,nullptr);if(e){size_t n;clGetProgramBuildInfo(pr[l],d,CL_PROGRAM_BUILD_LOG,0,nullptr,&n);std::string log(n,' ');clGetProgramBuildInfo(pr[l],d,CL_PROGRAM_BUILD_LOG,n,log.data(),nullptr);std::cerr<<log<<std::endl;}ck(e,"build");kn[l]=clCreateKernel(pr[l],"assess",&e);ck(e,"kernel");pl[l]=clCreateBuffer(ctx,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,p.size()*STRIDE,l?static_cast<void*>(soa.data()):const_cast<Plan*>(p.data()),&e);ck(e,"plans");}
 }
 void load(const std::vector<Job>&j,size_t count){if(jobs)clReleaseMemObject(jobs);cl_int e;jobs=clCreateBuffer(ctx,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,j.size()*sizeof(Job),const_cast<Job*>(j.data()),&e);ck(e,"jobs");if(count>capacity){if(out)clReleaseMemObject(out);out=clCreateBuffer(ctx,CL_MEM_WRITE_ONLY,count*sizeof(unsigned),nullptr,&e);ck(e,"output");capacity=count;}}
 void launch(unsigned layout,size_t wg,U start,U count){auto k=kn[layout];ck(clSetKernelArg(k,0,sizeof(jobs),&jobs),"arg0");ck(clSetKernelArg(k,1,sizeof(pl[layout]),&pl[layout]),"arg1");ck(clSetKernelArg(k,2,sizeof(out),&out),"arg2");ck(clSetKernelArg(k,3,sizeof(start),&start),"arg3");ck(clSetKernelArg(k,4,sizeof(count),&count),"arg4");size_t global=(count+wg-1)/wg*wg;ck(clEnqueueNDRangeKernel(q,k,1,nullptr,&global,&wg,0,nullptr,&ev),"enqueue");ck(clFlush(q),"flush");}
 void read(unsigned*dest,size_t count){ck(clEnqueueReadBuffer(q,out,CL_TRUE,0,count*sizeof(unsigned),dest,0,nullptr,nullptr),"read");cl_ulong a,b;ck(clGetEventProfilingInfo(ev,CL_PROFILING_COMMAND_START,sizeof(a),&a,nullptr),"profile start");ck(clGetEventProfilingInfo(ev,CL_PROFILING_COMMAND_END,sizeof(b),&b,nullptr),"profile end");lastms=(b-a)/1e6;clReleaseEvent(ev);ev=nullptr;}
};
double run(std::vector<Device*>&d,unsigned layout,size_t wg,unsigned cards,const std::vector<Job>&j,std::vector<unsigned>&out){size_t total=j.size()*NC;out.resize(total);auto start=Clock::now();size_t half=cards==2?total/2:total;d[0]->launch(layout,wg,0,half);if(cards==2)d[1]->launch(layout,wg,half,total-half);d[0]->read(out.data(),half);if(cards==2)d[1]->read(out.data()+half,total-half);return std::chrono::duration<double,std::milli>(Clock::now()-start).count();}
int main(int argc,char**argv){assert(argc>=3);std::string mode=argv[1],prefix=argv[2];auto p=plans();cl_uint np=0;ck(clGetPlatformIDs(0,nullptr,&np),"platforms");std::vector<cl_platform_id>platforms(np);ck(clGetPlatformIDs(np,platforms.data(),nullptr),"platform ids");std::vector<cl_device_id>ids;for(auto platform:platforms){cl_uint n=0;cl_int e=clGetDeviceIDs(platform,CL_DEVICE_TYPE_GPU,0,nullptr,&n);if(e==CL_DEVICE_NOT_FOUND)continue;ck(e,"device count");std::vector<cl_device_id>v(n);ck(clGetDeviceIDs(platform,CL_DEVICE_TYPE_GPU,n,v.data(),nullptr),"devices");for(auto id:v)if(info(id,CL_DEVICE_NAME).find("B50")!=std::string::npos)ids.push_back(id);}assert(ids.size()==2&&ids[0]!=ids[1]);Device a(ids[0],0,p),b(ids[1],1,p);std::vector<Device*>d{&a,&b};std::vector<Job>jobs;std::vector<unsigned>ref,out;
 if(mode=="bench"){
  U s=0xb50beac0123ULL;for(unsigned i=0;i<32;i++){unsigned n=4+i%3;jobs.push_back({rnd(s)&limit(n),n,i%10});}for(auto dev:d)dev->load(jobs,jobs.size()*NC);ref.resize(jobs.size()*NC);omp_set_num_threads(12);auto start=Clock::now();
  #pragma omp parallel for schedule(static)
  for(size_t i=0;i<ref.size();i++){auto&j=jobs[i/NC];ref[i]=score(j,p[(j.n-4)*NC+i%NC]);}
  double cpums=std::chrono::duration<double,std::milli>(Clock::now()-start).count();std::ofstream log(prefix+"-timings.tsv");assert(log);log<<"cards\tlayout\twg\trepeat\twall_ms\tgpu0_ms\tgpu1_ms\tcount\n";std::cout<<"CPU_REFERENCE_PASS count="<<ref.size()<<" threads=12 wall_ms="<<cpums<<std::endl;std::ofstream cpu(prefix+"-cpu.txt");cpu<<cpums<<" "<<ref.size()<<"\n";
  double best=1e99;unsigned bl=0;size_t bw=64;
  // One warm-up per variant. Tuning data are fixed, never benchmark circuit seeds.
  for(unsigned l=0;l<2;l++)for(size_t wg:{size_t(64),size_t(128),size_t(256)}){run(d,l,wg,2,jobs,out);assert(out==ref);std::vector<double>ms;for(unsigned rep=0;rep<3;rep++){double wall=run(d,l,wg,2,jobs,out);assert(out==ref);ms.push_back(wall);log<<2<<'\t'<<l<<'\t'<<wg<<'\t'<<rep<<'\t'<<wall<<'\t'<<a.lastms<<'\t'<<b.lastms<<'\t'<<out.size()<<'\n';}std::sort(ms.begin(),ms.end());std::cout<<"TUNE_PASS layout="<<l<<" wg="<<wg<<" median_ms="<<ms[1]<<std::endl;if(ms[1]<best){best=ms[1];bl=l;bw=wg;}}
  // Different truth functions for validation and one/two-card comparison.
  for(auto&j:jobs)j.truth=rnd(s)&limit(j.n);for(auto dev:d)dev->load(jobs,jobs.size()*NC);
  start=Clock::now();
  #pragma omp parallel for schedule(static)
  for(size_t i=0;i<ref.size();i++){auto&j=jobs[i/NC];ref[i]=score(j,p[(j.n-4)*NC+i%NC]);}
  cpums=std::chrono::duration<double,std::milli>(Clock::now()-start).count();cpu<<cpums<<" "<<ref.size()<<"\n";
  for(unsigned cards:{1u,2u})for(unsigned rep=0;rep<3;rep++){double wall=run(d,bl,bw,cards,jobs,out);assert(out==ref);log<<cards<<'\t'<<bl<<'\t'<<bw<<'\t'<<(rep+100)<<'\t'<<wall<<'\t'<<a.lastms<<'\t'<<(cards==2?b.lastms:0)<<'\t'<<out.size()<<'\n';std::cout<<"HOLDOUT_PASS cards="<<cards<<" ms="<<wall<<" cpu_ms="<<cpums<<std::endl;}
  for(auto&j:jobs)for(unsigned c:{0u,1u,63u,1024u,32767u,65535u})exact(j,p[(j.n-4)*NC+c]);std::ofstream cfg(prefix+"-config.txt");cfg<<bl<<" "<<bw<<"\n";std::cout<<"GPU_TUNING_COMPLETE layout="<<bl<<" wg="<<bw<<" exact_cpu_gpu_agreement=true distinct_B50=2\n";
 }else{assert(mode=="search"&&argc==5);std::ifstream in(argv[3]),cfg(argv[4]);assert(in&&cfg);std::string truth;unsigned n,k;while(in>>n>>k>>truth){assert(n>=4&&n<=6&&k<=20);jobs.push_back({std::stoull(truth,nullptr,16),n,k});}assert(!jobs.empty());unsigned layout;size_t wg;cfg>>layout>>wg;assert(layout<2&&(wg==64||wg==128||wg==256));size_t count=jobs.size()*NC;assert(count<400000000ULL);for(auto dev:d)dev->load(jobs,count);
  std::vector<unsigned>reference(count);omp_set_num_threads(12);auto tick=Clock::now();
  #pragma omp parallel for schedule(static)
  for(size_t i=0;i<count;i++){auto&j=jobs[i/NC];reference[i]=score(j,p[(j.n-4)*NC+i%NC]);}
  double cpu_ms=std::chrono::duration<double,std::milli>(Clock::now()-tick).count();
  std::ofstream perf(prefix+"-perf.tsv");assert(perf);perf<<"cards\trepeat\twall_ms\tgpu0_ms\tgpu1_ms\tcount\n";perf<<"0\t0\t"<<cpu_ms<<"\t0\t0\t"<<count<<'\n';double wall=0;
  for(unsigned cards:{1u,2u}){run(d,layout,wg,cards,jobs,out);assert(out==reference);for(unsigned rep=0;rep<5;rep++){wall=run(d,layout,wg,cards,jobs,out);assert(out==reference);perf<<cards<<'\t'<<rep<<'\t'<<wall<<'\t'<<a.lastms<<'\t'<<(cards==2?b.lastms:0)<<'\t'<<count<<'\n';}}
  std::cout<<"ACTUAL_WORKLOAD_CPU_GPU_PASS count="<<count<<" threads=12 cpu_ms="<<cpu_ms<<" both_distinct_GPUs=true"<<std::endl;
  std::ofstream result(prefix+"-best.tsv");assert(result);result<<"n\tk\ttruth\tcandidate\tT\tN\tdepth\tpolarity\tanf\tgates\n";
  for(size_t i=0;i<jobs.size();i++){auto&j=jobs[i];std::vector<unsigned>order(NC);std::iota(order.begin(),order.end(),0);std::partial_sort(order.begin(),order.begin()+8,order.end(),[&](unsigned x,unsigned y){return std::pair(out[i*NC+x],x)<std::pair(out[i*NC+y],y);});for(unsigned z=0;z<8;z++){unsigned c=order[z],v=out[i*NC+c];auto&pp=p[(j.n-4)*NC+c];assert(v==score(j,pp));exact(j,pp);result<<j.n<<'\t'<<j.k<<'\t'<<std::hex<<j.truth<<std::dec<<'\t'<<c<<'\t'<<(v>>16)<<'\t'<<(v&65535)<<'\t'<<unsigned(pp.len)<<'\t'<<unsigned(pp.pol)<<'\t'<<std::hex<<anf(j,pp)<<std::dec<<'\t';for(unsigned g=0;g<pp.len;g++){if(g)result<<',';result<<unsigned(pp.gate[g]);}result<<'\n';}}
  std::cout<<"GPU_SEARCH_PASS jobs="<<jobs.size()<<" candidates="<<count<<" two_gpu_wall_ms="<<wall<<" gpu0_ms="<<a.lastms<<" gpu1_ms="<<b.lastms<<" selected_all_truths_exact=true\n";
 }
}
