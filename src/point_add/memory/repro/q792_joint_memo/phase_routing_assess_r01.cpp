#define CL_TARGET_OPENCL_VERSION 120
#include <CL/cl.h>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <future>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
using U=uint64_t;
void ck(cl_int e){if(e){std::cerr<<"OpenCL "<<e<<std::endl;std::abort();}}
std::string info(cl_device_id d,cl_device_info k){size_t n;ck(clGetDeviceInfo(d,k,0,nullptr,&n));std::string s(n,'\0');ck(clGetDeviceInfo(d,k,n,s.data(),nullptr));return s.c_str();}
template<class T>std::vector<T> read(const std::string&p){std::ifstream f(p,std::ios::binary|std::ios::ate);assert(f);size_t n=f.tellg();assert(n%sizeof(T)==0);std::vector<T>x(n/sizeof(T));f.seekg(0);f.read((char*)x.data(),n);assert(f);return x;}
const char* source=R"CLC(
kernel void assess(global const uint4*ops,global const ulong*cases,global uint*out,global ulong*counts,uint nops,uint ncases){
 uint id=get_global_id(0);if(id>=ncases)return;ulong state[9];for(uint i=0;i<9;i++)state[i]=cases[id*18+i];ulong t=0;
 for(uint i=0;i<nops;i++){uint4 o=ops[i];uint on=1;if(o.x>=1)on&=(state[o.z/64]>>(o.z%64))&1;if(o.x==2)on&=(state[o.w/64]>>(o.w%64))&1;state[o.y/64]^=((ulong)on)<<(o.y%64);t+=o.x==2;}
 uint bad=0;for(uint i=0;i<9;i++)bad|=state[i]!=cases[id*18+9+i];out[id]=bad;if(id==0)counts[0]=t;
}
)CLC";
std::string run(cl_device_id device,unsigned di,const std::string&root){
 cl_int e;auto c=clCreateContext(nullptr,1,&device,nullptr,nullptr,&e);ck(e);auto q=clCreateCommandQueue(c,device,CL_QUEUE_PROFILING_ENABLE,&e);ck(e);auto p=clCreateProgramWithSource(c,1,&source,nullptr,&e);ck(e);e=clBuildProgram(p,1,&device,"-cl-std=CL1.2",nullptr,nullptr);if(e){size_t n;clGetProgramBuildInfo(p,device,CL_PROGRAM_BUILD_LOG,0,nullptr,&n);std::string s(n,' ');clGetProgramBuildInfo(p,device,CL_PROGRAM_BUILD_LOG,n,s.data(),nullptr);std::cerr<<s;}ck(e);auto k=clCreateKernel(p,"assess",&e);ck(e);
 std::ostringstream report;report<<"DEVICE "<<di<<' '<<info(device,CL_DEVICE_NAME)<<" driver="<<info(device,CL_DRIVER_VERSION)<<'\n';
 for(unsigned clock=di*2;clock<di*2+2;clock++){
  std::string base=root+"/j"+std::to_string(clock);auto ops=read<uint32_t>(base+"-ops.bin");auto cases=read<U>(base+"-cases.bin");assert(ops.size()%4==0&&cases.size()%18==0);cl_uint no=ops.size()/4,nc=cases.size()/18;assert(no&&nc);
  auto ob=clCreateBuffer(c,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,ops.size()*4,ops.data(),&e);ck(e);auto cb=clCreateBuffer(c,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,cases.size()*8,cases.data(),&e);ck(e);auto out=clCreateBuffer(c,CL_MEM_WRITE_ONLY,nc*4,nullptr,&e);ck(e);auto count=clCreateBuffer(c,CL_MEM_WRITE_ONLY,8,nullptr,&e);ck(e);cl_mem ms[]={ob,cb,out,count};for(unsigned i=0;i<4;i++)ck(clSetKernelArg(k,i,sizeof(cl_mem),&ms[i]));ck(clSetKernelArg(k,4,4,&no));ck(clSetKernelArg(k,5,4,&nc));size_t local=256,global=(nc+255)/256*256;cl_event event;ck(clEnqueueNDRangeKernel(q,k,1,nullptr,&global,&local,0,nullptr,&event));std::vector<uint32_t>bad(nc);U t;ck(clEnqueueReadBuffer(q,out,CL_TRUE,0,nc*4,bad.data(),0,nullptr,nullptr));ck(clEnqueueReadBuffer(q,count,CL_TRUE,0,8,&t,0,nullptr,nullptr));U cpu_t=0;for(unsigned i=0;i<no;i++)cpu_t+=ops[4*i]==2;assert(t==cpu_t);unsigned errors=0,first=nc;for(unsigned i=0;i<nc;i++)if(bad[i]){errors++;first=std::min(first,i);}cl_ulong begin,end;ck(clGetEventProfilingInfo(event,CL_PROFILING_COMMAND_START,sizeof(begin),&begin,nullptr));ck(clGetEventProfilingInfo(event,CL_PROFILING_COMMAND_END,sizeof(end),&end,nullptr));
  report<<"CLOCK "<<clock<<" cases="<<nc<<" errors="<<errors<<" first_error="<<first<<" T="<<t<<" ops="<<no<<" ms="<<double(end-begin)/1e6<<'\n';
  std::ofstream f(base+"-gpu-result.tsv");f<<nc<<'\t'<<errors<<'\t'<<first<<'\t'<<t<<'\t'<<no<<'\n';assert(f);std::ofstream bo(base+"-gpu-mismatches.bin",std::ios::binary);bo.write((char*)bad.data(),bad.size()*4);assert(bo);
  clReleaseEvent(event);for(auto b:ms)ck(clReleaseMemObject(b));
 }ck(clReleaseKernel(k));ck(clReleaseProgram(p));ck(clReleaseCommandQueue(q));ck(clReleaseContext(c));return report.str();
}
int main(int argc,char**argv){assert(argc==2);cl_uint n;ck(clGetPlatformIDs(0,nullptr,&n));std::vector<cl_platform_id>ps(n);ck(clGetPlatformIDs(n,ps.data(),nullptr));std::vector<cl_device_id>ids;
 for(auto p:ps){cl_uint nd;auto e=clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,0,nullptr,&nd);if(e==CL_DEVICE_NOT_FOUND)continue;ck(e);std::vector<cl_device_id>ds(nd);ck(clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,nd,ds.data(),nullptr));for(auto d:ds)if(info(d,CL_DEVICE_NAME).find("B50")!=std::string::npos)ids.push_back(d);}assert(ids.size()==2&&ids[0]!=ids[1]);auto a=std::async(std::launch::async,run,ids[0],0,std::string(argv[1]));auto b=std::async(std::launch::async,run,ids[1],1,std::string(argv[1]));std::cout<<a.get()<<b.get()<<"PHASE_ROUTING_GPU_ASSESSMENT_FINISHED both_B50=true inspect_error_counts=true\n";
}
