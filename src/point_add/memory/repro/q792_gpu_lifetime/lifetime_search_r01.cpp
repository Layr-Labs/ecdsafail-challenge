#define CL_TARGET_OPENCL_VERSION 120
#include <CL/cl.h>
#include <vector>
#include <string>
#include <fstream>
#include <iostream>
#include <cassert>
#include <algorithm>
void ck(cl_int x){if(x){std::cerr<<"OpenCL error "<<x<<std::endl;std::exit(2);}}
std::string info(cl_device_id d,cl_device_info k){size_t n;ck(clGetDeviceInfo(d,k,0,nullptr,&n));std::string s(n,'\0');ck(clGetDeviceInfo(d,k,n,s.data(),nullptr));return s.c_str();}
const char*source=R"CLC(
uint tof(uint k){return k<2?0:2*k-3;}
uint pm(uint h){return h==0?16:h==1?24:28;}
uint pv(uint h){return h==0?0:h==1?16:h==2?24:28;}
kernel void score(global const uint*in,global uint*out,uint jobs,uint start,uint count){
 uint lane=get_global_id(0);if(lane>=count)return;uint id=start+lane;
 uint lo=in[jobs+id],hi=in[2*jobs+id],n=in[3*jobs+id],fixed=in[4*jobs+id],wire=in[6*jobs+id],split=in[7*jobs+id];
 uint old=0,newcost=0,lastm=0,lastv=0,have=0,loads=0;
 for(uint i=1;i<n;i++){
  uint value=i-1;if(value<lo||value>=hi)continue;uint h=value/64,left=max(lo,h*64),right=min(hi,(h+1)*64),lowm=0;
  for(uint b=0;b<6;b++)if((left>>b)!=((right-1)>>b))lowm|=1u<<(b+5);
  uint highm=lo/64==(hi-1)/64?0:pm(h);
  old+=tof(popcount(lowm|highm));
  if(value>=252)continue;right=min(min(hi,252u),(h+1)*64);lowm=0;
  for(uint b=0;b<6;b++)if((left>>b)!=((right-1)>>b))lowm|=1u<<(b+5);
  uint cm=(lowm&~((1u<<(5+split))-1))|(pm(h)&~fixed);
  uint cv=(((value&63)<<5)|pv(h))&cm;
  if(!have||cm!=lastm||cv!=lastv){if(have)newcost+=tof(popcount(lastm));newcost+=tof(popcount(cm));lastm=cm;lastv=cv;have=1;loads++;}
  uint consumer=(lowm&((1u<<(5+split))-1));
  newcost+=tof(popcount(consumer)+1);
 }
 if(have)newcost+=tof(popcount(lastm));
 out[id*4]=old*2;out[id*4+1]=(fixed&(1u<<wire))?newcost*2:0xffffffff;out[id*4+2]=loads;out[id*4+3]=have;
}
)CLC";
struct Device{
 cl_context ctx;cl_command_queue q;cl_program p;cl_kernel k;cl_mem data,out;cl_event event;unsigned ix;
 Device(cl_device_id id,unsigned index,const std::vector<unsigned>&input,unsigned jobs):ix(index){
  std::cout<<"DEVICE "<<ix<<" "<<info(id,CL_DEVICE_NAME)<<" driver="<<info(id,CL_DRIVER_VERSION)<<std::endl;
  cl_int e;ctx=clCreateContext(nullptr,1,&id,nullptr,nullptr,&e);ck(e);q=clCreateCommandQueue(ctx,id,CL_QUEUE_PROFILING_ENABLE,&e);ck(e);
  p=clCreateProgramWithSource(ctx,1,&source,nullptr,&e);ck(e);e=clBuildProgram(p,1,&id,"-cl-std=CL1.2",nullptr,nullptr);if(e){size_t n;clGetProgramBuildInfo(p,id,CL_PROGRAM_BUILD_LOG,0,nullptr,&n);std::string s(n,' ');clGetProgramBuildInfo(p,id,CL_PROGRAM_BUILD_LOG,n,s.data(),nullptr);std::cerr<<s;}ck(e);
  k=clCreateKernel(p,"score",&e);ck(e);data=clCreateBuffer(ctx,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,input.size()*4,const_cast<unsigned*>(input.data()),&e);ck(e);out=clCreateBuffer(ctx,CL_MEM_WRITE_ONLY,jobs*4*4,nullptr,&e);ck(e);
 }
 void launch(unsigned jobs,unsigned start,unsigned count){ck(clSetKernelArg(k,0,sizeof(data),&data));ck(clSetKernelArg(k,1,sizeof(out),&out));ck(clSetKernelArg(k,2,4,&jobs));ck(clSetKernelArg(k,3,4,&start));ck(clSetKernelArg(k,4,4,&count));size_t group=256,size=(count+255)/256*256;ck(clEnqueueNDRangeKernel(q,k,1,nullptr,&size,&group,0,nullptr,&event));ck(clFlush(q));}
 void read(unsigned start,unsigned count,unsigned*values){ck(clEnqueueReadBuffer(q,out,CL_TRUE,start*16,count*16,values,0,nullptr,nullptr));cl_ulong a,b;ck(clGetEventProfilingInfo(event,CL_PROFILING_COMMAND_START,sizeof(a),&a,nullptr));ck(clGetEventProfilingInfo(event,CL_PROFILING_COMMAND_END,sizeof(b),&b,nullptr));std::cout<<"KERNEL "<<ix<<" ms="<<(b-a)/1e6<<std::endl;}
};
int main(int argc,char**argv){
 assert(argc==3);std::ifstream f(argv[1]);unsigned jobs;f>>jobs;assert(jobs==202*11*7);std::vector<unsigned>input(jobs*8);for(unsigned j=0;j<jobs;j++)for(unsigned col=0;col<8;col++)f>>input[col*jobs+j];assert(f);
 cl_uint np;ck(clGetPlatformIDs(0,nullptr,&np));std::vector<cl_platform_id>platforms(np);ck(clGetPlatformIDs(np,platforms.data(),nullptr));std::vector<cl_device_id>ids;
 for(auto p:platforms){cl_uint nd;cl_int x=clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,0,nullptr,&nd);if(x==CL_DEVICE_NOT_FOUND)continue;ck(x);std::vector<cl_device_id>ds(nd);ck(clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,nd,ds.data(),nullptr));for(auto d:ds)if(info(d,CL_DEVICE_NAME).find("B50")!=std::string::npos)ids.push_back(d);}assert(ids.size()==2&&ids[0]!=ids[1]);
 Device a(ids[0],0,input,jobs),b(ids[1],1,input,jobs);unsigned half=jobs/2;a.launch(jobs,0,half);b.launch(jobs,half,jobs-half);std::vector<unsigned>out(jobs*4);a.read(0,half,out.data());b.read(half,jobs-half,out.data()+half*4);
 std::ofstream result(argv[2]);assert(result);for(unsigned j=0;j<jobs;j++){result<<j;for(unsigned col=0;col<8;col++)result<<'\t'<<input[col*jobs+j];for(unsigned col=0;col<4;col++)result<<'\t'<<out[j*4+col];result<<'\n';}
 std::cout<<"LIFETIME_GPU_PASS jobs="<<jobs<<" both_B50=true CPU_scores_not_used_for_selection=true"<<std::endl;
}
