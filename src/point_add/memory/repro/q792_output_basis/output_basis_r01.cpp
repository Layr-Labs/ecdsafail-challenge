#define CL_TARGET_OPENCL_VERSION 120
#include <CL/cl.h>
#include <vector>
#include <array>
#include <string>
#include <iostream>
#include <fstream>
#include <cassert>
#include <algorithm>
#include <chrono>
void ck(cl_int x){if(x){std::cerr<<"CL_ERROR "<<x<<std::endl;std::exit(2);}}
std::string info(cl_device_id d,cl_device_info key){size_t n=0;ck(clGetDeviceInfo(d,key,0,nullptr,&n));std::string s(n,'\0');ck(clGetDeviceInfo(d,key,n,s.data(),nullptr));return s.c_str();}
const char *source=R"CLC(
kernel void basis(global const uint*n,global const uint*cost,global uint*out,uint groups,uint start,uint count){
 uint lid=get_global_id(0);if(lid>=count)return;uint g=start+lid,m=n[g];uint piv[8]={0,0,0,0,0,0,0,0};uint total=0;
 for(uint i=0;i<m;i++){uint best=0xffffffff,chosen=0,remainder=0;
  for(uint mask=1;mask<(1u<<m);mask++){uint x=mask;for(int b=7;b>=0;b--)if((x>>b)&1)x^=piv[b];uint c=cost[mask*groups+g];if(x&&c<best){best=c;chosen=mask;remainder=x;}}
  uint top=31-clz(remainder);piv[top]=remainder;out[g*9+i]=chosen;total+=best;
 }out[g*9+8]=total;
}
)CLC";
struct Dev{cl_context ctx;cl_command_queue q;cl_program p;cl_kernel k;cl_mem bn,bc,bo;cl_event e;unsigned index;
Dev(cl_device_id id,unsigned ix,const std::vector<unsigned>&n,const std::vector<unsigned>&c):index(ix){cl_int x;std::cout<<"DEVICE "<<ix<<" "<<info(id,CL_DEVICE_NAME)<<" driver="<<info(id,CL_DRIVER_VERSION)<<std::endl;ctx=clCreateContext(nullptr,1,&id,nullptr,nullptr,&x);ck(x);q=clCreateCommandQueue(ctx,id,CL_QUEUE_PROFILING_ENABLE,&x);ck(x);p=clCreateProgramWithSource(ctx,1,&source,nullptr,&x);ck(x);x=clBuildProgram(p,1,&id,"-cl-std=CL1.2",nullptr,nullptr);if(x){size_t len;clGetProgramBuildInfo(p,id,CL_PROGRAM_BUILD_LOG,0,nullptr,&len);std::string log(len,' ');clGetProgramBuildInfo(p,id,CL_PROGRAM_BUILD_LOG,len,log.data(),nullptr);std::cerr<<log;}ck(x);k=clCreateKernel(p,"basis",&x);ck(x);bn=clCreateBuffer(ctx,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,n.size()*4,const_cast<unsigned*>(n.data()),&x);ck(x);bc=clCreateBuffer(ctx,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,c.size()*4,const_cast<unsigned*>(c.data()),&x);ck(x);bo=clCreateBuffer(ctx,CL_MEM_WRITE_ONLY,n.size()*9*4,nullptr,&x);ck(x);}
void launch(unsigned groups,unsigned start,unsigned count){ck(clSetKernelArg(k,0,sizeof(bn),&bn));ck(clSetKernelArg(k,1,sizeof(bc),&bc));ck(clSetKernelArg(k,2,sizeof(bo),&bo));ck(clSetKernelArg(k,3,4,&groups));ck(clSetKernelArg(k,4,4,&start));ck(clSetKernelArg(k,5,4,&count));size_t wg=256,size=(count+255)/256*256;ck(clEnqueueNDRangeKernel(q,k,1,nullptr,&size,&wg,0,nullptr,&e));ck(clFlush(q));}
void read(unsigned start,unsigned count,unsigned*data){ck(clEnqueueReadBuffer(q,bo,CL_TRUE,start*9*4,count*9*4,data,0,nullptr,nullptr));cl_ulong a,b;ck(clGetEventProfilingInfo(e,CL_PROFILING_COMMAND_START,sizeof(a),&a,nullptr));ck(clGetEventProfilingInfo(e,CL_PROFILING_COMMAND_END,sizeof(b),&b,nullptr));std::cout<<"KERNEL "<<index<<" ms="<<(b-a)/1e6<<std::endl;}
};
int main(int argc,char**argv){assert(argc==3);std::ifstream f(argv[1]);assert(f);unsigned groups;f>>groups;assert(groups>=2);std::vector<unsigned>n(groups),cost(groups*256,0xffffffff);for(unsigned g=0;g<groups;g++){f>>n[g];assert(n[g]>=2&&n[g]<=8);for(unsigned m=1;m<(1u<<n[g]);m++)f>>cost[m*groups+g];}assert(f);cl_uint np;ck(clGetPlatformIDs(0,nullptr,&np));std::vector<cl_platform_id>plats(np);ck(clGetPlatformIDs(np,plats.data(),nullptr));std::vector<cl_device_id>ids;for(auto p:plats){cl_uint nd;cl_int x=clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,0,nullptr,&nd);if(x==CL_DEVICE_NOT_FOUND)continue;ck(x);std::vector<cl_device_id>v(nd);ck(clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,nd,v.data(),nullptr));for(auto d:v)if(info(d,CL_DEVICE_NAME).find("B50")!=std::string::npos)ids.push_back(d);}assert(ids.size()==2&&ids[0]!=ids[1]);Dev a(ids[0],0,n,cost),b(ids[1],1,n,cost);unsigned half=groups/2;a.launch(groups,0,half);b.launch(groups,half,groups-half);std::vector<unsigned>out(groups*9);a.read(0,half,out.data());b.read(half,groups-half,out.data()+half*9);std::ofstream result(argv[2]);assert(result);unsigned checked=0;for(unsigned g=0;g<groups;g++){std::array<unsigned,8>piv{};unsigned score=0;result<<g;for(unsigned j=0;j<n[g];j++){unsigned m=out[g*9+j],x=m;assert(m&&m<(1u<<n[g]));for(int k=7;k>=0;k--)if(x>>k&1)x^=piv[k];assert(x);piv[31-__builtin_clz(x)]=x;score+=cost[m*groups+g];result<<'\t'<<m;}assert(score==out[g*9+8]);result<<'\t'<<score<<'\n';checked++;}std::cout<<"GPU_OUTPUT_BASIS_PASS groups="<<groups<<" both_B50=true CPU_selected_rank_and_score_checks="<<checked<<std::endl;}
