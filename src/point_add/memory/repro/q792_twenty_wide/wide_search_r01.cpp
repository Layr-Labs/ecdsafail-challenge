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
kernel void score(global const uchar*truth,global const uint4*jobs,global uint2*out,uint start){
 uint id=start+get_group_id(0),l=get_local_id(0),w=get_local_size(0);uint4 j=jobs[id];uint n=j.x,k=j.y,pol=j.z,off=j.w,N=1u<<n;
 local uchar a[4096];local uint ts[64],ns[64];
 for(uint m=l;m<N;m+=w)a[m]=truth[off+(m^pol)];barrier(CLK_LOCAL_MEM_FENCE);
 for(uint b=0;b<n;b++){uint bit=1u<<b;for(uint m=l;m<N;m+=w)if(m&bit)a[m]^=a[m^bit];barrier(CLK_LOCAL_MEM_FENCE);}
 uint t=0,ops=0;for(uint m=l;m<N;m+=w)if(a[m]){uint c=k+popcount(m);uint cost=c<2?0:2*c-3;t+=cost;ops+=max(1u,cost)+2*popcount(m&pol);}ts[l]=t;ns[l]=ops;barrier(CLK_LOCAL_MEM_FENCE);
 for(uint z=w/2;z;z/=2){if(l<z){ts[l]+=ts[l+z];ns[l]+=ns[l+z];}barrier(CLK_LOCAL_MEM_FENCE);}if(l==0)out[id]=(uint2)(ts[0],ns[0]);
}
)CLC";
struct Device{
 cl_context ctx;cl_command_queue q;cl_program p;cl_kernel kernel;cl_mem truth,jobs,out;cl_event event;unsigned ix;
 Device(cl_device_id id,unsigned index,const std::vector<unsigned char>&data,const std::vector<unsigned>&desc,unsigned count):ix(index){
 std::cout<<"DEVICE "<<ix<<" "<<info(id,CL_DEVICE_NAME)<<" driver="<<info(id,CL_DRIVER_VERSION)<<std::endl;cl_int e;ctx=clCreateContext(nullptr,1,&id,nullptr,nullptr,&e);ck(e);q=clCreateCommandQueue(ctx,id,CL_QUEUE_PROFILING_ENABLE,&e);ck(e);p=clCreateProgramWithSource(ctx,1,&source,nullptr,&e);ck(e);e=clBuildProgram(p,1,&id,"-cl-std=CL1.2",nullptr,nullptr);if(e){size_t n;clGetProgramBuildInfo(p,id,CL_PROGRAM_BUILD_LOG,0,nullptr,&n);std::string s(n,' ');clGetProgramBuildInfo(p,id,CL_PROGRAM_BUILD_LOG,n,s.data(),nullptr);std::cerr<<s;}ck(e);kernel=clCreateKernel(p,"score",&e);ck(e);
 truth=clCreateBuffer(ctx,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,data.size(),const_cast<unsigned char*>(data.data()),&e);ck(e);jobs=clCreateBuffer(ctx,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,desc.size()*4,const_cast<unsigned*>(desc.data()),&e);ck(e);out=clCreateBuffer(ctx,CL_MEM_WRITE_ONLY,count*8,nullptr,&e);ck(e);}
 void launch(unsigned start,unsigned count){ck(clSetKernelArg(kernel,0,sizeof(truth),&truth));ck(clSetKernelArg(kernel,1,sizeof(jobs),&jobs));ck(clSetKernelArg(kernel,2,sizeof(out),&out));ck(clSetKernelArg(kernel,3,4,&start));size_t local=64,global=size_t(count)*64;ck(clEnqueueNDRangeKernel(q,kernel,1,nullptr,&global,&local,0,nullptr,&event));ck(clFlush(q));}
 void read(unsigned start,unsigned count,unsigned*values){ck(clEnqueueReadBuffer(q,out,CL_TRUE,start*8,count*8,values,0,nullptr,nullptr));cl_ulong a,b;ck(clGetEventProfilingInfo(event,CL_PROFILING_COMMAND_START,sizeof(a),&a,nullptr));ck(clGetEventProfilingInfo(event,CL_PROFILING_COMMAND_END,sizeof(b),&b,nullptr));std::cout<<"KERNEL "<<ix<<" ms="<<(b-a)/1e6<<std::endl;}
};
int main(int argc,char**argv){assert(argc==3);std::ifstream f(argv[1]);unsigned nf;f>>nf;std::vector<unsigned char>truth;std::vector<unsigned>desc,offset;
for(unsigned j=0;j<nf;j++){unsigned n,k;std::string bits;f>>n>>k>>bits;assert(n<=12&&bits.size()==(1u<<n));unsigned pos=truth.size();for(char c:bits){assert(c=='0'||c=='1');truth.push_back(c-'0');}offset.push_back(desc.size()/4);for(unsigned pol=0;pol<(1u<<n);pol++){desc.push_back(n);desc.push_back(k);desc.push_back(pol);desc.push_back(pos);}}assert(f);unsigned count=desc.size()/4;assert(count>1);
cl_uint np;ck(clGetPlatformIDs(0,nullptr,&np));std::vector<cl_platform_id>ps(np);ck(clGetPlatformIDs(np,ps.data(),nullptr));std::vector<cl_device_id>ids;for(auto p:ps){cl_uint nd;cl_int e=clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,0,nullptr,&nd);if(e==CL_DEVICE_NOT_FOUND)continue;ck(e);std::vector<cl_device_id>ds(nd);ck(clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,nd,ds.data(),nullptr));for(auto d:ds)if(info(d,CL_DEVICE_NAME).find("B50")!=std::string::npos)ids.push_back(d);}assert(ids.size()==2&&ids[0]!=ids[1]);
Device a(ids[0],0,truth,desc,count),b(ids[1],1,truth,desc,count);unsigned half=count/2;a.launch(0,half);b.launch(half,count-half);std::vector<unsigned>scores(count*2);a.read(0,half,scores.data());b.read(half,count-half,scores.data()+half*2);
std::ofstream out(argv[2]);assert(out);for(unsigned j=0;j<nf;j++){unsigned first=offset[j],N=1u<<desc[first*4];for(unsigned p=0;p<N;p++)out<<j<<' '<<p<<' '<<scores[(first+p)*2]<<' '<<scores[(first+p)*2+1]<<'\n';}
std::cout<<"WIDE_GPU_SEARCH_PASS functions="<<nf<<" candidates="<<count<<" both_B50=true CPU_scores_not_used_for_selection=true"<<std::endl;
}
