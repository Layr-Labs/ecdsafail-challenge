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
void ck(cl_int e){if(e){std::cerr<<"OpenCL "<<e<<std::endl;std::abort();}}
std::string info(cl_device_id d,cl_device_info k){size_t n;ck(clGetDeviceInfo(d,k,0,nullptr,&n));std::string s(n,'\0');ck(clGetDeviceInfo(d,k,n,s.data(),nullptr));return s.c_str();}
template<class T>std::vector<T>read(const std::string&p){std::ifstream f(p,std::ios::binary|std::ios::ate);assert(f);size_t n=f.tellg();assert(n%sizeof(T)==0);std::vector<T>x(n/sizeof(T));f.seekg(0);f.read((char*)x.data(),n);assert(f);return x;}
template<class T>void save(const std::string&p,const std::vector<T>&v){std::ofstream f(p,std::ios::binary);f.write((char*)v.data(),v.size()*sizeof(T));assert(f);}
const char*src=R"CLC(
kernel void classify(global const uint*w,uint nw,global uint*records){uint ix=get_global_id(0);if(ix>=nw)return;uint n=w[ix*42+1],nt=0,truth[256],anf[256];for(uint i=0;i<8;i++)nt+=w[ix*42+10+4*i]==2;
for(uint x=0;x<(1u<<n);x++){uint y=x;for(uint i=0;i<8;i++){uint b=ix*42+10+4*i,k=w[b],t=w[b+1],a=w[b+2],c=w[b+3];uint on=k==0?1:((y>>a)&1);if(k==2)on&=(y>>c)&1;y^=on<<t;}truth[x]=y;anf[x]=y;}
for(uint b=0;b<n;b++)for(uint x=0;x<(1u<<n);x++)if(x&(1u<<b))anf[x]^=anf[x^(1u<<b)];uint u=0,eligible=1,degree=0;for(uint x=1;x<(1u<<n);x++)if(anf[x]){uint d=popcount(x);degree=max(degree,d);if(d>2)eligible=0;if(d==2){if(u&&u!=anf[x])eligible=0;u=anf[x];}}
uint at=ix*516;records[at]=n;records[at+1]=nt;records[at+2]=eligible;records[at+3]=u;for(uint x=0;x<256;x++){records[at+4+x]=x<(1u<<n)?truth[x]:0;records[at+260+x]=x<(1u<<n)?anf[x]:0;}
}
)CLC";
std::string run(cl_device_id d,unsigned di,const std::string&input,const std::string&output){cl_int e;auto c=clCreateContext(nullptr,1,&d,nullptr,nullptr,&e);ck(e);auto q=clCreateCommandQueue(c,d,0,&e);ck(e);auto p=clCreateProgramWithSource(c,1,&src,nullptr,&e);ck(e);ck(clBuildProgram(p,1,&d,"-cl-std=CL1.2",nullptr,nullptr));auto k=clCreateKernel(p,"classify",&e);ck(e);std::ostringstream report;report<<"DEVICE "<<di<<' '<<info(d,CL_DEVICE_NAME)<<'\n';for(unsigned j=di*2;j<di*2+2;j++){auto w=read<uint32_t>(input+"/j"+std::to_string(j)+"-windows.bin");cl_uint n=w.size()/42;std::vector<uint32_t>r(n*516,0);auto wb=clCreateBuffer(c,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,w.size()*4,w.data(),&e);ck(e);auto rb=clCreateBuffer(c,CL_MEM_WRITE_ONLY,r.size()*4,nullptr,&e);ck(e);ck(clSetKernelArg(k,0,sizeof(wb),&wb));ck(clSetKernelArg(k,1,4,&n));ck(clSetKernelArg(k,2,sizeof(rb),&rb));size_t global=((n+63)/64)*64,local=64;ck(clEnqueueNDRangeKernel(q,k,1,nullptr,&global,&local,0,nullptr,nullptr));ck(clEnqueueReadBuffer(q,rb,CL_TRUE,0,r.size()*4,r.data(),0,nullptr,nullptr));unsigned eligible=0;for(unsigned i=0;i<n;i++)eligible+=r[i*516+2]!=0;save(output+"/j"+std::to_string(j)+"-classification.bin",r);report<<"CLOCK "<<j<<" windows="<<n<<" affine_or_single_output_direction_quadratic="<<eligible<<'\n';clReleaseMemObject(wb);clReleaseMemObject(rb);}clReleaseKernel(k);clReleaseProgram(p);clReleaseCommandQueue(q);clReleaseContext(c);return report.str();}
int main(int argc,char**argv){assert(argc==3);cl_uint np;ck(clGetPlatformIDs(0,nullptr,&np));std::vector<cl_platform_id>ps(np);ck(clGetPlatformIDs(np,ps.data(),nullptr));std::vector<cl_device_id>ids;for(auto p:ps){cl_uint n;auto e=clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,0,nullptr,&n);if(e==CL_DEVICE_NOT_FOUND)continue;ck(e);std::vector<cl_device_id>d(n);ck(clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,n,d.data(),nullptr));for(auto x:d)if(info(x,CL_DEVICE_NAME).find("B50")!=std::string::npos)ids.push_back(x);}assert(ids.size()==2);auto a=std::async(std::launch::async,run,ids[0],0,std::string(argv[1]),std::string(argv[2]));auto b=std::async(std::launch::async,run,ids[1],1,std::string(argv[1]),std::string(argv[2]));std::cout<<a.get()<<b.get()<<"BOTH_B50_UNCONDITIONAL_TRUTH_CLASSIFIED exhaustive_all_inputs=true\n";}
