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
kernel void classify(global const uint*w,uint nw,global int*records,global const uint*bank,uint nb){uint ix=get_global_id(0);if(ix>=nw)return;uint n=w[ix*42+1],truth[256];for(uint x=0;x<(1u<<n);x++){uint y=x;for(uint i=0;i<8;i++){uint b=ix*42+10+4*i,k=w[b],t=w[b+1],a=w[b+2],c=w[b+3];uint on=k==0?1:((y>>a)&1);if(k==2)on&=(y>>c)&1;y^=on<<t;}truth[x]=y;}int match=-1;for(uint b=0;b<nb;b++){if(bank[b*257]!=n)continue;uint ok=1;for(uint x=0;x<(1u<<n);x++)if(truth[x]!=bank[b*257+1+x]){ok=0;break;}if(ok){match=b;break;}}records[ix]=match;
}
)CLC";
std::string run(cl_device_id d,unsigned di,const std::string&input,const std::string&output){cl_int e;auto c=clCreateContext(nullptr,1,&d,nullptr,nullptr,&e);ck(e);auto q=clCreateCommandQueue(c,d,0,&e);ck(e);auto p=clCreateProgramWithSource(c,1,&src,nullptr,&e);ck(e);ck(clBuildProgram(p,1,&d,"-cl-std=CL1.2",nullptr,nullptr));auto k=clCreateKernel(p,"classify",&e);ck(e);std::ostringstream report;report<<"DEVICE "<<di<<' '<<info(d,CL_DEVICE_NAME)<<'\n';for(unsigned j=di*2;j<di*2+2;j++){auto w=read<uint32_t>(input+"/j"+std::to_string(j)+"-windows.bin");cl_uint n=w.size()/42;std::vector<int32_t>r(n,-1);auto wb=clCreateBuffer(c,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,w.size()*4,w.data(),&e);ck(e);auto rb=clCreateBuffer(c,CL_MEM_WRITE_ONLY,r.size()*4,nullptr,&e);ck(e);ck(clSetKernelArg(k,0,sizeof(wb),&wb));ck(clSetKernelArg(k,1,4,&n));ck(clSetKernelArg(k,2,sizeof(rb),&rb));auto bank=read<uint32_t>(input+"/bank.bin");cl_uint nb=bank.size()/257;auto bb=clCreateBuffer(c,CL_MEM_READ_ONLY|CL_MEM_COPY_HOST_PTR,bank.size()*4,bank.data(),&e);ck(e);ck(clSetKernelArg(k,3,sizeof(bb),&bb));ck(clSetKernelArg(k,4,4,&nb));size_t global=((n+63)/64)*64,local=64;ck(clEnqueueNDRangeKernel(q,k,1,nullptr,&global,&local,0,nullptr,nullptr));ck(clEnqueueReadBuffer(q,rb,CL_TRUE,0,r.size()*4,r.data(),0,nullptr,nullptr));unsigned eligible=0;for(unsigned i=0;i<n;i++)eligible+=r[i]>=0;save(output+"/j"+std::to_string(j)+"-matches.bin",r);report<<"CLOCK "<<j<<" windows="<<n<<" full_function_matches="<<eligible<<'\n';clReleaseMemObject(wb);clReleaseMemObject(rb);clReleaseMemObject(bb);}clReleaseKernel(k);clReleaseProgram(p);clReleaseCommandQueue(q);clReleaseContext(c);return report.str();}
int main(int argc,char**argv){assert(argc==3);cl_uint np;ck(clGetPlatformIDs(0,nullptr,&np));std::vector<cl_platform_id>ps(np);ck(clGetPlatformIDs(np,ps.data(),nullptr));std::vector<cl_device_id>ids;for(auto p:ps){cl_uint n;auto e=clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,0,nullptr,&n);if(e==CL_DEVICE_NOT_FOUND)continue;ck(e);std::vector<cl_device_id>d(n);ck(clGetDeviceIDs(p,CL_DEVICE_TYPE_GPU,n,d.data(),nullptr));for(auto x:d)if(info(x,CL_DEVICE_NAME).find("B50")!=std::string::npos)ids.push_back(x);}assert(ids.size()==2);auto a=std::async(std::launch::async,run,ids[0],0,std::string(argv[1]),std::string(argv[2]));auto b=std::async(std::launch::async,run,ids[1],1,std::string(argv[1]),std::string(argv[2]));std::cout<<a.get()<<b.get()<<"BOTH_B50_LIBRARY_MATCH_FINISHED all_inputs_compared=true\n";}
