#include <array>
#include <vector>
#include <queue>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <cassert>
struct Cube {uint16_t truth; int degree,neg;};
int main(int argc,char**argv){assert(argc==2);std::array<Cube,81> cubes;
 for(int i=0;i<81;i++){int v=i,mask=0,value=0,d=0,neg=0;for(int b=0;b<4;b++){int t=v%3;v/=3;if(t){mask|=1<<b;d++;if(t==2)value|=1<<b;else neg++;}}uint16_t truth=0;for(int x=0;x<16;x++)if((x&mask)==value)truth|=1<<x;cubes[i]={truth,d,neg};}
 std::ofstream out(argv[1],std::ios::binary);assert(out);int tables=0;
 for(int spec=0;spec<61;spec++){int pk=0,pn=0,lambda=-1;if(spec<6){static int ks[]={0,1,1,2,2,2},ns[]={0,0,1,0,1,2};pk=ks[spec];pn=ns[spec];}else lambda=4+2*(spec-6);
  std::array<int,81> weights;for(int i=0;i<81;i++){int k=pk+cubes[i].degree;weights[i]=lambda>=0?lambda+4*cubes[i].degree+2*cubes[i].neg:(k<=2?1:4*k-8)+2*(pn+cubes[i].neg);assert(weights[i]>0);}
  std::vector<int> dist(65536,1000000);std::vector<uint8_t> choice(65536,255);using Node=std::pair<int,int>;std::priority_queue<Node,std::vector<Node>,std::greater<Node>> queue;dist[0]=0;queue.push({0,0});
  while(!queue.empty()){auto[d,t]=queue.top();queue.pop();if(d!=dist[t])continue;for(int i=0;i<81;i++){int nt=t^cubes[i].truth,nd=d+weights[i];if(nd<dist[nt]){dist[nt]=nd;choice[nt]=i;queue.push({nd,nt});}}}
  for(int t=0;t<65536;t++){int at=t,sum=0,steps=0;uint16_t got=0;while(at){int c=choice[at];assert(c<81);got^=cubes[c].truth;at^=cubes[c].truth;sum+=weights[c];assert(++steps<64);}assert(got==t&&sum==dist[t]);}
  out.write(reinterpret_cast<char*>(choice.data()),choice.size());tables++;std::cerr<<"ESOP4_TABLE_PASS spec="<<spec<<" lambda="<<lambda<<" truths=65536\n";
 }
 assert(out);std::cerr<<"ESOP4_ALL_PASS tables="<<tables<<" exact_truths="<<tables*65536<<" bytes="<<tables*65536<<"\n";
}
