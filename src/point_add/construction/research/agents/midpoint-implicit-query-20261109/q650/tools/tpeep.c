// tpeep: exact peephole on an ECDSA-Fail raw trace (u16le records kind,a,b,c; EMPTY=65535) + span sidecar.
// Deletes pairs of identical unconditional X/CX/CCX records (kinds 6/8/13 with no classical operand) when every live
// record between them commutes with them. Rules (q = quantum wire):
//   X-type gates g,h commute iff target(g) not in controls(h) and target(h) not in controls(g).
//   Z(q) (7), CZ(q1,q2) (9): diagonal -> block a candidate iff its target is q / q1 / q2.
//   hmr(q) (12): blocks any candidate touching q.  Classically controlled X/CX (6/8 with bit): block like the gate,
//   never matched.  Classical-only ops (3,4,5) touch no qubit: transparent.  cond begin/end (15/16) and all other
//   kinds: full barrier (pairs never cancel across a conditional boundary).
// Usage: tpeep IN.u16le IN.tsv OUT.u16le OUT.tsv [W=4096]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define E 65535u
typedef struct {uint64_t key; uint64_t op; uint16_t t,a,b; uint8_t kind;} Live; // kind: 0 gate,1 diag(t,a),2 hmr(t)
static Live *L; static size_t nl=0, cap;
static uint8_t *del; // bitmap
#define SETDEL(i) (del[(i)>>3]|=(uint8_t)(1u<<((i)&7)))
#define ISDEL(i) (del[(i)>>3]>>((i)&7)&1)
int main(int argc,char**argv){
  if(argc<5){fprintf(stderr,"usage: tpeep IN.u16le IN.tsv OUT.u16le OUT.tsv [W]\n");return 2;}
  size_t W=argc>5?strtoull(argv[5],0,10):4096; cap=4*W+16; L=malloc(cap*sizeof(Live));
  FILE*f=fopen(argv[1],"rb"); if(!f){perror(argv[1]);return 1;}
  fseeko(f,0,SEEK_END); uint64_t N=ftello(f)/8; fseeko(f,0,SEEK_SET);
  del=calloc(N/8+1,1); const size_t CH=1<<22; uint16_t*buf=malloc(CH*8); uint64_t op=0,removed=0;
  size_t got;
  while((got=fread(buf,8,CH,f))>0){
    for(size_t r=0;r<got;r++,op++){uint16_t k=buf[4*r],a=buf[4*r+1],b=buf[4*r+2],c=buf[4*r+3];
      uint16_t A,B,T; int gate=0,blk=-1;
      if(k==6){ if(b==E){A=E;B=E;T=a;gate=1;} else {A=E;B=E;T=a;blk=0;} }
      else if(k==8){ if(c==E){A=a;B=E;T=b;gate=1;} else {A=a;B=E;T=b;blk=0;} }
      else if(k==13){A=a;B=b;T=c;gate=1;}
      else if(k==7){A=E;B=E;T=a;blk=1;}
      else if(k==9){A=b;B=E;T=a;blk=1;}
      else if(k==12){A=E;B=E;T=a;blk=2;}
      else if(k==3||k==4||k==5){continue;}
      else {nl=0;continue;}
      if(gate){ uint64_t key=((uint64_t)A<<32)|((uint64_t)B<<16)|T; long hit=-1; size_t steps=0;
        for(long j=(long)nl-1;j>=0&&steps<W;j--,steps++){Live*y=&L[j];
          if(y->kind==0&&y->key==key){hit=j;break;}
          if(y->kind==0){ if(y->t==A||y->t==B||T==y->a||T==y->b) break; }
          else if(y->kind==1){ if(T==y->t||T==y->a) break; }
          else { if(T==y->t||A==y->t||B==y->t) break; } }
        if(hit>=0){ SETDEL(L[hit].op); SETDEL(op); removed+=2; memmove(&L[hit],&L[hit+1],(nl-hit-1)*sizeof(Live)); nl--; continue; }
        if(nl==cap){ memmove(L,L+(nl-2*W),2*W*sizeof(Live)); nl=2*W; }
        L[nl].key=key;L[nl].op=op;L[nl].t=T;L[nl].a=A;L[nl].b=B;L[nl].kind=0;nl++;
      } else { // blocker: a classically controlled gate is pushed as a never-matching gate
        if(nl==cap){ memmove(L,L+(nl-2*W),2*W*sizeof(Live)); nl=2*W; }
        L[nl].key=~0ull;L[nl].op=op;L[nl].t=T;L[nl].a=A;L[nl].b=B;L[nl].kind=(uint8_t)blk;nl++; }
    }
  }
  fprintf(stderr,"tpeep: ops %llu removed %llu (%.3f%%) W=%zu\n",(unsigned long long)op,(unsigned long long)removed,100.0*removed/op,W);
  if(getenv("TPEEP_DUMP")){FILE*dd=fopen(getenv("TPEEP_DUMP"),"w");for(uint64_t i=0;i<N;i++)if(ISDEL(i))fprintf(dd,"%llu\n",(unsigned long long)i);fclose(dd);}
  // pass 2: write kept records
  fseeko(f,0,SEEK_SET); FILE*o=fopen(argv[3],"wb"); if(!o){perror(argv[3]);return 1;}
  uint16_t*ob=malloc(CH*8); op=0;
  while((got=fread(buf,8,CH,f))>0){size_t m=0;for(size_t r=0;r<got;r++,op++) if(!ISDEL(op)){memcpy(ob+4*m,buf+4*r,8);m++;} if(m&&fwrite(ob,8,m,o)!=m){perror("write");return 1;}}
  fclose(o); fclose(f);
  // prefix counts of deletions per 64-op word for span remap
  uint64_t nw=N/64+1; uint64_t*pre=malloc((nw+1)*8); pre[0]=0;
  for(uint64_t w=0;w<nw;w++){uint64_t x=0; memcpy(&x,del+8*w,(8*w+8<=N/8+1)?8:(N/8+1-8*w)); pre[w+1]=pre[w]+__builtin_popcountll(x);}
  #define DELBEFORE(i) (pre[(i)>>6] + ((i)&63 ? __builtin_popcountll(({uint64_t x=0; memcpy(&x,del+8*((i)>>6),(8*((i)>>6)+8<=N/8+1)?8:(N/8+1-8*((i)>>6))); x;}) & ((1ull<<((i)&63))-1)) : 0))
  FILE*ti=fopen(argv[2],"r"),*to=fopen(argv[4],"w"); if(!ti||!to){perror("tsv");return 1;}
  char line[4096]; uint64_t rows=0;
  while(fgets(line,sizeof line,ti)){ char*p=line; char*fld[8]; int nf=0; fld[nf++]=p;
    for(;*p&&nf<8;p++) if(*p=='\t'){*p=0;fld[nf++]=p+1;}
    if(nf<4){fputs(line,to);continue;}
    uint64_t s=strtoull(fld[2],0,10),e=strtoull(fld[3],0,10);
    uint64_t s2=s-DELBEFORE(s), e2=e-(e>=N?pre[nw]:DELBEFORE(e));
    fprintf(to,"%s\t%s\t%llu\t%llu",fld[0],fld[1],(unsigned long long)s2,(unsigned long long)e2);
    for(int i=4;i<nf;i++) fprintf(to,"\t%s",fld[i]);
    if(nf<=4) fputc('\n',to); rows++; }
  fclose(ti); fclose(to);
  fprintf(stderr,"tpeep: wrote %llu ops, %llu span rows\n",(unsigned long long)(N-removed),(unsigned long long)rows);
  return 0;
}
