/* Monte Carlo toy for the PIL + SVL + (S3) envelope (Theorem R chain), k = 1 and k = 2.
   Slots j=1..N at positions X+j, box jitter of width H, adaptive decision policies.
   Rational "primes" p<=19 (tails 19-smooth). Good(<u) := Eu_s(u') <= A for all u' <= u.
   Counts ordered k-tuples of distinct elements in J=[z,z+delta] by skeleton (E_P, runs). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdint.h>

#ifndef NS
#define NS 1500
#endif
#define N NS
#ifndef XX
#define XX 10.0
#endif
#define X XX
#define H 4.0
static double rat[8] = {2,3,5,7,0,0,0,0}; static int NR=4;
static double smooth[200000]; static int nsmooth = 0;
static uint64_t rs = 88172645463325252ULL;
static double urand(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return (rs>>11)*(1.0/9007199254740992.0); }
static int cmpd(const void*a,const void*b){ double x=*(double*)a,y=*(double*)b; return (x>y)-(x<y); }
static void gen_smooth(double lim){
  /* all 19-smooth integers <= lim */
  double st[64]; int idx[64]; int sp=0; (void)st; (void)idx;
  /* simple BFS */
  nsmooth=0; smooth[nsmooth++]=1;
  for(int i=0;i<NR;i++){ int cur=nsmooth; for(int a=0;a<cur;a++){ double v=smooth[a]; while((v*=rat[i])<=lim) smooth[nsmooth++]=v; } }
  qsort(smooth,nsmooth,sizeof(double),cmpd); (void)sp;
}
static int lower_idx(double v){ int lo=0,hi=nsmooth; while(lo<hi){int m=(lo+hi)/2; if(smooth[m]<v) lo=m+1; else hi=m;} return lo; }

typedef struct { int ncol; int slot[4]; int ex[4]; } Elt; /* jittered factorisation, slots ascending */
static Elt elts[4096]; static int nelts;
static int nslot_dec; static int dslot[N+2]; static double dval[N+2];

static void add_elt(int nc,const int*sl,const int*ex){
  if(nelts>=4096) return; Elt*e=&elts[nelts++]; e->ncol=nc; for(int i=0;i<nc;i++){e->slot[i]=sl[i];e->ex[i]=ex[i];}
}
/* enumerate products M of decided primes (multisets, slots ascending) with M <= zhi, and tails */
static double zlo_g, zhi_g;
static void dfs(int start,double M,int nc,int*sl,int*ex){
  if(nc>0){
    int i=lower_idx(zlo_g/M);
    while(i<nsmooth && smooth[i]*M<=zhi_g){ add_elt(nc,sl,ex); i++; }
  }
  if(nc>=3) return;
  for(int a=start;a<nslot_dec;a++){
    double q=dval[a]; if(M*q>zhi_g) continue;
    double MM=M; int e=0;
    while(MM*q<=zhi_g){ MM*=q; e++; sl[nc]=dslot[a]; ex[nc]=e; dfs(a+1,MM,nc+1,sl,ex); }
  }
}

/* skeleton tallies */
#define MAXK 64
typedef struct { int k; int EP[4]; int runs; double sum; } Tally; /* runs: for k=2: 2 => (2), 11 => (1,1) */
static Tally tal[MAXK]; static int ntal=0;
static void tally(int k,const int*EP,int runs,double w){
  for(int i=0;i<ntal;i++){ if(tal[i].k==k && tal[i].runs==runs && !memcmp(tal[i].EP,EP,sizeof(int)*(k*k))){ tal[i].sum+=w; return; } }
  if(ntal<MAXK){ tal[ntal].k=k; memset(tal[ntal].EP,0,sizeof(tal[ntal].EP)); memcpy(tal[ntal].EP,EP,sizeof(int)*k*k); tal[ntal].runs=runs; tal[ntal].sum=w; ntal++; }
}

static void classify_pair(const Elt*a,const Elt*b){
  /* columns: union of slots */
  int cols[8], nc=0;
  for(int i=0;i<a->ncol;i++) cols[nc++]=a->slot[i];
  for(int i=0;i<b->ncol;i++){ int s=b->slot[i],f=0; for(int j=0;j<nc;j++) if(cols[j]==s) f=1; if(!f) cols[nc++]=s; }
  /* sort ascending (decision order earliest first) */
  for(int i=0;i<nc;i++) for(int j=i+1;j<nc;j++) if(cols[j]<cols[i]){int t=cols[i];cols[i]=cols[j];cols[j]=t;}
  int E[2][8];
  for(int j=0;j<nc;j++){ E[0][j]=0;E[1][j]=0;
    for(int i=0;i<a->ncol;i++) if(a->slot[i]==cols[j]) E[0][j]=a->ex[i];
    for(int i=0;i<b->ncol;i++) if(b->slot[i]==cols[j]) E[1][j]=b->ex[i]; }
  /* greedy pivots latest first */
  int piv[8], np=0, vx=0, vy=0; int ispiv[8]={0};
  for(int j=nc-1;j>=0;j--){
    int ex=E[0][j], ey=E[1][j];
    if(np==0){ ispiv[j]=1; piv[np++]=j; vx=ex; vy=ey; }
    else if(np==1){ if(ex*vy-ey*vx!=0){ ispiv[j]=1; piv[np++]=j; } }
  }
  if(np!=2) return; /* not rank-full */
  /* pivots in decision order earliest first: piv[1] < piv[0] */
  int pe=piv[1], pl=piv[0];
  int EP[4]={E[0][pe],E[0][pl],E[1][pe],E[1][pl]}; /* rows x (earliest, latest) */
  int freebetween=0; for(int j=pe+1;j<pl;j++) if(!ispiv[j]) freebetween=1;
  int runs = freebetween? 11 : 2;
  tally(2,EP,runs,1.0);
}

int main(int argc,char**argv){
  int policy=atoi(argv[1]); double Afac=atof(argv[2]); long nsamp=atol(argv[3]); double delta=atof(argv[4]);
  rs ^= (uint64_t)(policy*1000003 + (int)(Afac*1000) + 17);
  double zlo=atof(argv[5]), zhi=atof(argv[6]);
  gen_smooth(zhi+delta+1);
  double Er=1; for(int i=0;i<NR;i++) Er/= (1-1/rat[i]);
  /* max possible Eu: all slots decided at lowest possible values */
  double Emax=Er; for(int j=1;j<=N;j++) Emax/= (1-1/(X+j-H/2));
  double A = Afac*Emax; if(A<Er) A=Er;
  double goodcount=0;
  for(long it=0;it<nsamp;it++){
    nslot_dec=0; double Eu=Er; int good=1; double lastU=0.5; int burst=0;
    for(int j=1;j<=N;j++){
      int D;
      switch(policy){
        case 0: D=1; break;
        case 1: D = urand()<0.5; break;
        case 2: D = (lastU<0.5) || (j%3==0); break;           /* depends on last offset */
        case 3: if(burst>0){D=1;burst--;} else D = urand()<0.3; break; /* bursty, adaptive below */
        default: D=1;
      }
      if(D){ double U=urand(); double q=X+j+H*(U-0.5); dslot[nslot_dec]=j; dval[nslot_dec]=q; nslot_dec++;
             if(Eu>A) good=0; Eu/= (1-1/q); lastU=U; if(policy==3 && U<0.4) burst=3; }
      /* good event checks Eu_s(u) for u = j+1 */
      if(Eu>A) good=0;
    }
    if(!good) continue;
    goodcount+=1;
    double z = zlo + (zhi-zlo)*urand();
    zlo_g=z; zhi_g=z+delta; nelts=0;
    int sl[4],ex[4]; dfs(0,1.0,0,sl,ex);
    for(int i=0;i<nelts;i++){
      /* k=1: latest jittered prime exponent */
      int EP1[1]={elts[i].ex[elts[i].ncol-1]}; tally(1,EP1,1,1.0);
      for(int j=0;j<nelts;j++) if(j!=i) classify_pair(&elts[i],&elts[j]);
    }
  }
  double tau1=X+1-H/2, tau2=X+2-H/2, theta=1.0;
  printf("policy=%d Afac=%.3f A=%.4f Er=%.4f Emax=%.4f nsamp=%ld P(good)=%.4f delta=%.2f\n",policy,Afac,A,Er,Emax,nsamp,goodcount/nsamp,delta);
  for(int i=0;i<ntal;i++){
    double est=tal[i].sum/nsamp, env;
    if(tal[i].k==1){ int e=tal[i].EP[0]; env=theta*delta*pow(tau1,-(e-1))*A; 
      printf("  k=1 e=%d            E[X;Good]=%.5g  envelope=%.5g  ratio=%.4f\n",e,est,env,est/env); }
    else { int*P=tal[i].EP; double det=fabs((double)P[0]*P[3]-(double)P[1]*P[2]);
      int s1=P[0]+P[2], s2=P[1]+P[3];
      double Fin = (tal[i].runs==2)? A*A : A*(A-Er);
      env=theta*theta*delta*delta/det*pow(tau1,-(s1-1))*pow(tau2,-(s2-1))*Fin;
      printf("  k=2 EP=[[%d,%d],[%d,%d]] runs=%s E[X;Good]=%.5g  envelope=%.5g  ratio=%.4f\n",P[0],P[1],P[2],P[3],tal[i].runs==2?"(2)  ":"(1,1)",est,env,est/env); }
  }
  return 0;
}
