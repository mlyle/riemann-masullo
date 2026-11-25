// Exact first-prime Riesz enclosures for Re chi, chi modulo 5 with chi(2)=i.
// Input is the rational-series table from quartic-mod-five-log-table.py.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>
using I = __int128_t;
using U = uint64_t;
static std::string dec(I v) {
  if (v < 0) return "-"+dec(-v);
  if (v == 0) return "0";
  std::string s;
  while (v) { s.push_back(char('0'+v%10)); v/=10; }
  std::reverse(s.begin(),s.end()); return s;
}
static U fourth(U j) { return j*j*j*j; }
int main(int argc, char** argv) {
  if (argc != 2) return 2;
  U J=std::stoul(argv[1]);
  if (J<1 || J>256) return 2;
  constexpr U bins=4096, scale=U(1)<<30, block=U(1)<<18;
  std::array<U,bins+1> lo{},hi{};
  for (U i=0;i<=bins;++i)
    if (!(std::cin>>lo[i]>>hi[i]) || hi[i]<lo[i] || hi[i]-lo[i]>2) return 2;
  U cutoff=fourth(J);
  std::vector<U> primes;
  for (U p=3;p*p<=cutoff;p+=2) {
    bool prime=true;
    for (U r:primes) {
      if (r*r>p) break;
      if (p%r==0) { prime=false; break; }
    }
    if (prime) primes.push_back(p);
  }
  I sumLo=0,sumHi=0,weightedLo=0,weightedHi=0;
  U j=1,total=0;
  auto report=[&](U until) {
    while (j<=J && fourth(j)<=until) {
      U x=fourth(j);
      std::cout<<j<<" "<<dec(x*sumLo-weightedLo)<<" "<<dec(x*sumHi-weightedHi)<<"\n";
      ++j;
    }
  };
  for (U a=3;a<=cutoff;a+=2*block) {
    U b=std::min(cutoff,a+2*block-2);
    std::vector<uint8_t> sieve((b-a)/2+1,1);
    for (U r:primes) {
      if (r*r>b) break;
      U m=std::max(r*r,((a+r-1)/r)*r);
      if (m%2==0) m+=r;
      for (;m<=b;m+=2*r) sieve[(m-a)/2]=0;
    }
    for (U k=0;k<sieve.size();++k) {
      if (!sieve[k]) continue;
      U p=a+2*k;
      report(p);
      ++total;
      if (p%5!=1 && p%5!=4) continue;
      U e=63-__builtin_clzll(p), base=U(1)<<e;
      U m=p*bins/base, i=m-bins, r=p*bins-base*m;
      // p = 2^e (1+i/bins)(1+u), u = r/(base*m) <= 1/bins.
      U lin=r*scale/(base*m);
      I l=I(e*lo[bins]+lo[i]+lin)-I(scale/(2*bins*bins));
      I h=I(e*hi[bins]+hi[i]+lin+1);
      if (p%5==4) { I t=l; l=-h; h=-t; }
      sumLo+=l; sumHi+=h; weightedLo+=p*l; weightedHi+=p*h;
    }
  }
  report(cutoff);
  std::cerr<<"primes through cutoff "<<total+(cutoff>=2)<<"\n";
}
