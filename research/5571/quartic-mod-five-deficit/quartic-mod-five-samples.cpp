// Exact first-prime Riesz enclosures for the quartic character modulo 5, chi(2)=i.
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
  const bool complex_rows=argc==3 && std::string(argv[2])=="--complex";
  if (argc!=2 && !complex_rows) return 2;
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
  struct Moments {
    I low=0, high=0, weightedLow=0, weightedHigh=0;
    void add(U p,I l,I h) {
      low+=l; high+=h; weightedLow+=p*l; weightedHigh+=p*h;
    }
    void print(U x) const {
      std::cout<<" "<<dec(x*low-weightedLow)<<" "<<dec(x*high-weightedHigh);
    }
  };
  Moments real,imag;
  U j=1,total=0;
  auto report=[&](U until) {
    while (j<=J && fourth(j)<=until) {
      U x=fourth(j);
      std::cout<<j;
      real.print(x);
      if (complex_rows) imag.print(x);
      std::cout<<"\n";
      ++j;
    }
  };
  report(2);
  if (complex_rows && cutoff>=2) imag.add(2,lo[bins],hi[bins]);
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
      const U residue=p%5;
      if (residue==0 || (!complex_rows && residue!=1 && residue!=4)) continue;
      U e=63-__builtin_clzll(p), base=U(1)<<e;
      U m=p*bins/base, i=m-bins, r=p*bins-base*m;
      // p = 2^e (1+i/bins)(1+u), u = r/(base*m) <= 1/bins.
      U lin=r*scale/(base*m);
      I l=I(e*lo[bins]+lo[i]+lin)-I(scale/(2*bins*bins));
      I h=I(e*hi[bins]+hi[i]+lin+1);
      if (residue==3 || residue==4) { I t=l; l=-h; h=-t; }
      (residue==1 || residue==4 ? real : imag).add(p,l,h);
    }
  }
  report(cutoff);
  std::cerr<<"primes through cutoff "<<total+(cutoff>=2)<<"\n";
}
