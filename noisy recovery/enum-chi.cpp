// DLP Recovery Algorithm (as described in Section 7 of the paper)
//
// Usage:
//
// * Install NTL and boost::math
//
// * Compile with
//   g++ enum-chi.cpp -Ofast -lntl -lpthread -lgmp -g -lboost_math_c99 -o chi -march=native -mtune=native
//
// * Execute as ./chi <file> in one of the subdirectories containing
//   key files (sk_512.dat, hprime_512.dat), where the <file> command line
//   argument is one of data*.dat file in the same subdirectory (these
//   files correspond to aggregated data from DLP timing traces).
//

#include<stdio.h>
#include<stdlib.h>
#include<cstdio>
#include<algorithm>
#include<cmath>
#include<cstdlib>
#include<tuple>
#include<vector>
#include<ctime>
#include<NTL/matrix.h>
#include<NTL/ZZ.h>
#include<NTL/RR.h>
#include<NTL/vec_ZZ.h>
#include<NTL/vec_RR.h>
#include<NTL/mat_ZZ.h>
#include<NTL/mat_RR.h>
#include<iostream>
#include<time.h>
#include<math.h>
#include<fstream>
#include<time.h>
#include<boost/math/distributions/chi_squared.hpp>
#include<cstdint>

using namespace std;
NTL_CLIENT;

typedef float Real;
typedef pair<Real,Real> DF;
	
long q = 1031;
const int B=200;
const Real K=6;

vector<Real> gsnorm,gssigma;
vector<int> target;


struct State{
	vector<Real> a,s,error;
	DF df() const{
		Real  d= a[0],f=0;
		for(int j = 0; j <a.size()-1; j++)
		{
			d -= s[j] * a[j+1];
			f += s[s.size()-j-1] * a[j+1];
		}
		return make_pair(d,f);
	}
	void update(int an,DF df){
		Real d,f;
		d=df.first;
		f=df.second;
		Real fact=(an-f)/d;
		s.push_back(fact);
		for(int i=0;i<a.size()-1-i;i++){
			Real olds=s[i];
			s[i]-=fact*s[a.size()-2-i];
			if (i<a.size()-2-i)
				s[a.size()-2-i]-=fact*olds;
		}
		a.push_back(an);
	}
};

inline Real sqr(Real x){
	return x*x;
}

// weight function
inline Real rho(Real x, Real sx)
{
	Real Sigma1 = sx*sx;
	return x * x / Sigma1;
}

long nbUpd=0,nbTest=0;

vector<Real> bounds;
vector<int> hprime; // 1/(1+h*conj(h))

// Check that A*hprime is small (so a is a solution)

bool check(const vector<Real> &a){ 
	int n=hprime.size();
//	printf("%d %d\n",n,hprime[0]);
	for(int i=1;i<n;i++){
		int value=0;
		for(int j=0;j<n;j++)
			value+=(i-j<0?-1:1)*(j<n/2 ? int(a[j]) : -int(a[n-j]))*hprime[(i-j+n)%n];
		value=((value%q)+q)%q;
//		printf("%d %d\n",i,value);
		if(min(value,q-value)>B)
			return false;
	}
	return true;
}

// Check that A*hprime is small (so a is a solution)
bool checkConj(vector<Real> a){
	if(check(a))
		return true;
	for(int i=1;i<a.size();i+=2)
		a[i]*=-1;
	return check(a);
}

// Pruned search

bool searchRec(const State &s){
	const int n=s.a.size();
	if(n==hprime.size()/2){
		nbTest++;
		bool eq=checkConj(s.a);
		if(eq){
			printf("%f\n",s.error.back());
			puts("success");
		}
		return eq;
	}
	DF df=s.df();
	Real prod=s.a[0]-df.first;
	for(int an=n==1? 0 : -B;an<=B;an++){
		Real x=s.a[0]-sqr(an-df.second)/df.first-prod-gsnorm[n];
		if (abs(x)<K*gssigma[n]){
			Real val=rho(x,gssigma[n]);
			Real tot=s.error.back()+val;
			bool ok=tot<=bounds[n];
			for(int i=n-1;ok && i>=0;i--)
				ok=(tot-s.error[i])<bounds[n-i];
			if(ok){
				State nouv=s;
				nbUpd++;
				nouv.update(an,df);
				nouv.error.push_back(tot);
				if(searchRec(nouv))
					return true;
			}
		}
	}
	return false;
}


void search(){
	double tau=0.2;
	State s;
	s.a.push_back(round(gsnorm[0]));
	s.error.push_back(0);
	double incr=.7;
	long ancNbUpd=0;
	bounds.insert(bounds.begin(),hprime.size()/2,0.);
	while(1){
		for (int d=1;d<hprime.size()/2;d++){
			boost::math::chi_squared chi(d);
			bounds[d]=boost::math::quantile(boost::math::complement(chi,tau/sqrt(d)));
		}
		printf("tau=%f incr=%.1f ",tau,incr);
		fflush(stdout);
		if(searchRec(s))
			break;
		printf("nbUpd=%ld nbTest=%ld\n",nbUpd,nbTest);
//		if(ancNbUpd>1000)	incr*=nbUpd/ancNbUpd>5 ? 1.5 : (nbUpd/ancNbUpd<1.5 ? 1.5 : 1);
		ancNbUpd=nbUpd;
		nbUpd=0;
		nbTest=0;
		tau*=incr;
	}
	printf("nbUpd=%ld nbTest=%ld\n",nbUpd,nbTest);
}


void test(char *file)
{
	printf("%s\n",file);
	RR::SetPrecision(53);

	long n = 512;
	long q = 1031;
	

	char fname[80];
	sprintf(fname, "sk_%d.dat", n);
	ifstream fin_sk(fname);
	
	vec_ZZ sk;
	fin_sk >> sk;

	vector<int> f(n), g(n);
	for(int i = 0; i < n; i++)
	{
		f[i] = to_int(sk(i+1)); 
		g[i] = to_int(sk(i+n+1));
	}

	// load the approximate AR
	ifstream fin(file);
	vector<long> data1(n/2), data2(n/2);
	for(long i = 0; i < n/2; i++)
		fin >> data1[i];
	for(long i = 0; i < n/2; i++)
		fin >> data2[i];
	long total_trial;
	fin >> total_trial;
	
	sprintf(fname, "hprime_%d.dat", n);
	ifstream fin_hp(fname);
	vec_ZZ hp;
	fin_hp>>hp;
	for(int i=0;i<n;i++)
		hprime.push_back(to_int(hp(i+1)));


	vector<Real> AR1(n/2),AR2(n/2);
	for(long i = 0; i < n/2; i++)
		AR1[i] = (total_trial+0.) /data1[i];
	for(long i = 0; i < n/2; i++)
		AR2[i] = (total_trial+0.) /data2[i];
	vector<int> klist1(n/2),klist2(n/2);
	klist1[0] = klist2[n/2-1]=3;
	for(long i = 0; i < n/2-1; i++)
	{
		klist1[i+1]=klist1[i];
		if(AR1[i+1] * 1.1 < AR1[i])
		{
			klist1[i+1]++;
			printf("%d %f %f\n",i,AR1[i+1]);
		}
		klist2[n/2-i-2]=klist2[n/2-i-1];
		if(AR2[n/2-i-2] * 1.1 < AR2[n/2-i-1])
		{
			klist2[n/2-i-2]++;
			printf("%d %f %f\n",i,AR2[i+1]);
		}
	}
	cout<<endl;

	
	
	double swidth = 2.2358 * 32; // Signatures are with exactly this sigma
	double sigma0 = 1/sqrt(2*log(2));
	double var=0;
	for(int i = 0; i < n/2; i++)
	{
		Real g1=g1=swidth / (sigma0 * AR1[i] * klist1[i]),g2=q / swidth * sigma0 * AR2[i] * klist2[i];
		Real s1=sqrt((1.-AR1[i])/total_trial),s2=sqrt((1.-AR2[i])/total_trial);
		Real l=s1*s1/(s1*s1+s2*s2);
		gsnorm.push_back(pow(l*g2+(1-l)*g1,2));
		gssigma.push_back(gsnorm.back()*2*s1*s2/sqrt(s1*s1+s2*s2));
		printf("%.1f ",-log(gssigma.back())/log(2));
	}
	cout << endl;
	cout << "Obtained GS-norms" << endl;

	target.insert(target.begin(),n,0.);
	for(int i=0;i<n;i++)
		for(int j=0;j<n;j++){
			int pos=(i+2*n-j)%(2*n);
			target[pos%n]+=(pos>=n ? -1:1)*(f[i]*f[j]+g[i]*g[j]);
		}

	if(target[1]<0){
		for(int j = 1; j < n/2; j+=2)
		{
			target[j] *= -1;
		}
	}
	cout<<"Target =";
	for(int i=0;i<n/2;i++)
		cout<<target[i]<<" ";
	cout<<endl;
	State correct;
	correct.a.push_back(target[0]);
	correct.error.push_back(0);
	printf("Errors :");
	for(int i=1;i<n/2;i++){
		DF df=correct.df();
		correct.update(target[i],df);
		correct.error.push_back(correct.error.back()+rho(correct.df().first-gsnorm[i],gssigma[i]));
		printf("%.1f ",abs((correct.df().first-gsnorm[i])/gssigma[i]));
	}
	printf("\n Tau err=:");
	bounds.push_back(0);
	Real tau=5;
	for(int l=1;l<n/10;l++){
		Real maxi=0;
		for(int beg=0;beg<n/2-l;beg++){
			maxi=max(maxi,correct.error[beg+l]-correct.error[beg]);
//			printf("%f %d\n",beg,correct.error[beg+l]-correct.error[beg],beg);
		}
		bounds.push_back(maxi+1e-6);
		boost::math::chi_squared chi(l);
		Real v=boost::math::cdf(boost::math::complement(chi,maxi));
		tau=min(tau,(Real)(v*sqrt(l)));
		printf("%.6f (%.3f)",v*sqrt(l),maxi);
	}
	puts("");
	printf("Tau=%f\n",tau);

	// Full recovery
	clock_t t = clock();
		
	cout << "Go solving" << endl;
	search();

	cout << "full-recovery time = " << Real(clock() - t) / CLOCKS_PER_SEC << "s" << endl;
}

int main(int argc,char **argv)
{
	test(argv[1]);
	return 0;
}
