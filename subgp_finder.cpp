#include<iostream>
#include<cstdio>
#include<cstring>
#include<vector>
#include<set>
#include<unordered_set>
#include<map>
#include<bitset>
#include<algorithm>

#include<assert.h>
using namespace std;

template<typename Functor>
struct fix_type {
    Functor functor;

    template<typename... Args>
    decltype(auto) operator()(Args&&... args) const&
    { return functor(functor, std::forward<Args>(args)...); }

    /* other cv- and ref-qualified overloads of operator() omitted for brevity */
};

template<typename Functor>
fix_type<typename std::decay<Functor>::type> fix(Functor&& functor)
{ return { std::forward<Functor>(functor) }; }

/***************************************************************************************/

const int MAXG=360;

struct gp{
	int n;
	int O[MAXG][MAXG];
}G;

struct subgp{
	unordered_set<int> c;
	bool maximal;
	int order(){
		return c.size();
	}
}trivial_subgp,full_subgp,tmp_subgp;

void generate_tmp_subgp(int newc){
	unordered_set<int> new_elem_p,new_elem_q; new_elem_p.insert(newc);
	tmp_subgp.c.insert(newc);
	for(;;){
		new_elem_q.clear();
		for(int i:tmp_subgp.c)
			for(int j:new_elem_p){
				if(tmp_subgp.c.find(G.O[i][j])==tmp_subgp.c.end()) new_elem_q.insert(G.O[i][j]);
				if(tmp_subgp.c.find(G.O[j][i])==tmp_subgp.c.end()) new_elem_q.insert(G.O[j][i]);
			}
		if(!new_elem_q.empty()){
			new_elem_p=new_elem_q;
			for(int j:new_elem_p) tmp_subgp.c.insert(j);
		}else break;
	}
}

struct subgps{
	vector<subgp> a;
	void print(){
		map<int,int> order_distribution;
		for(subgp H:a)
			++order_distribution[H.order()];
		for(auto it:order_distribution)
			cout<<"Order of subgroups:"<<it.first<<"     number of subgroups:"<<it.second<<"\n";
		cout<<"Total: "<<a.size()<<"\n";
		
		map<int,int> order_distribution_maxl;
		int maxl=0;
		for(subgp H:a) if(H.maximal){
			++maxl;
			++order_distribution_maxl[H.order()];
		}
		for(auto it:order_distribution_maxl)
			cout<<"Order of maximal subgroups:"<<it.first<<"     number of maximal subgroups:"<<it.second<<"\n";
		cout<<"Total maximal subgroups: "<<maxl<<"\n";
	}
};

subgps subgp_finder(){
	trivial_subgp.c.insert(0); trivial_subgp.maximal=true;
	for(int i=0;i<G.n;i++) full_subgp.c.insert(i); full_subgp.maximal=false;
	
	subgps ret;
	vector<subgp> bfsq; bfsq.push_back(trivial_subgp); int i=0,j=1;
	while(i!=j){
		for(int k=0;k<G.n;k++) if(bfsq[i].c.find(k)==bfsq[i].c.end()){
			tmp_subgp=bfsq[i]; generate_tmp_subgp(k);
			if(tmp_subgp.c==full_subgp.c) continue;
			else bfsq[i].maximal=false;
			bool caught=false;
			for(int l=0;l<j;l++)
				if(bfsq[l].c==tmp_subgp.c){
					caught=true;
					break;
				}
			if(!caught){
				bfsq.push_back(tmp_subgp); bfsq[j].maximal=true; ++j;
			}
		}
		ret.a.push_back(bfsq[i]);
		++i;
		if(i%10==0) cerr<<i<<" subgroups have been caught.\n";
	}
	ret.a.push_back(full_subgp);
	return ret;
}

gp alternating_group(int k){
	auto factorial = fix([](auto&& self, int n) -> int { return n < 2 ? 1 : n * self(self, n - 1); });
	
	vector<vector<int>> perms;
	vector<int> perm,c;
	for(int i=0;i<k;i++) perm.push_back(i);
	perms.push_back(perm);
	
	for(int i=1;i<factorial(k);i++){
		int last_inc;
		for(int j=k-1;j>=1;j--)
			if(perm[j-1]<perm[j]){
				last_inc=j-1;
				break;
			}
		int last_bigger;
		for(int j=last_inc+1;j<k;j++)
			if(perm[j]>perm[last_inc])
				last_bigger=j;
		swap(perm[last_inc],perm[last_bigger]);
		sort(perm.begin()+last_inc+1,perm.end());
		// count reverse pairs
		int rev_cnt=0;
		for(int ii=0;ii<k;ii++)
			for(int jj=ii+1;jj<k;jj++)
				if(perm[ii]>perm[jj])
					++rev_cnt;
		if(rev_cnt%2==0)
			perms.push_back(perm);
	} 
	
	assert(perms.size() == factorial(k)/2);
	//for(int i=0;i<perms.size();i++){
	//	for(int j=0;j<k;j++) cerr<<perms[i][j];
	//	cerr<<"\n";
	//}
	
	gp retG;
	retG.n=factorial(k)/2;
	for(int s=0;s<retG.n;s++)
		for(int t=0;t<retG.n;t++){
			for(int i=0;i<k;i++) perm[i]=perms[t][perms[s][i]];
			retG.O[s][t]=find(perms.begin(),perms.end(),perm)-perms.begin();
		}
	return retG;
}

void Dunfield_Thurston_2007_upper_bound(int g,subgps subgps_of_G){
	double ans=0.0;
	for(subgp H:subgps_of_G.a)
		if(H.maximal)
			ans+=1.0/pow((double)G.n/(double)H.order(),g);
	cout.precision(6);
	cout<<fixed<<"Dunfield_Thurston_2007_upper_bound = "<<ans<<"\n";
}

int main(){
	G=alternating_group(6);
	subgps subgps_of_G=subgp_finder();
	subgps_of_G.print();
	Dunfield_Thurston_2007_upper_bound(2,subgps_of_G);
}

