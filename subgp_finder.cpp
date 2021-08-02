#include<iostream>
#include<cstdio>
#include<cstring>
#include<cmath> 
#include<vector>
#include<set>
#include<unordered_set>
#include<unordered_map>
#include<map>
#include<bitset>
#include<algorithm>

#include<time.h>
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


class hashFunctions{
public:
	size_t operator()(const pair<int,int>& s) const{
		size_t ret=s.first+s.second;
		return ret;
    }
	size_t operator()(const unordered_set<int>& s) const{
		size_t ret=0;
		for(auto x:s) ret+=x;
		return ret;
    }
};

/***************************************************************************************/

const int MAXgeneratingPairs=5000;

struct gp{
	int n;
	vector<vector<int>> O;
	vector<int> inv,idx_cyclicgroup,generator_cyclicgroup;
	unordered_set<pair<int,int>,hashFunctions> generatingPairs; // instead of storing generators, we save their cyclic groups 
	int tot_cyclicgroups;
	vector<unordered_set<int>> cyclicgroups;
	void resize(int nn){
		n=nn;
		O.resize(n,vector<int>(n));
		generatingPairs.clear();
	}
	void getinv(){
		inv.resize(n);
		for(int i=0;i<n;i++)
			for(int j=0;j<n;j++)
				if(O[i][j]==0){
					inv[i]=j;
					break;
				}
	}
	void getcyclicgroups(){
		tot_cyclicgroups=0;
		idx_cyclicgroup.resize(n);
		unordered_map<unordered_set<int>,int,hashFunctions> __cyclicgroups;
		for(int i=0;i<n;i++){
			int x=0;
			unordered_set<int> H;
			for(;;){
				H.insert(x);
				x=O[x][i];
				if(x==0) break;
			}
			if(!__cyclicgroups.count(H)){
				generator_cyclicgroup.push_back(i);
				cyclicgroups.push_back(unordered_set<int>{}); 
				__cyclicgroups[H]=tot_cyclicgroups++;
			}
			idx_cyclicgroup[i]=__cyclicgroups[H];
			cyclicgroups[idx_cyclicgroup[i]].insert(i);
		}
	}
	void insertgeneratingPairs(pair<int,int> gen){
		if(generatingPairs.size()<MAXgeneratingPairs)
			generatingPairs.insert(gen);
		else if(generatingPairs.size()==MAXgeneratingPairs)
			cerr<<"generatingPairs.size() = "<<MAXgeneratingPairs<<"\n"; 
	}
}G;

struct subgp{
	unordered_set<int> c;
	unordered_set<int> generators;
	bool maximal;
	int order(){
		return c.size();
	}
}trivial_subgp,full_subgp,tmp_subgp;

bool generate_tmp_subgp(int newc){
	unordered_set<int> new_elem_p,new_elem_q;
	tmp_subgp.generators.insert(newc);
	int pow_newc=newc,stage;
	while(tmp_subgp.c.find(pow_newc)==tmp_subgp.c.end()){
		new_elem_p.insert(pow_newc);
		tmp_subgp.c.insert(pow_newc);
		pow_newc=G.O[pow_newc][newc];
	}
	for(stage=1;;stage++){
		auto includes_all = [&](const unordered_set<int> & bigs,const int & g1,const int & g2){
			return (bigs.count(g1) && bigs.count(g2));
		};
		for(const pair<int,int> & gen:G.generatingPairs){
			for(int g1:G.cyclicgroups[gen.first]){
				for(int g2:G.cyclicgroups[gen.second]){
					if(includes_all(tmp_subgp.c,g1,g2)){
						stage=-1;
						break;
					}
				}
				if(stage==-1) break;
			}
			if(stage==-1) break;
		}
		if(tmp_subgp.c.size()*2>G.n)
			stage=-2;
		if(stage<0)
			break;
		new_elem_q.clear();
		auto c=tmp_subgp.c; 
		for(int i:c)
			for(int j:new_elem_p){
				if(tmp_subgp.c.insert(G.O[i][j]).second) new_elem_q.insert(G.O[i][j]);
				if(tmp_subgp.c.insert(G.O[j][i]).second) new_elem_q.insert(G.O[j][i]);
			}
		if(!new_elem_q.empty())
			new_elem_p=new_elem_q;
		else
			break;
	}
	if(stage==-1)
		return true;
	else if(stage==-2 || tmp_subgp.c.size()==G.n){
		auto elements2pairofcyclicgroups = [&](const unordered_set<int> & elems){
			int r1=-1,r2=-1;
			for(int g:elems){
				if(r1==-1) r1=G.idx_cyclicgroup[g];
				else r2=G.idx_cyclicgroup[g];
			}
			return make_pair(r1,r2);
		};
		if(tmp_subgp.generators.size()==2)
			G.insertgeneratingPairs(elements2pairofcyclicgroups(tmp_subgp.generators));
		return true;
	}else
		return false;
}

struct subgps{
	vector<pair<subgp,int>> a;
	unordered_set<unordered_set<int>,hashFunctions> insert_conjugacy_class(subgp H){
		unordered_set<unordered_set<int>,hashFunctions> s;
		for(int i=0;i<G.n;i++){
			unordered_set<int> H1;
			for (int g:H.c)
				H1.insert(G.O[G.O[i][g]][G.inv[i]]);
			s.insert(H1);
		}
		a.push_back(make_pair(H,s.size()));
		return s;
	}
	void print(){
		map<int,int> order_distribution;
		int tot=0,maxl=0;
		cout<<"Number of conjugacy classes of subgroups: "<<a.size()<<"\n";
		for(int i=0;i<a.size();i++){
			cout<<"#"<<i<<"     ";
			auto H=a[i];
			tot+=H.second;
			cout<<"Order of subgroups:"<<H.first.order()<<"     number of subgroups:"<<H.second<<"     ";
			if(H.first.maximal){
				maxl+=H.second;
				cout<<"maximal";
			}
			cout<<"\n";
		}
		cout<<"Total: "<<tot<<"\n";
		cout<<"Total maximal subgroups: "<<maxl<<"\n";
	}
};

bool check_conjugacy(subgp H1,subgp H2){
	for(int i=0;i<G.n;i++){
		subgp H3;
		bool conj_equiv=true;
		for(int g:H1.c)
			if(H2.c.find(G.O[G.O[i][g]][G.inv[i]])==H2.c.end()){
				conj_equiv=false;
				break;
			}
		if(conj_equiv) return true;
	}
	return false;
}

subgps subgp_finder(){
	trivial_subgp.c.insert(0); trivial_subgp.maximal=true;
	for(int i=0;i<G.n;i++) full_subgp.c.insert(i); full_subgp.maximal=false;
	
	timespec ts_beg,ts_end;
	cerr<<"Start to catch subgroups.\n";
	clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts_beg);
	
	subgps ret;
	vector<subgp> bfsq; // conjugacy classes of subgroups
	vector<unordered_set<unordered_set<int>,hashFunctions>> bfsq_all; // all subgroups within the conjugacy class
	bfsq.push_back(trivial_subgp);
	bfsq_all.push_back(ret.insert_conjugacy_class(bfsq[0]));
	for(int i=0,j=1;i!=j;i++){
		//for(int k=0;k<G.n;k++){
		for(int kk=0;kk<G.tot_cyclicgroups;kk++){
			int k=G.generator_cyclicgroup[kk];
			if(bfsq[i].c.find(k)==bfsq[i].c.end()){
				tmp_subgp=bfsq[i];
				if(generate_tmp_subgp(k))
					continue;
				else
					ret.a[i].first.maximal=false;
				bool caught=false;
				for(int l=0;l<j;l++) if(bfsq[l].order()==tmp_subgp.order()){
					if(bfsq_all[l].find(tmp_subgp.c)!=bfsq_all[l].end()){
						caught=true;
						break;
					}
				}
				if(!caught){
					bfsq.push_back(tmp_subgp);
					bfsq_all.push_back(ret.insert_conjugacy_class(bfsq[j]));
					++j;
				}
			}
		}
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts_end);
		cerr<<i<<" subgroups have been caught. (time: "<<(ts_end.tv_sec-ts_beg.tv_sec)+(ts_end.tv_nsec-ts_beg.tv_nsec)/1e9<<" sec)\n";
		clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &ts_beg);
	}
	ret.insert_conjugacy_class(full_subgp);
	return ret;
}

gp alternating_group(int k){
	auto factorial = fix([](auto&& self, int n) -> int { return n < 2 ? 1 : n * self(self, n - 1); });
	
	vector<vector<int>> perms;
	vector<int> perm;
	map<vector<int>,int> id;
	perms.resize(factorial(k)/2,vector<int>(k));
	perm.resize(k);
	for(int i=0;i<k;i++) perm[i]=i;
	perms[0]=perm; 
	for(int i=1,tot=1;i<factorial(k);i++){
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
			perms[tot++]=perm;
	}
	for(int i=0;i<perms.size();i++) id[perms[i]]=i;
	gp retG;
	retG.resize(factorial(k)/2);
	for(int s=0;s<retG.n;s++)
		for(int t=0;t<retG.n;t++){
			for(int i=0;i<k;i++) perm[i]=perms[t][perms[s][i]];
			retG.O[s][t]=id[perm];
		}
	retG.getinv();
	retG.getcyclicgroups();
	return retG;
}

void Dunfield_Thurston_2007_upper_bound(int g,subgps subgps_of_G){
	double ans=0.0;
	for(auto H:subgps_of_G.a)
		if(H.first.maximal)
			ans+=(double)H.second/pow((double)G.n/(double)H.first.order(),g);
	cout.precision(6);
	cout<<fixed<<"Dunfield_Thurston_2007_upper_bound = "<<ans<<"\n";
}

int main(){
	//freopen("A8.txt","w",stdout);
	int t; cin>>t;
	G=alternating_group(t);
	subgps subgps_of_G=subgp_finder();
	subgps_of_G.print();
	Dunfield_Thurston_2007_upper_bound(2,subgps_of_G);
}
