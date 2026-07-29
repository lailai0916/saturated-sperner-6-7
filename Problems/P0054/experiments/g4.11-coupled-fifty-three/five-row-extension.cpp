#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Mask=std::uint32_t;

int bits(Mask mask)
{
	return __builtin_popcount(mask);
}

bool is_clutter(const std::vector<Mask> &rows)
{
	for(std::size_t i=0;i<rows.size();i++)
	{
		for(std::size_t j=0;j<rows.size();j++)
		{
			if(i!=j&&(rows[i]&rows[j])==rows[i])return 0;
		}
	}
	return 1;
}

std::vector<Mask> blockers(const std::vector<Mask> &rows,int n)
{
	std::vector<Mask> ans;
	for(Mask mask=1;mask<(Mask{1}<<n);mask++)
	{
		bool hit=1;
		for(Mask row:rows)if(!(mask&row)){hit=0;break;}
		if(!hit)continue;
		bool minimal=1;
		for(int i=0;i<n;i++)
		{
			if(!(mask&(Mask{1}<<i)))continue;
			Mask sub=mask^(Mask{1}<<i);
			bool still=1;
			for(Mask row:rows)if(!(sub&row)){still=0;break;}
			if(still){minimal=0;break;}
		}
		if(minimal)ans.push_back(mask);
	}
	return ans;
}

std::vector<std::pair<int,int>> parse(const std::string &key)
{
	std::vector<std::pair<int,int>> ans;
	std::size_t pos=0;
	while(pos<key.size())
	{
		std::size_t colon=key.find(':',pos),comma=key.find(',',colon);
		ans.push_back({std::stoi(key.substr(pos,colon-pos)),std::stoi(key.substr(colon+1,comma-colon-1))});
		pos=comma+1;
	}
	return ans;
}

std::vector<std::string> read_keys(const std::string &path)
{
	std::ifstream input(path);
	if(!input)throw std::runtime_error("cannot open kernel report");
	std::vector<std::string> keys;
	std::string line;
	while(std::getline(input,line))
	{
		if(line.rfind("class=",0)!=0)continue;
		std::string key=line.substr(6);
		key=key.substr(0,key.find('|'));
		keys.push_back(key);
	}
	if(keys.size()!=8)throw std::runtime_error("expected eight kernel classes");
	return keys;
}

bool contains_all(const std::vector<Mask> &big,const std::vector<Mask> &small)
{
	for(Mask row:small)if(std::find(big.begin(),big.end(),row)==big.end())return 0;
	return 1;
}

bool degrees_at_most_three(const std::vector<Mask> &rows,int n)
{
	for(int i=0;i<n;i++)
	{
		int cnt=0;
		for(Mask row:rows)if(row&(Mask{1}<<i))cnt++;
		if(cnt>3)return 0;
	}
	return 1;
}

bool valid_extension(const std::vector<Mask> &c,const std::vector<Mask> &kernel,int n,int x)
{
	if(c.size()!=7||!is_clutter(c)||!degrees_at_most_three(c,n))return 0;
	for(Mask row:c)if(bits(row)<3||bits(row)>8)return 0;
	std::vector<Mask> d=blockers(c,n);
	if(d.size()!=8||!contains_all(d,kernel)||!degrees_at_most_three(d,n))return 0;
	int with_x=0;
	for(Mask row:d)
	{
		if(bits(row)<3||bits(row)>7)return 0;
		if(row&(Mask{1}<<x))with_x++;
	}
	return with_x==3;
}

int main(int argc,char **argv)
{
	if(argc!=2)
	{
		std::cerr<<"usage: five-row-extension FIVE_ROW_KERNEL_REPORT\n";
		return 2;
	}
	std::vector<std::string> keys=read_keys(argv[1]);
	std::uint64_t total_q=0,total_valid=0;
	for(std::size_t id=0;id<keys.size();id++)
	{
		auto data=parse(keys[id]);
		std::vector<int> support;
		for(auto [mask,multiplicity]:data)
		{
			for(int i=0;i<multiplicity;i++)support.push_back(mask);
		}
		int old_n=support.size(),x=old_n;
		std::vector<Mask> kernel(5);
		for(int i=0;i<old_n;i++)
		{
			for(int row=0;row<5;row++)if(support[i]&(1<<row))kernel[row]|=Mask{1}<<i;
		}
		auto bk=blockers(kernel,old_n);
		int pairs=0;
		std::vector<Mask> c0;
		for(Mask row:bk)
		{
			if(bits(row)==2){row|=Mask{1}<<x;pairs++;}
			c0.push_back(row);
		}
		std::uint64_t q_count=0,valid=0;
		if(pairs==3&&bk.size()==7)
		{
			q_count=1;
			if(valid_extension(c0,kernel,old_n+1,x))valid=1;
		}
		else if(pairs==3&&bk.size()==6)
		{
			std::vector<int> deg(old_n+1);
			for(Mask row:c0)for(int i=0;i<=old_n;i++)if(row&(Mask{1}<<i))deg[i]++;
			for(Mask chosen=0;chosen<(Mask{1}<<old_n);chosen++)
			{
				bool degree_ok=1;
				for(int i=0;i<old_n;i++)if((chosen&(Mask{1}<<i))&&deg[i]>=3)degree_ok=0;
				if(!degree_ok)continue;
				for(int fresh=0;fresh+bits(chosen)<=8;fresh++)
				{
					if(fresh+bits(chosen)<3)continue;
					Mask q=chosen;
					for(int i=0;i<fresh;i++)q|=Mask{1}<<(old_n+1+i);
					std::vector<Mask> c=c0;
					c.push_back(q);
					if(!is_clutter(c))continue;
					q_count++;
					if(valid_extension(c,kernel,old_n+1+fresh,x))valid++;
				}
			}
		}
		std::cout<<"class="<<id+1<<" points="<<old_n<<" blockers="<<bk.size()<<" pairs="<<pairs
			<<" q_candidates="<<q_count<<" valid_extensions="<<valid<<'\n';
		total_q+=q_count;
		total_valid+=valid;
	}
	std::cout<<"total_q_candidates="<<total_q<<'\n';
	std::cout<<"total_valid_extensions="<<total_valid<<'\n';
	return 0;
}
