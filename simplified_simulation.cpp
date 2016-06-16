/* Author: Qiyun He

This is a simplified and cleaned version of the simulation code. 

*/

#include <cstdio>
#include <iostream>
#include <vector>
#include <float.h>
#include <utility>
#include <queue>
#include <ctime>
using namespace std;

int defaultServerNum = 1000;

struct server
{
	double cost;
	int region;
	server(){}
	server(int a, int b){
		cost = a;
		region = b;
	}
};

/* For simplicity, we assume there are 5 regions in total */
struct channel
{
	int popularity;
	double p[5];
	channel(){}
	channel(int a, double b, double c, double d, double e, double f){
		popularity = a;
		p[0] = b;
		p[1] = c;
		p[2] = d;
		p[3] = e;
		p[4] = f;
	}
};

struct state
{
	double cost;
	int numOfServer[5];

	state& operator=(state const& a)
	{
		cost = a.cost;
		numOfServer[0] = a.numOfServer[0];
		numOfServer[1] = a.numOfServer[1];
		numOfServer[2] = a.numOfServer[2];
		numOfServer[3] = a.numOfServer[3];
		numOfServer[4] = a.numOfServer[4];
	    return *this;
	};
	state(){
		cost = -1;
		numOfServer[0]=defaultServerNum;
		numOfServer[1]=defaultServerNum;
		numOfServer[2]=defaultServerNum;
		numOfServer[3]=defaultServerNum;
		numOfServer[4]=defaultServerNum;
	}
	void print(){
		cout<<"Current state: "<<cost<<" "<<numOfServer[0]<<" "<<numOfServer[1]<<" "<<numOfServer[2]<<" "<<numOfServer[3]<<" "<<numOfServer[4]<<endl;
	}
};

struct cost
{
	double sat;
	double lease;
	double bandwidth;
	double locality;
	double getSum(){
		return sat+lease+bandwidth+locality;
	}
};

int sizeServer;
int sizeChannel;
double priceOfServer[5]={0.105, 0.120, 0.129, 0.132, 0.163};

vector<server> serverList;
vector<channel> channelList;
vector< vector<double> > table;
double sat[] = {0, 0.5, 0.7, 0.85, 0.95, 1};
double band[] = {3, 2.75, 2.5, 2.25, 2};
double bandwidthPrice = 0.07;
double bandwidthPriceInRegion[] = {0.07, 0.08, 0.09, 0.10, 0.11};
int numOfRep = 5;
//double o=0.33,p=0.33,q=0.33;
double o=0.5,p=0.15,q=0.35;  // o p q are weight parameters (alpha beta gamma)
vector< vector<state> > DPTable;
int numberOfServerInRegion[] = {0,0,0,0,0};
vector<server> serverListInRegion[5];

/* cost */
double F(int i, int x, int m){ // for channel i, from server x+1, totally m representations

	double lease=0;
	double bandwidth;
	double locality=0;
	double averageBandwidthPrice = 0;
	for (int ii = x+1; ii <= x+m; ++ii)
	{
		lease += serverList[ii].cost;
		averageBandwidthPrice += bandwidthPriceInRegion[ serverList[ii].region ];
	}
	/* averageBandwidthPrice is an approximation but should be the same as in reality servers with the same prices are together */
	averageBandwidthPrice /= m;
	bandwidth = band[m] * channelList[i].popularity * averageBandwidthPrice;
	
	for (int ii = x+1; ii <= x+m; ++ii){
		double local;
		local = channelList[i].p[ serverList[ii].region ];
		local = 1-local;
		locality += local;
	}	
	locality *= channelList[i].popularity;
	locality /= m;
	return o*(channelList[i].popularity*(1-sat[m])) + p*(lease+bandwidth) + q*locality;
}

double FforRegion(int i, int x, int m, int r){ // for channel i, from server x+1, totally m representations, in region r

	double lease=0;
	double bandwidth;
	double locality=0;
	double averageBandwidthPrice = 0;
	if(numberOfServerInRegion[r]-x < m)return -1; // not enough
	for (int ii = x+1; ii <= x+m; ++ii)
	{
		lease += serverListInRegion[r][ii].cost;
		averageBandwidthPrice += bandwidthPriceInRegion[ serverListInRegion[r][ii].region ];
	}
	averageBandwidthPrice /= m;
	bandwidth = band[m] * channelList[i].popularity * averageBandwidthPrice;
	
	for (int ii = x+1; ii <= x+m; ++ii){
		double local;
		local = channelList[i].p[ serverListInRegion[r][ii].region ];
		local = 1-local;
		locality += local;
	}	
	locality *= channelList[i].popularity;
	locality /= m;
	return o*(channelList[i].popularity*(1-sat[m])) + p*(lease+bandwidth) + q*locality;
}

double costOfTop(int n, int sizeChannel){
	double cost = 0;
	for(int i=1; i<=n; i++){
		cost += F(i, (i-1) * numOfRep, numOfRep);
	}
	int lastServerIndex = numOfRep*n;
	for(int i=n+1; i<=sizeChannel; i++){
		cost += F(i, lastServerIndex++, 1);
	}
	return cost;
}

double calculateTotalPrice(int channelNum, double serverPrice, int serverRegion, int numOfRepresentations){
	double lease = serverPrice * numOfRepresentations;
	double bandwidth = band[numOfRepresentations] * channelList[channelNum].popularity * bandwidthPriceInRegion[serverRegion];
	double locality = channelList[channelNum].p[serverRegion];
	locality = (1-locality)*channelList[channelNum].popularity;
	return o*(channelList[channelNum].popularity*(1-sat[numOfRepresentations]))+p*(lease+bandwidth)+q*locality;
}

double greedyAlg(int sizeChannel){
	double totalP=0;

	for (int i = 1; i <= sizeChannel; ++i){
		double price;
		priority_queue< double > pq;
		for(int c=0;c<5;c++){ // for all region 
			for(int nor=1;nor<=5;nor++){
				price = calculateTotalPrice(i, priceOfServer[c], c, nor); // use the cheapest
				pq.push(-price);
			}
		}
		totalP -= pq.top();
	}
	return totalP;
}

double greedyAlgWithLimit(int sizeChannel){
	int numOfServer[5];
	double totalP=0;
	int totalNumOfServer = sizeServer;

	numOfServer[0]=numberOfServerInRegion[0];
	numOfServer[1]=numberOfServerInRegion[1];
	numOfServer[2]=numberOfServerInRegion[2];
	numOfServer[3]=numberOfServerInRegion[3];
	numOfServer[4]=numberOfServerInRegion[4];

	for (int i = 1; i <= sizeChannel; ++i){
		double price;
		priority_queue< pair<double, pair<int, int> > > pq;
		for(int c=0;c<5;c++){ // for all region 
			for(int nor=1;nor<=5;nor++){
				price = FforRegion(i,numberOfServerInRegion[c] - numOfServer[c], nor, c);
				if(price!=-1)
					pq.push( make_pair(-price, make_pair(c,nor)) );
			}
		}
		while(1){
			if(pq.empty()){
				cout<<"Not enough cloud instances!"<<endl;
				break;
			}
			int nor = pq.top().second.second;
			int c = pq.top().second.first;
			if(numOfServer[c]-nor >= 0 && totalNumOfServer-nor>=sizeChannel-i) {
				numOfServer[c]-=nor;
				totalNumOfServer -= nor;
				break;
			}
			else pq.pop();
		}
		totalP -= pq.top().first;
	}
	return totalP;
}

state calculateTotalPriceDP(int channelNum, int serverRegion, int numOfRepresentations, state lastState){
	double crtCost = FforRegion(channelNum, numberOfServerInRegion[serverRegion] - lastState.numOfServer[serverRegion], numOfRepresentations, serverRegion);
	double totalCost = lastState.cost + crtCost;
	state newState = lastState;
	newState.numOfServer[serverRegion]-=numOfRepresentations;
	if(newState.numOfServer[serverRegion] >=0){
		newState.cost=totalCost;
	} else {
		newState.cost=-2;
	}
	return newState;
}

double DP(){
	DPTable[0][0].cost = 0;
	for(int i=0;i<5;i++){
		DPTable[0][0].numOfServer[i] = numberOfServerInRegion[i];
	}
	state tmpState, returnedState;
	for(int i=1;i<=sizeChannel;i++){
		for(int j=i;j<=min(numOfRep*i, sizeServer); j++){
			tmpState = state();
			for(int m=1; m<=numOfRep; m++){
				if(j-m>=i-1 && DPTable[i-1][j-m].cost!=-1){
					for(int reg = 0; reg<=4; reg++){
						returnedState = calculateTotalPriceDP(i,reg,m, DPTable[i-1][j-m]);
						if( (returnedState.cost < tmpState.cost || tmpState.cost==-1 ) && returnedState.cost != -2 ){
							tmpState = returnedState;
						}
					}
				}
			}
			if(DPTable[i][j].cost!=-1) DPTable[i][j] = DPTable[i][j].cost<=tmpState.cost? DPTable[i][j] : tmpState;
			else DPTable[i][j] = tmpState;
		}
	}
	tmpState = DPTable[sizeChannel][sizeChannel];
	for(int j = sizeChannel+1; j<=sizeServer;j++){
		if(DPTable[sizeChannel][j].cost < tmpState.cost && DPTable[sizeChannel][j].cost!=-1) tmpState = DPTable[sizeChannel][j];
	}
	return tmpState.cost;
}

double heuristicDP(){
	double tmpCost, tp;
	for (int i = 1; i <= sizeChannel; ++i)
	{
		for(int j = i; j<= min(i*numOfRep, sizeServer); ++j){
			tmpCost=-2;//DBL_MAX/2;
			for(int m=1; m <= numOfRep; m++){
				if(j-m >= i-1 && table[i-1][j-m]!=-1){ //j-m is the last server not used by channel i
					tp = F(i, j-m, m) + table[i-1][j-m]; // for the i^th channel, use try use the (j-m+1)^th cheapest server
					if(tp < tmpCost || tmpCost==-2) tmpCost = tp;
				}
			}
			if(table[i][j] != -1) table[i][j] = min(table[i][j], tmpCost);
			else table[i][j] = tmpCost;
		}
	}
	tmpCost = table[sizeChannel][sizeChannel];
	for(int j = sizeChannel+1; j<=sizeServer;j++){
		if(table[sizeChannel][j] < tmpCost && table[sizeChannel][j]!=-1) tmpCost = table[sizeChannel][j];
	}
	return tmpCost;
}

int main(){

	int a,b;
	double c,d,e,f,g; // popularity share in 5 regions
	cin>>sizeServer>>sizeChannel;

	serverList.push_back( server(0,0) );
	for (int i = 0; i < sizeServer; ++i)
	{
		cin>>c>>b;
		serverList.push_back( server(a,b) );
		numberOfServerInRegion[b]++;
		serverListInRegion[b].push_back( server(a,b) );
	}

	channelList.push_back( channel(0,0,0,0,0,0) );
	for (int i = 0; i < sizeChannel; ++i)
	{
		cin>>b>>c>>d>>e>>f>>g;
		channelList.push_back( channel(b,c,d,e,f,g) );
	}

	table = vector< vector<double> > (sizeChannel+2, vector<double> (sizeServer+2, -1));
	DPTable = vector< vector<state> > (sizeChannel+2, vector<state>(sizeServer+2, state()));
	table[0][0] = 0;

	for (int i = 1; i <= sizeChannel; ++i)
	{
		table[i][i] = table[i-1][i-1] + F(i, i-1, 1);
	}
	
	cout<<"TopN:               "<<costOfTop(300, sizeChannel)<<endl;
	cout<<"greedyAlg:          "<<greedyAlg(sizeChannel)<<endl;
	cout<<"greedyAlgWithLimit: "<<greedyAlgWithLimit(sizeChannel)<<endl;
	cout<<"heuristicDP:        "<<heuristicDP()<<endl;
	cout<<"DP:                 "<<DP()<<endl;
	cout<<"================================="<<endl;


	return 0;
}