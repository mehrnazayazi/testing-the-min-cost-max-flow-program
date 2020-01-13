
/**
 *   ///////////////////////
 *   // MIN COST MAX FLOW //
 *   ///////////////////////
 *
 *   Authors: Frank Chu, Igor Naverniouk
 **/

/*********************
 * Min cost max flow * (Edmonds-Karp relabelling + fast heap Dijkstra)
 *********************
 * Takes a directed graph where each edge has a capacity ('cap') and a
 * cost per unit of flow ('cost') and returns a maximum flow network
 * of minimal cost ('fcost') from s to t. USE mcmf3.cpp FOR DENSE GRAPHS!
 *
 * PARAMETERS:
 *      - cap (global): adjacency matrix where cap[u][v] is the capacity
 *          of the edge u->v. cap[u][v] is 0 for non-existent edges.
 *      - cost (global): a matrix where cost[u][v] is the cost per unit
 *          of flow along the edge u->v. If cap[u][v] == 0, cost[u][v] is
 *          ignored. ALL COSTS MUST BE NON-NEGATIVE!
 *      - n: the number of vertices ([0, n-1] are considered as vertices).
 *      - s: source vertex.
 *      - t: sink.
 * RETURNS:
 *      - the flow
 *      - the total cost through 'fcost'
 *      - fnet contains the flow network. Careful: both fnet[u][v] and
 *          fnet[v][u] could be positive. Take the difference.
 * COMPLEXITY:
 *      - Worst case: O(m*log(m)*flow  <?  n*m*log(m)*fcost)
 * FIELD TESTING:
 *      - Valladolid 10594: Data Flow
 * REFERENCE:
 *      Edmonds, J., Karp, R.  "Theoretical Improvements in Algorithmic
 *          Efficieincy for Network Flow Problems".
 *      This is a slight improvement of Frank Chu's implementation.
 **/

#include <iostream>
using namespace std;


int m2, n2;
int Head[80200], Cost[80200], BackupCost[80200];
int End[80200], Cap[80200];
int Y[80200], Next[80200];
int p[80200], l[80200];
bool PathExists;
int minCost = 0, flow2=0;



// the maximum number of vertices + 1
#define NN 1024

// adjacency matrix (fill this up)
int cap[NN][NN];

// cost per unit of flow matrix (fill this up)
int cost[NN][NN];

// flow network and adjacency list
int fnet[NN][NN], adj[NN][NN], deg[NN];

// Dijkstra's predecessor, depth and priority queue
int par[NN], d[NN], q[NN], inq[NN], qs;

// Labelling function
int pi[NN];

#define CLR(a, x) memset( a, x, sizeof( a ) )
#define Inf (INT_MAX/2)
#define BUBL { \
    t = q[i]; q[i] = q[j]; q[j] = t; \
    t = inq[q[i]]; inq[q[i]] = inq[q[j]]; inq[q[j]] = t; }

// Dijkstra's using non-negative edge weights (cost + potential)
#define Pot(u,v) (d[u] + pi[u] - pi[v])
bool dijkstra( int n, int s, int t )
{
    CLR( d, 0x3F );
    CLR( par, -1 );
    CLR( inq, -1 );
    //for( int i = 0; i < n; i++ ) d[i] = Inf, par[i] = -1;
    d[s] = qs = 0;
    inq[q[qs++] = s] = 0;
    par[s] = n;

    while( qs )
    {
        // get the minimum from q and bubble down
        int u = q[0]; inq[u] = -1;
        q[0] = q[--qs];
        if( qs ) inq[q[0]] = 0;
        for( int i = 0, j = 2*i + 1, t; j < qs; i = j, j = 2*i + 1 )
        {
            if( j + 1 < qs && d[q[j + 1]] < d[q[j]] ) j++;
            if( d[q[j]] >= d[q[i]] ) break;
            BUBL;
        }

        // relax edge (u,i) or (i,u) for all i;
        for( int k = 0, v = adj[u][k]; k < deg[u]; v = adj[u][++k] )
        {
            // try undoing edge v->u
            if( fnet[v][u] && d[v] > Pot(u,v) - cost[v][u] )
                d[v] = Pot(u,v) - cost[v][par[v] = u];

            // try using edge u->v
            if( fnet[u][v] < cap[u][v] && d[v] > Pot(u,v) + cost[u][v] )
                d[v] = Pot(u,v) + cost[par[v] = u][v];

            if( par[v] == u )
            {
                // bubble up or decrease key
                if( inq[v] < 0 ) { inq[q[qs] = v] = qs; qs++; }
                for( int i = inq[v], j = ( i - 1 )/2, t;
                     d[q[i]] < d[q[j]]; i = j, j = ( i - 1 )/2 )
                BUBL;
            }
        }
    }

    for( int i = 0; i < n; i++ ) if( pi[i] < Inf ) pi[i] += d[i];

    return par[t] >= 0;
}
#undef Pot

int mcmf4( int n, int s, int t, int &fcost )
{
    // build the adjacency list
    CLR( deg, 0 );
    for( int i = 0; i < n; i++ )
        for( int j = 0; j < n; j++ )
            if( cap[i][j] || cap[j][i] ) adj[i][deg[i]++] = j;

    CLR( fnet, 0 );
    CLR( pi, 0 );
    int flow = fcost = 0;

    // repeatedly, find a cheapest path from s to t
    while( dijkstra( n, s, t ) )
    {
        // get the bottleneck capacity
        int bot = INT_MAX;
        for( int v = t, u = par[v]; v != s; u = par[v = u] ){
            if( fnet[v][u] ){
                if(bot> fnet[v][u]){
                    bot = fnet[v][u];
                }
            }else{
                if(bot>cap[u][v]-fnet[u][v]){
                    bot = cap[u][v]-fnet[u][v];
                }
            }

        }

        // update the flow network
        for( int v = t, u = par[v]; v != s; u = par[v = u] )
            if( fnet[v][u] ) { fnet[v][u] -= bot; fcost -= bot * cost[v][u]; }
            else { fnet[u][v] += bot; fcost += bot * cost[u][v]; }

        flow += bot;
    }

    return flow;
}




void Dijkstra2(){
    bool uncoloured[n2];
    l[0] = 0;
    p[0] = 0;
    uncoloured [0] = true;
    for (int i = 1; i < n2; ++i) {
        p[i] = 0;
        uncoloured[i] = true;
        l[i] = 20000;
    }
    bool uncoloured_exist = true;
    int u = 0;
    int counter = 0;
    while(uncoloured_exist){
        counter++;
        if(counter> 2 * m2){
            if(l[n2 - 1] < 20000){
                return;
            }
            PathExists = false;
            return;
        }
        uncoloured[u] = false;
        uncoloured_exist = false;
        int next = Y[u];
        while(next!=-1){
            if(u == 17 && End[next] == 26){
//                cout<<"cap of edge: "<<Cap[next]<<endl;
            }
            if(Cap[next]!=0){
                int neighbor = End[next];
                if(uncoloured[neighbor]){
                    if(l[neighbor] > l[u]+ Cost[next]){
                        l[neighbor] = l[u] + Cost[next];
                        p[neighbor] = u;
                    }
                }
            }
            next = Next[next];
        }
        int min = 20000;
        for (int i = 0; i < n2; ++i) {
            if(uncoloured[i]){
                uncoloured_exist = true;
                if(l[i] < min){
                    min = l[i];
                    u = i;
                }
            }
        }
    }


}


void AddEdge(int head, int end, int cost, int cap, int name){
    int i = 0, next;
    Head[name] = head;
    End[name] = end;
    Cost[name] = cost;
    Cap[name] = cap;
    if( Y[head]== -1){
        Y[head] = name;
    }else{
        int former = Y[head];
        int next = Next[former];
        while(next!= -1){//TODO change it to get back to head;
            former = next;
            next = Next[former];
        }
        Next[former] = name;
    }
}


bool testProgram(int numV, int m, int flow,int cost, int Randcost[250][250],int Randcap[250][250]){
    int  x, y, w, c;
    n2 = numV;
    m2 = m;
    for (int i = 0; i < n2; ++i) {
        p[i] = -1;
    }
    for(int i=0; i < n2; i++){
        Y[i] = -1;
    }
    for(int i=0; i < 2 * m2; i++){
        Next[i] = -1;
    }
    int numEdge = 0;
    for (int i = 0; i < numV ; ++i) {
        for (int j = 0; j < numV; ++j) {
            if(Randcap[i][j]!=-1){
                AddEdge(i,j,Randcost[i][j],Randcap[i][j],numEdge);
                AddEdge(j,i,-Randcost[i][j],0,m2+numEdge);
                numEdge++;
            }
        }
    }
    for (int k = 0; k < 2 * m2; ++k) {
        BackupCost[k] = Cost[k];
    }
    PathExists = true;
    int pathCost = 0, minCap = 20000;
    while(PathExists){
        int pathCost = 0;
        Dijkstra2();
        if(!PathExists){
            break;
        } else{
            int i = n2 - 1;
            while (i!=0){
//                cout<<p[i]<<", ";
                cout.flush();
                i = p[i];
            }
//            cout<<endl;
        }
        int i = n2 - 1;
        minCap = 200000;
        while (i!=0){
            for(int j=0;j< 2 * m2; j++){
                if(End[j] == i && Head[j]==p[i]){
                    if(Cap[j] < minCap){
                        minCap = Cap[j];
                        if(Cap[j] == 0){
//                            cout<<"bottle neck= "<<Head[j]<<"-->>"<<End[j]<<endl;
                        }
                    }
                    pathCost+=BackupCost[j];
                    break;
                }
            }
            i = p[i];
        }
//        cout<<"path min cap = "<< minCap<<endl;
        i = n2 - 1;
        while(i != 0){
            for (int j = 0; j < 2 * m2 ; ++j) {
                if(End[j] == i && Head[j]==p[i]){
                    Cap[j]-=minCap;
                }
                if(End[j] == p[i] && Head[j]== i){
                    Cap[j]+=minCap;
                }
            }
            i = p[i];
        }
        minCost+=(pathCost*minCap);
        flow2 += minCap;
        for (int i = 0; i < 2 * m2; ++i) {
            Cost[i] = Cost[i]+ l[Head[i]] - l[End[i]];
        }
    }
    if(flow == flow2 && cost == minCost){
        return true;
    }
    return false;
}

//----------------- EXAMPLE USAGE -----------------
#include <iostream>
#include <stdio.h>
using namespace std;

int main()
{
    int numV, Randcost[250][250], Randcap[250][250];
    srand(time(NULL));
    for (int j = 0; j < 250; ++j) {
        for (int i = 0; i < 250; ++i) {
            Randcost[i][j] = -1;
            Randcap[i][j] = -1;
        }
    }
    //choose number of Vertices
    numV = (rand() % 90)+20;// v1 in the range 0 to 99
    for (int i = 0; i < numV ; ++i) {
        for (int j = 0; j < numV; ++j) {
            int fill = rand()%2;
            if(fill){
                if(Randcost[j][i]==-1){
                    Randcost[i][j] = rand() % 200;
//                    cout<<cost[i][j];
                    Randcap[i][j] = rand()%200;
                }
            }
        }
    }
    int m = 0;
    for (int k = 0; k <numV ; ++k) {
        for (int i = 0; i <numV ; ++i) {
            if(Randcap[k][i]!=-1){
                m++;
                cout<<k<<" "<<i<<" "<<Randcap[k][i]<<" "<<Randcost[k][i];
                cout.flush();
                cout<<endl;
            }

        }

    }


//    int numV;
//    //  while ( cin >> numV && numV ) {
//    cin >> numV;
    memset( cap, 0, sizeof( cap ) );

//    int m, a, b, c, cp;
    int s=0, t=numV-1;
//    cin >> m;
//    cin >> s >> t;

    // fill up cap with existing capacities.
    // if the edge u->v has capacity 6, set cap[u][v] = 6.
    // for each cap[u][v] > 0, set cost[u][v] to  the
    // cost per unit of flow along the edge i->v
    for (int l = 0; l < numV; ++l) {
        for (int i = 0; i < numV; ++i) {
            if(Randcap[l][i]!=-1){
                cost[l][i] = Randcost[l][i];
                cap[l][i] = Randcap[l][i];
            }
        }
    }


    int fcost;
    int flow = mcmf4(numV, s, t, fcost );
    if(testProgram(numV,m,flow,fcost,Randcost,Randcap)){
        cout<<"True"<<endl;
    }else{
        cout<<"False"<<endl;
    }
//    cout << "flow: " << flow << endl;
//    cout << "cost: " << fcost << endl;

    return 0;
}
