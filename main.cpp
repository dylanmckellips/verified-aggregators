#include <iostream>
#include <vector>
#include <queue>
#include <algorithm>
#include <random>
#include <deque>
#include <unordered_map>

// Basic graph representation
using Graph = std::vector<std::vector<int>>;

std::vector<int> u(std::vector<int> A, std::vector<int> B);

// Generate a random bipartite graph
Graph generateRandomBipartiteGraph(int leftSize, int rightSize, double edgeProbability) {
    std::random_device rd;
    std::mt19937 gen(rd());
    std::uniform_real_distribution<> dis(0.0, 1.0);

    int totalVertices = leftSize + rightSize;
    Graph g(totalVertices);

    for (int i = 0; i < leftSize; ++i) {
        for (int j = 0; j < rightSize; ++j) {
            if (dis(gen) < edgeProbability) {
                int rightVertex = leftSize + j;
                g[i].push_back(rightVertex);
                g[rightVertex].push_back(i);
            }
        }
    }

    return g;
}

// Compute degeneracy of a graph using bucket sort for efficiency
// Returns the degeneracy value
int computeDegeneracy(const Graph& g) {
    int n = g.size();
    std::vector<int> degree(n);
    for (int i = 0; i < n; ++i) {
        degree[i] = g[i].size();
    }

   // int maxDegree = 0;
    std::vector<std::deque<int>> buckets(n);

    for (int i = 0; i < n; ++i) {
        buckets[degree[i]].push_back(i);
    }

    int degeneracy = 0;
    for (int i = 0; i < n; ++i) {
        int d = 0;
        while (d < n && buckets[d].empty()) {
            d++;
        }

        if (d == n) break;

        degeneracy = std::max(degeneracy, d);

        int v = buckets[d].front();
        buckets[d].pop_front();
        degree[v] = -1;

        for (int u : g[v]) {
            if (degree[u] >= 0) {
                // Remove u from its current bucket
                auto& bucket = buckets[degree[u]];
                bucket.erase(std::find(bucket.begin(), bucket.end(), u));
                degree[u]--;
                // Add u to its new bucket
                buckets[degree[u]].push_back(u);
            }
        }
    }

    return degeneracy;
}

// Degeneracy ordering: uses degeneracy algorithm to order vertices
std::vector<int> degeneracyOrdering(const Graph& g) {
    int n = g.size();
    std::vector<int> degree(n);
    for (int i = 0; i < n; ++i) {
        degree[i] = g[i].size();
    }

    std::vector<int> ordering;
    ordering.reserve(n);
    std::vector<std::deque<int>> buckets(n);

    for (int i = 0; i < n; ++i) {
        buckets[degree[i]].push_back(i);
    }

    for (int i = 0; i < n; ++i) {
        int d = 0;
        while (d < n && buckets[d].empty()) {
            d++;
        }

        if (d == n) break;

        int v = buckets[d].front();
        buckets[d].pop_front();
        ordering.push_back(v);
        degree[v] = -1;

        for (int u : g[v]) {
            if (degree[u] >= 0) {
                auto& bucket = buckets[degree[u]];
                bucket.erase(std::find(bucket.begin(), bucket.end(), u));
                degree[u]--;
                buckets[degree[u]].push_back(u);
            }
        }
    }

    return ordering;
}


std::vector<int> getGamma(Graph G, std::vector<int> C){
    //return set of vertices in G that are adjacent to all vertices in C
    std::vector<int> gamma;
    for (int v = 0; v < (int)G.size(); ++v) {
        bool adjacentToAll = true;
        for (int c : C) {
            if (std::find(G[v].begin(), G[v].end(), c) == G[v].end()) {
                adjacentToAll = false;
                break;
            }
        }
        if (adjacentToAll) {
            gamma.push_back(v);
        }
    }
    return gamma;
}


float DENSITY(Graph G, std::vector<int> H, std::vector<int> C) {
    std::vector<int> gammac = getGamma(G, C);
    if (gammac.empty()) return 0.0f;          // avoid divide-by-zero
    std::vector<int> HC = u(H, C);
    if (HC.empty()) return 0.0f;
    int edges = 0;
    for (int v : HC) {
        for (int w : gammac) {
            if (std::find(G[v].begin(), G[v].end(), w) != G[v].end())
                edges++;
        }
    }
    return static_cast<float>(edges) / (HC.size() * gammac.size());
}




//helper get degeneracy ordering of a subgraph
std::vector<int> getDegenOrderSubgraph(Graph G, std::vector<int> vertices) {
    Graph subgraph(vertices.size());
    std::unordered_map<int, int> vertexMap;
    for (int i = 0; i < (int)vertices.size(); ++i) {
        vertexMap[vertices[i]] = i;
    }
    for (int v : vertices) {
        for (int nb : G[v]) {
            if (vertexMap.count(nb)) {
                subgraph[vertexMap[v]].push_back(vertexMap[nb]);
            }
        }
    }
    // Get ordering on subgraph indices, then map BACK to original IDs
    std::vector<int> subOrder = degeneracyOrdering(subgraph);
    std::vector<int> result;
    result.reserve(subOrder.size());
    for (int idx : subOrder) {
        result.push_back(vertices[idx]); // map back to original vertex ID
    }
    return result;
}

std::vector<int> u(std::vector<int> A, std::vector<int> B){
    for (int b : B) {
        if (std::find(A.begin(), A.end(), b) == A.end()) {
            A.push_back(b);
        }
    }
    return A;
}

std::vector<int> getHv(Graph G, std::vector<int> orderH, int v) {
    std::vector<int> Hv;
    
    // Find position of v in orderH
    auto vIt = std::find(orderH.begin(), orderH.end(), v);
    
    // Get N(v) - direct neighbors of v
    std::vector<int> neighbors(G[v].begin(), G[v].end());
    
    // Get N²(v) - neighbors of neighbors (excluding v itself)
    std::vector<int> neighbors2;
    for (int u : neighbors) {
        for (int w : G[u]) {
            if (w != v && std::find(neighbors.begin(), neighbors.end(), w) == neighbors.end()) {
                neighbors2.push_back(w);
            }
        }
    }
    
    // Iterate through orderH, only looking at vertices after v
    for (auto it = std::next(vIt); it != orderH.end(); ++it) {
        int u = *it;
        if (std::find(neighbors2.begin(), neighbors2.end(), u) != neighbors2.end()) {
            Hv.push_back(u);
        }
    }
    return Hv;
}


std::vector<std::vector<int>> aggregator(Graph G, std::vector<int> H, float p, std::vector<int> dorder, std::vector<int> C){
    if (DENSITY(G, H, C) > p) {
        return {u(u(H, C), getGamma(G, C))};
    }

    std::vector<std::vector<int>> S;
  
    //S = empty set
    std::vector<int> orderH = getDegenOrderSubgraph(G, H);
    
    //for v in order(H)
    for (int v: orderH) {
        //H_v = {u | u \in H \cap N^2(v) AND u>v in degen order}
        std::vector<int> Hv = getHv(G, orderH, v);
        std::vector<int> Cv = C;
        Cv.push_back(v);
        std::vector<std::vector<int>> Sv = aggregator(G, Hv, p, dorder, Cv); //recurse
        S.insert(S.end(), Sv.begin(), Sv.end());
        H.erase(std::remove(H.begin(), H.end(), v), H.end());

        if (DENSITY(G, H, C) > p) {
            S.push_back(u(u(H, C), getGamma(G, C)));
            return S;
        }

        
    }

    return S;

}

std::vector<int> getRightHalf(Graph G) {
    int n = G.size();
    std::vector<int> color(n, 0); // 0 = unvisited, 1 = left, 2 = right
    std::vector<int> rightVertices;

    for (int start = 0; start < n; start++) {
        if (color[start] != 0) continue;

        std::queue<int> q;
        color[start] = 1;
        q.push(start);

        while (!q.empty()) {
            int v = q.front(); q.pop();
            for (int u : G[v]) {
                if (color[u] == 0) {
                    color[u] = (color[v] == 1) ? 2 : 1;
                    q.push(u);
                }
            }
        }
    }

    for (int i = 0; i < n; i++)
        if (color[i] == 2)
            rightVertices.push_back(i);

    return rightVertices;
}

int main() {

    std::cout << "Random Bipartite Graph" << std::endl;
    int leftVertices = 10;
    int rightVertices = 10;
    double edgeProbability = 0.6;

    Graph bipartite = generateRandomBipartiteGraph(leftVertices, rightVertices, edgeProbability);

    std::cout << "Bipartite graph with " << leftVertices << " left vertices and " 
              << rightVertices << " right vertices" << std::endl;
    std::cout << "Edge probability: " << edgeProbability << std::endl;

    auto bipartiteOrder = degeneracyOrdering(bipartite);
    std::cout << "Degeneracy ordering: ";
    for (int v : bipartiteOrder) {
        std::cout << v << " ";
    }
    std::cout << std::endl;
    std::cout << "Degeneracy: " << computeDegeneracy(bipartite) << std::endl << std::endl;

    std::vector<std::vector<int>> aGATED = aggregator(bipartite, getRightHalf(bipartite), .5, bipartiteOrder, {});
    std::cout << "Aggregated sets: " << std::endl;
    for (const auto& set : aGATED) {
        std::cout << "{ ";
        for (int v : set) {
            std::cout << v << " ";
        }
        std::cout << "}" << std::endl;
    }

    std::cout << "Done." << std::endl;
    return 0;
}