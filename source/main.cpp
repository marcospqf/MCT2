#include "MCTS.hpp"
#include <bits/stdc++.h>
#include <csignal>
using namespace std;
int main() {
  srand(time(NULL));
  int n, m;
  cin >> n >> m;
  vector<vector<int>> graph(n + 1);
  vector<set<int>> g(n + 1);
  for (int i = 0; i < m; i++) {
    char c;
    int u, v;
    cin >> c >> u >> v;
    assert(u > v);
    if (g[u].count(v))
      continue;
    // assert(!g[u].count(v));
    assert(u <= n and v <= n);
    g[u].insert(v);
    g[v].insert(u);
    graph[u].push_back(v);
    graph[v].push_back(u);
  }
  MCTS test(n, graph);
  signal(SIGINT, test.SetShutDown);
  set<int> click = test.Process();
  for (int x : click) {
    for (int y : click) {
      if (x == y)
        continue;
      assert(g[x].count(y));
    }
  }

  std::cout << "OLHA AS CLIQUE" << endl;
  for (int x : click) {
    std::cout << x << " ";
  }
  std::cout << endl;
  return 0;
}
