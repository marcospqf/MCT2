#include "MCTS.hpp"
const int kINF = 0x3f3f3f3f;
double MCTS::Cp = 2.0 / sqrt(2);
bool MCTS::shutdown = false;
Graph::Graph(int n) : nvertex(n), graph(n + 1) {}
Graph::Graph(int n, vector<vector<int>> graph_) : nvertex(n), graph(graph_) {}
void Graph::AddEdge(int u, int v) {
  graph[u].push_back(v);
  graph[v].push_back(u);
}

set<int> Graph::NextCandidates(int vertex, set<int> &candidates) {
  set<int> nxt_candidates;
  for (int v : graph[vertex])
    if (candidates.count(v))
      nxt_candidates.insert(v);
  return nxt_candidates;
}

set<int> Graph::MaxCliqueMaxDegreeHeuristic(set<int> candidates,
                                            set<int> clique) {
  int len = candidates.size();
  vector<int> degree(len, 1);
  vector<int> vertex(len, 0);
  map<int, int> vertex_to_pos;
  int cnt = 0;
  for (int u : candidates) {
    vertex[cnt] = u;
    vertex_to_pos[u] = cnt;
    for (int v : graph[u])
      degree[cnt] += candidates.count(v);
    cnt++;
  }
  for (int i = 0; i < len; i++) {
    int maxi = 0;
    int u = 0;
    for (int j = 0; j < len; j++) {
      if (degree[j] > maxi and degree[j] > 0)
        maxi = degree[j], u = vertex[j];
    }
    if (maxi == 0)
      break;
    int cnt = 0;
    for (int v : graph[u])
      if (clique.count(v))
        cnt++;
    if (cnt == clique.size())
      clique.insert(u);

    degree[vertex_to_pos[u]] = 0;
    for (int v : graph[u])
      if (candidates.count(v))
        degree[vertex_to_pos[v]]--;
  }
  return clique;
}
set<int> Graph::MaxCliqueMinDegreeHeuristic(set<int> candidates,
                                            set<int> clique) {
  int len = candidates.size();
  vector<int> degree(len, 1);
  vector<int> vertex(len, 0);
  map<int, int> vertex_to_pos;
  int cnt = 0;
  for (int u : candidates) {
    vertex[cnt] = u;
    vertex_to_pos[u] = cnt;
    for (int v : graph[u])
      degree[cnt] += candidates.count(v);
    cnt++;
  }

  for (int i = 0; i < len; i++) {
    int mini = kINF;
    int u = 0;
    for (int j = 0; j < len; j++) {
      if (degree[j] < mini and degree[j] > 0)
        mini = degree[j], u = vertex[j];
    }
    if (mini == kINF)
      break;
    int cnt = 0;
    for (int v : graph[u])
      if (clique.count(v))
        cnt++;
    if (cnt == clique.size())
      clique.insert(u);

    degree[vertex_to_pos[u]] = 0;
    for (int v : graph[u])
      if (candidates.count(v))
        degree[vertex_to_pos[v]]--;
  }
  return clique;
}

set<int> Graph::MaxCliqueRandomHeuristic(set<int> candidates, set<int> clique) {
  vector<int> cand;
  for (int x : candidates)
    cand.push_back(x);
  random_shuffle(cand.begin(), cand.end());

  for (int u : cand) {
    int nvis = 0;
    for (int v : graph[u])
      nvis += clique.count(v);
    if (nvis == clique.size())
      clique.insert(u);
  }
  return clique;
}

set<int> Graph::Solver(set<int> candidates, set<int> clique) {
  map<int, int> map_to_idx;
  map<int, int> trad;
  int n = 0;
  for (int u : candidates) {
    trad[n] = u;
    map_to_idx[u] = n++;
  }
  vector<long long> g(n, 0);
  vector<long long> dp((1ll << (n / 2 + 2)), 0);
  vector<long long> dp2((1ll << (n / 2 + 2)), 0);
  for (int u : candidates)
    for (int v : graph[u])
      if (candidates.count(v))
        g[map_to_idx[u]] |= (1ll << map_to_idx[v]);
  long long t1 = n / 2;
  long long t2 = n - t1;
  long long r = 0;
  long long maximum_clique = 0;
  for (long long mask = 1; mask < (1ll << t1); mask++) {
    for (long long j = 0; j < t1; j++)
      if (mask & (1ll << j)) {
        long long outra = mask - (1ll << j);
        long long r1 = __builtin_popcountll(dp[mask]);
        long long r2 = __builtin_popcountll(dp[outra]);
        if (r2 > r1)
          dp[mask] = dp[outra];
      }
    bool click = true;
    for (long long j = 0; j < t1; j++)
      if ((1ll << j) & mask)
        if (((g[j] ^ mask) & mask))
          click = false;
    if (click)
      dp[mask] = mask;
    long long r1 = __builtin_popcountll(dp[mask]);
    if (r1 > r)
      r = r1, maximum_clique = dp[mask];
  }

  for (long long mask = 1; mask < (1ll << t2); mask++) {
    for (long long j = 0; j < t2; j++)
      if (mask & (1ll << j)) {
        long long outra = mask - (1ll << j);
        long long r1 = __builtin_popcountll(dp2[mask]);
        long long r2 = __builtin_popcountll(dp2[outra]);
        if (r2 > r1)
          dp2[mask] = dp2[outra];
      }
    bool click = true;
    for (long long j = 0; j < t2; j++) {
      if ((1ll << j) & mask) {
        long long m1 = g[j + t1];
        long long cara = mask << t1;
        if ((m1 ^ cara) & cara) {
          click = false;
        }
      }
    }
    if (click) {
      dp2[mask] = mask;
    }
    long long r1 = __builtin_popcountll(dp2[mask]);
    if (r1 > r)
      r = r1, maximum_clique = dp2[mask];
  }

  for (long long mask = 0; mask < (1ll << t1); mask++) {
    long long tudo = (1ll << n) - 1;
    for (long long j = 0; j < t1; j++)
      if ((1ll << j) & mask)
        tudo &= g[j];

    tudo >>= t1;
    long long x = __builtin_popcountll(dp[mask]);
    long long y = __builtin_popcountll(dp2[tudo]);
    if (x + y > r) {
      r = x + y, maximum_clique = dp[mask] + (dp2[tudo] << t1);
    }
    r = max(r, x + y);
  }
  set<int> maxi_clique;
  for (int i = 0; i < n; i++)
    if ((1ll << i) & maximum_clique)
      maxi_clique.insert(trad[i]);
  return maxi_clique;
}

int Graph::UpperBoundClique(set<int> &clique, set<int> &candidates) {
  return clique.size() + candidates.size();
}

/*-----------------------*/
State::State(set<int> clique_, vector<State *> son_, set<int> candidates_,
             int nvisited_, double sum_reward_, bool is_terminal_,
             int upper_bound_clique_)
    : clique(clique_), son(son_), nvisited(nvisited_), candidates(candidates_),
      sum_reward(sum_reward_), is_terminal(is_terminal_),
      upper_bound_clique(upper_bound_clique_) {}

double State::GetReward(int nvis, double normalize) {
  if (nvisited == 0)
    return kINF;
  return sum_reward / (nvisited * normalize) +
         MCTS::Cp * sqrt((2.0 * log(nvis)) / (double)nvisited);
}
int State::GetBestChild() {
  assert(nvisited > 0);
  double maxi = -kINF;
  vector<int> best;
  double maxi_mean = -kINF;
  vector<int> idx_terminals;
  for (int i = 0; i < (int)son.size(); i++) {
    if (son[i] != nullptr) {
      if (son[i]->is_terminal) {
        idx_terminals.push_back(i);
      } else {
        maxi_mean = max(maxi_mean, sum_reward / nvisited);
      }
    }
  }
  if (idx_terminals.size() > 0) {
    int tam = idx_terminals.size();
    int vai = rand() % tam;
    return idx_terminals[vai];
  }
  for (int i = 0; i < (int)son.size(); i++) {
    if (son[i] != nullptr) {
      double uct = son[i]->GetReward(nvisited, maxi_mean);
      if (uct > maxi and fabs(uct - maxi) > 1e-8) {
        best.clear();
        maxi = uct;
        best.push_back(i);
      } else if (fabs(uct - maxi) <= 1e-8) {
        best.push_back(i);
      }
    }
  }
  if (best.size() == 0)
    return -1;
  int tam = best.size();
  return best[rand() % tam];
}

/*--------------------------*/

MCTS::MCTS(int n, vector<vector<int>> graph_) {
  graph = new Graph(n, graph_);
  set<int> candidates;
  for (int i = 1; i <= n; i++)
    candidates.insert(i);

  root = new State({}, {}, candidates, 0, 0, true, kINF);
  shutdown = false;
}

void MCTS::SetShutDown(int signum) { shutdown = true; }

set<int> MCTS::Process() {
  int cnt = 0;
  while (root != nullptr and !shutdown) {
    root = Build(root).first;
    if (cnt % 100 == 0)
      std::cout << maximum_clique.size() << endl;
    cnt++;
  }
  return maximum_clique;
}

vector<State *> MCTS::GenChildren(State *&tree_vertex) {
  vector<State *> result;
  set<int> clique = tree_vertex->clique;
  set<int> candidates = tree_vertex->candidates;
  State *with_vertex = nullptr;
  State *without_vertex = nullptr;
  if (candidates.size() > 0) {
    int idx = rand() % candidates.size();
    int vertex = -1;
    for (int x : candidates)
      if (idx == 0)
        vertex = x;
      else
        idx--;
    assert(vertex != -1);
    candidates.erase(vertex);
    without_vertex = new State(clique, {}, candidates, 0, 0, true,
                               graph->UpperBoundClique(clique, candidates));
    clique.insert(vertex);
    with_vertex =
        new State(clique, {}, graph->NextCandidates(vertex, candidates), 0, 0,
                  true, graph->UpperBoundClique(clique, candidates));
    result.push_back(without_vertex);
    result.push_back(with_vertex);
  }
  return result;
}

State *MCTS::Expand(State *&tree_vertex) {
  set<int> clique = tree_vertex->clique;
  set<int> candidates = tree_vertex->candidates;
  vector<State *> son = GenChildren(tree_vertex);
  int nvisited = 1;
  bool is_terminal = false;
  set<int> simu_clique = Simulation(tree_vertex);
  if (maximum_clique.size() < simu_clique.size())
    maximum_clique = simu_clique;
  if (son.size() > 0) {
    return tree_vertex = new State(clique, son, candidates, nvisited,
                                   (double)simu_clique.size(), is_terminal,
                                   graph->UpperBoundClique(clique, candidates));
  }
  delete tree_vertex;
  tree_vertex = nullptr;
  return nullptr;
}

pair<State *, double> MCTS::Build(State *&tree_vertex) {
  // std::cout << tree_vertex->next_graph_vertex << endl;
  tree_vertex->nvisited++;
  if (tree_vertex->is_terminal) {
    tree_vertex = Expand(tree_vertex);
    if (tree_vertex == nullptr) {
      return {nullptr, -1};
    }
    if (tree_vertex->upper_bound_clique <= (int)maximum_clique.size()) {
      EraseBranch(tree_vertex);
      return {nullptr, -1};
    }
    return {tree_vertex, tree_vertex->sum_reward};
  }
  if (tree_vertex->candidates.size() <= 40) {
    set<int> clique =
        graph->Solver(tree_vertex->candidates, tree_vertex->clique);
    if (maximum_clique.size() < clique.size())
      maximum_clique = clique;
    EraseBranch(tree_vertex);
    return {nullptr, -1};
  }

  int idx = tree_vertex->GetBestChild();
  if (idx == -1) {
    tree_vertex->son.clear();
    delete tree_vertex;
    tree_vertex = nullptr;
    return {nullptr, -1};
  }
  pair<State *, double> new_child = Build(tree_vertex->son[idx]);
  tree_vertex->son[idx] = new_child.first;
  tree_vertex->sum_reward += new_child.second;
  if (tree_vertex->upper_bound_clique <= (int)maximum_clique.size()) {
    EraseBranch(tree_vertex);
    return {nullptr, -1};
  }
  return {tree_vertex, new_child.second};
}

set<int> MCTS::Simulation(State *tree_vertex) {
  set<int> candidates = tree_vertex->candidates;
  set<int> c1 = graph->MaxCliqueMinDegreeHeuristic(tree_vertex->candidates,
                                                   tree_vertex->clique);
  set<int> c2 = graph->MaxCliqueMaxDegreeHeuristic(tree_vertex->candidates,
                                                   tree_vertex->clique);
  set<int> c3 = graph->MaxCliqueRandomHeuristic(tree_vertex->candidates,
                                                tree_vertex->clique);
  if (c1.size() > c2.size())
    c2 = c1;
  if (c2.size() > c3.size())
    c3 = c2;
  return c3;
}

void MCTS::EraseBranch(State *&tree_vertex) {
  if (tree_vertex == nullptr)
    return;
  for (auto son : tree_vertex->son) {
    EraseBranch(son);
  }
  tree_vertex->son.clear();
  delete tree_vertex;
  tree_vertex = nullptr;
}
