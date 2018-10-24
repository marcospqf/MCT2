#ifndef _mcts_hpp
#define _mcts_hpp
#include <bits/stdc++.h>
using namespace std;
class Graph {
  int nvertex;
  vector<vector<int>> graph;

public:
  Graph(int n);
  Graph(int n, vector<vector<int>> graph_);
  void AddEdge(int u, int v);
  set<int> NextCandidates(int vertex, set<int> &candidates);
  int UpperBoundClique(set<int> &clique, set<int> &candidates);
  set<int> MaxCliqueMinDegreeHeuristic(set<int> candidates, set<int> clique);
  set<int> MaxCliqueMaxDegreeHeuristic(set<int> candidates, set<int> clique);
  set<int> MaxCliqueRandomHeuristic(set<int> candidates, set<int> clique);
};

class State {
public:
  set<int> clique;
  vector<State *> son;
  set<int> candidates;
  int nvisited;
  double sum_reward;
  bool is_terminal;
  int upper_bound_clique;
  State(set<int> clique_, vector<State *> son_, set<int> candidates_,
        int nvisited_, double sum_reward_, bool is_terminal_,
        int upper_bound_clique_);
  double GetReward(int number_vis_parent, double normalize);
  int GetBestChild();
  void SetNextGraphVertex(Graph *graph, set<int> &clique, vector<int> &perm);
};

class MCTS {
private:
  vector<int> perm;
  set<int> maximum_clique;
  Graph *graph;
  State *root;
  static bool shutdown;

public:
  static double Cp;
  static void SetShutDown(int signum);
  // build graph;
  MCTS(int n, vector<vector<int>> graph_);
  State *Expand(State *&u);
  pair<State *, double> Build(State *&tree_vertex);
  set<int> Simulation(State *tree_vertex);
  set<int> Process();
  vector<State *> GenChildren(State *&tree_vertex);
  void EraseBranch(State *&tree_vertex);
};

#endif
