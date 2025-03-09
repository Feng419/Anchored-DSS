#include <bits/stdc++.h>
using namespace std;

struct Graph {
    int n, m;
    vector<vector<int>> out_nei;
    vector<vector<int>> in_nei;
    Graph(int n): n(n), m(0) {
        out_nei.assign(n + 1, {});
        in_nei.assign(n + 1, {});
    }
    void add_edge(int u, int v) {
        out_nei[u].push_back(v);
        in_nei[v].push_back(u);
        m++;
    }
};

struct FlowEdge {
    int v;
    int cap;
    int rev;
};

struct MaxFlow {
    int N;
    vector<vector<FlowEdge>> adj;
    MaxFlow(int N): N(N), adj(N) {}
    void addEdge(int u, int v, int cap) {
        FlowEdge a = {v, cap, (int)adj[v].size()};
        FlowEdge b = {u, 0, (int)adj[u].size()};
        adj[u].push_back(a);
        adj[v].push_back(b);
    }
    bool bfs(int s, int t, vector<int> &level) {
        fill(level.begin(), level.end(), -1);
        deque<int> dq;
        level[s] = 0;
        dq.push_back(s);

        while (!dq.empty()) {
            int u = dq.front();
            dq.pop_front();

            for (auto &e : adj[u]) {
                if (level[e.v] < 0 && e.cap > 0) {
                    level[e.v] = level[u] + 1;
                    dq.push_back(e.v);

                    if (e.v == t)
                        return true;
                }
            }
        }

        return level[t] >= 0;
    }
    int dfs(int u, int t, int flow, vector<int> &level, vector<int> &it) {
        if (u == t)
            return flow;

        for (int &i = it[u]; i < (int)adj[u].size(); ++i) {
            FlowEdge &e = adj[u][i];

            if (e.cap > 0 && level[e.v] == level[u] + 1) {
                int ret = dfs(e.v, t, min(flow, e.cap), level, it);

                if (ret > 0) {
                    e.cap -= ret;
                    adj[e.v][e.rev].cap += ret;
                    return ret;
                }
            }
        }

        return 0;
    }
    int maxflow(int s, int t) {
        int total = 0;
        vector<int> level(N), it(N);

        while (bfs(s, t, level)) {
            fill(it.begin(), it.end(), 0);

            while (int pushed = dfs(s, t, INT_MAX, level, it)) {
                total += pushed;
            }
        }

        return total;
    }
};

int main() {
    ios::sync_with_stdio(false);
    cin.tie(NULL);

    int n, m;

    if (!(cin >> n >> m)) {
        return 0;
    }

    Graph G(n);

    for (int i = 0; i < m; ++i) {
        int u, v;
        cin >> u >> v;
        G.add_edge(u, v);
    }

    int r;
    cin >> r;
    vector<int> R_nodes(r);
    unordered_set<int> R;
    R.reserve(r * 2);

    for (int i = 0; i < r; ++i) {
        cin >> R_nodes[i];
        R.insert(R_nodes[i]);
    }

    vector<int> outdeg(n + 1), indeg(n + 1);

    for (int u = 1; u <= n; ++u) {
        outdeg[u] = G.out_nei[u].size();
        indeg[u] = G.in_nei[u].size();
    }

    // Frank-Wolfe
    vector<double> r_out(n + 1, 0.0), r_in(n + 1, 0.0);
    vector<double> beta_out(n + 1, 0.0), beta_in(n + 1, 0.0);
    int maxIter = 50;

    for (int iter = 1; iter <= maxIter; ++iter) {
        for (int u = 1; u <= n; ++u) {
            double ru = r_out[u] + beta_out[u];

            for (int v : G.out_nei[u]) {
                double rv = r_in[v] + beta_in[v];

                if (ru < rv) {
                    r_out[u] += 1.0;
                } else if (ru > rv) {
                    r_in[v] += 1.0;
                } else {
                    r_out[u] += 0.5;
                    r_in[v] += 0.5;
                }
            }
        }
        double v_max = -1e12;

        for (int u = 1; u <= n; ++u) {
            double val_out = r_out[u] + beta_out[u];
            double val_in  = r_in[u] + beta_in[u];

            if (val_out > v_max)
                v_max = val_out;

            if (val_in  > v_max)
                v_max = val_in;
        }

        for (int u : R_nodes) {
            if (u >= 1 && u <= n) {
                double current_out = r_out[u] + beta_out[u];
                double current_in  = r_in[u] + beta_in[u];
                beta_out[u] += (v_max - current_out);
                beta_in[u]  += (v_max - current_in);
            }
        }
    }

    vector<double> values;
    values.reserve(2 * n + 1);

    for (int u = 1; u <= n; ++u) {
        values.push_back(r_out[u] + beta_out[u]);
        values.push_back(r_in[u] + beta_in[u]);
    }

    values.push_back(0.0);
    sort(values.begin(), values.end(), greater<double>());
    values.erase(unique(values.begin(), values.end(), [&](double a, double b) {
        return fabs(a - b) < 1e-9;
    }), values.end());

    double best_density = -1e12;
    vector<int> best_S, best_T;
    vector<char> inS(n + 1), inT(n + 1);

    for (double lambda : values) {
        int S_size = 0, T_size = 0;

        for (int u = 1; u <= n; ++u) {
            if (r_out[u] + beta_out[u] >= lambda) {
                inS[u] = 1;
                S_size++;
            } else {
                inS[u] = 0;
            }

            if (r_in[u] + beta_in[u] >= lambda) {
                inT[u] = 1;
                T_size++;
            } else {
                inT[u] = 0;
            }
        }

        for (int u : R_nodes) {
            if (u < 1 || u > n)
                continue;

            if (!inS[u] && !inT[u]) {
                inS[u] = 1;
                S_size++;
            }
        }

        if (S_size == 0 || T_size == 0) {
            continue;
        }

        long long edges_in_ST = 0;
        long long out_penalty = 0;
        long long in_penalty = 0;

        for (int u = 1; u <= n; ++u) {
            if (inS[u] && R.find(u) == R.end()) {
                out_penalty += outdeg[u];
            }

            if (inT[u] && R.find(u) == R.end()) {
                in_penalty += indeg[u];
            }
        }

        for (int u = 1; u <= n; ++u) {
            if (!inS[u])
                continue;

            for (int v : G.out_nei[u]) {
                if (inT[v]) {
                    edges_in_ST++;

                    if (R.find(u) == R.end())
                        out_penalty--;

                    if (R.find(v) == R.end())
                        in_penalty--;
                }
            }
        }

        double numerator = 2.0 * edges_in_ST - (double)out_penalty - (double)in_penalty;
        double density_value = numerator / sqrt((double)S_size * T_size);

        if (density_value > best_density) {
            best_density = density_value;
            best_S.clear();
            best_T.clear();

            for (int u = 1; u <= n; ++u) {
                if (inS[u])
                    best_S.push_back(u);
            }

            for (int v = 1; v <= n; ++v) {
                if (inT[v])
                    best_T.push_back(v);
            }
        }
    }

    unordered_set<int> S_set(best_S.begin(), best_S.end());
    unordered_set<int> T_set(best_T.begin(), best_T.end());

    for (int u : R_nodes) {
        if (u < 1 || u > n)
            continue;

        if (S_set.find(u) == S_set.end() && T_set.find(u) == T_set.end()) {
            best_S.push_back(u);
            S_set.insert(u);
        }
    }

    S_set.clear();
    T_set.clear();

    for (int u : best_S)
        S_set.insert(u);

    for (int v : best_T)
        T_set.insert(v);

    for (int u : R_nodes) {
        if (u < 1 || u > n)
            continue;

        bool inS_final = S_set.find(u) != S_set.end();
        bool inT_final = T_set.find(u) != T_set.end();
        bool hasOutEdgeInside = false;

        if (inS_final) {
            for (int w : G.out_nei[u]) {
                if (T_set.find(w) != T_set.end()) {
                    hasOutEdgeInside = true;
                    break;
                }
            }
        }

        bool hasInEdgeInside = false;

        if (inT_final) {
            for (int p : G.in_nei[u]) {
                if (S_set.find(p) != S_set.end()) {
                    hasInEdgeInside = true;
                    break;
                }
            }
        }

        if (inS_final && !hasOutEdgeInside) {
            S_set.erase(u);
        }

        if (inT_final && !hasInEdgeInside) {
            T_set.erase(u);
        }

        if (S_set.find(u) == S_set.end() && T_set.find(u) == T_set.end()) {
            S_set.insert(u);
        }
    }

    best_S.assign(S_set.begin(), S_set.end());
    best_T.assign(T_set.begin(), T_set.end());
    sort(best_S.begin(), best_S.end());
    sort(best_T.begin(), best_T.end());
    unordered_set<int> S_final_set(best_S.begin(), best_S.end());
    unordered_set<int> T_final_set(best_T.begin(), best_T.end());
    long long edges_ST = 0;
    long long out_R = 0;
    long long in_R = 0;

    for (int u : best_S) {
        if (R.find(u) == R.end()) {
            out_R += outdeg[u];
        }
    }

    for (int v : best_T) {
        if (R.find(v) == R.end()) {
            in_R += indeg[v];
        }
    }

    for (int u : best_S) {
        for (int v : G.out_nei[u]) {
            if (T_final_set.find(v) != T_final_set.end()) {
                edges_ST++;

                if (R.find(u) == R.end())
                    out_R--;

                if (R.find(v) == R.end())
                    in_R--;
            }
        }
    }

    double numerator_final = 2.0 * edges_ST - (double)out_R - (double)in_R;
    double density_final = numerator_final;

    if (!best_S.empty() && !best_T.empty()) {
        density_final = numerator_final / sqrt((double)best_S.size() * best_T.size());
    } else {
        density_final = 0.0;
    }

    int source = 0;
    int sink = n + 1;
    MaxFlow flow(n + 2);

    for (int u : best_S) {
        if (R.find(u) != R.end()) {
            flow.addEdge(source, u, INT_MAX); 
        } else {
            // cap = number of anchor neighbors in subgraph
            int cap = 0;

            for (int w : G.out_nei[u]) {
                if (R.find(w) != R.end() && T_final_set.find(w) != T_final_set.end())
                    cap++;
            }

            for (int w : G.in_nei[u]) {
                if (R.find(w) != R.end() && S_final_set.find(w) != S_final_set.end())
                    cap++;
            }

            flow.addEdge(source, u, cap);
        }
    }
    for (int u : best_S) {
        for (int v : G.out_nei[u]) {
            if (S_final_set.find(u) != S_final_set.end() && T_final_set.find(v) != T_final_set.end()) {
                if (R.find(v) != R.end()) {
                    // v is anchor
                    flow.addEdge(u, v, 1);
                }

                if (R.find(u) != R.end()) {
                    // u is anchor
                    flow.addEdge(v, u, 1);
                }
            }
        }
    }

    int rho_cap = (int) llround(numerator_final);

    if (rho_cap < 0)
        rho_cap = 0;

    for (int u : best_S) {
        flow.addEdge(u, sink, rho_cap);
    }

    flow.maxflow(source, sink);

    cout << "S = {";

    for (size_t i = 0; i < best_S.size(); ++i) {
        cout << best_S[i];

        if (i < best_S.size() - 1)
            cout << ", ";
    }

    cout << "}\n";
    cout << "T = {";

    for (size_t j = 0; j < best_T.size(); ++j) {
        cout << best_T[j];

        if (j < best_T.size() - 1)
            cout << ", ";
    }

    cout << "}\n";
    cout.setf(std::ios::fixed);
    cout << setprecision(6);
    cout << "rho_R(S,T) = " << density_final << "\n";

    return 0;
}
