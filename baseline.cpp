#include <bits/stdc++.h>
using namespace std;

struct Graph {
    int n, m;
    vector<vector<int>> out_neighbors;
    vector<vector<int>> in_neighbors;
    Graph(int n): n(n), m(0) {
        out_neighbors.assign(n + 1, {});
        in_neighbors.assign(n + 1, {});
    }
    void add_edge(int u, int v) {
        out_neighbors[u].push_back(v);
        in_neighbors[v].push_back(u);
        m++;
    }
};

struct FlowEdge {
    int v;
    int capacity;
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
                if (level[e.v] < 0 && e.capacity > 0) {
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

            if (e.capacity > 0 && level[e.v] == level[u] + 1) {
                int ret = dfs(e.v, t, min(flow, e.capacity), level, it);

                if (ret > 0) {
                    e.capacity -= ret;
                    adj[e.v][e.rev].capacity += ret;
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

    // Prepare outdeg and indeg arrays
    vector<int> outdeg(n + 1), indeg(n + 1);

    for (int u = 1; u <= n; ++u) {
        outdeg[u] = G.out_neighbors[u].size();
        indeg[u] = G.in_neighbors[u].size();
    }

    // Frank-Wolfe algorithm to compute r and beta values
    vector<double> r_out(n + 1, 0.0), r_in(n + 1, 0.0);
    vector<double> beta_out(n + 1, 0.0), beta_in(n + 1, 0.0);
    int maxIter = 50;

    for (int iter = 1; iter <= maxIter; ++iter) {
        // Distribute weights for each edge based on current r + beta
        for (int u = 1; u <= n; ++u) {
            double ru = r_out[u] + beta_out[u];

            for (int v : G.out_neighbors[u]) {
                double rv = r_in[v] + beta_in[v];

                if (ru < rv) {
                    r_out[u] += 1.0;
                } else if (ru > rv) {
                    r_in[v] += 1.0;
                } else {
                    // If equal, split the weight
                    r_out[u] += 0.5;
                    r_in[v] += 0.5;
                }
            }
        }

        // Find the current maximum value of r(u)+beta(u) across all u (for both out and in roles)
        double v_max = -1e12;

        for (int u = 1; u <= n; ++u) {
            double val_out = r_out[u] + beta_out[u];
            double val_in  = r_in[u] + beta_in[u];

            if (val_out > v_max)
                v_max = val_out;

            if (val_in  > v_max)
                v_max = val_in;
        }

        // Adjust beta for anchor nodes (nodes in R)
        for (int u : R_nodes) {
            if (u >= 1 && u <= n) {
                // Ensure anchor's out and in values reach v_max
                double current_out = r_out[u] + beta_out[u];
                double current_in  = r_in[u] + beta_in[u];
                beta_out[u] += (v_max - current_out);
                beta_in[u]  += (v_max - current_in);
            }
        }
    }

    // Compute combined values for threshold candidates
    vector<double> values;
    values.reserve(2 * n + 1);

    for (int u = 1; u <= n; ++u) {
        values.push_back(r_out[u] + beta_out[u]);
        values.push_back(r_in[u] + beta_in[u]);
    }

    // Include 0 as a candidate to consider possibly including all nodes
    values.push_back(0.0);
    sort(values.begin(), values.end(), greater<double>());
    // Remove duplicate (or very close) values
    values.erase(unique(values.begin(), values.end(), [&](double a, double b) {
        return fabs(a - b) < 1e-9;
    }), values.end());

    double best_density = -1e12;
    vector<int> best_S, best_T;
    // Temporary membership flags for S and T
    vector<char> inS(n + 1), inT(n + 1);

    for (double lambda : values) {
        // Build S and T based on threshold lambda
        // S = {u | r_out[u] + beta_out[u] >= lambda}
        // T = {v | r_in[v] + beta_in[v] >= lambda}
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

        // Ensure R ⊆ S ∪ T by adding any missing anchor to S (if not in either)
        for (int u : R_nodes) {
            if (u < 1 || u > n)
                continue;

            if (!inS[u] && !inT[u]) {
                inS[u] = 1;
                S_size++;
            }
        }

        // If either S or T is empty, skip (density undefined or 0)
        if (S_size == 0 || T_size == 0) {
            continue;
        }

        // Compute numerator components for ρ_R(S, T)
        long long edges_in_ST = 0;
        long long out_penalty = 0;
        long long in_penalty = 0;

        // Sum full outdeg and indeg for non-anchor nodes in S and T
        for (int u = 1; u <= n; ++u) {
            if (inS[u] && R.find(u) == R.end()) {
                out_penalty += outdeg[u];
            }

            if (inT[u] && R.find(u) == R.end()) {
                in_penalty += indeg[u];
            }
        }

        // Subtract edges that are internal (from S to T)
        for (int u = 1; u <= n; ++u) {
            if (!inS[u])
                continue;

            for (int v : G.out_neighbors[u]) {
                if (inT[v]) {
                    edges_in_ST++;

                    if (R.find(u) == R.end())
                        out_penalty--;

                    if (R.find(v) == R.end())
                        in_penalty--;
                }
            }
        }

        // Compute density = (2*edges_in_ST - out_penalty - in_penalty) / sqrt(|S| * |T|)
        double numerator = 2.0 * edges_in_ST - (double)out_penalty - (double)in_penalty;
        double density_value = numerator / sqrt((double)S_size * T_size);

        if (density_value > best_density) {
            best_density = density_value;
            best_S.clear();
            best_T.clear();

            // Record best S and T sets
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

    // Ensure anchors are included in the final solution (R ⊆ S ∪ T)
    unordered_set<int> S_set(best_S.begin(), best_S.end());
    unordered_set<int> T_set(best_T.begin(), best_T.end());

    for (int u : R_nodes) {
        if (u < 1 || u > n)
            continue;

        if (S_set.find(u) == S_set.end() && T_set.find(u) == T_set.end()) {
            // If an anchor somehow not included, add it to S by default
            best_S.push_back(u);
            S_set.insert(u);
        }
    }

    // Adjust anchor nodes not to be in both sets if not needed (to potentially improve density)
    // If an anchor has no outgoing edges in subgraph, remove it from S; if no incoming edges, remove from T.
    // This step ensures R ⊆ S ∪ T still holds.
    // Recompute membership flags for final sets
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
        // Count edges from u to T (out edges inside subgraph)
        bool hasOutEdgeInside = false;

        if (inS_final) {
            for (int w : G.out_neighbors[u]) {
                if (T_set.find(w) != T_set.end()) {
                    hasOutEdgeInside = true;
                    break;
                }
            }
        }

        bool hasInEdgeInside = false;

        if (inT_final) {
            for (int p : G.in_neighbors[u]) {
                if (S_set.find(p) != S_set.end()) {
                    hasInEdgeInside = true;
                    break;
                }
            }
        }

        if (inS_final && !hasOutEdgeInside) {
            // remove u from S if it's there without contributing edges
            S_set.erase(u);
        }

        if (inT_final && !hasInEdgeInside) {
            // remove u from T if it's there without contributing edges
            T_set.erase(u);
        }

        // Ensure anchor still in at least one set
        if (S_set.find(u) == S_set.end() && T_set.find(u) == T_set.end()) {
            // If both removed, add anchor to S by default
            S_set.insert(u);
        }
    }

    // Reconstruct best_S and best_T from sets, sorted for output
    best_S.assign(S_set.begin(), S_set.end());
    best_T.assign(T_set.begin(), T_set.end());
    sort(best_S.begin(), best_S.end());
    sort(best_T.begin(), best_T.end());
    // Recompute best_density with adjusted anchor distribution (for final output accuracy)
    // Compute edges and penalties for final sets
    unordered_set<int> S_final_set(best_S.begin(), best_S.end());
    unordered_set<int> T_final_set(best_T.begin(), best_T.end());
    long long edges_in_ST_final = 0;
    long long out_penalty_final = 0;
    long long in_penalty_final = 0;

    for (int u : best_S) {
        if (R.find(u) == R.end()) {
            out_penalty_final += outdeg[u];
        }
    }

    for (int v : best_T) {
        if (R.find(v) == R.end()) {
            in_penalty_final += indeg[v];
        }
    }

    for (int u : best_S) {
        for (int v : G.out_neighbors[u]) {
            if (T_final_set.find(v) != T_final_set.end()) {
                edges_in_ST_final++;

                if (R.find(u) == R.end())
                    out_penalty_final--;

                if (R.find(v) == R.end())
                    in_penalty_final--;
            }
        }
    }

    double numerator_final = 2.0 * edges_in_ST_final - (double)out_penalty_final - (double)in_penalty_final;
    double density_final = numerator_final;

    // If S or T is empty (should not happen because anchor fix ensured anchors in one set), handle to avoid /0
    if (!best_S.empty() && !best_T.empty()) {
        density_final = numerator_final / sqrt((double)best_S.size() * best_T.size());
    } else {
        density_final = 0.0;
    }

    // Maximum flow stability check (for verification, not necessarily used to adjust output further)
    // Build flow network
    int source = 0;
    int sink = n + 1;
    MaxFlow flow(n + 2);

    // Source to each node in subgraph
    for (int u : best_S) {
        if (R.find(u) != R.end()) {
            flow.addEdge(source, u, INT_MAX); // anchor node
        } else {
            // capacity = number of anchor neighbors in subgraph
            int cap = 0;

            for (int w : G.out_neighbors[u]) {
                if (R.find(w) != R.end() && T_final_set.find(w) != T_final_set.end())
                    cap++;
            }

            for (int w : G.in_neighbors[u]) {
                if (R.find(w) != R.end() && S_final_set.find(w) != S_final_set.end())
                    cap++;
            }

            flow.addEdge(source, u, cap);
        }
    }

    // Edges between nodes (directed) as per anchor connections
    for (int u : best_S) {
        for (int v : G.out_neighbors[u]) {
            if (S_final_set.find(u) != S_final_set.end() && T_final_set.find(v) != T_final_set.end()) {
                // only consider edges where one endpoint is anchor
                if (R.find(v) != R.end()) {
                    // v is anchor, add edge u->v
                    flow.addEdge(u, v, 1);
                }

                if (R.find(u) != R.end()) {
                    // u is anchor, add edge v->u
                    flow.addEdge(v, u, 1);
                }
            }
        }
    }

    // Nodes to sink with capacity = density_value (rounded or as int if rational? We'll use numerator to avoid fractional)
    // They used ρ_R(S*) itself. We'll use numerator_final (which is ρ * sqrt(|S||T|)) as capacity to avoid fractions.
    // But numerator_final could be non-integer (though original measure fraction can be rational).
    // To avoid floating, multiply by common denom (maybe 2) or scale by subgraph size:
    // Instead, we'll multiply all flow capacities by 2 (since measure formula uses 2*E).
    // Actually, numerator_final = 2|E|-... is integer, since edges and penalties are integers.
    // So numerator_final is rational? Wait, 2*edges - sums = integer indeed.
    // So we can use numerator_final as int capacity (since it should be integer).
    int rho_capacity = (int) llround(numerator_final);

    if (rho_capacity < 0)
        rho_capacity = 0;

    for (int u : best_S) {
        flow.addEdge(u, sink, rho_capacity);
    }

    // Compute max flow
    flow.maxflow(source, sink);
    // (We could check min cut equality condition here if needed)

    // Output the result
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
