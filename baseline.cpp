#include <bits/stdc++.h>
using namespace std;

struct Graph {
    int n;
    long long m;
    vector<vector<int>> out_neighbors;
    vector<vector<int>> in_neighbors;
    Graph(int nodes=0) : n(nodes), m(0) {
        out_neighbors.assign(n+1, {});
        in_neighbors.assign(n+1, {});
    }
    void add_edge(int u, int v) {
        if(u < 1 || u > n || v < 1 || v > n) return;
        out_neighbors[u].push_back(v);
        in_neighbors[v].push_back(u);
        m++;
    }
};

// Dinic 最大流算法（适用于 double 类型容量）
struct FlowEdge {
    int v;
    double cap;
    int rev;
};
struct Dinic {
    int N;
    vector<vector<FlowEdge>> adj;
    vector<int> level;
    vector<int> it;
    int source, sink;
    double INF_CAP;
    Dinic(int n) : N(n) {
        adj.assign(n, {});
        level.assign(n, 0);
        it.assign(n, 0);
        INF_CAP = 1e12;  // 近似无穷大的容量
    }
    void add_edge(int u, int v, double cap) {
        FlowEdge a = {v, cap, (int)adj[v].size()};
        FlowEdge b = {u, 0.0, (int)adj[u].size()};
        adj[u].push_back(a);
        adj[v].push_back(b);
    }
    bool bfs() {
        fill(level.begin(), level.end(), -1);
        deque<int> dq;
        level[source] = 0;
        dq.push_back(source);
        while(!dq.empty()) {
            int u = dq.front();
            dq.pop_front();
            for(auto &e : adj[u]) {
                if(level[e.v] < 0 && e.cap > 1e-9) {
                    level[e.v] = level[u] + 1;
                    dq.push_back(e.v);
                }
            }
        }
        return level[sink] >= 0;
    }
    double dfs(int u, double flow) {
        if(u == sink) return flow;
        for(int &i = it[u]; i < (int)adj[u].size(); ++i) {
            FlowEdge &e = adj[u][i];
            if(e.cap > 1e-9 && level[e.v] == level[u] + 1) {
                double ret = dfs(e.v, min(flow, e.cap));
                if(ret > 1e-9) {
                    e.cap -= ret;
                    adj[e.v][e.rev].cap += ret;
                    return ret;
                }
            }
        }
        return 0.0;
    }
    double max_flow(int s, int t) {
        source = s;
        sink = t;
        double flow = 0.0;
        while(bfs()) {
            fill(it.begin(), it.end(), 0);
            while(true) {
                double f = dfs(source, INF_CAP);
                if(f < 1e-9) break;
                flow += f;
            }
        }
        return flow;
    }
};

namespace LADS {

/// 局部扩展：从锚点集合 R 出发扩展候选区域
vector<int> LocalAnchoredDensestSubgraph(const Graph &g, const vector<int> &R) {
    int n = g.n;
    vector<char> inRegion(n+1, false);
    deque<int> dq;
    // 将 R 中的节点加入候选区域
    for(int u: R) {
        if(u >= 1 && u <= n && !inRegion[u]) {
            inRegion[u] = true;
            dq.push_back(u);
        }
    }
    // 扩展 1 跳邻居（出邻居和入邻居）
    size_t idx = 0;
    while(idx < dq.size()) {
        int u = dq[idx++];
        // 添加 u 的所有出邻居
        for(int v: g.out_neighbors[u]) {
            if(!inRegion[v]) {
                inRegion[v] = true;
                dq.push_back(v);
            }
        }
        // 添加 u 的所有入邻居
        for(int v: g.in_neighbors[u]) {
            if(!inRegion[v]) {
                inRegion[v] = true;
                dq.push_back(v);
            }
        }
        // （以上简单实现为将 R 节点的直接邻居加入区域。
        // 根据需要可多跳扩展，这里采用 1 跳邻域作为候选区域。）
    }
    // 将候选区域节点输出为 vector 并排序
    vector<int> region;
    region.reserve(dq.size());
    for(int node: dq) {
        region.push_back(node);
    }
    sort(region.begin(), region.end());
    region.erase(unique(region.begin(), region.end()), region.end());
    return region;
}

/// 基于最大流和二分查找的全局优化：在候选区域上优化 ρ_R(S, T)
tuple<vector<int>, vector<int>, double> ImprovedGlobalAnchoredDensestSubgraphSetFlow(
        const Graph &g, const vector<int> &R, const vector<int> &region) {
    int k = region.size();
    // 建立候选区域节点到索引的映射
    vector<int> mapToIndex(g.n+1, -1);
    for(int i = 0; i < k; ++i) {
        mapToIndex[region[i]] = i;
    }
    // 计算 vol(R) = ∑_{u∈R} |N_out(u)| （R 中节点的出度总和）
    double volR = 0.0;
    for(int u: R) {
        if(u >= 1 && u <= g.n) {
            volR += (double)g.out_neighbors[u].size();
        }
    }
    if(volR < 0.0) volR = 0.0;
    // 初始化二分范围 [low, high]
    double low = 0.0, high = 0.0;
    for(int u: R) {
        if(u >= 1 && u <= g.n) {
            high += (double)g.out_neighbors[u].size();
            high += (double)g.in_neighbors[u].size();
        }
    }
    if(high < 1.0) high = 1.0;

    // 存储当前最佳解（S、T 切割）对应的 out_cut 和 in_cut 标记
    vector<char> best_out_cut, best_in_cut;
    double best_alpha = 0.0;

    // 二分搜索最佳 ρ 值
    for(int iter = 0; iter < 50; ++iter) {
        double mid = (low + high) / 2.0;
        // 构造流网络并计算给定 α(mid) 下的最小割
        int totalNodes = 2 + 2 * k;
        int source = 0, sink = 1;
        Dinic flow(totalNodes);
        // 添加锚点节点的约束（R 中节点必须包含在 S 和 T 中）
        for(int u: R) {
            if(mapToIndex[u] != -1) {
                int idx = mapToIndex[u];
                int u_out = 2 + idx;
                int u_in  = 2 + k + idx;
                // 锚点 u_in 和 u_out 都与源点连接无限容量边（确保锚点出点和入点都在源点一侧）
                flow.add_edge(source, u_in, flow.INF_CAP);
                flow.add_edge(source, u_out, flow.INF_CAP);
            }
        }
        // 添加非锚点节点的成员资格边
        for(int idx = 0; idx < k; ++idx) {
            int u = region[idx];
            bool isAnchor = (find(R.begin(), R.end(), u) != R.end());
            if(isAnchor) continue;
            int u_out = 2 + idx;
            int u_in  = 2 + k + idx;
            // 排除在 T 中（u_in 连到源点）的代价为 mid
            flow.add_edge(source, u_in, mid);
            // 排除在 S 中（u_out 连到汇点）的代价为 mid
            flow.add_edge(u_out, sink, mid);
        }
        // 添加原图中的有向边对应的容量为1的边（u_out -> v_in）
        for(int idx = 0; idx < k; ++idx) {
            int u = region[idx];
            for(int v: g.out_neighbors[u]) {
                int v_idx = (v >= 1 && v <= g.n ? mapToIndex[v] : -1);
                if(v_idx != -1) {
                    int u_out = 2 + idx;
                    int v_in  = 2 + k + v_idx;
                    flow.add_edge(u_out, v_in, 1.0);
                }
            }
        }
        // 计算最大流，对应求得当前 α 下的最小割
        double cutVal = flow.max_flow(source, sink);
        // 从残差网络中 BFS 找到源点可达节点，判定 S、T 集合
        vector<char> vis(totalNodes, false);
        deque<int> dq;
        dq.push_back(source);
        vis[source] = true;
        while(!dq.empty()) {
            int u = dq.front();
            dq.pop_front();
            for(auto &e : flow.adj[u]) {
                if(e.cap > 1e-9 && !vis[e.v]) {
                    vis[e.v] = true;
                    dq.push_back(e.v);
                }
            }
        }
        vector<char> out_in_cut(k, false), in_in_cut(k, false);
        for(int idx = 0; idx < k; ++idx) {
            int u_out = 2 + idx;
            int u_in  = 2 + k + idx;
            if(vis[u_out]) out_in_cut[idx] = true;
            if(vis[u_in])  in_in_cut[idx] = true;
        }
        // 根据最小割与 vol(R) 的关系调整二分范围，并记录当前最好解
        if(cutVal < volR - 1e-9) {
            // 如果割值 < vol(R)，说明当前 α 偏低（存在密度更高的子图），提高下界
            best_alpha = mid;
            best_out_cut = out_in_cut;
            best_in_cut = in_in_cut;
            low = mid;
        } else {
            // 否则割值 >= vol(R)，α 偏高，降低上界
            high = mid;
        }
    }

    // 根据记录的最佳 cut 标记重构 S 和 T 集合
    vector<int> Sset, Tset;
    if(!best_out_cut.empty()) {
        for(int idx = 0; idx < k; ++idx) {
            if(best_out_cut[idx]) Sset.push_back(region[idx]);
            if(!best_in_cut.empty() && best_in_cut[idx]) Tset.push_back(region[idx]);
        }
    }
    // 确保锚点 R 中的节点都包含在输出的 S 和 T 中
    for(int u: R) {
        if(find(Sset.begin(), Sset.end(), u) == Sset.end()) {
            Sset.push_back(u);
        }
        if(find(Tset.begin(), Tset.end(), u) == Tset.end()) {
            Tset.push_back(u);
        }
    }
    sort(Sset.begin(), Sset.end());
    sort(Tset.begin(), Tset.end());
    // 计算输出子图的实际 ρ_R(S,T) 值
    unordered_set<int> Sset_h(Sset.begin(), Sset.end());
    unordered_set<int> Tset_h(Tset.begin(), Tset.end());
    long long edges_ST = 0;
    for(int u: Sset) {
        for(int v: g.out_neighbors[u]) {
            if(Tset_h.count(v)) {
                edges_ST++;
            }
        }
    }
    long long sum_out = 0;
    for(int u: Sset) {
        if(find(R.begin(), R.end(), u) != R.end()) continue;
        for(int v: g.out_neighbors[u]) {
            if(Tset_h.count(v)) {
                sum_out++;
            }
        }
    }
    long long sum_in = 0;
    for(int v: Tset) {
        if(find(R.begin(), R.end(), v) != R.end()) continue;
        for(int u: g.in_neighbors[v]) {
            if(Sset_h.count(u)) {
                sum_in++;
            }
        }
    }
    double numerator = 2.0 * edges_ST - (double)sum_out - (double)sum_in;
    double denom = sqrt((double)Sset.size() * (double)Tset.size());
    double density = (denom > 1e-9 ? numerator / denom : 0.0);
    return {Sset, Tset, density};
}

} // namespace LADS

int main() {
    ios::sync_with_stdio(false);
    cin.tie(NULL);

    // 读取输入
    int n, m;
    if(!(cin >> n >> m)) {
        return 0;
    }
    Graph g(n);
    for(int i = 0; i < m; ++i) {
        int u, v;
        cin >> u >> v;
        g.add_edge(u, v);
    }
    int r_size;
    cin >> r_size;
    vector<int> R;
    R.reserve(r_size);
    for(int i = 0; i < r_size; ++i) {
        int node;
        cin >> node;
        R.push_back(node);
    }
    sort(R.begin(), R.end());
    R.erase(unique(R.begin(), R.end()), R.end());
    // 局部扩展得到候选区域
    vector<int> region = LADS::LocalAnchoredDensestSubgraph(g, R);
    // 全局优化求解最佳 S, T 和对应的 ρ 值
    auto [S, T, rho] = LADS::ImprovedGlobalAnchoredDensestSubgraphSetFlow(g, R, region);
    // 输出结果
    cout << "S = {";
    for(size_t i = 0; i < S.size(); ++i) {
        cout << S[i];
        if(i < S.size() - 1) cout << ", ";
    }
    cout << "}\n";
    cout << "T = {";
    for(size_t j = 0; j < T.size(); ++j) {
        cout << T[j];
        if(j < T.size() - 1) cout << ", ";
    }
    cout << "}\n";
    cout.setf(std::ios::fixed);
    cout << setprecision(6);
    cout << "rho_R(S,T) = " << rho << "\n";
    return 0;
}
