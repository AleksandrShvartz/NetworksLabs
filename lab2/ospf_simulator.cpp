#include <iostream>
#include <vector>
#include <queue>
#include <map>
#include <set>
#include <algorithm>
#include <random>
#include <iomanip>
#include <climits>
#include <sstream>
#include <functional>
#include <cassert>

// ============================================================
// Link State Advertisement (LSA)
// ============================================================
struct LSA {
    int origin_id;
    int seq_num;
    std::vector<std::pair<int,int>> neighbors; // (neighbor_id, cost)
};

// ============================================================
// Routing table entry
// ============================================================
struct RouteEntry {
    int dest;
    int next_hop;
    int cost;
};

// ============================================================
// Link between two routers
// ============================================================
struct Link {
    int router_a;
    int router_b;
    int cost;
    bool active;
};

// ============================================================
// Router
// ============================================================
class Router {
public:
    int id;
    int num_routers;

    // LSDB: origin_id -> LSA
    std::map<int, LSA> lsdb;
    // Routing table: dest -> RouteEntry
    std::map<int, RouteEntry> routing_table;
    // Own LSA sequence number
    int own_seq_num;
    // Messages to flood to neighbors
    std::queue<LSA> outgoing_lsas;

    Router() : id(-1), num_routers(0), own_seq_num(0) {}

    Router(int id, int num_routers) : id(id), num_routers(num_routers), own_seq_num(0) {}

    // Generate own LSA based on current active neighbors
    LSA generate_lsa(const std::vector<std::pair<int,int>>& active_neighbors) {
        own_seq_num++;
        LSA lsa;
        lsa.origin_id = id;
        lsa.seq_num = own_seq_num;
        lsa.neighbors = active_neighbors;
        lsdb[id] = lsa;
        return lsa;
    }

    // Receive an LSA; return true if it's new/updated (should be flooded further)
    bool receive_lsa(const LSA& lsa) {
        auto it = lsdb.find(lsa.origin_id);
        if (it == lsdb.end() || it->second.seq_num < lsa.seq_num) {
            lsdb[lsa.origin_id] = lsa;
            return true;
        }
        return false;
    }

    // Run Dijkstra on LSDB to compute routing table
    void compute_spf() {
        routing_table.clear();

        // Build adjacency from LSDB
        std::map<int, std::vector<std::pair<int,int>>> adj;
        for (auto& [origin, lsa] : lsdb) {
            for (auto& [neighbor, cost] : lsa.neighbors) {
                adj[origin].push_back({neighbor, cost});
            }
        }

        // Dijkstra
        std::map<int, int> dist;
        std::map<int, int> prev;
        std::set<int> visited;
        // priority queue: (distance, node)
        std::priority_queue<std::pair<int,int>,
                            std::vector<std::pair<int,int>>,
                            std::greater<>> pq;

        dist[id] = 0;
        pq.push({0, id});

        while (!pq.empty()) {
            auto [d, u] = pq.top();
            pq.pop();

            if (visited.count(u)) continue;
            visited.insert(u);

            if (adj.find(u) == adj.end()) continue;

            for (auto& [v, w] : adj[u]) {
                int new_dist = d + w;
                if (dist.find(v) == dist.end() || new_dist < dist[v]) {
                    dist[v] = new_dist;
                    prev[v] = u;
                    pq.push({new_dist, v});
                }
            }
        }

        // Build routing table from prev map
        for (auto& [dest, d] : dist) {
            if (dest == id) continue;
            // Trace back to find next hop
            int node = dest;
            while (prev.count(node) && prev[node] != id) {
                node = prev[node];
            }
            RouteEntry entry;
            entry.dest = dest;
            entry.next_hop = node;
            entry.cost = d;
            routing_table[dest] = entry;
        }
    }

    // Try to route a message; returns path or empty if unreachable
    std::vector<int> get_path_to(int dest) const {
        std::vector<int> path;
        if (dest == id) {
            path.push_back(id);
            return path;
        }
        auto it = routing_table.find(dest);
        if (it == routing_table.end()) return path; // unreachable
        path.push_back(id);
        // We only know next_hop, so return partial info
        path.push_back(it->second.next_hop);
        return path;
    }
};

// ============================================================
// Network
// ============================================================
class Network {
public:
    int num_routers;
    std::vector<Router> routers;
    std::vector<Link> links;
    std::mt19937 rng;

    Network(int n, unsigned seed) : num_routers(n), rng(seed) {
        routers.resize(n);
        for (int i = 0; i < n; i++) {
            routers[i] = Router(i, n);
        }
    }

    void add_link(int a, int b, int cost = 1) {
        links.push_back({a, b, cost, true});
    }

    // Get active neighbors of router r
    std::vector<std::pair<int,int>> get_active_neighbors(int r) const {
        std::vector<std::pair<int,int>> result;
        for (auto& link : links) {
            if (!link.active) continue;
            if (link.router_a == r) result.push_back({link.router_b, link.cost});
            else if (link.router_b == r) result.push_back({link.router_a, link.cost});
        }
        return result;
    }

    // Full OSPF convergence: all routers generate LSAs, flood, compute SPF
    // Returns number of ticks (rounds of flooding) to converge
    int converge() {
        // Phase 1: Each router generates its own LSA
        for (int i = 0; i < num_routers; i++) {
            auto neighbors = get_active_neighbors(i);
            LSA lsa = routers[i].generate_lsa(neighbors);
            routers[i].outgoing_lsas.push(lsa);
        }

        // Phase 2: Flood LSAs until no more updates
        int ticks = 0;
        bool changed = true;
        while (changed) {
            changed = false;
            ticks++;

            // Collect all LSAs to distribute
            std::vector<std::pair<int, LSA>> to_distribute;
            for (int i = 0; i < num_routers; i++) {
                while (!routers[i].outgoing_lsas.empty()) {
                    LSA lsa = routers[i].outgoing_lsas.front();
                    routers[i].outgoing_lsas.pop();
                    // Send to all active neighbors
                    auto neighbors = get_active_neighbors(i);
                    for (auto& [nb, cost] : neighbors) {
                        to_distribute.push_back({nb, lsa});
                    }
                }
            }

            // Deliver LSAs
            for (auto& [receiver, lsa] : to_distribute) {
                if (routers[receiver].receive_lsa(lsa)) {
                    changed = true;
                    routers[receiver].outgoing_lsas.push(lsa);
                }
            }
        }

        // Phase 3: Each router computes SPF
        for (int i = 0; i < num_routers; i++) {
            routers[i].compute_spf();
        }

        return ticks;
    }

    // Route a message from src to dst using hop-by-hop routing tables
    // Returns the full path, or empty if unreachable
    std::vector<int> route_message(int src, int dst) const {
        std::vector<int> path;
        std::set<int> visited;
        int current = src;
        path.push_back(current);

        while (current != dst) {
            visited.insert(current);
            auto it = routers[current].routing_table.find(dst);
            if (it == routers[current].routing_table.end()) {
                return {}; // unreachable
            }
            int next = it->second.next_hop;

            // Verify link is active
            bool link_ok = false;
            for (auto& link : links) {
                if (!link.active) continue;
                if ((link.router_a == current && link.router_b == next) ||
                    (link.router_b == current && link.router_a == next)) {
                    link_ok = true;
                    break;
                }
            }
            if (!link_ok || visited.count(next)) {
                return {}; // broken route
            }
            current = next;
            path.push_back(current);
        }
        return path;
    }

    // Break a random active link
    int break_random_link() {
        std::vector<int> active_indices;
        for (int i = 0; i < (int)links.size(); i++) {
            if (links[i].active) active_indices.push_back(i);
        }
        if (active_indices.empty()) return -1;
        std::uniform_int_distribution<int> dist(0, active_indices.size() - 1);
        int idx = active_indices[dist(rng)];
        links[idx].active = false;
        return idx;
    }

    // Restore a link
    void restore_link(int idx) {
        if (idx >= 0 && idx < (int)links.size()) {
            links[idx].active = true;
        }
    }

    // Break links with given probability
    std::vector<int> stochastic_break(double prob) {
        std::vector<int> broken;
        std::uniform_real_distribution<double> dist(0.0, 1.0);
        for (int i = 0; i < (int)links.size(); i++) {
            if (links[i].active && dist(rng) < prob) {
                links[i].active = false;
                broken.push_back(i);
            }
        }
        return broken;
    }

    void restore_all_links() {
        for (auto& link : links) link.active = true;
    }

    // Check if all routers can reach all other routers
    bool is_fully_connected() const {
        // BFS from router 0
        std::set<int> visited;
        std::queue<int> bfs;
        bfs.push(0);
        visited.insert(0);
        while (!bfs.empty()) {
            int u = bfs.front(); bfs.pop();
            for (auto& link : links) {
                if (!link.active) continue;
                int neighbor = -1;
                if (link.router_a == u) neighbor = link.router_b;
                else if (link.router_b == u) neighbor = link.router_a;
                if (neighbor >= 0 && !visited.count(neighbor)) {
                    visited.insert(neighbor);
                    bfs.push(neighbor);
                }
            }
        }
        return (int)visited.size() == num_routers;
    }

    // Check if routing tables are consistent (every reachable pair has correct shortest path)
    bool verify_routing_tables() const {
        // BFS shortest paths as ground truth
        for (int src = 0; src < num_routers; src++) {
            // BFS from src
            std::map<int, int> true_dist;
            std::queue<int> bfs;
            true_dist[src] = 0;
            bfs.push(src);
            while (!bfs.empty()) {
                int u = bfs.front(); bfs.pop();
                for (auto& link : links) {
                    if (!link.active) continue;
                    int neighbor = -1;
                    if (link.router_a == u) neighbor = link.router_b;
                    else if (link.router_b == u) neighbor = link.router_a;
                    if (neighbor >= 0 && !true_dist.count(neighbor)) {
                        true_dist[neighbor] = true_dist[u] + link.cost;
                        bfs.push(neighbor);
                    }
                }
            }

            // Verify routing table entries
            for (auto& [dest, entry] : routers[src].routing_table) {
                if (true_dist.count(dest) && entry.cost != true_dist[dest]) {
                    return false;
                }
            }
            // Check no missing reachable destinations
            for (auto& [dest, d] : true_dist) {
                if (dest == src) continue;
                if (!routers[src].routing_table.count(dest)) {
                    return false;
                }
            }
        }
        return true;
    }

    // Print routing table for a router
    void print_routing_table(int router_id) const {
        std::cerr << "Router " << router_id << " routing table:\n";
        std::cerr << "  Dest  NextHop  Cost\n";
        for (auto& [dest, entry] : routers[router_id].routing_table) {
            std::cerr << "  " << std::setw(4) << dest
                      << "  " << std::setw(7) << entry.next_hop
                      << "  " << std::setw(4) << entry.cost << "\n";
        }
    }
};

// ============================================================
// Topology builders
// ============================================================
Network build_linear(int n, unsigned seed) {
    Network net(n, seed);
    for (int i = 0; i < n - 1; i++) {
        net.add_link(i, i + 1, 1);
    }
    return net;
}

Network build_ring(int n, unsigned seed) {
    Network net(n, seed);
    for (int i = 0; i < n; i++) {
        net.add_link(i, (i + 1) % n, 1);
    }
    return net;
}

Network build_star(int n, unsigned seed) {
    // Router 0 is the center
    Network net(n, seed);
    for (int i = 1; i < n; i++) {
        net.add_link(0, i, 1);
    }
    return net;
}

// ============================================================
// Experiments
// ============================================================
struct ExperimentResult {
    std::string topology;
    int num_routers;
    int convergence_ticks;
    bool tables_correct;
    int total_routes;
    double avg_path_length;

    // For link failure experiments
    double failure_prob;
    int links_broken;
    int reconvergence_ticks;
    bool tables_correct_after;
    int reachable_pairs;
    int total_pairs;
};

void run_topology_experiment(const std::string& topo_name,
                             std::function<Network(int, unsigned)> builder,
                             int n, unsigned seed,
                             std::vector<ExperimentResult>& results) {
    Network net = builder(n, seed);

    // Initial convergence
    int ticks = net.converge();
    bool correct = net.verify_routing_tables();

    // Compute average path length
    double total_path_len = 0;
    int path_count = 0;
    for (int s = 0; s < n; s++) {
        for (int d = 0; d < n; d++) {
            if (s == d) continue;
            auto path = net.route_message(s, d);
            if (!path.empty()) {
                total_path_len += path.size() - 1;
                path_count++;
            }
        }
    }

    ExperimentResult res;
    res.topology = topo_name;
    res.num_routers = n;
    res.convergence_ticks = ticks;
    res.tables_correct = correct;
    res.total_routes = path_count;
    res.avg_path_length = path_count > 0 ? total_path_len / path_count : 0;
    res.failure_prob = 0;
    res.links_broken = 0;
    res.reconvergence_ticks = 0;
    res.tables_correct_after = true;
    res.reachable_pairs = path_count;
    res.total_pairs = n * (n - 1);
    results.push_back(res);
}

void run_failure_experiment(const std::string& topo_name,
                            std::function<Network(int, unsigned)> builder,
                            int n, double fail_prob, unsigned seed,
                            std::vector<ExperimentResult>& results) {
    Network net = builder(n, seed);

    // Initial convergence
    net.converge();

    // Break links stochastically
    auto broken = net.stochastic_break(fail_prob);

    // Reconverge
    int ticks = net.converge();
    bool correct = net.verify_routing_tables();

    // Count reachable pairs
    int reachable = 0;
    double total_path_len = 0;
    for (int s = 0; s < n; s++) {
        for (int d = 0; d < n; d++) {
            if (s == d) continue;
            auto path = net.route_message(s, d);
            if (!path.empty()) {
                reachable++;
                total_path_len += path.size() - 1;
            }
        }
    }

    ExperimentResult res;
    res.topology = topo_name;
    res.num_routers = n;
    res.convergence_ticks = 0;
    res.tables_correct = true;
    res.total_routes = 0;
    res.avg_path_length = reachable > 0 ? total_path_len / reachable : 0;
    res.failure_prob = fail_prob;
    res.links_broken = broken.size();
    res.reconvergence_ticks = ticks;
    res.tables_correct_after = correct;
    res.reachable_pairs = reachable;
    res.total_pairs = n * (n - 1);
    results.push_back(res);
}

// ============================================================
// Main
// ============================================================
int main() {
    std::cout << std::fixed << std::setprecision(2);

    const int NUM_ROUTERS = 10;
    const unsigned BASE_SEED = 42;
    const int NUM_FAILURE_RUNS = 20;

    std::vector<std::string> topo_names = {"linear", "ring", "star"};
    std::vector<std::function<Network(int, unsigned)>> builders = {
        build_linear, build_ring, build_star
    };

    // === Part 1: Basic convergence ===
    std::cout << "=== PART 1: Initial Convergence (N=" << NUM_ROUTERS << ") ===" << std::endl;
    std::cout << "topology,num_routers,convergence_ticks,tables_correct,reachable_pairs,total_pairs,avg_path_length" << std::endl;

    std::vector<ExperimentResult> basic_results;
    for (int t = 0; t < 3; t++) {
        run_topology_experiment(topo_names[t], builders[t], NUM_ROUTERS, BASE_SEED, basic_results);
        auto& r = basic_results.back();
        std::cout << r.topology << "," << r.num_routers << ","
                  << r.convergence_ticks << "," << (r.tables_correct ? "yes" : "no") << ","
                  << r.reachable_pairs << "," << r.total_pairs << ","
                  << r.avg_path_length << std::endl;
    }

    // Print sample routing tables
    std::cerr << "\n=== Sample Routing Tables (N=" << NUM_ROUTERS << ") ===\n\n";
    for (int t = 0; t < 3; t++) {
        Network net = builders[t](NUM_ROUTERS, BASE_SEED);
        net.converge();
        std::cerr << "--- " << topo_names[t] << " topology ---\n";
        net.print_routing_table(0);
        if (NUM_ROUTERS > 3) net.print_routing_table(NUM_ROUTERS / 2);
        std::cerr << "\n";
    }

    // === Part 2: Scalability ===
    std::cout << "\n=== PART 2: Scalability ===" << std::endl;
    std::cout << "topology,num_routers,convergence_ticks,avg_path_length" << std::endl;

    for (int n : {5, 10, 20, 50}) {
        for (int t = 0; t < 3; t++) {
            std::vector<ExperimentResult> res;
            run_topology_experiment(topo_names[t], builders[t], n, BASE_SEED, res);
            auto& r = res.back();
            std::cout << r.topology << "," << n << "," << r.convergence_ticks << ","
                      << r.avg_path_length << std::endl;
        }
    }

    // === Part 3: Stochastic link failures ===
    std::cout << "\n=== PART 3: Stochastic Link Failures (N=" << NUM_ROUTERS << ") ===" << std::endl;
    std::cout << "topology,failure_prob,avg_links_broken,avg_reconvergence_ticks,"
              << "avg_reachable_ratio,tables_always_correct,avg_path_length" << std::endl;

    std::vector<double> fail_probs = {0.0, 0.10, 0.20, 0.30, 0.50};

    for (int t = 0; t < 3; t++) {
        for (double fp : fail_probs) {
            double total_broken = 0, total_ticks = 0, total_reach = 0;
            double total_path_len = 0;
            int path_count = 0;
            bool always_correct = true;

            for (int run = 0; run < NUM_FAILURE_RUNS; run++) {
                std::vector<ExperimentResult> res;
                run_failure_experiment(topo_names[t], builders[t], NUM_ROUTERS,
                                      fp, BASE_SEED + run, res);
                auto& r = res.back();
                total_broken += r.links_broken;
                total_ticks += r.reconvergence_ticks;
                total_reach += (double)r.reachable_pairs / r.total_pairs;
                if (r.reachable_pairs > 0) {
                    total_path_len += r.avg_path_length;
                    path_count++;
                }
                if (!r.tables_correct_after) always_correct = false;
            }

            std::cout << topo_names[t] << "," << fp << ","
                      << total_broken / NUM_FAILURE_RUNS << ","
                      << total_ticks / NUM_FAILURE_RUNS << ","
                      << total_reach / NUM_FAILURE_RUNS << ","
                      << (always_correct ? "yes" : "no") << ","
                      << (path_count > 0 ? total_path_len / path_count : 0) << std::endl;
        }
    }

    // === Part 4: Single link failure and recovery ===
    std::cout << "\n=== PART 4: Single Link Failure & Recovery ===" << std::endl;
    std::cout << "topology,event,convergence_ticks,reachable_pairs,tables_correct" << std::endl;

    for (int t = 0; t < 3; t++) {
        Network net = builders[t](NUM_ROUTERS, BASE_SEED);

        // Initial
        int ticks = net.converge();
        int reachable = 0;
        for (int s = 0; s < NUM_ROUTERS; s++)
            for (int d = 0; d < NUM_ROUTERS; d++)
                if (s != d && !net.route_message(s, d).empty()) reachable++;
        bool correct = net.verify_routing_tables();
        std::cout << topo_names[t] << ",initial," << ticks << "," << reachable << ","
                  << (correct ? "yes" : "no") << std::endl;

        // Break link 0
        net.links[0].active = false;
        ticks = net.converge();
        reachable = 0;
        for (int s = 0; s < NUM_ROUTERS; s++)
            for (int d = 0; d < NUM_ROUTERS; d++)
                if (s != d && !net.route_message(s, d).empty()) reachable++;
        correct = net.verify_routing_tables();
        std::cout << topo_names[t] << ",link_break," << ticks << "," << reachable << ","
                  << (correct ? "yes" : "no") << std::endl;

        // Restore link 0
        net.links[0].active = true;
        ticks = net.converge();
        reachable = 0;
        for (int s = 0; s < NUM_ROUTERS; s++)
            for (int d = 0; d < NUM_ROUTERS; d++)
                if (s != d && !net.route_message(s, d).empty()) reachable++;
        correct = net.verify_routing_tables();
        std::cout << topo_names[t] << ",link_restore," << ticks << "," << reachable << ","
                  << (correct ? "yes" : "no") << std::endl;
    }

    // === Part 5: Demonstration of hop-by-hop routing ===
    std::cerr << "\n=== Hop-by-hop Routing Demonstration ===\n\n";
    for (int t = 0; t < 3; t++) {
        Network net = builders[t](NUM_ROUTERS, BASE_SEED);
        net.converge();
        std::cerr << "--- " << topo_names[t] << " ---\n";
        // Route from 0 to last, and from 0 to middle
        for (int dst : {NUM_ROUTERS - 1, NUM_ROUTERS / 2}) {
            auto path = net.route_message(0, dst);
            std::cerr << "  0 -> " << dst << ": ";
            if (path.empty()) {
                std::cerr << "UNREACHABLE";
            } else {
                for (int i = 0; i < (int)path.size(); i++) {
                    if (i > 0) std::cerr << " -> ";
                    std::cerr << path[i];
                }
            }
            std::cerr << "\n";
        }
    }

    return 0;
}
