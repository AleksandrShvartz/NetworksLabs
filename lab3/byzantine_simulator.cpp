// ============================================================
// Byzantine Generals Problem — Lamport-Shostak-Pease Simulator
// ============================================================
#include <iostream>
#include <vector>
#include <map>
#include <set>
#include <algorithm>
#include <random>
#include <iomanip>
#include <string>
#include <numeric>
#include <cmath>
#include <functional>
#include <sstream>

// ============================================================
// Core Types
// ============================================================

enum ByzantineStrategy { RANDOM, ALWAYS_ZERO, ALWAYS_OPPOSITE, SPLIT };

std::string strategy_name(ByzantineStrategy s) {
    switch (s) {
        case RANDOM:          return "RANDOM";
        case ALWAYS_ZERO:     return "ALWAYS_ZERO";
        case ALWAYS_OPPOSITE: return "ALWAYS_OPPOSITE";
        case SPLIT:           return "SPLIT";
    }
    return "UNKNOWN";
}

struct General {
    int id;
    bool is_byzantine;
    ByzantineStrategy strategy;
    int initial_value; // 0 or 1
    std::mt19937 rng;

    General() : id(0), is_byzantine(false), strategy(RANDOM), initial_value(0), rng(0) {}

    General(int id, bool byz, ByzantineStrategy strat, int val, unsigned seed)
        : id(id), is_byzantine(byz), strategy(strat), initial_value(val), rng(seed) {}

    int get_send_value(int honest_value, int recipient_id, int total_recipients) {
        if (!is_byzantine) return honest_value;
        switch (strategy) {
            case RANDOM: {
                std::uniform_int_distribution<int> dist(0, 1);
                return dist(rng);
            }
            case ALWAYS_ZERO:
                return 0;
            case ALWAYS_OPPOSITE:
                return 1 - honest_value;
            case SPLIT:
                return (recipient_id < total_recipients / 2) ? 0 : 1;
        }
        return honest_value;
    }
};

struct SimResult {
    int n;
    int m;
    bool agreement;     // IC1: all loyal lieutenants agree
    bool correctness;   // IC2: if commander is loyal, they agree on his value
    int message_count;
    int commander_id;
    int commander_value;
    bool commander_byzantine;
};

// ============================================================
// OM(m) Algorithm
// ============================================================

int g_message_count = 0;
bool g_debug = false;

int majority_vote(const std::vector<int>& values) {
    int count0 = 0, count1 = 0;
    for (int v : values) {
        if (v == 0) count0++;
        else if (v == 1) count1++;
    }
    if (count0 > count1) return 0;
    if (count1 > count0) return 1;
    return 0; // tie-break: default 0
}

// OM(m) algorithm
// commander: index of commander in `participants`
// participants: list of general IDs participating
// generals: reference to all generals
// m: recursion depth
// returns: map from general_id -> decided value
std::map<int, int> om_algorithm(
    int commander_idx,
    const std::vector<int>& participants,
    std::vector<General>& generals,
    int m,
    int depth = 0)
{
    std::map<int, int> decisions;
    int cmd_id = participants[commander_idx];
    General& cmd = generals[cmd_id];

    // Lieutenants = participants minus commander
    std::vector<int> lieutenants;
    for (int i = 0; i < (int)participants.size(); i++) {
        if (i != commander_idx) {
            lieutenants.push_back(participants[i]);
        }
    }

    if (m == 0) {
        // OM(0): Commander sends value to each lieutenant
        for (int lt_id : lieutenants) {
            int val = cmd.get_send_value(cmd.initial_value, lt_id, (int)lieutenants.size());
            g_message_count++;
            decisions[lt_id] = val;

            if (g_debug) {
                std::string indent(depth * 2, ' ');
                std::cerr << indent << "OM(0): General " << cmd_id
                          << " -> General " << lt_id << ": " << val << "\n";
            }
        }
        return decisions;
    }

    // OM(m), m > 0
    // Step 1: Commander sends value to each lieutenant
    std::map<int, int> received; // lt_id -> value received from commander
    for (int lt_id : lieutenants) {
        int val = cmd.get_send_value(cmd.initial_value, lt_id, (int)lieutenants.size());
        g_message_count++;
        received[lt_id] = val;

        if (g_debug) {
            std::string indent(depth * 2, ' ');
            std::cerr << indent << "OM(" << m << "): General " << cmd_id
                      << " -> General " << lt_id << ": " << val << "\n";
        }
    }

    // Step 2: Each lieutenant i acts as commander for OM(m-1)
    // among remaining participants (lieutenants minus self)
    // sub_values[lt_id][sender_id] = value that lt_id decides for sender_id's sub-round
    std::map<int, std::map<int, int>> sub_values;

    for (int i = 0; i < (int)lieutenants.size(); i++) {
        int lt_i = lieutenants[i];
        // Save and set initial_value for sub-commander
        int saved_val = generals[lt_i].initial_value;
        generals[lt_i].initial_value = received[lt_i];

        // Sub-participants: all lieutenants, with lt_i as commander
        std::vector<int> sub_participants = lieutenants;
        int sub_cmd_idx = i; // lt_i's position in lieutenants

        auto sub_decisions = om_algorithm(sub_cmd_idx, sub_participants, generals, m - 1, depth + 1);

        // Each lieutenant j gets a value from lt_i's sub-round
        for (auto& [lt_j, val] : sub_decisions) {
            sub_values[lt_j][lt_i] = val;
        }

        generals[lt_i].initial_value = saved_val;
    }

    // Step 3: Each lieutenant takes majority of values
    for (int lt_id : lieutenants) {
        std::vector<int> vals;
        // Value from commander (received directly) — used as lt_id's own report
        vals.push_back(received[lt_id]);
        // Values reported by other lieutenants via OM(m-1)
        for (auto& [sender_id, val] : sub_values[lt_id]) {
            vals.push_back(val);
        }
        decisions[lt_id] = majority_vote(vals);
    }

    return decisions;
}

// ============================================================
// Theoretical Message Count
// ============================================================

long long theoretical_messages(int n, int m) {
    if (m == 0) return n - 1;
    return (long long)(n - 1) + (long long)(n - 1) * theoretical_messages(n - 1, m - 1);
}

// ============================================================
// Run Single Simulation
// ============================================================

SimResult run_simulation(
    int n, int m,
    int commander_id,
    const std::set<int>& byzantine_ids,
    ByzantineStrategy strategy,
    int commander_value,
    unsigned seed)
{
    std::mt19937 master_rng(seed);
    std::vector<General> generals(n);
    for (int i = 0; i < n; i++) {
        bool byz = byzantine_ids.count(i) > 0;
        generals[i] = General(i, byz, strategy, (i == commander_id) ? commander_value : 0,
                              master_rng());
    }

    // Set initial value for commander
    generals[commander_id].initial_value = commander_value;

    g_message_count = 0;

    std::vector<int> participants(n);
    std::iota(participants.begin(), participants.end(), 0);

    // Find commander index in participants
    int cmd_idx = commander_id;

    auto decisions = om_algorithm(cmd_idx, participants, generals, m);

    // Evaluate: check loyal lieutenants
    std::vector<int> loyal_decisions;
    for (auto& [lt_id, val] : decisions) {
        if (byzantine_ids.count(lt_id) == 0) {
            loyal_decisions.push_back(val);
        }
    }

    bool agreement = true;
    if (!loyal_decisions.empty()) {
        for (size_t i = 1; i < loyal_decisions.size(); i++) {
            if (loyal_decisions[i] != loyal_decisions[0]) {
                agreement = false;
                break;
            }
        }
    }

    bool correctness = true;
    bool cmd_is_byz = byzantine_ids.count(commander_id) > 0;
    if (!cmd_is_byz && agreement && !loyal_decisions.empty()) {
        correctness = (loyal_decisions[0] == commander_value);
    } else if (cmd_is_byz) {
        correctness = agreement; // IC2 only applies to loyal commander
    }

    SimResult res;
    res.n = n;
    res.m = m;
    res.agreement = agreement;
    res.correctness = correctness;
    res.message_count = g_message_count;
    res.commander_id = commander_id;
    res.commander_value = commander_value;
    res.commander_byzantine = cmd_is_byz;
    return res;
}

// ============================================================
// Experiments
// ============================================================

void part1_basic_correctness() {
    std::cout << "=== PART 1: Basic Correctness (n=4, m=1) ===" << std::endl;
    std::cout << "commander,traitor,cmd_value,agreement,correctness,messages" << std::endl;

    int n = 4, m = 1;
    for (int cmd = 0; cmd < n; cmd++) {
        for (int traitor = 0; traitor < n; traitor++) {
            if (traitor == cmd) continue;
            for (int val = 0; val <= 1; val++) {
                std::set<int> byz = {traitor};
                auto res = run_simulation(n, m, cmd, byz, RANDOM, val, 42 + cmd * 100 + traitor * 10 + val);
                std::cout << cmd << "," << traitor << "," << val << ","
                          << (res.agreement ? "yes" : "no") << ","
                          << (res.correctness ? "yes" : "no") << ","
                          << res.message_count << std::endl;
            }
        }
    }
    std::cout << std::endl;
}

void part2_scaling() {
    std::cout << "=== PART 2: Scaling ===" << std::endl;
    std::cout << "n,m,trials,agreement_rate,correctness_rate,avg_messages" << std::endl;

    struct Config { int n; int m; };
    std::vector<Config> configs = {
        {4, 1}, {7, 1}, {10, 1}, {13, 1},
        {7, 2}, {10, 2}, {13, 2}
    };

    int trials = 20;
    std::mt19937 seed_gen(12345);

    for (auto& cfg : configs) {
        int agree_count = 0, correct_count = 0;
        long long total_msgs = 0;

        for (int t = 0; t < trials; t++) {
            unsigned seed = seed_gen();
            std::mt19937 trial_rng(seed);

            // Random commander
            int cmd = trial_rng() % cfg.n;
            // Random m byzantine generals (not commander for half, commander for other half)
            std::vector<int> candidates;
            for (int i = 0; i < cfg.n; i++) candidates.push_back(i);
            std::shuffle(candidates.begin(), candidates.end(), trial_rng);
            std::set<int> byz;
            for (int i = 0; i < cfg.m && (int)byz.size() < cfg.m; i++) {
                byz.insert(candidates[i]);
            }

            int val = trial_rng() % 2;
            ByzantineStrategy strat = static_cast<ByzantineStrategy>(trial_rng() % 4);

            auto res = run_simulation(cfg.n, cfg.m, cmd, byz, strat, val, seed);
            if (res.agreement) agree_count++;
            if (res.correctness) correct_count++;
            total_msgs += res.message_count;
        }

        std::cout << std::fixed << std::setprecision(2)
                  << cfg.n << "," << cfg.m << "," << trials << ","
                  << (double)agree_count / trials << ","
                  << (double)correct_count / trials << ","
                  << (double)total_msgs / trials << std::endl;
    }
    std::cout << std::endl;
}

void part3_boundary() {
    std::cout << "=== PART 3: Boundary n=3m vs n=3m+1 ===" << std::endl;
    std::cout << "n,m,constraint,trials,agreement_rate,correctness_rate" << std::endl;

    struct Config { int n; int m; std::string label; };
    std::vector<Config> configs = {
        {3, 1, "n=3m (violated)"},
        {4, 1, "n=3m+1 (satisfied)"},
        {6, 2, "n=3m (violated)"},
        {7, 2, "n=3m+1 (satisfied)"}
    };

    int trials = 50;
    std::mt19937 seed_gen(67890);

    for (auto& cfg : configs) {
        int agree_count = 0, correct_count = 0;

        for (int t = 0; t < trials; t++) {
            unsigned seed = seed_gen();
            std::mt19937 trial_rng(seed);

            int cmd = trial_rng() % cfg.n;
            std::vector<int> candidates;
            for (int i = 0; i < cfg.n; i++) candidates.push_back(i);
            std::shuffle(candidates.begin(), candidates.end(), trial_rng);
            std::set<int> byz;
            for (int i = 0; i < cfg.m && (int)byz.size() < cfg.m; i++) {
                byz.insert(candidates[i]);
            }

            int val = trial_rng() % 2;
            ByzantineStrategy strat = static_cast<ByzantineStrategy>(trial_rng() % 4);

            auto res = run_simulation(cfg.n, cfg.m, cmd, byz, strat, val, seed);
            if (res.agreement) agree_count++;
            if (res.correctness) correct_count++;
        }

        std::cout << std::fixed << std::setprecision(2)
                  << cfg.n << "," << cfg.m << ","
                  << cfg.label << ","
                  << trials << ","
                  << (double)agree_count / trials << ","
                  << (double)correct_count / trials << std::endl;
    }
    std::cout << std::endl;
}

void part4_strategies() {
    std::cout << "=== PART 4: Byzantine Strategies (n=7, m=2) ===" << std::endl;
    std::cout << "strategy,commander_type,trials,agreement_rate,correctness_rate" << std::endl;

    int n = 7, m = 2, trials = 20;
    ByzantineStrategy strategies[] = {RANDOM, ALWAYS_ZERO, ALWAYS_OPPOSITE, SPLIT};
    std::mt19937 seed_gen(11111);

    for (auto strat : strategies) {
        // Case 1: honest commander
        {
            int agree_count = 0, correct_count = 0;
            for (int t = 0; t < trials; t++) {
                unsigned seed = seed_gen();
                std::mt19937 trial_rng(seed);

                int cmd = 0; // honest commander
                // Pick m byzantines from non-commander
                std::vector<int> non_cmd;
                for (int i = 1; i < n; i++) non_cmd.push_back(i);
                std::shuffle(non_cmd.begin(), non_cmd.end(), trial_rng);
                std::set<int> byz;
                for (int i = 0; i < m; i++) byz.insert(non_cmd[i]);

                int val = trial_rng() % 2;
                auto res = run_simulation(n, m, cmd, byz, strat, val, seed);
                if (res.agreement) agree_count++;
                if (res.correctness) correct_count++;
            }
            std::cout << strategy_name(strat) << ",honest," << trials << ","
                      << std::fixed << std::setprecision(2)
                      << (double)agree_count / trials << ","
                      << (double)correct_count / trials << std::endl;
        }
        // Case 2: byzantine commander
        {
            int agree_count = 0, correct_count = 0;
            for (int t = 0; t < trials; t++) {
                unsigned seed = seed_gen();
                std::mt19937 trial_rng(seed);

                int cmd = 0; // byzantine commander
                std::set<int> byz = {0};
                // Pick m-1 more byzantines from non-commander
                std::vector<int> non_cmd;
                for (int i = 1; i < n; i++) non_cmd.push_back(i);
                std::shuffle(non_cmd.begin(), non_cmd.end(), trial_rng);
                for (int i = 0; i < m - 1; i++) byz.insert(non_cmd[i]);

                int val = trial_rng() % 2;
                auto res = run_simulation(n, m, cmd, byz, strat, val, seed);
                if (res.agreement) agree_count++;
                if (res.correctness) correct_count++;
            }
            std::cout << strategy_name(strat) << ",byzantine," << trials << ","
                      << std::fixed << std::setprecision(2)
                      << (double)agree_count / trials << ","
                      << (double)correct_count / trials << std::endl;
        }
    }
    std::cout << std::endl;
}

void part5_message_complexity() {
    std::cout << "=== PART 5: Message Complexity ===" << std::endl;
    std::cout << "n,m,actual_messages,theoretical_messages" << std::endl;

    struct Config { int n; int m; };
    std::vector<Config> configs = {
        {4, 1}, {7, 1}, {10, 1}, {13, 1}, {16, 1},
        {7, 2}, {10, 2}, {13, 2},
        {10, 3}, {13, 3}
    };

    for (auto& cfg : configs) {
        // Run one simulation with no byzantines to count messages
        std::set<int> byz = {1}; // one byzantine
        auto res = run_simulation(cfg.n, cfg.m, 0, byz, ALWAYS_ZERO, 1, 99999);
        long long theo = theoretical_messages(cfg.n, cfg.m);

        std::cout << cfg.n << "," << cfg.m << ","
                  << res.message_count << ","
                  << theo << std::endl;
    }
    std::cout << std::endl;
}

// ============================================================
// Debug Trace Example
// ============================================================

void debug_trace_example() {
    std::cerr << "=== Debug Trace: OM(1) with n=4, commander=0, traitor=3 ===" << std::endl;
    g_debug = true;

    std::set<int> byz = {3};
    run_simulation(4, 1, 0, byz, SPLIT, 1, 42);

    g_debug = false;
    std::cerr << std::endl;
}

// ============================================================
// Main
// ============================================================

int main() {
    debug_trace_example();

    part1_basic_correctness();
    part2_scaling();
    part3_boundary();
    part4_strategies();
    part5_message_complexity();

    return 0;
}
