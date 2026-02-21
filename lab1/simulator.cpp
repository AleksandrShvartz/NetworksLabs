#include <iostream>
#include <vector>
#include <queue>
#include <random>
#include <algorithm>
#include <cstring>
#include <iomanip>
#include <set>
#include <map>
#include <functional>
#include <sstream>

// ============================================================
// Packet structure
// ============================================================
struct Packet {
    int seq_num;
    char data;
    bool is_ack;
    int ack_num;
};

// ============================================================
// Statistics
// ============================================================
struct Stats {
    int total_packets_sent = 0;
    int total_acks_sent = 0;
    int packets_lost = 0;
    int acks_lost = 0;
    int retransmissions = 0;
    int total_data_packets = 0; // unique data packets needed
    int ticks = 0;

    double efficiency() const {
        if (total_packets_sent == 0) return 0.0;
        return (double)total_data_packets / total_packets_sent;
    }

    double throughput() const {
        if (ticks == 0) return 0.0;
        return (double)total_data_packets / ticks;
    }
};

// ============================================================
// Lossy Channel
// ============================================================
class Channel {
public:
    Channel(double loss_prob, std::mt19937& rng)
        : loss_prob_(loss_prob), rng_(rng), dist_(0.0, 1.0) {}

    bool transmit(const Packet& pkt, std::queue<Packet>& dest) {
        if (dist_(rng_) < loss_prob_) {
            return false; // lost
        }
        dest.push(pkt);
        return true;
    }

private:
    double loss_prob_;
    std::mt19937& rng_;
    std::uniform_real_distribution<double> dist_;
};

// ============================================================
// Go-Back-N Protocol
// ============================================================
class GBN_Sender {
public:
    GBN_Sender(int window_size, int total, int timeout)
        : window_size_(window_size), total_(total), timeout_(timeout),
          base_(0), next_seq_(0), timer_(0) {}

    bool is_done() const { return base_ >= total_; }

    void send(Channel& ch, std::queue<Packet>& to_receiver, Stats& stats) {
        while (next_seq_ < base_ + window_size_ && next_seq_ < total_) {
            Packet pkt;
            pkt.seq_num = next_seq_;
            pkt.data = 'A' + (next_seq_ % 26);
            pkt.is_ack = false;
            pkt.ack_num = -1;

            bool delivered = ch.transmit(pkt, to_receiver);
            stats.total_packets_sent++;
            if (!delivered) stats.packets_lost++;

            if (next_seq_ == base_) timer_ = 0;
            next_seq_++;
        }
    }

    void receive_ack(std::queue<Packet>& from_receiver) {
        while (!from_receiver.empty()) {
            Packet ack = from_receiver.front();
            from_receiver.pop();
            if (ack.ack_num >= base_) {
                base_ = ack.ack_num + 1;
                // Restart timer for new base packet
                if (base_ < total_) {
                    timer_ = 0;
                }
            }
        }
    }

    void tick(Channel& ch, std::queue<Packet>& to_receiver, Stats& stats) {
        // Single timer for the oldest unacked packet
        if (base_ < total_ && base_ < next_seq_) {
            timer_++;
            if (timer_ >= timeout_) {
                // Timeout: retransmit all from base
                next_seq_ = base_;
                for (int i = base_; i < std::min(base_ + window_size_, total_); i++) {
                    Packet pkt;
                    pkt.seq_num = i;
                    pkt.data = 'A' + (i % 26);
                    pkt.is_ack = false;
                    pkt.ack_num = -1;

                    bool delivered = ch.transmit(pkt, to_receiver);
                    stats.total_packets_sent++;
                    stats.retransmissions++;
                    if (!delivered) stats.packets_lost++;

                    next_seq_ = i + 1;
                }
                timer_ = 0;
            }
        }
    }

private:
    int window_size_;
    int total_;
    int timeout_;
    int base_;
    int next_seq_;
    int timer_;
};

class GBN_Receiver {
public:
    GBN_Receiver() : expected_seq_(0) {}

    void receive(std::queue<Packet>& from_sender, Channel& ch,
                 std::queue<Packet>& to_sender, Stats& stats) {
        while (!from_sender.empty()) {
            Packet pkt = from_sender.front();
            from_sender.pop();

            if (pkt.seq_num == expected_seq_) {
                received_data_.push_back(pkt.data);
                Packet ack;
                ack.is_ack = true;
                ack.ack_num = expected_seq_;
                ack.seq_num = -1;

                bool delivered = ch.transmit(ack, to_sender);
                stats.total_acks_sent++;
                if (!delivered) stats.acks_lost++;

                expected_seq_++;
            } else if (expected_seq_ > 0) {
                // Discard and send ack for last correctly received
                Packet ack;
                ack.is_ack = true;
                ack.ack_num = expected_seq_ - 1;
                ack.seq_num = -1;

                bool delivered = ch.transmit(ack, to_sender);
                stats.total_acks_sent++;
                if (!delivered) stats.acks_lost++;
            }
        }
    }

    const std::vector<char>& data() const { return received_data_; }

private:
    int expected_seq_;
    std::vector<char> received_data_;
};

// ============================================================
// Selective Repeat Protocol
// ============================================================
class SR_Sender {
public:
    SR_Sender(int window_size, int total, int timeout)
        : window_size_(window_size), total_(total), timeout_(timeout),
          base_(0), next_seq_(0) {
        timers_.resize(total, -1);
        acked_.resize(total, false);
    }

    bool is_done() const { return base_ >= total_; }

    void send(Channel& ch, std::queue<Packet>& to_receiver, Stats& stats) {
        while (next_seq_ < base_ + window_size_ && next_seq_ < total_) {
            Packet pkt;
            pkt.seq_num = next_seq_;
            pkt.data = 'A' + (next_seq_ % 26);
            pkt.is_ack = false;
            pkt.ack_num = -1;

            bool delivered = ch.transmit(pkt, to_receiver);
            stats.total_packets_sent++;
            if (!delivered) stats.packets_lost++;

            timers_[next_seq_] = 0;
            next_seq_++;
        }
    }

    void receive_ack(std::queue<Packet>& from_receiver) {
        while (!from_receiver.empty()) {
            Packet ack = from_receiver.front();
            from_receiver.pop();
            if (ack.ack_num >= base_ && ack.ack_num < base_ + window_size_) {
                acked_[ack.ack_num] = true;
                // Slide window
                while (base_ < total_ && acked_[base_]) {
                    base_++;
                }
            }
        }
    }

    void tick(Channel& ch, std::queue<Packet>& to_receiver, Stats& stats) {
        for (int i = base_; i < next_seq_ && i < base_ + window_size_; i++) {
            if (!acked_[i] && timers_[i] >= 0) {
                timers_[i]++;
                if (timers_[i] >= timeout_) {
                    // Retransmit only this packet
                    Packet pkt;
                    pkt.seq_num = i;
                    pkt.data = 'A' + (i % 26);
                    pkt.is_ack = false;
                    pkt.ack_num = -1;

                    bool delivered = ch.transmit(pkt, to_receiver);
                    stats.total_packets_sent++;
                    stats.retransmissions++;
                    if (!delivered) stats.packets_lost++;

                    timers_[i] = 0;
                }
            }
        }
    }

private:
    int window_size_;
    int total_;
    int timeout_;
    int base_;
    int next_seq_;
    std::vector<int> timers_;
    std::vector<bool> acked_;
};

class SR_Receiver {
public:
    SR_Receiver(int window_size, int total)
        : window_size_(window_size), total_(total), expected_seq_(0) {
        buffered_.resize(total, false);
        buffer_data_.resize(total, 0);
    }

    void receive(std::queue<Packet>& from_sender, Channel& ch,
                 std::queue<Packet>& to_sender, Stats& stats) {
        while (!from_sender.empty()) {
            Packet pkt = from_sender.front();
            from_sender.pop();

            if (pkt.seq_num >= expected_seq_ &&
                pkt.seq_num < expected_seq_ + window_size_) {
                buffered_[pkt.seq_num] = true;
                buffer_data_[pkt.seq_num] = pkt.data;

                Packet ack;
                ack.is_ack = true;
                ack.ack_num = pkt.seq_num;
                ack.seq_num = -1;

                bool delivered = ch.transmit(ack, to_sender);
                stats.total_acks_sent++;
                if (!delivered) stats.acks_lost++;

                // Deliver in-order data
                while (expected_seq_ < total_ && buffered_[expected_seq_]) {
                    received_data_.push_back(buffer_data_[expected_seq_]);
                    expected_seq_++;
                }
            } else if (pkt.seq_num < expected_seq_) {
                // Re-ack
                Packet ack;
                ack.is_ack = true;
                ack.ack_num = pkt.seq_num;
                ack.seq_num = -1;

                bool delivered = ch.transmit(ack, to_sender);
                stats.total_acks_sent++;
                if (!delivered) stats.acks_lost++;
            }
        }
    }

    const std::vector<char>& data() const { return received_data_; }

private:
    int window_size_;
    int total_;
    int expected_seq_;
    std::vector<bool> buffered_;
    std::vector<char> buffer_data_;
    std::vector<char> received_data_;
};

// ============================================================
// Simulation runners
// ============================================================
Stats run_gbn(int total_packets, int window_size, double loss_prob,
              int timeout, unsigned seed) {
    std::mt19937 rng(seed);
    Channel forward_ch(loss_prob, rng);
    Channel reverse_ch(loss_prob, rng);

    std::queue<Packet> to_receiver, to_sender;
    GBN_Sender sender(window_size, total_packets, timeout);
    GBN_Receiver receiver;
    Stats stats;
    stats.total_data_packets = total_packets;

    const int MAX_TICKS = 1000000;
    int tick = 0;

    while (!sender.is_done() && tick < MAX_TICKS) {
        sender.send(forward_ch, to_receiver, stats);
        receiver.receive(to_receiver, reverse_ch, to_sender, stats);
        sender.receive_ack(to_sender);
        sender.tick(forward_ch, to_receiver, stats);
        tick++;
    }

    stats.ticks = tick;
    return stats;
}

Stats run_sr(int total_packets, int window_size, double loss_prob,
             int timeout, unsigned seed) {
    std::mt19937 rng(seed);
    Channel forward_ch(loss_prob, rng);
    Channel reverse_ch(loss_prob, rng);

    std::queue<Packet> to_receiver, to_sender;
    SR_Sender sender(window_size, total_packets, timeout);
    SR_Receiver receiver(window_size, total_packets);
    Stats stats;
    stats.total_data_packets = total_packets;

    const int MAX_TICKS = 1000000;
    int tick = 0;

    while (!sender.is_done() && tick < MAX_TICKS) {
        sender.send(forward_ch, to_receiver, stats);
        receiver.receive(to_receiver, reverse_ch, to_sender, stats);
        sender.receive_ack(to_sender);
        sender.tick(forward_ch, to_receiver, stats);
        tick++;
    }

    stats.ticks = tick;
    return stats;
}

// ============================================================
// Main: run experiments and output results
// ============================================================
int main() {
    const int TOTAL_PACKETS = 1000;
    const int TIMEOUT = 10;
    const int NUM_RUNS = 5;

    std::vector<int> window_sizes = {1, 2, 4, 8, 16, 32};
    std::vector<double> loss_probs = {0.0, 0.05, 0.10, 0.20, 0.30, 0.50};

    std::cout << std::fixed << std::setprecision(4);

    // CSV header for easy parsing
    std::cout << "protocol,window_size,loss_prob,avg_efficiency,avg_throughput,"
              << "avg_packets_sent,avg_retransmissions,avg_ticks" << std::endl;

    for (double loss : loss_probs) {
        for (int ws : window_sizes) {
            // GBN
            double gbn_eff = 0, gbn_tp = 0, gbn_sent = 0, gbn_retr = 0, gbn_ticks = 0;
            for (int r = 0; r < NUM_RUNS; r++) {
                Stats s = run_gbn(TOTAL_PACKETS, ws, loss, TIMEOUT, 42 + r);
                gbn_eff += s.efficiency();
                gbn_tp += s.throughput();
                gbn_sent += s.total_packets_sent;
                gbn_retr += s.retransmissions;
                gbn_ticks += s.ticks;
            }
            std::cout << "GBN," << ws << "," << loss << ","
                      << gbn_eff / NUM_RUNS << ","
                      << gbn_tp / NUM_RUNS << ","
                      << gbn_sent / NUM_RUNS << ","
                      << gbn_retr / NUM_RUNS << ","
                      << gbn_ticks / NUM_RUNS << std::endl;

            // SR
            double sr_eff = 0, sr_tp = 0, sr_sent = 0, sr_retr = 0, sr_ticks = 0;
            for (int r = 0; r < NUM_RUNS; r++) {
                Stats s = run_sr(TOTAL_PACKETS, ws, loss, TIMEOUT, 42 + r);
                sr_eff += s.efficiency();
                sr_tp += s.throughput();
                sr_sent += s.total_packets_sent;
                sr_retr += s.retransmissions;
                sr_ticks += s.ticks;
            }
            std::cout << "SR," << ws << "," << loss << ","
                      << sr_eff / NUM_RUNS << ","
                      << sr_tp / NUM_RUNS << ","
                      << sr_sent / NUM_RUNS << ","
                      << sr_retr / NUM_RUNS << ","
                      << sr_ticks / NUM_RUNS << std::endl;
        }
    }

    return 0;
}
