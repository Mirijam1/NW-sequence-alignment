//
// Created by sicco on 23/04/2021.
//
#ifndef FLEXFRINGE_PREDICT_H
#define FLEXFRINGE_PREDICT_H

#include "state_merger.h"
#include "inputdata.h"

static constexpr int GAP_DISTANCE_PENALTY = -1;
static constexpr int MATCH = 2;
static constexpr int MISMATCH_PENALTY = -10;

apta_node* single_step(apta_node* n, tail* t, apta* a);
double compute_score(apta_node* next_node, tail* next_tail);
double predict_trace(state_merger* m, trace* tr);
void predict_csv(state_merger* m, istream& input, ofstream& output);
void predict(state_merger* m, istream& input, ofstream& output);

class sequence_alignment {

private:
    state_merger* merger;
    trace* tr;
    std::vector<int> tr_vec; // stores trace
    std::map<int, std::map<int, std::vector<std::tuple<apta_node*, apta_node*, int>>>> matrix;
    std::map<int, std::map<int, std::map<int, int>>> matrix_gaps; // stores gaps size in current alignment
    std::vector<std::vector<std::tuple<apta_node*, apta_node*, int>>> best; // stores optimal alignment

    int matches;
    int mismatches;
    int skips;
    int jumps;
    int trace_score;
    int normalized_trace_score;

public:
    sequence_alignment(state_merger* m, trace* trace)
        : merger(m), tr(trace), matches(0), mismatches(0), skips(0), jumps(0), trace_score(0), normalized_trace_score(0) {
        merger = m;
        tr = trace;

        tail* t = tr->get_head();
        tr_vec.push_back(0);
        best.push_back(std::vector<std::tuple<apta_node*, apta_node*, int>>(1, { nullptr, merger->get_aut()->get_root(), initial_score}));
        while (!t->is_final()) {
            int symbol = std::stoi(merger->get_dat()->get_symbol(t->get_symbol()));
            tr_vec.push_back(symbol);
            t = t->future();

            best.push_back(std::vector<std::tuple<apta_node*, apta_node*, int>>(1, { nullptr, nullptr, initial_score }));
        }
    };

    // Function declarations
    float nw_alignment();
    int calculate_matrix_value(apta_node* from, apta_node* to, int symbol_index, tail* t);
    std::pair<int, int> get_left_value(apta_node* from, apta_node* to, int symbol_index, int left, tail* t);
    std::pair<int, int> get_diagonal_value(apta_node* from, apta_node* to, int symbol_index, int diagonal, tail* t);
    std::pair<int, int> get_up_value(apta_node* from, apta_node* to, int symbol_index, int up, tail* t);
    void print_matrix_to_file(const std::string& filename);
    //void backtrace();

    // Optionally, provide getter functions to access matrix data if needed
    state_merger* get_merger() const { return merger; }
    trace* get_trace() const { return tr; }
    std::map<int, std::map<int, std::vector<std::tuple<apta_node*, apta_node*, int>>>>& get_matrix() { return matrix; }
    int get_matches() { return matches; };
    int get_mismatches() { return mismatches; };
    int get_skips() { return skips; };
    int get_jumps() { return jumps; };
    int get_trace_score() { return trace_score; };
    float get_normalized_trace_score(int score) { 
        trace_score = score;
        float max = tr->get_length() * MATCH;
        float min = tr->get_length() * MISMATCH_PENALTY;
        float normalized_trace_score = (trace_score == 0) ? 0 : (trace_score - min) / (max - min);
        return normalized_trace_score;
    };

    static constexpr int initial_score = std::numeric_limits<int>::min() / 2; // divide by 2 to avoid overflow
};


#endif //FLEXFRINGE_PREDICT_H
