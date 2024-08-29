//
// Created by sicco on 23/04/2021.
//

#include "predict.h"
#include "dfa_properties.h"
#include <queue>
#include <iostream>
#include <fstream>
#include "count_types.h"
#include <chrono>

struct tail_state_compare{ bool operator()(const pair<double, pair<apta_node*, tail*>> &a, const pair<double, pair<apta_node*, tail*>> &b) const{ return a.first < b.first; } };

int rownr = 1;
map<int,double> sw_score_per_symbol;
map<tail*,double> sw_individual_tail_score;

double compute_skip_penalty(apta_node* node){
    if(ALIGN_SKIP_PENALTY != 0) return 1.0 + ALIGN_SKIP_PENALTY;
    return 1.0;
}

double compute_jump_penalty(apta_node* old_node, apta_node* new_node){
    if(ALIGN_DISTANCE_PENALTY != 0) return 1.0 + (ALIGN_DISTANCE_PENALTY * (double)(merged_apta_distance(old_node, new_node, -1)));
    return 1.0;
}

double compute_score(apta_node* next_node, tail* next_tail){
    //if(PREDICT_ALIGN){ cerr << next_node->get_data()->align_score(next_tail) << endl; }
    if(PREDICT_ALIGN){ return next_node->get_data()->align_score(next_tail); }
    return next_node->get_data()->predict_score(next_tail);
}

double update_score(double old_score, apta_node* next_node, tail* next_tail){
    double score = compute_score(next_node, next_tail);
    if(PREDICT_MINIMUM) return min(old_score, score);
    return old_score + score;
}

list<int> state_sequence;
list<double> score_sequence;
list<bool> align_sequence;
list<string> nw_align_sequence;
int mismatches = 0;
float normalized_trace_score = 0;
double trace_score_sum = 0;
apta_node* ending_state = nullptr;
tail* ending_tail = nullptr;
int nonfinal = 0;
int nonexisting = 0;

void align(state_merger* m, tail* t, bool always_follow, double lower_bound) {
    apta_node *n = m->get_aut()->get_root();

    double score;

    priority_queue<pair<double, pair<apta_node*, tail *>>,
            vector<pair<double, pair<apta_node*, tail *>>>, tail_state_compare> Q;
    map<apta_node *, map<int, double> > V;
    map<apta_node *, apta_node*> T;

    state_set *states = m->get_all_states();

    Q.push(pair<double, pair<apta_node*, tail *>>(log(1.0),
                                                        pair<apta_node*, tail *>(n, t)));

    apta_node* next_node = nullptr;
    tail *next_tail = nullptr;

    while (!Q.empty()) {
        pair<double, pair<apta_node *, tail *>> next = Q.top();
        Q.pop();

        score = next.first;
        next_node = next.second.first;
        next_tail = next.second.second;

        //cerr << score << " " << Q.size() << endl;

        if (next_tail == nullptr) {
            break;
        }
        if (lower_bound != 1 && score < lower_bound){
            break;
        }

        int index = next_tail->get_index();
        //cerr << index << " " << next_node->get_number() << endl;

        if (V.find(next_node) != V.end() && V[next_node].rbegin()->first >= index) continue;
        V[next_node][index] = score;

        //cerr << index << " " << next_node->get_number() << endl;

        if (next_tail->is_final()) {
            // STOP RUN
            //cerr << "final: " << compute_score(score, next_node, next_tail) << endl;
            //cout << "final: " << score << "+" << compute_score(next_node, next_tail) << endl;
            Q.push(pair<double, pair<apta_node *, tail *>>(
                    update_score(score, next_node, next_tail),
                    pair<apta_node*, tail *>(next_node, 0)));
        } else {
            // FOLLOW TRANSITION
            apta_node *child = next_node->child(next_tail);
            if (child != nullptr) {
                child = child->find();
                //cerr << "follow: " << compute_score(score, next_node, next_tail) << endl;
                //cout << "follow " << child->get_number() << ": " << score << "+" << compute_score(next_node, next_tail) << endl;
                Q.push(pair<double, pair<apta_node *, tail *>>(
                        update_score(score, next_node, next_tail),
                        pair<apta_node *, tail *>(child, next_tail->future())));
            }

            if (always_follow && child != nullptr) continue;
                    
            // JUMP TO ALIGN -- calling align consistent
            for(auto jump_child : *states){
                if (jump_child == next_node) continue;
                if (jump_child->get_data()->align_consistent(next_tail)) {
                    //apta_node *next_child = jump_child->child(next_tail)->find();
                    //cerr << "jump: " << compute_score(score, next_node, next_tail) << endl;
                    //cout << "jump " << jump_child->get_number() << ": (" << score << "+" << compute_score(next_node, next_tail) << ")*" << compute_jump_penalty(next_node, jump_child) << endl;
                    Q.push(pair<double, pair<apta_node *, tail *>>(
                            update_score(score, next_node, next_tail) *
                                    compute_jump_penalty(next_node, jump_child),
                            pair<apta_node *, tail *>(jump_child, next_tail)));
                }
            }

            // SKIP TO ALIGN
            // UNCLEAR whether this is needed.
            //cerr << "skip: " << compute_score(score, next_node, next_tail) << endl;
            //cout << "skip " << next_node->get_number() << ": (" << score << "+" << compute_score(next_node, next_tail) << ")*" << compute_skip_penalty(next_node) << endl;
            Q.push(pair<double, pair<apta_node *, tail *>>(
                    update_score(score, next_node, next_tail) *
                        compute_skip_penalty(next_node),
                    pair<apta_node *, tail *>(next_node, next_tail->future())));
        }
    }

    // RUN NOT ENDED
    if(next_tail != nullptr || score == -INFINITY){
        return;
    }

    ending_state = next_node;

    double current_score = score;
    tail* current_tail = t;
    while(current_tail->future() != nullptr){ current_tail = current_tail->future(); }

    ending_tail = current_tail;
    if(ending_tail->is_final()) ending_tail = ending_tail->past();

    //state_sequence->push_front(next_node->number);
    //score_sequence->push_front(next_node->data->align_score(current_tail));
    //current_score -= log(next_node->data->predict_score(current_tail));
    //current_tail = current_tail->past();

    while(current_tail != nullptr){
        //cerr << "current score : " << current_score << endl;
        int index = current_tail->get_index();

        //cerr << index << endl;

        apta_node* prev_node = nullptr;
        double max_score = -1;
        bool advance = true;
        for(auto node : *states){
            if (V.find(node) != V.end()) {
                map<int, double> vm = V[node];
                if (vm.find(index) != vm.end()) {
                    double old_score = vm[index];
                    if (current_tail->is_final()){
                        double score = update_score(old_score, node, current_tail);
                        //cerr << "final " << old_score << " " << score << endl;
                        if (score == current_score) {
                            max_score = old_score;
                            prev_node = node;
                            advance = true;
                            break;
                        }
                    }
                    if (node->child(current_tail) != 0 && node->child(current_tail)->find() == next_node) {
                        double score = update_score(old_score, node, current_tail);
                        //cerr << "take transition " << old_score << " " << score << endl;
                        if (score == current_score) {
                            max_score = old_score;
                            prev_node = node;
                            advance = true;
                            break;
                        }
                    } else if (node == next_node) {
                        double score = update_score(old_score, node, current_tail) *
                                       compute_skip_penalty(node);
                        //cerr << "skip symbol " << old_score << " " << score << endl;
                        if (score == current_score) {
                            max_score = old_score;
                            prev_node = node;
                            advance = true;
                            break;
                        }
                    }
                }
                if (vm.find(index+1) != vm.end() && !current_tail->is_final()){
                    if (node->child(current_tail->future()) == nullptr
                    && next_node->get_data()->align_consistent(current_tail->future()))
                    {
                        double old_score = vm[index+1];
                        double score = update_score(old_score, node, current_tail->future())
                            * compute_jump_penalty(node, next_node);
                        //cerr << "jump " << old_score << " " << score << endl;
                        if (score == current_score) {
                            max_score = old_score;
                            prev_node = node;
                            advance = false;
                            break;
                        }
                    }
                }
            }
        }
        
        //cerr << prev_node << endl;

        if(prev_node != nullptr) {
            state_sequence.push_front(next_node->get_number());
            score_sequence.push_front(prev_node->get_data()->align_score(current_tail));
            align_sequence.push_front(advance);
            current_score = max_score;
            next_node = prev_node;
            if(advance) current_tail = current_tail->past();
            //cerr << current_score << endl;
        }
    }
}

double prob_single_parallel(tail* p, tail* t, apta_node* n, double prod_prob, bool flag){
    double result = -100000;
    if(n == nullptr) return result;
    if(t == p) t = t->future();
    n = n->find();

    if(t->is_final()){
        if(flag){
            if(FINAL_PROBABILITIES){
                return prod_prob + log(n->get_data()->predict_score(t));
            }
            return prod_prob;
        }
        double prob = n->get_data()->predict_score(p);
        return prob_single_parallel(p, t, n->child(p), prod_prob + log(prob), true);
    } else {
        double prob = n->get_data()->predict_score(t);
        result = prob_single_parallel(p, t->future(), n->child(t), prod_prob + log(prob), flag);
        if(result != -100000) return result;

        if (!flag) {
            double prob = n->get_data()->predict_score(p);
            return prob_single_parallel(p, t, n->child(p), prod_prob + log(prob), true);
        }
    }
    return -100000;
}

apta_node* single_step(apta_node* n, tail* t, apta* a){
    apta_node* child = n->child(t);
    if(child == 0){
        if(PREDICT_RESET) return a->get_root();
        else if(PREDICT_REMAIN) return n;
        else return nullptr;
    }
    return child->find();
}

double predict_trace(state_merger* m, trace* tr){
    apta_node* n = m->get_aut()->get_root();
    tail* t = tr->get_head();
    double score = 0.0;

    for(int j = 0; j < t->get_length(); j++){
        score = compute_score(n, t);
        n = single_step(n, t, m->get_aut());
        if(n == nullptr) break;

        t = t->future();
    }

    if(FINAL_PROBABILITIES && t->get_symbol() == -1){
        score = compute_score(n, t);
    }
    return score;
}

double add_visits(state_merger* m, trace* tr){
    apta_node* n = m->get_aut()->get_root();
    tail* t = tr->get_head();
    double score = 0.0;

    for(int j = 0; j < t->get_length(); j++){
        n = single_step(n, t, m->get_aut());
        if(n == nullptr) break;
        t = t->future();
    }
    return score;
}

void predict_trace_update_sequences(state_merger* m, tail* t){
    apta_node* n = m->get_aut()->get_root();
    double score = 0.0;

    for(int j = 0; j < t->get_length(); j++){
        score = compute_score(n, t);
        score_sequence.push_back(score);

        n = single_step(n, t, m->get_aut());
        if(n == nullptr){
            state_sequence.push_back(-1);
            align_sequence.push_back(false);
            break;
        }

        t = t->future();
        state_sequence.push_back(n->get_number());
        align_sequence.push_back(true);
    }

    if(FINAL_PROBABILITIES && t->get_symbol() == -1){
        score = compute_score(n, t);
        score_sequence.push_back(score);
        state_sequence.push_back(n->get_number());
        align_sequence.push_back(true);
    }

    ending_state = n;
    ending_tail = t;
    if(ending_tail->is_final()) ending_tail = ending_tail->past();
}

template <typename T>
void write_list(list<T>& list_to_write, ofstream& output){
    if(list_to_write.empty()){
        output << "[]";
        return;
    }

    output << "[";
    bool first = true;
    for(auto val : list_to_write) {
        if (!first) { output << ","; }
        else first = false;
        output << val;
    }
    output << "]";
}


void predict_trace(state_merger* m, ofstream& output, trace* tr){
    if(REVERSE_TRACES) tr->reverse();

    state_sequence.clear();
    score_sequence.clear();
    align_sequence.clear();
    nw_align_sequence.clear();
    ending_state = nullptr;
    ending_tail = nullptr;

    if(PREDICT_ALIGN) {
        align(m, tr->get_head(), true, 1.0);
    } else {
        predict_trace_update_sequences(m, tr->get_head());
    }

    if (PREDICT_ALIGN_NW) {
        sequence_alignment* seq_alignment = new sequence_alignment(m, tr);
        normalized_trace_score = seq_alignment->nw_alignment();
        seq_alignment->print_matrix_to_file("../matrix_output.txt");
        mismatches = seq_alignment->get_mismatches();
        cout << tr->to_string() << " " << "trace_score = " << seq_alignment->get_trace_score() << " normalized: " << normalized_trace_score << " matches: " << seq_alignment->get_matches() << ", mismatches : " << seq_alignment->get_mismatches() << endl;
    }   

    output << rownr << "; " << "\"" << tr->to_string() << "\"";

    output << "; ";
    write_list(state_sequence, output);
    output << "; ";
    write_list(score_sequence, output);

    if(SLIDING_WINDOW) {
        auto score_it = score_sequence.begin();
        auto state_it = state_sequence.begin();
        auto align_it = align_sequence.begin();
        tail *tail_it = tr->get_head();
        while (score_it != score_sequence.end() && tail_it != nullptr && !tail_it->is_final()) {
            sw_individual_tail_score[tail_it] = *score_it;

            int tail_nr = tail_it->get_nr();
            if (sw_score_per_symbol.find(tail_nr) == sw_score_per_symbol.end())
                sw_score_per_symbol[tail_nr] = *score_it;
            else sw_score_per_symbol[tail_nr] += *score_it;
            if (*align_it) { tail_it = tail_it->future(); }
            ++state_it;
            ++score_it;
            ++align_it;
        }

        list<double> score_tail_sequence;
        list<int> tail_nr_sequence;

        tail_it = tr->get_head();
        while(tail_it != nullptr && !tail_it->is_final()){
            int tail_nr = tail_it->get_nr();
            tail_nr_sequence.push_back(tail_nr);
            if (sw_score_per_symbol.find(tail_nr) != sw_score_per_symbol.end())
                score_tail_sequence.push_back(sw_score_per_symbol[tail_nr]);
            tail_it = tail_it->future();
        }

        output << "; ";
        write_list(score_tail_sequence, output);

        double front_tail_score = score_tail_sequence.front();
        if(!score_tail_sequence.empty()) output << "; " << front_tail_score;
        else output << "; " << 0;

        list<int> row_nrs_front_tail;
        tail* front_tail = tr->get_head();
        tail* root_cause = front_tail;
        while(front_tail != nullptr){
            row_nrs_front_tail.push_back(front_tail->get_sequence());
                if(front_tail_score > 0 && sw_individual_tail_score[front_tail] > 1.5 * sw_individual_tail_score[root_cause]){
                    root_cause = front_tail;
                }
                if(front_tail_score < 0 && sw_individual_tail_score[front_tail] < 1.5 * sw_individual_tail_score[root_cause]){
                    root_cause = front_tail;
                }
            front_tail = front_tail->split_from;
        }
        output << "; " << "\"" << root_cause->to_string() << "\"";
        output << "; ";
        write_list(row_nrs_front_tail, output);
    }


    if (PREDICT_ALIGN) {
        output << "; ";
        write_list(align_sequence, output);
        int nr_misaligned = 0;
        for (int b : align_sequence) { if (b != 1) nr_misaligned++; }
        output << "; " << nr_misaligned ;
    }

    if (PREDICT_ALIGN_NW) {
        output << "; ";
        write_list(nw_align_sequence, output);
        output << "; " << normalized_trace_score << "; " << mismatches;
        trace_score_sum += normalized_trace_score;
    }

    if(PREDICT_TRACE){
        if(score_sequence.empty()){
            output << "; 0; 0; 0;";
        } else {
            double sum = 0.0;
            for(auto val : score_sequence) sum += val;
            output << "; " << sum << "; " << (sum / (double)score_sequence.size());

            double min = 0.0;
            for(auto val : score_sequence) if(val < min) min = val;
            output << "; " << min;
        }
    }

    if(ending_state != nullptr){
        if(PREDICT_TYPE){
            output << "; " << inputdata::string_from_type(tr->get_type());
            output << "; " << ending_state->get_data()->predict_type_score(tr->get_head());

            int type_predict = ending_state->get_data()->predict_type(ending_tail);
            output << "; " << inputdata::string_from_type(type_predict);
            output << "; " << ending_state->get_data()->predict_type_score(type_predict);
        }

        if(PREDICT_SYMBOL) {
            if (ending_tail != nullptr) {
                output << "; " << inputdata::string_from_symbol(ending_tail->get_symbol());
                output << "; " << ending_state->get_data()->predict_symbol_score(ending_tail);
            } else output << "; 0; 0";

            int symbol_predict = ending_state->get_data()->predict_symbol(ending_tail);
            output << "; " << inputdata::string_from_symbol(symbol_predict);
            output << "; " << ending_state->get_data()->predict_symbol_score(symbol_predict);
        }

        if(PREDICT_DATA) {
            if (ending_tail != nullptr) {
                output << "; " << ending_tail->get_data();
                output << "; " << ending_state->get_data()->predict_data_score(ending_tail);
            } else output << "; 0; 0";

            string data_predict = ending_state->get_data()->predict_data(ending_tail);
            output << "; " << data_predict;
            output << "; " << ending_state->get_data()->predict_data_score(data_predict);
        }
    }
    else{
        if(PREDICT_TYPE){
            output << "; 0; 0; 0; 0";
        }
        if(PREDICT_SYMBOL){
            output << "; 0; 0; 0; 0";
        }
        if(PREDICT_DATA){
            output << "; 0; 0; 0; 0";
        }
    }
    output << endl;
}

void predict_csv(state_merger* m, istream& input, ofstream& output){
    inputdata* id = m->get_dat();
    rownr = -1;

    output << "row nr; abbadingo trace; state sequence; score sequence";
    if(SLIDING_WINDOW) output << "; score per sw tail; score first sw tail; root cause sw tail score; row nrs first sw tail";
    if(PREDICT_ALIGN) output << "; alignment; num misaligned";
    if(PREDICT_TRACE) output << "; sum scores; mean scores; min score";
    if(PREDICT_TYPE) output << "; trace type; type probability; predicted trace type; predicted type probability";
    if(PREDICT_SYMBOL) output << "; next trace symbol; next symbol probability; predicted symbol; predicted symbol probability";
    output << endl;

    while(!input.eof()) {
        rownr += 1;
        trace* tr = id->read_csv_row(input);
        if(tr == nullptr) continue;
        if(!tr->get_end()->is_final()){
            continue;
        }
        predict_trace(m, output, tr);
        tail* tail_it = tr->get_head();
        //cerr << "predicted " << tr->to_string() << " " << tail_it->get_nr() << " " << tail_it->tr->get_sequence() << endl;
        for(int i = 0; i < SLIDING_WINDOW_STRIDE; i++){
            tail* tail_to_delete = tail_it;
            while(tail_to_delete->split_from != nullptr) tail_to_delete = tail_to_delete->split_from;
            if(tail_to_delete->get_index() < SLIDING_WINDOW_SIZE - SLIDING_WINDOW_STRIDE) continue;
            add_visits(m, tail_to_delete->tr);
            //cerr << "deleting " << tail_to_delete->tr->to_string() << " " << tail_to_delete->get_nr() << " " << tail_to_delete->tr->get_sequence() << endl;
            tail_to_delete->tr->erase();
            tail_it = tail_it->future();
        }
    }
}

void predict(state_merger* m, istream& input, ofstream& output) {
    //output << "first row nr; last row nr; abbadingo trace; state sequence; score sequence";
    output << "first row nr; abbadingo trace; state sequence; score sequence";
    if (SLIDING_WINDOW) output << "; score per sw tail; score first sw tail; root cause sw tail score; row nrs first sw tail";
    if (PREDICT_ALIGN) output << "; alignment; num misaligned";
    if (PREDICT_ALIGN_NW) output << "; nw-alignment; norm-nw-score; nw-mismatches";
    if (PREDICT_TRACE) output << "; sum scores; mean scores; min score";
    if (PREDICT_TYPE) output << "; trace type; type probability; predicted trace type; predicted type probability";
    if (PREDICT_SYMBOL) output << "; next trace symbol; next symbol probability; predicted symbol; predicted symbol probability";
    output << endl;
    rownr = -1;
    inputdata* id = m->get_dat();
    cout << "#states " << m->get_final_apta_size() << endl;
    std::chrono::steady_clock::time_point begin = std::chrono::steady_clock::now();


    //std::ofstream outFile("../output.txt");
    //std::streambuf* coutbuf = std::cout.rdbuf(); // Save old buffer
    //std::cout.rdbuf(outFile.rdbuf()); // Redirect cout to outFile

    for (int i = 0; i < id->get_max_sequences(); ++i) {
        rownr += 1;
        trace* tr = mem_store::create_trace();
        id->read_abbadingo_sequence(input, tr);
        predict_trace(m, output, tr);
        add_visits(m, tr);
        tr->erase();
    }

    // Restore the original buffer
    //std::cout.rdbuf(coutbuf); // Reset to standard output again
    //// Close the file stream
    //outFile.close();
    cout << "#traces: " << id->get_max_sequences() << " avg: " << trace_score_sum / id->get_max_sequences() << " nonfinal: " << nonfinal << " nonexisting: " << nonexisting << endl;

    auto end = std::chrono::steady_clock::now();

    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - begin).count();

    // Convert microseconds to seconds
    auto total_seconds = duration / 1'000'000;

    // Extract hours, minutes, and seconds
    auto hours = total_seconds / 3600;
    auto minutes = (total_seconds % 3600) / 60;
    auto seconds = total_seconds % 60;

    // Extract milliseconds
    auto milliseconds = (duration / 1'000) % 1'000;

    std::cout << "Time difference = " << hours << " hours, "
        << minutes << " minutes, "
        << seconds << " seconds, "
        << milliseconds << " milliseconds" << std::endl;
}

/*Needleman-Wunsch*/
float sequence_alignment::nw_alignment() {
    //cout << "initialize_matrix: " << merger->get_final_apta_size() << " and " << tr->to_string() << endl;
    // all nodes in model
    state_set* ss = merger->get_all_states();
    //cout << "Check" << endl;
    //for (auto i : merger->get_dat()->get_original_alphabet()) {
    //    cout << i << endl;
    //}
    //cout << "End" << endl;
    tail* t = tr->get_head();

    int symbol_index = 1; // index 0 is saved for the edge of the matrix.

    apta_node* prev_from = 0;
    apta_node* prev_to = 0;
    int prev_score = 0;

    while (!t->is_final()) {
        int tail_symbol = t->get_symbol();
        int symbol = std::stoi(merger->get_dat()->get_symbol(tail_symbol));
        //bfs
        queue<apta_node*> q;
        q.push(get_merger()->get_aut()->get_root());
        int best_score = INT_MIN / 2; // to avoid overflow incase of calculations
        string aligned_states = "";

        while (!q.empty()) {
            apta_node* curr = q.front();
            q.pop();
            //cout << "CHECK: NODE: " << curr << " " << curr->get_number() << endl;
            for (auto guards_it = curr->guards_start(); guards_it != curr->guards_end(); ++guards_it) {
                // guard.first is the symbol
                pair<int, apta_guard*> guard = *guards_it;

                // Check if the symbol is not found in the model alphabet
                auto it = merger->get_dat()->get_model_alphabet();
                if (std::find(it.begin(), it.end(),
                    merger->get_dat()->get_symbol(tail_symbol)) == it.end()) {
                    nonexisting++;
                    return 0;
                }
                cout << "\ninitialize_matrix " << curr->find()->get_number() << "->" << guard.second->get_target()->get_number() << " x " << symbol_index << ": " << merger->get_dat()->get_symbol(guard.first) << endl;
                apta_node* target_node = guard.second->get_target();
                int score = calculate_matrix_value(curr, target_node, symbol_index, t);
                matrix[guard.second->get_target()->find()->get_number()][symbol_index].push_back({curr, target_node, score});
                
                // update alignment if current transition has a better score
                if (score > best_score) {
                    best[symbol_index] = { {curr, target_node, score} };
                    best_score = score;
                }
                else if (score == best_score) { // other possible transition
                    best[symbol_index].push_back({ curr, target_node, score });
                }
                q.push(target_node);
            }
        }
        int options = 0;
        bool mismatched = false;
        //for (auto i : best[symbol_index]) {
        //if (prev_to != 0) cout << symbol_index << " " << prev_to->get_number() << endl;
        apta_node* first = std::get<0>(best[symbol_index][0]);
        apta_node* second = std::get<1>(best[symbol_index][0]);
        int score = std::get<2>(best[symbol_index][0]);
        cout << symbol_index << " " << first->get_number() << "->" << second->get_number() << " gap: " << matrix_gaps[second->get_number()][symbol_index][first->get_number()] << " score: " << score << " expected_score: " << prev_score + GAP_DISTANCE_PENALTY << endl;;
            //<< prev_score + (GAP_DISTANCE_PENALTY*matrix_gaps[second->get_number()][symbol_index][first->get_number()] )<< endl;
        int expected_score = prev_score + GAP_DISTANCE_PENALTY;
        if (NW_SCORING == "linear") expected_score = prev_score + GAP_DISTANCE_PENALTY * matrix_gaps[second->get_number()][symbol_index][first->get_number()];
        else if (NW_SCORING == "dynamic") expected_score = prev_score + GAP_DISTANCE_PENALTY * merged_apta_distance(prev_to, first->find(), -1);
        //cout << merged_apta_distance(prev_to, second->find(), -1) << endl;
        if (prev_to == 0 && prev_from == 0 && score == expected_score) {
            // initial mismatch
            mismatches++;
            // skipped symbol in trace
            nw_align_sequence.push_back(to_string(second->get_number()) + "/-");

        }
        else if (prev_to != 0 && prev_from != 0 && prev_from == first->find() && prev_to == second->find() && score == expected_score) {
            mismatches++;
            // skipped symbol in trace
            nw_align_sequence.push_back(to_string(second->get_number()) + "/-");
        }
        else if (prev_to != 0 && prev_to != first->find()) {
            mismatches++;
            nw_align_sequence.push_back(to_string(second->get_number()) + "/+");
        }
        else {
            matches++;
            nw_align_sequence.push_back(to_string(second->get_number()));
        }
        prev_score = score;
        prev_from = first->find();
        prev_to = second->find();
        symbol_index++;
        t = t->future();
    }

    //    for (auto i : best[symbol_index]) {
    //        //if (prev_to != 0) cout << symbol_index << " " << prev_to->get_number() << endl;
    //        apta_node* first = std::get<0>(i);
    //        apta_node* second = std::get<1>(i);
    //        int score = std::get<2>(i);
    //        //cout << symbol_index << " " << first->get_number() << "->" << second->get_number() << " gap: " << matrix_gaps[second->get_number()][symbol_index][first->get_number()] << " score: " << score << " expected_score: " << prev_score + (GAP_DISTANCE_PENALTY*matrix_gaps[second->get_number()][symbol_index][first->get_number()] )<< endl;
    //        int expected_score = prev_score + GAP_DISTANCE_PENALTY;
    //        if (NW_SCORING == "linear") expected_score = prev_score + GAP_DISTANCE_PENALTY * matrix_gaps[second->get_number()][symbol_index][first->get_number()];
    //        else if (NW_SCORING == "dynamic") expected_score = prev_score + GAP_DISTANCE_PENALTY * merged_apta_distance(prev_to, first->find(), -1);
    //        //cout << merged_apta_distance(prev_to, second->find(), -1) << endl;
    //        if (prev_to != 0 && prev_from != 0 && prev_from == first->find() && prev_to == second->find() && score == expected_score) {
    //            mismatched = true;      
    //            // skipped symbol in trace
    //            aligned_states.append(to_string(second->get_number()) + "/-");
    //        } else if (prev_to != 0 && prev_to != first->find()) {
    //            mismatched = true;
    //            aligned_states.append(to_string(second->get_number()) + "/+");
    //        }
    //        else {
    //            matches++;
    //            aligned_states.append(to_string(second->get_number()));
    //        }
    //        prev_score = score;
    //        prev_from = first->find();
    //        prev_to = second->find();
    //        //cout << prev_to->get_number() << endl;
    //        if (options > 0) aligned_states.append("|");
    //        options++;
    //    }
    //    if (mismatched) mismatches++;
    //    symbol_index++;
    //    t = t->future();
    //    nw_align_sequence.push_back(aligned_states);
    //}
    // ensure trace ends in a final state
    count_data* countDataPtr = dynamic_cast<count_data*>(prev_to->get_data());
    //cout << "prev_to " << prev_to->get_number()<< " final: " << countDataPtr->num_final() << endl;
    if (countDataPtr && countDataPtr->num_final() > 0) return get_normalized_trace_score(prev_score);
    nonfinal++;
    return 0;
    //return (countDataPtr && countDataPtr->num_final() > 0) ? get_normalized_trace_score(prev_score) : 0;
}

/**
* Fills alignment matrix for given transition.
*
* @from node from which the transition goes
* @to node to which the transition goes.
* @symbol_index current index in tail
* @matrix alignment matrix
*/
int sequence_alignment::calculate_matrix_value(apta_node* from, apta_node* to, int symbol_index, tail* t) {
    //cout << "calculate_matrix_value for " << from->get_number() << "->" << to->get_number() << " at: " << symbol_index << endl;
    apta_node* to_rep = to->find();
    apta_node* from_rep = from->find();
    // check if at starting point of matrix 
    if (to_rep->get_depth() == 0 && symbol_index == 0) {
        matrix_gaps[to_rep->get_number()][symbol_index][from_rep->get_number()]=0;
        return 0;
    }
    // check if at initial row  
    else if (symbol_index == 0) {
        int level = to_rep->get_depth();
        matrix_gaps[to_rep->get_number()][symbol_index][from_rep->get_number()]=0;
        return level * GAP_DISTANCE_PENALTY;
    }
    // check if at initial column 
    else if (to_rep->get_depth() == 0) {
        //matrix_gaps[to_rep->get_number()][symbol_index][from_rep->get_number()]=0;
        return symbol_index * GAP_DISTANCE_PENALTY;
    }
    // if there has been no transition into from node, most at an edge -> depth==0
    if (auto to_map = matrix.find(from->get_number()); to_map == matrix.end() && from_rep->get_depth() == 0) {
        // set diagonal value
        matrix[from_rep->get_number()][symbol_index - 1].push_back({ from, from, calculate_matrix_value(from, from, symbol_index - 1, t) });
        // set up value
        matrix[from_rep->get_number()][symbol_index].push_back({ from, from, calculate_matrix_value(from, from, symbol_index, t) });
    }
      // if there has been no transition into from node, most likely jumped to from node. 
    //if (auto to_map = matrix.find(from->get_number()); to_map == matrix.end()) {
    //    if (from_rep->get_depth() == 0) {
    //        matrix[from_rep->get_number()][symbol_index - 1].push_back({ from, from, calculate_matrix_value(from, from, symbol_index - 1, t) });
    //        matrix[from_rep->get_number()][symbol_index].push_back({ from, from, calculate_matrix_value(from, from, symbol_index, t) });
    //    }
    pair<int, int> left = (symbol_index - 1) == 0 ? std::make_pair(to_rep->get_depth() * GAP_DISTANCE_PENALTY, 0) : get_left_value(from, to, symbol_index, initial_score, t);
    pair<int, int> diagonal = get_diagonal_value(from, to, symbol_index, initial_score, t);
    pair<int, int> up = get_up_value(from, to, symbol_index, initial_score, t);

    int res = std::max({ left.first, up.first, diagonal.first });
    //if (res == diagonal.first) matrix_gaps[to_rep->get_number()][symbol_index][from_rep->get_number()] = diagonal.second;
    //else if (res == left.first) matrix_gaps[to_rep->get_number()][symbol_index][from_rep->get_number()] = left.second;
    //else matrix_gaps[to_rep->get_number()][symbol_index][from_rep->get_number()] = up.second;
    matrix_gaps[to_rep->get_number()][symbol_index][from_rep->get_number()] = (res == diagonal.first) ? diagonal.second : (res == left.first) ? left.second : up.second;

    //cout << "calculateMatrix: curr symbol_index " << symbol_index << ", transition: " << from_rep->get_number() << "->" << to_rep->get_number() << ": max{left: "
    //    << left.first << "/"<< left.second << ", up: " << up.first << "/" << up.second << ", diagonal: " << diagonal.first << "/" << diagonal.second << "}=" << from_rep->get_number() << "->" << to_rep->get_number() << ": "
    //    << std::max({ left.first, up.first, diagonal.first }) << endl;

    return res;
}


/**
* Gets the value that should be left from->to transition in the matrix.
*
* @from node from which the transition goes
* @to node to which the transition goes.
* @symbol_index current index in tail
* @matrix alignment matrix
* @GAP_DISTANCE_PENALTY gap distance penalty
* @left left score upper value
*/
pair<int, int> sequence_alignment::get_left_value(apta_node* from, apta_node* to, int symbol_index, int left, tail* t) {
    //std::cout << "LEFT, looking for " << from->get_number() << "->" << to->get_number() << " at: " << symbol_index - 1 << std::endl;
    apta_node* to_rep = to->find();
    apta_node* from_rep = from->find();
    int gaps = 0;

    // find transition into current destination node  
    if (auto to_map = matrix.find(to_rep->get_number()); to_map != matrix.end()) {
        // check if transition into current destination node at previous index exists 
        if (auto index_transitions = to_map->second.find(symbol_index - 1); index_transitions == to_map->second.end()) {
            //cout << "LEFT value found to: " << to->get_number() << ", no value found at symbol_index: " << symbol_index - 1 << endl;
            // calculate score if it did not exist 
            matrix[to_rep->get_number()][symbol_index - 1].push_back({ from, to, calculate_matrix_value(from, to, symbol_index - 1, t) });
            to_map = matrix.find(to_rep->get_number());
        }
        // for all transitions into current destination node at previous index 
        for (auto i : to_map->second.find(symbol_index - 1)->second) {
            apta_node* first = std::get<0>(i);
            apta_node* second = std::get<1>(i);
            //cout << first->get_number() << "->" << second->get_number() << endl;
            // store transition with highest score 
            if (first->find() == from_rep && second->find() == to_rep) {
                gaps = matrix_gaps[to_rep->get_number()][symbol_index - 1][from_rep->get_number()]+1;
                //left = std::max(left, std::get<2>(i) + GAP_DISTANCE_PENALTY);
                //*gaps);
                // 
                if (NW_SCORING == "static") left = std::max(left, std::get<2>(i) + GAP_DISTANCE_PENALTY);
                else if (NW_SCORING == "linear") left = std::max(left, std::get<2>(i) + GAP_DISTANCE_PENALTY*gaps);
                else if (NW_SCORING == "dynamic") {
                    left = std::max(left, std::get<2>(i) + GAP_DISTANCE_PENALTY * merged_apta_distance(std::get<1>(best[symbol_index - 1][0]), to_rep, -1));
                    int temp = GAP_DISTANCE_PENALTY * merged_apta_distance(std::get<1>(best[symbol_index - 1][0]), to_rep, -1);
                    //cout << "left: " << std::get<1>(best[symbol_index - 1][0])->get_number() << ":::" << to_rep->get_number() << " " << GAP_DISTANCE_PENALTY << " * " << merged_apta_distance(std::get<1>(best[symbol_index - 1][0]), to_rep, -1) << "= " << temp << endl;
                }
            }
            else {
                //cout << "LEFT found " << first->get_number() << "->" << second->get_number() << " instead of " << from_rep->get_number() << "->" << to_rep->get_number() << endl;
            }
        }
    }
    else {
        cerr << "LEFT, NO VALUE FOUND IN MATRIX, SOURCE: " << to_rep->get_number() << " AT INDEX: " << symbol_index - 1 << endl;
    }
    return std::make_pair(left,gaps);
}

/**
* Gets the value that should be diagonal from from->to transition in the matrix.
*
* @from node from which the transition goes
* @to node to which the transition goes.
* @symbol_index current index in tail
* @matrix alignment matrix
* @matchScore match score penalty
* @diagonal max score diagonal value
*/
pair<int, int> sequence_alignment::get_diagonal_value(apta_node* from, apta_node* to, int symbol_index, int diagonal, tail* t) {
    apta_node* to_rep = to->find();
    apta_node* from_rep = from->find();
    bool match = false;
    int gaps = 0;
    //cout << "DIAGONAL, looking for " << "->" << from->get_number() << " at: " << symbol_index - 1 << std::endl;

    // find transition into current source node  
    if (auto to_map = matrix.find(from_rep->get_number()); to_map != matrix.end()) {
        //check if transition into current source node at previous index exists 
        //if (auto index_transitions = to_map->second.find(symbol_index - 1); index_transitions == to_map->second.end() || to_map->second.find(symbol_index - 1)->second.size() == 0) {
        if (auto index_transitions = to_map->second.find(symbol_index - 1);
            index_transitions == to_map->second.end() || index_transitions->second.size() == 0) {
            //cout << "DIAGONAL value found to: " << from_rep->get_number() << ", no value found at symbol_index: " << symbol_index - 1 << ", size: " << matrix[from->get_number()][symbol_index - 1].size() << std::endl;
            // calculate score if it did not exist, 
            // if it did not exist, the symbol_index we are looking for is 0, so set the edge value by calculating the matrix value again.
            return std::pair(from_rep->get_depth() * GAP_DISTANCE_PENALTY + MISMATCH_PENALTY, 1); // TODO: unsure mismatch penalty
        }

        // get all transitions into current source node at previous index 
        for (auto i : to_map->second.find(symbol_index - 1)->second) {
            apta_node* first = std::get<0>(i);
            apta_node* second = std::get<1>(i);
            // check if destination node of transitions go into current source node and depth is current depth - 1 
            if (second->find() == from_rep) {
                //cout << first->find()->get_number() << "->" << second->find()->get_number() << endl;
                int score = std::get<2>(i);
                apta_node* child = second->find()->child(t);
                match = (child && child->get_number() == to_rep->get_number()) ? 1 : 0;
                //score += (match) ? MATCH : MISMATCH_PENALTY;
                if (match) {
                    //cout << first->find()->get_number() << "->" << second->find()->get_number() << " match" << endl;
                    score += MATCH;
                }
                else {
                    //cout << first->find()->get_number() << "->" << second->find()->get_number() <<  " mismatch" << endl;
                    gaps = matrix_gaps[from_rep->get_number()][symbol_index - 1][first->find()->get_number()] + 1;
                    if (NW_SCORING == "static") score += MISMATCH_PENALTY;
                    else if (NW_SCORING == "linear") score += MISMATCH_PENALTY * gaps;
                    else if (NW_SCORING == "dynamic") {
                        score += MISMATCH_PENALTY * merged_apta_distance(std::get<1>(best[symbol_index - 1][0]), to_rep, -1);
                        //cout << "diagonal: " << std::get<1>(best[symbol_index - 1][0])->get_number() << ":::" << to_rep->get_number() << " " << MISMATCH_PENALTY << " * " << merged_apta_distance(std::get<1>(best[symbol_index - 1][0]), to_rep, -1) << "= " << score << endl;
                    }
                }
                diagonal = std::max(diagonal, score);
            }
            else {
                //cout << "DIAGONAL found " << first->get_number() << "->" << second->get_number() << " instead of ->" << from_rep->get_number() << endl;
            }
        }
    }
    else {
        cerr << "DIAGONAL, NO VALUE FOUND IN MATRIX, SOURCE: " << from->get_number() << " AT INDEX: " << symbol_index - 1 << endl;
    }
    return std::pair(diagonal, gaps);
}

/**
* Gets the value that should be above from->to transition in the matrix.
*
* @from node from which the transition goes
* @to node to which the transition goes.
* @symbol_index current index in tail
* @matrix alignment matrix
* @GAP_DISTANCE_PENALTY gap distance penalty
* @up max score upper value
*/
pair<int,int> sequence_alignment::get_up_value(apta_node* from, apta_node* to, int symbol_index, int up, tail* t) {
    //cout << "UP, looking for ->" << from->get_number() << " at: " << symbol_index << std::endl;
    apta_node* to_rep = to->find();
    apta_node* from_rep = from->find();
    int gaps = 0;

    // find transition into current source node  
    if (auto to_map = matrix.find(from_rep->get_number()); to_map != matrix.end()) {
        //check if transition into current source node at previous index exists 
        if (auto index_transitions = to_map->second.find(symbol_index); index_transitions == to_map->second.end()) {
            //cout << "UP no transition at index: " << symbol_index << ", size: " << matrix[from->get_number()][symbol_index - 1].size() << endl;
            // use transitions into current destination at previous index to calculate score at current index 
            // IDEA: use the score from the PREVIOUS transition into current source node to compute score of current transition. 
            // TODO: CHECK DEPTH 
            //for (auto i : matrix[from_rep->get_number()][symbol_index - 1]) {
            //    //cout << "prev value at " << symbol_index - 1 << ": " << first->get_number() << "->" << second->get_number() << ": " << score << endl;
            //    matrix[from_rep->get_number()][symbol_index].push_back({ std::get<0>(i), std::get<1>(i), calculate_matrix_value(std::get<0>(i), std::get<1>(i), symbol_index, t) });
            //}
            matrix[from_rep->get_number()][symbol_index].push_back({ from, to, calculate_matrix_value(from, to, symbol_index, t) });
            to_map = matrix.find(from_rep->get_number());
        }
        // for all transitions into current source node 
        for (auto i : to_map->second.find(symbol_index)->second) {
            apta_node* first = std::get<0>(i);
            apta_node* second = std::get<1>(i);
            // check if destination of transitions are the same and level of edge is the current edge level - 1 
            //TODO: FIX DEPTH 
            //if (second == from && (second->get_depth() == (to->get_depth() - 1))) { 
            if (second->find() == from_rep) {
                //cout << first->get_number() << "->" << second->get_number() << ": " << up << endl;
                gaps = matrix_gaps[from_rep->get_number()][symbol_index][first->find()->get_number()] + 1;
                //up = std::max(up, std::get<2>(i) + GAP_DISTANCE_PENALTY);
                //* gaps);
                if (NW_SCORING == "static") up = std::max(up, std::get<2>(i) + GAP_DISTANCE_PENALTY);
                else if (NW_SCORING == "linear") up = std::max(up, std::get<2>(i) + GAP_DISTANCE_PENALTY*gaps);
                else if (NW_SCORING == "dynamic") {
                    up = std::max(up, std::get<2>(i) + GAP_DISTANCE_PENALTY * merged_apta_distance(std::get<1>(best[symbol_index - 1][0]), to_rep, -1));
                    //cout << "up: " << std::get<1>(best[symbol_index - 1][0])->get_number() << ":::" << to_rep->get_number() << " " << GAP_DISTANCE_PENALTY << " * " << merged_apta_distance(std::get<1>(best[symbol_index - 1][0]), to_rep, -1) << "= " << up << endl;
                }
            }
           /* else if (second == from_rep) {
                cout << "UP: transition " << first->get_number() << "->" << second->get_number() << " found, level of transition: " << second->get_depth() << " curr level: " << (to_rep->get_depth() - 1) << endl;
            }
            else {
                cout << "UP: transition found " << first->get_number() << "->" << second->get_number() << " instead of ->" << from_rep->get_number() << endl;
            }*/
        }
    }
    else {
        cerr << "UP, NO VALUE FOUND IN MATRIX, SOURCE: " << from_rep->get_number() << " AT INDEX:" << symbol_index << endl;
    }
    return std::make_pair(up, gaps);
}

void sequence_alignment::print_matrix_to_file(const string& filename) {
    ofstream outputFile(filename); // Create an output file stream
    // Check if the file is opened successfully
    if (!outputFile.is_open()) {
        cerr << "Error: Unable to open file: " << filename << endl;
        return;
    }
    // print alignment score matrix
    int index = get_trace()->get_length() + 1;
    outputFile << matrix.size() << "x" << index << endl;
    int maxWidth = 0; // Initialize vector to store maximum widths 
    for (const auto& row : matrix) {
        for (const auto& col : row.second) {
            if (col.first > index) index = col.first;
            for (const auto& tuple : col.second) {
                // Construct the string from tuple elements 
                std::stringstream ss;
                ss << "(" << std::get<0>(tuple)->get_number() << ", "
                    << std::get<1>(tuple)->get_number() << ": "
                    << std::get<2>(tuple) << ")";

                string result = ss.str(); // Convert stringstream to string 

                if (result.length() > maxWidth) maxWidth = result.length() * 2.5;
            }
        }
    }
    outputFile << "\t";
    for (int num = 0; num <= index; ++num) {
        if (num < index) outputFile << std::setw(maxWidth) << std::left << tr_vec[num] << num << ": ";
    }
    outputFile << endl;
    for (const auto& row : matrix) {
        outputFile << row.first << "\t";
        for (const auto& col : row.second) {
            for (const auto& tuple : col.second) {
                // Construct the string from tuple elements 
                std::stringstream ss;
                ss << col.first << "," << std::get<1>(tuple)->get_depth() << ": (" << std::get<0>(tuple)->get_number() << ", "
                    << std::get<1>(tuple)->get_number() << ": "
                    << std::get<2>(tuple) << ")";

                string result = ss.str(); // Convert stringstream to string 

                outputFile << std::setw(maxWidth) << std::left << result;
            }
        }
        outputFile << endl;
    }
    // print gap matrix
    for (int num = 0; num <= index; ++num) {
        if (num < index) outputFile << std::setw(maxWidth) << std::left << tr_vec[num] << num << ": ";
    }
    outputFile << endl;
    for (const auto& row : matrix_gaps) {
        outputFile << row.first << "\t";
        for (const auto& col : row.second) {
            for (const auto& to : col.second) {
                // Construct the string from tuple elements 
                std::stringstream ss;
                ss << col.first /*<< "," << std::get<1>(tuple)->get_depth()*/ << ": (" << to.first << ", "
                    << row.first << ": "
                    << to.second << ")";
                string result = ss.str(); // Convert stringstream to string 
                outputFile << std::setw(maxWidth) << std::left << result;
            }
        }
        outputFile << endl;
    }
     //Close the output file stream
    outputFile.close();
}