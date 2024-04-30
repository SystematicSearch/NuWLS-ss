#ifndef _BASIS_PMS_H_
#define _BASIS_PMS_H_

#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <cmath>
#include <cstring>
#include <queue>
#include <map>
#include <stdio.h>
#include <stdlib.h>
#include <sys/times.h> //these two h files are for timing in linux
#include <unistd.h>

using namespace std;

/* ------------------------------------- added parameters by Systematic Search ------------------------------------- */
constexpr bool   use_runtime_unit_propagate    = true;
constexpr int    num_cand_in_propagate         = 5;
constexpr int    init_local_optima_thres       = 10;
constexpr int    local_optima_thres_multiplier = 500;
constexpr bool   use_propagate_size_limit      = true;
constexpr int    propagate_size_limit          = 20;
constexpr bool   use_final_attempt             = true;
constexpr int    final_attempt_looptime        = 15;
constexpr int    final_attempt_step            = 10000;
constexpr double double_tol                    = 1e-6;
/* ---------------------------------- end of added parameters by Systematic Search ---------------------------------- */


#define mypop(stack) stack[--stack##_fill_pointer]
#define mypush(item, stack) stack[stack##_fill_pointer++] = item

const float MY_RAND_MAX_FLOAT = 10000000.0;
const int MY_RAND_MAX_INT = 10000000;
const float BASIC_SCALE = 0.0000001; //1.0f/MY_RAND_MAX_FLOAT;

// Define a data structure for a literal.
struct lit
{
	int clause_num; //clause num, begin with 0
	int var_num;	//variable num, begin with 1
	bool sense;		//is 1 for true literals, 0 for false literals.
};

static struct tms start_time;
static double get_runtime()
{
	struct tms stop;
	times(&stop);
	return (double)(stop.tms_utime - start_time.tms_utime + stop.tms_stime - start_time.tms_stime) / sysconf(_SC_CLK_TCK);
}
static void start_timing()
{
	times(&start_time);
}

/* ----------------------------------------- auxiliary struct and functions ----------------------------------------- */
struct var_with_sense {
    var_with_sense() = default;
    var_with_sense(int u, int b) { id = u; sense = b; };
    int id   {0};
    int sense{0};
};

static int to_index(int v, bool sense) { return (v << 1) + sense; }

/* used to backtrack */
class FlipRecord {
public:
    FlipRecord() = default;
    explicit FlipRecord(int x) {
        capacity = x;
        index = new int[capacity];
        memset(index, -1, capacity * sizeof(int));
        queue = new int[capacity];
    }
    ~FlipRecord() {
        delete[] index;
        delete[] queue;
    }
    int capacity{0};
    int* index{};
    int* queue{};
    int size{0};
    int cnt{0};

    void init(int n) {
        capacity = n;
        if (index == nullptr) {
            index = new int[capacity];
        }
        memset(index, -1, capacity * sizeof(int));
        if (queue == nullptr) {
            queue = new int[capacity];
        }
        size = 0;
        cnt = 0;
    }

    inline void remove(int v) {
        int idx = index[v];
        int tail = queue[--size];
        queue[idx] = tail;
        index[tail] = idx;
        index[v] = -1;
    }

    inline void remove_tail() {
        int tail = queue[--size];
        index[tail] = -1;
    }

    inline void push(int v) {
        if (index[v] != -1) {
            remove(v);
            return;
        }
        index[v] = size;
        queue[size++] = v;
        cnt++;
    }

    inline void clear() {
        for (int i = 0; i < size; ++i) {
            index[queue[i]] = -1;
        }
        size = 0;
        cnt = 0;
    }

    inline int tail() {
        if (size > 0) {
            return queue[size - 1];
        } else
            exit(-1);
    }
};

template <typename ItemType, typename ScoreType, typename TimeStampType> class CandFilter
{
public:
    vector<ScoreType> scoreVec;
    vector<TimeStampType> timeStampVec;
    vector<ItemType> itemVec;
    bool full{false};
    int size{10};
    explicit CandFilter(int s) {
        size = s;
        scoreVec.reserve(size);
        timeStampVec.reserve(size);
        itemVec.reserve(size);
    }
    CandFilter() = default;
    void Insert(ItemType& item, ScoreType score, TimeStampType timeStamp) {
        for (auto& currItem: itemVec) {
            if (item == currItem) { return; }
        }

        if (!full) {
            itemVec.push_back(item);
            scoreVec.push_back(score);
            timeStampVec.push_back(timeStamp);
            if (itemVec.size() == size) { full = true; }
            return;
        }
        ItemType tmpItem = item;
        ScoreType tmpScore = score;
        TimeStampType tmpTimeStamp = timeStamp;
        for (size_t i = 0; i < size; ++i) {
            if (scoreVec[i] > tmpScore) { continue; }
            if (scoreVec[i] > tmpScore && tmpScore > scoreVec[i]) {
                if (timeStampVec[i] < tmpTimeStamp) { continue; }
                if (timeStampVec[i] == tmpTimeStamp && rand() % 2 == 1) { continue; }
            }
            tmpItem = itemVec[i];
            itemVec[i] = tmpItem;
            tmpScore = scoreVec[i];
            scoreVec[i] = tmpScore;
            tmpTimeStamp = timeStampVec[i];
            timeStampVec[i] = tmpTimeStamp;
        }
    }
    bool IsEmpty() {
        return itemVec.empty();
    }
};
/* ------------------------------------- end of auxiliary struct and functions ------------------------------------- */

class ISDist
{
  private:
    /* ----------------- members used by Systematic search ----------------- */
    // implication
    enum class imply_level { empty, clause, formula };
    vector<vector<var_with_sense>> propagate_table;
    vector<imply_level> flag;
    int local_optima_thres;
    FlipRecord propagate_record;
    
    // for statistics
    double num_local_optima{0};
    double num_backtrack{0};
    double propagate_succ_len{0};
    double propagate_fail_len{0};
    int final_attempt_success{0};
    int final_attempt_attempt{0};
    vector<long long> opt_soln_update_history;
    vector<double> opt_soln_update_time;
    /* -------------- end of members used by Systematic search -------------- */

    /***********non-algorithmic information ****************/
    int problem_weighted;

    //size of the instance
    int num_vars;    //var index from 1 to num_vars
    int num_clauses; //clause index from 0 to num_clauses-1
    int num_hclauses;
    int num_sclauses;

    //steps and time
    int tries;
    int max_tries;
    unsigned int max_flips;
    unsigned int max_non_improve_flip;
    unsigned int step;
    int final_attempt_state;

    int print_time;
    int cutoff_time;
    int prioup_time;
    double opt_time;

    /**********end non-algorithmic information*****************/
    /* literal arrays */
    lit **var_lit;         //var_lit[i][j] means the j'th literal of var i.
    int *var_lit_count;    //amount of literals of each var
    lit **clause_lit;      //clause_lit[i][j] means the j'th literal of clause i.
    int *clause_lit_count; // amount of literals in each clause

    /* Information about the variables. */
    double *score;
    long long *time_stamp;
    int **var_neighbor;
    int *var_neighbor_count;
    int *neighbor_flag;
    int *temp_neighbor;

    /* Information about the clauses */
    long long top_clause_weight;
    long long *org_clause_weight;
    long long total_soft_weight;
    long long max_soft_weight;
    long long min_soft_weight;
    double *clause_weight;
    double *tuned_org_clause_weight;
    double coe_tuned_weight;
    int *sat_count;
    int *sat_var;
    long long *clause_selected_count;
    int *best_soft_clause;
    long long total_soft_length;
    long long total_hard_length;

    //original unit clause stack
    lit *unit_clause;
    int unit_clause_count;

    //unsat clauses stack
    int *hardunsat_stack;           //store the unsat clause number
    int *index_in_hardunsat_stack;  //which position is a clause in the unsat_stack
    int hardunsat_stack_fill_pointer;

    int *softunsat_stack;           //store the unsat clause number
    int *index_in_softunsat_stack;  //which position is a clause in the unsat_stack
    int softunsat_stack_fill_pointer;

    //variables in unsat clauses
    int *unsatvar_stack;
    int unsatvar_stack_fill_pointer;
    int *index_in_unsatvar_stack;
    int *unsat_app_count; //a varible appears in how many unsat clauses

    //good decreasing variables (dscore>0 and confchange=1)
    int *goodvar_stack;
    int goodvar_stack_fill_pointer;
    int *already_in_goodvar_stack;

    /* Information about solution */
    int *cur_soln; //the current solution, with 1's for True variables, and 0's for False variables
    int *cur_soln_cpy;
    int *best_soln;
    int *local_opt_soln;
    //when find a feasible solution, this is marked as 1.

    long long local_opt;
    int local_soln_feasible;
    int hard_unsat_nb;
    long long soft_unsat_weight;
    long long opt_unsat_weight;

    //clause weighting
    int *large_weight_clauses;
    int large_weight_clauses_count;
    int large_clause_count_threshold;

    int *soft_large_weight_clauses;
    int *already_in_soft_large_weight_stack;
    int soft_large_weight_clauses_count;
    int soft_large_clause_count_threshold;

    //tem data structure used in algorithm
    int *best_array;
    int best_count;
    int *temp_lit;

    int local_optima_count{0};

    //parameters used in algorithm
    float rwprob;
    float rdprob;
    float smooth_probability;
    float soft_smooth_probability;
    int hd_count_threshold;
    double h_inc;
    double s_inc;
    double h_inc_1;
    double h_inc_2;
    double s_inc_1;
    double s_inc_2;
    double softclause_weight_threshold;
    float random_prob;
    int coe_soft_clause_weight;

    //function used in algorithm
    void build_neighbor_relation();
    void allocate_memory();
    
    void increase_weights();
    void hard_increase_weights();

    void soft_increase_weights();
    void soft_increase_weights_large();
    void soft_increase_weights_small();
    void smooth_weights();
    void hard_smooth_weights();
    void soft_smooth_weights();
    void update_clause_weights();
    void unsat(int clause);
    void sat(int clause);
    void init(vector<int> &init_solution);
    void param_settings();
    void flip(int flipvar);
    double get_curr_punish();
    void update_best_soln();
    void flip_up(int flipvar);
    void flip_up(int flipvar, map<int, long long>& former_time_stamp, FlipRecord& backtrack_record);
    void reset_time_stamp(map<int, long long>& former_time_stamp);
    void update_goodvarstack1(int flipvar);
    void update_goodvarstack2(int flipvar);
    int pick_var();
    int systematic_search();
    double backtrack_impl(int best_var, double last_punish); // return new_punish - old_punish
    vector<var_with_sense>& get_formula_level(int v, int sense);
    vector<var_with_sense>& get_clause_level(int v, int sense);
    vector<var_with_sense>& get_table(int v, int sense);

  public:
    ISDist();
    void settings();
    void build_instance(char *filename);
    void local_search_with_decimation(char *inputfile);
    void simple_print();
    void print_best_solution();
    void free_memory();
    bool verify_sol();
    bool parse_parameters2(int argc, char **argv);
    template<class T> void print_array(ofstream& ofs, vector<T>& vec, string name);
    int best_soln_feasible;
    string addr;
};

#endif
