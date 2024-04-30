#ifndef PROPAGATE_H
#define PROPAGATE_H
#include "basis_pms.h"
#include "deci.h"

vector<var_with_sense>& ISDist::get_clause_level(int v, int sense) {
    auto posIndex = to_index(v, sense);
    if (flag[posIndex] == imply_level::clause || flag[posIndex] == imply_level::formula) {
        return propagate_table[posIndex];
    }
    propagate_table[posIndex].reserve(num_vars);
    // record what is in table
    vector<int> visited(num_vars + 1, -1);

    for (int i = 0; i < var_lit_count[v]; ++i) {
        auto &l = var_lit[v][i];
        if (l.sense == sense) { continue; }
        // only consider like -x1 + x2 >= 1
        auto c = l.clause_num;
        if (org_clause_weight[c] != top_clause_weight) { continue; }
        if (clause_lit_count[c] == 1) {
            // means v == 1-sense
            propagate_table[posIndex].clear();
            propagate_table[posIndex].emplace_back(l.var_num, l.sense);
            flag[posIndex] = imply_level::formula;
            propagate_table[posIndex].shrink_to_fit();
            return propagate_table[posIndex];
        } else if (clause_lit_count[c] == 2) {
            for (int j = 0; j < clause_lit_count[c]; ++j) {
                auto &l2 = clause_lit[c][j];
                if (l2.var_num == l.var_num) { continue; }
                if (visited[l2.var_num] == -1) {
                    propagate_table[posIndex].emplace_back(l2.var_num, l2.sense);
                    visited[l2.var_num] = l2.sense;
                } else if (visited[l2.var_num] == l2.sense) {
                    continue;
                } else {
                    // -l -> l
                    propagate_table[posIndex].clear();
                    propagate_table[posIndex].emplace_back(l.var_num, l.sense);
                    flag[posIndex] = imply_level::formula;
                    propagate_table[posIndex].shrink_to_fit();
                    return propagate_table[posIndex];
                }
            }
        }
    }

    propagate_table[posIndex].shrink_to_fit();
    flag[posIndex] = imply_level::clause;

    return propagate_table[posIndex];
}

vector<var_with_sense> &ISDist::get_formula_level(int v, int sense) {
    //double get_start_time = get_runtime();
    auto index = to_index(v, sense);
    if (flag[index] == imply_level::formula) { return propagate_table[index]; }
    int malloc_var_size = num_vars + 1;
    vector<var_with_sense> dfs;
    dfs.reserve(malloc_var_size);
    vector<int> visited(malloc_var_size, -1);

    auto& UPvector = get_clause_level(v, sense);
    // UPvector -> sense and visited
    for (auto& vws: UPvector) {
        // check if newSense conflict with previous sense
        auto newSense = vws.sense;
        if (visited[vws.id] != -1) {
            if (visited[vws.id] != newSense) {
                UPvector.clear();
                UPvector.emplace_back(v, 1-sense);
                UPvector.shrink_to_fit();
                flag[index] = imply_level::formula;
                //time += get_runtime() - get_start_time;
                return UPvector;
            } else { continue; }
        } else {
            dfs.push_back(vws);
            visited[vws.id] = newSense;
        }
    }
    while (!dfs.empty()) {
        auto searchVWS = dfs.back();
        dfs.pop_back();

        auto& searchUP = get_clause_level(searchVWS.id, searchVWS.sense);

        // visit children of searchVWS
        for (auto& childVWS: searchUP) {
            auto newSense = childVWS.sense;
            if (visited[childVWS.id] != -1) {
                if (visited[childVWS.id] != newSense) {
                    UPvector.emplace_back(v, 1-sense);
                    UPvector.shrink_to_fit();
                    flag[index] = imply_level::formula;
                    //time += get_runtime() - get_start_time;
                    return UPvector;
                } else {
                    continue;
                }
            } else {
                dfs.push_back(childVWS);
                visited[childVWS.id] = newSense;
            }
        }
    }

    // fill in unit propagation vector
    UPvector.clear();
    UPvector.reserve(num_vars);
    for (int vid = 1; vid <= num_vars; ++vid) {
        if (vid == v) { continue; }
        if (visited[vid] == -1) { continue; }
        UPvector.emplace_back(vid, visited[vid]);
    }
    UPvector.shrink_to_fit();
    flag[index] = imply_level::formula;
    //time += get_runtime() - get_start_time;
    return UPvector;
}

vector<var_with_sense>& ISDist::get_table(int v, int sense) {
    if (num_vars > 100000) {
        return get_clause_level(v, sense);
    } else {
        return get_formula_level(v, sense);
    }
}


#endif //PROPAGATE_H
