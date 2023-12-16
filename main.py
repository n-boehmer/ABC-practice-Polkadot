from code.util.read import *
from code.util.MES import *
from code.util.seqPhragmen import *
from code.util.phragmms import *
from os import listdir
from os.path import isfile, join
import numpy as np
import time
try:
    from abcvoting.preferences import Profile
    from abcvoting.preferences import Voter
    from abcvoting import abcrules
    from abcvoting.misc import *
    from abcvoting.output import output, DETAILS
    from abcvoting import abcrules_gurobi, abcrules_ortools, abcrules_mip, misc, scores
    from abcvoting.misc import str_committees_with_header, header, str_set_of_candidates
    from abcvoting.misc import sorted_committees, CandidateSet
    from abcvoting import properties
except ModuleNotFoundError:
    # Error handling
    pass

import os
import multiprocessing
import functools
import matplotlib.pyplot as plt
from textwrap import wrap
import gurobipy as gp
from gurobipy import GRB
import tikzplotlib
from fractions import Fraction
import collections
from collections import Counter
import pandas as pd

try:
    import dataframe_image as dfi
except:
    pass
from math import log10, floor
import sys
import time


def separable_rule_algorithm(rule_id, profile, committeesize, resolute):
    """
    Algorithm for separable rules (such as AV and SAV).
    """
    score = [0] * profile.num_cand
    for voter in profile:
        for cand in voter.approved:
            if rule_id == "sav":
                # Satisfaction Approval Voting
                score[cand] += voter.weight / len(voter.approved)
            elif rule_id == "av":
                # (Classic) Approval Voting
                score[cand] += voter.weight
            else:
                raise UnknownRuleIDError(rule_id)

    # smallest score to be in the committee
    cutoff = sorted(score)[-committeesize]
    certain_cands = [cand for cand in profile.candidates if score[cand] > cutoff]
    possible_cands = [cand for cand in profile.candidates if score[cand] == cutoff]
    missing = committeesize - len(certain_cands)
    if len(possible_cands) == missing:
        # candidates with score[cand] == cutoff
        # are also certain candidates because all these candidates
        # are required to fill the committee
        certain_cands = sorted(certain_cands + possible_cands)
        possible_cands = []
        missing = 0

    if resolute:
        committees = sorted_committees([(certain_cands + possible_cands[:missing])])
    return committees[0], sorted(score)


def marginal_thiele_scores_add(marginal_scorefct, profile, committee, papp=False):
    """
    Return marginal score increases from adding one candidate to the committee.

    The function returns a list of length `num_cand` where the i-th entry contains the
    marginal score increase when adding candidate i.
    Candidates that are already in the committee receive a small value (-1).

    Parameters
    ----------
        marginal_scorefct : func
            The marginal score function to be used.

        profile : abcvoting.preferences.Profile
            A profile.

        committee : iterable of int
            A committee.

    Returns
    -------
        list
            Marginal score increases from adding candidates to the committee.
    """
    if papp:
        marginal = [0] * profile.num_cand
        counter_committee = Counter(committee)
        for voter in profile:
            intersectionsize = sum([counter_committee[c] for c in voter.approved if c in counter_committee])
            for cand in voter.approved:
                marginal[cand] += voter.weight * marginal_scorefct(intersectionsize + 1)
    else:
        marginal = [0] * profile.num_cand
        for voter in profile:
            intersectionsize = len(voter.approved.intersection(committee))
            for cand in voter.approved:
                marginal[cand] += voter.weight * marginal_scorefct(intersectionsize + 1)
        for cand in committee:
            marginal[cand] = -1
    return marginal


def seq_thiele(scorefct_id, profile, committeesize, papp=False):
    """Compute one winning committee (=resolute) for sequential Thiele methods.

    Tiebreaking between candidates in favor of candidate with smaller
    number/index (candidates with larger numbers get deleted first).
    """
    committee = []
    marginal_scorefct = scores.get_marginal_scorefct(scorefct_id, committeesize)
    detailed_info = []

    # build a committee starting with the empty set
    for _ in range(committeesize):
        additional_score_cand = marginal_thiele_scores_add(
            marginal_scorefct, profile, committee, papp
        )
        tied_cands = [
            cand
            for cand in range(len(additional_score_cand))
            if additional_score_cand[cand] == max(additional_score_cand)
        ]
        next_cand = tied_cands[0]  # tiebreaking in favor of candidate with smallest index
        committee.append(next_cand)
        detailed_info.append(max(additional_score_cand))

    return committee, detailed_info


def greedy_justified_candidate_rule(weights, votes, k, m):
    total = sum(weights)
    committee = set()
    voter_satisfaction = [0] * len(votes)

    supporter_sets = [[] for _ in range(m)]
    for i, v in enumerate(votes):
        for c in v:
            supporter_sets[c].append(i)

    l = k
    while l >= 1:
        candidate_support = [0] * m
        for i in range(len(votes)):
            if voter_satisfaction[i] < l:
                for c in votes[i]:
                    if c not in committee:
                        candidate_support[c] += weights[i]
        violations = [c for c in range(m) if candidate_support[c] > (l * total) / k]
        while len(violations) > 0:
            committee.add(violations[0])
            candidate_support[violations[0]] = 0
            for i in supporter_sets[violations[0]]:
                voter_satisfaction[i] += 1
                if voter_satisfaction[i] == l:
                    for c in votes[i]:
                        candidate_support[c] -= weights[i]
            violations = [c for c in range(m) if candidate_support[c] > (l * total) / k]
        l = l - 1

    free = k - len(committee)
    print(free)
    ####SECOND PHASE
    candidate_support = [0] * m
    for i in range(len(votes)):
        for c in votes[i]:
            if c not in committee:
                candidate_support[c] += weights[i]
    indices = list(np.argsort(candidate_support))
    indices.reverse()
    second_part = indices[:free]
    for c in second_part:
        committee.add(c)
    return committee, None


def maximin_support(weights, s_votes, committee):
    total = sum(weights)
    votes = []
    k = len(committee)
    new_comittee = []

    for c in committee:
        id = c * (k + 1)
        while id in new_comittee:
            id += 1
        if id > (c + 1) * (k + 1):
            print('error in maxmin')
            exit()
        new_comittee.append(id)
    committee = new_comittee
    for s in s_votes:
        votes.append([c for c in committee if int(c / (k + 1)) in s])
    new_ids = {}
    id = 0
    for c in committee:
        new_ids[c] = id
        id += 1
    for v in votes:
        for i in range(len(v)):
            v[i] = new_ids[v[i]]

    num_remaining_candidates = len(committee)

    supporter_list = [[] for _ in range(num_remaining_candidates)]

    for i in range(len(votes)):
        for j in range(len(votes[i])):
            supporter_list[votes[i][j]].append([i, j])

    num_voters = len(votes)
    m = gp.Model("mip1")

    m.setParam('OutputFlag', False)
    m.setParam('FeasibilityTol', 1e-8)

    supp = m.addVars(num_remaining_candidates, lb=0, vtype=GRB.CONTINUOUS)
    opt = m.addVar(vtype=GRB.CONTINUOUS)

    xs = []
    for v in votes:
        x = m.addVars(len(v), lb=0, vtype=GRB.CONTINUOUS)
        xs.append(x)

    for i in range(num_voters):
        m.addConstr(gp.quicksum(xs[i][j] for j in range(len(votes[i]))) <= weights[i] / total)

    for j in range(num_remaining_candidates):
        m.addConstr(gp.quicksum(xs[tup[0]][tup[1]] for tup in supporter_list[j]) == supp[j])
        m.addConstr(opt <= supp[j])

    m.setObjective(opt, GRB.MAXIMIZE)
    m.optimize()

    try:
        support_values = [supp[j].X for j in range(num_remaining_candidates)]
    except:
        print(weights, committee)
    summed = sum(support_values)
    return m.objVal, np.std(support_values), sorted(support_values)


def priceability_dev(weights, s_votes, committee, num_candidates, papp=False, given_price=None):
    not_included = [i for i in range(num_candidates) if not i in committee]

    total = sum(weights)
    votes = []
    k = len(committee)
    new_comittee = []

    for c in committee:
        id = num_candidates + c * (k + 1)
        while id in new_comittee:
            id += 1
        if id > num_candidates + (c + 1) * (k + 1):
            print('error in price')
            exit()
        new_comittee.append(id)
    committee = new_comittee
    committee_member_votes = []
    non_committee_member_votes = []
    for s in s_votes:
        committee_member_votes.append([c for c in committee if int((c - num_candidates) / (k + 1)) in s])
        non_committee_member_votes.append([c for c in not_included if c in s])
    new_ids = {}
    id = 0
    for c in committee + not_included:
        new_ids[c] = id
        id += 1
    for v in committee_member_votes:
        for i in range(len(v)):
            v[i] = new_ids[v[i]]
    for v in non_committee_member_votes:
        for i in range(len(v)):
            v[i] = new_ids[v[i]]

    num_candidates = id

    num_remaining_candidates = len(committee)

    updated_com = [new_ids[c] for c in committee]
    updated_not_com = [new_ids[c] for c in not_included]

    supporter_list = [[] for _ in range(num_candidates)]

    for i in range(len(committee_member_votes)):
        for j in range(len(committee_member_votes[i])):
            supporter_list[committee_member_votes[i][j]].append([i, j])

    supporter_list_non_commitee = [[] for _ in range(num_candidates)]
    for i in range(len(non_committee_member_votes)):
        for j in range(len(non_committee_member_votes[i])):
            supporter_list_non_commitee[non_committee_member_votes[i][j]].append(i)

    if papp:
        for i in range(len(non_committee_member_votes)):
            for j in range(len(committee_member_votes[i])):
                supporter_list_non_commitee[committee_member_votes[i][j]].append(i)

    num_voters = len(committee_member_votes)
    m = gp.Model("mip1")

    m.setParam('OutputFlag', True)
    m.setParam('FeasibilityTol', 1e-8)

    if papp:
        supp = m.addVars(num_candidates, lb=0, vtype=GRB.CONTINUOUS)
    else:
        supp = m.addVars(len(updated_not_com), lb=0, vtype=GRB.CONTINUOUS)
    opt = m.addVar(vtype=GRB.CONTINUOUS, lb=-1, ub=1)
    price = m.addVar(vtype=GRB.CONTINUOUS)

    if not given_price is None:
        m.addConstr(price == given_price)

    xs = []
    for v in committee_member_votes:
        x = m.addVars(len(v) + 1, lb=0, vtype=GRB.CONTINUOUS)
        xs.append(x)

    for i in range(num_voters):
        m.addConstr(gp.quicksum(xs[i][j] for j in range(len(committee_member_votes[i]) + 1)) == weights[i] / total)

    for j in range(num_remaining_candidates):
        m.addConstr(gp.quicksum(xs[tup[0]][tup[1]] for tup in supporter_list[j]) == price)
    if papp:
        for j in range(num_candidates):
            m.addConstr(gp.quicksum(xs[v][len(committee_member_votes[v])] for v in
                                    supporter_list_non_commitee[j]) == supp[j])
            m.addConstr(opt >= supp[j] - price)
    else:
        for j in range(num_candidates - num_remaining_candidates):
            m.addConstr(gp.quicksum(xs[v][len(committee_member_votes[v])] for v in
                                    supporter_list_non_commitee[j + num_remaining_candidates]) == supp[j])
            m.addConstr(opt >= supp[j] - price)

    m.setObjective(opt, GRB.MINIMIZE)
    m.optimize()


    try:
        support_values = [(supp[j].X - price.X) / price.X for j in range(len(updated_not_com))]
    except:
        print('ERROR OCCURED in PRICE DEV')
        print(weights, committee, num_candidates, papp, given_price)

    return m.objVal / price.X, sorted(support_values,reverse=True), price.X



def minimum_support(weights, s_votes, committee,l_list,rule,idd):
    total = sum(weights)
    votes = []
    k = len(committee)
    new_comittee = []

    for c in committee:
        id = c * (k + 1)
        while id in new_comittee:
            id += 1
        if id > (c + 1) * (k + 1):
            print('error in minimum supp')
            exit()
        new_comittee.append(id)
    committee = new_comittee
    for s in s_votes:
        votes.append([c for c in committee if int(c / (k + 1)) in s])
    new_ids = {}
    id = 0
    for c in committee:
        new_ids[c] = id
        id += 1
    for v in votes:
        for i in range(len(v)):
            v[i] = new_ids[v[i]]

    num_remaining_candidates = len(committee)

    results=[]
    prev=[]
    first=True

    if polkadot:
        prefix = "./pol_plots/"
    else:
        prefix = "./kur_plots/"
    dir =  prefix + str(k) + "/minimum_support/"+rule+"/"
    if not os.path.exists(dir):
        os.makedirs(dir)

    f = open(dir+str(idd)+".txt", "w")
    f.write("")
    f.close()
    print(dir+str(idd)+".txt")

    for num_sel in l_list:
        print("NUMMM SELECTED", num_sel)
        num_voters = len(votes)
        m = gp.Model("mip1")
        m.setParam('OutputFlag', True)
        m.setParam('FeasibilityTol', 1e-8)
        m.setParam('Presolve', 2)
        m.setParam('MIPGap',1e-3)
        selected = m.addVars(num_remaining_candidates,vtype=GRB.BINARY)




        non_intersecting_votes = m.addVars(num_voters, lb=0, ub=1, vtype=GRB.CONTINUOUS)
        opt = m.addVar(vtype=GRB.CONTINUOUS)

        m.addConstr(gp.quicksum(selected[j] for j in range(num_remaining_candidates)) == num_sel)

        for i in range(num_voters):
            for c in votes[i]:
                m.addConstr(selected[c] + non_intersecting_votes[i] <= 1)

        m.addConstr(gp.quicksum((1 - non_intersecting_votes[j]) * weights[j] / total for j in range(num_voters)) == opt)

        if not first:
            m.update()
            t = 0
            for v in m.getVars():
                v.Start = prev[t]
                t += 1
        m.setObjective(opt, GRB.MINIMIZE)
        m.optimize()

        results.append(m.objVal)


        f = open(dir+str(idd)+".txt", "a")
        f.write(str(m.objVal)+"\n")
        f.close()

        first=False
        prev=[]
        for v in m.getVars():
            prev.append(v.X)

    return results


def ejr_plus_violations(weights, votes, committee, k, m,papp=False):
    total = sum(weights)
    n = len(votes)
    voter_satsifaction = [0] * n
    violations = []
    counter_committee = Counter(committee)
    for i, v in enumerate(votes):
        voter_satsifaction[i] = sum([counter_committee[c] for c in v if c in counter_committee])
    for l in range(1, k + 1):
        candidates_support = [0] * m
        for i in range(len(votes)):
            if voter_satsifaction[i] < l:
                for c in votes[i]:
                    if c not in committee or papp:
                        candidates_support[c] += weights[i]
        violations = violations + [c for c in range(m) if candidates_support[c] > (l * total) / k]
    return len(set(violations))


def prop_degree(weights, votes, committee, k, m, papp=False):
    total = sum(weights)
    n = len(votes)
    voter_satsifaction = [0] * n
    counter_committee = Counter(committee)
    for i, v in enumerate(votes):
        voter_satsifaction[i] = sum([counter_committee[c] for c in v if c in counter_committee])

    supporter_sets = [[] for _ in range(m)]
    summed_weights = [[] for _ in range(m)]
    average_satis = [[] for _ in range(m)]
    for i, v in enumerate(votes):
        for c in v:
            supporter_sets[c].append(i)
    for c in range(m):
        supporter_sets[c] = [x for _, x in
                             sorted(zip([voter_satsifaction[i] for i in supporter_sets[c]], supporter_sets[c]))]
        summed_weights[c] = [sum([weights[supporter_sets[c][j]] for j in range(i + 1)]) for i in
                             range(len(supporter_sets[c]))]
        average_satis[c] = [
            sum([weights[supporter_sets[c][j]] * voter_satsifaction[supporter_sets[c][j]] for j in range(i + 1)]) /
            summed_weights[c][i] for i in
            range(len(supporter_sets[c]))]

    unselected_candidate_supporter_set = [0 for _ in range(k)]

    min_rep = []
    for t in range(1, k + 1):
        cur = k + 1
        for c in range(m):
            if c not in committee or papp:
                if len(supporter_sets[c]) > 0 and summed_weights[c][-1] >= t * total / k:
                    unselected_candidate_supporter_set[t - 1] += 1
                    nec_vot = next(x for x, val in enumerate(summed_weights[c])
                                   if val >= t * total / k)
                    if average_satis[c][nec_vot] < cur:
                        cur = average_satis[c][nec_vot]
        if cur != k + 1:
            min_rep.append(cur)
    return 0, min_rep, unselected_candidate_supporter_set


def jr_check(weights, votes, committee, k, m, candidate_names, voter_names,papp=False):
    total = sum(weights)
    n = len(votes)
    voter_satsifaction = [0] * n
    counter_committee = Counter(committee)
    for i, v in enumerate(votes):
        voter_satsifaction[i] = sum([counter_committee[c] for c in v if c in counter_committee])
    candidates_support = [0] * m
    for i in range(len(votes)):
        if voter_satsifaction[i] == 0:
            for c in votes[i]:
                if c not in committee or papp:
                    candidates_support[c] += weights[i]
    violations = [c for c in range(m) if candidates_support[c] > total / k]

    return len(set(violations))


def plotting(eras, values, rules, value_name, k, log=False, cut=None, xl=None, rev=False, marker=""):
    if xl is None:
        xl = 'Eras'
    print(value_name)
    if polkadot:
        prefix = "./pol_plots/"
    else:
        prefix = "./kur_plots/"
    dir = prefix + str(k) + "/"
    if not os.path.exists(dir):
        os.makedirs(dir)
    for i in range(len(rules)):
        if cut is None:
            if rev:
                plt.plot(eras, list(reversed(values[i])), label=rules[i], marker=marker)
            elif float('inf') in values[i]:
                cutt = values[i].index(float('inf'))
                plt.plot(eras[:cutt], values[i][:cutt], label=rules[i], marker=marker)
            else:
                plt.plot(eras, values[i], label=rules[i], marker=marker)
        else:
            plt.plot(eras[:cut + 1], values[i][:cut + 1], label=rules[i], marker=marker)
    plt.xlabel(xl)
    plt.ylabel(value_name)
    if log:
        plt.yscale('log')
    tikzplotlib.save(dir + value_name + ".tex")

    plt.legend()
    ti = ""
    for i in range(len(rules)):
        avg = sum(values[i]) / len(values[i])
        ti = ti + " " + rules[i] + " " + str(round(avg, 2))
    plt.title("\n".join(wrap(ti, 70)))
    plt.savefig(dir + value_name)
    plt.close()


def plotting_simple(eras, values, value_name, log=False):
    if polkadot:
        dir = "./pol_plots/"
    else:
        dir = "./kur_plots/"
    if not os.path.exists(dir):
        os.makedirs(dir)

    plt.title(sum(values) / len(values))
    plt.plot(eras, values)
    plt.xlabel('Eras')
    plt.ylabel(value_name)
    if log:
        plt.yscale('log')
    tikzplotlib.save(dir + value_name + ".tex", standalone=True)
    plt.savefig(dir + value_name)
    plt.close()


def candidate_support(weights, votes, committee, num_candidates):
    n = len(votes)
    voter_satsifaction = [0] * n
    counter_committee = Counter(committee)
    for i, v in enumerate(votes):
        voter_satsifaction[i] = sum([counter_committee[c] for c in v if c in counter_committee])
    candidates_approvals = {}
    candidates_approvers_weight = {}
    candidates_equal_split_support = {}

    non_com_candidates_weight = {}

    for c in committee:
        candidates_approvals[c] = 0
        candidates_approvers_weight[c] = 0
        candidates_equal_split_support[c] = 0

    for c in range(num_candidates):
        if c not in committee:
            non_com_candidates_weight[c] = 0

    for i in range(len(votes)):
        for c in votes[i]:
            if c in committee:
                candidates_approvals[c] += 1
                candidates_approvers_weight[c] += weights[i]
                candidates_equal_split_support[c] += weights[i] / voter_satsifaction[i]
            else:
                non_com_candidates_weight[c] += weights[i]

    support_committe = sorted([candidates_approvers_weight[c] / sum(weights) for c in committee])
    return candidates_approvals[min(candidates_approvals, key=candidates_approvals.get)], candidates_approvers_weight[
        min(candidates_approvers_weight, key=candidates_approvers_weight.get)] / sum(weights), \
           candidates_equal_split_support[
               min(candidates_equal_split_support, key=candidates_equal_split_support.get)] / sum(
               weights), support_committe, non_com_candidates_weight[
               max(non_com_candidates_weight, key=non_com_candidates_weight.get)] / sum(weights)


def coverage(weights, votes, committee):
    n = len(votes)
    voter_satsifaction = [0] * n
    counter_committee = Counter(committee)

    for i, v in enumerate(votes):
        voter_satsifaction[i] = sum([counter_committee[c] for c in v if c in counter_committee])
    avg_satisfaction = sum(voter_satsifaction) / len(voter_satsifaction)
    weighted_total_satisfaction = sum([voter_satsifaction[i] * weights[i] for i in range(n)]) / sum(weights)
    fraction_of_covered = sum([1 for i in range(n) if voter_satsifaction[i] > 0]) / n
    weight_fraction_of_covered = sum([weights[i] for i in range(n) if voter_satsifaction[i] > 0]) / sum(weights)
    summed_pav_score = sum(
        [sum([1 / (i + 1) for i in range(voter_satsifaction[i])]) * weights[i] for i in range(n)]) / sum(weights)

    return avg_satisfaction, weighted_total_satisfaction, fraction_of_covered, weight_fraction_of_covered, summed_pav_score


def buying_candidates(details, k, number, rule, total):
    if rule == "sav":
        money_needed = number * details[-k + number - 1]
    elif rule == "av_unb":
        money_needed = details[-k + number - 1]
    elif rule == "av":
        money_needed = math.ceil(number / 16) * details[-k + number - 1]
    elif rule == "phragmms" or rule == "phragmms-PAPP":
        money_needed = details[k - number]
    elif rule == "seqphragmen" or rule == "seqphragmen-PAPP":
        thresh = details[k - number]
        money_needed = number * 1 / thresh
    else:
        money_needed = 0
    return money_needed / total


def plot_money_needed(eras, elections, rules, committees, details, k):
    money_needed = []
    for j in range(len(rules)):
        money_needed_single = []
        for i in range(len(elections)):
            [weights, votes, num_candidates, candidate_names, _, _, _] = elections[i]
            money_needed_single.append(
                [buying_candidates(details[i][j], k, t, rules[j], sum(weights)) for t in range(1, k + 1)])
        money_needed.append(money_needed_single)

    plotting(eras, [[money_needed[j][i][0] for i in range(len(elections))] for j in range(len(rules))], rules,
             "Cost of Buying One", k)
    plotting(eras, [[money_needed[j][i][int(k / 2) - 1] for i in range(len(elections))] for j in range(len(rules))],
             rules, "Cost of Buying Half", k)
    plotting(list(range(k)),
             [[sum([money_needed[j][i][t] for i in range(len(elections))]) / len(elections) for t in range(k)] for j in
              range(len(rules))],
             rules, "cost of buying", k, xl="number of committee members")
    return money_needed


def paap_compute_candidate_frequencies(rules, committees, k):
    freq_dis = []
    for j in range(len(rules)):
        freq_dis_single = []
        for i in range(len(committees)):
            print(len(committees[i][j]))
            counter = collections.Counter(committees[i][j])
            frequencies = [counter[x] for x in sorted(counter.keys())]
            frequencies.sort(reverse=True)
            print(frequencies)
            print(len(frequencies))
            frequencies = frequencies + ([0] * (k - len(frequencies)))
            freq_dis_single.append(frequencies)
        freq_dis.append(freq_dis_single)

    plotting(list(range(k)),
             [[sum([freq_dis[j][i][t] for i in range(len(elections))]) / len(elections) for t in range(k)] for j in
              range(len(rules))],
             rules, "frequencies of duplicates", k, log=False)


def plots_single(k, max_min, ejrp, props, prop_deg, minimum_supp, l_list, pricea, pricea_maxi, rules, lenel,
                 combined_object):
    [election, winning_committee, i, j, next_commitee, next_election] = combined_object
    if rules[j][-4:] == "PAPP":
        papp = True
    else:
        papp = False
    print(i, j)
    [weights, votes, num_candidates, candidate_names, voter_names, _, _] = election

    ####OVERLAP WITH NEXT####
    if i < lenel - 1:
        [_, _, _, next_candidate_names, _, _, _] = next_election
        ov_next = compute_distances_successive_committees(winning_committee, next_commitee,
                                                          candidate_names, next_candidate_names)
    else:
        ov_next = 0
    if max_min:
        ###MAXIMIN SUPPORT###
        ms, vs, dist = maximin_support(weights, votes, winning_committee)
    else:
        ms, vs, dist = 0, 0, 0

    ####COVERAGE AND SATISFACTION####
    a_s, w_t_s, f_o_s, w_f_o_c, s_p_s = coverage(weights, votes, winning_committee)

    ###CANDIDATE COVERAGE
    c_a, c_w, c_s, sup_dis, approver_non_com = candidate_support(weights, votes, winning_committee, num_candidates)

    ####EJR PLURS
    if ejrp:
        ejr_pl = ejr_plus_violations(weights, votes, winning_committee, k, num_candidates,papp)
    else:
        ejr_pl = 0
    print('HEY')
    ####Prop notions
    if props:
        jr = jr_check(weights, votes, winning_committee, k, num_candidates, voter_names, candidate_names,papp)
    else:
        jr = 0

    if prop_deg:
        min_prop, dist_prop, unselected_cand = prop_degree(weights, votes, winning_committee, k, num_candidates, papp)
    else:
        min_prop, dist_prop, unselected_cand = 0, [0 for _ in range(k)], [0 for _ in range(k)]

    if minimum_supp:
        supp_list=minimum_support(weights, votes, winning_committee, l_list,rules[j],i)
    else:
        supp_list = [0 for _ in l_list]
    if pricea:
        price, list_p, pr = priceability_dev(weights, votes, winning_committee, num_candidates, papp=papp)
    else:
        pr = 0
        price = 0
        list_p = [0 for _ in range(num_candidates - k)]

    if pricea_maxi:
        price_2, list_p_2, pr2 = priceability_dev(weights, votes, winning_committee, num_candidates, papp=papp,
                                                  given_price=ms)
    else:
        pr2 = 0
        price_2 = 0
        list_p_2 = [0 for _ in range(num_candidates - k)]

    return [ov_next, ms, vs, dist, a_s, w_t_s, f_o_s, w_f_o_c, s_p_s, c_a, c_w, c_s, ejr_pl,
            jr, sup_dis, min_prop, dist_prop, supp_list, price, list_p, approver_non_com, price_2, list_p_2, pr, pr2,
            unselected_cand]


def myround(n):
    if n == 0:
        return 0
    if n >= 1:
        return round(n, 3)
    else:
        return round(n, 1 - int(floor(log10(abs(n)))))


def plot_stats(eras, elections, rules, committees, details, k, max_min=False, ejrp=False, props=False, buying=False,
               prop_d=False, minimum_supp=False, pricea=False, price_maxi=False):
    if buying:
        money_needed = plot_money_needed(eras, elections, rules, committees, details, k)
    overlap_to_next = []
    min_support = []
    var_support = []
    avg_satisfaction = []
    weighted_total_satisfaction = []
    fraction_of_covered = []
    weight_fraction_of_covered = []
    summed_pav_score = []
    min_candidate_approval = []
    min_candidate_weight = []
    min_candidate_support_split = []
    supports = []
    supports_g = []
    ejr_plus = []
    jr = []
    price = []
    s_price = []
    prop_d_min = []
    prop_d_dis = []

    minimum_supp_dis = []

    price_dev = []
    price_dev_dis = []
    approver_non_com = []

    price_dev_maxi = []
    price_dev_dis_maxi = []

    price = []
    price_maximin = []

    unselected_cand = []


    l_list=list(range(1,k+1,15))

    for j in range(len(rules)):
        print(rules[j])

        # partial_func = functools.partial(plots_single, elections, committees, k, max_min, ejrp, props,prop_d,minimum_supp,l_list,pricea,price_maxi,rules, j)
        # pool = multiprocessing.Pool(40)
        # results = pool.map(partial_func, list(range(len(elections))))

        combined_object = [[elections[i], committees[i][j], i, j, committees[i + 1][j], elections[i + 1]] for i in
                           range(len(elections) - 1)]
        combined_object.append(
            [elections[len(elections) - 1], committees[len(elections) - 1][j], len(elections) - 1, j, None, None])
        partial_func = functools.partial(plots_single, k, max_min, ejrp, props, prop_d, minimum_supp, l_list, pricea,
                                         price_maxi, rules, len(elections))
        pool = multiprocessing.Pool(multiprocessing.cpu_count())
        results = pool.map(partial_func, combined_object)

        pool.close()
        pool.join()

        overlap_to_next_single = [results[i][0] for i in range(len(elections))]
        min_support_single = [results[i][1] for i in range(len(elections))]
        var_support_single = [results[i][2] for i in range(len(elections))]
        supports_single = [results[i][3] for i in range(len(elections))]
        avg_satisfaction_single = [results[i][4] for i in range(len(elections))]
        weighted_total_satisfaction_single = [results[i][5] for i in range(len(elections))]
        fraction_of_covered_single = [results[i][6] for i in range(len(elections))]
        weight_fraction_of_covered_single = [results[i][7] for i in range(len(elections))]
        summed_pav_score_single = [results[i][8] for i in range(len(elections))]
        min_candidate_approval_single = [results[i][9] for i in range(len(elections))]
        min_candidate_weight_single = [results[i][10] for i in range(len(elections))]
        min_candidate_support_split_single = [results[i][11] for i in range(len(elections))]
        ejr_plus_single = [results[i][12] for i in range(len(elections))]
        jr_single = [results[i][13] for i in range(len(elections))]
        supports_single_g = [results[i][14] for i in range(len(elections))]

        prop_d_min.append([results[i][15] for i in range(len(elections))])
        prop_d_dis.append([results[i][16] for i in range(len(elections))])

        minimum_supp_dis.append([results[i][17] for i in range(len(elections))])

        price_dev.append([results[i][18] for i in range(len(elections))])
        price_dev_dis.append([results[i][19] for i in range(len(elections))])

        approver_non_com.append([results[i][20] for i in range(len(elections))])

        price_dev_maxi.append([results[i][21] for i in range(len(elections))])
        price_dev_dis_maxi.append([results[i][22] for i in range(len(elections))])

        price.append([results[i][23] for i in range(len(elections))])
        price_maximin.append([results[i][24] for i in range(len(elections))])

        unselected_cand.append([results[i][25] for i in range(len(elections))])


        jr.append(jr_single)
        ejr_plus.append(ejr_plus_single)
        supports.append(supports_single)
        min_support.append(min_support_single)
        var_support.append(var_support_single)
        overlap_to_next.append(overlap_to_next_single)
        avg_satisfaction.append(avg_satisfaction_single)
        weighted_total_satisfaction.append(weighted_total_satisfaction_single)
        fraction_of_covered.append(fraction_of_covered_single)
        weight_fraction_of_covered.append(weight_fraction_of_covered_single)
        summed_pav_score.append(summed_pav_score_single)
        min_candidate_approval.append(min_candidate_approval_single)
        min_candidate_weight.append(min_candidate_weight_single)
        min_candidate_support_split.append(min_candidate_support_split_single)
        supports_g.append(supports_single_g)

    plotting(eras[:-1], [overlap_to_next[j][:-1] for j in range(len(overlap_to_next))], rules, "reelected candidates",
             k)
    if max_min:
        plotting(eras, min_support, rules, "maximin support", k, log=True)
        plotting(eras, var_support, rules, "maximin support var", k, log=True)
        plotting(list(range(k)),
                 [[sum([supports[j][i][t] for i in range(len(elections))]) / len(elections) for t in range(k)] for j in
                  range(len(rules))], rules, "assigned support in maximin assignment", k, log=True,
                 xl="number of candidates", rev=True)

    plotting(list(range(k)),
             [[sum([supports_g[j][i][t] for i in range(len(elections))]) / len(elections) for t in range(k)] for j in
              range(len(rules))], rules, "support", k, log=True)
    if props:
        plotting(eras, jr, rules, "jr_sati", k)
    if prop_d:
        plotting(eras, prop_d_min, rules, "proportionality degree ratio", k)

        rewritte = []
        for j in range(len(rules)):
            indiv = [[] for _ in range(k)]
            for i in range(len(elections)):
                for t in range(len(prop_d_dis[j][i])):
                    indiv[t].append(prop_d_dis[j][i][t])
            rewritte.append([sum(indiv[i]) / len(indiv[i]) for i in range(k) if len(indiv[i]) > 0])

        max_length = max([len(prop_d_dis[j][i]) for i in range(len(elections)) for j in
                          range(len(rules))])
        for r in rewritte:
            while len(r) < max_length:
                r.append(float('inf'))


        plotting(list(range(1, max_length + 1)),
                 rewritte + [list(range(1, max_length + 1))], rules + ['linear'], "minimum average satisfaction", k,
                 xl='number of supporters', marker="x")

        to_plot = [[sum([unselected_cand[j][i][t] for i in range(len(elections))]) / len(elections) for t in range(k)]
                   for j in range(len(rules))]

        max_nonzero = max([to_plot[j].index(0) for j in range(len(rules))])

        plotting(list(range(1, k + 1)),
                 [[sum([unselected_cand[j][i][t] for i in range(len(elections))]) / len(elections) for t in range(k)]
                  for j
                  in
                  range(len(rules))], rules, "\# non-selected candidates", k, cut=max_nonzero,
                 xl='number of supporters', marker="x")

    if minimum_supp:
        plotting(l_list,
                 [[sum([minimum_supp_dis[j][i][t] for i in range(len(elections))]) / len(elections) for t in
                   range(len(l_list))] for j in
                  range(len(rules))], rules, "minimum summed money", k)

    if pricea:
        plotting(eras, price, rules, "pricability", k)
        plotting(eras, price_dev, rules, "deviation_pricability", k)
        plotting(list(range(min([e[2] for e in elections]) - k - 1)),
                 [[sum([price_dev_dis[j][i][t] for i in range(len(elections))]) / len(elections) for t in
                   range(min([e[2] for e in elections]) - k - 1)] for j
                  in
                  range(len(rules))], rules, "frac{supporter's money-price}{price}", k, xl="number of candidates",
                 rev=False)

    if price_maxi:
        plotting(eras, price_maximin, rules, "pricability_maximin", k)
        plotting(eras, price_dev_maxi, rules, "deviation_pricability_maximin", k)
        plotting(list(range(min([e[2] for e in elections]) - k)),
                 [[sum([price_dev_dis_maxi[j][i][t] for i in range(len(elections))]) / len(elections) for t in
                   range(min([e[2] for e in elections]) - k)] for j
                  in
                  range(len(rules))], rules, "deviation_pricability assign_maximin", k)

    plotting(eras, approver_non_com, rules, "Maximum Approver Weight of Non Committee Member", k)
    plotting(eras, avg_satisfaction, rules, "Average Voter Satisfaction", k)
    plotting(eras, weighted_total_satisfaction, rules, "Weighted Total Satisfaction", k)
    plotting(eras, fraction_of_covered, rules, "Fraction of Voters Covered", k)
    plotting(eras, weight_fraction_of_covered, rules, "Fraction of Weight Covered", k)
    plotting(eras, summed_pav_score, rules, "Total PAV score", k)

    plotting(eras, min_candidate_approval, rules, "min approval score of committee member", k)
    plotting(eras, min_candidate_weight, rules, "min approver weight of committee member", k, log=True)
    plotting(eras, min_candidate_support_split, rules, "min approver equal split", k, log=True)
    if ejrp:
        plotting(eras, ejr_plus, rules, "ejr plus violations", k)
    ###Overalp of rules####
    ov_rules = []
    ov_results = []
    aggreg_results = [[[] for _ in range(len(rules))] for _ in range(len(rules))]
    for i in range(len(rules)):
        aggreg_results[i][i] = [0]
    for i in range(len(rules)):
        for j in range(i + 1, len(rules)):
            ov_rules.append(rules[i] + " " + rules[j])
            ov_results.append([])
    for i in range(len(elections)):
        winning_committees = committees[i]
        overlap = compute_pairwise_distances(winning_committees)
        id = 0
        for i in range(len(rules)):
            for j in range(i + 1, len(rules)):
                relevant_ov_results = ov_results[id]
                relevant_ov_results.append(overlap[i, j])
                aggreg_results[i][j].append(overlap[i, j])
                aggreg_results[j][i].append(overlap[i, j])
                id += 1
    df = pd.DataFrame(
        [[sum(aggreg_results[i][j]) / len(aggreg_results[i][j]) for i in range(len(rules))] for j in range(len(rules))],
        columns=rules, index=rules)
    eval_df_styled = df.style.background_gradient()  # adding a gradient based on values in cell

    if polkadot:
        prefix = "./pol_plots/" + str(k) + "/"
    else:
        prefix = "./kur_plots/" + str(k) + "/"


    df = df.applymap(myround)
    original_stdout = sys.stdout  # Save a reference to the original standard output

    with open(prefix + 'overlap_rules.txt', 'w') as f:
        sys.stdout = f  # Change the standard output to the file we created.
        print(df.to_latex())
        sys.stdout = original_stdout

    plotting(eras, ov_results, ov_rules, "Overlap of Different Rules", k)

    metrics = ["overlap next", "maximin support", "maximin variance", "JR violations", "EJR+ violations",
               "prop deg \ell=1", "prop deg \ell=5", "prop deg \ell=10", "price", "priceability gap",
               "price dev maximin", "maximum support of loser", "weighted satisfaction", "covered weight", "PAV score",
               "minimum support of winner", "buying one", "buying half", "buying one-third",
               "minimum weight of winner (equal split)", "priceability violations"]

    if prop_d:
        prop1 = [[rewritte[j][0] if len(rewritte[j]) > 0 else -1] for j in range(len(rules))]
        prop5 = [[rewritte[j][4] if len(rewritte[j]) > 4 else -1] for j in range(len(rules))]
        prop10 = [[rewritte[j][9] if len(rewritte[j]) > 9 else -1] for j in range(len(rules))]
    else:
        prop1 = [[-1] for _ in range(len(rules))]
        prop5 = [[-1] for _ in range(len(rules))]
        prop10 = [[-1] for _ in range(len(rules))]

    if buying:
        money_needed1 = [[money_needed[j][i][0] for i in range(len(elections))] for j in range(len(rules))]
        money_neededhalf = [[money_needed[j][i][int(k / 2) - 1] for i in range(len(elections))] for j in
                            range(len(rules))]
        money_neededtwothrid = [[money_needed[j][i][int(k / 3) - 1] for i in range(len(elections))] for j in
                                range(len(rules))]
    else:
        money_needed1 = [[-1] for _ in range(len(rules))]
        money_neededhalf = [[-1] for _ in range(len(rules))]
        money_neededtwothrid = [[-1] for _ in range(len(rules))]
    priceability_violations = [
        [sum([1 for t in range(len(price_dev_dis[j][i])) if price_dev_dis[j][i][t] >= 0]) for i in
         range(len(elections))] for j
        in
        range(len(rules))]

    result_lists = [overlap_to_next, min_support, var_support, jr, ejr_plus, prop1, prop5, prop10, price, price_dev,
                    price_dev_maxi, approver_non_com, weighted_total_satisfaction, weight_fraction_of_covered,
                    summed_pav_score, min_candidate_weight, money_needed1, money_neededhalf, money_neededtwothrid,
                    min_candidate_support_split, priceability_violations]
    aggreg_results = [[[] for _ in range(len(metrics))] for _ in range(len(rules))]
    for id in range(len(result_lists)):
        for j in range(len(rules)):
            aggreg_results[j][id] = sum(result_lists[id][j]) / len(result_lists[id][j])
    df = pd.DataFrame(
        aggreg_results,
        columns=metrics, index=rules)
    eval_df_styled = df.style.background_gradient()  # adding a gradient based on values in cell

    if polkadot:
        prefix = "./pol_plots/" + str(k) + "/"
    else:
        prefix = "./kur_plots/" + str(k) + "/"

    df = df.applymap(myround)

    original_stdout = sys.stdout  # Save a reference to the original standard output

    with open(prefix + 'summary_prop' + str(time.time()) + '.txt', 'w') as f:
        sys.stdout = f  # Change the standard output to the file we created.
        print(df.to_latex(columns=["weighted satisfaction", "PAV score", "maximum support of loser", "JR violations",
                                   "EJR+ violations", "prop deg \ell=1", "prop deg \ell=5", "prop deg \ell=10",
                                   "priceability violations", "priceability gap"]))
        sys.stdout = original_stdout

    original_stdout = sys.stdout  # Save a reference to the original standard output

    with open(prefix + 'summary_overrep' + str(time.time()) + '.txt', 'w') as f:
        sys.stdout = f  # Change the standard output to the file we created.
        print(df.to_latex(
            columns=["covered weight", "maximin support", "maximin variance", "minimum support of winner", "buying one","buying one-third",
                     "buying half", "minimum weight of winner (equal split)"]))
        sys.stdout = original_stdout
    print(prefix + str(time.time()) + "summary.png")
    dfi.export(eval_df_styled, prefix + "summary.png", table_conversion="matplotlib")


def compute_winning_committees(weights, votes, num_candidates, k, rules):
    profile = Profile(num_cand=num_candidates)
    for i in range(len(weights)):
        profile.add_voter(Voter(votes[i], weights[i]))
    results = []
    for rule in rules:
        if rule in ["av", "sav"]:
            res, details = separable_rule_algorithm(rule, profile, k, resolute=True)
        elif rule == "seqcc":
            res, details = seq_thiele("cc", profile, k)
        elif rule == "seqpav":
            res, details = seq_thiele("pav", profile, k)
        elif rule == "seqphragmen":
            res, details = seqphragmen(profile, k)
        elif rule == "greedy_ejrp":
            res, details = greedy_justified_candidate_rule(weights, votes, k, num_candidates)
        elif rule == "mes":
            res, details = equal_shares(weights, votes, num_candidates, k)
        elif rule == "seqphragmen-PAPP":
            res, details = seqphragmen(profile, k, papp=True)
        elif rule == "mes-PAPP":
            res, details = equal_shares(weights, votes, num_candidates, k, papp=True)
        elif rule == "seqpav-PAPP":
            res, details = seq_thiele("pav", profile, k, papp=True)
        elif rule == "phragmms":
            res, details = my_phragmms(weights, votes, num_candidates, k)


        elif rule == "phragmms-PAPP":
            res, details = my_phragmms(weights, votes, num_candidates, k, papp=True)
        else:
            print(rule, " RULE NOT IMPLEMENTED")
        results.append([res, details])
    return results


def store_committees(era, committees, rules, k, self_multiplier):
    if polkadot:
        prefix = "./pol_committees/"
    else:
        prefix = "./kur_committees/"
    if self_multiplier == 1:
        os.makedirs(prefix + str(k) + "/", exist_ok=True)  #
        for i in range(len(committees)):
            with open(prefix + str(k) + '/' + str(era) + '_' + rules[i] + '.txt', 'w') as f:
                f.write(str(committees[i][0]))
            with open(prefix + str(k) + '/' + str(era) + '_' + rules[i] + '_details.txt', 'w') as f:
                f.write(str(committees[i][1]))
    else:
        os.makedirs(prefix + str(k) + "/" + str(self_multiplier) + "/", exist_ok=True)  #
        for i in range(len(committees)):
            with open(prefix + str(k) + '/' + str(self_multiplier) + "/" + str(era) + '_' + rules[i] + '.txt',
                      'w') as f:
                f.write(str(committees[i][0]))
            with open(prefix + str(k) + '/' + str(self_multiplier) + "/" + str(era) + '_' + rules[i] + '_details.txt',
                      'w') as f:
                f.write(str(committees[i][1]))


def compute_and_write_single_committee(k, rules, self_multiplier, id):
    if polkadot:
        file = "./pol_elections/era" + str(id) + ".txt"
    else:
        file = "./kur_elections/era" + str(id) + ".txt"
    print(id)
    if self_multiplier == 1:
        [weights, votes, num_candidates, _, _, _, _] = read_election(file)
    else:
        [weights, votes, num_candidates, _, _, svotes, sstake] = read_election(file)
        for i in range(self_multiplier - 1):
            weights = weights + sstake
            votes = votes + svotes
    if 0 in weights:
        print(weights, id)
    winning_committees = compute_winning_committees(weights, votes, num_candidates, k, rules)
    store_committees(id, winning_committees, rules, k, self_multiplier)


def compute_and_write_committees(start, end, k, rules, self_multiplier=1, sub=None):
    if sub is None:
        sub = range(start, end + 1)
    eras = []
    for id in sub:
        if polkadot:
            file = "./pol_elections/era" + str(id) + ".txt"
        else:
            file = "./kur_elections/era" + str(id) + ".txt"
        if os.path.exists(file):
            eras.append(id)
    partial_func = functools.partial(compute_and_write_single_committee, k, rules, self_multiplier)
    pool = multiprocessing.Pool(multiprocessing.cpu_count())
    pool.map(partial_func, eras)
    pool.close()
    pool.join()



def read_committees(start, end, k, rules, self_multiplier=1, sub=None):
    if polkadot:
        prefix = "./pol_committees/"
    else:
        prefix = "./kur_committees/"
    elections = []
    winning_committees = []
    winning_committees_list = []
    details_committees = []
    eras = []
    if sub is None:
        sub = range(start, end + 1)
    for id in sub:
        if polkadot:
            file_e = "./pol_elections/era" + str(id) + ".txt"
        else:
            file_e = "./kur_elections/era" + str(id) + ".txt"
        if os.path.exists(file_e):
            eras.append(id)
            election = read_election(file_e)
            elections.append(election)
            winning_committees_era = []
            winning_committees_list_era = []
            details_committees_era = []
            for rule in rules:
                if self_multiplier == 1:
                    file_c = prefix + str(k) + '/' + str(id) + '_' + rule + '.txt'
                else:
                    file_c = prefix + str(k) + '/' + str(self_multiplier) + '/' + str(id) + '_' + rule + '.txt'
                with open(file_c, 'r') as f:
                    read_set = f.read()
                wc = eval(read_set)
                winning_committees_list_era.append(list(wc))
                file_d = prefix + str(k) + '/' + str(id) + '_' + rule + '_details.txt'
                if os.path.isfile(file_d):
                    with open(file_d, 'r') as f:
                        read_set = f.read()
                    if read_set == "None":
                        details_committees_era.append([0] * election[2])
                    else:
                        wc = eval(read_set)
                        if len(read_set) == 0:
                            print("ERRR")
                            exit()
                        details_committees_era.append(wc)
                else:
                    details_committees_era.append([0] * election[2])
            winning_committees_list.append(winning_committees_list_era)
            details_committees.append(details_committees_era)
    return eras, elections, winning_committees_list, details_committees


def compute_pairwise_distances(committees, printout=False, rules=None):
    cl = len(committees)
    overlap = np.zeros((cl, cl))
    for i in range(cl):
        for j in range(i + 1, cl):
            if type(committees[i]) is list:
                print(i, j)
            overlap[i, j] = len(list((Counter(committees[i]) & Counter(committees[j])).elements()))
            overlap[j, i] = overlap[i, j]
            if printout:
                print(rules[i], rules[j], overlap[i, j])
    return overlap


def compute_distances_successive_committees(cur_committee, next_committee, cur_candidates_names, next_candidate_names):
    cur_named_committees = [cur_candidates_names[i] for i in cur_committee]
    next_named_committees = [next_candidate_names[i] for i in next_committee]

    return len(list((Counter(cur_named_committees) & Counter(next_named_committees)).elements()))


def gini(x):
    total = 0
    for i, xi in enumerate(x[:-1], 1):
        total += np.sum(np.abs(xi - x[i:]))
    return total / (len(x) ** 2 * np.mean(x))


def instance_analysis(start, end):
    if polkadot:
        prefix = "./pol_plots/"
    else:
        prefix = "./kur_plots/"
    ns = []
    ms = []
    ws = []
    avs = []
    eras = []
    gs = []
    weight_distribution = []
    support_distribution = []
    for id in range(start, end + 1):
        print(id)
        if polkadot:
            file = "./pol_elections/era" + str(id) + ".txt"
        else:
            file = "./kur_elections/era" + str(id) + ".txt"
        if os.path.exists(file):
            eras.append(id)
            [weights, votes, num_candidates, _, _, _, _] = read_election(file)
            tot = 0
            candidate_support = [0] * num_candidates
            for i, v in enumerate(votes):
                tot += len(v)
                for c in v:
                    candidate_support[c] += weights[i]
            ms.append(num_candidates)
            ns.append(len(votes))
            ws.append(sum(weights))
            avs.append(tot / len(votes))
            gs.append(gini(np.array(candidate_support, dtype=np.float64)))
            weight_distribution.append(sorted([w / sum(weights) for w in weights], reverse=True))
            support_distribution.append(sorted([w / sum(weights) for w in candidate_support], reverse=True))


    plt.plot(eras,ns)
    plt.ylabel('number of voters')
    plt.xlabel('era')
    plt.savefig(prefix + "ov_instances_n.png")
    tikzplotlib.save(prefix + "ov_instances_n.tex", standalone=True)
    plt.close()
    plt.plot(eras, ms)
    plt.ylabel('number of candidates')
    plt.xlabel('era')
    plt.savefig(prefix + "ov_instances_m.png")
    tikzplotlib.save(prefix + "ov_instances_m.tex", standalone=True)
    plt.close()


    plt.scatter(ns, ms, c=eras, s=10, marker='o', cmap='binary')
    plt.xlabel('number of voters')
    plt.ylabel('number of candidates')
    plt.colorbar()
    plt.savefig(prefix + "general_ov_instances.png")
    tikzplotlib.save(prefix + "general_ov_instances.tex", standalone=True)
    plt.close()
    plt.scatter(gs, avs, c=eras, s=10, marker='o', cmap='binary')
    plt.xlabel('gini coefficient of approval scores')
    plt.ylabel('average vote length')
    plt.colorbar()
    plt.savefig(prefix + "general_ov_instances2.png")
    tikzplotlib.save(prefix + "general_ov_instances2.tex", standalone=True)
    plt.close()
    minimum_candidate = min(ms)

    plotting(list(range(minimum_candidate)),
             [[sum([support_distribution[j][i] for j in range(len(support_distribution))]) / len(support_distribution)
               for i in range(minimum_candidate)]], ["base"], "weight of supporters", "", log=True,
             xl="number of candidates")

    minimum_voter = min(ns)
    plotting(list(range(minimum_voter)),
             [[sum([weight_distribution[j][i] for j in range(len(weight_distribution))]) / len(weight_distribution) for
               i in range(minimum_voter)]], ["base"], "voting weight", "", log=True, xl="number of voters")


def change_in_opinions(start, end):
    if polkadot:
        file = "./pol_elections/era" + str(start) + ".txt"
    else:
        file = "./kur_elections/era" + str(start) + ".txt"
    [weights, votes, num_candidates, candidates_names, voter_names, _, _] = read_election(
        file)
    prev_weights = weights
    prev_votes = votes
    prev_num_candidates = num_candidates
    prev_candidates_names = candidates_names
    prev_voter_names = voter_names

    m_changes = []
    n_changes = []
    w_changes = []
    f_v_changes = []
    eras = []
    for id in [end]:
        if polkadot:
            file = "./pol_elections/era" + str(id) + ".txt"
        else:
            file = "./kur_elections/era" + str(id) + ".txt"
        if os.path.exists(file):
            print(id)
            eras.append(id)
            [weights, votes, num_candidates, candidates_names, voter_names, _, _] = read_election(file)
            voter_int = set(voter_names).intersection(set(prev_voter_names))
            n_changes.append((len(set(voter_names)) + len(set(prev_voter_names)) - 2 * len(voter_int)) / (
                    len(set(voter_names)) + len(set(prev_voter_names))))
            m_changes.append((len(set(candidates_names)) + len(set(prev_candidates_names)) - 2 * len(
                set(candidates_names).intersection(set(prev_candidates_names)))) / (
                                     len(set(candidates_names)) + len(set(prev_candidates_names))))
            w_changes.append(sum(
                [abs(weights[voter_names.index(stash)] - prev_weights[prev_voter_names.index(stash)]) for stash in
                 voter_int]) / sum([weights[voter_names.index(stash)] for stash in
                 voter_int]))
            f_v_change_sing = []
            for stash in voter_int:
                stash_v_cur = [candidates_names[c] for c in votes[voter_names.index(stash)] if
                               candidates_names[c] in prev_candidates_names]
                stash_v_prev = [prev_candidates_names[c] for c in prev_votes[prev_voter_names.index(stash)] if
                                prev_candidates_names[c] in candidates_names]
                int_size = len(set(stash_v_cur).intersection(set(stash_v_prev)))
                if len(stash_v_cur) == 0 and len(stash_v_prev) == 0:
                    f_v_change_sing.append(0)
                else:
                    f_v_change_sing.append(
                        (len(stash_v_cur) + len(stash_v_prev) - 2 * int_size) / (len(stash_v_cur) + len(stash_v_prev)))
            f_v_changes.append(sum(f_v_change_sing) / len(f_v_change_sing))

            prev_weights = weights
            prev_votes = votes
            prev_num_candidates = num_candidates
            prev_candidates_names = candidates_names
            prev_voter_names = voter_names

    plotting_simple(eras, m_changes, "relative change in candidate set")
    plotting_simple(eras, n_changes, "relative change in voter set")
    plotting_simple(eras, w_changes, "relative change in weights of ov voters")
    plotting_simple(eras, f_v_changes, "relative opinion shift in ov voters")


def compute_distances_multip(start, end, k, rules, self_multipliers, sub=None):
    _, _, base, _ = read_committees(start, end, k, rules, self_multiplier=1, sub=sub)
    overlaps = [[0 for _ in self_multipliers] for _ in rules]
    for i in range(len(self_multipliers)):
        _, _, committees, _ = read_committees(start, end, k, rules, self_multiplier=self_multipliers[i], sub=sub)
        for j in range(len(rules)):
            overlaps[j][i] = sum([len(list((Counter(base[t][j]) & Counter(committees[t][j])).elements())) for t in
                                  range(len(committees))]) / len(committees)

    plotting(self_multipliers, overlaps, rules, "Overlap with non-weighted version", k)


if not os.path.exists('./pol_plots/'):
    os.makedirs('./pol_plots/')

if not os.path.exists('./kur_plots/'):
    os.makedirs('./kur_plots/')

polkadot = True
start = 398

end = 1078
eras=None

instance_analysis(start,end)


rules = ['av', 'sav', 'seqpav', 'phragmms', 'seqphragmen', 'mes']
for rule in rules:
    for k in [300]:
        compute_and_write_committees(start, end, k, [rule],sub=eras)

for k in [300]:
    eras, elections, winning_committees, details_committees = read_committees(start, end, k, rules, sub=eras)

    plot_stats(eras, elections, rules, winning_committees, details_committees, k, max_min=True, ejrp=True,
                   props=True,
                   prop_d=True,
                   buying=True, minimum_supp=False, pricea=True, price_maxi=False)


###CHANGING THE COMMITTEE SIZE
for rule in rules:
    for k in [200,250,350,400]:
        compute_and_write_committees(start, end, k, [rule],sub=eras)

for k in [200,250,350,400]:
    eras, elections, winning_committees, details_committees = read_committees(start, end, k, rules, sub=eras)

    plot_stats(eras, elections, rules, winning_committees, details_committees, k, max_min=True, ejrp=True,
                   props=True,
                   prop_d=True,
                   buying=True, minimum_supp=True, pricea=True, price_maxi=False)


#Allowing Copies

rules=["phragmms-PAPP","seqphragmen-PAPP", "mes-PAPP","seqpav-PAPP"]
for rule in rules:
    for k in [300]:
        compute_and_write_committees(start, end, k, [rule],sub=eras)

for k in [300]:
    eras, elections, winning_committees, details_committees = read_committees(start, end, k, rules, sub=eras)

    plot_stats(eras, elections, rules, winning_committees, details_committees, k, max_min=True, ejrp=True,
                   props=True,
                   prop_d=True,
                   buying=True, minimum_supp=True, pricea=True, price_maxi=False)



#KUSAMA


polkadot=False

start=2960
end=5164
eras=None
instance_analysis(start,end)



rules = ['av', 'sav', 'seqpav', 'phragmms', 'seqphragmen', 'mes']
for rule in rules:
    for k in [1000]:
        compute_and_write_committees(start, end, k, [rule],sub=eras)

for k in [1000]:
    eras, elections, winning_committees, details_committees = read_committees(start, end, k, rules, sub=eras)

    plot_stats(eras, elections, rules, winning_committees, details_committees, k, max_min=True, ejrp=True,
                   props=True,
                   prop_d=True,
                   buying=True, minimum_supp=True, pricea=True, price_maxi=False)
