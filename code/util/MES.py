import os
import math
from abcvoting.preferences import Profile
from abcvoting.preferences import Voter
from code.util.seqPhragmen import *


def clean_election(votes,num_can):
    dummies = [c for c in range(num_can) if len([i for i in range(len(weights)) if c in votes[i]]) == 0]
    name_dict = {c:c - len([x for x in dummies if x < c]) for c in range(num_can)}
    new_votes = []
    for x in votes:
        new_votes = new_votes + [set([name_dict[y] for y in x])]
    return new_votes, num_can - len(dummies)

def clean_election_eq_sh(votes, num_can, weights, price):
    dummies = [c for c in range(num_can) if sum([weights[i] for i in range(len(weights)) if c in votes[i]]) < price]
    name_dict = {c:c - len([x for x in dummies if x < c]) for c in range(num_can)}
    new_votes = []
    for x in votes:
        new_votes = new_votes + [set([name_dict[y] for y in x])]
    return new_votes, num_can - len(dummies)

"""
Input: 
- list weights, list votes, int num_can - as returned by the read function - ORIGINAL ELECTION INSTANCE
- a list of (at most k-1) candidates W
- a list of budgets, where ith entry refers to current budget of voter i 
- a float price, corresponding to the price of a candidate as defined by the equal shares method
Output: 
- a candidate c 
- and a float q 
(such that c is q-affordable and that is the case for minimum q over all possible candidates)
"""
def min_affordable(weights, votes, num_can, budgets, price, W, papp=False):
    q_min = price + 1

    for c in range(num_can):
        
        if c in W and not papp:
            continue

        q = sum(weights) + 1

        supporters = [i for i in range(len(weights)) if c in votes[i]]
        s = len(supporters)
        if s == 0:
            continue

        # create lists of weights, relative, and absolute budgets
        sup_weights = [weights[i] for i in supporters]
        abs_budgets = [budgets[i] for i in supporters]
        rel_budgets = [budgets[i] / weights[i] for i in supporters]

        # sort all lists by non-increasing relative budget
        zipped = sorted(zip(rel_budgets, abs_budgets, sup_weights))
        sup_weights = [x for _, _, x in zipped]
        abs_budgets = [x for _, x, _ in zipped]
        rel_budgets = [x for x, _, _ in zipped]

        # find threshold in list (who is the first voter not paying full budget?)
        for i in range(s + 1):
            av_budget = sum(abs_budgets[:i]) + sum(sup_weights[j] * rel_budgets[i] for j in range(i, s))

            if av_budget >= price:
                q = (price - sum(abs_budgets[:i])) / (sum(sup_weights[j] for j in range(i, s)))
                break

        if q < q_min:
            q_min = q
            c_min = c

    if q_min == price + 1:
        return None, None
    else:
        return q_min, c_min


def equal_shares(weights, votes, num_can, k, papp=False):
    W = []
    budgets = [(weights[i]/sum(weights))*k for i in range(len(weights))]
    #price = sum(weights) / k
    price = 1
    q_list=[]

    # pre-processing: eliminate all candidates that have not chance of winning
    #votes, num_can = clean_election_eq_sh(votes, num_can, weights, price)

    for z in range(k):
        # find minimum q-affordable candidate
        q, c = min_affordable(weights, votes, num_can, budgets, price, W, papp)

        # if no candidate is q-affordable for any q, complete with seqphragmen! (build profile and construct loads from relative budgets)
        if c == None:
            if z<k: 
                rel_budgets = [budgets[i]/weights[i] for i in range(len(weights))]
                max_budget = max(rel_budgets)
                load = [max_budget - rel_budgets[i] for i in range(len(weights))]
                profile = Profile(num_can)
                for i in range(len(weights)): 
                    profile.add_voter(Voter(list(votes[i]),weight=weights[i]))
                U,_ = seqphragmen(profile,k,load,W,papp)
                return U,[]
                break
                
        W = W + [c]
        q_list = q_list + [q]
        # update budgets
        red = 0
        for i in range(len(weights)):
            if c in votes[i]:
                if budgets[i] < q * weights[i]:
                    red += budgets[i]
                    budgets[i] = 0
                else:
                    red += q * weights[i]
                    budgets[i] = budgets[i] - q * weights[i]
                    
        assert math.isclose(red,price), "Method of equal shares error: reduced budget does not coincide with price"
    return W,[]
