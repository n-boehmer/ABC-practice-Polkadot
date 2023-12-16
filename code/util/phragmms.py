import code.util.npos as npos
#from code.util.npos import *
#import npos

def my_phragmms(weights,votes,num_can,k,papp=False):
    votelist = [(i,weights[i],list(votes[i])) for i in range(len(weights))]
    nom,com = npos.phragmms(votelist,k,papp=papp)
    W = [] 
    for c in com: 
        if c.duplicate: 
            W += [c.copyOf]
        else: 
            W += [c.validator_id]
    #introduced to get information about buying_in 
    tuple_list = sorted([(c.electedpos,c.electedscore) for c in com])
    buy_values = [min([tuple_list[i][1] for i in range(j+1)])*(k-j) for j in range(k)]
    return W, buy_values
