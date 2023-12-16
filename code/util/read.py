import os

def read_election(file):
    """read_election(file)

        Reads an election file and returns the election.

        Parameters
        ----------
        file: the file (with path if necessary) that contains the validators data.

        Returns:
          weights: list of voting weights of voters. Entry i of the weights list matches entry i of the votes list.
          votes: list of approval lists of voters (each approval lists contains the ids of approved candidates starting with 0).
          num_candidates: number of candidates

        """
    weights=[]
    votes=[]
    svotes = []
    sstake = []
    candidates_names=[]
    voter_names = []
    with open(file, "r") as a_file:
        vote_part = False
        self_votes=False
        for line in a_file:
            if vote_part:
                if line[:2]=="%%":
                    self_votes=True
                else:
                #Add votes as we are in the votes part of the election file
                    stripped_line = line.strip()
                    if stripped_line[-1]!=":":
                        li = list(stripped_line.split(":"))
                        if int(li[1])>0:
                            voter_names.append(li[0])
                            weights.append(int(li[1]))
                            vo=list(li[2].split(","))
                            votes.append(set([int(c) for c in vo]))
                            if self_votes:
                                svotes.append(set([int(c) for c in vo]))
                                sstake.append(int(li[1]))
            #detect start of vote part in election file
            elif line[:2]=="##":
                vote_part=True
                stripped_line = line.strip()
                li = list(stripped_line.split(" "))
                num_candidates=int(li[1])
            elif line[0]!='#':
                stripped_line = line.strip()
                li = list(stripped_line.split(","))
                candidates_names.append(li[1])
    return weights,votes,num_candidates,candidates_names,voter_names,svotes,sstake
