# ABC-practice-Polkadot

This repository contains the code and data for the experiments published in "Niclas Boehmer, Markus Brill, Alfonso Cevallos, Jonas Gehrlein, Luis Sánchez-Fernández, and Ulrike Schmidt-Kraepelin. Approval-Based Committee Voting in Practice: A Case Study of (Over-)Representation in the Polkadot Blockchain. AAAI 2024. Accepted for Publication".

### Data

The elections generated from the Polkadot network can be found in the folder pol_elections and the elections generated from the Kusama network in kur_elections. The election files follow the following format: 
1. A line starting with “#” followed by the names of the files from which the election was generated. 
2. For each candidate, one line containing their id in the election as well as their stash address in the network (separated by a “,”).
3. A line starting with “##” followed by the number of candidates, the number of voters, and the average vote length (separated by a “,”).
4. For each voter, one line containing their stash address in the network followed by “:”, their voting weight in the election followed by “:”, and the election id of the candidates they approve (candidate ids are separated by a “,”). 
5. The line “%% Self Votes”
6. For each candidate approving themselves, one line containing their stash address in the network followed by “:”, their voting weight in the election followed by “:”, and their election id (that is the election id of the candidate they approve). 

### Experiments

Besides standard libraries, a working installation of Gurobi and abcvoting (https://abcvoting.readthedocs.io/en/latest/) is needed to execute the code. 

To reproduce our experiments, please execute: python3 main.py

The results for Polkadot can be found in pol_plots/k/ where k is the committee size in question. The plots for Kusama can be found in kur_plots/k/.







