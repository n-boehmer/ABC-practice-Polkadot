def seqphragmen(
		profile, committeesize, start_load=None, partial_committee=None, papp=False
):
	"""
	Algorithm for computing resolute seq-Phragmen (1 winning committee).
	"""
	division = lambda x, y: x / y  # standard float division

	approvers_weight = {}
	for cand in profile.candidates:
		approvers_weight[cand] = sum(voter.weight for voter in profile if cand in voter.approved)
	load = start_load
	if load is None:
		load = [0 for _ in range(len(profile))]
	committee = partial_committee
	if partial_committee is None:
		committee = []  # build committees starting with the empty set

	detailed_info = {
		"next_cand": [],
		"tied_cands": [],
		"load": [],
		"max_load": [],
	}

	for _ in range(len(committee), committeesize):
		approvers_load = {}
		for cand in profile.candidates:
			approvers_load[cand] = sum(
				voter.weight * load[v] for v, voter in enumerate(profile) if cand in voter.approved
			)
		new_maxload = [
			division(approvers_load[cand] + 1, approvers_weight[cand])
			if approvers_weight[cand] > 0
			else committeesize + 1
			for cand in profile.candidates
		]
		if not papp: # exclude committees already in the committee
			for cand in profile.candidates:
				if cand in committee:
					new_maxload[cand] = committeesize + 2  # that's larger than any possible value
		opt = min(new_maxload)

		next_cand = new_maxload.index(min(new_maxload))#tied_cands[0]
		for v, voter in enumerate(profile):
			if next_cand in voter.approved:
				load[v] = new_maxload[next_cand]

		committee = sorted(committee + [next_cand])
		detailed_info["next_cand"].append(next_cand)
		detailed_info["load"].append(list(load))  # create copy of `load`
		detailed_info["max_load"].append(opt)

	detailed_info["committee_load_pairs"] = {tuple(committee): load}
	return committee, detailed_info["max_load"]
