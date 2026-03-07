# make a prefix tree(hash) of the database

def prefix_hash(db):
    ph = {}
    sz = 0
    for r, (label, rule) in enumerate(db.rules.items()):
        print(f"{r} of {len(db.rules)}, {sz=}")
        tokens = tuple(rule.consequent.tokens)
        print(tokens)
        for lead in range(len(tokens)+1):
            prefix = tokens[:lead]
            if prefix not in ph: ph[prefix] = []
            ph[prefix].append(label)
            sz += 1
        # if r == 100: break
    return ph

if __name__ == "__main__":
    import metamathpy.setmm as ms
    # db = ms.load_pl()
    db = ms.load_all()
    ph = prefix_hash(db)

    # print(ph[()])
    # print(ph[("wff",)])
    # print(ph[("wff","(")])
    # print(ph[("|-",)])
    # print(ph[("|-","(")])
    # print(ph[("|-","(","ph")])

    leads = {}
    for key in ph.keys():
        if len(key) not in leads: leads[len(key)] = []
        leads[len(key)].append(key)

    for lead in sorted(leads.keys())[:2000]:
        print(lead, len(leads[lead]))
        # print("", [" ".join(key) for key in leads[lead]])
    
