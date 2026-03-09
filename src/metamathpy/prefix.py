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

    import numpy as np
    import metamathpy.setmm as ms
    import metamathpy.database as md
    import metamathpy.proof as mp

    db = ms.load_pl()
    # db = ms.load_all()
    ph = prefix_hash(db)

    # find longest key
    keys = list(ph.keys())
    lens = list(map(len,keys))
    idx = np.argmax(lens)
    print(lens[idx], keys[idx])

    # input('.')

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

    for lead in sorted(leads.keys()):
        print(lead, len(leads[lead]))

    for key in leads[70]: print(key)

    # consequent = md.Statement("test", "$p", "wff ( ph -> ( ph -> ph ) )".split(" "), ())
    # essentials = []
    # # floatings = [md.Statement("test2", "$f", "wff ph".split(" "), ())]
    # floatings = [db.rules["wph"].consequent]
    # disjoint = set()
    # variables = {"wph"}
    # prove_rule = md.Rule(consequent, essentials, floatings, disjoint, variables)
    # prove_rule.finalize()
    # print(prove_rule)

    # # # check known proof
    # # known_proof = "wph wph wph wi wi".split(" ")
    # # prove_rule.consequent = md.Statement("test", "$p", "wff ( ph -> ( ph -> ph ) )".split(" "), known_proof)
    # # root, steps = mp.verify_normal_proof(db, prove_rule)
    # # print(root)

    # consequent = md.Statement("test", "$p", "wff ph".split(" "), ())
    # essentials = []
    # # floatings = [md.Statement("test2", "$f", "wff ph".split(" "), ())]
    # floatings = [db.rules["wph"].consequent]
    # disjoint = set()
    # variables = {"wph"}
    # prove_rule = md.Rule(consequent, essentials, floatings, disjoint, variables)
    # prove_rule.finalize()
    # print(prove_rule)

    # # check known proof
    # known_proof = "wph".split(" ")
    # prove_rule.consequent = md.Statement("test", "$p", consequent.tokens, known_proof)
    # root, steps = mp.verify_normal_proof(db, prove_rule)
    # print(root)

    consequent = md.Statement("test", "$p", "wff ( ph -> ph )".split(" "), ())
    essentials = []
    # floatings = [md.Statement("test2", "$f", "wff ph".split(" "), ())]
    floatings = [db.rules["wph"].consequent]
    disjoint = set()
    variables = {"wph"}
    prove_rule = md.Rule(consequent, essentials, floatings, disjoint, variables)
    prove_rule.finalize()
    print(prove_rule)

    # check known proof
    known_proof = "wph wph wi".split(" ")
    prove_rule.consequent = md.Statement("test", "$p", consequent.tokens, known_proof)
    root, steps = mp.verify_normal_proof(db, prove_rule)
    print(root)

    # premises = ["wph"]
    premises = ["wph", "wi"] # or all labels up to prove_label

    # prefix proof search
    # want something like partial proof steps?
    potential_rules = list(premises)
    for t in range(1, len(consequent.tokens)+1):
        for rule_label in list(potential_rules):
            rule_tokens = db.rules[rule_label].consequent.tokens
            if rule_tokens[:t] != consequent.tokens[:t]:
                if rule_tokens[t-1] in db.rules[rule_label].variables:
                    # set up recursive proof
                    pass
                else:
                    potential_rules.remove(rule_label)
        print(t, consequent.tokens[:t], potential_rules)
        if len(potential_rules) == 0: break

    if len(potential_rules) > 0:
        print("potential proof with", potential_rules)
    else:
        print("no matching rules")

