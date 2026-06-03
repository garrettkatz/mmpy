import src.metamathpy.setmm as ms

db = ms.load_pl()
tcs = ("wff", "|-")
counts = {tc: [] for tc in tcs}
for rule in db.rules.values():
    counts[rule.consequent.tokens[0]].append(len(rule.essentials))

import matplotlib.pyplot as pt
for i,tc in enumerate(tcs):
    pt.subplot(1,2,i+1)
    pt.hist(counts[tc])
    pt.title(tc)
pt.show()

