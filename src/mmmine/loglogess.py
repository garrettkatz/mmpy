import numpy as np
import metamathpy.setmm as ms
import matplotlib.pyplot as pt

db = ms.load_pl()
# db = ms.load_all()

# number of essentials for each rule
less = [len(rule.essentials) for rule in db.rules.values()]

# histogram bins
bins = np.arange(max(less)+1)+.5 # uniform buckets
# bins = # log scale buckets

hist, _ = np.histogram(less, bins)

pt.bar(bins[1:]+.5, hist, align='center')
pt.xscale('log')
pt.yscale('log')
pt.show()

