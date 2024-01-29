## metamath-py

A python interface to [Metamath](https://us.metamath.org/)

# install

`$ pip install --user metamath-py`

# basic usage

Loading a .mm file (may take a minute for large databases):

```
>>> import metamathpy as mm
>>> import os
>>> db = mm.database.parse(os.path.join(os.environ["HOME"], "metamath", "set.mm"))
```

Access any statement by its label, for example the major premise of the modus ponens axiom:

```
>>> db.statements['maj'] # uses a named tuple data structure
Statement(label='maj', tag='$e', tokens=['|-', '(', 'ph', '->', 'ps', ')'], proof=[])
>>> " ".join(db.statements['maj'].tokens) # more human readable
|- ( ph -> ps )
```

Access any inference rule by the label of its consequent:

```
>>> db.rules['ax-mp']
<metamathpy.database.Rule object at 0x7fe21f099370>
>>> db.rules['ax-mp'].print() # pretty-print it
ax-mp $a |- ps $.
disjoint variable sets: set()
  wph $f wff ph $.
  wps $f wff ps $.
  min $e |- ph $.
  maj $e |- ( ph -> ps ) $.
```

It has fields for the consequent and hypotheses

```
>>> db.rules['ax-mp'].consequent
Statement(label='ax-mp', tag='$a', tokens=['|-', 'ps'], proof=[])
>>> db.rules['ax-mp'].essentials
[Statement(label='min', tag='$e', tokens=['|-', 'ph'], proof=[]), Statement(label='maj', tag='$e', tokens=['|-', '(', 'ph', '->', 'ps', ')'], proof=[])]
```

Verify a proof to construct the proof tree in memory:

```
>>> import metamathpy.proof as mp
>>> root, steps = mp.verify_proof(db, db.rules['a1i'])
```

`root` is a ProofStep object representing the final step of the proof; it is the root of a proof tree.  The nodes of that tree are other ProofStep objects and the values in the `steps` dictionary; the corresponding key is the step's conclusion.  ProofSteps display like strings but have the following attributes:

```
>>> root
ax-mp |- ( ps -> ph )
>>> root.conclusion # the conclusion of this step of the proof
('|-', '(', 'ps', '->', 'ph', ')')
>>> root.rule # the rule used to justify this step
<metamathpy.database.Rule object at 0x7fe21f099370>
>>> root.rule.consequent # in this case it is ax-mp
Statement(label='ax-mp', tag='$a', tokens=['|-', 'ps'], proof=[])
>>> root.substitution # the variable substitution that unified ax-mp with this step
{'ph': ('ph',), 'ps': ('(', 'ps', '->', 'ph', ')')}
>>> root.dependencies # the other steps on which this one was justified
{'wph': wph wff ph, 'wps': wi wff ( ps -> ph ), 'min': a1i.1 |- ph, 'maj': ax-1 |- ( ph -> ( ps -> ph ) )}

The dependencies are a dictionary where keys are the labels of the rule's hypotheses, and values are the other proof steps that satisfied those hypotheses.  These can be thought of as the children of the root in the proof tree.


