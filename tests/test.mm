$c ( ) > ~ : wff $.
$v P Q R $.
wp $f wff P $.
wq $f wff Q $.
wr $f wff R $.
wi $a wff ( P > Q ) $.
wn $a wff ~ P $.

$( Three axioms of propositional logic from Margaris $)

ax1 $a : ( P > ( Q > P ) ) $.

ax2 $a : ( ( P > ( Q > R ) ) > ( ( P > Q ) > ( P > R ) ) ) $.

ax3 $a : ( ( ~ P > ~ Q ) > ( Q > P ) ) $.

$( One inference rule: modus ponens $)

${
    maj $e : ( P > Q ) $.
    min $e : P $.
$}

$( inference versions of axioms $)
${
    a1i.1 $e : P $.
    a1i   $p : ( Q > P ) $=
      wp wq wp wi wp wq ax1 a1i.1 axm $.
$}

$( inference versions of axioms $)
${
    a2i.1 $e : ( P > ( Q > R ) ) $.
    a2i   $p : ( ( P > Q ) > ( P > R ) ) $=
      wp wq wr wi wi wp wq wi wp wr wi wi wp wq wr ax2 a2i.1 axm $.
$}

$( deduction version of inference rule $)
$( Hint: a2i has a match $)
${
    mpd.maj $e : ( P > ( Q > R ) ) $.
    mpd $p : ( P > R ) $=
      wp wq wi wp wr wi wp wq wr mpd.maj a2i mpd.min axm $.
$}

$( law of syllogism $)
${
    syl.1 $e : ( P > Q ) $.
    syl $p : ( P > R ) $=
      wp wq wr wq wr wi wp syl.2 a1i syl.1 mpd $.
$}