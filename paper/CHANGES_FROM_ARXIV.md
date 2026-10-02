# Differences from the arXiv version

The formalization follows [`manuscript.tex`](manuscript.tex), with the five
corrections listed in Part 2.  That file is not the text of
[arXiv:2609.07621v1](https://arxiv.org/abs/2609.07621v1): it is a different
text of the same paper, with the same main theorems but a different proof of
the frequency bound.  The arXiv source will be replaced.  The unmodified arXiv
source is [`arxiv/`](arxiv/): `main.tex`, its bibliography `main.bbl` and the
figure `figures/fig_paths.pdf`, byte for byte as served by arXiv.  Part 1
compares the two texts result by result.  Part 2 lists every change made to
`manuscript.tex`.  Line numbers refer to `manuscript.tex` and to
`arxiv/main.tex`.

## Part 1. The arXiv text and the formalized text

The arXiv text rewrites the introduction and Sections 2 to 6, so a line diff
of the two files is not informative.  The table lists every numbered result
of either text.

| arXiv:2609.07621v1 | `manuscript.tex` | Relation |
| --- | --- | --- |
| Theorem 1.1, `thm:main`, lines 167-172 | Theorem 1.1, `thm:main`, lines 192-198 | same statement |
| Theorem 1.2, `thm:annealed`, lines 180-186 | Theorem 1.2, `thm:annealed`, lines 207-214 | different constant, see 1.1 |
| Proposition 2.1, `prop:generator`, lines 486-505 | Proposition 2.1, `prop:generator`, lines 576-597 | same statement |
| Lemma 2.2, `lem:variational-bound`, (14), lines 530-535 | (15), `eq:var`, lines 626-638 | see 1.2 |
| Lemma 3.1, `lem:raise`, lines 634-646 | Lemma 5.1, `lem:raise`, lines 1179-1191 | see 1.3 |
| Lemma 3.2, `lem:formulas`, lines 719-737 | Lemma 3.1, `lem:formulas`, lines 827-841 | same formulas |
| Lemma 4.1, `lem:parity`, lines 791-805 | none | see 1.4 |
| Lemma 5.1, `lem:effective-energy`, lines 951-962 | none | see 1.4 |
| Proposition 6.1, `prop:frequency`, lines 1070-1079 | Proposition 2.2, `prop:frequency`, lines 644-661 | different statements, see 1.4 |
| Proposition 6.2, `prop:time`, lines 1141-1151 | none | see 1.5 |
| none | Lemma 4.1, `lem:onecoin`; Proposition 4.2, `prop:key`; Lemmas 5.2 to 5.4, `lem:four`, `lem:distinct`, `lem:correction-calculation` | see 1.4 |
| Problems 7.1 to 7.3 | Problems 6.1 to 6.4 | open questions, see 1.5 |

### 1.1 The constant in Theorem 1.2

arXiv, lines 181-184:

> For every $\lambda\in(0,1]$,
> $\int_0^\infty e^{-\lambda t}\overline p_t(0,0)\,dt\leq2048$,

`manuscript.tex`, lines 208-212:

> There is a constant $C<\infty$ with
> $\int_0^\infty e^{-\lambda t}\overline p_t(0,0)\,dt\leq C$ for all
> $\lambda\in(0,1]$,

The formalized statement `Manhattan.Frozen.Main.theorem_1_2` is the second
one: the constant is existential.  The numeral $2048$ is not formalized.  For
the undamped integral the development proves
$\int_0^\infty\overline p_t(0,0)\,dt\leq2.75\cdot10^8$
(`Manhattan.Paper.Constant.annealed_green_le_numeral`).  The same applies to
the numeral $2048$ in Proposition 6.1 and to the numeral $16$ in Lemma 5.1 of
the arXiv text; the formalization proves both statements with an unspecified
constant, and the constant of Lemma 5.1 below $670$
(`Manhattan.V4.v4ConstantSplit_lt`).  Consequently the sentence of the arXiv
Section 1.5, lines 432-434, "Every theorem, lemma and proposition of this
paper has been formalized", holds for Theorem 1.2, Lemma 5.1 and
Proposition 6.1 only with their numerals replaced by a constant.

### 1.2 The variational bound

arXiv Lemma 2.2 asserts $0\leq r_\lambda(p)\leq\|g\|_{+}^2+\|1-A_pg\|_{-}^2$
for every $g\in L^2(\mathbb P)$ and proves it by weighted Cauchy-Schwarz.
`manuscript.tex` (15) asserts that $r_\lambda(p)$ equals the infimum of the
right side over $g$, citing Theorem 4.1 of Komorowski, Landim and Olla, and
uses only the resulting upper bound.  The formalization proves the upper bound
(`Manhattan.Frozen.Operator.resolventQuadratic_le`) and, for the arXiv form,
both inequalities (`Manhattan.Certificate.variational_bound`).  The equality
in (15) is not formalized.

### 1.3 The commutation clause of Lemma 3.1 (arXiv) and Lemma 5.1 (`manuscript.tex`)

arXiv, lines 644-645: "$\Pi_n$ commutes with every bounded multiplier that is a
function of $P$", proved by approximation with trigonometric polynomials and
the spectral calculus.  `manuscript.tex`, line 1190: "$\Pi_n$ commutes with
every continuous multiplier that is a function of $P$", with the proof of
correction 5 below.  The multipliers used in either text are continuous.

### 1.4 The test function and the frequency bound

The two texts bound $r_\lambda(p)$ by different test functions.
In `manuscript.tex` the degree-one coefficient is the cutoff
$f_p(r)=-i\,\mathrm{sgn}(\sin p_1)\mathbf 1_I(r)/\sin r$ of (33), Lemma 4.1
estimates it, and Proposition 4.2 builds the degree-three coefficient by the
rank-one minimization (34); Lemmas 5.2 to 5.4 supply the Fourier-Walsh
estimates.  Proposition 2.2 then states: there are $r_0\in(0,1)$ and
$C<\infty$ and, for each $\lambda\in(0,1]$ and $p\in\mathbb T^2$, a function
$g_{\lambda,p}$ with
$\|g_{\lambda,p}\|_{+}^2+\|1-A_pg_{\lambda,p}\|_{-}^2\leq
C\min\{1/(\lambda+\theta(p)),\,1/(a(p)^2L_\lambda(p)^{3/2})\}$, where
$L_\lambda(p)=1+\log_+(r_0/(\sqrt\lambda+a(p)))$.

In the arXiv text one real even function $\varphi$ determines both parts of
the test function (Lemma 4.1, the parity construction), Lemma 5.1 bounds the
resulting quadratic functional through the weight $q$, and Proposition 6.1
states $r_\lambda(p)\leq2048/(\lambda+a(p)^2[1+\log_+(1/(\sqrt\lambda+a(p)))]^{3/2})$.

Both texts obtain the logarithmic gain with exponent $3/2$ and deduce
Theorem 1.2 from it.  The manifest of this repository certifies the route of
`manuscript.tex`.  The arXiv route is formalized separately in
`Manhattan/V4/`, which proves Theorem 1.1 a second time (`Manhattan.V4.theorem_1_1_v4`)
and the arXiv Lemma 5.1 and Proposition 6.1 with unspecified constants, as
described in 1.1.  [`../VERIFICATION.md`](../VERIFICATION.md) compares those
statements with the arXiv text one by one.

### 1.5 Results without a counterpart

Proposition 6.2 of the arXiv text, the heat-kernel bound $p^\omega_t(x,y)\leq
2/(t+2)$ and the bound on the time derivative of $\overline p_t(0,0)$, has no
counterpart in `manuscript.tex`; it is formalized in `Manhattan/Paper/`.  The
open questions differ: `manuscript.tex` has a fourth problem, `prob:degrees`,
and the arXiv Problem 7.3 asserts that a random shift of the alternating
environment gives a stationary ergodic law under which the walk is recurrent,
which is formalized in `Manhattan/Paper/Ergodic/`.  The introductions differ
in wording and organization and carry no further mathematical statement.

## Part 2. Corrections to `manuscript.tex`

### Correction 1. The continuous-time walk (Section 1.1, lines 203-204)

arXiv, lines 174-176:

> We prove the above theorem by analyzing a continuous time version of the
> walk, which jumps across each of its two outgoing edges at rate $1$.
> Write $p^\omega_t(z,z')$ for its transition probabilities

Corrected:

> Write $p^\omega_t(z,z')$ for its transition probabilities.  The jump times
> form a rate-two Poisson process independent of the jump chain, so
> $p^\omega_t(z,z')=\sum_{n\geq0}e^{-2t}(2t)^np^\omega_n(z,z')/n!$.

The continuous-time transition probabilities were used without a formula that
identifies them.  The formalization defines them by this Poisson
subordination of the discrete kernel, and the proof of Theorem 1.1 uses the
same identity.

### Correction 2. Completeness of the Walsh products (Section 3, lines 712-713)

arXiv, lines 571-573:

> Taking conditional expectations onto increasing finite sets that exhaust
> all lines and applying $L^2$ martingale convergence gives the
> Fourier--Walsh basis of $L^2(\mathbb P)$.

Corrected:

> Enumerate the countably many line signs.  Conditional expectation onto the
> first $N$ signs and $L^2$ martingale convergence as $N\to\infty$ extend this
> basis to $L^2(\mathbb P)$

Martingale convergence identifies the limit only when the finite sets of signs
exhaust all lines; the enumeration supplies such a filtration.

### Correction 3. The coefficient of an element of $\mathcal H_n$ (Section 3.1, line 728)

arXiv, lines 586-587:

> The sum converges in $L^2(\mathbb P)$ and runs over ordered line indices;
> $f$ vanishes when two line indices coincide.

Corrected:

> where the sum runs over ordered $n$-tuples of line indices and $f$ vanishes
> when two line indices coincide.

The factor $n!$ in the isometry (17), and the normalizing factors $\sqrt2$, $2$
and $\sqrt{18}$ of Section 3.4, hold for the sum over ordered tuples; over
unordered sets of line indices the factor would be $1$.

### Correction 4. The rank-one minimization (Section 4.2, lines 966-970, equation (34))

The arXiv text has no counterpart; its test function does not use this
minimization.

Corrected hypotheses and domain:

> If $B>0$ and $M>0$ on a measurable set $J$ with $\int_J dm/M<\infty$, if
> $\eta,w\in\mathbb C$, [...] then, with the infimum over measurable $u$ such
> that $\int_J|u|\,dm$ and $\int_JM|u|^2\,dm$ are finite,

The formula $\inf_u\{\cdots\}=|w|^2/(B+\sigma)$ needs $\sigma<\infty$, which
is the integrability of $1/M$, and needs a class of functions over which the
infimum is taken.  With both stated, the minimizer
$u=\overline\eta w/[M(B+\sigma)]$ belongs to the class and attains the value
(`Manhattan.Estimates.rankOneMinimizationClaim_proved`).  In the application
$J$ is an interval on which $M\geq c|\alpha|$ with $\alpha$ bounded away from
zero, so the hypothesis holds.

### Correction 5. Commutation of $\Pi_n$ with multipliers (Lemma 5.1, line 1190, and its proof, lines 1233-1235)

arXiv, lines 644-645 and 667-670:

> $\Pi_n$ commutes with every bounded multiplier that is a function of $P$.
>
> Simultaneous translations preserve distinctness, so $\Pi_n$ commutes with
> their multipliers.  Uniform approximation by trigonometric polynomials gives
> commutation with continuous functions of $P$ in operator norm; spectral
> calculus extends this to bounded Borel functions of $P$.

Corrected statement: "$\Pi_n$ commutes with every continuous multiplier that
is a function of $P$."  Corrected proof:

> For $y\in\mathbb Z^2$, multiplication by $e^{iy\cdot P}$ is a constant
> multiple of the simultaneous translation of all line indices by $y$.  Such
> translations preserve distinctness, so $\Pi_n$ commutes with them.  A
> continuous multiplier that is a function of $P$ is a uniform limit of
> linear combinations of these translations, so $\Pi_n$ commutes with the
> multiplier.

The proof asserted that every multiplier depending on $P$ is a linear
combination of translations.  That describes only the trigonometric
polynomials in $P$.  It covers $\lambda+\theta(P)$ but not the multiplier $M$
of (35), whose terms $2|\sin(P_i/2)|$ have infinitely many nonzero Fourier
coefficients.  Every multiplier to which the lemma is applied, namely
$\lambda+\theta(P)$, $M$ and their reciprocals, is continuous, so the
statement restricted to continuous multipliers suffices, and uniform
approximation proves it.
