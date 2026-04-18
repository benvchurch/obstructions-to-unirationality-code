# From bitangents to genus-2 Pryms: the math behind the pipeline

This note documents the algebraic geometry implemented in
`steiner_pipeline.m` (driven by `tests.m`), the Hensel-lift experiment
`hensel_decomp.m`, and `check_isogeny_correct.m`. It explains how the 28
bitangents of a smooth plane
quartic, the 63 Steiner complexes, the quartic decomposition formula
$aF = L_iL_jL_kL_l + bQ^2$, and the determinantal pencil that produces
genus-2 curves all fit together — and why the resulting genus-2 curves are
the Prym varieties of the étale double covers of $C$.

Throughout, $C \subset \mathbb P^2$ is a smooth plane quartic over a field
$k$ of characteristic $\ne 2$, $g(C) = 3$, $K_C = \mathcal O_C(1)$, and
$J = \operatorname{Jac}(C)$.

---

## 1. Theta characteristics on a curve of genus 3

A **theta characteristic** on a smooth projective curve $C$ of genus $g$ is a
line bundle $\kappa \in \operatorname{Pic}(C)$ satisfying
$$ \kappa^{\otimes 2} \;\cong\; K_C. $$

The set $\Theta(C)$ of theta characteristics is a torsor under
$J[2] = \operatorname{Pic}^0(C)[2] \cong (\mathbb Z/2)^{2g}$:
once any one $\kappa_0$ is fixed, every theta characteristic is of the form
$\kappa_0 + \eta$ for a unique $\eta \in J[2]$. So
$|\Theta(C)| = 2^{2g}$ — for $g=3$, that's $64$.

Each theta characteristic has a $\mathbb Z/2$-valued **parity**
$$ \mathrm{par}(\kappa) \;:=\; h^0(C, \kappa) \bmod 2, $$
shown by Atiyah and Mumford to be a deformation invariant
[Atiyah 1971, Mumford 1971]. The number of even and odd theta characteristics
is given by
$$
N_+ = 2^{g-1}\bigl(2^g + 1\bigr), \qquad
N_- = 2^{g-1}\bigl(2^g - 1\bigr).
$$
For $g=3$: $N_+ = 36$ even and $N_- = 28$ odd. The conceptual reason for
this split is the **Arf invariant** of a quadratic refinement of the Weil
pairing — the topic of §2.

---

## 2. Symplectic structure on $J[2]$ and the Arf invariant

### 2.1 The Weil pairing makes $J[2]$ into a symplectic $\mathbb F_2$-space

The Weil pairing on 2-torsion,
$$ e_2 : J[2] \times J[2] \;\longrightarrow\; \mu_2 \;\cong\; \mathbb F_2, $$
is a non-degenerate alternating bilinear form. For a curve of genus $g$,
$J[2] \cong \mathbb F_2^{2g}$, and $(J[2], e_2)$ admits a **symplectic basis**
$e_1, f_1, \ldots, e_g, f_g$ with
$$ e_2(e_i, f_j) = \delta_{ij}, \qquad e_2(e_i, e_j) = e_2(f_i, f_j) = 0. $$
The full symmetry group is $\operatorname{Sp}(2g, \mathbb F_2)$, of order
$2^{g^2}\prod_{k=1}^{g}(2^{2k} - 1)$. For $g = 3$ this gives
$|\operatorname{Sp}(6, \mathbb F_2)| = 1\,451\,520$.

A subtlety worth flagging up front: the 2-torsion *subgroup* $J[2]$ and the
quotient $J/2J$ are abstractly isomorphic (both are $\mathbb F_2^{2g}$ for $J$
finite over the algebraic closure), but they are **dual** as Galois modules
over a non-algebraically-closed field (Cartier duality). When you compute on
the Magma side, picking out the order-2 element of each cyclic factor of
$J(\mathbb F_p)$ gives the $J[2]$-class; reducing coordinates mod 2 gives the
$J/2J$-class. These two prescriptions agree as functions of the abstract
group, but **differ** as functions of the actual Magma class group whenever
$J(\mathbb F_p)$ has a $\mathbb Z/2^k\mathbb Z$ factor with $k \ge 2$. The
pipeline below systematically uses $J[2]$ (the function `ClassJ2` in the
script).

### 2.2 Quadratic refinements

A **quadratic refinement** of $e_2$ is a function $q : J[2] \to \mathbb F_2$
satisfying
$$ q(x + y) \;=\; q(x) \;+\; q(y) \;+\; e_2(x, y) \qquad \forall\, x, y \in J[2]. $$
Equivalently, $q$ is a "set-theoretic" lift of $e_2$ to a function on $J[2]$
itself rather than on $J[2] \otimes J[2]$. The set of quadratic refinements
forms a torsor under the additive group of *linear* forms $J[2] \to \mathbb F_2$,
which via $e_2$ is identified with $J[2]$ itself; in particular there are
exactly $2^{2g}$ quadratic refinements.

The **Arf invariant** of $q$ is the element of $\mathbb F_2$ defined in any
symplectic basis $(e_i, f_i)$ by
$$ \operatorname{Arf}(q) \;:=\; \sum_{i=1}^{g} q(e_i)\,q(f_i) \;\in\; \mathbb F_2; $$
the sum is independent of the chosen symplectic basis. Equivalently, the Arf
invariant is the **"majority bit"** of $q$ in the following sense:
$$
|q^{-1}(0)| \;=\; 2^{2g-1} \;+\; 2^{g-1}(-1)^{\operatorname{Arf}(q)},
\qquad
|q^{-1}(1)| \;=\; 2^{2g-1} \;-\; 2^{g-1}(-1)^{\operatorname{Arf}(q)}.
$$
A refinement is called **even** if $\operatorname{Arf}(q) = 0$ and **odd** if
$\operatorname{Arf}(q) = 1$. From the formula above, the number of even
refinements is $2^{g-1}(2^g + 1)$ and the number of odd is $2^{g-1}(2^g - 1)$
— exactly $N_+$ and $N_-$ from §1.

Arf introduced this invariant in [Arf 1941] precisely to classify quadratic
forms over $\mathbb F_2$. The pair $(\operatorname{rk}, \operatorname{Arf})$
is a complete invariant of a non-degenerate quadratic form over $\mathbb F_2$,
and the Arf invariant is the unique non-trivial $\operatorname{Sp}(2g, \mathbb F_2)$-invariant
of a quadratic refinement of a fixed symplectic form.

### 2.3 Riemann–Mumford: $\Theta(C) \leftrightarrow$ quadratic refinements

The numerical coincidence between $|\Theta_\pm|$ and the count of
even/odd refinements is no accident:

**Theorem (Riemann–Mumford).** *Let $C$ be a smooth projective curve over an
algebraically closed field of characteristic $\ne 2$. There is a canonical
bijection*
$$ \Theta(C) \;\xrightarrow{\;\sim\;}\; \bigl\{\text{quadratic refinements of } e_2 \text{ on } J(C)[2]\bigr\},
   \qquad \kappa \;\longmapsto\; q_\kappa, $$
*defined by*
$$ q_\kappa(\eta) \;=\; h^0(C, \kappa + \eta) \;+\; h^0(C, \kappa) \pmod 2. $$
*This bijection intertwines parity with the Arf invariant:*
$$ \operatorname{par}(\kappa) \;=\; h^0(C, \kappa) \bmod 2 \;=\; \operatorname{Arf}(q_\kappa). $$

In particular, the Arf-invariant counting formula recovers
$N_\pm = 2^{g-1}(2^g \pm 1)$ as a *conceptual* fact, not a coincidence.

References: [Riemann 1876] (the original via theta function characteristics),
[Mumford 1971, Theorem 1], [Atiyah 1971, §3], [Dolgachev 2012, §5.2].

### 2.4 Translation behaviour: when does parity flip?

Two consequences of Riemann–Mumford structure the rest of the paper:

**(Parity flip rule.)** If $\kappa \in \Theta(C)$ and $\eta \in J[2]$, then
$$ \operatorname{par}(\kappa + \eta) \;-\; \operatorname{par}(\kappa) \;=\; q_\kappa(\eta) \pmod 2. $$
That is, translating by $\eta$ flips parity iff $\eta$ is "$q_\kappa$-odd."

**(Abstract even/odd dichotomy on $J[2] \setminus \{0\}$.)** Fix any even
theta characteristic $\kappa_0$, and use it to identify $\Theta(C)$ with $J[2]$
via $\eta \mapsto \kappa_0 + \eta$. Then
$$ J[2] \setminus \{0\} \;=\; \underbrace{\{\eta : q_{\kappa_0}(\eta) = 0\}}_{|.|\,=\,2^{2g-1} - 1} \;\sqcup\; \underbrace{\{\eta : q_{\kappa_0}(\eta) = 1\}}_{|.|\,=\,2^{2g-1}}. $$
For $g = 3$ this is the famous decomposition
$$ 63 \;=\; 35 \;+\; 28, $$
where the **35** "even" classes correspond to even theta characteristics
distinct from $\kappa_0$ and the **28** "odd" classes correspond to odd theta
characteristics (= bitangents, by §3).

The partition into 35 and 28 is invariant under
$\operatorname{Sp}(6, \mathbb F_2)$ — i.e. it does *not* depend on the choice
of even base $\kappa_0$, although the labelling of individual elements does.
Classically, the 35 even nonzero classes are called **syzygetic** and the 28
odd ones are called **azygetic** (Salmon's terminology, see
[Salmon 1879, §219]; modern accounts in [Dolgachev–Ortland 1988, Ch. IX] and
[Dolgachev 2012, §5.4]).

### 2.5 The Klein quartic case

For the Klein quartic, the geometric automorphism group $\operatorname{PSL}(2,7)$
embeds in $\operatorname{Sp}(6, \mathbb F_2)$ and acts on $J[2] \setminus \{0\}$.
The orbit decomposition respects the Arf decomposition $63 = 35 + 28$:

| Orbit size | Arf type of $\eta$ | Classical name |
| --- | --- | --- |
| 28 | odd | azygetic / "bitangent class" |
| 21 | even | syzygetic |
| 7 + 7 (Galois-conjugate pair) | even | syzygetic |

Totals: $28 + 21 + 7 + 7 = 63$, with $35 = 21 + 7 + 7$ even and $28$ odd. ✓

This is the orbit data that the Steiner-pipeline scripts process for the
Klein quartic and its twist `C_twist` (see `klein_steiner_pryms.md` in the
project memory for the corresponding j-invariant data).

References for this section: [Arf 1941], [Mumford 1971, §1],
[Dolgachev 2012, §5.2 and §5.4], [Dolgachev–Ortland 1988, Ch. IX],
[Birman–Craggs 1978] for the topological perspective.

---

## 3. Bitangents = odd theta characteristics

For a smooth plane quartic $C \subset \mathbb P^2$, the canonical bundle is
$K_C = \mathcal O_C(1)$, so canonical divisors are cut out by lines.

A **bitangent** line $L \subset \mathbb P^2$ to $C$ is one whose intersection
divisor on $C$ is a sum of two double points,
$$ L \cdot C \;=\; 2P + 2Q $$
(or $4P$ for a hyperflex). The line gives a section of $\mathcal O_C(1) = K_C$
vanishing on $2P + 2Q$, so
$$ K_C \;\sim\; 2(P+Q), $$
which means $D := P + Q$ (an effective degree-2 divisor) defines a theta
characteristic
$$ \kappa_L := \mathcal O_C(P+Q) \in \Theta(C). $$

This $\kappa_L$ is **odd**: it has the obvious nonzero section vanishing on
$P+Q$, so $h^0(\kappa_L) \ge 1$. By Riemann–Roch and Clifford,
$h^0(\kappa_L) = 1$ generically, and $\operatorname{Arf}(q_{\kappa_L}) = 1$.

**Theorem (Aronhold, Cayley, Salmon).** *The map $L \mapsto \kappa_L$ is a
bijection between bitangents to $C$ and odd theta characteristics.* In
particular, a smooth plane quartic has exactly $N_- = 28$ bitangents.

References: [Salmon 1879, §216], [Dolgachev 2012, §6.1].

In the code: `FindBitangentsFp` searches for lines $L = [A:B:C]$ over
$\mathbb F_p$ such that the restriction of $F$ to $L$ is a perfect square as
a polynomial in the line parameter. Over a number field, the script builds
the **tangency ideal**
$$ I_{\mathrm{tg}} = \bigl\langle\,
   \text{coefficient}_t F(t,1,-at-b) \;-\; \text{coefficient}_t (\alpha t^2 + \beta t + \gamma)^2
   \,\bigr\rangle \subset \mathbb Q[a,b,\alpha,\beta,\gamma],
$$
eliminates $\alpha,\beta,\gamma$, and factors the resulting univariate in $b$
(then $a$) to find the bitangent coordinates over the splitting field. Three
charts are used to cover lines through $[1\!:\!0\!:\!0]$ and the line
$\{x = 0\}$.

---

## 4. Steiner complexes from $J[2]$

Fix two odd theta characteristics $\kappa_i, \kappa_j \in \Theta_-$
corresponding to bitangents $L_i, L_j$. Their difference is a 2-torsion
element
$$ \eta_{ij} \;:=\; \kappa_i - \kappa_j \;\in\; J[2]. $$
For a fixed nonzero $\eta \in J[2]$, the set
$$ S_\eta \;:=\; \bigl\{\, \{i,j\} \;:\; \kappa_i - \kappa_j = \eta \,\bigr\} $$
is the **Steiner complex** associated to $\eta$.

**Counting.** Every unordered pair of distinct bitangents gives a unique
nonzero $\eta \in J[2]$ as its difference, and there are $\binom{28}{2} = 378$
such pairs and $|J[2] \setminus \{0\}| = 63$ classes. By a uniform counting
argument (the action of $J[2]$ on pairs is "balanced" under the symplectic
action of the geometric monodromy), each nonzero $\eta$ appears the same
number of times:
$$ |S_\eta| \;=\; \frac{\binom{N_-}{2}}{|J[2] \setminus \{0\}|}
   \;=\; \frac{\binom{28}{2}}{63} \;=\; 6 \quad\text{(for } g = 3\text{).} $$
So **each Steiner complex consists of exactly 6 disjoint pairs of bitangents,
i.e. 12 bitangents in total**, and there are $63$ such complexes. The
remaining $28 - 12 = 16$ bitangents are not involved in any given $S_\eta$.
Double-counting incidences via $63 \cdot 12 = 28 \cdot k$ gives $k = 27$:
**each bitangent appears in exactly 27 Steiner complexes** (one for each of
its $\binom{28}{1} - 1 = 27$ partners, since each unordered pair of
bitangents is contained in a unique $S_\eta$, namely the one indexed by their
difference).

References: [Dolgachev 2012, §6.1.5], [Salmon 1879, §219],
[Dolgachev–Ortland 1988, Ch. IX].

The number $63 \cdot 6 = 378 = \binom{28}{2}$ accounts for every unordered
pair of bitangents. The combinatorics encodes the symmetric structure of the
**Cayley quartic** or "Aronhold set": modulo the symplectic group
$\operatorname{Sp}(6, \mathbb F_2)$, this is the orbit data of the natural
action on the 28 odd characteristics.

### 4.1 Computing $\eta_{ij}$ in Magma: the $J[2]$ class, not $J/2J$

In the code: the function field of $C$ over $\mathbb F_p$ is constructed in
`steiner_pipeline.m` STEP 1. For each bitangent line $L_i$, the script forms the
function $L_i / L_{\mathrm{ref}} \in k(C)$, takes
$$ \tfrac12 \operatorname{div}\!\bigl(L_i / L_{\mathrm{ref}}\bigr) \;\in\; \operatorname{Pic}^0(C), $$
which is well-defined exactly because $L_i$ is bitangent (all valuations
even), and recovers the corresponding **$J[2]$ class**
$\eta_i = \kappa_i - \kappa_{\mathrm{ref}}$.

The translation from a class group element to a $J[2]$ element is performed
by the function `ClassJ2`:
```
j2 := [];
for k in [1..#invs] do
    if invs[k] eq 0 then continue; end if;
    if invs[k] mod 2 ne 0 then continue; end if;
    // For Z/nZ (n even), the unique 2-torsion element is n/2.
    // The map a -> (2*a div n) mod 2 sends 0 -> 0 and n/2 -> 1.
    Append(~j2, (2 * coords[k] div invs[k]) mod 2);
end for;
```
This is *not* the same as `ReduceMod2`, which reduces every coordinate of
the class-group element mod 2 — that would give the $J/2J$ class. The two
prescriptions agree for class groups whose finite part is 2-elementary (only
$\mathbb Z/2$ factors), but **differ** when there are $\mathbb Z/4$ or larger
2-power factors. The Steiner pipeline needs the literal 2-torsion *line
bundle*, so `ClassJ2` is the correct primitive.

(Cf. the warning recorded in the project's `MEMORY.md`:
*"`ReduceMod2(cls)` (coordinate mod 2) computes action on $\mathrm{Cl}/2\mathrm{Cl} = J/2J$, NOT $J[2]$."*)

Pairs $\{i,j\}$ are then binned by the $J[2]$ class $\eta_i - \eta_j$ to
recover the 63 complexes (each with 6 pairs, verified by the assertions
`nclasses eq 63` and `s eq 6` in `steiner_pipeline.m`).

### 4.2 Even vs. odd $\eta$, and the parity of the complex

By §2.4, the quadratic refinement $q_{\kappa_0}$ on $J[2]$ partitions the
nonzero classes into 35 **syzygetic** (even, $q = 0$) and 28 **azygetic**
(odd, $q = 1$). The classical Steiner-complex theory of plane quartics
[Salmon 1879] is developed for the syzygetic case: a syzygetic Steiner
complex is the data needed to write the quartic decomposition
$aF = L_iL_jL_kL_l + bQ^2$ of §5.

For a plane quartic with $g=3$, the 28 odd nonzero $\eta$ are in canonical
bijection with the 28 bitangents (via the parity flip rule of §2.4: the
"bitangent class" of a bitangent $L_i$ is $\kappa_i - \kappa_0$). The 35 even
nonzero $\eta$ correspond to the 35 even theta characteristics of the form
$\kappa_0 + \eta$; equivalently, to "Cayley octads" / Aronhold systems of
seven bitangents (see [Dolgachev 2012, Ch. 6]).

For the Klein quartic specifically, the orbit decomposition $28 + 21 + 7 + 7$
under $\operatorname{PSL}(2,7)$ refines this 28+35 split: one orbit of size
28 = the azygetic orbit, three orbits (sizes 21, 7, 7) inside the 35 syzygetic
classes. (See `klein_steiner_pryms.md` in `~/.claude` memory for the orbit
decomposition and j-invariant data on the C_twist case.)

---

## 5. The quartic decomposition formula

Fix a Steiner complex $S_\eta = \bigl\{\{i_1,j_1\}, \ldots, \{i_6,j_6\}\bigr\}$
and pick *two* of its six pairs, say $\{i,j\}$ and $\{k,l\}$. The classical
identity is:

**Theorem.** *There exists a conic $Q \in H^0(\mathbb P^2, \mathcal O(2))$
and scalars $a, b \in k$ (not both zero) such that*
$$ a\,F \;=\; L_i\,L_j\,L_k\,L_l \;+\; b\,Q^2. \tag{$\star$} $$
*The conic $Q$ is the unique (up to scalar) conic in $\mathbb P^2$ that
**passes through** the eight contact points
$\{P_i, P_i', P_j, P_j', P_k, P_k', P_l, P_l'\}$
of the four bitangents $L_i, L_j, L_k, L_l$ (where
$L_m \cdot C = 2 P_m + 2 P_m'$). The intersection $Q \cap C$ is precisely
these eight points, each with multiplicity one — so $Q$ is a conic
**through** the eight contact points, not a conic tangent to $C$ there.*

References: [Salmon 1879, §220], [Dolgachev 2012, Prop. 6.1.7],
[Caporaso–Sernesi 2003] for a modern reconstruction perspective.

The geometric content of $(\star)$ is a divisor identity on $C$. Each
bitangent $L_m$ cuts $C$ in $2(P_m + P_m')$, so
$$
\operatorname{div}(L_iL_jL_kL_l)\big|_C
\;=\; 2\bigl(P_i + P_i' + P_j + P_j' + P_k + P_k' + P_l + P_l'\bigr)
\;\in\; |4 K_C|,
$$
a divisor of degree 16 supported on 8 distinct points, each with
multiplicity 2. Since $aF|_C = 0$, the relation $(\star)$ forces
$\operatorname{div}(Q^2)|_C$ to equal the same divisor, so
$$
\operatorname{div}(Q)\big|_C \;=\; P_i + P_i' + P_j + P_j' + P_k + P_k' + P_l + P_l',
$$
a degree-8 divisor in $|2K_C|$ — exactly the (unique up to scalar) conic
through the 8 contact points, with **multiplicity one at each**. That $Q$
has a double zero on each pair $(P_m, P_m')$ in the expression
$b Q^2 = -L_iL_jL_kL_l$ is an artifact of squaring, not of $Q$ being tangent
to $C$.

In the code, two linear-algebra steps implement this:

1. **`FindConic`** assembles a $12 \times 10$ matrix encoding the conditions
   "the restriction of $Q$ to each $L_m$ is proportional to the contact
   quadratic $h_m$ of $L_m$" for $m \in \{i,j,k,l\}$ (3 conditions per
   line, so 12 rows; 6 unknowns for $Q$ and 4 proportionality constants
   $\lambda_m$, so 10 columns). The kernel is 1-dimensional and gives $Q$.
2. **Quartic decomposition step** then assembles the $3 \times 15$ matrix
   whose rows are the coefficient vectors of $F$, $L_iL_jL_kL_l$, and $Q^2$
   in the basis of degree-4 monomials, and reads off the relation
   $a\,F + (-1)\,L_iL_jL_kL_l + b\,Q^2 = 0$ from the kernel.

For each Steiner complex there are $\binom{6}{2} = 15$ pair-of-pairs, hence
$63 \cdot 15 = 945$ such conics in total. The script verifies them all and
prints `Verified 945 / 945`.

---

## 6. From the decomposition to a $3 \times 3$ symmetric pencil

Rewrite $(\star)$ as
$$ b\,Q^2 \;-\; (-L_iL_j)(L_kL_l) \;=\; a\,F. $$
Set $Q_1 := b\,L_iL_j$, $Q_2 := b\,Q$, $Q_3 := -L_kL_l$ (each a homogeneous
quadratic form, i.e. an element of $\operatorname{Sym}^2 V^*$ with
$V = k^3$). Then
$$ Q_1 Q_3 \;-\; Q_2^2 \;=\; -ab\,F, $$
i.e. $C$ is cut out (up to scalar) by the **discriminant** of the symmetric
matrix
$$
M \;:=\;
\begin{pmatrix}
Q_1 & Q_2 \\
Q_2 & Q_3
\end{pmatrix},
$$
viewing $Q_1, Q_2, Q_3$ as quadratic forms on $\mathbb P^2$. Equivalently,
$C$ is the **degeneracy locus** of the pencil $\{Q_1 + 2tQ_2 + t^2 Q_3\}$
of conics, parametrised by $t \in \mathbb P^1$.

Now upgrade to the level of $3 \times 3$ symmetric matrices on $\mathbb P^2$
itself: write each conic $Q_m$ as a symmetric matrix $M_m \in \mathrm{Sym}^2(k^3)$
of size $3$, and form the matrix-valued polynomial
$$ M(t) \;:=\; M_1 \;+\; 2 t\, M_2 \;+\; t^2 M_3 \;\in\; \mathrm{Mat}_3\bigl(k[t]\bigr). $$

The locus
$$ \widetilde{C} \;:=\; \bigl\{\, (t, [v]) \in \mathbb P^1 \times \mathbb P^2 \;:\; v^\top M(t) v = 0 \,\bigr\} $$
is a $(2,2)$-divisor in $\mathbb P^1 \times \mathbb P^2$; the projection
$\widetilde C \to \mathbb P^1$ is a conic bundle (smooth conics for generic
$t$, degenerating to line pairs when $\det M(t) = 0$).

**Definition.** Set
$$ B \;:=\; \bigl\{\, t \in \mathbb P^1 \;:\; \det M(t) = 0 \,\bigr\}. $$
For generic input, $\det M(t)$ is a polynomial of degree 6, so $|B| = 6$.
The hyperelliptic curve
$$ \mathcal H \;:\; y^2 \;=\; -\det M(t) $$
has 6 Weierstrass points (or 5 + the point at infinity when $\det$ has
degree 5), hence genus
$$ g(\mathcal H) \;=\; \tfrac{6 - 2}{2} \;=\; 2. $$

This is the function `MakeGenus2` (for the $\mathbb F_p$ cross-check) and the
inline determinantal-pencil block inside `TryMakeGenus2` (for the $K$ pipeline)
in `steiner_pipeline.m`.

---

## 7. Why $\mathcal H$ is the Prym variety

For each non-zero $\eta \in J(C)[2]$ there is an associated **étale double
cover** $\pi : D_\eta \to C$, classified by $\eta \in H^1(C, \mathbb Z/2)
\cong J(C)[2]$. By Riemann–Hurwitz,
$$ 2(g_{D_\eta} - 1) \;=\; 2 \cdot 2(g_C - 1) \;=\; 8 \quad \implies \quad g_{D_\eta} = 5. $$
The covering involution $\sigma$ acts on $\operatorname{Jac}(D_\eta)$, and the
**Prym variety** is the connected component of the kernel of the trace map,
$$ P(D_\eta / C) \;:=\; \bigl(\ker \operatorname{Nm}_\pi\bigr)^{0}
   \;\subset\; \operatorname{Jac}(D_\eta). $$
It is a $(g_{D_\eta} - g_C) = 2$-dimensional principally polarized abelian
variety (the principal polarization is *twice* the restriction of the
canonical polarization on $\operatorname{Jac}(D_\eta)$, divided by 2 — this
is the special fact about étale double covers due to Mumford).

References: [Mumford 1974], [Beauville 1977], [Donagi 1992].

For a generic curve of genus $\le 5$, the Prym map
$\mathcal R_g \to \mathcal A_{g-1}$ is dominant; for $g = 3$ the source has
dimension $\dim \mathcal M_3 + 6 = 12$ and the target $\mathcal A_2$ has
dimension $3$, so generic fibres have dimension $9$.

**The decisive theorem** is:

**Theorem (Wirtinger / Recillas / Verra / Dolgachev).** *Let $C \subset \mathbb P^2$
be a smooth plane quartic, $\eta \in J(C)[2] \setminus \{0\}$, and
$\pi : D_\eta \to C$ the corresponding étale double cover. Then
$P(D_\eta / C)$ is the Jacobian of a smooth genus-2 curve $\mathcal H_\eta$,
and $\mathcal H_\eta$ can be realised explicitly as the discriminant curve
$y^2 = -\det M(t)$ of any pencil $M(t)$ of $3 \times 3$ symmetric matrices
constructed from any pair of pairs in the Steiner complex $S_\eta$.*

References: [Wirtinger 1895], [Recillas 1974], [Beauville 1977, §6],
[Verra 1987], [Dolgachev 2012, §5.5].

In other words: **the genus-2 curves produced by `steiner_pipeline.m` are
exactly the 63 Prym varieties** of the étale double
covers of $C$, presented as Jacobians of explicit genus-2 curves. Different
choices of pair-of-pairs within the same Steiner complex give *the same*
genus-2 curve (up to isomorphism), reflecting the well-definedness of the
Prym.

The connection to the user's earlier question: *"the Pryms of the genus-5
étale covers of the Klein quartic"* and *"the j-invariants of the elliptic
factors of the genus-2 curves"* are the same computation viewed through two
lenses.

---

## 8. Splitting the Prym: elliptic factors via the $\mathbb Z/3$ trick

A 2-dimensional ppav $A$ is either irreducible or (2,2)-isogenous to a
product $E_1 \times E_2$ of elliptic curves. When $A = J(\mathcal H)$ for a
genus-2 hyperelliptic curve, one tests for an elliptic decomposition by
looking for an order-3 automorphism of $\mathbb P^1$ that **permutes the 6
Weierstrass points** of $\mathcal H$.

Concretely: an order-3 Möbius transformation has two fixed points and
partitions the remaining points into orbits of size 3. If the 6 Weierstrass
points $\{p_1,\ldots,p_6\}$ split as a single $\mathbb Z/3$-orbit of
length 3 plus another orbit of length 3 (no fixed Weierstrass points),
then this $\mathbb Z/3$ action descends to a degree-3 map
$\mathcal H \to E$ onto an elliptic curve, and the second elliptic factor
$E'$ is the quotient by the genus-2 hyperelliptic involution.

In the script `FindOrbit`, this is implemented as: for each ordered triple
$(p_a, p_b, p_c)$ of Weierstrass points, apply the unique Möbius
transformation sending $(p_a, p_b, p_c) \mapsto (0, 1, \infty)$, then check
whether the images of the remaining three points form a $\mathbb Z/3$-orbit
$\{x, 1 - 1/x, 1/(1-x)\}$ — these are the cyclic permutations of the
generic cross-ratio under the order-3 element of the anharmonic group
$S_3 \subset \mathrm{PGL}_2$ acting on cross-ratios.

When such an $x$ is found, the cross-ratio $\lambda = x$ identifies the
elliptic curve via the standard formula
$$
j(E) \;=\; 256 \cdot \frac{(1 - s(1-s))^3}{s^2 (1-s)^2},
\qquad s \;=\; (1-\lambda)\,\bigl(\lambda + \sqrt{\lambda^2 - \lambda + 1}\,\bigr)^2.
$$
(The intermediate variable $s$ comes from a $2$-isogeny normalisation —
with the square root, the formula returns the j-invariant of one of the two
isogeny factors of the (2,2)-decomposition.)

For the Klein-twist case `C_twist`, this returns the j-invariants documented
in `check_isogeny_correct.m` and in the project memory `klein_steiner_pryms.md`:

| PSL(2,7) orbit on Steiner complexes | Arf type | min poly of $j$ over $\mathbb Q$ | splitting |
| --- | --- | --- | --- |
| size 28 (azygetic, "bitangent class") | odd | $v^2 + 13856v - 26578688$ | $\mathbb Q(\sqrt{7})$, $j = -6928 \pm 3264 \sqrt 7$ |
| size $7+7$ (syzygetic, conjugate pair) | even | $v^4 - 103439 v^3 + 6670405329 v^2 + \cdots$ | irreducible$/\mathbb Q$, splits as $\mathrm{mp}_2 \cdot \mathrm{mp}_3$ over $\mathbb Q(\sqrt{-7})$ |
| size 21 (syzygetic) | even | not separately recorded | re-derive from `steiner_pipeline.m` |

The script `check_isogeny_correct.m` then proves rigorously, via the CM-field
criterion (the squarefree part of $a_p^2 - 4p$ for ordinary reduction), that
the elliptic factors from different PSL(2,7) orbits are not
$\overline{\mathbb Q}$-isogenous, and that none of them is the curve
$E = \texttt{49a1}$ that appears in $J(C_{\mathrm{twist}}) \cong E^3$.

---

## 9. End-to-end pipeline summary

Given a smooth plane quartic $F(x,y,z) \in k[x,y,z]_4$:

All references below are to `steiner_pipeline.m` unless noted otherwise.

| Step | Object | Code | Math |
| --- | --- | --- | --- |
| 0 | reduce mod good prime $p$ | search loop | smoothness check |
| 1 | 28 bitangents over $\mathbb F_p$ (later over $K \supset \mathbb Q$) | `FindBitangentsFp`, tangency ideal + elimination | odd theta characteristics §3 |
| 2 | $63$ Steiner complexes | function-field $J[2]$ classes of $L_i/L_{\mathrm{ref}}$, via `ClassJ2` | Steiner complexes §4 |
| 3 | witnessing conic $Q$ for each pair-of-pairs | $12 \times 10$ linear system (`FindConic`) | conic through 8 contact points §5 |
| 4 | scalars $a, b$ in $aF = L_iL_jL_kL_l + bQ^2$ | nullspace of $3 \times 15$ coefficient matrix | quartic decomposition §5 |
| 5 | symmetric pencil $M(t) = M_1 + 2tM_2 + t^2 M_3$ | `MakeGenus2` / `TryMakeGenus2` | linear system of conics §6 |
| 6 | genus-2 curve $\mathcal H : y^2 = -\det M(t)$ | `HyperellipticCurve` | Prym = Jacobian §7 |
| 7 | Igusa invariants and (when (2,2)-reducible) elliptic factor j-invariants | `IgusaInvariants`, `FindOrbit` | $\mathbb Z/3$ on Weierstrass points §8 |
| 8 | rigorous (non-)isogeny among elliptic factors | `check_isogeny_correct.m` | CM-field criterion (squarefree part of $a_p^2 - 4p$) |

`steiner_pipeline.m` accepts any smooth plane quartic over $\mathbb Q$ via
`tests.m` (edit the `tests` sequence to add a new curve). `hensel_decomp.m` is
a separate standalone Hensel-lift experiment for quadric decompositions
hardcoded to the Klein quartic.

---

## References

- C. Arf, *Untersuchungen über quadratische Formen in Körpern der
  Charakteristik 2 (Teil I)*, J. Reine Angew. Math. **183** (1941), 148–167.
- M. F. Atiyah, *Riemann surfaces and spin structures*,
  Ann. Sci. École Norm. Sup. (4) **4** (1971), 47–62.
- A. Beauville, *Variétés de Prym et jacobiennes intermédiaires*,
  Ann. Sci. École Norm. Sup. (4) **10** (1977), 309–391.
- J. Birman and R. Craggs, *The $\mu$-invariant of 3-manifolds and certain
  structural properties of the group of homeomorphisms of a closed, oriented
  2-manifold*, Trans. Amer. Math. Soc. **237** (1978), 283–309.
- L. Caporaso and E. Sernesi, *Recovering plane curves from their bitangents*,
  J. Algebraic Geom. **12** (2003), 225–244.
- I. Dolgachev, *Classical Algebraic Geometry: A Modern View*, Cambridge
  Univ. Press, 2012. (Especially Chapters 5 and 6 on plane quartics,
  bitangents, theta characteristics, and Steiner complexes.)
- I. Dolgachev and D. Ortland, *Point sets in projective spaces and theta
  functions*, Astérisque **165** (1988).
- R. Donagi, *The fibers of the Prym map*, Curves, Jacobians, and Abelian
  Varieties (Amherst, MA, 1990), Contemp. Math. **136** (1992), 55–125.
- D. Mumford, *Theta characteristics of an algebraic curve*,
  Ann. Sci. École Norm. Sup. (4) **4** (1971), 181–192.
- D. Mumford, *Prym varieties I*, in *Contributions to Analysis*
  (L. Ahlfors et al., eds.), Academic Press, 1974, 325–350.
- S. Recillas, *Jacobians of curves with $g^1_4$'s are the Pryms of trigonal
  curves*, Bol. Soc. Mat. Mexicana (2) **19** (1974), 9–13.
- B. Riemann, *Theorie der Abel'schen Functionen*, J. Reine Angew. Math.
  **54** (1857), 115–155; reprinted in *Gesammelte Mathematische Werke* (1876).
- G. Salmon, *A Treatise on the Higher Plane Curves*, 3rd ed., Hodges,
  Foster, and Figgis, 1879. (The classical reference for bitangents and
  Steiner complexes.)
- A. Verra, *The fibre of the Prym map in genus three*,
  Math. Ann. **276** (1987), 433–448.
- W. Wirtinger, *Untersuchungen über Thetafunctionen*, Teubner, Leipzig, 1895.
