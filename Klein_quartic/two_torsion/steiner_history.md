# History of "Steiner complex" definitions in this project

This note records the chain of three different working definitions of
"Steiner complex" that the Klein-quartic / Fermat-quartic two-torsion code
has gone through, and the equivalence proof tying them together. It exists
because the question "what was the original definition?" came up after we
had cycled through three of them and lost track. Written 2026-04-09.

---

## TL;DR

| Version | Where | Definition |
|---|---|---|
| **(A) "8 points on a conic"** (user, March 6 2026) | session prompt; never a code comment | A set of 6 unordered pairs of bitangents is a Steiner complex iff for every two of those pairs the 8 intersection points (with $C$) of the 4 lines lie on a conic. |
| **(B) Contact-quadratic linear system** (`steiner.m`, first impl) | docstring of the now-deleted `Klein_quartic/two_torsion/steiner.m` | Two pairs $\{L_i,L_j\}, \{L_k,L_l\}$ are *conic-compatible* iff the linear system "$Q\rvert_{L_m} = \lambda_m h_m$ for $m=i,j,k,l$" has a nontrivial solution; a Steiner complex is a maximal mutually conic-compatible class of pairs. |
| **(C) $J[2]$ difference binning** (current `steiner_pipeline.m`, also `steiner_genus2.m`, `hensel_decomp.m`) | `steiner_pipeline.m:112-117` | Pick a base bitangent $L_0$. For each other bitangent $L_i$, compute the half-divisor class $[D_i] \in J[2]$. Bin pairs $\{L_i, L_j\}$ by $[D_i] - [D_j] \in J[2]$. The 63 bins (one per nonzero $\eta \in J[2]$) are the Steiner complexes. |

(A) is the *literal* classical definition. (B) is what (A) becomes when you
implement it via contact quadratics rather than via "find 8 points and fit a
conic". (C) is what we ended up with after rewriting the pipeline to use
function-field class groups instead of scheme-theoretic intersection.

All three give the same 63 sets of 6 pairs.

---

## (A) The original user-supplied definition

On **March 6 2026** (session
`4e09dfe1-977f-4297-8a64-484114973cd4`, subagent log
`agent-acompact-32cd36336cb09002.jsonl`), the user wrote:

> "excellent, now we want to arrange these into 'Steiner complexes'. First
> save the data of these lines so we don't need to recompute. The next step
> is to partition the pairs of distinct bitangent lines into 63 Steiner
> complexes of six elements each. **A collection of six (unordered pairs)
> of bitangent lines is a Steiner complex if for each distinct pair (of
> distinct pairs of bitangents) the 8 points obtained by intersecting each
> line with C_twist live on a conic.** Find the Steiner complexes and also
> save in some data structure the conics that witness the Steiner complexes."

This is a closure condition: a candidate set of 6 pairs is a Steiner
complex iff the conic property holds for *every* one of the
$\binom{6}{2} = 15$ pair-of-pairs inside it. The pair-of-pairs is the
combinatorial primitive; the 6-pair complex is what you get by closing it
up.

This is the classical definition you'll find in Salmon §220–221 and in
Dolgachev's *Classical Algebraic Geometry* §6.1.

## (B) The first implementation: `steiner.m` and the contact-quadratic linear system

The first implementation (later deleted; see
`Klein_quartic/two_torsion/CLEANUP_REPORT.md`) translated (A) into a
linear-algebra check that doesn't ever explicitly compute the 8 contact
points. Its docstring read:

> "A Steiner complex is a set of 6 unordered pairs of bitangent lines such
> that for any two pairs, the 8 tangency points (2 per line, 4 lines) lie
> on a conic. Method: reduce to $\mathbb F_p$, use contact-quadratic
> approach. For bitangent $L_i$ with contact quad $h_i$, a conic $Q$ passes
> through the tangency points of $L_i$ iff $Q\rvert_{L_i}$ is proportional
> to $h_i$. Two pairs $\{L_i,L_j\}, \{L_k,L_l\}$ are conic-compatible iff
> the linear system '$Q\rvert_{L_m} = \lambda_m h_m$ for $m=i,j,k,l$' has a
> nontrivial solution in $Q$."

Why this works as a check: each bitangent $L_m$ has a unique-up-to-scalar
"contact quadratic" $h_m \in k[L_m]$, namely the polynomial whose roots
(with multiplicity) are the parameter values of the two contact points
$P_m, P_m'$ on the line $L_m$. (Recall $L_m \cdot C = 2 P_m + 2 P_m'$, so
the contact divisor is $P_m + P_m'$, of degree 2 — that's exactly the
degree of $h_m$.) A conic $Q$ in $\mathbb P^2$ passes through both $P_m$
and $P_m'$ iff $Q\rvert_{L_m}$ vanishes at exactly those parameter values
iff $Q\rvert_{L_m} \propto h_m$.

So the existence of *some* nonzero $Q$ obeying $Q\rvert_{L_m} \propto h_m$
for $m \in \{i,j,k,l\}$ is exactly the existence of a conic through the 8
contact points of the 4 bitangents — which is (A) for that pair-of-pairs.

The matrix is $12 \times 10$:
- 12 rows = 4 bitangents × 3 conditions per line (the restriction
  $Q\rvert_{L_m}$ is a quadratic in the line parameter, with 3 coefficients
  that must each match $\lambda_m$ times the corresponding coefficient of
  $h_m$);
- 10 columns = 6 unknown coefficients of $Q \in \mathrm{Sym}^2 V^*$ + 4
  unknown scalars $\lambda_i, \lambda_j, \lambda_k, \lambda_l$.

For a conic-compatible pair-of-pairs the kernel is exactly $1$-dimensional
and gives $Q$. This same routine survives in the current code as
`FindConic` — see `steiner_pipeline.m`'s STEP 2.

This was definition (A) under the hood; the user-facing object was still
"the conic exists", just verified via this clever 12×10 system instead of
by interpolating 8 points.

## (C) The rewrite: `steiner_pipeline.m` and $J[2]$ difference binning

When we rebuilt the pipeline as `steiner_pipeline.m` (April 2026), the
relevant header comment is:

```
// STEP 1: Function field and Steiner complexes via J[2]
//
// Use the explicit function field FF = Fp(t)[u]/(f(t,u,1)) to avoid
// brittle scheme-intersection code. For each pair of bitangent lines,
// div(L_i/L_j) = 2*(D_i - D_j) as a divisor on C, so the half-divisor
// gives the J[2] class directly.
```

The motivation was practical: scheme-theoretic intersection of lines with
projective plane curves over a function field was fragile in Magma, and we
wanted a routine that didn't need it. The function-field route gives
$D_i - D_j \in J[2]$ as a class-group element directly, with no
intersection theory. The 63 Steiner complexes then fall out of binning all
$\binom{28}{2} = 378$ pairs by the $J[2]$ class of $D_i - D_j$:
$378 / 6 = 63$, and each bin has size 6.

The old contact-conic check (now `FindConic`) is still there, but as
*STEP 2* — it's used to *witness* each Steiner complex with its 15 conics
after the binning has already produced the 63 sets of 6 pairs. The roles
of "definition" and "witness" got swapped between version (B) and version
(C).

---

## Why all three are equivalent

The cleanest equivalence proof goes through $\mathrm{Pic}^8(C)$.

Each bitangent $L_m$ gives an odd theta characteristic $\kappa_m =
\mathcal O_C(P_m + P_m')$ with $2 \kappa_m = K_C$. Fix one bitangent and
write $\kappa_m = \kappa_0 + \eta_m$ for the unique $\eta_m \in J[2]$.
Then the degree-8 divisor

$$
D := P_i + P_i' + P_j + P_j' + P_k + P_k' + P_l + P_l'
   \;\sim\; \kappa_i + \kappa_j + \kappa_k + \kappa_l
   \;=\; 2 K_C + (\eta_i + \eta_j + \eta_k + \eta_l) \in \mathrm{Pic}^8(C).
$$

Under the canonical embedding $C \hookrightarrow \mathbb P^2$, the linear
system $|2 K_C|$ is exactly the linear system of conic sections cut out on
$C$. So:

$$
D \in |2 K_C|
\quad\Longleftrightarrow\quad
\eta_i + \eta_j + \eta_k + \eta_l \;=\; 0 \text{ in } J[2]
\quad\Longleftrightarrow\quad
(\kappa_i - \kappa_j) + (\kappa_l - \kappa_k) \;=\; 0
\quad\Longleftrightarrow\quad
[D_i - D_j] \;=\; [D_k - D_l] \text{ in } J[2].
$$

Reading the chain left-to-right:

- $D \in |2 K_C|$ is **(A)** — there exists a conic through the 8 contact
  points.
- $D \in |2 K_C|$ is exactly the property the contact-quadratic linear
  system tests, so it's **(B)** — the kernel of the $12 \times 10$ matrix
  is the realization of the conic in $|2K_C|$.
- The condition $[D_i - D_j] = [D_k - D_l]$ in $J[2]$ is **(C)** — the two
  pairs land in the same bin under difference-binning.

So all three definitions specify the same combinatorial structure: the 63
fibres of the difference map

$$
\binom{\{\text{bitangents}\}}{2} \;\longrightarrow\; J[2] \setminus \{0\},
\qquad \{L_i, L_j\} \mapsto [D_i - D_j],
$$

each fibre being a Steiner complex of 6 disjoint pairs.

---

## A subtlety: $Q$ is *through*, not *tangent*

When pipeline_math.md was first written this session, the §5 theorem
phrased $Q$ as a "contact conic that is tangent to $C$ at the eight contact
points". That was wrong, and worth recording why so the same mistake
doesn't get re-introduced.

The relation in degree 4 is

$$ a F = L_i L_j L_k L_l + b Q^2. \tag{$\star$} $$

Restricting both sides to $C$ (where $F \equiv 0$):

$$ \mathrm{div}(L_i L_j L_k L_l)\rvert_C
   = \mathrm{div}(b Q^2)\rvert_C \quad (\text{up to sign}). $$

The left side is

$$ 2(P_i + P_i' + P_j + P_j' + P_k + P_k' + P_l + P_l'), $$

a divisor of degree 16 supported on 8 distinct points each with
multiplicity 2 (each bitangent contributes $2 P_m + 2 P_m'$).

So $2 \cdot \mathrm{div}(Q)\rvert_C$ has degree 16 and is supported on
those same 8 points each with multiplicity 2. Dividing by 2 (which is
legitimate because the divisor is divisible by 2 in the divisor group of
$C$):

$$ \mathrm{div}(Q)\rvert_C
   = P_i + P_i' + P_j + P_j' + P_k + P_k' + P_l + P_l', $$

a degree-8 divisor with **multiplicity one at each of the 8 points**.
That's a conic *through* the 8 contact points — the unique one in
$|2 K_C|$ — not a conic tangent to $C$.

The "double zero per pair $(P_m, P_m')$" structure that makes $Q^2$ behave
nicely in $(\star)$ comes from squaring $Q$, not from $Q$ being tangent.
A genuine "contact conic" (tangent to $C$ at all of its intersection
points) would have $Q \cap C$ a divisor of degree 8 supported on $\le 4$
points each with multiplicity $\ge 2$, by Bézout. Our $Q$ has 8 distinct
support points with multiplicity 1 — the opposite extreme.

The classical literature uses "Steiner conic" or "Steiner's conic" for the
$Q$ here; "contact conic" is a misnomer in this context.

---

## References

- **G. Salmon**, *A Treatise on the Higher Plane Curves*, 3rd ed., Hodges,
  Foster, and Figgis, Dublin, 1879. §216 (28 bitangents and odd theta
  characteristics), §220–221 (Steiner's theorem on conics through 8 contact
  points and the syzygetic vs azygetic dichotomy).
- **I. Dolgachev**, *Classical Algebraic Geometry: A Modern View*, CUP,
  2012. §6.1 has the modern treatment of bitangents, theta characteristics
  and Steiner complexes; Prop. 6.1.7-ish area for the
  $|2 K_C|$ ↔ "conics through 8 contact points" identification.
- **L. Caporaso, E. Sernesi**, "Recovering plane curves from their
  bitangents", *J. Algebraic Geom.* 12 (2003) 225–244 — uses the same
  identity from the reconstruction-of-quartics-from-bitangents perspective.
- **D. Mumford**, *Tata Lectures on Theta II*, Birkhäuser, 1984. §3 has the
  theta-characteristic / Arf-invariant phrasing used in §2 of
  pipeline_math.md.

---

## File history (relevant pieces)

- `Klein_quartic/two_torsion/steiner.m` — first implementation (March 2026,
  version (B)). Now deleted; documented in
  `Klein_quartic/two_torsion/CLEANUP_REPORT.md`.
- `Klein_quartic/two_torsion/syzygetic_*.m` — exploratory scripts that
  verified the rational identity $-F + \ell_1 \ell_2 \ell_3 \ell_4 = 7 Q^2$
  for the Klein twist over $\mathbb F_{71}$ and over $\mathbb Q(\sqrt{-7})$.
  These were specializations of $(\star)$ for Q-rational bitangents, not
  alternative definitions of "Steiner complex". Now deleted; see
  `CLEANUP_REPORT.md`.
- `Klein_quartic/two_torsion/steiner_pipeline.m` — current consolidated
  pipeline (version (C) for binning + version (B)'s `FindConic` retained as
  the witnessing routine).
- `Klein_quartic/two_torsion/pipeline_math.md`, `pipeline_math.tex` —
  written in this session; §4 documents version (C) as the working
  definition, §5 documents the conic-through-8-points characterization as
  a theorem about the witness $Q$ (with the tangency error fixed
  2026-04-09).
