# Pieri proof and the two root-of-unity shortcuts

> Design note for issue #20, drafted during planning. The issue numbers in Section 7 refer to an
> earlier internal 20-item plan, not to GitHub issues; `docs/MACDONALD.md` and the roadmap (#15)
> are current. Nothing here is formalized unless the source map in `docs/PROOF_OUTLINE.md` says
> so.


## 1. Conventions

Fix `N`, and pad every partition by zeros to length `N`.  We write
`mu <= lambda` for dominance:

```text
sum_{i <= s} mu_i <= sum_{i <= s} lambda_i  for every s.
```

Let `K = Q(q,t)`.  The finite-variable Macdonald polynomial
`P_lambda[X_N;q,t]` is the monic, dominance-unitriangular eigenvector of
`D_N^1` with eigenvalue

```text
epsilon_lambda(q,t) = sum_i q^(lambda_i) t^(N-i).
```

This is the definition recommended in `MACDONALD.md`.  For a vertical strip
`lambda/mu`, put `delta_i = lambda_i - mu_i`.  The row-pair form of the
elementary Pieri coefficient is

```text
psi'_(lambda/mu) =
  product over i < j with delta_i = 0 and delta_j = 1 of

  (1 - q^(mu_i-mu_j) t^(j-i-1))
  (1 - q^(lambda_i-lambda_j) t^(j-i+1))
  ---------------------------------------------------- .
  (1 - q^(mu_i-mu_j) t^(j-i))
  (1 - q^(lambda_i-lambda_j) t^(j-i))
```

This is equation (2.12) of Borodin--Corwin, with the same `P`
normalization.  The theorem to be proved is

```text
e_r P_mu = sum_{lambda/mu a vertical r-strip} psi'_(lambda/mu) P_lambda.
```

The discussion below treats `q` and `t` as independent until the explicitly
marked specialization step.

## 2. Shortcut (1): regularity from Pieri

### Verdict

The shortcut is correct.  It needs two short arguments that were implicit in
the proposal:

1. every endpoint occurring in the iterated Pieri expansion is dominated by
   `lambda`;
2. the chain ending at `lambda` is unique.

It then proves regularity of `P_lambda` at `q = zeta` without the integral
form `J_lambda`.

### Corrected argument

Let `zeta` be a primitive `k`th root of unity, and let

```text
R_k = Q(t)[q]_(Phi_k(q))
```

be the local ring at the cyclotomic polynomial.  Apply generic Pieri
successively to

```text
e_(lambda') = e_(lambda'_1) e_(lambda'_2) ... e_(lambda'_m) P_empty.
```

At the `j`th distinguished step, add one box to precisely the first
`lambda'_j` rows.  Thus the row increment is an initial string of ones
followed by zeros.  There is no pair `i < j` with `delta_i = 0` and
`delta_j = 1`, so the row-pair product is empty and the coefficient of this
step is one.

This chain is the only chain ending at `lambda`.  At the first step all
`lambda'_1` nonzero rows must receive a box: adding to any lower row would
make the endpoint too long, since boxes are never removed.  Inductively,
after `s-1` steps row `i` already contains `min(lambda_i,s-1)` boxes.  Rows
with `lambda_i<s` are at their endpoint capacity, while there are exactly
`lambda'_s` remaining rows with `lambda_i>=s`.  The strip has that same size,
so it must add to precisely those rows.  This proves uniqueness of the
column-by-column chain.

Now consider any endpoint `eta` of any chain in the expansion.  At step `j`,
a vertical strip of size `lambda'_j` puts at most
`min(r,lambda'_j)` boxes in the first `r` rows.  Hence

```text
sum_{i <= r} eta_i
  <= sum_j min(r,lambda'_j)
   = sum_{i <= r} lambda_i.
```

Therefore `eta <= lambda`; equality can occur only for the distinguished
chain just described.  We have proved

```text
e_(lambda') = P_lambda + sum_{eta < lambda} a_(lambda,eta) P_eta.    (2.1)
```

Each `a_(lambda,eta)` is a finite sum of products of row-pair coefficients.
Every denominator in such a coefficient is `1-q^a t^b` with `b >= 1`.
Its value at `q = zeta` is a nonzero element of `Q(zeta,t)`, even when
`a = 0`.  Equivalently, the denominator is a unit of `R_k`.  Thus every
`a_(lambda,eta)` lies in `R_k`.

Induct in increasing dominance order in each degree.  Equation (2.1) gives

```text
P_lambda = e_(lambda')
           - sum_{eta < lambda} a_(lambda,eta) P_eta,
```

so all monomial coefficients of `P_lambda` lie in `R_k`.  The generic
monomial transition matrix has diagonal entries one.  After evaluation at
`q = zeta`, it is still unitriangular and hence invertible.  Consequently the
specialized polynomials `P_lambda[X_N;zeta,t]` exist and form a basis in each
degree.

The statement that the distinguished step has coefficient one should not be
applied to the other chains.  Those coefficients need only be regular, and
the row-pair denominators give exactly that.

### Consequence for the implementation plan

Once generic Pieri is available, this argument removes the integral-form
normalizations `c_lambda`, `c'_lambda`, `b_lambda`, `Q_lambda`, and
`J_lambda` from the main route.  In the numbering of `MACDONALD.md`, it
removes issue 11 and most of issue 9.  A small local-ring specialization API
is still needed.

## 3. Shortcut (2): the root-of-unity rectangle

### Verdict

The shortcut is also correct, conditional on shortcut (1).  One phrase
should be replaced: the individual rational coefficients of `D_N^1` do not
become polynomials in the `x_i`.  What is polynomial is the induced action on
symmetric polynomials after alternant/Vandermonde cancellation.  That is the
fact which permits specialization.

### Corrected argument

Assume `0 <= h <= N` and set

```text
M_(k,h) = m_(k^h) = e_h(x_1^k,...,x_N^k).
```

For

```text
D_N^1 = sum_i A_i(x;t) T_(q,x_i),
A_i(x;t) = product_{j != i} (t x_i - x_j)/(x_i-x_j),
```

Macdonald VI (3.6)--(3.10) proves that the sum induces a polynomial
endomorphism of the symmetric-polynomial ring, with matrix coefficients
polynomial in `q,t`.  We may therefore set `q = zeta`.  Since `zeta^k = 1`,
every shift `T_(zeta,x_i)` fixes `M_(k,h)`.  The standard rational identity

```text
sum_i A_i(x;t) = 1+t+...+t^(N-1) = [N]_t
```

then gives

```text
D_N^1(zeta,t) M_(k,h) = [N]_t M_(k,h).                     (3.1)
```

The specialized eigenvalue of `P_(k^h)` is also `[N]_t`: the first `h`
terms acquire a factor `zeta^k=1`, and the remaining parts are zero.  By
shortcut (1), the specialized `P` polynomials are a unitriangular basis, so

```text
P_(k^h)(zeta,t) - M_(k,h)
  is in span {P_alpha(zeta,t) : alpha < (k^h)}.             (3.2)
```

Suppose a lower basis vector had eigenvalue `[N]_t`.  Equality

```text
sum_i zeta^(alpha_i) t^(N-i) = sum_i t^(N-i)
```

in `Q(zeta)[t]` implies coefficientwise that `zeta^(alpha_i)=1`.  Hence
`alpha=k beta` for a partition `beta` of `h`.  Dominance is preserved under
scaling, and every partition of `h` dominates `(1^h)`.  Thus
`k beta < k(1^h)` is impossible.  No lower eigenvalue is `[N]_t`.

Both terms in (3.2) satisfy (3.1).  Expanding their difference in the lower
`P_alpha` basis and comparing eigenvalues makes every coefficient zero.
Therefore

```text
P_(k^h)[X_N;zeta,t] = e_h(x_1^k,...,x_N^k) = m_(k^h).
```

This removes the one-variable branching package, issue 14 of
`MACDONALD.md`.  The case `h=0` is immediate; the displayed finite-variable
statement presupposes `h<=N`.

## 4. Which generic Pieri proof should be formalized?

### 4.1 Macdonald VI Section 6

Macdonald's route is the most economical complete route.  It begins after
the full generating operator has been shown to act diagonally on `P`.  Grid
evaluation turns this spectral action into the recurrence VI (6.5).
Evaluation symmetry VI (6.6) and normalized Pieri VI (6.7) are then proved
simultaneously by dominance induction.  The principal specialization
VI (6.11), derived from the first-column coefficient, converts the normalized
coefficient into the explicit row-pair product VI (6.13).

This proof is finite-variable, uses the desired `P` normalization, and ends
with exactly the coefficient needed here.  Macdonald's notes attribute the
symmetry and this proof of symmetry and Pieri to Koornwinder; the cited 1988
item is an unpublished manuscript.  Noumi's modern finite-variable account
presents the same structural idea as “spectral action plus self-duality.”

### 4.2 Operator and bispectral routes

The operator route is not a different short proof so much as the mechanism
inside Section 6.  We should define the single polynomial

```text
D_N(X;q,t) = sum_{r=0}^N D_N^r X^r,
```

whose eigenvalue on `P_lambda` is

```text
product_i (1 + X q^(lambda_i) t^(N-i)).
```

Taking the coefficient of `X^r` supplies every `D_N^r`.  Evaluating the
operator at `x_i=q^(mu_i)t^(N-i)` produces the transition coefficients for
vertical `r`-strips.  Evaluation symmetry then turns this difference-operator
action into multiplication by `e_r`.

One could prove commutativity of the `D_N^r` directly, use their simple joint
spectrum, and avoid a scalar product.  In Lean, however, this replaces a
finite bilinear-form argument by larger determinant or affine-Hecke operator
identities.  Macdonald's actual economy is the reverse: prove all `D_N^r`
self-adjoint, use their triangular action, and infer their diagonal action on
the already defined `D_N^1` eigenbasis.  Commutativity follows afterward.

### 4.3 Cauchy and orthogonality routes

Some orthogonality is useful, but a constant-term-first proof is not the
recommended foundation.  The torus constant-term product brings in Laurent
series and infinite `q`-products before they are otherwise needed.  The dual
Cauchy identity likewise does not by itself identify the explicit local
factor `psi'`; one must still prove the skew coefficient or evaluation
formula.

We retain only Macdonald's finite algebraic pairing VI (2.20), characterized
degreewise by

```text
<g_lambda,m_mu> = Kronecker(lambda,mu).
```

Its degree-truncated Cauchy kernel proves self-adjointness of the generating
operator.  This is much smaller than formalizing the analytic or stable
constant-term theory.

### 4.4 Other direct-operator literature

The alternatives confirm the chosen architecture but do not shorten it.

* Kirillov--Noumi's `q`-difference and affine-Hecke raising operators are
  powerful enough to prove integral-form results.  They require Dunkl/Hecke
  operators and a reproducing kernel, which is substantially more structure
  than the present Pieri theorem.
* Mimachi--Noumi's nonsymmetric reproducing kernel similarly moves the burden
  to nonsymmetric Macdonald polynomials and affine Hecke algebra.
* Okounkov and Knop--Sahi interpolation polynomials obtain binomial and Pieri
  phenomena from extra vanishing conditions.  Formalizing interpolation
  polynomials solely to recover ordinary vertical Pieri is longer than the
  grid-evaluation argument.
* Lassalle--Schlosser invert a known Pieri formula to obtain explicit
  transition formulas; their method therefore cannot serve as the missing
  proof of Pieri.
* Van Diejen--Emsiz prove a root-system-level Pieri formula from a difference
  equation and duality.  In type `A` this has the same bispectral core, with
  considerably more general notation and residue calculations.
* Garsia--Haiman and Haglund--Haiman--Loehr formulas are best suited to
  positivity and modified/integral forms.  Converting them to the finite
  `P`-normalized row-pair rule would introduce more normalization and
  triangularity work than it saves.

Thus we recommend Macdonald VI Section 6, expressed as a generating-operator
and evaluation-symmetry proof.  Noumi's Chapters 5--6 are the best modern
secondary blueprint.

## 5. Complete dependency ledger for the chosen route

The following is complete at theorem-package granularity.  Routine finite-sum,
coercion, and denominator side lemmas belong to the package that first uses
them.  Size estimates are source lines excluding tests and documentation.

The flags have the following meanings:

* **[D]** uses the full family `D_N^r`, normally through `D_N(X;q,t)`;
* **[SP]** uses the finite algebraic scalar product;
* **[PS]** uses the principal-specialization formula.  The formula is derived
  in Lemma 13, not assumed.

### Lemma 1. The `g` basis **[SP]**

**Statement.**  Define `g_r[X_N;q,t]` by

```text
sum_{r>=0} g_r u^r = product_i (t x_i u;q)_infinity/(x_i u;q)_infinity,
```

interpreted coefficientwise, and put `g_lambda=product_i g_(lambda_i)`.
For fixed degree `d`, the `g_lambda` with `lambda` a partition of `d` and
`length lambda <= N` form a basis of the symmetric homogeneous subspace.

**Source and proof idea.**  Macdonald VI (2.8), (2.19).  Expand each fixed
coefficient as a finite sum.  At `q=t=0`, the functions become the complete
functions `h_lambda`, which form a basis by their unitriangular Schur
transition.  The generic transition determinant is therefore not the zero
rational function.

**Lean infrastructure.**  `MvPolynomial`, `msymm`, homogeneous components,
partitions, finite `q`-Pochhammer coefficients, and finite triangular matrices.

**Size.**  M/L, 300--500 lines.

### Lemma 2. Finite algebraic pairing and kernel **[SP]**

**Statement.**  There is a unique symmetric nondegenerate bilinear form in
each degree satisfying

```text
<g_lambda,m_mu>_(q,t) = delta_(lambda,mu).
```

Its degree-`d` reproducing kernel is the degree-`d` part of

```text
Pi(x,y) = product_(i,j)
  (t x_i y_j;q)_infinity/(x_i y_j;q)_infinity.
```

**Source and proof idea.**  Macdonald VI (2.20)--(2.21).  Define the matrix in
dual bases; symmetry follows from the kernel identity, and invertibility from
the basis theorem.

**Lean infrastructure.**  Finite-dimensional bilinear forms, tensor products
or bivariate `MvPolynomial`, and degree truncation.  No analytic convergence
and no torus constant term are needed.

**Size.**  M, 250--400 lines.

### Lemma 3. Polynomial generating operator **[D]**

**Statement.**  The alternant quotient defining `D_N(X;q,t)` is divisible by
the Vandermonde and induces an endomorphism of symmetric polynomials.  Its
coefficient is

```text
D_N^r = sum_(I subset {1,...,N}, |I|=r)
  t^(r(r-1)/2)
  product_(i in I, j notin I) (t x_i-x_j)/(x_i-x_j)
  product_(i in I) T_(q,x_i).
```

**Source and proof idea.**  Macdonald VI (3.2)--(3.6).  Apply the shift inside
an antisymmetrization.  The numerator remains alternating and is therefore
divisible by the Vandermonde.

**Lean infrastructure.**  Multivariate substitutions, alternants,
Vandermonde divisibility, localization for the displayed rational expression,
and descent back to `MvPolynomial`.  Tau Ceti's alternant work is reusable.

**Size.**  XL, 700--1,200 lines.  This is the go/no-go milestone.

### Lemma 4. Dominance-triangular action **[D]**

**Statement.**  For every partition `lambda` of length at most `N`,

```text
D_N(X) m_lambda =
  product_i (1+X q^(lambda_i)t^(N-i)) m_lambda
  + sum_(mu<lambda) c_(lambda,mu)(X) m_mu.
```

In particular, the coefficient of `X` gives the triangular action and
eigenvalue used to define `P_lambda`.

**Source and proof idea.**  Macdonald VI (3.6)--(3.10).  Analyze the orbit sum
of a leading monomial; all other exponent vectors sort to dominated
partitions.

**Lean infrastructure.**  Monomial symmetric polynomials, permutation orbit
sums, dominance, leading coefficients, and finite polynomial matrices.

**Size.**  L/XL, 500--900 lines.

### Lemma 5. Self-adjointness of every coefficient **[D, SP]**

**Statement.**  For `0<=r<=N`,

```text
<D_N^r f,g>_(q,t) = <f,D_N^r g>_(q,t).
```

Equivalently, `(D_x(X)-D_y(X)) Pi(x,y)=0` degree by degree.

**Source and proof idea.**  Macdonald VI (3.11)--(3.12).  Conjugate the kernel
by the shift, observe that the remaining identity is independent of `q`, and
reduce it to the `q=t` Schur case.  Formalize only a fixed total degree, so
all series truncate.

**Lean infrastructure.**  Lemmas 2--3, bivariate substitutions, finite
coefficient extraction, and Schur Cauchy/orthogonality facts from Tau Ceti.

**Size.**  XL, 600--1,000 lines.

### Lemma 6. The `D_N^1` eigenbasis is orthogonal **[SP]**

**Statement.**  The eigenvalues
`sum_i q^(lambda_i)t^(N-i)` are pairwise distinct over `Q(q,t)`.  Hence the
monic unitriangular `D_N^1` eigenvectors `P_lambda` exist uniquely and satisfy

```text
<P_lambda,P_mu>_(q,t)=0  if lambda != mu.
```

**Source and proof idea.**  Macdonald VI (4.7).  Recursive triangular linear
algebra gives existence.  Self-adjointness and distinct eigenvalues give
orthogonality.

**Lean infrastructure.**  The existing recommended definition, finite
triangular matrices, rational functions, and the elementary theorem that
eigenvectors of a self-adjoint operator with distinct eigenvalues are
orthogonal.

**Size.**  M, 250--400 lines beyond the definition of `P`.

### Lemma 7. Joint spectral action **[D, SP]**

**Statement.**  The same polynomials satisfy

```text
D_N(X) P_lambda =
  product_i (1+X q^(lambda_i)t^(N-i)) P_lambda.              (5.1)
```

**Source and proof idea.**  Macdonald VI (4.15).  Lemma 4 makes the matrix of
`D_N(X)` triangular in the unitriangular `P` basis.  Lemma 5 makes it
self-adjoint in the orthogonal basis.  A triangular self-adjoint matrix in an
orthogonal basis is diagonal, and Lemma 4 identifies the diagonal.

**Lean infrastructure.**  Lemmas 4--6 and nondegeneracy of the pairing.
Direct commutativity is not needed; it follows from (5.1).

**Size.**  S/M, 150--300 lines.

### Lemma 8. Nonzero base evaluation **[SP]**

**Statement.**  With

```text
u_mu(f) = f(q^(mu_1)t^(N-1),...,q^(mu_N)),
```

we have `u_0(P_lambda) != 0` as a rational function.

**Source and proof idea.**  At `q=t`, Macdonald VI (4.14)(i) gives
`P_lambda=s_lambda`; the principal Schur evaluation at
`(t^(N-1),...,1)` is nonzero.  This proves that the generic rational function
is not identically zero.  This is not the Macdonald principal-specialization
formula.

**Lean infrastructure.**  A specialization lemma for rational functions,
the `q=t` Schur identification, and Tau Ceti's bialternant/principal Schur
evaluation.

**Size.**  M, 250--450 lines.

### Lemma 9. Grid evaluation of the operator **[D]**

**Statement.**  If `I` is an `r`-subset and `theta_i=1` exactly on `I`, then
the specialized coefficient `u_mu(A_I)` is nonzero exactly when
`mu+theta` is a partition.  In that case define

```text
B_((mu+theta)/mu) = u_mu(A_I).
```

**Source and proof idea.**  Macdonald VI (6.2)--(6.4).  Substitute the grid
values in the explicit product.  A zero occurs exactly at an adjacent equal
pair for which the lower row, but not the upper row, is incremented.

**Lean infrastructure.**  Lemma 3, evaluation of rational products, adjacent
partition inequalities, and vertical-strip encodings by Boolean vectors.

**Size.**  L, 350--600 lines.

### Lemma 10. The grid recurrence **[D]**

**Statement.**  For all partitions `lambda,mu` and `0<=r<=N`,

```text
u_lambda(e_r) u_mu(P_lambda)
  = sum_(nu/mu vertical r-strip)
      B_(nu/mu) u_nu(P_lambda).                              (5.2)
```

**Source and proof idea.**  Macdonald VI (6.5).  Evaluate the coefficient of
`X^r` in (5.1) at the `mu` grid and use Lemma 9 to discard illegal subsets.

**Lean infrastructure.**  Lemmas 7 and 9, finite coefficient extraction, and
the fact that `u_lambda(e_r)` is the `r`th elementary symmetric function of
the spectral variables.

**Size.**  S, 100--180 lines.

### Lemma 11. Evaluation matrices separate lower terms

**Statement.**  For a partition `rho`, let `I_rho` be the strict principal
dominance ideal of partitions of `|rho|` below `rho`.  The matrix

```text
(u_mu(P_lambda)/u_0(P_lambda))_(mu,lambda in I_rho)
```

is nonsingular over `Q(q,t)`.

**Source and proof idea.**  Macdonald VI (6.8) and the following Example 1.
Unitriangularity permits replacement of `P` by `m`.  The highest `t`-degree
term of the resulting determinant is a determinant of
`q^(<mu,lambda>)`.  Rearrangement, or positive definiteness after a real
specialization of `q`, shows that this determinant is nonzero.

**Lean infrastructure.**  Finite determinants, invariance under
unitriangular column operations, weighted leading terms, and a strict
rearrangement/Gram-matrix lemma for partitions.

**Size.**  L, 400--700 lines.

### Lemma 12. Evaluation symmetry and normalized Pieri **[D]**

**Statement.**  Put `Pbar_lambda=P_lambda/u_0(P_lambda)`.  Simultaneously,

```text
u_lambda(Pbar_mu) = u_mu(Pbar_lambda),                       (5.3)

Pbar_mu e_r = sum_(nu/mu vertical r-strip)
                B_(nu/mu) Pbar_nu.                           (5.4)
```

for all allowed indices and all `r`.

**Source and proof idea.**  Macdonald VI (6.6)--(6.8).  Induct on size and
then dominance.  For nonempty `mu`, remove an initial column segment to write
`mu=sigma+(1^r)`.  Triangularity gives an unknown expansion of
`Pbar_sigma e_r`.  Evaluate it on all lower grids.  Recurrence (5.2), the
inductive symmetry, and Lemma 11 identify every coefficient with `B`.  Apply
the resulting Pieri identity at a general grid and compare once more with
(5.2) to obtain symmetry for `mu`.

**Lean infrastructure.**  Lemmas 8--11, well-founded induction on
`(size,dominance)`, coefficient comparison in the `P` basis, and finite
matrix injectivity.

**Size.**  XL, 700--1,100 lines.  This is the central theorem package.

### Lemma 13. Principal specialization **[PS]**

**Statement.**  For `length lambda <= N`,

```text
u_0(P_lambda) = t^(n(lambda))
  product_(s in lambda)
    (1-q^(a'(s)) t^(N-l'(s)))
    /(1-q^(a(s)) t^(l(s)+1)).                                (5.5)
```

**Source and proof idea.**  Macdonald VI (6.10)--(6.12), including the cell
form customarily denoted (6.11').  Rewrite (5.4) in the unnormalized `P`
basis.  For `lambda=mu+(1^r)`, monicity says that the coefficient of the
leading term is one, whereas (5.4) makes it
`B_(lambda/mu)u_0(P_mu)/u_0(P_lambda)`.  Hence
`u_0(P_lambda)=B_(lambda/mu)u_0(P_mu)`.  Remove first columns recursively and
verify that the product in (5.5) satisfies the same ratio; Macdonald uses an
injective logarithm on finite products of `1-q^a t^b`.

**Lean infrastructure.**  Young-diagram cells, arm/leg and coarm/coleg
statistics, finite-product cancellation, and the first-column bijections.
The logarithm device may be replaced by equality of factor multiplicities.

**Size.**  L, 400--700 lines.

### Lemma 14. Explicit row-pair coefficient **[PS]**

**Statement.**  Rewriting (5.4) for unnormalized `P` gives

```text
psi'_(lambda/mu)
  = B_(lambda/mu) u_0(P_mu)/u_0(P_lambda),                   (5.6)
```

and substitution of (5.5) reduces (5.6) to the row-pair product displayed in
Section 1.

**Source and proof idea.**  Macdonald VI (6.9), (6.13); Borodin--Corwin
(2.12).  Group the factors by row pairs.  Pairs with increment pattern
`(0,0)`, `(1,0)`, or `(1,1)` cancel; only `(0,1)` remains.

**Lean infrastructure.**  Lemmas 9 and 13, finite-product reindexing, row/cell
bijections, and localization identities for `1-q^a t^b`.

**Size.**  L, 350--650 lines.

### Lemma 15. Generic vertical Pieri theorem **[D, SP, PS]**

**Statement.**  For every `0<=r<=N`,

```text
e_r P_mu = sum_(lambda/mu vertical r-strip)
              psi'_(lambda/mu) P_lambda,
```

and both sides are zero for the expected out-of-range finite-variable
indices.

**Source and proof idea.**  Combine Lemmas 12 and 14 and discharge the
`r=0`, `r>N`, and length-boundary cases.

**Lean infrastructure.**  The preceding packages and the existing
elementary-symmetric-polynomial API.

**Size.**  S, 100--200 lines.

The full estimate is roughly 5,500--9,300 source lines.  Lemmas 3, 5, and 12
carry most of the uncertainty.  Shortcut (1) should follow as a 250--450 line
local-ring module; shortcut (2) as a 200--350 line root-eigenspace module.

## 6. Does `e_1` determine all `e_r` cases?

No.  For `N>=2`, the symmetric-polynomial algebra is freely generated by
`e_1,...,e_N`; `e_r` is not a polynomial in `e_1`.  Iterating the `e_1`
Pieri rule produces weighted sums over saturated paths.  Those sums determine
multiplication by powers of `e_1`, not multiplication by `e_r`, and they do
not isolate the vertical strips of size `r`.

The `e_1` case together with the full generating operator and evaluation
symmetry does determine every case, but only because the coefficient of
`X^r` supplies the independent operator `D_N^r`.  This is not a reduction of
the theorem to `e_1`; it imports precisely the missing higher structure.
Likewise, `e_1` plus a full set of raising-operator or symmetric-function
relations could recover the result, but would not be more economical than
Lemma 15.  The formalization needs every `r`.

## 7. Revised issue impact

Relative to the plan in `MACDONALD.md`:

* issue 9 is reduced to `P`, the finite algebraic pairing, and only the
  normalizations internal to the proof of generic Pieri;
* issue 10 should implement Macdonald's degreewise finite pairing, not the
  torus constant-term form;
* issue 11 (`IntegralForm`) leaves the main dependency chain;
* issues 12--13 should be replaced by Lemmas 1--15 above;
* issue 14 (`Branching`) leaves the main dependency chain;
* issue 15 becomes the short local-ring induction of Section 2;
* issue 16 becomes the eigenspace argument of Section 3.

The two shortcuts therefore work, but they do not make generic Pieri smaller.
They make Pieri the single large Macdonald theorem and remove two other large
theory packages from everything downstream.

## 8. Citation audit

The equation numbers above were checked against Macdonald, Chapter VI:
VI (2.8), (2.19)--(2.21), (3.2)--(3.12), (4.7), (4.14)--(4.15), and
(6.1)--(6.13).  The row-pair convention was checked independently against
Borodin--Corwin (2.12).  Noumi's book contents confirm that “Orthogonality and
Higher-Order q-Difference Operators” precedes “Self-duality, Pieri Formula
and Cauchy Formulas,” exactly matching the selected dependency order.

The arXiv metadata for 2604.25440 gives P. Alexandersson and L. Dai,
“Partition division maps, symmetric functions and positivity.”  The entry in
`MACDONALD.md` has been corrected accordingly.

## References

* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, second
  edition, Chapter VI; [verified scan](https://math.berkeley.edu/~corteel/MATH249/macdonald.pdf).
* A. Borodin and I. Corwin, “Macdonald processes,” equation (2.12),
  [arXiv:1111.4408](https://arxiv.org/abs/1111.4408).
* M. Noumi, *Macdonald Polynomials: Commuting Family of q-Difference
  Operators and Their Joint Eigenfunctions*, especially Chapters 5--6,
  [Springer, 2023](https://doi.org/10.1007/978-981-99-4587-0).
* A. N. Kirillov and M. Noumi, “q-Difference raising operators for Macdonald
  polynomials and the integrality of transition coefficients,”
  [arXiv:q-alg/9605005](https://arxiv.org/abs/q-alg/9605005).
* K. Mimachi and M. Noumi, “A reproducing kernel for nonsymmetric Macdonald
  polynomials,” [arXiv:q-alg/9610014](https://arxiv.org/abs/q-alg/9610014).
* A. Okounkov, “Binomial formula for Macdonald polynomials,”
  [arXiv:q-alg/9608021](https://arxiv.org/abs/q-alg/9608021).
* S. Sahi, “Interpolation, integrality, and a generalization of Macdonald's
  polynomials,”
  [doi:10.1155/S107379289600030X](https://doi.org/10.1155/S107379289600030X),
  and F. Knop and S. Sahi, “Difference equations and symmetric polynomials
  defined by their zeros,”
  [doi:10.1155/S1073792896000311](https://doi.org/10.1155/S1073792896000311).
* M. Lassalle and M. Schlosser, “Inversion of the Pieri formula for Macdonald
  polynomials,” [arXiv:math/0402127](https://arxiv.org/abs/math/0402127).
* J. F. van Diejen and E. Emsiz, “A Pieri formula for Macdonald's spherical
  functions and polynomials,”
  [arXiv:1009.4482](https://arxiv.org/abs/1009.4482).
* P. Alexandersson and L. Dai, “Partition division maps, symmetric functions
  and positivity,” [arXiv:2604.25440](https://arxiv.org/abs/2604.25440).
