# Audit of Chen's Lemma 3

## Printed statement

For \(S=\sigma+it\), \(\sigma\ge \tfrac12\), the scan states

\[
  \sum_{q\le Q}\sum_{\chi\pmod q}^{*}|L(S,\chi)|^4
  \ll Q^2|S|^2(\log Q)^4.
\]

There are three independent issues with this formulation and its printed
proof.

## 1. Modulus one has to be excluded

There is one primitive character modulo \(1\), and its L-function is the
Riemann zeta function.  Consequently the left side contains
\(|\zeta(S)|^4\).  Since \(\zeta\) has a pole at \(S=1\), no estimate uniform
on the closed half-plane \(\sigma\ge\tfrac12\) can include that term.  This
is not repaired merely by assigning an arbitrary finite value to a
meromorphic function exactly at its pole: the values are already unbounded
as \(S\to1\).

The natural range is therefore

\[
  \sum_{2\le q\le Q}\sum_{χ\pmod q}^{*}|L(S,χ)|^4,
  \qquad Q\ge2.
\]

This also matches the proof, whose Pólya–Vinogradov truncation is for
nonprincipal primitive characters.  Every primitive character of conductor
\(q\ge2\) is nonprincipal.

## 2. The last line of the printed proof loses a height logarithm

The scan chooses \(N=[Q|S|]\), squares the Dirichlet polynomial, and applies
the large sieve.  Its penultimate displayed bound contains

\[
  (Q^2+Q^2|S|^2)
  \sum_{n\le[Q|S|]^2}\frac{d(n)^2}{n}.
\]

The standard divisor-square estimate makes the last sum
\(O((\log(Q|S|))^4)\), not \(O((\log Q)^4)\) uniformly in \(S\).  Hence the
printed calculation does not imply its final displayed line when \(|t|\)
is unbounded.

After using \(|S|\ge\sigma\ge\tfrac12\), the calculation supports a bound of
the shape

\[
  \sum_{2\le q\le Q}\sum_{χ\pmod q}^{*}|L(S,χ)|^4
  \ll Q^2|S|^2
     \bigl(\log(2Q(1+|S|))\bigr)^4.
\]

In Lean this proof-supported statement is
`Lemma3FourthMomentWithHeightLog`.  The stronger log-\(Q\)-only statement is
`Lemma3FourthMoment`; it is the statement currently consumed by the
derivative fourth-moment part of Lemma 6, but it requires an additional
argument not present in Chen's proof.

## 3. The Dirichlet-series identity is used outside absolute convergence

The first line of the proof writes

\[
  L(S,\chi)=\sum_{n\ge1}\frac{\chi(n)}{n^S}
\]

throughout \(\sigma\ge\tfrac12\).  For a nonprincipal primitive character
this is mathematically valid when \(\sigma>0\), by bounded partial character
sums and Dirichlet's test.  It is nevertheless an additional theorem: the
standard absolutely convergent Dirichlet-series representation only applies
for \(\sigma>1\).  The printed proof does not say that it is invoking
conditional convergence and analytic continuation.

This distinction is concrete in the formalization.  Mathlib's packaged
theorem `DirichletCharacter.LFunction_eq_LSeries` has the hypothesis
`1 < re S`; it cannot justify the displayed equality on the half-plane used
in Lemma 3.  A complete formal proof of even the height-logarithmic variant
therefore still needs a bridge showing that the conditionally convergent
character Dirichlet series agrees with the analytic L-function for
`0 < re S` (or an equivalent analytic-continuation argument).  The current
code does not disguise that bridge as an absolute-convergence statement.

## Consequence for Lemma 6

Chen applies Lemma 3 at \(S=\beta+i\nu\) with unbounded \(\nu\).  Replacing
the strong form by the proof-supported form is possible only after carrying
an extra \(\log(2Q(1+|\nu|))\) through Cauchy's formula and checking that the
resulting factor remains integrable against the rapidly decaying contour
kernel.  This is not merely a bookkeeping mismatch in the present proof:
the current large-pair-block majorant has already relaxed the smoothing
kernel to an integrable multiple of \((1+\nu^2)^{-1}\).  Multiplying that
relaxed majorant by a further linear height factor would no longer be
integrable.  To use the height-logarithmic form one must therefore retain
more of the original high-order smoothing decay until after the extra
height logarithm is absorbed.  The existing formal interface intentionally
does not silently perform this replacement.  Thus the current status is:

* `lFunction_fourth_moment` is the sole unresolved theorem implementing the
  strong log-\(Q\)-only claim;
* `Lemma3FourthMomentWithHeightLog` records the weaker target supported by
  the size calculation, but is presently a proposition rather than a proved
  theorem;
* `lemma3FourthMomentWithHeightLog_of_strong` formally verifies that the
  strong statement implies the height-logarithmic one; no converse is
  available;
* proving that weaker target still requires the conditional-series bridge
  just described.
