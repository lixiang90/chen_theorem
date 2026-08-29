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
`Lemma3FourthMoment`; it remains recorded only as the claim printed in the
paper and has no theorem asserting it.  Lemma 6 now consumes the proved
height-logarithmic statement.

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
in Lemma 3.  The formalization supplies the required conditional-convergence
bridge in `Lemma6/StripGrowth.lean` and applies finite Abel summation in
`Lemma3/Approximation.lean`; it does not disguise this step as absolute
convergence.

## Consequence for Lemma 6

Chen applies Lemma 3 at \(S=\beta+i\nu\) with unbounded \(\nu\).  The
formalization carries the height logarithm through Cauchy's formula.  On an
occupied dyadic block it proves

\[
  \log(2Q(1+2|\beta+i\nu|))
  \ll (\log x)\sqrt{1+\nu^2}.
\]

Consequently the derivative fourth moment acquires
\((1+\nu^2)^2\); after taking a fourth root in equations (19) and (20), the
kernel weight becomes \((1+\nu^2)^{3/4}\).  The smoothing kernel still
dominates this by an integrable multiple of \((1+\nu^2)^{-1}\), so the
final Lemma 6 estimates are unchanged.

The current status is:

* `lFunction_fourth_moment_with_height_log` proves
  `Lemma3FourthMomentWithHeightLog` without `sorry`;
* `Lemma3FourthMoment` remains only a definition documenting the stronger
  printed claim, whose proof still has the height-log gap described above;
* `lemma6_deriv_fourth_moment_of_lFunction_fourth_moment_with_height_log`
  transfers the proved form to the derivative moment;
* `Lemma6/Core.lean` instantiates that transfer and the full Lemma 6 build
  succeeds.  The separate classical zero-free-region input remains the only
  `sorry` in the Lemma 6 analytic chain.
