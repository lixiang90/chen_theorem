# Formalization of Chen's theorem (1 + 2) in Lean 4 / Mathlib

This Lake project is an in-progress formalization of Chen Jingrun's 1973 paper,
with the remaining analytic input isolated in `primitive_zero_free_region`:

> Chen Jingrun, *On the representation of a large even integer as the sum of a
> prime and the product of at most two primes*, Sci. Sinica **16** (1973), 111–128.

(A LaTeX transcription of the paper, in Chinese and English, lives in the parent
directory: `../latex/main.tex`, `../latex/main_en.tex`.)

- **Lean**: `leanprover/lean4:v4.32.2`
- **Mathlib**: release tag `v4.32.2`
- **Only direct package dependency**: Mathlib (including its normal transitive packages).
- **Locally included analytic proofs**: selected Apache-2.0 sources from
  `PrimeNumberTheoremAnd` commit `c6c73610b406689c4b58325cbe1342ecca25d755`,
  under `ChenTheorem/Analysis/PNT/`; no external PNT package is fetched or imported.
  See `Analysis/PNT/SOURCES.json` (under `ChenTheorem/`) for provenance.

## Build

```
cd formal
lake exe cache get   # download prebuilt Mathlib binaries
lake build
lake env lean AuditAnalysis.lean  # local PNT / Mertens / Perron trust check
lake env lean AuditSieve.lean     # Rosser sieve and prime-weight distribution trust check
lake env lean Audit.lean          # completion gate; currently fails on the zero-free-region input
```

## Structure

| File | Contents |
|---|---|
| `ChenTheorem/Defs.lean` | All definitions: `IsP2`, counting functions `P_x(1,2)`/`x_h(1,2)`, singular series `C_x`, smoothing function `Φ`, sieve weights `λ_d`, the sums `Ω`, `M₁`, and the sifted prime counts of Lemma 9 |
| `ChenTheorem/LargeSieve/Gallagher.lean` | Centered-interval Sobolev/Gallagher inequality |
| `ChenTheorem/LargeSieve/Additive.lean` | Parseval, Farey spacing, and the additive large sieve |
| `ChenTheorem/LargeSieve/Character.lean` | Gauss-sum transition, character large sieve (2), and dyadic form (3) |
| `ChenTheorem/SieveLemmas.lean` | Lemmas 1–4: properties of `Φ`, the large sieve, the `L`-function fourth moment, primitive character sums |
| `ChenTheorem/Lemma5/Core.lean` | Finite-sum definitions and elementary reductions used in Lemma 5 |
| `ChenTheorem/Lemma5/{Arithmetic,Smoothing}.lean` | Arithmetic majorants, formula (5), and the small-base transition estimate |
| `ChenTheorem/Lemma5/{PrimeReciprocals,EulerPenalty}.lean` | Prime reciprocal estimates and the Euler-factor penalty for excluded prime divisors |
| `ChenTheorem/Lemma5/Boundary/{Sieve,Selberg,Weights,Mass,Analytic}.lean` | The dimension-two boundary sieve, Selberg diagonalization and optimal weights, the lower bound for `G(R)`, and the final short-interval estimate |
| `ChenTheorem/Lemma6/FourthMoment.lean` | The dyadic, totient-weighted `L'` fourth moment required after equation (15), with one rigorous logarithmic slack over the paper's displayed exponent, explicitly derived from the corrected Lemma 3 interface |
| `ChenTheorem/Lemma6/{PairBlockEstimate,LargePairBlock}.lean` | The full dyadic-block analysis of equations (13)–(20): block-summed A/B contour bounds, the remainder majorant scale bounds, and the pointwise regime estimates closing each occupied `(l,k)` block by `O(x/(log x)^20)` |
| `ChenTheorem/Analysis/{AnalyticLogBranch,ZeroFreeLogDerivative}.lean` | Holomorphic normalized logarithms and the bound `224 M/R` for logarithmic derivatives on a three-quarter subdisk of a zero-free disk |
| `ChenTheorem/Lemma6/{LFunctionEulerBounds,LFunctionDiskLogDerivative}.lean` | Two-sided Euler/Möbius series bounds to the right of one and an explicit primitive L-function logarithmic-derivative bound conditional only on a zero-free disk |
| `ChenTheorem/Lemma6/{ZeroFreeRegionData,ZeroFreeWidthGeometry,ZeroFreeRegionDisks,ZeroFreeWidthScale,ZeroFreeLogScale,ZeroFreeLogDerivativeBound,ZeroFreeRegionAssembly}.lean` | The original region interface and a complete derivation of its half-width `L'/L` estimate from mixed-region nonvanishing, with explicit disk geometry and conductor-height bounds |
| `ChenTheorem/Analysis/CompactZeroFreeStrip.lean` | Compactness gives local zero-free strips for fixed nontrivial characters and common strips for finite continuous families |
| `ChenTheorem/Lemma6/CompactDirichletFamily.lean` | A common strip for all nonprincipal characters with bounded conductor and height, and extension of a mixed region across a bounded conductor-height box |
| `ChenTheorem/Lemma6/{DirichletPhase,DirichletLogDerivativePositivity}.lean` | The classical three-four-one logarithmic-derivative inequality, proved from nonnegative von Mangoldt series terms |
| `ChenTheorem/Lemma6/LFunctionZeroCount.lean` | An unconditional Jensen bound for zeros with multiplicity in disks centered at `5/4+it` and reaching to the left of one |
| `ChenTheorem/Analysis/{BlaschkeFactor,DiskBlaschkeProduct,AnalyticZeroFactorization,ZeroFreeFactorBounds,BlaschkeLogDerivative,DiskZeroLogDerivative,DiskZeroCount,LocalZeroLogDerivative,LocalZeroLogDerivativeBound}.lean` | Exact finite zero factorization, boundary and center norm control, and a local logarithmic-derivative expansion with all zero-count and remainder bounds proved |
| `ChenTheorem/Lemma6/{LFunctionLocalZeroLogDerivative,LFunctionLocalZeroScale}.lean` | A primitive L-function local zero-pole expansion with error at most `60000 log(q(abs(t)+2))`, without assuming a zero-free disk |
| `ChenTheorem/Lemma6/ZeroFreeRegion.lean` | The single remaining `sorry`: uniform mixed-region nonvanishing at every fixed Siegel exponent; the companion derivative bound is supplied by the proved assembly theorem |
| `ChenTheorem/Lemma6/Equation21.lean` | The complete equation-(21) pipeline from that interface: the unsplit logarithmic-derivative integrand, holomorphy inside the region, Cauchy–Goursat on `[1-1/√(log x), α]` rectangles, horizontal-edge decay from the kernel's half-power decay, and the final character-level bound `≪ (log x)^90 · Σ (x/p₁p₂)^{1-1/√(log x)}` |
| `ChenTheorem/Lemma6/Core.lean` | The finite `N_m`, its small/large-conductor split, equations (12)–(21), and the proved final logarithmic deduction for Lemma 6 |
| `ChenTheorem/Main/NumericalBounds.lean` | Independent, `sorry`-free analytic proofs of the numerical integral bounds (24) and (27), with exact rational remainder estimates |
| `ChenTheorem/Lemma8/PrimeReciprocal.lean` | The prime-reciprocal Mertens theorem from the locally included analytic proofs, exact Abel-summation formulas, both partial-summation steps between (23) and (24), and uniform error control |
| `ChenTheorem/Lemma9/BombieriVinogradov/` | The completed standalone level-`1/2` Bombieri--Vinogradov proof: exact character and primitive-conductor reductions, Vaughan decomposition, Type-I and Type-II large-sieve estimates, sharp boundary and imprimitive-character errors, finite-contour Siegel--Walfisz estimates for arbitrary fixed polylogarithmic conductor ranges, and the final theorem `bombieriVinogradov : Statement`, conditional only on `primitive_zero_free_region` |
| `ChenTheorem/Lemma9/RichertBombieri.lean` | Proved equation (26) for the original and fixed-shift families; no extra sieve axiom, inheriting only the zero-free-region gap through BV |
| `ChenTheorem/Lemma9/LinearSieve/{Basic,Rosser,RosserWeights,RosserSieve}.lean` | Constructed finite Rosser lower/upper coefficients, strict level support, unit coefficient bound, unique prime-string expansion, and exact main-term/remainder bounds; the subsequent modules complete the asymptotic proof |
| `ChenTheorem/Lemma9/BombieriVinogradov/PrimeWeights.lean` | Conversion from the existing von-Mangoldt BV statement to prime logarithmic weights, including uniform prime-power error control and arbitrary reduced residues |
| `ChenTheorem/Lemma9/LinearSieve/{PrimeSequence,PrimeSubsequence,MiddlePrimeErrors,WeightedPrimeSieve}.lean` | Actual `x-p` prime sequences, density `1/φ(d)`, exact progression remainders, multiplicity-one middle-prime modulus sums, and separate/combined logarithmically weighted Rosser bounds with BV remainder control |
| `ChenTheorem/Lemma9/LinearSieve/{LogWeights,SmallPrimeLoss,ReducedPrimeCounts,ChenPrimeCounts,CountCutoff}.lean` | Ordinary-count conversion with aggregate small-prime loss `5 ceil T`, non-reduced-class loss at most `3/2` times the number of prime factors of `x`, exact identification with the original Chen counts, a finite Rosser bound for those counts, and logarithmic cutoff control; the subsequent modules complete the asymptotic proof |
| `ChenTheorem/Analysis/MertensProduct.lean` and `Analysis/PNT/IEANTN/Mertens.lean` | Locally included, kernel-audited proof of Mertens' third theorem and natural-cutoff Euler product normalization |
| `ChenTheorem/Lemma9/LinearSieve/{SieveProduct,DivisorProductTail,SieveProductAsymptotics,PowerSieveCutoff,ChenSieveNormalization}.lean` | Exact density-product factorization, uniform prime-divisor tail bounds and equation-(25) normalization: the actual sieve product times `log x / C_x` tends to `20 exp(-γ)`; this establishes vanishing relative error, not the paper's stronger printed error rate |
| `ChenTheorem/Lemma9/LinearSieve/{CountLossAsymptotics,CountAsymptoticSieve,PowerSieveLevel}.lean` | All original count-conversion and BV losses absorbed into arbitrary `δ xC_x/log² x`; explicit valid levels `Q=floor(x^a)` and `floor(Q/k)` for `1/3<a<1/2`, leaving the sharp Rosser main terms to be estimated |
| `ChenTheorem/Lemma9/LinearSieve/{ShiftedPrimeSequence,ShiftedPrimeSubsequence,ShiftedWeightedPrimeSieve}.lean` | Actual translated prime sequence `p+h`, exact remainders in `-h mod d`, and separate finite/BV logarithmic bounds without added modulus multiplicity |
| `ChenTheorem/Lemma9/LinearSieve/{ShiftedLogWeights,ShiftedReducedPrimeCounts,ShiftedChenPrimeCounts}.lean` | Exact connection to existing shifted counts, with small-prime loss `5 ceil T` and non-reduced-class loss `3ω(h)/2` |
| `ChenTheorem/Lemma9/LinearSieve/{ShiftedSieveNormalization,ShiftedCountLossAsymptotics,ShiftedCountAsymptoticSieve}.lean` | Fixed-shift singular-series normalization, arbitrary-precision error absorption, and an explicit power-level count bound; the subsequent modules complete the asymptotic proof |
| `ChenTheorem/Lemma9/LinearSieve/{DensityInterval,DensityRatio,DensityQuantitative}.lean` | Positive exact product ratios and the quantitative dimension-one bound `(1+K/log w) log z/log w`, uniform over all finite odd-prime subsets and natural endpoints `2≤w≤z` |
| `ChenTheorem/Lemma9/LinearSieve/{RosserDefect,BuchstabMeasure}.lean` | Nonnegative Rosser error recursions, normalized main-term reconstruction, and exact cumulative Buchstab masses; the subsequent modules complete the asymptotic proof |
| `ChenTheorem/Lemma9/LinearSieve/{AbelTail,DensityReal,WeightedBuchstab,BuchstabIntegral,BuchstabError}.lean` | Real-cutoff dimension-one bounds, exact weighted Abel identities, and continuous Buchstab comparison with explicit error `2K f(z)/log w` for differentiable nonnegative increasing weights satisfying the logarithmic growth bound; the subsequent modules complete the asymptotic proof |
| `ChenTheorem/Lemma9/LinearSieve/{SieveParameter,BuchstabParameter,RosserIntegralStep,RosserExactLevel}.lean` | Exact logarithmic substitution, parameter-integral comparison for admissible smooth envelopes, an actual Rosser recursion step with an explicit small-prime remainder, and eventual exact vanishing of that remainder at a fixed cutoff; the subsequent modules complete the asymptotic proof |
| `ChenTheorem/Lemma9/LinearSieve/{ContinuousTail,ContinuousTerms,ContinuousTailDerivative,ContinuousTermDerivative,ContinuousPartials}.lean` | Actual beta-two continuous terms, positivity, continuity, support and weighted monotonicity; derivative formulas on the stated open intervals and the finite odd/even delay system |
| `ChenTheorem/Lemma9/LinearSieve/{ContinuousTailMass,ContinuousMass,ContinuousConvergence,ContinuousErrors,ContinuousErrorDerivative}.lean` | Exact mass telescoping proves convergence of both parity series; half-line uniform convergence, continuity, bounds and rigorously differentiated limiting delay equations |
| `ChenTheorem/Lemma9/LinearSieve/{ContinuousErrorDecay,ContinuousInitial,ContinuousPairing,ContinuousEndpoint,ContinuousFunctions}.lean` | Weighted errors tend to zero; a conserved integral pairing proves the sharp lower endpoint value; the constructed functions satisfy `F=A/s` on `1<s≤3`, `f=A log(s-1)/s` on `2≤s≤4`, both delay equations and limits equal to one; the discrete comparison and calibration `A=2 exp γ` are completed in subsequent modules below |
| `ChenTheorem/Lemma9/LinearSieve/{ContinuousErrorRegularity,ContinuousUpperSmooth,ContinuousErrorIntegrals,ContinuousBuchstab,RosserContinuousStep}.lean` | The actual error functions satisfy the Buchstab comparison hypotheses, including the upper derivative at the joining point; concrete Rosser steps hold for upper `s>3` and active lower `s>2`, with explicit density errors and a scalable child-state induction hypothesis; uniform cutoff induction is proved in RosserUniformError |
| `ChenTheorem/Lemma9/LinearSieve/{RosserUpperTransport,RosserUpperComparison,RosserCubeCutoff,RosserUpperInitial}.lean` | Exact upper-polynomial transport beyond the cube-root cutoff and a uniform reduction of `1<s≤3` to a local error bound at parameter `s_m>3`, with `s_m→3`; the subsequent modules complete the asymptotic proof |
| `ChenTheorem/Lemma9/LinearSieve/{RosserStoppingMass,RosserChainBound,RosserDepthTail,RosserMassLogBound,RosserLargeParameter}.lean` | Exact decomposition of the actual defect by stopping depth, factorial bounds for decreasing chains and the depth remainder, and a uniform large-parameter bound with no child-state assumptions |
| `ChenTheorem/Lemma9/LinearSieve/{RosserStoppingParity,RosserFirstMass,RosserFirstComparison,RosserDepthRecursion}.lean` | Depth parity, the exact first stopping contribution and its uniform continuous comparison for `s>1`, plus normalized depth recursion and explicit power levels eliminating each fixed-depth prefix |
| `ChenTheorem/Lemma9/LinearSieve/{AbelRight,BuchstabRight,ContinuousTermJunction,BuchstabTerm}.lean` | Abel and Buchstab estimates for integrable right derivatives, left derivatives of the recursive continuous terms at their junctions, and a Buchstab bound by the next continuous term with explicit density error |
| `ChenTheorem/Lemma9/LinearSieve/{BuchstabFirstTerm,RosserDepthComparison,RosserSecondComparison}.lean` | The first-term junction, a common Buchstab constant for every positive depth, exact propagation of additive child errors by the tail mass, and a second-depth estimate with all child assumptions discharged by a minimum-level condition |
| `ChenTheorem/Lemma9/LinearSieve/RosserSecondUniform.lean` | Choosing `w=D^(1/8)` proves a uniform second-depth bound by `f₂+ε` for every terminal cutoff at least two, including stopped and small-cutoff cases, and the prime-cutoff version needed by the next depth |
| `ChenTheorem/Lemma9/LinearSieve/{RosserDepthTransport,RosserDepthInitial}.lean` | Exact cube-cutoff transport for every upper depth at least two and transfer of a fixed-depth comparison from `s>3` to all `s>1`; RosserFixedDepth discharges the large-parameter induction hypothesis |
| `ChenTheorem/Lemma9/LinearSieve/{RosserDepthSplit,RosserDepthStep,RosserFixedDepth}.lean` | A general power split and induction prove the uniform continuous comparison for every fixed positive depth and every fixed finite sum of depths; thresholds may depend on depth; later cutoff induction controls the full defect |
| `ChenTheorem/Lemma9/LinearSieve/RosserGrowingTail.lean` | The actual relative defect after depth `ceil(6 log B(z)/log 2)` has nonnegative remainder at most `1/B(z)^2`, tending to zero uniformly in the level and prime set; `B(z)` is a fixed positive multiple of `log z` |
| `ChenTheorem/Lemma9/LinearSieve/ContinuousAuxiliary.lean` | Nonnegative auxiliary errors constructed from the actual error derivatives, their initial formulas, continuity across the lower endpoint, delay equations with weight `s²`, and weighted monotonicity; the initial constant is not assumed to equal `2 exp(γ)` |
| `ChenTheorem/Lemma9/LinearSieve/ContinuousAuxiliaryIntegrals.lean` | The weighted auxiliary errors tend to zero; exact finite-interval integrals retain the terminal term, include the joining endpoints, and imply improper-integral limits and finite integral upper bounds |
| `ChenTheorem/Lemma9/LinearSieve/{ContinuousAuxiliaryWeights,AuxiliaryLevelError}.lean` | Weighted auxiliary integral bounds, weighted monotonicity, and the exact logarithmic error rescaling at child level `D/p`; the basic scale tends to zero for fixed parameters, but discrete density errors and the extra uniformity factors still need control |
| `ChenTheorem/Lemma9/LinearSieve/{AuxiliaryJunction,AuxiliaryWeightDerivative,BuchstabAuxiliary,AuxiliaryChildSum}.lean` | Left derivatives through the auxiliary junctions give nonnegative integrable right derivatives after parameter reversal; actual discrete child-level error sums are bounded by the parent error scale plus an explicit terminal density error, which still needs absorption |
| `ChenTheorem/Lemma9/LinearSieve/{AuxiliaryMajorant,BuchstabPartials,RosserPartialDefect,RosserPartialComparison}.lean` | Uniform auxiliary majorants for continuous partial sums and an exact cumulative discrete recurrence give upper/lower conditional depth steps with constants independent of the cutoffs; child hypotheses, the active-branch condition, the small-prime prefix and both density errors remain explicit |
| `ChenTheorem/Lemma9/LinearSieve/{ContinuousPositivity,AuxiliaryStrictContraction}.lean` | Strict positivity of the actual continuous terms, errors and auxiliary functions; for each fixed parameter and logarithmic exponent below one, the weighted auxiliary integral has a positive gap uniform in every upper endpoint at least one unit away; quantitative control as the parameter grows is still required |
| `ChenTheorem/Lemma9/LinearSieve/{AuxiliaryLowerStep,AuxiliaryLowerBound,AuxiliaryExponentialLowerBound}.lean` | Short-interval delay integrals give a simultaneous quantitative induction with a free step length; both auxiliary functions are bounded below by `c exp(-s log s - s log log s - 6s)` for `s≥3`, `log s≥2`, with one proved positive constant; later modules complete the shift ratios and uniform sieve estimates |
| `ChenTheorem/Lemma9/LinearSieve/{AuxiliaryInflation,InflatedAuxiliaryError,AuxiliaryInflationDerivative,InflatedAuxiliaryLowerBound}.lean` | The additional factor `(1+s^d/log D)^s`, its actual child-level comparison, fixed-parameter limits, shifted derivative bound and explicit lower bound for the full auxiliary error; the weighted decreasing product is proved in the later modules, and uniform cutoff induction is proved below |
| `ChenTheorem/Lemma9/LinearSieve/{FactorialExponentialTail,RosserParameterExponential,RosserAuxiliaryComparison}.lean` | Exponential-series control of factorial tails, the actual depth `floor(s)-2` and an explicit exponential comparison of the full discrete defect with both inflated auxiliary errors; the growing-parameter estimate is completed in the following modules |
| `ChenTheorem/Lemma9/LinearSieve/{ComparisonEnvelope,GrowingSieveParameter,DepthMassLevelBound,GrowingEnvelopeLimit,RosserGrowingParameter}.lean` | A decreasing envelope and the split `σ=L^(1/d) log L` prove `defect ≤ exp(-s) · inflated auxiliary error` uniformly for all `s≥σ(log D)`, cutoffs, odd prime sets and sieve signs at sufficiently large levels, for fixed `d>2` and real `δ` |
| `ChenTheorem/Lemma9/LinearSieve/{RosserPrefixNormalization,GrowingPrefixCutoff,GrowingPrefixRatio,RosserGrowingPrefix}.lean` | The actual rounded prefix at `m=floor(exp(log D/(2σ)))` has parameter `t∈[σ,2σ]` and stays active; exact product normalization and the density condition give a bound `C(σ/s) exp(-σ) E(D,t)` uniform in depth and the prime set; the later transport theorem transfers this to the parent parameter |
| `ChenTheorem/Lemma9/LinearSieve/{AuxiliarySumPairing,AuxiliarySumDecay,AuxiliaryExponentialDecay}.lean` | The actual auxiliary sum satisfies the scalar delay equation and a vanishing pairing with `q(s)=s²−2s+1/2`; elementary shift bounds and a second use of the pairing prove `upper/lower auxiliary error ≤ C exp(-s)` for `s≥16`; the stronger logarithmic shift ratios are supplied by the later modules |
| `ChenTheorem/Lemma9/LinearSieve/{AuxiliaryDifferencePairing,AuxiliaryComparability,AuxiliaryShiftComparison}.lean` | A second vanishing pairing and a maximum principle prove uniform comparability of both auxiliary errors to their sum on `[2,∞)`; both cross-shift ratios are uniformly comparable to `Q(s−1)/(sQ(s))`; the scalar logarithmic estimates are supplied below |
| `ChenTheorem/Lemma9/LinearSieve/{AuxiliaryBarrierPhase,AuxiliaryBarrierKernel,AuxiliaryBarrierIntegral,AuxiliaryBarrierCritical,ContinuousFirstZero,AuxiliaryLogarithmicLower}.lean` | Explicit unit-interval kernel estimates and exclusion of a first stationary point prove `Q(s−1)/(sQ(s)) ≥ (1/4) log s` eventually; both cross-shift ratios therefore have uniform logarithmic lower bounds |
| `ChenTheorem/Lemma9/LinearSieve/{AuxiliaryBarrierKernelLower,AuxiliaryBarrierIntegralLower,AuxiliaryBarrierUpperCritical,AuxiliaryLogarithmicUpper,AuxiliaryUniformShift}.lean` | The opposite comparison proves the scalar upper bound `r(s) ≤ 9 log s` eventually; compactness extends both scalar and cross-shift bounds uniformly to all `s≥3`, with fixed positive constants |
| `ChenTheorem/Lemma9/LinearSieve/{InflationLogBounds,InflationSlopeLimit,InflatedAuxiliaryMonotonicity,InflatedAuxiliaryTransport,RosserParentPrefix}.lean` | Uniformly small logarithmic slopes prove shifted inflated weighted errors antitone on `[3,2σ]`; transport by `s/t` gives the actual prefix bound `C exp(-σ) E(D,s)` and absorption into any fixed positive fraction of the parent error, uniformly in depth and prime sets; later modules complete middle-range absorption and uniform cutoff induction |
| `ChenTheorem/Lemma9/LinearSieve/{AuxiliaryLowerInitialShift,InflationInitialSlope,InflatedLowerMonotonicity,InflatedChildWeight,InflatedChildInitialWeight,InflatedPrimeWeight}.lean` | Initial formulas extend lower cross-shift bounds to `s>2` and lower inflated monotonicity to `[2,2σ]`; factorization and the upper initial formula prove weighted child monotonicity on both full required domains, hence ordinary monotonicity and logarithmic growth in the prime-size variable |
| `ChenTheorem/Lemma9/LinearSieve/{BuchstabMonotoneRight,ChildInflationDerivative,InflatedWeightRegularity,BuchstabInflatedParameter,BuchstabInflated,InflatedAuxiliaryChildSum}.lean` | Monotonicity supplies the interior derivative sign; the integrable one-sided product derivative proves Buchstab bounds for both actual inflated child-level error sums, with explicit integral and terminal loss; no regularity or shape assumptions remain in the specializations |
| `ChenTheorem/Lemma9/LinearSieve/{InflationContractionGap,InflationSlopeGap,InflatedAuxiliaryDissipation,InflatedAuxiliaryIntegral,InflatedAuxiliaryContraction,InflatedContractedChildSum}.lean` | The combined loss from the child denominator and error exponent dominates twice the inflation slope; integrating the parent derivative yields quantitative contraction, hence both true child-error sums are bounded by `(1−(1−δ)/(4B))` times the parent error plus explicit terminal density loss |
| `ChenTheorem/Lemma9/LinearSieve/{GrowingDensityBudget,InflatedTerminalLoss,InflatedTerminalAbsorption,InflatedAbsorbedChildSum}.lean` | The terminal density loss is absorbed uniformly; the actual child-error sums retain factor `1−(1−δ)/(16σ)` for `d>3` and `0≤δ<1` |
| `ChenTheorem/Lemma9/LinearSieve/{ContinuousTerminalLoss,ContinuousTerminalAbsorption,RosserInflatedStep}.lean` | Under `3/d<1−δ`, the continuous main-term density error is also absorbed in the actual active depth step, uniformly in both depths, with the small-prime prefix retained |
| `ChenTheorem/Lemma9/LinearSieve/{RosserPrefixAbsorption,RosserInflatedParentStep}.lean` | The prefix is smaller than any prescribed multiple of `E/σ`, including the lower endpoint two; absorption and monotonicity align the step with the actual parent cutoff `z+1`, retaining factor `1−(1−δ)/(64σ)` and an explicit child hypothesis |
| `ChenTheorem/Lemma9/LinearSieve/{ContinuousPartialLimits,BuchstabErrors,RosserStoppedError}.lean` | Passage to full continuous errors preserves the Buchstab density constant; `L(s)=2/s` for `0<s≤2` controls stopped lower branches at every depth and for the total defect |
| `ChenTheorem/Lemma9/LinearSieve/{RosserFullErrorStep,RosserFullErrorParentStep,RosserFullDefectStep}.lean` | Both absorbed steps now compare actual total Rosser defects with full continuous errors at the exact parent and child cutoffs; the quantitative contraction remains, while child defect bounds are explicit hypotheses |
| `ChenTheorem/Lemma9/LinearSieve/RosserBoundedLevel.lean` | One multiplier controls all bounded levels, cutoffs and odd prime sets, for both signs and both full auxiliary errors; the initial upper interval and global induction are assembled below |
| `ChenTheorem/Lemma9/LinearSieve/{CubeCutoffRounding,InitialInflationBudget,RosserUnroundedPrefix,RosserCubeErrorStep,CubeInitialBudget,InitialTransferAlgebra,RosserInitialErrorTransfer}.lean` | Quantitative cube-rounding, density and inflation losses are absorbed; the contracted cube estimate transfers over the entire initial upper interval with the same error multiplier |
| `ChenTheorem/Lemma9/LinearSieve/{RosserInductionParameters,RosserUniformError,RosserAsymptoticError}.lean` | Strong induction on the cutoff proves actual total-defect bounds uniformly in every level and prime set, without child assumptions; compact-parameter limits yield the constructed F/f polynomial bounds, with the initial constant calibrated in the modules below |
| `ChenTheorem/Lemma9/LinearSieve/{BuchstabFunction,BuchstabLaplace,BuchstabLaplaceEquation,BuchstabAbelian}.lean` | The constructed Buchstab function, its delay equation and Laplace ODE; a dilation and dominated convergence prove the scaled transform limit `2/A` |
| `ChenTheorem/Lemma9/LinearSieve/{EulerGammaIntegral,ExponentialIntegral,BuchstabLaplaceEvaluation,InitialConstantCalibration,CalibratedRosserBounds}.lean` | Gamma integral evaluation, `E₁(t)+log t→−γ`, exact Laplace transform, calibration `A=2 exp γ`, and classical numerical Rosser bounds on the initial intervals |
| `ChenTheorem/Lemma9/LinearSieve/{SecondInterval,LowerSecondInterval,WeightedProfileIntegral,ChenProfileIdentity,ProfileContinuity}.lean` | Explicit second-interval F/f formulas and f(5); the weighted upper integral combines exactly into equation (26), and continuity provides every positive loss at levels a<1/2; discrete prime sums still need to be assembled |
| `ChenTheorem/MainEstimates.lean` | Lemmas 5–9: the sieve decomposition, `M₁ ≤ …`, `Ω ≤ 3.9404 xC_x/(log x)²`, the Richert-sieve lower bound `≥ 2.6408 xC_x/(log x)²` |
| `ChenTheorem/Lemma9/LinearSieve/{PrimeAbelAbsolute,UpperPrimeWeight,LogPowerSubstitution,UpperPrimeSumLimit,MidPrimeSumLimit}.lean` | Actual weighted prime sums converge to Chen's continuous upper-profile integral, including replacement of `1/p` by `1/φ(p)` |
| `ChenTheorem/Lemma9/LinearSieve/{RoundedLevelBounds,PowerParameterLimits,ChildParameterApproximation,PowerRosserBounds}.lean` | Uniform rounded parent/child level estimates and actual Rosser bounds at the continuous profile arguments |
| `ChenTheorem/Lemma9/LinearSieve/{WeightedRosserSum,NormalizedRosserProfile,CountProfileBounds}.lean` | Weighted child sums, normalized Rosser main terms, and both count lower bounds for every constant below the continuous profile |
| `ChenTheorem/Main/KeyInequality.lean` | Complete proof of inequality (28): finite partition, two-witness injection, repeated-prime encoding of nonsquarefree exceptions, and the `O(x^0.9)` reciprocal-square tail |
| `ChenTheorem/Main/ShiftedDefs.lean` | Fixed-shift versions of the roughness predicate, sieve weights, divisor and character expansions, error terms, and sifted counting functions; the shift `h` is kept separate from the scale `x` |
| `ChenTheorem/Main/ShiftedSieveLemmas.lean` | Parallel Lemmas 1--4 for Theorem 2, proved by reusing the residue-independent original theorems (including the corrected height-logarithmic Lemma 3) |
| `ChenTheorem/Main/ShiftedLemma5.lean` | The shifted Lemma 5 core: weight support and pointwise bounds, small-third-prime tail, character orthogonality, and the Selberg-square/smoothed-sieve expansion |
| `ChenTheorem/Main/{ShiftedLemma5Boundary,ShiftedLemma5Arithmetic}.lean` | The smoothing-boundary estimate, shifted `M3`/`M5` arithmetic errors, and the completed final estimate `shiftedSieveOmega_le_mOne_add_mTwo` for shifted Lemma 5 |
| `ChenTheorem/Main/ShiftedLemma6.lean` | The shifted Lemma 6 conductor decomposition, reduction to the finite `N_m` of equation (12), the completed small-conductor equation-(21) contour estimate, and the interfaces for the large-conductor dyadic blocks |
| `ChenTheorem/Main/ShiftedLemma6Large.lean` | Completion of shifted Lemma 6: scalar block majorants, cutoff/logarithm and mollifier-scale estimates, both A/B contributions in equations (19)--(20), the per-block bounds, and the final large-conductor `N_m` and `M2` logarithmic estimates |
| `ChenTheorem/Main/ShiftedLemma7.lean` | The shifted Lemmas 5--6 combination and the algebraic part of shifted Lemma 7, including Selberg diagonalization, the shifted Moebius transform, and the exact normalization identity (22) |
| `ChenTheorem/Main/ShiftedLemma7Normalization.lean` | Dyadic comparison of the fixed-shift normalization with the unshifted Lemma 7 normalization, the coefficient bound, and the completed shifted `M1` estimate with coefficient `8 + 24 * epsilon` |
| `ChenTheorem/Main/ShiftedLemma8.lean` | The completed shifted Lemma 8, reusing the shift-independent prime-pair kernel and proving `shiftedSieveOmega ≤ 3.9404 x C_h/(log x)^2` |
| `ChenTheorem/Main/ShiftedLemma9.lean` | The completed numerical deduction for shifted Lemma 9 from the fixed-shift instance of the common Richert--Bombieri interface |
| `ChenTheorem/Main/ShiftedKeyInequality.lean` | Fixed-shift inequality (28): prime-factor classification, two-witness injection, endpoint and nonsquarefree exception bounds, and the final `x^0.91` loss |
| `ChenTheorem/Main/ShiftedEstimate.lean` | Complete aggregation of shifted Lemmas 1--9 and inequality (28), including the `0.67` numerical gap and the even-floor argument removing the auxiliary parity restriction on the scale |
| `ChenTheorem/Main.lean` | Completed deductions of inequality (28), Theorem 1 (`P_x(1,2) ≥ 0.67 xC_x/(log x)²` and Chen's theorem proper), and Theorem 2 (twin analogue) from the named upstream estimates |

## Correspondence with the paper

| Paper | Lean |
|---|---|
| `(1,2)`, `P₂` numbers | `Chen.IsP2` |
| `P_x(1,2)` | `Chen.chenCount` |
| `x_h(1,2)` | `Chen.chenCountShift` |
| `C_x` | `Chen.chenConst` (with `Chen.twinConst` the infinite product) |
| `Φ(y)` (Lemma 1) | `Chen.chenPhi` (defined via the incomplete-gamma formula derived inside Lemma 1, rather than the contour integral) |
| `f(k)`, `S`, `λ_d` | `Chen.fW`, `Chen.sieveNorm`, `Chen.sieveWeight` |
| `Ω` | `Chen.sieveOmega` |
| `M₁` | `Chen.mOne` |
| Lemma 1 | `chenPhi_eq_zero`, `chenPhi_monotoneOn`, `chenPhi_nonneg`, `chenPhi_le_one`, `chenPhi_ge` (**all five proved**) |
| Lemma 2, eqs. (2)–(3) | `large_sieve`, `large_sieve_dyadic` |
| Lemma 3 | `lFunction_fourth_moment_with_height_log` proves the corrected height-logarithmic form on `2 ≤ q ≤ Q`; the printed log-`Q`-only claim remains documented as `Lemma3FourthMoment` but is not asserted as a theorem |
| Lemma 4 | `primitive_char_sum_bound` (general squarefree `k`, **proved**); `primitive_char_sum_bound_prime` (prime case, **proved**) |
| Lemma 5 | `sieveOmega_le_mOne_add_mTwo` (**proved**) |
| Lemma 6 | `mTwo_le` (final deduction **proved** from the stronger `mTwo_le_log12`); equations (12)–(21) are all proved, and the corrected Lemma-3 height logarithm is carried through the Cauchy/Hölder/kernel estimates. The only remaining analytic input is the classical zero-free region `primitive_zero_free_region` |
| Lemmas 5–6 combined | `sieveOmega_le_mOne` (deduction **proved**; depends on the pending Lemma 6 input) |
| Lemma 7 | `mOne_le` (**proved**); `eventually_smoothed_pair_mass_le` is derived from `Chen.chebyshevPsi_isEquivalent` and the uniform lower bound `x^(1/3) < x/(p₁p₂)`, while the Selberg normalization, positivity, summation, and constants are all machine-checked |
| Equation (24) | `equation24_integral_bound` (**proved**, no `sorryAx`) |
| Lemma 8 | `sieveOmega_le` (**proved**); `primeReciprocal_mertens` is obtained from the locally included analytic proofs, and the two Abel-summation steps, uniform Mertens-error control, `eventually_chenPairs_kernel_le_integral_add`, error conversion, and the numerical integral are all machine-checked. The theorem inherits only the pending Lemma 6 zero-free-region input through `sieveOmega_le_mOne` |
| `P_x(x, x^{1/10})`, `P_x(x, p', x^{1/10})` | `Chen.sievedPrimeCount`, `Chen.sievedPrimeCountAt` |
| Equation (27) | `equation27_integral_bound` (**proved**, no `sorryAx`) |
| Lemma 9 | `sieved_lower_bound` (**proved** from the locally proved Richert–Bombieri specialization; equation (27), loss management, and the final numerical deduction are machine-checked, inheriting only the zero-free-region input) |
| Inequality (28) | `key_inequality` (**proved**) |
| Theorem 1 | `chenCount_lower` (quantitative), `chen_theorem` (qualitative), both deductions proved |
| Theorem 2 | `chenCountShift_lower`, `chen_twin` (**proved** from the complete shifted Lemmas 1--9 and shifted inequality (28), conditional only on the shared zero-free-region input) |

## Design notes / deliberate simplifications

* **`≪` constants.** Vinogradov `≪` statements are rendered as `∃ C > 0, …`;
  "for all sufficiently large even `x`" is rendered as
  `∀ᶠ x in atTop, Even x → …`.
* **`Φ` via a real integral — Lemma 1 fully proved.** The paper defines `Φ` by a
  vertical contour integral and *proves* (inside Lemma 1) that it equals a
  normalized incomplete gamma integral for `y ≥ 1`. We adopt the latter as the
  definition, turning the whole of Lemma 1 into a statement in real analysis,
  and all five of its parts are proved (no `sorry`):
  `n! · Φ(y) = ∫_{(0, a(y)]} e^{-t} t^n dt` with `a(y) = (log x)^{1.1} log y`,
  `n = ⌊log x⌋`, compared against the convergent Euler integral
  `n! = ∫_{(0,∞)} e^{-t} t^n dt` (`Real.Gamma_eq_integral` specialized to
  `s = n + 1`, via `Real.Gamma_nat_eq_factorial`).
  * *Vanishing on `[0,1]`, nonnegativity, `≤ 1`* (`chenPhi_eq_zero`,
    `chenPhi_nonneg`, `chenPhi_le_one`): `log x > 0` (as `x > 1`) forces
    `a(y) ≤ 0` on `[0,1]`, emptying the defining interval `Ioc 0 (a y)`;
    nonnegativity and the bound `≤ 1` follow by comparing that interval's
    integral against `Ioi 0` (`MeasureTheory.setIntegral_nonneg`,
    `MeasureTheory.setIntegral_mono_set`).
  * *Monotonicity* (`chenPhi_monotoneOn`): splits on `y ≤ 1` (constant `0`) vs.
    `y > 1` (genuine monotonicity of `log`, hence of `a(y)`, hence of the
    growing-interval integral).
  * *The quantitative tail bound* (`chenPhi_ge`, the hardest part): reduces
    `1 - Φ(y)` to `(n!)⁻¹ ∫_{(a(y),∞)} e^{-t}t^n dt` via
    `Ioc 0 a ∪ Ioi a = Ioi 0`; bounds this by `(n!)⁻¹ ∫_{(2n,∞)}` since
    `a(y) ≥ 2n` follows from the hypothesis on `y`; rescales
    `t = nx` (`MeasureTheory.integral_comp_mul_left_Ioi`) to reduce to
    `∫_{(2,∞)} e^{-nx}x^n dx`; bounds the integrand there by
    `e^{n(log2-1)}e^{-nx/2}` using the concavity tangent line
    `log t ≤ t - 1` of `Real.log_le_sub_one_of_pos` (applied at `t = x/2`, so
    `log x ≤ log 2 + x/2 - 1`, tight at `x = 2`) via
    `MeasureTheory.integral_mono_of_nonneg` (which needs only the *majorant*'s
    integrability, not the integrand's); and closes the loop with the
    elementary factorial bound `n^n ≤ n! · eⁿ`, obtained from Mathlib's
    Stirling inequality `Stirling.le_factorial_stirling` by discarding the
    `√(2πn) ≥ 1` factor. The final numeric inequality has enormous slack
    (`log x ≥ 10⁴` against a requirement of roughly `log x ≥ 5`), so a loose
    bound `log 2 < 0.7` (`Real.log_two_lt_d9`) suffices throughout.
* **Lemma 4, proved.** For a prime modulus `p`, every nontrivial
  character is automatically primitive: its conductor divides `p`
  (`DirichletCharacter.conductor_dvd_level`), hence is `1` or `p`, and conductor
  `1` forces the character trivial (`DirichletCharacter.eq_one_iff_conductor_eq_one`).
  So `∑*_{χ mod p} χ(m) = (∑_{all χ} χ(m)) - χ₀(m)`, and both terms are computed
  in closed form: the first via Mathlib's orthogonality relation
  `DirichletCharacter.sum_characters_eq` (`= φ(p)` if `m ≡ 1 mod p`, else `0`),
  the second via `MulChar.one_apply`/`MulChar.map_nonunit` (`= 1` if `(m,p)=1`,
  else `0`). A three-way case split on `(m mod p = 1)` and `(m,p) = 1` then
  matches the bound `≤ (m-1,p)` exactly (with equality in the "generic" case
  `p ∤ m(m-1)`). This is a genuinely different — and shorter — route than the
  paper's own prime-modulus proof (which builds primitive characters explicitly
  from a primitive root mod `p`). For coprime moduli `a,b`, the formalization
  constructs the CRT equivalence between characters mod `ab` and pairs of
  characters mod `a,b`, proves that conductors multiply, and hence that
  primitivity and primitive character sums factor. Strong induction over a
  squarefree odd `k` then reduces the general bound to the prime case. The
  omitted case `(m,k) ≠ 1` in the paper is handled explicitly: every character
  value is zero.
* **Lemma 2, proved.** A centered-interval Sobolev inequality is applied to a
  trigonometric polynomial; Parseval and Farey-fraction separation give the
  additive large sieve. A machine-checked Gauss-sum identity and finite
  character orthogonality then give (2), including `|τ(χ)|² = q`. Covering
  `(D,Q]` by disjoint blocks `(2ⁱD,2ⁱ⁺¹D]` gives (3), with the explicit
  universal constant `8 + 2π`.
* **Lemma 6 / `M₂`.** The finite character-sum form of `M₂` is defined and
  Lemma 5 retains it explicitly:
  `Ω ≤ (M₁+M₂)/(1-ε) + O(x (log x)^{-2.01})`.  The estimate
  `M₂ ≪ x (log x)^{-2.01}` is now fully reduced, by machine-checked proofs,
  to the documented classical zero-free region with companion `L'/L` bound
  (`primitive_zero_free_region`).  The corrected Lemma-3 fourth moment is now
  proved and instantiated in the pipeline.  In particular
  `lemma6_large_pair_block_estimate_of_deriv_fourth_moment` (equations
  (13)–(20)) does not depend on `sorryAx` — its `Lemma 3` dependence is
  explicit in the hypothesis — and the equation-(21) small-conductor estimate
  is proved from `primitive_zero_free_region` alone.
* **Primitive character sums.** `Chen.primSum` sums over primitive
  `DirichletCharacter ℂ q` via a `tsum`, avoiding `Fintype` instance juggling for
  the degenerate modulus `q = 0` that never occurs in the ranges used.
  `DirichletCharacter.LFunction` additionally requires a `[NeZero q]` instance
  (it is undefined at `q = 0`), which a bound summation variable can't supply on
  its own; `Chen.lFourthTerm` works around this with a `dif` that produces `0`
  at `q = 0` and manufactures the instance from `q ≠ 0` otherwise.
* **Bound-variable type ascriptions.** Several `Finset.filter` predicates mix a
  natural-number membership test with real-exponent conditions, e.g.
  `fun k => 1 ≤ k ∧ (k : ℝ) ≤ x ^ (1/4) ∧ k.Coprime x`. Left unannotated, Lean's
  elaborator can process the real-number ascription before the ambient type of
  `k` is unified with `ℕ` (postponed dot-notation resolution), silently
  defaulting the bound variable to `ℝ`. Every such lambda is annotated
  `fun k : ℕ => …` to force the type immediately.
* **Theorem 2's constant.** The singular series for `p + h` is `chenConst h`
  (product over odd primes dividing `h`), which is what the paper's `C_x` means
  in that context.
* Everything is stated for **natural-number subtraction** `x - p`, harmless since
  all statements only concern `p ≤ x`.
* **`chenPhi_ge` needed an extra `1 < x` hypothesis.** `Real.log` in Mathlib is
  defined via `|x|` for negative reals, so `Real.log x ≥ 10⁴` alone does not
  pin `x` down to a large *positive* number (e.g. `x = -e^{10⁴}` also satisfies
  it) — and unlike `chenPhi` itself (which only ever sees `x` through `log x`),
  `chenPhi_ge`'s conclusion involves genuine real exponentiation `x ^ (-0.1 : ℝ)`
  directly, which behaves differently at negative bases. The other four parts
  of Lemma 1 already carried a `1 < x` hypothesis for the same reason; this one
  had been missing it and has been corrected to match.

## Status

See [STATUS.md](STATUS.md) for the current kernel audit, exact remaining proof
obligations, and the dependency migration. The main theorems are **not yet
unconditional**. Build success must not be confused with passing `Audit.lean`.

Builds with `lake build` (Lean `v4.32.2`, Mathlib `v4.32.2`) with zero errors.
The project contains exactly one documented `sorry`, in
`primitive_zero_free_region` (`Lemma6/ZeroFreeRegion.lean`), and no explicit
non-foundational axioms. The remaining input supplies the height-dependent
Dirichlet zero-free region and the arbitrary fixed Siegel exponent. The
companion `L'/L` bound required by Lemma 6 and Bombieri--Vinogradov is now
derived from mixed-region nonvanishing by `primitiveZeroFreeRegion_of_nonvanishing`.

`richert_bombieri_equation26` is now a theorem with its original statement.
The actual totient-weighted prime-sum limit, the uniform rounded child-level
approximation, and the parent/child Rosser bounds have been combined with
both families' count and BV remainder interfaces. The 43 new supporting
theorems are covered by `AuditSieve.lean`; the count-profile theorems take the
BV statement explicitly, and their kernel closures use only standard axioms.
The final unconditional wrappers use the existing BV theorem and therefore
still inherit the single zero-free-region `sorryAx`.

The remaining analytic work now has a proved disk estimate: a normalized
holomorphic logarithm and Borel--Carathéodory give `224 M/R` on a three-quarter
subdisk. Euler/Möbius series bounds and primitive L-function growth supply
an explicit arithmetic specialization. Disk containment and scale estimates
now extend it to the entire requested half-width region. The remaining
goal is mixed-region nonvanishing for primitive real characters. Additional proved
tools include compact local strips and the three-four-one inequality.
Finite Blaschke factorization and Jensen now give a local zero-pole expansion
with an absolute `60000 log(q(abs(t)+2))` remainder for primitive L-functions.
The uniform logarithmic zero-free region is now proved for primitive characters
with nonprincipal square, using zero-pole positivity, exact change-of-level
logarithmic derivatives, the zeta pole bound, and the three-four-one inequality.
`RealZeroFreeReduction` reduces the original remaining goal to primitive real
characters. Their nonexceptional region and Siegel estimates remain open.
For primitive real characters, conjugate-zero pairing now proves that any
zero in a uniform box of width and height `c/log(2q)` around 1 must be real;
any such zero is now also proved unique and simple in a uniform smaller box.
The possible exceptional real zero is not excluded, and its Siegel distance
bound remains unproved.

The former `chenCountShift_lower_estimate` `sorry` has been eliminated.  Its
proof now runs through the complete shifted Lemmas 1--9, shifted inequality
(28), the numerical gap `2.6408 - 3.9404/2`, and an even-floor comparison that
extends the auxiliary even-scale estimate to every sufficiently large `x`.

**Lemma 1 is fully proved** — all five parts (`chenPhi_eq_zero`, `chenPhi_nonneg`,
`chenPhi_le_one`, `chenPhi_monotoneOn`, `chenPhi_ge`), no `sorry`, built on top of
seven supporting private lemmas (Gamma-integral/factorial identities, the
concavity tangent-line bound, the Stirling-derived factorial bound, and the
rescaling/tail estimates).

**Lemma 4 is fully proved** (`primitive_char_sum_bound`), using CRT
multiplicativity and strong induction, with the prime case
(`primitive_char_sum_bound_prime`) established via Dirichlet-character
orthogonality — see the design note above.

**Lemma 2 is fully proved** (`large_sieve`, `large_sieve_dyadic`) through the
three modules under `ChenTheorem/LargeSieve/`; neither theorem depends on
`sorryAx`.

**Lemma 5 is fully proved** (`sieveOmega_le_mOne_add_mTwo`).  Its
dimension-two upper-bound sieve is organized under `ChenTheorem/Lemma5/`;
in particular the large-base smoothing boundary is bounded by
`O(x (log x)^{-2.01})` using a short transition interval, optimal Selberg
weights, the lower bound `G(R) ≫ (log x)^1.97`, and the prime harmonic estimate.

The height-logarithmic `L`-function fourth moment supported by Chen's Lemma 3
calculation is proved in `Lemma3/FourthMoment.lean`; the stronger printed
log-`Q`-only claim is documented but not used.  Apart from
`primitive_zero_free_region`, the Lemma 6 pipeline is machine-checked: the
finite Mellin reduction, A/B decomposition, large-conductor regimes (19)–(20),
the equation-(21) contour shift, and the final deduction
`mTwo_le_log12 ⇒ mTwo_le`.

The prime-number-theorem input behind Lemma 7 is discharged from
`Chen.chebyshevPsi_isEquivalent`.  The prime-reciprocal Mertens theorem used
in Lemma 8 is likewise a proved theorem in the locally included
`ChenTheorem/Analysis/PNT/` sources, and both Abel-summation steps and their uniform error
estimates are proved locally; there is no longer a Lemma 8-specific axiom.
Lemma 8 still transitively depends on the Lemma 6 zero-free-region input.
Lemma 9 is machine-checked using the proved `richert_bombieri_equation26`,
which inherits only the zero-free-region gap through Bombieri--Vinogradov.

The paper-internal numerical integrals (24) and (27), inequality (28), the
final numerical deduction and extraction of an actual representation for
Theorem 1, and the infinitude deduction for Theorem 2 are complete.
Consequently Theorem 1 is conditional only on the zero-free-region input.
Theorem 2's complete nine-lemma parallel chain is machine-checked conditional
on the same input.  Shifted inequality (28), the
quantitative estimate `chenCountShift_lower_estimate`, and the final infinitude
deduction are also complete.  In the original Theorem 1 chain, Lemmas 1, 2, 4,
5, and 7 are complete machine-checked proofs; Lemma 3 is complete in the
corrected form used by the argument.
