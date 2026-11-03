import QuantumSep.DiscretizedOptimization
import Mathlib.MeasureTheory.Measure.Real

/-!
# Randomized optimization of one flat correlation matrix

This module applies the permitted dense-CSP PTAS contract to the concrete CSP
constructed in `MatrixCSPReduction` and transfers its `2/3` success
probability to normalized product vectors.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The full deterministic error charged after a successful CSP call. -/
def discretizedOptimizationError
    (sigma mesh penalty gamma cspError boundedError : ℝ) : ℝ :=
  boundedError +
    (4 * gamma * (2 * (sigma + 1)) ^ 3 * mesh +
      8 * penalty * (2 * (sigma + 1)) *
        ((2 * (sigma + 1)) ^ 2 + 1) * mesh) +
    2 * matrixPredicateScale gamma (2 * (sigma + 1)) penalty *
      cspError +
    (gamma ^ 2 + gamma ^ 2 * (2 * (sigma + 1)) ^ 4) /
      (4 * penalty)

/-- The randomized procedure obtained by running the dense-CSP PTAS and
normalizing its two output coordinate vectors. -/
def flatMatrixOptimizationProcedure
    (ptas : DenseMaxFourCSPPTASContract)
    (sigma mesh : ℝ)
    (net : ComplexDiskNet (2 * (sigma + 1)) mesh)
    (M : BipartiteMatrix ι)
    (penalty gamma cspError : ℝ)
    (hgamma : 0 ≤ gamma)
    (hkappa : 0 ≤ 2 * (sigma + 1))
    (hpenalty : 0 ≤ penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2) :
    RandomizedProcedure Unit ((ι → ℂ) × (ι → ℂ)) := by
  letI := matrixCSPAlphabet_nonempty net hkappa
  let csp :=
    matrixDenseMaxFourCSP net M penalty gamma
      hgamma hkappa hpenalty hentry
  let base := ptas.procedure ι (MatrixCSPAlphabet net) csp cspError
  exact {
    Seed := base.Seed
    seedMeasurableSpace := base.seedMeasurableSpace
    seedMeasure := base.seedMeasure
    seedProbability := base.seedProbability
    run := fun _ seed =>
      (normalizedCSPOutputX net (base.run () seed),
        normalizedCSPOutputY net (base.run () seed))
    runtime := fun _ seed =>
      base.runtime () seed + 8 * Fintype.card ι + 4
  }

theorem flatMatrixOptimizationProcedure_output_normalized
    (ptas : DenseMaxFourCSPPTASContract)
    (sigma mesh : ℝ)
    (net : ComplexDiskNet (2 * (sigma + 1)) mesh)
    (M : BipartiteMatrix ι)
    (penalty gamma cspError : ℝ)
    (hgamma : 0 ≤ gamma)
    (hkappa : 0 ≤ 2 * (sigma + 1))
    (hpenalty : 0 ≤ penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (seed :
      (flatMatrixOptimizationProcedure ptas sigma mesh net M
        penalty gamma cspError hgamma hkappa hpenalty hentry).Seed) :
    vectorNormSq
        ((flatMatrixOptimizationProcedure ptas sigma mesh net M
          penalty gamma cspError hgamma hkappa hpenalty hentry).run () seed).1 =
          Fintype.card ι ∧
      vectorNormSq
        ((flatMatrixOptimizationProcedure ptas sigma mesh net M
          penalty gamma cspError hgamma hkappa hpenalty hentry).run () seed).2 =
          Fintype.card ι := by
  constructor
  · exact vectorNormSq_normalizeVectorOrOne _
  · exact vectorNormSq_normalizeVectorOrOne _

/-- With probability at least `2/3`, the concrete randomized output satisfies
the fully assembled flat-matrix approximation guarantee. -/
theorem flatMatrixOptimizationProcedure_success
    (ptas : DenseMaxFourCSPPTASContract)
    (sigma mesh : ℝ)
    (net : ComplexDiskNet (2 * (sigma + 1)) mesh)
    (M : BipartiteMatrix ι)
    (penalty gamma cspError t boundedError : ℝ)
    (hgamma : 0 ≤ gamma) (hsigma : 0 < sigma)
    (hmesh : 0 ≤ mesh) (hpenalty : 0 < penalty)
    (hcspError : 0 < cspError)
    (htpos : 0 < t) (ht : t ≤ 1 / 2)
    (hboundedError : 0 < boundedError)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (htrace0 : partialTrace0 M = 0)
    (htrace1 : partialTrace1 M = 0)
    (hden16 : 16 < t ^ 2 * Fintype.card ι)
    (htrunc : 16 * gamma ≤ boundedError * sigma)
    (hnormalize :
      32 * t * (gamma * (sigma + 1) ^ 4) ≤ boundedError)
    (hconditional :
      128 * (gamma * (sigma + 1) ^ 4 + 1) ≤
        boundedError * t ^ 2 * Fintype.card ι) :
    let alg :=
      flatMatrixOptimizationProcedure ptas sigma mesh net M
        penalty gamma cspError hgamma (by positivity) hpenalty.le hentry
    alg.eventProbability
      {seed | ∀ x y : ι → ℂ,
        vectorNormSq x = Fintype.card ι →
        vectorNormSq y = Fintype.card ι →
        matrixQuarticForm M x y ≤
          matrixQuarticForm M
            (alg.run () seed).1 (alg.run () seed).2 +
          discretizedOptimizationError
            sigma mesh penalty gamma cspError boundedError} ≥ 2 / 3 := by
  dsimp only
  letI := matrixCSPAlphabet_nonempty net (by positivity)
  let csp :=
    matrixDenseMaxFourCSP net M penalty gamma
      hgamma (by positivity) hpenalty.le hentry
  let base :=
    ptas.procedure ι (MatrixCSPAlphabet net) csp cspError
  let goodCSP : Set base.Seed :=
    {seed | ∀ assignment,
      csp.value assignment ≤
        csp.value (base.run () seed) + cspError}
  let goodOutput : Set base.Seed :=
    {seed | ∀ x y : ι → ℂ,
      vectorNormSq x = Fintype.card ι →
      vectorNormSq y = Fintype.card ι →
      matrixQuarticForm M x y ≤
        matrixQuarticForm M
          (normalizedCSPOutputX net (base.run () seed))
          (normalizedCSPOutputY net (base.run () seed)) +
        discretizedOptimizationError
          sigma mesh penalty gamma cspError boundedError}
  have hsubset : goodCSP ⊆ goodOutput := by
    intro seed hseed
    intro x y hx hy
    have h :=
      successfulCSP_output_approximates_all
        sigma mesh net M penalty gamma cspError t boundedError
        hgamma hsigma hmesh hpenalty htpos ht hboundedError
        hentry htrace0 htrace1 hden16 htrunc hnormalize hconditional
        (base.run () seed) hseed x y hx hy
    simpa [discretizedOptimizationError, add_assoc] using h
  have hptas :=
    ptas.success ι (MatrixCSPAlphabet net) csp cspError hcspError
  change base.eventProbability goodOutput ≥ 2 / 3
  calc
    2 / 3 ≤ base.eventProbability goodCSP := by
      have hfiveSixths :
          5 / 6 ≤
            @Measure.real ptas.Seed ptas.seedMeasurableSpace
              ptas.seedMeasure goodCSP := by
        convert hptas using 1
        congr 1
      have htwoThirds : (2 / 3 : ℝ) ≤ 5 / 6 := by norm_num
      exact htwoThirds.trans hfiveSixths
    _ ≤ base.eventProbability goodOutput := by
      letI := base.seedMeasurableSpace
      letI := base.seedProbability
      exact measureReal_mono hsubset

end

end QuantumSep
