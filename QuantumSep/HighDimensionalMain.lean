import QuantumSep.SuccessfulReduction
import QuantumSep.EfficientHaarPair
import QuantumSep.DiskNetCardinality
import Mathlib.MeasureTheory.Measure.Prod

/-!
# The high-dimensional randomized optimization algorithm

This module constructs the actual joint Haar/PTAS procedure and proves its
success probability.  Numerical parameter selection is separated from this
probabilistic assembly.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory
open scoped Matrix

noncomputable section

/-- Dimension-independent entry parameter for the projected flat matrix. -/
def mainCSPGamma
    (hc : GaussianHypercontractivityContract) (p : ℕ) : ℝ :=
  32 * flatMomentConstant hc * (p : ℝ) ^ 2

theorem mainCSPGamma_nonneg
    (hc : GaussianHypercontractivityContract) (p : ℕ) :
    0 ≤ mainCSPGamma hc p := by
  unfold mainCSPGamma
  exact mul_nonneg
    (mul_nonneg (by norm_num) (flatMomentConstant_pos hc).le)
    (sq_nonneg (p : ℝ))

theorem flatThreshold_nonneg
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d)) (p : ℕ) :
    0 ≤ flatThreshold hc d M p := by
  unfold flatThreshold flatMomentScale
  exact mul_nonneg (by norm_num)
    (mul_nonneg
      (div_nonneg
        (mul_nonneg (flatMomentConstant_pos hc).le
          (sq_nonneg (p : ℝ)))
        (sq_nonneg (d : ℝ)))
      (by
        unfold frobeniusNorm
        exact Real.sqrt_nonneg _))

def mainFlatMatrix
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d)) (p : ℕ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    BipartiteMatrix (Fin d) :=
  haarThresholdFlat d (correlationPart M)
    (flatThreshold hc d (correlationPart M) p) UV

def mainTailMatrix
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d)) (p : ℕ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    BipartiteMatrix (Fin d) :=
  haarThresholdTail d (correlationPart M)
    (flatThreshold hc d (correlationPart M) p) UV

def mainProjectedMatrix
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d)) (p : ℕ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    BipartiteMatrix (Fin d) :=
  correlationPart (mainFlatMatrix hc d M p UV)

/-- The projected flat matrix has the entry bound required by the concrete
dense-CSP reduction. -/
theorem mainProjectedMatrix_entry_bound
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (p : ℕ)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
    (a b c e : Fin d) :
    ‖mainProjectedMatrix hc d M p UV (a, c) (b, e)‖ ≤
      mainCSPGamma hc p / (d : ℝ) ^ 2 := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  let C := correlationPart M
  let flat := mainFlatMatrix hc d M p UV
  have hCnorm : frobeniusNorm C ≤ 1 :=
    (correlationPart_frobeniusNorm_le M).trans hMnorm
  have hthreshold : 0 ≤ flatThreshold hc d C p :=
    flatThreshold_nonneg hc d C p
  have hflat :
      entryNorm flat ≤ flatThreshold hc d C p := by
    exact haarThresholdFlat_entryNorm_le
      d C (flatThreshold hc d C p) hthreshold UV
  calc
    ‖mainProjectedMatrix hc d M p UV (a, c) (b, e)‖ ≤
        entryNorm (mainProjectedMatrix hc d M p UV) :=
      norm_entry_le_entryNorm _ (a, c) (b, e)
    _ ≤ 4 * entryNorm flat := by
      exact correlationPart_entryNorm_le flat
    _ ≤ 4 * flatThreshold hc d C p :=
      mul_le_mul_of_nonneg_left hflat (by norm_num)
    _ ≤ mainCSPGamma hc p / (d : ℝ) ^ 2 := by
      have hcoef :
          0 ≤ 32 * flatMomentConstant hc * (p : ℝ) ^ 2 := by
        exact mul_nonneg
          (mul_nonneg (by norm_num) (flatMomentConstant_pos hc).le)
          (sq_nonneg (p : ℝ))
      unfold flatThreshold flatMomentScale mainCSPGamma
      calc
        4 * (8 *
            (flatMomentConstant hc * (p : ℝ) ^ 2 /
              (d : ℝ) ^ 2 * frobeniusNorm C)) =
          (32 * flatMomentConstant hc * (p : ℝ) ^ 2) /
              (d : ℝ) ^ 2 * frobeniusNorm C := by ring
        _ ≤
          (32 * flatMomentConstant hc * (p : ℝ) ^ 2) /
              (d : ℝ) ^ 2 * 1 := by
            gcongr
        _ = (32 * flatMomentConstant hc * (p : ℝ) ^ 2) /
              (d : ℝ) ^ 2 := by ring

/-- A reusable real-probability intersection bound. -/
theorem probability_inter_ge
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B : Set Ω) (hAmeas : MeasurableSet A)
    (hBmeas : MeasurableSet B)
    (a b : ℝ)
    (hA : μ.real A ≥ 1 - a)
    (hB : μ.real B ≥ 1 - b) :
    μ.real (A ∩ B) ≥ 1 - a - b := by
  have hAc : μ.real Aᶜ ≤ a := by
    rw [measureReal_compl hAmeas, probReal_univ]
    linarith
  have hBc : μ.real Bᶜ ≤ b := by
    rw [measureReal_compl hBmeas, probReal_univ]
    linarith
  have hcompl :
      μ.real ((A ∩ B)ᶜ) ≤ a + b := by
    rw [Set.compl_inter]
    exact (measureReal_union_le Aᶜ Bᶜ).trans (add_le_add hAc hBc)
  rw [measureReal_compl (hAmeas.inter hBmeas), probReal_univ] at hcompl
  linarith

/-- Numerical data required by the high-dimensional discretization theorem.
Every inequality appearing in the deterministic bounded-amplitude reduction
is recorded explicitly. -/
structure HighDimensionalParameters
    (hc : GaussianHypercontractivityContract)
    (d p : ℕ) where
  sigma : ℝ
  mesh : ℝ
  penalty : ℝ
  cspError : ℝ
  truncation : ℝ
  boundedError : ℝ
  sigma_pos : 0 < sigma
  mesh_pos : 0 < mesh
  penalty_pos : 0 < penalty
  cspError_pos : 0 < cspError
  truncation_pos : 0 < truncation
  truncation_le_half : truncation ≤ 1 / 2
  boundedError_pos : 0 < boundedError
  dimension_gt_sixteen :
    16 < truncation ^ 2 * d
  truncation_error :
    16 * mainCSPGamma hc p ≤ boundedError * sigma
  normalization_error :
    32 * truncation *
        (mainCSPGamma hc p * (sigma + 1) ^ 4) ≤
      boundedError
  conditional_error :
    128 * (mainCSPGamma hc p * (sigma + 1) ^ 4 + 1) ≤
      boundedError * truncation ^ 2 * d

/-- The explicit finite disk net used in the main CSP. -/
def highDimensionalNet
    {hc : GaussianHypercontractivityContract} {d p : ℕ}
    (params : HighDimensionalParameters hc d p) :
    ComplexDiskNet (2 * (params.sigma + 1)) params.mesh :=
  explicitComplexDiskNet _ _ params.mesh_pos

/-- The dense CSP associated with the projected canonical flat matrix for a
particular Haar pair. -/
def highDimensionalCSP
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (p : ℕ)
    (params : HighDimensionalParameters hc d p)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    DenseMaxFourCSP (Fin d)
      (MatrixCSPAlphabet (highDimensionalNet params)) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact matrixDenseMaxFourCSP
    (highDimensionalNet params)
    (mainProjectedMatrix hc d M p UV)
    params.penalty (mainCSPGamma hc p)
    (mainCSPGamma_nonneg hc p)
    (by
      have := params.sigma_pos
      positivity)
    params.penalty_pos.le
    (by
      intro a b c e
      simpa [cardR] using
        mainProjectedMatrix_entry_bound
          hc d hd M hMnorm p UV a b c e)

/-- The actual high-dimensional optimizer: sample two independent Haar
unitaries, construct the resulting finite CSP, solve it with independent
PTAS coins, normalize the assignment, and rotate back to the input basis. -/
def highDimensionalOptimizationProcedure
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (p : ℕ)
    (params : HighDimensionalParameters hc d p) :
    RandomizedProcedure Unit
      ((Fin d → ℂ) × (Fin d → ℂ)) := by
  let haar := efficientHaarPairProcedure sampler d
  let net := highDimensionalNet params
  letI := matrixCSPAlphabet_nonempty net (by
    have := params.sigma_pos
    positivity)
  let randomCSP := fun UV =>
    highDimensionalCSP hc d hd M hMnorm p params UV
  letI := haar.seedMeasurableSpace
  letI := haar.seedProbability
  letI := ptas.seedMeasurableSpace
  letI := ptas.seedProbability
  exact {
    Seed := haar.Seed × ptas.Seed
    seedMeasurableSpace := Prod.instMeasurableSpace
    seedMeasure := haar.seedMeasure.prod ptas.seedMeasure
    seedProbability := inferInstance
    run := fun _ seed =>
      let UV := haar.run () seed.1
      let assignment :=
        ptas.solve (Fin d) (MatrixCSPAlphabet net)
          (randomCSP UV) params.cspError seed.2
      rotateProductOutput d UV
        (normalizedCSPOutputX net assignment)
        (normalizedCSPOutputY net assignment)
    runtime := fun _ seed =>
      let UV := haar.run () seed.1
      haar.runtime () seed.1 +
        ptas.runtime (Fin d) (MatrixCSPAlphabet net)
          (randomCSP UV) params.cspError seed.2 +
        8 * d + 4
  }

/-- Every output of the high-dimensional optimizer is normalized, regardless
of whether the random run satisfies its accuracy event. -/
theorem highDimensionalOptimizationProcedure_output_normalized
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (p : ℕ)
    (params : HighDimensionalParameters hc d p)
    (seed :
      (highDimensionalOptimizationProcedure sampler ptas hc d hd M
        hMnorm p params).Seed) :
    vectorNormSq
        ((highDimensionalOptimizationProcedure sampler ptas hc d hd M
          hMnorm p params).run () seed).1 = d ∧
      vectorNormSq
        ((highDimensionalOptimizationProcedure sampler ptas hc d hd M
          hMnorm p params).run () seed).2 = d := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : IsProbabilityMeasure haar.seedMeasure := haar.seedProbability
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  letI : IsProbabilityMeasure ptas.seedMeasure := ptas.seedProbability
  let net := highDimensionalNet params
  letI := matrixCSPAlphabet_nonempty net (by
    have := params.sigma_pos
    positivity)
  let randomCSP := fun UV =>
    highDimensionalCSP hc d hd M hMnorm p params UV
  let UV := haar.run () seed.1
  let assignment :=
    ptas.solve (Fin d) (MatrixCSPAlphabet net)
      (randomCSP UV) params.cspError seed.2
  change
    vectorNormSq
        (rotateProductOutput d UV
          (normalizedCSPOutputX net assignment)
          (normalizedCSPOutputY net assignment)).1 = d ∧
      vectorNormSq
        (rotateProductOutput d UV
          (normalizedCSPOutputX net assignment)
          (normalizedCSPOutputY net assignment)).2 = d
  exact rotateProductOutput_normalized d UV _ _
    (by
      simpa [normalizedCSPOutputX] using
        (vectorNormSq_normalizeVectorOrOne
          (matrixCSPAssignmentX net assignment)))
    (by
      simpa [normalizedCSPOutputY] using
        (vectorNormSq_normalizeVectorOrOne
          (matrixCSPAssignmentY net assignment)))

/-- Exact uniform runtime bound for the high-dimensional construction.  The
alphabet and accuracy terms are displayed explicitly so that their
dimension-independence can be discharged after numerical parameters are
selected. -/
theorem highDimensionalOptimizationProcedure_runtime_bound
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (p : ℕ)
    (params : HighDimensionalParameters hc d p)
    (seed :
      (highDimensionalOptimizationProcedure sampler ptas hc d hd M
        hMnorm p params).Seed) :
    (highDimensionalOptimizationProcedure sampler ptas hc d hd M
        hMnorm p params).runtime () seed ≤
      2 * sampler.runtimeConstant *
          (d + 1) ^ sampler.runtimeDegree +
        ptas.runtimeConstant
            (Fintype.card
              (MatrixCSPAlphabet (highDimensionalNet params)))
            (Nat.ceil (1 / params.cspError)) *
          (d + 1) ^
            ptas.runtimeDegree
              (Fintype.card
                (MatrixCSPAlphabet (highDimensionalNet params)))
              (Nat.ceil (1 / params.cspError)) +
        8 * d + 4 := by
  let haar := efficientHaarPairProcedure sampler d
  let net := highDimensionalNet params
  letI := matrixCSPAlphabet_nonempty net (by
    have := params.sigma_pos
    positivity)
  let randomCSP :=
    fun UV => highDimensionalCSP hc d hd M hMnorm p params UV
  have hhaar :=
    efficientHaarPairProcedure_runtime sampler d seed.1
  have hcsp :=
    ptas.polynomial_runtime
      (Fin d) (MatrixCSPAlphabet net)
      (randomCSP (haar.run () seed.1))
      params.cspError seed.2
  change
    haar.runtime () seed.1 +
          ptas.runtime (Fin d) (MatrixCSPAlphabet net)
            (randomCSP (haar.run () seed.1)) params.cspError seed.2 +
          8 * d + 4 ≤ _
  simpa [haar, net, Nat.add_assoc] using
    (Nat.add_le_add_right
      (Nat.add_le_add hhaar hcsp) (8 * d + 4))

/-- The canonical Haar decomposition used by the procedure succeeds with
probability at least `1 - δ²`, including the zero-correlation case. -/
theorem mainHaarConclusion_probability
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (delta : ℝ) (hdelta : 0 < delta)
    (hdecay :
      64 * flatMomentConstant hc ^ 2 * (p : ℝ) ^ 4 /
          (8 : ℝ) ^ (2 * p) ≤ delta ^ 4) :
    ((unitaryHaarMeasure d).prod
      (unitaryHaarMeasure d)).real
        {UV |
          HaarFlatTailConclusion d (correlationPart M)
            (flatThreshold hc d (correlationPart M) p) delta UV} ≥
      1 - delta ^ 2 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let C := correlationPart M
  have hCherm : C.IsHermitian :=
    correlationPart_isHermitian M hM
  have hzero0 : partialTrace0 C = 0 :=
    partialTrace0_correlationPart M
  have hzero1 : partialTrace1 C = 0 :=
    partialTrace1_correlationPart M
  by_cases hC0 : C = 0
  · have hall :
        {UV |
          HaarFlatTailConclusion d C
            (flatThreshold hc d C p) delta UV} = Set.univ := by
        apply Set.eq_univ_of_forall
        intro UV
        have hτ :
            0 ≤ flatThreshold hc d C p := by
          rw [hC0]
          simp [flatThreshold, flatMomentScale, frobeniusNorm,
            frobeniusSq]
        refine ⟨haarThreshold_decomposition d C
            (flatThreshold hc d C p) UV,
          haarThresholdFlat_isHermitian d C hCherm
            (flatThreshold hc d C p) UV,
          haarThresholdTail_isHermitian d C hCherm
            (flatThreshold hc d C p) UV,
          haarThresholdFlat_entryNorm_le d C
            (flatThreshold hc d C p) hτ UV, ?_⟩
        rw [hC0]
        simp [flatThreshold, flatMomentScale, frobeniusNorm,
          frobeniusSq, haarThresholdTail, bipartiteUnitaryConjugate,
          thresholdTail]
    change
      ((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d)).real
          {UV |
            HaarFlatTailConclusion d C
              (flatThreshold hc d C p) delta UV} ≥
        1 - delta ^ 2
    rw [hall, probReal_univ]
    nlinarith [sq_nonneg delta]
  · have hexpect :=
      flatThreshold_expectedTailBound
        hc d hd C hC0 p hp delta hdecay
    change
      ((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d)).real
          {UV |
            HaarFlatTailConclusion d C
              (flatThreshold hc d C p) delta UV} ≥
        1 - delta ^ 2
    apply haarFlatTailConclusion_measureReal_ge
      hc d C hCherm hC0 hzero0 hzero1 p hp height
      (flatThreshold hc d C p)
      (flatThreshold_pos hc d hd C hC0 p hp)
      delta hdelta
    convert hexpect using 1 <;> ring

/-- Deterministic correctness of the high-dimensional procedure on the
measurable core where both the Haar decomposition and the PTAS call succeed.
This pointwise theorem is used by adaptive fresh-coin composition. -/
theorem highDimensionalOptimizationProcedure_correct_of_core
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (p : ℕ)
    (delta : ℝ) (hdelta : 0 ≤ delta)
    (params : HighDimensionalParameters hc d p)
    (seed :
      (highDimensionalOptimizationProcedure sampler ptas hc d hd M
        hMnorm p params).Seed)
    (hhaar :
      let haar := efficientHaarPairProcedure sampler d
      HaarFlatTailConclusion d (correlationPart M)
        (flatThreshold hc d (correlationPart M) p) delta
        (haar.run () seed.1))
    (hcspGood :
      let haar := efficientHaarPairProcedure sampler d
      let net := highDimensionalNet params
      letI := matrixCSPAlphabet_nonempty net (by
        have := params.sigma_pos
        positivity)
      let UV := haar.run () seed.1
      let csp :=
        highDimensionalCSP hc d hd M hMnorm p params UV
      ∀ assignment,
        csp.value assignment ≤
          csp.value
            (ptas.solve (Fin d) (MatrixCSPAlphabet net)
              csp params.cspError seed.2) +
          params.cspError) :
    ∀ x y : Fin d → ℂ,
      vectorNormSq x = d →
      vectorNormSq y = d →
      matrixQuarticForm M x y ≤
        matrixQuarticForm M
          ((highDimensionalOptimizationProcedure sampler ptas hc d hd M
            hMnorm p params).run () seed).1
          ((highDimensionalOptimizationProcedure sampler ptas hc d hd M
            hMnorm p params).run () seed).2 +
        discretizedOptimizationError
          params.sigma params.mesh params.penalty
          (mainCSPGamma hc p) params.cspError
          params.boundedError +
        2 * delta + 4 / Real.sqrt d := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : IsProbabilityMeasure haar.seedMeasure := haar.seedProbability
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  letI : IsProbabilityMeasure ptas.seedMeasure := ptas.seedProbability
  let net := highDimensionalNet params
  letI := matrixCSPAlphabet_nonempty net (by
    have := params.sigma_pos
    positivity)
  let UV := haar.run () seed.1
  let csp :=
    highDimensionalCSP hc d hd M hMnorm p params UV
  let assignment :=
    ptas.solve (Fin d) (MatrixCSPAlphabet net)
      csp params.cspError seed.2
  let outputX := normalizedCSPOutputX net assignment
  let outputY := normalizedCSPOutputY net assignment
  have hentry :
      ∀ a b c e,
        ‖mainProjectedMatrix hc d M p UV (a, c) (b, e)‖ ≤
          mainCSPGamma hc p / cardR (ι := Fin d) ^ 2 := by
    intro a b c e
    simpa [cardR] using
      mainProjectedMatrix_entry_bound
        hc d hd M hMnorm p UV a b c e
  have hcspSuccess :
      ∀ other,
        (matrixDenseMaxFourCSP net
          (mainProjectedMatrix hc d M p UV)
          params.penalty (mainCSPGamma hc p)
          (mainCSPGamma_nonneg hc p) (by
            have := params.sigma_pos
            positivity)
          params.penalty_pos.le hentry).value other ≤
        (matrixDenseMaxFourCSP net
          (mainProjectedMatrix hc d M p UV)
          params.penalty (mainCSPGamma hc p)
          (mainCSPGamma_nonneg hc p) (by
            have := params.sigma_pos
            positivity)
          params.penalty_pos.le hentry).value assignment +
        params.cspError := by
    simpa [csp, highDimensionalCSP, UV, net, assignment] using
      hcspGood
  have hcsp :
      ∀ x y : Fin d → ℂ,
        vectorNormSq x = d →
        vectorNormSq y = d →
        matrixQuarticForm
            (mainProjectedMatrix hc d M p UV) x y ≤
          matrixQuarticForm
            (mainProjectedMatrix hc d M p UV)
            outputX outputY +
          discretizedOptimizationError
            params.sigma params.mesh params.penalty
            (mainCSPGamma hc p) params.cspError
            params.boundedError := by
    intro x y hx hy
    have h :=
      successfulCSP_output_approximates_all
        params.sigma params.mesh net
        (mainProjectedMatrix hc d M p UV)
        params.penalty (mainCSPGamma hc p)
        params.cspError params.truncation params.boundedError
        (mainCSPGamma_nonneg hc p) params.sigma_pos
        params.mesh_pos.le params.penalty_pos
        params.truncation_pos params.truncation_le_half
        params.boundedError_pos hentry
        (partialTrace0_correlationPart (mainFlatMatrix hc d M p UV))
        (partialTrace1_correlationPart (mainFlatMatrix hc d M p UV))
        (by simpa using params.dimension_gt_sixteen)
        params.truncation_error params.normalization_error
        (by simpa using params.conditional_error)
        assignment hcspSuccess
        x y (by simpa using hx) (by simpa using hy)
    simpa [mainProjectedMatrix, outputX, outputY,
      discretizedOptimizationError, add_assoc] using h
  have houtputX : vectorNormSq outputX = d := by
    simpa [outputX, normalizedCSPOutputX] using
      (vectorNormSq_normalizeVectorOrOne
        (matrixCSPAssignmentX net assignment))
  have houtputY : vectorNormSq outputY = d := by
    simpa [outputY, normalizedCSPOutputY] using
      (vectorNormSq_normalizeVectorOrOne
        (matrixCSPAssignmentY net assignment))
  have hdecomp :
      FlatTailDecomposition
        (bipartiteUnitaryConjugate d (correlationPart M) UV)
        (correlationPart M)
        (mainFlatMatrix hc d M p UV)
        (mainTailMatrix hc d M p UV)
        (flatThreshold hc d (correlationPart M) p) delta := by
    exact (haarFlatTailConclusion_iff_decomposition
      d (correlationPart M)
      (flatThreshold hc d (correlationPart M) p)
      delta UV).mp (by simpa [UV, haar] using hhaar)
  have hfinal :=
    successfulReduction_approximates
      d hd M hMnorm UV
      (mainFlatMatrix hc d M p UV)
      (mainTailMatrix hc d M p UV)
      (flatThreshold hc d (correlationPart M) p)
      delta
      (discretizedOptimizationError
        params.sigma params.mesh params.penalty
        (mainCSPGamma hc p) params.cspError
        params.boundedError)
      hdelta hdecomp outputX outputY
      houtputX houtputY
      (by simpa [mainProjectedMatrix] using hcsp)
  simpa [highDimensionalOptimizationProcedure, haar, net, UV, csp,
    assignment, outputX, outputY] using hfinal

/-- End-to-end correctness of the high-dimensional randomized optimizer.
The only probabilistic inputs are the exact Haar sampler and the dense-CSP
PTAS contracts. -/
theorem highDimensionalOptimizationProcedure_success
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (hMnorm : frobeniusNorm M ≤ 1)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (delta : ℝ) (hdelta : 0 < delta)
    (hdeltaProbability : delta ^ 2 ≤ 1 / 6)
    (hdecay :
      64 * flatMomentConstant hc ^ 2 * (p : ℝ) ^ 4 /
          (8 : ℝ) ^ (2 * p) ≤ delta ^ 4)
    (params : HighDimensionalParameters hc d p) :
    let alg :=
      highDimensionalOptimizationProcedure sampler ptas hc d hd M
        hMnorm p params
    alg.eventProbability
      {seed |
        ∀ x y : Fin d → ℂ,
          vectorNormSq x = d →
          vectorNormSq y = d →
          matrixQuarticForm M x y ≤
            matrixQuarticForm M
              (alg.run () seed).1 (alg.run () seed).2 +
            discretizedOptimizationError
              params.sigma params.mesh params.penalty
              (mainCSPGamma hc p) params.cspError
              params.boundedError +
            2 * delta + 4 / Real.sqrt d} ≥
      2 / 3 := by
  dsimp only
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : IsProbabilityMeasure haar.seedMeasure := haar.seedProbability
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  letI : IsProbabilityMeasure ptas.seedMeasure := ptas.seedProbability
  let net := highDimensionalNet params
  letI := matrixCSPAlphabet_nonempty net (by
    have := params.sigma_pos
    positivity)
  let randomCSP : haar.Seed →
      DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) :=
    fun seed =>
      highDimensionalCSP hc d hd M hMnorm p params
        (haar.run () seed)
  let haarConclusion : Set
      (Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :=
    {UV |
      HaarFlatTailConclusion d (correlationPart M)
        (flatThreshold hc d (correlationPart M) p) delta UV}
  let goodHaarSeed : Set haar.Seed :=
    (haar.run ()) ⁻¹' haarConclusion
  let goodHaar : Set (haar.Seed × ptas.Seed) :=
    goodHaarSeed ×ˢ Set.univ
  let goodCSP : Set (haar.Seed × ptas.Seed) :=
    {seed | ∀ assignment,
      (randomCSP seed.1).value assignment ≤
        (randomCSP seed.1).value
          (ptas.solve (Fin d) (MatrixCSPAlphabet net)
            (randomCSP seed.1) params.cspError seed.2) +
        params.cspError}
  let goodOutput : Set (haar.Seed × ptas.Seed) :=
    {seed |
      ∀ x y : Fin d → ℂ,
        vectorNormSq x = d →
        vectorNormSq y = d →
        matrixQuarticForm M x y ≤
          matrixQuarticForm M
            ((highDimensionalOptimizationProcedure sampler ptas hc d hd M
              hMnorm p params).run () seed).1
            ((highDimensionalOptimizationProcedure sampler ptas hc d hd M
              hMnorm p params).run () seed).2 +
          discretizedOptimizationError
            params.sigma params.mesh params.penalty
            (mainCSPGamma hc p) params.cspError
            params.boundedError +
          2 * delta + 4 / Real.sqrt d}
  have hCherm :
      (correlationPart M).IsHermitian :=
    correlationPart_isHermitian M hM
  have hzero0 :
      partialTrace0 (correlationPart M) = 0 :=
    partialTrace0_correlationPart M
  have hzero1 :
      partialTrace1 (correlationPart M) = 0 :=
    partialTrace1_correlationPart M
  have hhaarConclusionMeas :
      MeasurableSet haarConclusion := by
    exact measurableSet_haarFlatTailConclusion
      d (correlationPart M) hCherm hzero0 hzero1
      (flatThreshold hc d (correlationPart M) p)
      (flatThreshold_nonneg hc d (correlationPart M) p) delta
  have hgoodHaarSeedMeas :
      @MeasurableSet haar.Seed haar.seedMeasurableSpace
        goodHaarSeed := by
    exact hhaarConclusionMeas.preimage
      (efficientHaarPairProcedure_run_measurable sampler d)
  have hgoodHaarMeas :
      @MeasurableSet (haar.Seed × ptas.Seed)
        (@Prod.instMeasurableSpace haar.Seed ptas.Seed
          haar.seedMeasurableSpace ptas.seedMeasurableSpace)
        goodHaar :=
    hgoodHaarSeedMeas.prod MeasurableSet.univ
  have hgoodCSPMeas :
      @MeasurableSet (haar.Seed × ptas.Seed)
        (@Prod.instMeasurableSpace haar.Seed ptas.Seed
          haar.seedMeasurableSpace ptas.seedMeasurableSpace)
        goodCSP := by
    simpa [goodCSP, randomCSP] using
      ptas.independent_success_event_measurable
        haar.Seed (Fin d) (MatrixCSPAlphabet net)
        haar.seedMeasure randomCSP params.cspError
  have hhaarBase :
      haar.eventProbability goodHaarSeed ≥
        1 - delta ^ 2 := by
    rw [efficientHaarPairProcedure_eventProbability
      sampler d haarConclusion hhaarConclusionMeas]
    exact mainHaarConclusion_probability
      hc d hd M hM p hp height delta hdelta hdecay
  have hgoodHaarProbability :
      (haar.seedMeasure.prod ptas.seedMeasure).real goodHaar ≥
        1 - delta ^ 2 := by
    rw [show goodHaar = goodHaarSeed ×ˢ Set.univ by rfl,
      measureReal_prod_prod, probReal_univ, mul_one]
    exact hhaarBase
  have hgoodCSPProbability :
      (haar.seedMeasure.prod ptas.seedMeasure).real goodCSP ≥
        5 / 6 := by
    simpa [goodCSP, randomCSP] using
      ptas.success_on_independent_random_instance
        haar.Seed (Fin d) (MatrixCSPAlphabet net)
        haar.seedMeasure randomCSP params.cspError
        params.cspError_pos
  have hbothProbability :
      (haar.seedMeasure.prod ptas.seedMeasure).real
          (goodHaar ∩ goodCSP) ≥
        1 - delta ^ 2 - 1 / 6 := by
    exact probability_inter_ge
      (haar.seedMeasure.prod ptas.seedMeasure)
      goodHaar goodCSP hgoodHaarMeas hgoodCSPMeas
      (delta ^ 2) (1 / 6)
      hgoodHaarProbability
      (by
        convert hgoodCSPProbability using 1 <;> norm_num)
  have hsubset : goodHaar ∩ goodCSP ⊆ goodOutput := by
    intro seed hseed
    have hhaar :
        HaarFlatTailConclusion d (correlationPart M)
          (flatThreshold hc d (correlationPart M) p) delta
          (haar.run () seed.1) := by
      exact hseed.1.1
    let UV := haar.run () seed.1
    let assignment :=
      ptas.solve (Fin d) (MatrixCSPAlphabet net)
        (randomCSP seed.1) params.cspError seed.2
    let outputX := normalizedCSPOutputX net assignment
    let outputY := normalizedCSPOutputY net assignment
    have hentry :
        ∀ a b c e,
          ‖mainProjectedMatrix hc d M p UV (a, c) (b, e)‖ ≤
            mainCSPGamma hc p / cardR (ι := Fin d) ^ 2 := by
      intro a b c e
      simpa [cardR] using
        mainProjectedMatrix_entry_bound
          hc d hd M hMnorm p UV a b c e
    have hcspSuccess :
        ∀ other,
          (matrixDenseMaxFourCSP net
            (mainProjectedMatrix hc d M p UV)
            params.penalty (mainCSPGamma hc p)
            (mainCSPGamma_nonneg hc p) (by
              have := params.sigma_pos
              positivity)
            params.penalty_pos.le hentry).value other ≤
          (matrixDenseMaxFourCSP net
            (mainProjectedMatrix hc d M p UV)
            params.penalty (mainCSPGamma hc p)
            (mainCSPGamma_nonneg hc p) (by
              have := params.sigma_pos
              positivity)
            params.penalty_pos.le hentry).value assignment +
          params.cspError := by
      have hh :
          ∀ other,
            (randomCSP seed.1).value other ≤
              (randomCSP seed.1).value assignment +
                params.cspError := by
        simpa [goodCSP, assignment] using hseed.2
      simpa [randomCSP, highDimensionalCSP, UV, net] using hh
    have hcsp :
        ∀ x y : Fin d → ℂ,
          vectorNormSq x = d →
          vectorNormSq y = d →
          matrixQuarticForm
              (mainProjectedMatrix hc d M p UV) x y ≤
            matrixQuarticForm
              (mainProjectedMatrix hc d M p UV)
              outputX outputY +
            discretizedOptimizationError
              params.sigma params.mesh params.penalty
              (mainCSPGamma hc p) params.cspError
              params.boundedError := by
      intro x y hx hy
      have h :=
        successfulCSP_output_approximates_all
          params.sigma params.mesh net
          (mainProjectedMatrix hc d M p UV)
          params.penalty (mainCSPGamma hc p)
          params.cspError params.truncation params.boundedError
          (mainCSPGamma_nonneg hc p) params.sigma_pos
          params.mesh_pos.le params.penalty_pos
          params.truncation_pos params.truncation_le_half
          params.boundedError_pos hentry
          (partialTrace0_correlationPart (mainFlatMatrix hc d M p UV))
          (partialTrace1_correlationPart (mainFlatMatrix hc d M p UV))
          (by simpa using params.dimension_gt_sixteen)
          params.truncation_error params.normalization_error
          (by simpa using params.conditional_error)
          assignment hcspSuccess
          x y (by simpa using hx) (by simpa using hy)
      simpa [mainProjectedMatrix, outputX, outputY,
        discretizedOptimizationError, add_assoc] using h
    have houtputX : vectorNormSq outputX = d := by
      simpa [outputX, normalizedCSPOutputX] using
        (vectorNormSq_normalizeVectorOrOne
          (matrixCSPAssignmentX net assignment))
    have houtputY : vectorNormSq outputY = d := by
      simpa [outputY, normalizedCSPOutputY] using
        (vectorNormSq_normalizeVectorOrOne
          (matrixCSPAssignmentY net assignment))
    have hdecomp :
        FlatTailDecomposition
          (bipartiteUnitaryConjugate d (correlationPart M) UV)
          (correlationPart M)
          (mainFlatMatrix hc d M p UV)
          (mainTailMatrix hc d M p UV)
          (flatThreshold hc d (correlationPart M) p) delta := by
      exact (haarFlatTailConclusion_iff_decomposition
        d (correlationPart M)
        (flatThreshold hc d (correlationPart M) p)
        delta UV).mp (by simpa [UV] using hhaar)
    have hfinal :=
      successfulReduction_approximates
        d hd M hMnorm UV
        (mainFlatMatrix hc d M p UV)
        (mainTailMatrix hc d M p UV)
        (flatThreshold hc d (correlationPart M) p)
        delta
        (discretizedOptimizationError
          params.sigma params.mesh params.penalty
          (mainCSPGamma hc p) params.cspError
          params.boundedError)
        hdelta.le hdecomp outputX outputY
        houtputX houtputY
        (by simpa [mainProjectedMatrix] using hcsp)
    simpa [goodOutput, highDimensionalOptimizationProcedure,
      haar, net, randomCSP, UV, assignment, outputX, outputY] using hfinal
  change
    (haar.seedMeasure.prod ptas.seedMeasure).real goodOutput ≥ 2 / 3
  calc
    2 / 3 ≤
        (haar.seedMeasure.prod ptas.seedMeasure).real
          (goodHaar ∩ goodCSP) := by
      have hnumeric :
          (2 / 3 : ℝ) ≤ 1 - delta ^ 2 - 1 / 6 := by
        linarith
      exact hnumeric.trans hbothProbability
    _ ≤
        (haar.seedMeasure.prod ptas.seedMeasure).real goodOutput :=
      measureReal_mono hsubset

end

end QuantumSep
