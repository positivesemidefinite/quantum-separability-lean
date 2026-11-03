import QuantumSep.MainTheorem

/-!
# Unit-vector form of the optimization theorem

The algorithm works internally with vectors of squared norm `d`.  This file
performs the final division by `sqrt d` and states the result using ordinary
unit vectors and the unnormalized quadratic expectation.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory

noncomputable section

def physicalVector
    (d : ℕ) (x : Fin d → ℂ) : Fin d → ℂ :=
  scaleVector (1 / Real.sqrt d) x

def scaledFromPhysical
    (d : ℕ) (x : Fin d → ℂ) : Fin d → ℂ :=
  scaleVector (Real.sqrt d) x

def physicalProductObjective
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (x y : Fin d → ℂ) : ℝ :=
  matrixQuadraticFormReal M (productVector d x y)

theorem physicalVector_normSq
    (d : ℕ) (hd : 0 < d)
    (x : Fin d → ℂ)
    (hx : vectorNormSq x = d) :
    vectorNormSq (physicalVector d x) = 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hsqrtSq : (Real.sqrt (d : ℝ)) ^ 2 = d :=
    Real.sq_sqrt hdR.le
  unfold physicalVector
  rw [vectorNormSq_scaleVector, hx]
  field_simp [hsqrt.ne']
  nlinarith

theorem scaledFromPhysical_normSq
    (d : ℕ) (hd : 0 < d)
    (x : Fin d → ℂ)
    (hx : vectorNormSq x = 1) :
    vectorNormSq (scaledFromPhysical d x) = d := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold scaledFromPhysical
  rw [vectorNormSq_scaleVector, hx, mul_one,
    Real.sq_sqrt hdR.le]

theorem physicalVector_scaledFromPhysical
    (d : ℕ) (hd : 0 < d)
    (x : Fin d → ℂ) :
    physicalVector d (scaledFromPhysical d x) = x := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  funext i
  unfold physicalVector scaledFromPhysical scaleVector
  push_cast
  field_simp [hsqrt.ne']

theorem physicalProductObjective_physicalVector
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (x y : Fin d → ℂ) :
    physicalProductObjective d M
        (physicalVector d x) (physicalVector d y) =
      matrixQuarticForm M x y := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
  have hsqrtSq : (Real.sqrt (d : ℝ)) ^ 2 = d :=
    Real.sq_sqrt hdR.le
  have hquartic :=
    matrixQuarticForm_scaleVector M x y
      (1 / Real.sqrt d) (1 / Real.sqrt d)
  have hrelation :=
    matrixQuarticForm_eq_productQuadratic d M
      (physicalVector d x) (physicalVector d y)
  unfold physicalVector at hrelation
  have hcombined :
      physicalProductObjective d M
          (physicalVector d x) (physicalVector d y) /
            (d : ℝ) ^ 2 =
        (1 / Real.sqrt d) ^ 2 *
          (1 / Real.sqrt d) ^ 2 *
            matrixQuarticForm M x y := by
    simpa [physicalVector, physicalProductObjective] using
      hrelation.symm.trans hquartic
  field_simp [hsqrt.ne', hdR.ne'] at hcombined
  have hfour :
      (Real.sqrt (d : ℝ)) ^ 4 = (d : ℝ) ^ 2 := by
    calc
      (Real.sqrt (d : ℝ)) ^ 4 =
          ((Real.sqrt (d : ℝ)) ^ 2) ^ 2 := by ring
      _ = (d : ℝ) ^ 2 := by rw [hsqrtSq]
  rw [hfour] at hcombined
  have hdSq : 0 < (d : ℝ) ^ 2 := sq_pos_of_pos hdR
  unfold physicalProductObjective at hcombined ⊢
  nlinarith

theorem matrixQuarticForm_scaledFromPhysical
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (x y : Fin d → ℂ) :
    matrixQuarticForm M
        (scaledFromPhysical d x) (scaledFromPhysical d y) =
      physicalProductObjective d M x y := by
  rw [← physicalProductObjective_physicalVector d hd M
    (scaledFromPhysical d x) (scaledFromPhysical d y),
    physicalVector_scaledFromPhysical d hd,
    physicalVector_scaledFromPhysical d hd]

/-- The final procedure in the conventional unit-vector normalization. -/
def physicalProductOptimizationProcedure
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1) :
    RandomizedProcedure Unit ((Fin d → ℂ) × (Fin d → ℂ)) := by
  let base :=
    productOptimizationProcedure
      sampler ptas hc tau htau d hd M hMnorm
  letI : MeasurableSpace base.Seed := base.seedMeasurableSpace
  letI : IsProbabilityMeasure base.seedMeasure := base.seedProbability
  exact {
    Seed := base.Seed
    seedMeasurableSpace := base.seedMeasurableSpace
    seedMeasure := base.seedMeasure
    seedProbability := base.seedProbability
    run := fun _ seed =>
      (physicalVector d (base.run () seed).1,
        physicalVector d (base.run () seed).2)
    runtime := base.runtime
  }

/-- Polynomial-runtime property stated directly for the conventional
unit-vector procedure. -/
def PhysicalProductOptimizerPolynomialRuntime
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau) : Prop :=
  ∃ C degree : ℕ,
    ∀ (d : ℕ) (hd : 0 < d)
      (M : BipartiteMatrix (Fin d))
      (hMnorm : frobeniusNorm M ≤ 1),
      ProcedureRuntimeBound
        (physicalProductOptimizationProcedure
          sampler ptas hc tau htau d hd M hMnorm)
        (C * (d + 1) ^ degree)

theorem physicalProductOptimizationProcedure_polynomial_runtime
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (ram : RealRAMModelContract)
    (tau : ℝ) (htau : 0 < tau) :
    PhysicalProductOptimizerPolynomialRuntime
      sampler ptas hc tau htau := by
  obtain ⟨C, degree, hbound⟩ :=
    productOptimizationProcedure_polynomial_runtime
      sampler ptas hc ram tau htau
  refine ⟨C, degree, ?_⟩
  intro d hd M hMnorm
  intro seed
  exact hbound d hd M hMnorm seed

theorem physicalProductOptimizationProcedure_output_unit
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (seed :
      (physicalProductOptimizationProcedure
        sampler ptas hc tau htau d hd M hMnorm).Seed) :
    let alg :=
      physicalProductOptimizationProcedure
        sampler ptas hc tau htau d hd M hMnorm
    vectorNormSq (alg.run () seed).1 = 1 ∧
      vectorNormSq (alg.run () seed).2 = 1 := by
  let base :=
    productOptimizationProcedure
      sampler ptas hc tau htau d hd M hMnorm
  have hnorm :=
    productOptimizationProcedure_output_normalized
      sampler ptas hc tau htau d hd M hMnorm seed
  exact
    ⟨physicalVector_normSq d hd (base.run () seed).1 hnorm.1,
      physicalVector_normSq d hd (base.run () seed).2 hnorm.2⟩

theorem physicalProductOptimizationProcedure_success
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (hMnorm : frobeniusNorm M ≤ 1) :
    let alg :=
      physicalProductOptimizationProcedure
        sampler ptas hc tau htau d hd M hMnorm
    alg.eventProbability
      {seed |
        ∀ x y : Fin d → ℂ,
          vectorNormSq x = 1 →
          vectorNormSq y = 1 →
          physicalProductObjective d M x y ≤
            physicalProductObjective d M
              (alg.run () seed).1 (alg.run () seed).2 + tau} ≥
      2 / 3 := by
  dsimp only
  let base :=
    productOptimizationProcedure
      sampler ptas hc tau htau d hd M hMnorm
  letI : MeasurableSpace base.Seed := base.seedMeasurableSpace
  letI : IsProbabilityMeasure base.seedMeasure := base.seedProbability
  let goodScaled : Set base.Seed :=
    {seed |
      ∀ x y : Fin d → ℂ,
        vectorNormSq x = d →
        vectorNormSq y = d →
        matrixQuarticForm M x y ≤
          matrixQuarticForm M
            (base.run () seed).1 (base.run () seed).2 + tau}
  let goodPhysical : Set base.Seed :=
    {seed |
      ∀ x y : Fin d → ℂ,
        vectorNormSq x = 1 →
        vectorNormSq y = 1 →
        physicalProductObjective d M x y ≤
          physicalProductObjective d M
            (physicalVector d (base.run () seed).1)
            (physicalVector d (base.run () seed).2) + tau}
  have hsubset : goodScaled ⊆ goodPhysical := by
    intro seed hseed x y hx hy
    have h :=
      hseed (scaledFromPhysical d x) (scaledFromPhysical d y)
        (scaledFromPhysical_normSq d hd x hx)
        (scaledFromPhysical_normSq d hd y hy)
    rw [matrixQuarticForm_scaledFromPhysical d hd M,
      ← physicalProductObjective_physicalVector d hd M] at h
    exact h
  have hbase :=
    productOptimizationProcedure_success
      sampler ptas hc tau htau d hd M hM hMnorm
  change base.eventProbability goodPhysical ≥ 2 / 3
  calc
    2 / 3 ≤ base.eventProbability goodScaled := by
      simpa [goodScaled, base] using hbase
    _ ≤ base.eventProbability goodPhysical :=
      measureReal_mono hsubset (measure_ne_top _ _)

/-- Conventional unit-vector statement of the manuscript's main theorem. -/
theorem randomizedUnitProductOptimization_main
    (assumptions : AllowedAssumptions)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (hMnorm : frobeniusNorm M ≤ 1) :
    let alg :=
      physicalProductOptimizationProcedure
        assumptions.efficient_haar_sampling
        assumptions.dense_max_four_csp_ptas
        assumptions.gaussian_hypercontractivity
        tau htau d hd M hMnorm
    (∀ seed : alg.Seed,
      vectorNormSq (alg.run () seed).1 = 1 ∧
        vectorNormSq (alg.run () seed).2 = 1) ∧
      alg.eventProbability
        {seed |
          ∀ x y : Fin d → ℂ,
            vectorNormSq x = 1 →
            vectorNormSq y = 1 →
            physicalProductObjective d M x y ≤
              physicalProductObjective d M
                (alg.run () seed).1 (alg.run () seed).2 + tau} ≥
        2 / 3 ∧
      PhysicalProductOptimizerPolynomialRuntime
        assumptions.efficient_haar_sampling
        assumptions.dense_max_four_csp_ptas
        assumptions.gaussian_hypercontractivity tau htau := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact physicalProductOptimizationProcedure_output_unit
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau d hd M hMnorm
  · exact physicalProductOptimizationProcedure_success
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau d hd M hM hMnorm
  · exact physicalProductOptimizationProcedure_polynomial_runtime
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      assumptions.real_ram_model tau htau

end

end QuantumSep
