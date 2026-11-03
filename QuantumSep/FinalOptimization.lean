import QuantumSep.NumericalParameters

/-!
# The fully instantiated high-dimensional optimizer

All moment, tail, discretization, and dimension parameters are now explicit
functions of the requested additive accuracy.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory

noncomputable section

def effectiveAccuracy (tau : ℝ) : ℝ :=
  min tau 1

def mainTailAccuracy (tau : ℝ) : ℝ :=
  effectiveAccuracy tau / 8

def mainDiscretizationAccuracy (tau : ℝ) : ℝ :=
  effectiveAccuracy tau / 4

def mainMomentOrder
    (hc : GaussianHypercontractivityContract) (tau : ℝ) : ℕ :=
  flatMomentOrder (flatDecayInteger hc) (mainTailAccuracy tau)

def mainDimensionCutoff
    (hc : GaussianHypercontractivityContract) (tau : ℝ) : ℕ :=
  let alpha := effectiveAccuracy tau
  let p := mainMomentOrder hc tau
  max 1
    (max (8 * p)
      (max
        (selectedDimensionThreshold
            (mainCSPGamma hc p) (alpha / 4) + 1)
        (Nat.ceil (64 / alpha ^ 2))))

theorem effectiveAccuracy_pos
    {tau : ℝ} (htau : 0 < tau) :
    0 < effectiveAccuracy tau := by
  unfold effectiveAccuracy
  exact lt_min htau zero_lt_one

theorem effectiveAccuracy_le_tau (tau : ℝ) :
    effectiveAccuracy tau ≤ tau :=
  min_le_left _ _

theorem effectiveAccuracy_le_one (tau : ℝ) :
    effectiveAccuracy tau ≤ 1 :=
  min_le_right _ _

theorem mainTailAccuracy_pos
    {tau : ℝ} (htau : 0 < tau) :
    0 < mainTailAccuracy tau := by
  unfold mainTailAccuracy
  exact div_pos (effectiveAccuracy_pos htau) (by norm_num)

theorem mainTailAccuracy_lt_one
    {tau : ℝ} (htau : 0 < tau) :
    mainTailAccuracy tau < 1 := by
  have ha := effectiveAccuracy_le_one tau
  unfold mainTailAccuracy
  linarith

theorem mainMomentOrder_pos
    (hc : GaussianHypercontractivityContract)
    {tau : ℝ} (htau : 0 < tau) :
    0 < mainMomentOrder hc tau := by
  unfold mainMomentOrder
  exact (flatMomentOrder_bounds
    (flatDecayInteger hc)
    (by
      have := flatDecayInteger_ge_four hc
      omega)
    (mainTailAccuracy tau)
    (mainTailAccuracy_pos htau)
    (mainTailAccuracy_lt_one htau)).1

theorem mainMomentOrder_decay
    (hc : GaussianHypercontractivityContract)
    {tau : ℝ} (htau : 0 < tau) :
    64 * flatMomentConstant hc ^ 2 *
          (mainMomentOrder hc tau : ℝ) ^ 4 /
        (8 : ℝ) ^ (2 * mainMomentOrder hc tau) ≤
      mainTailAccuracy tau ^ 4 := by
  unfold mainMomentOrder
  exact flatMomentOrder_decay
    (flatMomentConstant hc) (flatDecayInteger hc)
    (flatDecayInteger_ge_four hc)
    (flatDecayInteger_choice hc)
    (mainTailAccuracy tau)
    (mainTailAccuracy_pos htau)
    (mainTailAccuracy_lt_one htau)

theorem mainTailAccuracy_probability
    {tau : ℝ} (htau : 0 < tau) :
    mainTailAccuracy tau ^ 2 ≤ 1 / 6 := by
  have ha0 := (effectiveAccuracy_pos htau).le
  have ha1 := effectiveAccuracy_le_one tau
  have hsq : effectiveAccuracy tau ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1)
      (by linarith : 0 ≤ 1 + effectiveAccuracy tau)]
  unfold mainTailAccuracy
  nlinarith

theorem local_error_le_of_dimension
    {tau : ℝ} (htau : 0 < tau)
    {d : ℕ} (hdim : 64 / tau ^ 2 ≤ (d : ℝ)) :
    4 / Real.sqrt d ≤ tau / 2 := by
  have hdreal : 0 < (d : ℝ) := by
    have hleft : 0 < 64 / tau ^ 2 := by positivity
    exact lt_of_lt_of_le hleft hdim
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  apply (div_le_iff₀ hsqrt).2
  have hsqrtSq :
      (Real.sqrt (d : ℝ)) ^ 2 = d :=
    Real.sq_sqrt hdreal.le
  have hmul : 64 ≤ tau ^ 2 * d := by
    simpa [mul_comm] using
      ((div_le_iff₀ (sq_pos_of_pos htau)).mp hdim)
  have hright : 0 ≤ tau / 2 * Real.sqrt d := by positivity
  have hsq :
      (4 : ℝ) ^ 2 ≤
        (tau / 2 * Real.sqrt d) ^ 2 := by
    rw [mul_pow, hsqrtSq]
    nlinarith
  nlinarith [sq_nonneg (4 - tau / 2 * Real.sqrt d)]

theorem mainDimensionCutoff_data
    (hc : GaussianHypercontractivityContract)
    {tau : ℝ} (htau : 0 < tau)
    {d : ℕ} (hdim : mainDimensionCutoff hc tau ≤ d) :
    0 < d ∧
      8 * mainMomentOrder hc tau ≤ d ∧
      selectedDimensionThreshold
          (mainCSPGamma hc (mainMomentOrder hc tau))
          (mainDiscretizationAccuracy tau) < d ∧
      64 / effectiveAccuracy tau ^ 2 ≤ (d : ℝ) := by
  let alpha := effectiveAccuracy tau
  let p := mainMomentOrder hc tau
  have hone : 1 ≤ d := by
    apply le_trans _ hdim
    unfold mainDimensionCutoff
    exact le_max_left _ _
  have hpdim : 8 * p ≤ d := by
    apply le_trans _ hdim
    unfold mainDimensionCutoff
    exact le_trans (le_max_left _ _)
      (le_max_right _ _)
  have hselectedPlus :
      selectedDimensionThreshold
          (mainCSPGamma hc p) (alpha / 4) + 1 ≤ d := by
    apply le_trans _ hdim
    unfold mainDimensionCutoff
    exact le_trans
      (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)
  have hceilNat :
      Nat.ceil (64 / alpha ^ 2) ≤ d := by
    apply le_trans _ hdim
    unfold mainDimensionCutoff
    exact le_trans
      (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)
  have hceilReal :
      64 / alpha ^ 2 ≤
        (Nat.ceil (64 / alpha ^ 2) : ℝ) := by
    exact Nat.le_ceil _
  have hceilCast :
      (Nat.ceil (64 / alpha ^ 2) : ℝ) ≤ d := by
    exact_mod_cast hceilNat
  refine ⟨by omega, ?_, ?_, ?_⟩
  · simpa [p] using hpdim
  · have : selectedDimensionThreshold
        (mainCSPGamma hc p) (alpha / 4) < d := by omega
    simpa [p, alpha, mainDiscretizationAccuracy] using this
  · simpa [alpha] using hceilReal.trans hceilCast

/-- The completely instantiated high-dimensional algorithm. -/
def instantiatedHighDimensionalProcedure
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hdim : mainDimensionCutoff hc tau ≤ d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1) :
    RandomizedProcedure Unit ((Fin d → ℂ) × (Fin d → ℂ)) := by
  let p := mainMomentOrder hc tau
  have hdata := mainDimensionCutoff_data hc htau hdim
  let params :=
    selectedHighDimensionalParameters hc p
      (mainDiscretizationAccuracy tau)
      (by
        unfold mainDiscretizationAccuracy
        exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
      d hdata.2.2.1
  exact highDimensionalOptimizationProcedure
    sampler ptas hc d hdata.1 M hMnorm p params

theorem instantiatedHighDimensionalProcedure_output_normalized
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hdim : mainDimensionCutoff hc tau ≤ d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (seed :
      (instantiatedHighDimensionalProcedure
        sampler ptas hc tau htau d hdim M hMnorm).Seed) :
    let alg :=
      instantiatedHighDimensionalProcedure
        sampler ptas hc tau htau d hdim M hMnorm
    vectorNormSq (alg.run () seed).1 = d ∧
      vectorNormSq (alg.run () seed).2 = d := by
  let p := mainMomentOrder hc tau
  have hdata := mainDimensionCutoff_data hc htau hdim
  let params :=
    selectedHighDimensionalParameters hc p
      (mainDiscretizationAccuracy tau)
      (by
        unfold mainDiscretizationAccuracy
        exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
      d hdata.2.2.1
  change
    vectorNormSq
        ((highDimensionalOptimizationProcedure sampler ptas hc d hdata.1 M
          hMnorm p params).run () seed).1 = d ∧
      vectorNormSq
        ((highDimensionalOptimizationProcedure sampler ptas hc d hdata.1 M
          hMnorm p params).run () seed).2 = d
  exact highDimensionalOptimizationProcedure_output_normalized
    sampler ptas hc d hdata.1 M hMnorm p params seed

theorem instantiatedHighDimensionalProcedure_runtime_bound
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hdim : mainDimensionCutoff hc tau ≤ d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (seed :
      (instantiatedHighDimensionalProcedure
        sampler ptas hc tau htau d hdim M hMnorm).Seed) :
    let p := mainMomentOrder hc tau
    let hdata := mainDimensionCutoff_data hc htau hdim
    let params :=
      selectedHighDimensionalParameters hc p
        (mainDiscretizationAccuracy tau)
        (by
          unfold mainDiscretizationAccuracy
          exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
        d hdata.2.2.1
    (instantiatedHighDimensionalProcedure
        sampler ptas hc tau htau d hdim M hMnorm).runtime () seed ≤
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
  dsimp only
  let p := mainMomentOrder hc tau
  have hdata := mainDimensionCutoff_data hc htau hdim
  let params :=
    selectedHighDimensionalParameters hc p
      (mainDiscretizationAccuracy tau)
      (by
        unfold mainDiscretizationAccuracy
        exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
      d hdata.2.2.1
  change
    (highDimensionalOptimizationProcedure sampler ptas hc d hdata.1 M
      hMnorm p params).runtime () seed ≤ _
  exact highDimensionalOptimizationProcedure_runtime_bound
    sampler ptas hc d hdata.1 M hMnorm p params seed

/-- Above the explicit cutoff, the instantiated algorithm is an additive
`tau` product-vector optimizer with probability at least `2/3`. -/
theorem instantiatedHighDimensionalProcedure_success
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hdim : mainDimensionCutoff hc tau ≤ d)
    (M : BipartiteMatrix (Fin d))
    (hM : M.IsHermitian)
    (hMnorm : frobeniusNorm M ≤ 1) :
    let alg :=
      instantiatedHighDimensionalProcedure
        sampler ptas hc tau htau d hdim M hMnorm
    alg.eventProbability
      {seed |
        ∀ x y : Fin d → ℂ,
          vectorNormSq x = d →
          vectorNormSq y = d →
          matrixQuarticForm M x y ≤
            matrixQuarticForm M
              (alg.run () seed).1 (alg.run () seed).2 + tau} ≥
      2 / 3 := by
  dsimp only
  let alpha := effectiveAccuracy tau
  let delta := mainTailAccuracy tau
  let eta := mainDiscretizationAccuracy tau
  let p := mainMomentOrder hc tau
  have hdata := mainDimensionCutoff_data hc htau hdim
  let params :=
    selectedHighDimensionalParameters hc p eta
      (by
        dsimp [eta, mainDiscretizationAccuracy]
        exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
      d (by simpa [p, eta] using hdata.2.2.1)
  let alg :=
    highDimensionalOptimizationProcedure
      sampler ptas hc d hdata.1 M hMnorm p params
  letI : MeasurableSpace alg.Seed := alg.seedMeasurableSpace
  letI : IsProbabilityMeasure alg.seedMeasure := alg.seedProbability
  let preciseGood : Set alg.Seed :=
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
          2 * delta + 4 / Real.sqrt d}
  let targetGood : Set alg.Seed :=
    {seed |
      ∀ x y : Fin d → ℂ,
        vectorNormSq x = d →
        vectorNormSq y = d →
        matrixQuarticForm M x y ≤
          matrixQuarticForm M
            (alg.run () seed).1 (alg.run () seed).2 + tau}
  have hprecise :
      alg.eventProbability preciseGood ≥ 2 / 3 := by
    simpa [alg, preciseGood, p, delta] using
      highDimensionalOptimizationProcedure_success
        sampler ptas hc d hdata.1 M hM hMnorm p
        (mainMomentOrder_pos hc htau) hdata.2.1
        delta (by simpa [delta] using mainTailAccuracy_pos htau)
        (by simpa [delta] using mainTailAccuracy_probability htau)
        (by simpa [p, delta] using mainMomentOrder_decay hc htau)
        params
  have hdisc :
      discretizedOptimizationError
          params.sigma params.mesh params.penalty
          (mainCSPGamma hc p) params.cspError
          params.boundedError ≤ eta := by
    simpa [params, selectedHighDimensionalParameters] using
      selected_discretizedOptimizationError_le
        (mainCSPGamma_nonneg hc p)
        (by
          dsimp [eta, mainDiscretizationAccuracy]
          exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
  have hlocal :
      4 / Real.sqrt d ≤ alpha / 2 := by
    exact local_error_le_of_dimension
      (effectiveAccuracy_pos htau) hdata.2.2.2
  have htotal :
      discretizedOptimizationError
          params.sigma params.mesh params.penalty
          (mainCSPGamma hc p) params.cspError
          params.boundedError +
          2 * delta + 4 / Real.sqrt d ≤ tau := by
    have halpha := effectiveAccuracy_le_tau tau
    dsimp [eta, mainDiscretizationAccuracy,
      delta, mainTailAccuracy] at hdisc ⊢
    dsimp [alpha] at hlocal
    linarith
  have hsubset : preciseGood ⊆ targetGood := by
    intro seed hseed
    intro x y hx hy
    have hs := hseed x y hx hy
    linarith
  change alg.eventProbability targetGood ≥ 2 / 3
  exact hprecise.trans
    (measureReal_mono hsubset (measure_ne_top _ _))

end

end QuantumSep
