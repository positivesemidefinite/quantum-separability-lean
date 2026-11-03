import QuantumSep.HighDimensionalMain

/-!
# Explicit numerical parameters

This module removes the numerical side conditions from the high-dimensional
algorithm.  All choices depend only on the requested accuracy and on the
dimension-independent entry constant.
-/

namespace QuantumSep

noncomputable section

def selectedSigma (gamma eta : ℝ) : ℝ :=
  1 + 64 * gamma / eta

def selectedKappa (gamma eta : ℝ) : ℝ :=
  2 * (selectedSigma gamma eta + 1)

def selectedAmplitudeScale (gamma eta : ℝ) : ℝ :=
  gamma * (selectedSigma gamma eta + 1) ^ 4

def selectedTruncation (gamma eta : ℝ) : ℝ :=
  min (1 / 2) (eta / (128 * (selectedAmplitudeScale gamma eta + 1)))

def selectedPenalty (gamma eta : ℝ) : ℝ :=
  (gamma ^ 2 + gamma ^ 2 * selectedKappa gamma eta ^ 4) / eta + 1

def selectedRoundingCoefficient (gamma eta : ℝ) : ℝ :=
  4 * gamma * selectedKappa gamma eta ^ 3 +
    8 * selectedPenalty gamma eta * selectedKappa gamma eta *
      (selectedKappa gamma eta ^ 2 + 1)

def selectedMesh (gamma eta : ℝ) : ℝ :=
  eta / (4 * (selectedRoundingCoefficient gamma eta + 1))

def selectedCSPError (gamma eta : ℝ) : ℝ :=
  eta /
    (8 * matrixPredicateScale gamma
      (selectedKappa gamma eta) (selectedPenalty gamma eta))

def selectedDimensionThreshold (gamma eta : ℝ) : ℕ :=
  Nat.ceil
    (max
      (17 / selectedTruncation gamma eta ^ 2)
      (512 * (selectedAmplitudeScale gamma eta + 1) /
        (eta * selectedTruncation gamma eta ^ 2)))

theorem selectedSigma_pos
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    0 < selectedSigma gamma eta := by
  unfold selectedSigma
  have : 0 ≤ 64 * gamma / eta := div_nonneg (mul_nonneg (by norm_num) hgamma) heta.le
  linarith

theorem selectedKappa_pos
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    0 < selectedKappa gamma eta := by
  unfold selectedKappa
  have := selectedSigma_pos hgamma heta
  positivity

theorem selectedAmplitudeScale_nonneg
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) :
    0 ≤ selectedAmplitudeScale gamma eta := by
  unfold selectedAmplitudeScale
  positivity

theorem selectedTruncation_pos
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    0 < selectedTruncation gamma eta := by
  unfold selectedTruncation
  apply lt_min (by norm_num)
  exact div_pos heta
    (mul_pos (by norm_num)
      (by
        have := selectedAmplitudeScale_nonneg (eta := eta) hgamma
        linarith))

theorem selectedPenalty_pos
    {gamma eta : ℝ} (heta : 0 < eta) :
    0 < selectedPenalty gamma eta := by
  unfold selectedPenalty
  have hnum :
      0 ≤ gamma ^ 2 + gamma ^ 2 * selectedKappa gamma eta ^ 4 := by
    positivity
  have := div_nonneg hnum heta.le
  linarith

theorem selectedRoundingCoefficient_nonneg
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    0 ≤ selectedRoundingCoefficient gamma eta := by
  unfold selectedRoundingCoefficient
  have hk := (selectedKappa_pos hgamma heta).le
  have hpen := (selectedPenalty_pos (gamma := gamma) heta).le
  positivity

theorem selectedMesh_pos
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    0 < selectedMesh gamma eta := by
  unfold selectedMesh
  exact div_pos heta
    (mul_pos (by norm_num)
      (by
        have := selectedRoundingCoefficient_nonneg hgamma heta
        linarith))

theorem selectedCSPError_pos
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    0 < selectedCSPError gamma eta := by
  unfold selectedCSPError
  exact div_pos heta
    (mul_pos (by norm_num)
      (by
        unfold matrixPredicateScale
        have hk := (selectedKappa_pos hgamma heta).le
        have hp := (selectedPenalty_pos (gamma := gamma) heta).le
        positivity))

theorem selectedTruncation_le_half
    (gamma eta : ℝ) :
    selectedTruncation gamma eta ≤ 1 / 2 :=
  min_le_left _ _

theorem selected_truncation_error
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    16 * gamma ≤
      (eta / 4) * selectedSigma gamma eta := by
  calc
    16 * gamma ≤ 16 * gamma + eta / 4 := by linarith
    _ = (eta / 4) * selectedSigma gamma eta := by
      unfold selectedSigma
      field_simp [heta.ne']
      <;> ring

theorem selected_normalization_error
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    32 * selectedTruncation gamma eta *
        selectedAmplitudeScale gamma eta ≤
      eta / 4 := by
  let A := selectedAmplitudeScale gamma eta
  let t := selectedTruncation gamma eta
  have hA : 0 ≤ A :=
    selectedAmplitudeScale_nonneg (eta := eta) hgamma
  have ht : 0 < t :=
    selectedTruncation_pos hgamma heta
  have hden : 0 < 128 * (A + 1) := by positivity
  have htupper :
      t ≤ eta / (128 * (A + 1)) := by
    exact min_le_right _ _
  have hmul :
      128 * (A + 1) * t ≤ eta := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((le_div_iff₀ hden).mp htupper)
  have hAt :
      128 * A * t ≤ 128 * (A + 1) * t := by
    gcongr
    linarith
  change 32 * t * A ≤ eta / 4
  nlinarith

theorem selected_penalty_error
    {gamma eta : ℝ} (heta : 0 < eta) :
    (gamma ^ 2 + gamma ^ 2 * selectedKappa gamma eta ^ 4) /
        (4 * selectedPenalty gamma eta) ≤
      eta / 4 := by
  let numerator :=
    gamma ^ 2 + gamma ^ 2 * selectedKappa gamma eta ^ 4
  have hnum : 0 ≤ numerator := by
    dsimp [numerator]
    positivity
  have hpen : 0 < selectedPenalty gamma eta :=
    selectedPenalty_pos heta
  have hcore :
      numerator ≤ eta * selectedPenalty gamma eta := by
    unfold selectedPenalty
    dsimp [numerator]
    field_simp [heta.ne']
    nlinarith
  apply (div_le_iff₀ (mul_pos (by norm_num) hpen)).2
  nlinarith

theorem selected_rounding_error
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    selectedRoundingCoefficient gamma eta *
        selectedMesh gamma eta ≤
      eta / 4 := by
  let R := selectedRoundingCoefficient gamma eta
  have hR : 0 ≤ R :=
    selectedRoundingCoefficient_nonneg hgamma heta
  have hden : 0 < 4 * (R + 1) := by positivity
  unfold selectedMesh
  change R * (eta / (4 * (R + 1))) ≤ eta / 4
  calc
    R * (eta / (4 * (R + 1))) =
        (R * eta) / (4 * (R + 1)) := by ring
    _ ≤ eta / 4 := by
      apply (div_le_iff₀ hden).2
      nlinarith

theorem selected_csp_error
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    2 * matrixPredicateScale gamma (selectedKappa gamma eta)
          (selectedPenalty gamma eta) *
        selectedCSPError gamma eta =
      eta / 4 := by
  have hscale :
      0 < matrixPredicateScale gamma (selectedKappa gamma eta)
        (selectedPenalty gamma eta) := by
    unfold matrixPredicateScale
    have hk := (selectedKappa_pos hgamma heta).le
    have hp := (selectedPenalty_pos (gamma := gamma) heta).le
    positivity
  unfold selectedCSPError
  field_simp [hscale.ne']
  ring

theorem selected_dimension_conditions
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta)
    {d : ℕ} (hdim : selectedDimensionThreshold gamma eta < d) :
    16 < selectedTruncation gamma eta ^ 2 * (d : ℝ) ∧
      128 * (selectedAmplitudeScale gamma eta + 1) ≤
        (eta / 4) * selectedTruncation gamma eta ^ 2 * (d : ℝ) := by
  let t := selectedTruncation gamma eta
  let A := selectedAmplitudeScale gamma eta
  let required :=
    max (17 / t ^ 2)
      (512 * (A + 1) / (eta * t ^ 2))
  have ht : 0 < t :=
    selectedTruncation_pos hgamma heta
  have hA : 0 ≤ A :=
    selectedAmplitudeScale_nonneg (eta := eta) hgamma
  have hrequiredNonneg : 0 ≤ required := by
    dsimp [required]
    exact le_max_of_le_left
      (div_nonneg (by norm_num) (sq_nonneg t))
  have hceil :
      required ≤ (selectedDimensionThreshold gamma eta : ℝ) := by
    unfold selectedDimensionThreshold
    change required ≤ (Nat.ceil required : ℝ)
    exact_mod_cast Nat.le_ceil required
  have hcastDim :
      (selectedDimensionThreshold gamma eta : ℝ) < d := by
    exact_mod_cast hdim
  have hreqDim : required < d :=
    lt_of_le_of_lt hceil hcastDim
  have hfirst :
      17 / t ^ 2 < d :=
    lt_of_le_of_lt (le_max_left _ _) hreqDim
  have htSq : 0 < t ^ 2 := sq_pos_of_pos ht
  have h17 : 17 < t ^ 2 * d := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((div_lt_iff₀ htSq).mp hfirst)
  have hsecond :
      512 * (A + 1) / (eta * t ^ 2) < d :=
    lt_of_le_of_lt (le_max_right _ _) hreqDim
  have hden : 0 < eta * t ^ 2 := mul_pos heta htSq
  have h512 :
      512 * (A + 1) < eta * t ^ 2 * d := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((div_lt_iff₀ hden).mp hsecond)
  constructor
  · change 16 < t ^ 2 * d
    linarith
  · change 128 * (A + 1) ≤ eta / 4 * t ^ 2 * d
    nlinarith

/-- The explicit valid parameter tuple above the explicit dimension cutoff. -/
def selectedHighDimensionalParameters
    (hc : GaussianHypercontractivityContract)
    (p : ℕ) (eta : ℝ) (heta : 0 < eta)
    (d : ℕ)
    (hdim :
      selectedDimensionThreshold (mainCSPGamma hc p) eta < d) :
    HighDimensionalParameters hc d p := by
  let gamma := mainCSPGamma hc p
  have hgamma : 0 ≤ gamma := mainCSPGamma_nonneg hc p
  have hdimensions :=
    selected_dimension_conditions hgamma heta hdim
  exact {
    sigma := selectedSigma gamma eta
    mesh := selectedMesh gamma eta
    penalty := selectedPenalty gamma eta
    cspError := selectedCSPError gamma eta
    truncation := selectedTruncation gamma eta
    boundedError := eta / 4
    sigma_pos := selectedSigma_pos hgamma heta
    mesh_pos := selectedMesh_pos hgamma heta
    penalty_pos := selectedPenalty_pos heta
    cspError_pos := selectedCSPError_pos hgamma heta
    truncation_pos := selectedTruncation_pos hgamma heta
    truncation_le_half := selectedTruncation_le_half gamma eta
    boundedError_pos := div_pos heta (by norm_num)
    dimension_gt_sixteen := hdimensions.1
    truncation_error := selected_truncation_error hgamma heta
    normalization_error := by
      simpa [selectedAmplitudeScale] using
        selected_normalization_error hgamma heta
    conditional_error := by
      simpa [selectedAmplitudeScale] using hdimensions.2
  }

theorem selected_discretizedOptimizationError_le
    {gamma eta : ℝ} (hgamma : 0 ≤ gamma) (heta : 0 < eta) :
    discretizedOptimizationError
        (selectedSigma gamma eta)
        (selectedMesh gamma eta)
        (selectedPenalty gamma eta)
        gamma
        (selectedCSPError gamma eta)
        (eta / 4) ≤
      eta := by
  have hround := selected_rounding_error hgamma heta
  have hcsp := selected_csp_error hgamma heta
  have hpen := selected_penalty_error (gamma := gamma) heta
  have hround' :
      4 * gamma * (2 * (selectedSigma gamma eta + 1)) ^ 3 *
            selectedMesh gamma eta +
          8 * selectedPenalty gamma eta *
              (2 * (selectedSigma gamma eta + 1)) *
              ((2 * (selectedSigma gamma eta + 1)) ^ 2 + 1) *
            selectedMesh gamma eta ≤
        eta / 4 := by
    unfold selectedRoundingCoefficient selectedKappa at hround
    convert hround using 1 <;> ring
  have hcsp' :
      2 * matrixPredicateScale gamma
            (2 * (selectedSigma gamma eta + 1))
            (selectedPenalty gamma eta) *
          selectedCSPError gamma eta =
        eta / 4 := by
    simpa [selectedKappa] using hcsp
  have hpen' :
      (gamma ^ 2 +
          gamma ^ 2 * (2 * (selectedSigma gamma eta + 1)) ^ 4) /
          (4 * selectedPenalty gamma eta) ≤
        eta / 4 := by
    simpa [selectedKappa] using hpen
  unfold discretizedOptimizationError
  linarith

end

end QuantumSep
