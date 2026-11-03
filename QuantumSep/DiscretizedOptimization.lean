import QuantumSep.MatrixCSPReduction
import QuantumSep.PenalizedNormalization
import QuantumSep.BoundedAmplitudeMain

/-!
# Deterministic correctness of a successful CSP call

This theorem assembles only proved ingredients: coordinatewise net rounding,
the exact CSP-value identity, and total normalization of the returned
assignment.
-/

namespace QuantumSep

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Output vectors extracted and normalized from a CSP assignment. -/
def normalizedCSPOutputX
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (assignment : ι → MatrixCSPAlphabet net) : ι → ℂ :=
  normalizeVectorOrOne (matrixCSPAssignmentX net assignment)

def normalizedCSPOutputY
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (assignment : ι → MatrixCSPAlphabet net) : ι → ℂ :=
  normalizeVectorOrOne (matrixCSPAssignmentY net assignment)

theorem normalizedCSPOutputX_normSq
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (assignment : ι → MatrixCSPAlphabet net) :
    vectorNormSq (normalizedCSPOutputX net assignment) =
      Fintype.card ι :=
  vectorNormSq_normalizeVectorOrOne _

theorem normalizedCSPOutputY_normSq
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (assignment : ι → MatrixCSPAlphabet net) :
    vectorNormSq (normalizedCSPOutputY net assignment) =
      Fintype.card ι :=
  vectorNormSq_normalizeVectorOrOne _

/-- Correctness of one successful finite-CSP call against every normalized,
coordinate-bounded competitor. -/
theorem successfulCSP_output_approximates_bounded
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (M : BipartiteMatrix ι)
    (penalty gamma cspError : ℝ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hepsilon : 0 ≤ epsilon) (hpenalty : 0 < penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (output : ι → MatrixCSPAlphabet net)
    (hsuccess : ∀ assignment,
      (matrixDenseMaxFourCSP net M penalty gamma
        hgamma hkappa hpenalty.le hentry).value assignment ≤
      (matrixDenseMaxFourCSP net M penalty gamma
        hgamma hkappa hpenalty.le hentry).value output + cspError) :
    ∀ x y : ι → ℂ,
      vectorNormSq x = Fintype.card ι →
      vectorNormSq y = Fintype.card ι →
      (∀ i, ‖x i‖ ≤ kappa) →
      (∀ i, ‖y i‖ ≤ kappa) →
      matrixQuarticForm M x y ≤
        matrixQuarticForm M
          (normalizedCSPOutputX net output)
          (normalizedCSPOutputY net output) +
        (4 * gamma * kappa ^ 3 * epsilon +
          8 * penalty * kappa * (kappa ^ 2 + 1) * epsilon) +
        2 * matrixPredicateScale gamma kappa penalty * cspError +
        (gamma ^ 2 + gamma ^ 2 * kappa ^ 4) / (4 * penalty) := by
  intro x y hxnorm hynorm hxcoord hycoord
  let rounded := matrixCSPRoundedAssignment net x y hxcoord hycoord
  have hround :=
    matrixPenalizedObjective_roundVector
      net M penalty gamma x y hgamma hkappa hepsilon hpenalty.le
      hentry hxcoord hycoord
  have hcompare :=
    matrixCSP_success_to_penalized
      net M penalty gamma cspError hgamma hkappa hpenalty.le hentry
      output hsuccess rounded
  have houtcoord :
      ∀ i, ‖matrixCSPAssignmentX net output i‖ ≤ kappa := by
    intro i
    exact net.points_mem _ (output i).1.2
  have hnormalize :=
    matrixPenalizedObjective_le_normalized
      M (matrixCSPAssignmentX net output)
        (matrixCSPAssignmentY net output)
      gamma kappa penalty hgamma hkappa hpenalty hentry houtcoord
  have hnormalizedPenalty :
      matrixPenalizedObjective M penalty x y =
        matrixQuarticForm M x y := by
    unfold matrixPenalizedObjective
    rw [denseAverage1_coordinateNormPenalty_eq,
      denseAverage1_coordinateNormPenalty_eq, hxnorm, hynorm]
    have hd : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp [hd]
    ring
  rw [matrixCSPAssignmentX_rounded,
    matrixCSPAssignmentY_rounded] at hcompare
  dsimp [normalizedCSPOutputX, normalizedCSPOutputY] at hnormalize ⊢
  rw [hnormalizedPenalty] at hround
  have hroundLower :
      matrixQuarticForm M x y ≤
        matrixPenalizedObjective M penalty
          (net.roundVector x) (net.roundVector y) +
        (4 * gamma * kappa ^ 3 * epsilon +
          8 * penalty * kappa * (kappa ^ 2 + 1) * epsilon) := by
    have hdifference := (abs_le.mp hround).2
    linarith
  linarith

/-- Adding the proved bounded-amplitude theorem extends the successful CSP
guarantee from bounded competitors to every normalized product vector. -/
theorem successfulCSP_output_approximates_all
    (sigma mesh : ℝ)
    (net : ComplexDiskNet (2 * (sigma + 1)) mesh)
    (M : BipartiteMatrix ι)
    (penalty gamma cspError t boundedError : ℝ)
    (hgamma : 0 ≤ gamma) (hsigma : 0 < sigma)
    (hmesh : 0 ≤ mesh) (hpenalty : 0 < penalty)
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
        boundedError * t ^ 2 * Fintype.card ι)
    (output : ι → MatrixCSPAlphabet net)
    (hsuccess : ∀ assignment,
      (matrixDenseMaxFourCSP net M penalty gamma
        hgamma (by positivity) hpenalty.le hentry).value assignment ≤
      (matrixDenseMaxFourCSP net M penalty gamma
        hgamma (by positivity) hpenalty.le hentry).value output + cspError) :
    ∀ x y : ι → ℂ,
      vectorNormSq x = Fintype.card ι →
      vectorNormSq y = Fintype.card ι →
      matrixQuarticForm M x y ≤
        matrixQuarticForm M
          (normalizedCSPOutputX net output)
          (normalizedCSPOutputY net output) +
        boundedError +
        (4 * gamma * (2 * (sigma + 1)) ^ 3 * mesh +
          8 * penalty * (2 * (sigma + 1)) *
            ((2 * (sigma + 1)) ^ 2 + 1) * mesh) +
        2 * matrixPredicateScale gamma (2 * (sigma + 1)) penalty *
          cspError +
        (gamma ^ 2 + gamma ^ 2 * (2 * (sigma + 1)) ^ 4) /
          (4 * penalty) := by
  intro x y hxnorm hynorm
  obtain ⟨xhat, yhat, hxhatNorm, hyhatNorm,
      hxhatCoord, hyhatCoord, hvalue⟩ :=
    exists_bounded_normalized_quartic_witness_within
      M x y gamma sigma t boundedError
      hgamma hsigma htpos ht hboundedError
      hxnorm hynorm hentry htrace0 htrace1
      hden16 htrunc hnormalize hconditional
  have hbounded :=
    successfulCSP_output_approximates_bounded
      net M penalty gamma cspError hgamma (by positivity) hmesh
      hpenalty hentry output hsuccess
      xhat yhat hxhatNorm hyhatNorm hxhatCoord hyhatCoord
  linarith

end

end QuantumSep
