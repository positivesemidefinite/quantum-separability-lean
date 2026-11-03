import QuantumSep.Normalization

/-!
# From the penalized objective back to normalized product vectors

This is the matrix-level version of Claim 1 in the discretization argument,
including the zero-vector fallback omitted by the displayed manuscript
formula.
-/

namespace QuantumSep

open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem denseAverage1_coordinateNormPenalty_eq
    (x : ι → ℂ) :
    denseAverage1 (coordinateNormPenalty x) =
      vectorNormSq x / Fintype.card ι - 1 := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold denseAverage1 coordinateNormPenalty vectorNormSq cardR
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp [hd]

theorem normRatio_le_sq_of_coordinate_bound
    (x : ι → ℂ) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hx : ∀ i, ‖x i‖ ≤ kappa) :
    vectorNormSq x / Fintype.card ι ≤ kappa ^ 2 := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hsum :
      vectorNormSq x ≤ Fintype.card ι * kappa ^ 2 := by
    unfold vectorNormSq
    calc
      (∑ i, Complex.normSq (x i)) ≤ ∑ _i : ι, kappa ^ 2 := by
        gcongr with i
        rw [Complex.normSq_eq_norm_sq]
        exact (sq_le_sq₀ (norm_nonneg _) hkappa).mpr (hx i)
      _ = Fintype.card ι * kappa ^ 2 := by simp
  exact (div_le_iff₀ hd).mpr (by simpa [mul_comm] using hsum)

/-- A normalized pair has quartic value bounded by the entry-flatness
parameter. -/
theorem abs_matrixQuarticForm_le_of_normalized
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hx : vectorNormSq x = Fintype.card ι)
    (hy : vectorNormSq y = Fintype.card ι) :
    |matrixQuarticForm M x y| ≤ gamma := by
  have hd : 0 < cardR (ι := ι) := by
    unfold cardR
    exact_mod_cast Fintype.card_pos
  have hl1x :=
    vectorL1_le_card_of_normSq_eq_card x (by simpa [cardR] using hx)
  have hl1y :=
    vectorL1_le_card_of_normSq_eq_card y (by simpa [cardR] using hy)
  have hbase := abs_matrixQuarticForm_le_l1 M x y gamma hgamma hentry
  have hx0 := vectorL1_nonneg x
  have hy0 := vectorL1_nonneg y
  calc
    |matrixQuarticForm M x y| ≤
        gamma / cardR (ι := ι) ^ 4 *
          (vectorL1 x ^ 2 * vectorL1 y ^ 2) := hbase
    _ ≤ gamma / cardR (ι := ι) ^ 4 *
          (cardR (ι := ι) ^ 2 * cardR (ι := ι) ^ 2) := by
      gcongr
    _ = gamma := by
      field_simp [ne_of_gt hd]

/-- Every bounded pair is dominated by its total normalization up to the
two explicit completing-square costs. -/
theorem matrixPenalizedObjective_le_normalized
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (gamma kappa penalty : ℝ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hpenalty : 0 < penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hxcoord : ∀ i, ‖x i‖ ≤ kappa) :
    matrixPenalizedObjective M penalty x y ≤
      matrixQuarticForm M
          (normalizeVectorOrOne x) (normalizeVectorOrOne y) +
        (gamma ^ 2 + gamma ^ 2 * kappa ^ 4) / (4 * penalty) := by
  let rx := vectorNormSq x / Fintype.card ι
  let ry := vectorNormSq y / Fintype.card ι
  let qn :=
    matrixQuarticForm M
      (normalizeVectorOrOne x) (normalizeVectorOrOne y)
  have hrx0 : 0 ≤ rx := by
    dsimp [rx]
    exact div_nonneg (vectorNormSq_nonneg x)
      (by exact_mod_cast (Nat.zero_le (Fintype.card ι)))
  have hrx : rx ≤ kappa ^ 2 :=
    normRatio_le_sq_of_coordinate_bound x kappa hkappa hxcoord
  have hproduct :
      matrixQuarticForm M x y = rx * ry * qn := by
    exact matrixQuarticForm_eq_normRatios_mul_normalizeVectorOrOne M x y
  have hqn :
      |qn| ≤ gamma := by
    apply abs_matrixQuarticForm_le_of_normalized
      M (normalizeVectorOrOne x) (normalizeVectorOrOne y)
      gamma hgamma hentry
    · exact vectorNormSq_normalizeVectorOrOne x
    · exact vectorNormSq_normalizeVectorOrOne y
  have hscalar :=
    penalized_to_normalized_lower_bound
      (matrixQuarticForm M x y) qn rx ry gamma kappa penalty
      hgamma hpenalty hrx0 hrx hproduct hqn
  unfold matrixPenalizedObjective
  rw [denseAverage1_coordinateNormPenalty_eq,
    denseAverage1_coordinateNormPenalty_eq]
  exact hscalar

end

end QuantumSep
