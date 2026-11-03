import QuantumSep.MatrixObjective

/-!
# Bounded-amplitude truncation

This file begins the bounded-amplitude lemma with the deterministic truncation
estimates.  Vectors use the manuscript's scaling `∑ᵢ |xᵢ|² = d`.
-/

open scoped BigOperators

namespace QuantumSep

noncomputable section

variable {ι : Type*}

/-- Coordinate `ℓ₁` norm. -/
def vectorL1 [Fintype ι] (x : ι → ℂ) : ℝ := ∑ i, ‖x i‖

/-- Squared Euclidean norm, kept as a real finite sum. -/
def vectorNormSq [Fintype ι] (x : ι → ℂ) : ℝ :=
  ∑ i, Complex.normSq (x i)

/-- The coordinate `ℓ₁` norm is nonnegative. -/
theorem vectorL1_nonneg [Fintype ι] (x : ι → ℂ) :
    0 ≤ vectorL1 x := by
  unfold vectorL1
  positivity

/-- Delete coordinates whose norm exceeds `sigma`. -/
def truncateVector (sigma : ℝ) (x : ι → ℂ) : ι → ℂ :=
  fun i => if ‖x i‖ ≤ sigma then x i else 0

theorem truncateVector_norm_le (sigma : ℝ) (x : ι → ℂ) (i : ι) :
    ‖truncateVector sigma x i‖ ≤ ‖x i‖ := by
  unfold truncateVector
  split_ifs <;> simp

theorem truncateVector_norm_le_threshold
    (sigma : ℝ) (x : ι → ℂ) (hsigma : 0 ≤ sigma) (i : ι) :
    ‖truncateVector sigma x i‖ ≤ sigma := by
  unfold truncateVector
  split_ifs with h
  · exact h
  · simpa using hsigma

theorem vectorL1_truncate_le [Fintype ι] (sigma : ℝ) (x : ι → ℂ) :
    vectorL1 (truncateVector sigma x) ≤ vectorL1 x := by
  unfold vectorL1
  gcongr with i
  exact truncateVector_norm_le sigma x i

/-- Truncation cannot increase the squared Euclidean norm. -/
theorem vectorNormSq_truncate_le
    [Fintype ι] (sigma : ℝ) (x : ι → ℂ) :
    vectorNormSq (truncateVector sigma x) ≤ vectorNormSq x := by
  unfold vectorNormSq
  apply Finset.sum_le_sum
  intro i _hi
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  exact (sq_le_sq₀
    (norm_nonneg (truncateVector sigma x i))
    (norm_nonneg (x i))).2
      (truncateVector_norm_le sigma x i)

theorem norm_sub_truncateVector_le
    (sigma : ℝ) (x : ι → ℂ) (hsigma : 0 < sigma) (i : ι) :
    ‖x i - truncateVector sigma x i‖ ≤
      Complex.normSq (x i) / sigma := by
  unfold truncateVector
  split_ifs with h
  · simp
    exact div_nonneg (Complex.normSq_nonneg _) hsigma.le
  · simp only [sub_zero]
    rw [Complex.normSq_eq_norm_sq]
    have hlarge : sigma < ‖x i‖ := lt_of_not_ge h
    apply (le_div_iff₀ hsigma).2
    nlinarith [norm_nonneg (x i)]

theorem vectorL1_sub_truncate_le
    [Fintype ι]
    (sigma : ℝ) (x : ι → ℂ) (hsigma : 0 < sigma) :
    vectorL1 (fun i => x i - truncateVector sigma x i) ≤
      vectorNormSq x / sigma := by
  unfold vectorL1 vectorNormSq
  calc
    (∑ i, ‖x i - truncateVector sigma x i‖) ≤
        ∑ i, Complex.normSq (x i) / sigma := by
      gcongr with i
      exact norm_sub_truncateVector_le sigma x hsigma i
    _ = (∑ i, Complex.normSq (x i)) / sigma := by
      rw [Finset.sum_div]

/-- Finite-dimensional Cauchy--Schwarz in the normalization used here. -/
theorem vectorL1_sq_le_card_mul_normSq [Fintype ι] (x : ι → ℂ) :
    vectorL1 x ^ 2 ≤ cardR (ι := ι) * vectorNormSq x := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    Finset.univ (fun i : ι => ‖x i‖) (fun _ => (1 : ℝ))
  unfold vectorL1 vectorNormSq
  simpa [Complex.normSq_eq_norm_sq, cardR, mul_comm] using hcs

/-- A vector with squared norm `d` has `ℓ₁` norm at most `d`. -/
theorem vectorL1_le_card_of_normSq_eq_card
    [Fintype ι]
    (x : ι → ℂ)
    (hnorm : vectorNormSq x = cardR (ι := ι)) :
    vectorL1 x ≤ cardR (ι := ι) := by
  have hcard : 0 ≤ cardR (ι := ι) := by
    unfold cardR
    positivity
  have hl1 : 0 ≤ vectorL1 x := by
    unfold vectorL1
    positivity
  have hsq := vectorL1_sq_le_card_mul_normSq x
  rw [hnorm] at hsq
  nlinarith

/-- The deleted tail has `ℓ₁` norm at most `d / sigma`. -/
theorem vectorL1_sub_truncate_le_card_div
    [Fintype ι]
    (sigma : ℝ) (x : ι → ℂ) (hsigma : 0 < sigma)
    (hnorm : vectorNormSq x = cardR (ι := ι)) :
    vectorL1 (fun i => x i - truncateVector sigma x i) ≤
      cardR (ι := ι) / sigma := by
  rw [← hnorm]
  exact vectorL1_sub_truncate_le sigma x hsigma

/-- Pointwise telescoping estimate in the form needed for `ℓ₁` summation. -/
lemma quartic_coordinate_difference_l1_pointwise
    (xa xb yc ye wa wb zc ze : ℂ) :
    ‖star xa * xb * star yc * ye -
        star wa * wb * star zc * ze‖ ≤
      (‖xa - wa‖ * ‖xb‖ + ‖wa‖ * ‖xb - wb‖) *
          ‖yc‖ * ‖ye‖ +
        ‖wa‖ * ‖wb‖ *
          (‖yc - zc‖ * ‖ye‖ + ‖zc‖ * ‖ye - ze‖) := by
  let A := star (xa - wa) * xb * star yc * ye
  let B := star wa * (xb - wb) * star yc * ye
  let C := star wa * wb * star (yc - zc) * ye
  let D := star wa * wb * star zc * (ye - ze)
  have hid :
      star xa * xb * star yc * ye -
          star wa * wb * star zc * ze =
        A + B + C + D := by
    dsimp [A, B, C, D]
    simp only [map_sub]
    ring
  rw [hid]
  calc
    ‖A + B + C + D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
      calc
        ‖A + B + C + D‖ ≤ ‖A + B + C‖ + ‖D‖ := norm_add_le _ _
        _ ≤ (‖A + B‖ + ‖C‖) + ‖D‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖ := by
          gcongr
          exact norm_add_le _ _
        _ = ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by ring
    _ = _ := by
      dsimp [A, B, C, D]
      simp only [norm_mul, Complex.norm_conj]
      ring

private lemma sum_four_product [Fintype ι] (f g h k : ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ e, f a * g b * h c * k e) =
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) * (∑ e, k e) := by
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]

private lemma sum_quartic_l1_factorization
    [Fintype ι]
    (x y w z : ι → ℂ) :
    (∑ a, ∑ b, ∑ c, ∑ e,
      ((‖x a - w a‖ * ‖x b‖ + ‖w a‖ * ‖x b - w b‖) *
          ‖y c‖ * ‖y e‖ +
        ‖w a‖ * ‖w b‖ *
          (‖y c - z c‖ * ‖y e‖ + ‖z c‖ * ‖y e - z e‖))) =
      (vectorL1 (fun i => x i - w i) * vectorL1 x +
          vectorL1 w * vectorL1 (fun i => x i - w i)) *
          vectorL1 y ^ 2 +
        vectorL1 w ^ 2 *
          (vectorL1 (fun i => y i - z i) * vectorL1 y +
            vectorL1 z * vectorL1 (fun i => y i - z i)) := by
  unfold vectorL1
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib, ← mul_assoc]
  rw [sum_four_product
      (fun i => ‖x i - w i‖) (fun i => ‖x i‖)
      (fun i => ‖y i‖) (fun i => ‖y i‖),
    sum_four_product
      (fun i => ‖w i‖) (fun i => ‖x i - w i‖)
      (fun i => ‖y i‖) (fun i => ‖y i‖),
    sum_four_product
      (fun i => ‖w i‖) (fun i => ‖w i‖)
      (fun i => ‖y i - z i‖) (fun i => ‖y i‖),
    sum_four_product
      (fun i => ‖w i‖) (fun i => ‖w i‖)
      (fun i => ‖z i‖) (fun i => ‖y i - z i‖)]
  ring

/-- Entry flatness and `ℓ₁` errors imply the manuscript's general truncation
estimate before substituting the normalized-vector bounds. -/
theorem abs_matrixQuarticForm_sub_le_l1
    [Fintype ι] [Nonempty ι]
    (M : BipartiteMatrix ι) (x y w z : ι → ℂ)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2) :
    |matrixQuarticForm M x y - matrixQuarticForm M w z| ≤
      gamma / cardR (ι := ι) ^ 4 *
        ((vectorL1 (fun i => x i - w i) * vectorL1 x +
            vectorL1 w * vectorL1 (fun i => x i - w i)) *
            vectorL1 y ^ 2 +
          vectorL1 w ^ 2 *
            (vectorL1 (fun i => y i - z i) * vectorL1 y +
              vectorL1 z * vectorL1 (fun i => y i - z i))) := by
  let f : ι → ι → ι → ι → ℝ := fun a b c e =>
    quarticSummand M x y a b c e -
      quarticSummand M w z a b c e
  let bound : ι → ι → ι → ι → ℝ := fun a b c e =>
    ((‖x a - w a‖ * ‖x b‖ + ‖w a‖ * ‖x b - w b‖) *
        ‖y c‖ * ‖y e‖ +
      ‖w a‖ * ‖w b‖ *
        (‖y c - z c‖ * ‖y e‖ + ‖z c‖ * ‖y e - z e‖))
  have hterm : ∀ a b c e,
      |f a b c e| ≤
        (gamma / cardR (ι := ι) ^ 2) * bound a b c e := by
    intro a b c e
    let p := star (x a) * x b * star (y c) * y e
    let r := star (w a) * w b * star (z c) * z e
    have hdiff : ‖p - r‖ ≤ bound a b c e := by
      exact quartic_coordinate_difference_l1_pointwise
        (x a) (x b) (y c) (y e) (w a) (w b) (z c) (z e)
    have hcoef : 0 ≤ gamma / cardR (ι := ι) ^ 2 :=
      div_nonneg hgamma (sq_nonneg _)
    dsimp only [f]
    have hid :
        quarticSummand M x y a b c e -
            quarticSummand M w z a b c e =
          (M (a, c) (b, e) * (p - r)).re := by
      unfold quarticSummand
      have hp :
          M (a, c) (b, e) * star (x a) * x b * star (y c) * y e =
            M (a, c) (b, e) * p := by
        dsimp [p]
        ring
      have hr :
          M (a, c) (b, e) * star (w a) * w b * star (z c) * z e =
            M (a, c) (b, e) * r := by
        dsimp [r]
        ring
      rw [hp, hr, mul_sub]
      rfl
    rw [hid]
    calc
      |(M (a, c) (b, e) * (p - r)).re| ≤
          ‖M (a, c) (b, e) * (p - r)‖ :=
        Complex.abs_re_le_norm _
      _ = ‖M (a, c) (b, e)‖ * ‖p - r‖ := norm_mul _ _
      _ ≤ (gamma / cardR (ι := ι) ^ 2) * bound a b c e := by
        exact mul_le_mul (hentry a b c e) hdiff
          (norm_nonneg _) hcoef
  have hsum :
      |∑ a, ∑ b, ∑ c, ∑ e, f a b c e| ≤
        ∑ a, ∑ b, ∑ c, ∑ e, |f a b c e| := by
    calc
      |∑ a, ∑ b, ∑ c, ∑ e, f a b c e| ≤
          ∑ a, |∑ b, ∑ c, ∑ e, f a b c e| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, |∑ c, ∑ e, f a b c e| := by
        gcongr with a
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, ∑ c, |∑ e, f a b c e| := by
        gcongr with a b
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, ∑ c, ∑ e, |f a b c e| := by
        gcongr with a b c
        exact Finset.abs_sum_le_sum_abs _ _
  have hcard : 0 < cardR (ι := ι) := by
    unfold cardR
    exact_mod_cast Fintype.card_pos
  unfold matrixQuarticForm
  have hrewrite :
      (∑ a, ∑ b, ∑ c, ∑ e, quarticSummand M x y a b c e) /
            cardR (ι := ι) ^ 2 -
          (∑ a, ∑ b, ∑ c, ∑ e, quarticSummand M w z a b c e) /
            cardR (ι := ι) ^ 2 =
        (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) /
          cardR (ι := ι) ^ 2 := by
    dsimp [f]
    simp_rw [Finset.sum_sub_distrib]
    ring
  rw [hrewrite, abs_div]
  have habsCard :
      |cardR (ι := ι) ^ 2| = cardR (ι := ι) ^ 2 :=
    abs_of_pos (sq_pos_of_pos hcard)
  rw [habsCard]
  calc
    |∑ a, ∑ b, ∑ c, ∑ e, f a b c e| /
          cardR (ι := ι) ^ 2 ≤
        (∑ a, ∑ b, ∑ c, ∑ e, |f a b c e|) /
          cardR (ι := ι) ^ 2 := by gcongr
    _ ≤
        (∑ a, ∑ b, ∑ c, ∑ e,
          (gamma / cardR (ι := ι) ^ 2) * bound a b c e) /
          cardR (ι := ι) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro a _ha
      apply Finset.sum_le_sum
      intro b _hb
      apply Finset.sum_le_sum
      intro c _hc
      apply Finset.sum_le_sum
      intro e _he
      exact hterm a b c e
    _ = gamma / cardR (ι := ι) ^ 4 *
        ((vectorL1 (fun i => x i - w i) * vectorL1 x +
            vectorL1 w * vectorL1 (fun i => x i - w i)) *
            vectorL1 y ^ 2 +
          vectorL1 w ^ 2 *
            (vectorL1 (fun i => y i - z i) * vectorL1 y +
              vectorL1 z * vectorL1 (fun i => y i - z i))) := by
      simp_rw [← Finset.mul_sum]
      rw [sum_quartic_l1_factorization]
      field_simp

/-- Truncating both normalized vectors at threshold `sigma` changes the flat
quartic objective by at most `4 * gamma / sigma`. -/
theorem abs_matrixQuarticForm_sub_truncate_le
    [Fintype ι] [Nonempty ι]
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (gamma sigma : ℝ)
    (hgamma : 0 ≤ gamma) (hsigma : 0 < sigma)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hnormx : vectorNormSq x = cardR (ι := ι))
    (hnormy : vectorNormSq y = cardR (ι := ι)) :
    |matrixQuarticForm M x y -
        matrixQuarticForm M
          (truncateVector sigma x) (truncateVector sigma y)| ≤
      4 * gamma / sigma := by
  have hcard : 0 < cardR (ι := ι) := by
    unfold cardR
    exact_mod_cast Fintype.card_pos
  have hl1x : vectorL1 x ≤ cardR (ι := ι) :=
    vectorL1_le_card_of_normSq_eq_card x hnormx
  have hl1y : vectorL1 y ≤ cardR (ι := ι) :=
    vectorL1_le_card_of_normSq_eq_card y hnormy
  have hl1tx :
      vectorL1 (truncateVector sigma x) ≤ cardR (ι := ι) :=
    le_trans (vectorL1_truncate_le sigma x) hl1x
  have hl1ty :
      vectorL1 (truncateVector sigma y) ≤ cardR (ι := ι) :=
    le_trans (vectorL1_truncate_le sigma y) hl1y
  have htailx :
      vectorL1 (fun i => x i - truncateVector sigma x i) ≤
        cardR (ι := ι) / sigma :=
    vectorL1_sub_truncate_le_card_div sigma x hsigma hnormx
  have htaily :
      vectorL1 (fun i => y i - truncateVector sigma y i) ≤
        cardR (ι := ι) / sigma :=
    vectorL1_sub_truncate_le_card_div sigma y hsigma hnormy
  have hgeneral := abs_matrixQuarticForm_sub_le_l1
    M x y (truncateVector sigma x) (truncateVector sigma y)
    gamma hgamma hentry
  have hcoefficient :
      0 ≤ gamma / cardR (ι := ι) ^ 4 := by positivity
  have hl1x0 : 0 ≤ vectorL1 x := vectorL1_nonneg x
  have hl1y0 : 0 ≤ vectorL1 y := vectorL1_nonneg y
  have hl1tx0 : 0 ≤ vectorL1 (truncateVector sigma x) :=
    vectorL1_nonneg _
  have hl1ty0 : 0 ≤ vectorL1 (truncateVector sigma y) :=
    vectorL1_nonneg _
  have htailx0 :
      0 ≤ vectorL1 (fun i => x i - truncateVector sigma x i) :=
    vectorL1_nonneg _
  have htaily0 :
      0 ≤ vectorL1 (fun i => y i - truncateVector sigma y i) :=
    vectorL1_nonneg _
  calc
    |matrixQuarticForm M x y -
        matrixQuarticForm M
          (truncateVector sigma x) (truncateVector sigma y)| ≤
      gamma / cardR (ι := ι) ^ 4 *
        ((vectorL1 (fun i => x i - truncateVector sigma x i) *
              vectorL1 x +
            vectorL1 (truncateVector sigma x) *
              vectorL1 (fun i => x i - truncateVector sigma x i)) *
            vectorL1 y ^ 2 +
          vectorL1 (truncateVector sigma x) ^ 2 *
            (vectorL1 (fun i => y i - truncateVector sigma y i) *
                vectorL1 y +
              vectorL1 (truncateVector sigma y) *
                vectorL1 (fun i => y i - truncateVector sigma y i))) :=
      hgeneral
    _ ≤ gamma / cardR (ι := ι) ^ 4 *
        (((cardR (ι := ι) / sigma) * cardR (ι := ι) +
            cardR (ι := ι) * (cardR (ι := ι) / sigma)) *
            cardR (ι := ι) ^ 2 +
          cardR (ι := ι) ^ 2 *
            ((cardR (ι := ι) / sigma) * cardR (ι := ι) +
              cardR (ι := ι) *
                (cardR (ι := ι) / sigma))) := by
      gcongr
    _ = 4 * gamma / sigma := by
      field_simp
      ring

/-- Absolute quartic bound in terms of coordinate `ℓ₁` norms. -/
theorem abs_matrixQuarticForm_le_l1
    [Fintype ι] [Nonempty ι]
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2) :
    |matrixQuarticForm M x y| ≤
      gamma / cardR (ι := ι) ^ 4 *
        (vectorL1 x ^ 2 * vectorL1 y ^ 2) := by
  have h := abs_matrixQuarticForm_sub_le_l1
    M x y (fun _ => 0) (fun _ => 0) gamma hgamma hentry
  have hzero :
      matrixQuarticForm M (fun _ => 0) (fun _ => 0) = 0 := by
    simp [matrixQuarticForm, quarticSummand]
  rw [hzero, sub_zero] at h
  simpa [vectorL1, pow_two] using h

theorem vectorL1_le_card_mul_of_coordinate_bound
    [Fintype ι]
    (x : ι → ℂ) (K : ℝ)
    (hx : ∀ i, ‖x i‖ ≤ K) :
    vectorL1 x ≤ cardR (ι := ι) * K := by
  unfold vectorL1 cardR
  calc
    (∑ i, ‖x i‖) ≤ ∑ _i : ι, K := by
      gcongr with i
      exact hx i
    _ = Fintype.card ι * K := by simp

/-- A uniform coordinate bound gives the manuscript's global quartic bound. -/
theorem abs_matrixQuarticForm_le_of_coordinate_bound
    [Fintype ι] [Nonempty ι]
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (gamma K : ℝ)
    (hgamma : 0 ≤ gamma) (_hK : 0 ≤ K)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hx : ∀ i, ‖x i‖ ≤ K)
    (hy : ∀ i, ‖y i‖ ≤ K) :
    |matrixQuarticForm M x y| ≤ gamma * K ^ 4 := by
  have hd : 0 < cardR (ι := ι) := by
    unfold cardR
    exact_mod_cast Fintype.card_pos
  have hl1x := vectorL1_le_card_mul_of_coordinate_bound x K hx
  have hl1y := vectorL1_le_card_mul_of_coordinate_bound y K hy
  have hbase := abs_matrixQuarticForm_le_l1
    M x y gamma hgamma hentry
  have hl1x0 := vectorL1_nonneg x
  have hl1y0 := vectorL1_nonneg y
  calc
    |matrixQuarticForm M x y| ≤
        gamma / cardR (ι := ι) ^ 4 *
          (vectorL1 x ^ 2 * vectorL1 y ^ 2) := hbase
    _ ≤ gamma / cardR (ι := ι) ^ 4 *
          ((cardR (ι := ι) * K) ^ 2 *
            (cardR (ι := ι) * K) ^ 2) := by
      gcongr
    _ = gamma * K ^ 4 := by
      field_simp [ne_of_gt hd]

end

end QuantumSep
