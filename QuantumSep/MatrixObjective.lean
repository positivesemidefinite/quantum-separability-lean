import QuantumSep.DenseCSP
import QuantumSep.MatrixPrelim
import QuantumSep.ScalarInequalities

/-!
# Concrete matrix objective and dense-CSP instance

This file instantiates the generic repeated-index calculation from
`DenseCSP.lean` with the manuscript's complex quartic form.
-/

open scoped BigOperators ComplexConjugate

namespace QuantumSep

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- One real quartic summand of the product-state matrix objective. -/
def quarticSummand
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (a b c e : ι) : ℝ :=
  (M (a, c) (b, e) * star (x a) * x b * star (y c) * y e).re

/-- The manuscript's quartic form, normalized by the square of the
dimension. -/
def matrixQuarticForm
    (M : BipartiteMatrix ι) (x y : ι → ℂ) : ℝ :=
  (∑ a, ∑ b, ∑ c, ∑ e, quarticSummand M x y a b c e) /
    cardR (ι := ι) ^ 2

/-- Coordinate contribution to the squared normalization penalty. -/
def coordinateNormPenalty (x : ι → ℂ) (a : ι) : ℝ :=
  Complex.normSq (x a) - 1

/-- The concrete penalized matrix objective. -/
def matrixPenalizedObjective
    (M : BipartiteMatrix ι) (penalty : ℝ)
    (x y : ι → ℂ) : ℝ :=
  matrixQuarticForm M x y -
    penalty * denseAverage1 (coordinateNormPenalty x) ^ 2 -
    penalty * denseAverage1 (coordinateNormPenalty y) ^ 2

/-- The quartic contribution placed in each dense four-CSP predicate. -/
def scaledQuarticSummand
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (a b c e : ι) : ℝ :=
  cardR (ι := ι) ^ 2 * quarticSummand M x y a b c e

/-- The exact concrete CSP predicate used by the reduction. -/
def matrixCSPPredicate
    (M : BipartiteMatrix ι) (penalty scale : ℝ)
    (x y : ι → ℂ) (a b c e : ι) : ℝ :=
  densePredicate (scaledQuarticSummand M x y) penalty scale
    (coordinateNormPenalty x) (coordinateNormPenalty y) a b c e

/-- The scale used to place every concrete predicate in `[0,1]`. -/
def matrixPredicateScale (gamma kappa penalty : ℝ) : ℝ :=
  gamma * kappa ^ 4 + 2 * penalty * (kappa ^ 2 + 1) ^ 2 + 1

/-- A bounded coordinate has a bounded normalization-penalty contribution. -/
theorem abs_coordinateNormPenalty_le
    (z : ℂ) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hz : ‖z‖ ≤ kappa) :
    |Complex.normSq z - 1| ≤ kappa ^ 2 + 1 := by
  have hsq : ‖z‖ ^ 2 ≤ kappa ^ 2 :=
    (sq_le_sq₀ (norm_nonneg z) hkappa).2 hz
  rw [abs_le]
  constructor
  · nlinarith [Complex.normSq_nonneg z]
  · rw [Complex.normSq_eq_norm_sq]
    nlinarith

/-- Entry flatness and coordinate amplitude imply the claimed bound on one
scaled quartic predicate term. -/
theorem abs_scaledQuarticSummand_le
    [Nonempty ι]
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (gamma kappa : ℝ) (a b c e : ι)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hentry :
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hxa : ‖x a‖ ≤ kappa) (hxb : ‖x b‖ ≤ kappa)
    (hyc : ‖y c‖ ≤ kappa) (hye : ‖y e‖ ≤ kappa) :
    |scaledQuarticSummand M x y a b c e| ≤ gamma * kappa ^ 4 := by
  have hcard : 0 < cardR (ι := ι) := by
    unfold cardR
    exact_mod_cast Fintype.card_pos
  let z :=
    M (a, c) (b, e) * star (x a) * x b * star (y c) * y e
  have hz :
      ‖z‖ =
        ‖M (a, c) (b, e)‖ * ‖x a‖ * ‖x b‖ * ‖y c‖ * ‖y e‖ := by
    simp [z]
  have hzBound :
      ‖z‖ ≤
        (gamma / cardR (ι := ι) ^ 2) *
          kappa * kappa * kappa * kappa := by
    rw [hz]
    gcongr
  unfold scaledQuarticSummand quarticSummand
  rw [abs_mul, abs_of_nonneg (sq_nonneg (cardR (ι := ι)))]
  calc
    cardR (ι := ι) ^ 2 * |z.re| ≤
        cardR (ι := ι) ^ 2 * ‖z‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm z)
        (sq_nonneg _)
    _ ≤ cardR (ι := ι) ^ 2 *
        ((gamma / cardR (ι := ι) ^ 2) *
          kappa * kappa * kappa * kappa) :=
      mul_le_mul_of_nonneg_left hzBound (sq_nonneg _)
    _ = gamma * kappa ^ 4 := by
      field_simp [ne_of_gt hcard]

/-- The concrete matrix predicate lies in `[0,1]` under exactly the manuscript's
entry-flatness and coordinate-amplitude hypotheses. -/
theorem matrixCSPPredicate_mem_unitInterval
    [Nonempty ι]
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (gamma kappa penalty : ℝ) (a b c e : ι)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hpenalty : 0 ≤ penalty)
    (hentry :
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hx : ∀ i, ‖x i‖ ≤ kappa)
    (hy : ∀ i, ‖y i‖ ≤ kappa) :
    matrixCSPPredicate M penalty
        (matrixPredicateScale gamma kappa penalty) x y a b c e ∈
      Set.Icc (0 : ℝ) 1 := by
  let K := kappa ^ 2 + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hq :
      |scaledQuarticSummand M x y a b c e| ≤ gamma * kappa ^ 4 :=
    abs_scaledQuarticSummand_le M x y gamma kappa a b c e
      hgamma hkappa hentry (hx a) (hx b) (hy c) (hy e)
  have hxa :
      |coordinateNormPenalty x a| ≤ K := by
    simpa [coordinateNormPenalty, K] using
      abs_coordinateNormPenalty_le (x a) kappa hkappa (hx a)
  have hxb :
      |coordinateNormPenalty x b| ≤ K := by
    simpa [coordinateNormPenalty, K] using
      abs_coordinateNormPenalty_le (x b) kappa hkappa (hx b)
  have hyc :
      |coordinateNormPenalty y c| ≤ K := by
    simpa [coordinateNormPenalty, K] using
      abs_coordinateNormPenalty_le (y c) kappa hkappa (hy c)
  have hye :
      |coordinateNormPenalty y e| ≤ K := by
    simpa [coordinateNormPenalty, K] using
      abs_coordinateNormPenalty_le (y e) kappa hkappa (hy e)
  have hxp :
      |penalty *
        (coordinateNormPenalty x a * coordinateNormPenalty x b)| ≤
          penalty * K ^ 2 := by
    rw [abs_mul, abs_of_nonneg hpenalty, abs_mul]
    apply mul_le_mul_of_nonneg_left _ hpenalty
    calc
      |coordinateNormPenalty x a| * |coordinateNormPenalty x b| ≤
          K * |coordinateNormPenalty x b| :=
        mul_le_mul_of_nonneg_right hxa (abs_nonneg _)
      _ ≤ K * K := mul_le_mul_of_nonneg_left hxb hK
      _ = K ^ 2 := by ring
  have hyp :
      |penalty *
        (coordinateNormPenalty y c * coordinateNormPenalty y e)| ≤
          penalty * K ^ 2 := by
    rw [abs_mul, abs_of_nonneg hpenalty, abs_mul]
    apply mul_le_mul_of_nonneg_left _ hpenalty
    calc
      |coordinateNormPenalty y c| * |coordinateNormPenalty y e| ≤
          K * |coordinateNormPenalty y e| :=
        mul_le_mul_of_nonneg_right hyc (abs_nonneg _)
      _ ≤ K * K := mul_le_mul_of_nonneg_left hye hK
      _ = K ^ 2 := by ring
  have hraw :
      |denseRawPredicate (scaledQuarticSummand M x y) penalty
          (coordinateNormPenalty x) (coordinateNormPenalty y) a b c e| ≤
        matrixPredicateScale gamma kappa penalty := by
    unfold denseRawPredicate matrixPredicateScale
    calc
      |scaledQuarticSummand M x y a b c e -
          penalty * (coordinateNormPenalty x a * coordinateNormPenalty x b) -
          penalty * (coordinateNormPenalty y c * coordinateNormPenalty y e)| ≤
        |scaledQuarticSummand M x y a b c e| +
          |penalty *
            (coordinateNormPenalty x a * coordinateNormPenalty x b)| +
          |penalty *
            (coordinateNormPenalty y c * coordinateNormPenalty y e)| := by
              linarith [abs_sub
                (scaledQuarticSummand M x y a b c e -
                  penalty *
                    (coordinateNormPenalty x a * coordinateNormPenalty x b))
                (penalty *
                  (coordinateNormPenalty y c * coordinateNormPenalty y e)),
                abs_sub (scaledQuarticSummand M x y a b c e)
                  (penalty *
                    (coordinateNormPenalty x a * coordinateNormPenalty x b))]
      _ ≤ gamma * kappa ^ 4 + penalty * K ^ 2 + penalty * K ^ 2 := by
        gcongr
      _ ≤ gamma * kappa ^ 4 +
          2 * penalty * (kappa ^ 2 + 1) ^ 2 + 1 := by
        dsimp [K]
        linarith
  have hscale :
      0 < matrixPredicateScale gamma kappa penalty := by
    unfold matrixPredicateScale
    positivity
  unfold matrixCSPPredicate densePredicate
  exact rescaledPredicate_mem_unitInterval _ _ hscale hraw

/-- The fourfold average of the scaled quartic summands is exactly the matrix
quartic form. -/
theorem denseAverage4_scaledQuartic_eq
    [Nonempty ι]
    (M : BipartiteMatrix ι) (x y : ι → ℂ) :
    denseAverage4 (scaledQuarticSummand M x y) =
      matrixQuarticForm M x y := by
  have hcard : cardR (ι := ι) ≠ 0 := by
    unfold cardR
    exact_mod_cast Fintype.card_ne_zero
  unfold denseAverage4 scaledQuarticSummand matrixQuarticForm
  simp_rw [← Finset.mul_sum]
  field_simp [hcard]

/-- The generic dense penalized objective specializes to the manuscript's
matrix penalized objective. -/
theorem densePenalizedObjective_matrix_eq
    [Nonempty ι]
    (M : BipartiteMatrix ι) (penalty : ℝ)
    (x y : ι → ℂ) :
    densePenalizedObjective (scaledQuarticSummand M x y) penalty
        (coordinateNormPenalty x) (coordinateNormPenalty y) =
      matrixPenalizedObjective M penalty x y := by
  unfold densePenalizedObjective matrixPenalizedObjective
  rw [denseAverage4_scaledQuartic_eq]

/-- Averaging the concrete matrix predicates gives precisely the affine
rescaling of the manuscript's penalized objective. -/
theorem matrixCSPValue_eq_rescaled_objective
    [Nonempty ι]
    (M : BipartiteMatrix ι) (penalty scale : ℝ)
    (x y : ι → ℂ) (hscale : scale ≠ 0) :
    denseAverage4 (matrixCSPPredicate M penalty scale x y) =
      rescaledPredicate scale (matrixPenalizedObjective M penalty x y) := by
  unfold matrixCSPPredicate
  rw [denseCSPValue_eq_rescaled_objective _ _ _ _ _ hscale,
    densePenalizedObjective_matrix_eq]

/-- A fourfold monomial changes by at most four one-coordinate errors. -/
lemma quartic_coordinate_difference_le
    (xa xb yc ye wa wb zc ze : ℂ) (kappa epsilon : ℝ)
    (hkappa : 0 ≤ kappa) (hepsilon : 0 ≤ epsilon)
    (_hxa : ‖xa‖ ≤ kappa) (hxb : ‖xb‖ ≤ kappa)
    (hyc : ‖yc‖ ≤ kappa) (hye : ‖ye‖ ≤ kappa)
    (hwa : ‖wa‖ ≤ kappa) (hwb : ‖wb‖ ≤ kappa)
    (hzc : ‖zc‖ ≤ kappa) (_hze : ‖ze‖ ≤ kappa)
    (hax : ‖xa - wa‖ ≤ epsilon)
    (hbx : ‖xb - wb‖ ≤ epsilon)
    (hcy : ‖yc - zc‖ ≤ epsilon)
    (hey : ‖ye - ze‖ ≤ epsilon) :
    ‖star xa * xb * star yc * ye -
        star wa * wb * star zc * ze‖ ≤
      4 * kappa ^ 3 * epsilon := by
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
  have hA : ‖A‖ ≤ epsilon * kappa ^ 3 := by
    dsimp [A]
    simp only [norm_mul]
    simp only [Complex.norm_conj]
    calc
      ‖xa - wa‖ * ‖xb‖ * ‖yc‖ * ‖ye‖ ≤
          epsilon * kappa * kappa * kappa := by gcongr
      _ = epsilon * kappa ^ 3 := by ring
  have hB : ‖B‖ ≤ epsilon * kappa ^ 3 := by
    dsimp [B]
    simp only [norm_mul]
    simp only [Complex.norm_conj]
    calc
      ‖wa‖ * ‖xb - wb‖ * ‖yc‖ * ‖ye‖ ≤
          kappa * epsilon * kappa * kappa := by gcongr
      _ = epsilon * kappa ^ 3 := by ring
  have hC : ‖C‖ ≤ epsilon * kappa ^ 3 := by
    dsimp [C]
    simp only [norm_mul]
    simp only [Complex.norm_conj]
    calc
      ‖wa‖ * ‖wb‖ * ‖yc - zc‖ * ‖ye‖ ≤
          kappa * kappa * epsilon * kappa := by gcongr
      _ = epsilon * kappa ^ 3 := by ring
  have hD : ‖D‖ ≤ epsilon * kappa ^ 3 := by
    dsimp [D]
    simp only [norm_mul]
    simp only [Complex.norm_conj]
    calc
      ‖wa‖ * ‖wb‖ * ‖zc‖ * ‖ye - ze‖ ≤
          kappa * kappa * kappa * epsilon := by gcongr
      _ = epsilon * kappa ^ 3 := by ring
  rw [hid]
  have hsum :
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
  calc
    ‖A + B + C + D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := hsum
    _ ≤ 4 * (epsilon * kappa ^ 3) := by linarith
    _ = 4 * kappa ^ 3 * epsilon := by ring

/-- Entry-flatness turns the coordinate estimate into an estimate for one
quartic summand. -/
lemma abs_quarticSummand_sub_le
    [Nonempty ι]
    (M : BipartiteMatrix ι) (x y w z : ι → ℂ)
    (gamma kappa epsilon : ℝ) (a b c e : ι)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hepsilon : 0 ≤ epsilon)
    (hentry :
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hx : ∀ i, ‖x i‖ ≤ kappa) (hy : ∀ i, ‖y i‖ ≤ kappa)
    (hw : ∀ i, ‖w i‖ ≤ kappa) (hz : ∀ i, ‖z i‖ ≤ kappa)
    (hxw : ∀ i, ‖x i - w i‖ ≤ epsilon)
    (hyz : ∀ i, ‖y i - z i‖ ≤ epsilon) :
    |quarticSummand M x y a b c e -
        quarticSummand M w z a b c e| ≤
      (gamma / cardR (ι := ι) ^ 2) *
        (4 * kappa ^ 3 * epsilon) := by
  let p := star (x a) * x b * star (y c) * y e
  let r := star (w a) * w b * star (z c) * z e
  have hdifference : ‖p - r‖ ≤ 4 * kappa ^ 3 * epsilon := by
    exact quartic_coordinate_difference_le
      (x a) (x b) (y c) (y e) (w a) (w b) (z c) (z e)
      kappa epsilon hkappa hepsilon
      (hx a) (hx b) (hy c) (hy e)
      (hw a) (hw b) (hz c) (hz e)
      (hxw a) (hxw b) (hyz c) (hyz e)
  have hcard : 0 < cardR (ι := ι) := by
    unfold cardR
    exact_mod_cast Fintype.card_pos
  have hcoefficient : 0 ≤ gamma / cardR (ι := ι) ^ 2 :=
    div_nonneg hgamma (sq_nonneg _)
  unfold quarticSummand
  have hid :
      (M (a, c) (b, e) * star (x a) * x b * star (y c) * y e).re -
          (M (a, c) (b, e) * star (w a) * w b * star (z c) * z e).re =
        (M (a, c) (b, e) * (p - r)).re := by
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
    _ ≤ (gamma / cardR (ι := ι) ^ 2) *
        (4 * kappa ^ 3 * epsilon) := by
      gcongr

/-- Full Lipschitz estimate for the flat quartic objective. -/
theorem abs_matrixQuarticForm_sub_le
    [Nonempty ι]
    (M : BipartiteMatrix ι) (x y w z : ι → ℂ)
    (gamma kappa epsilon : ℝ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hepsilon : 0 ≤ epsilon)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hx : ∀ i, ‖x i‖ ≤ kappa) (hy : ∀ i, ‖y i‖ ≤ kappa)
    (hw : ∀ i, ‖w i‖ ≤ kappa) (hz : ∀ i, ‖z i‖ ≤ kappa)
    (hxw : ∀ i, ‖x i - w i‖ ≤ epsilon)
    (hyz : ∀ i, ‖y i - z i‖ ≤ epsilon) :
    |matrixQuarticForm M x y - matrixQuarticForm M w z| ≤
      4 * gamma * kappa ^ 3 * epsilon := by
  let f : ι → ι → ι → ι → ℝ := fun a b c e =>
    quarticSummand M x y a b c e -
      quarticSummand M w z a b c e
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
  have hterm : ∀ a b c e,
      |f a b c e| ≤
        (gamma / cardR (ι := ι) ^ 2) *
          (4 * kappa ^ 3 * epsilon) := by
    intro a b c e
    exact abs_quarticSummand_sub_le M x y w z gamma kappa epsilon
      a b c e hgamma hkappa hepsilon (hentry a b c e)
      hx hy hw hz hxw hyz
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
    abs_of_nonneg (sq_nonneg _)
  rw [habsCard]
  calc
    |∑ a, ∑ b, ∑ c, ∑ e, f a b c e| /
          cardR (ι := ι) ^ 2 ≤
        (∑ a, ∑ b, ∑ c, ∑ e, |f a b c e|) /
          cardR (ι := ι) ^ 2 := by gcongr
    _ ≤
        (∑ _a : ι, ∑ _b : ι, ∑ _c : ι, ∑ _e : ι,
          (gamma / cardR (ι := ι) ^ 2) *
            (4 * kappa ^ 3 * epsilon)) /
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
    _ = 4 * gamma * kappa ^ 3 * epsilon := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      unfold cardR
      field_simp

/-- A uniform pointwise bound also bounds a one-coordinate dense average. -/
lemma abs_denseAverage1_le
    [Nonempty ι]
    (f : ι → ℝ) (bound : ℝ) (hbound : ∀ i, |f i| ≤ bound) :
    |denseAverage1 f| ≤ bound := by
  have hcard : 0 < cardR (ι := ι) := by
    unfold cardR
    exact_mod_cast Fintype.card_pos
  unfold denseAverage1
  rw [abs_div, abs_of_pos hcard]
  calc
    |∑ i, f i| / cardR (ι := ι) ≤
        (∑ i, |f i|) / cardR (ι := ι) := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _i : ι, bound) / cardR (ι := ι) := by
      gcongr with i
      exact hbound i
    _ = bound := by
      simp [cardR]

/-- Squared complex norms are Lipschitz on a bounded disk. -/
lemma abs_normSq_sub_normSq_le
    (x w : ℂ) (kappa epsilon : ℝ)
    (_hkappa : 0 ≤ kappa) (hepsilon : 0 ≤ epsilon)
    (hx : ‖x‖ ≤ kappa) (hw : ‖w‖ ≤ kappa)
    (hxw : ‖x - w‖ ≤ epsilon) :
    |Complex.normSq x - Complex.normSq w| ≤
      2 * kappa * epsilon := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hdiff : |‖x‖ - ‖w‖| ≤ epsilon :=
    le_trans (abs_norm_sub_norm_le x w) hxw
  have hsum : ‖x‖ + ‖w‖ ≤ 2 * kappa := by linarith
  rw [show ‖x‖ ^ 2 - ‖w‖ ^ 2 =
      (‖x‖ - ‖w‖) * (‖x‖ + ‖w‖) by ring, abs_mul]
  calc
    |‖x‖ - ‖w‖| * |‖x‖ + ‖w‖| ≤
        epsilon * (2 * kappa) := by
      rw [abs_of_nonneg (by positivity : 0 ≤ ‖x‖ + ‖w‖)]
      gcongr
    _ = 2 * kappa * epsilon := by ring

/-- Rounding every coordinate by at most `epsilon` changes the averaged
normalization error by at most `2 * kappa * epsilon`. -/
lemma abs_coordinatePenaltyAverage_sub_le
    [Nonempty ι]
    (x w : ι → ℂ) (kappa epsilon : ℝ)
    (hkappa : 0 ≤ kappa) (hepsilon : 0 ≤ epsilon)
    (hx : ∀ i, ‖x i‖ ≤ kappa)
    (hw : ∀ i, ‖w i‖ ≤ kappa)
    (hxw : ∀ i, ‖x i - w i‖ ≤ epsilon) :
    |denseAverage1 (coordinateNormPenalty x) -
        denseAverage1 (coordinateNormPenalty w)| ≤
      2 * kappa * epsilon := by
  let f : ι → ℝ := fun i =>
    coordinateNormPenalty x i - coordinateNormPenalty w i
  have hfi : ∀ i, |f i| ≤ 2 * kappa * epsilon := by
    intro i
    dsimp [f, coordinateNormPenalty]
    simpa using abs_normSq_sub_normSq_le (x i) (w i)
      kappa epsilon hkappa hepsilon (hx i) (hw i) (hxw i)
  have havg := abs_denseAverage1_le f (2 * kappa * epsilon) hfi
  have heq :
      denseAverage1 (coordinateNormPenalty x) -
          denseAverage1 (coordinateNormPenalty w) =
        denseAverage1 f := by
    unfold denseAverage1
    dsimp [f]
    simp_rw [Finset.sum_sub_distrib]
    ring
  rwa [heq]

/-- The averaged normalization error stays in `[-(κ²+1), κ²+1]`. -/
lemma abs_coordinatePenaltyAverage_le
    [Nonempty ι]
    (x : ι → ℂ) (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hx : ∀ i, ‖x i‖ ≤ kappa) :
    |denseAverage1 (coordinateNormPenalty x)| ≤ kappa ^ 2 + 1 := by
  apply abs_denseAverage1_le
  intro i
  exact abs_coordinateNormPenalty_le (x i) kappa hkappa (hx i)

/-- Lipschitz estimate for one squared normalization penalty. -/
lemma abs_coordinatePenaltySquare_sub_le
    [Nonempty ι]
    (x w : ι → ℂ) (kappa epsilon : ℝ)
    (hkappa : 0 ≤ kappa) (hepsilon : 0 ≤ epsilon)
    (hx : ∀ i, ‖x i‖ ≤ kappa)
    (hw : ∀ i, ‖w i‖ ≤ kappa)
    (hxw : ∀ i, ‖x i - w i‖ ≤ epsilon) :
    |denseAverage1 (coordinateNormPenalty x) ^ 2 -
        denseAverage1 (coordinateNormPenalty w) ^ 2| ≤
      4 * kappa * (kappa ^ 2 + 1) * epsilon := by
  let rx := denseAverage1 (coordinateNormPenalty x)
  let rw := denseAverage1 (coordinateNormPenalty w)
  have hdiff : |rx - rw| ≤ 2 * kappa * epsilon :=
    abs_coordinatePenaltyAverage_sub_le x w kappa epsilon
      hkappa hepsilon hx hw hxw
  have hrx : |rx| ≤ kappa ^ 2 + 1 :=
    abs_coordinatePenaltyAverage_le x kappa hkappa hx
  have hrw : |rw| ≤ kappa ^ 2 + 1 :=
    abs_coordinatePenaltyAverage_le w kappa hkappa hw
  have hsum : |rx + rw| ≤ 2 * (kappa ^ 2 + 1) := by
    calc
      |rx + rw| ≤ |rx| + |rw| := abs_add_le _ _
      _ ≤ 2 * (kappa ^ 2 + 1) := by linarith
  change |rx ^ 2 - rw ^ 2| ≤ _
  rw [show rx ^ 2 - rw ^ 2 = (rx - rw) * (rx + rw) by ring,
    abs_mul]
  calc
    |rx - rw| * |rx + rw| ≤
        (2 * kappa * epsilon) * (2 * (kappa ^ 2 + 1)) := by
      gcongr
    _ = 4 * kappa * (kappa ^ 2 + 1) * epsilon := by ring

/-- Complete Lipschitz estimate for the matrix objective with both
normalization penalties. -/
theorem abs_matrixPenalizedObjective_sub_le
    [Nonempty ι]
    (M : BipartiteMatrix ι) (penalty : ℝ)
    (x y w z : ι → ℂ) (gamma kappa epsilon : ℝ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hepsilon : 0 ≤ epsilon) (hpenalty : 0 ≤ penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hx : ∀ i, ‖x i‖ ≤ kappa) (hy : ∀ i, ‖y i‖ ≤ kappa)
    (hw : ∀ i, ‖w i‖ ≤ kappa) (hz : ∀ i, ‖z i‖ ≤ kappa)
    (hxw : ∀ i, ‖x i - w i‖ ≤ epsilon)
    (hyz : ∀ i, ‖y i - z i‖ ≤ epsilon) :
    |matrixPenalizedObjective M penalty x y -
        matrixPenalizedObjective M penalty w z| ≤
      4 * gamma * kappa ^ 3 * epsilon +
        8 * penalty * kappa * (kappa ^ 2 + 1) * epsilon := by
  have hq := abs_matrixQuarticForm_sub_le M x y w z
    gamma kappa epsilon hgamma hkappa hepsilon hentry
    hx hy hw hz hxw hyz
  have hpx := abs_coordinatePenaltySquare_sub_le x w kappa epsilon
    hkappa hepsilon hx hw hxw
  have hpy := abs_coordinatePenaltySquare_sub_le y z kappa epsilon
    hkappa hepsilon hy hz hyz
  unfold matrixPenalizedObjective
  have hid :
      matrixQuarticForm M x y -
            penalty * denseAverage1 (coordinateNormPenalty x) ^ 2 -
            penalty * denseAverage1 (coordinateNormPenalty y) ^ 2 -
          (matrixQuarticForm M w z -
            penalty * denseAverage1 (coordinateNormPenalty w) ^ 2 -
            penalty * denseAverage1 (coordinateNormPenalty z) ^ 2) =
        (matrixQuarticForm M x y - matrixQuarticForm M w z) -
          penalty *
            (denseAverage1 (coordinateNormPenalty x) ^ 2 -
              denseAverage1 (coordinateNormPenalty w) ^ 2) -
          penalty *
            (denseAverage1 (coordinateNormPenalty y) ^ 2 -
              denseAverage1 (coordinateNormPenalty z) ^ 2) := by
    ring
  rw [hid]
  calc
    |(matrixQuarticForm M x y - matrixQuarticForm M w z) -
          penalty *
            (denseAverage1 (coordinateNormPenalty x) ^ 2 -
              denseAverage1 (coordinateNormPenalty w) ^ 2) -
          penalty *
            (denseAverage1 (coordinateNormPenalty y) ^ 2 -
              denseAverage1 (coordinateNormPenalty z) ^ 2)| ≤
      |matrixQuarticForm M x y - matrixQuarticForm M w z| +
        penalty *
          |denseAverage1 (coordinateNormPenalty x) ^ 2 -
            denseAverage1 (coordinateNormPenalty w) ^ 2| +
        penalty *
          |denseAverage1 (coordinateNormPenalty y) ^ 2 -
            denseAverage1 (coordinateNormPenalty z) ^ 2| := by
      calc
        |(matrixQuarticForm M x y - matrixQuarticForm M w z) -
              penalty *
                (denseAverage1 (coordinateNormPenalty x) ^ 2 -
                  denseAverage1 (coordinateNormPenalty w) ^ 2) -
              penalty *
                (denseAverage1 (coordinateNormPenalty y) ^ 2 -
                  denseAverage1 (coordinateNormPenalty z) ^ 2)| ≤
            |(matrixQuarticForm M x y - matrixQuarticForm M w z) -
              penalty *
                (denseAverage1 (coordinateNormPenalty x) ^ 2 -
                  denseAverage1 (coordinateNormPenalty w) ^ 2)| +
            |penalty *
              (denseAverage1 (coordinateNormPenalty y) ^ 2 -
                denseAverage1 (coordinateNormPenalty z) ^ 2)| :=
          abs_sub _ _
        _ ≤
            (|matrixQuarticForm M x y - matrixQuarticForm M w z| +
              |penalty *
                (denseAverage1 (coordinateNormPenalty x) ^ 2 -
                  denseAverage1 (coordinateNormPenalty w) ^ 2)|) +
            |penalty *
              (denseAverage1 (coordinateNormPenalty y) ^ 2 -
                denseAverage1 (coordinateNormPenalty z) ^ 2)| := by
          gcongr
          exact abs_sub _ _
        _ = _ := by
          simp only [abs_mul, abs_of_nonneg hpenalty]
    _ ≤ 4 * gamma * kappa ^ 3 * epsilon +
        penalty * (4 * kappa * (kappa ^ 2 + 1) * epsilon) +
        penalty * (4 * kappa * (kappa ^ 2 + 1) * epsilon) := by
      gcongr
    _ = 4 * gamma * kappa ^ 3 * epsilon +
        8 * penalty * kappa * (kappa ^ 2 + 1) * epsilon := by ring

/-- With the manuscript's mesh choice, coordinatewise rounding costs at most
`η/4` in the concrete penalized matrix objective. -/
theorem abs_matrixPenalizedObjective_mesh_choice
    [Nonempty ι]
    (M : BipartiteMatrix ι) (penalty : ℝ)
    (x y w z : ι → ℂ) (gamma kappa η : ℝ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 < kappa)
    (hη : 0 ≤ η) (hpenalty : 0 < penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hx : ∀ i, ‖x i‖ ≤ kappa) (hy : ∀ i, ‖y i‖ ≤ kappa)
    (hw : ∀ i, ‖w i‖ ≤ kappa) (hz : ∀ i, ‖z i‖ ≤ kappa)
    (hxw : ∀ i,
      ‖x i - w i‖ ≤
        η /
          (16 * gamma * kappa ^ 3 +
            32 * penalty * kappa * (kappa ^ 2 + 1)))
    (hyz : ∀ i,
      ‖y i - z i‖ ≤
        η /
          (16 * gamma * kappa ^ 3 +
            32 * penalty * kappa * (kappa ^ 2 + 1))) :
    |matrixPenalizedObjective M penalty x y -
        matrixPenalizedObjective M penalty w z| ≤ η / 4 := by
  let epsilon :=
    η /
      (16 * gamma * kappa ^ 3 +
        32 * penalty * kappa * (kappa ^ 2 + 1))
  have hepsilon : 0 ≤ epsilon := by
    dsimp [epsilon]
    apply div_nonneg hη
    positivity
  have hlip := abs_matrixPenalizedObjective_sub_le
    M penalty x y w z gamma kappa epsilon
    hgamma hkappa.le hepsilon hpenalty.le hentry hx hy hw hz hxw hyz
  have hmesh :=
    discretization_mesh_choice gamma kappa penalty η
      hgamma hkappa hpenalty
  dsimp only at hmesh
  have hrearrange :
      4 * gamma * kappa ^ 3 * epsilon +
          8 * penalty * kappa * (kappa ^ 2 + 1) * epsilon =
        (4 * gamma * kappa ^ 3 +
          8 * penalty * kappa * (kappa ^ 2 + 1)) * epsilon := by
    ring
  rw [hrearrange, show epsilon =
      η /
        (16 * gamma * kappa ^ 3 +
          32 * penalty * kappa * (kappa ^ 2 + 1)) by rfl] at hlip
  linarith

end

end QuantumSep
