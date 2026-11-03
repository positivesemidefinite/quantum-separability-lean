import QuantumSep.CSPBridge

/-!
# Concrete dense four-CSP averaging

This module formalizes the repeated-index finite-sum calculation in the
manuscript's Lemma `lambda`.  The quartic contribution is kept as an arbitrary
real four-index function; the two penalty contributions depend on the first
and second, respectively third and fourth, indices.
-/

open scoped BigOperators

namespace QuantumSep

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The real cardinality of the variable set. -/
def cardR : ℝ := Fintype.card ι

/-- Average of a real function over four ordered indices, with repetitions. -/
def denseAverage4 (f : ι → ι → ι → ι → ℝ) : ℝ :=
  (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) / cardR (ι := ι) ^ 4

/-- Average of a real function over one index. -/
def denseAverage1 (f : ι → ℝ) : ℝ :=
  (∑ a, f a) / cardR (ι := ι)

/-- The unscaled summand used by the manuscript's dense Max-4-CSP. -/
def denseRawPredicate
    (quartic : ι → ι → ι → ι → ℝ)
    (penalty : ℝ) (xPenalty yPenalty : ι → ℝ)
    (a b c e : ι) : ℝ :=
  quartic a b c e -
    penalty * (xPenalty a * xPenalty b) -
    penalty * (yPenalty c * yPenalty e)

/-- The `[0,1]`-rescaled predicate. -/
def densePredicate
    (quartic : ι → ι → ι → ι → ℝ)
    (penalty scale : ℝ) (xPenalty yPenalty : ι → ℝ)
    (a b c e : ι) : ℝ :=
  rescaledPredicate scale
    (denseRawPredicate quartic penalty xPenalty yPenalty a b c e)

/-- The concrete penalized objective represented by the CSP. -/
def densePenalizedObjective
    (quartic : ι → ι → ι → ι → ℝ)
    (penalty : ℝ) (xPenalty yPenalty : ι → ℝ) : ℝ :=
  denseAverage4 quartic -
    penalty * denseAverage1 xPenalty ^ 2 -
    penalty * denseAverage1 yPenalty ^ 2

private theorem sum_four_const (r : ℝ) :
    (∑ _a : ι, ∑ _b : ι, ∑ _c : ι, ∑ _e : ι, r) =
      cardR (ι := ι) ^ 4 * r := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold cardR
  ring

private theorem sum_four_first_pair (f : ι → ℝ) :
    (∑ a : ι, ∑ b : ι, ∑ _c : ι, ∑ _e : ι, f a * f b) =
      cardR (ι := ι) ^ 2 * (∑ a : ι, f a) ^ 2 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (∑ a : ι, ∑ b : ι,
      Fintype.card ι * (Fintype.card ι * (f a * f b))) =
      (Fintype.card ι : ℝ) ^ 2 *
        ((∑ a : ι, f a) * ∑ b : ι, f b) by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    ring]
  unfold cardR
  ring

private theorem sum_four_second_pair (f : ι → ℝ) :
    (∑ _a : ι, ∑ _b : ι, ∑ c : ι, ∑ e : ι, f c * f e) =
      cardR (ι := ι) ^ 2 * (∑ c : ι, f c) ^ 2 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Fintype.sum_mul_sum f f]
  unfold cardR
  ring

private theorem sum_four_mul_left
    (r : ℝ) (f : ι → ι → ι → ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ e, r * f a b c e) =
      r * ∑ a, ∑ b, ∑ c, ∑ e, f a b c e := by
  symm
  simp only [Finset.mul_sum]

private theorem sum_four_div
    (f : ι → ι → ι → ι → ℝ) (r : ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ e, f a b c e / r) =
      (∑ a, ∑ b, ∑ c, ∑ e, f a b c e) / r := by
  symm
  simp only [Finset.sum_div]

private theorem sum_four_raw
    (quartic : ι → ι → ι → ι → ℝ)
    (penalty : ℝ) (xPenalty yPenalty : ι → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ e,
      denseRawPredicate quartic penalty xPenalty yPenalty a b c e) =
      (∑ a, ∑ b, ∑ c, ∑ e, quartic a b c e) -
        penalty * (∑ a : ι, ∑ b : ι, ∑ _c : ι, ∑ _e : ι,
          xPenalty a * xPenalty b) -
        penalty * (∑ _a : ι, ∑ _b : ι, ∑ c : ι, ∑ e : ι,
          yPenalty c * yPenalty e) := by
  unfold denseRawPredicate
  simp_rw [Finset.sum_sub_distrib]
  rw [sum_four_mul_left (ι := ι) penalty
      (fun a b _c _e => xPenalty a * xPenalty b),
    sum_four_mul_left (ι := ι) penalty
      (fun _a _b c e => yPenalty c * yPenalty e)]

/-- Averaging the repeated-index penalty summand produces the square of the
one-index average, exactly as used in the manuscript. -/
theorem denseAverage4_raw_eq_penalized
    [Nonempty ι]
    (quartic : ι → ι → ι → ι → ℝ)
    (penalty : ℝ) (xPenalty yPenalty : ι → ℝ) :
    denseAverage4
        (denseRawPredicate quartic penalty xPenalty yPenalty) =
      densePenalizedObjective quartic penalty xPenalty yPenalty := by
  have hcard : cardR (ι := ι) ≠ 0 := by
    unfold cardR
    exact_mod_cast Fintype.card_ne_zero
  unfold denseAverage4 densePenalizedObjective denseAverage1
  rw [sum_four_raw (ι := ι)]
  rw [sum_four_first_pair (ι := ι), sum_four_second_pair (ι := ι)]
  unfold denseAverage4
  field_simp [hcard]

/-- The concrete dense-CSP value is the affine rescaling of the concrete
penalized objective.  Ordered tuples may contain repeated indices. -/
theorem denseCSPValue_eq_rescaled_objective
    [Nonempty ι]
    (quartic : ι → ι → ι → ι → ℝ)
    (penalty scale : ℝ) (xPenalty yPenalty : ι → ℝ)
    (hscale : scale ≠ 0) :
    denseAverage4
        (densePredicate quartic penalty scale xPenalty yPenalty) =
      rescaledPredicate scale
        (densePenalizedObjective quartic penalty xPenalty yPenalty) := by
  have hcard : cardR (ι := ι) ≠ 0 := by
    unfold cardR
    exact_mod_cast Fintype.card_ne_zero
  unfold densePredicate rescaledPredicate denseAverage4
  simp_rw [Finset.sum_add_distrib]
  rw [sum_four_div (ι := ι)
    (denseRawPredicate quartic penalty xPenalty yPenalty) (2 * scale)]
  rw [sum_four_const (ι := ι)]
  have hraw :=
    denseAverage4_raw_eq_penalized quartic penalty xPenalty yPenalty
  unfold denseAverage4 at hraw
  field_simp [hcard, hscale] at hraw ⊢
  linear_combination hraw

end

end QuantumSep
