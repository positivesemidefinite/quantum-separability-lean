import Mathlib

/-!
# Algebraic bridge between the dense CSP value and the penalized objective

This file formalizes the sign-sensitive algebra used in Lemma `lambda` and in
the final optimization theorem.  The finite-sum encoding itself is separated
from this algebraic bridge because repeated CSP indices require a dedicated
assignment API.
-/

namespace QuantumSep

noncomputable section

/-- Abstract penalized objective. -/
def penalizedObjective (q penalty rx ry : ℝ) : ℝ :=
  q - penalty * (rx - 1) ^ 2 - penalty * (ry - 1) ^ 2

/-- Affine rescaling used to turn a bounded objective into a `[0,1]` predicate. -/
def rescaledPredicate (s value : ℝ) : ℝ :=
  1 / 2 + value / (2 * s)

/-- Inverting the affine rescaling. -/
theorem rescaledPredicate_inverse (s value : ℝ) (hs : s ≠ 0) :
    2 * s * (rescaledPredicate s value - 1 / 2) = value := by
  have hden : 2 * s ≠ 0 := mul_ne_zero (by norm_num) hs
  rw [show rescaledPredicate s value - 1 / 2 = value / (2 * s) by
    unfold rescaledPredicate
    ring]
  field_simp [hden]

/-- A lower bound on CSP value gives a lower bound with the same sign on the
penalized objective.  This is the sign used in the corrected final proof. -/
theorem csp_value_to_objective_lower_bound
    (s value opt ε objective : ℝ)
    (hs : 0 ≤ s)
    (hvalue : value ≥ opt - ε)
    (hobjective : objective = 2 * s * (value - 1 / 2)) :
    objective ≥ 2 * s * (opt - 1 / 2) - 2 * s * ε := by
  rw [hobjective]
  nlinarith

/-- If a raw expression is bounded by `s`, its affine rescaling lies in
`[0,1]`. -/
theorem rescaledPredicate_mem_unitInterval
    (s value : ℝ) (hs : 0 < s) (hvalue : |value| ≤ s) :
    rescaledPredicate s value ∈ Set.Icc (0 : ℝ) 1 := by
  rw [abs_le] at hvalue
  have hden : 0 < 2 * s := by positivity
  constructor
  · have hdiv : -(1 / 2 : ℝ) ≤ value / (2 * s) := by
      apply (le_div_iff₀ hden).2
      nlinarith [hvalue.1]
    simp only [rescaledPredicate]
    linarith
  · have hdiv : value / (2 * s) ≤ (1 / 2 : ℝ) := by
      apply (div_le_iff₀ hden).2
      nlinarith [hvalue.2]
    simp only [rescaledPredicate]
    linarith

end

end QuantumSep
