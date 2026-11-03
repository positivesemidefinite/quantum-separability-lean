import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Gaussian radial moments

The squared norm of a standard complex Gaussian vector has a Gamma law.
This file develops the negative moments of that law directly from mathlib's
Gamma density.  No probabilistic moment formula is taken as an assumption.
-/

open MeasureTheory Set Real
open ProbabilityTheory
open scoped ENNReal

namespace QuantumSep

/-- Exact negative moment of a Gamma random variable with unit rate.

The restrictions `0 < s < a` are precisely the integrability range at zero.
-/
theorem gamma_negative_moment (a s : ℝ) (ha : 0 < a) (hs : 0 < s)
    (has : s < a) :
    (∫ x : ℝ, x ^ (-s) ∂ gammaMeasure a 1) =
      Real.Gamma (a - s) / Real.Gamma a := by
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp only [smul_eq_mul, gammaPDF]
    simp_rw [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha one_pos _)]
    let g : ℝ → ℝ := fun x =>
      (1 / Real.Gamma a) * (x ^ (a - s - 1) * Real.exp (-x))
    calc
      (∫ x : ℝ, gammaPDFReal a 1 x * x ^ (-s)) =
          ∫ x : ℝ, (Set.Ioi 0).indicator g x := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : 0 < x
        · rw [Set.indicator_of_mem (show x ∈ Set.Ioi 0 from hx)]
          unfold gammaPDFReal g
          rw [if_pos hx.le]
          rw [show (1 : ℝ) ^ a = 1 by simp, one_div, one_mul]
          rw [show
              (Real.Gamma a)⁻¹ * x ^ (a - 1) * Real.exp (-x) * x ^ (-s) =
                (Real.Gamma a)⁻¹ * (x ^ (a - 1) * x ^ (-s)) *
                  Real.exp (-x) by ring]
          rw [← Real.rpow_add hx]
          rw [show a - 1 + -s = a - s - 1 by ring]
          ring
        · rw [Set.indicator_of_notMem (by simpa using hx)]
          unfold gammaPDFReal
          by_cases hx0 : x = 0
          · subst x
            simp [Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
          · have hneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
            rw [if_neg (not_le.mpr hneg)]
            simp
      _ = ∫ x : ℝ in Set.Ioi 0, g x :=
        integral_indicator measurableSet_Ioi
      _ = Real.Gamma (a - s) / Real.Gamma a := by
        unfold g
        calc
          (∫ x : ℝ in Set.Ioi 0,
              (1 / Real.Gamma a) *
                (x ^ (a - s - 1) * Real.exp (-x))) =
              (1 / Real.Gamma a) *
                ∫ x : ℝ in Set.Ioi 0,
                  x ^ (a - s - 1) * Real.exp (-x) := by
            rw [MeasureTheory.integral_const_mul]
          _ = (1 / Real.Gamma a) *
                ∫ x : ℝ in Set.Ioi 0,
                  x ^ ((a - s) - 1) * Real.exp (-(1 * x)) := by
            apply congrArg
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            ring_nf
          _ = Real.Gamma (a - s) / Real.Gamma a := by
            rw [Real.integral_rpow_mul_exp_neg_mul_Ioi
              (by linarith) one_pos]
            simp
            ring
  · exact (measurable_gammaPDFReal a 1).ennreal_ofReal
  · filter_upwards with x
    simp [gammaPDF]

/-- The Gamma function at a positive natural is the preceding factorial. -/
lemma gamma_nat_pos (n : ℕ) (hn : 0 < n) :
    Real.Gamma (n : ℝ) = (Nat.factorial (n - 1) : ℝ) := by
  have h := Real.Gamma_nat_eq_factorial (n - 1)
  rw [Nat.cast_sub hn] at h
  norm_num at h
  convert h using 1

/-- Exact even negative moment for an integer-shape Gamma law. -/
theorem gamma_negative_even_moment (d q : ℕ) (hq : 0 < q)
    (hqd : 2 * q < d) :
    (∫ x : ℝ, x ^ (-(2 * q : ℕ) : ℝ) ∂ gammaMeasure d 1) =
      (Nat.factorial (d - 2 * q - 1) : ℝ) /
        Nat.factorial (d - 1) := by
  rw [gamma_negative_moment (d : ℝ) (2 * q : ℕ)]
  · rw [← Nat.cast_sub (Nat.le_of_lt hqd)]
    rw [gamma_nat_pos (d - 2 * q) (Nat.sub_pos_of_lt hqd)]
    rw [gamma_nat_pos d
      (lt_trans (Nat.mul_pos (by norm_num) hq) hqd)]
  · exact_mod_cast (lt_trans (Nat.mul_pos (by norm_num) hq) hqd)
  · positivity
  · exact_mod_cast hqd

/-- The factorial ratio in the negative moment is bounded by the inverse
power of the smallest factor in the denominator. -/
lemma factorial_ratio_le_inverse_power (d q : ℕ) (hqd : 2 * q < d) :
    (Nat.factorial (d - 2 * q - 1) : ℝ) /
        Nat.factorial (d - 1) ≤
      1 / ((d - 2 * q : ℕ) : ℝ) ^ (2 * q) := by
  have hprodNat :=
    Nat.factorial_mul_ascFactorial (d - 2 * q - 1) (2 * q)
  have hbase : d - 2 * q - 1 + 1 = d - 2 * q := by omega
  have hsum : d - 2 * q - 1 + 2 * q = d - 1 := by omega
  rw [hbase, hsum] at hprodNat
  have hprodReal :
      (Nat.factorial (d - 2 * q - 1) : ℝ) *
          (Nat.ascFactorial (d - 2 * q) (2 * q) : ℝ) =
        (Nat.factorial (d - 1) : ℝ) := by
    exact_mod_cast hprodNat
  have hfactorial :
      (Nat.factorial (d - 2 * q - 1) : ℝ) ≠ 0 := by
    positivity
  have hbasePos : 0 < (d - 2 * q : ℕ) := Nat.sub_pos_of_lt hqd
  have hpowerPos :
      0 < ((d - 2 * q : ℕ) : ℝ) ^ (2 * q) := by positivity
  have hasc :
      ((d - 2 * q : ℕ) : ℝ) ^ (2 * q) ≤
        (Nat.ascFactorial (d - 2 * q) (2 * q) : ℝ) := by
    exact_mod_cast
      Nat.pow_succ_le_ascFactorial (d - 2 * q) (2 * q)
  calc
    (Nat.factorial (d - 2 * q - 1) : ℝ) /
        Nat.factorial (d - 1) =
      (Nat.factorial (d - 2 * q - 1) : ℝ) /
        ((Nat.factorial (d - 2 * q - 1) : ℝ) *
          Nat.ascFactorial (d - 2 * q) (2 * q)) := by
            rw [hprodReal]
    _ = 1 / (Nat.ascFactorial (d - 2 * q) (2 * q) : ℝ) := by
      field_simp
    _ ≤ 1 / ((d - 2 * q : ℕ) : ℝ) ^ (2 * q) :=
      one_div_le_one_div_of_le hpowerPos hasc

/-- Under `4q ≤ d`, the smallest factor `d - 2q` is at least `d/2`. -/
lemma inverse_power_le_two_div (d q : ℕ) (hq : 0 < q)
    (hfour : 4 * q ≤ d) :
    1 / ((d - 2 * q : ℕ) : ℝ) ^ (2 * q) ≤
      (2 / (d : ℝ)) ^ (2 * q) := by
  have hdNat : 0 < d := lt_of_lt_of_le
    (Nat.mul_pos (by norm_num) hq) hfour
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hbase :
      (d : ℝ) / 2 ≤ (d - 2 * q : ℕ) := by
    have htwiceBaseNat : d ≤ 2 * (d - 2 * q) := by omega
    have htwiceBase :
        (d : ℝ) ≤ 2 * ((d - 2 * q : ℕ) : ℝ) := by
      exact_mod_cast htwiceBaseNat
    linarith
  have hhalf : 0 < (d : ℝ) / 2 := by positivity
  have hinv :
      1 / ((d - 2 * q : ℕ) : ℝ) ≤ 2 / (d : ℝ) := by
    calc
      1 / ((d - 2 * q : ℕ) : ℝ) ≤ 1 / ((d : ℝ) / 2) :=
        one_div_le_one_div_of_le hhalf hbase
      _ = 2 / (d : ℝ) := by field_simp
  rw [← one_div_pow]
  gcongr

/-- The inverse-radius moment estimate used in the one-party Haar bound.
For a standard complex Gaussian vector in dimension `d`, its squared norm has
law `gammaMeasure d 1`, so this is exactly the moment beneath
`‖‖G‖₂⁻²‖_{L_{2q}} ≤ 2/d`. -/
theorem gamma_negative_even_moment_le (d q : ℕ) (hq : 0 < q)
    (hfour : 4 * q ≤ d) :
    (∫ x : ℝ, x ^ (-(2 * q : ℕ) : ℝ) ∂ gammaMeasure d 1) ≤
      (2 / (d : ℝ)) ^ (2 * q) := by
  have hqd : 2 * q < d := by omega
  rw [gamma_negative_even_moment d q hq hqd]
  exact le_trans (factorial_ratio_le_inverse_power d q hqd)
    (inverse_power_le_two_div d q hq hfour)

/-- Taking the `2q`-th root gives the inverse-radius `L_{2q}` estimate in
the exact numerical form used by the manuscript. -/
theorem gamma_inverse_radius_Lp_le (d q : ℕ) (hq : 0 < q)
    (hfour : 4 * q ≤ d) :
    ((∫ x : ℝ, x ^ (-(2 * q : ℕ) : ℝ) ∂ gammaMeasure d 1) ^
        (((2 * q : ℕ) : ℝ)⁻¹)) ≤
      2 / (d : ℝ) := by
  have hmoment :
      0 ≤ ∫ x : ℝ, x ^ (-(2 * q : ℕ) : ℝ) ∂ gammaMeasure d 1 := by
    rw [gamma_negative_even_moment d q hq (by omega)]
    positivity
  have hright : 0 ≤ 2 / (d : ℝ) := by
    have hd : 0 < d := by omega
    positivity
  have hexponent : 0 < ((2 * q : ℕ) : ℝ) := by positivity
  rw [Real.rpow_inv_le_iff_of_pos hmoment hright hexponent]
  rw [Real.rpow_natCast]
  exact gamma_negative_even_moment_le d q hq hfour

end QuantumSep
