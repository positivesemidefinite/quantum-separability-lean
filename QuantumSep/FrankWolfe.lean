import QuantumSep.ScalarInequalities
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The Frank--Wolfe weak-membership recursion

This file proves the matrix-independent Hilbert-space argument used in the
last section of the manuscript.  No convergence theorem is imported: the
quadratic expansion, approximate linear-oracle step, induction, and terminal
distance test are all proved here.
-/

open scoped RealInnerProductSpace

namespace QuantumSep

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The shifted squared-distance potential relative to an attained minimum. -/
def frankWolfePotential (rho : E) (minimum : ℝ) (sigma : E) : ℝ :=
  (1 / 2 : ℝ) * ‖sigma - rho‖ ^ 2 - minimum

/-- The first-order convexity inequality for squared distance, proved by
expanding the square at an actual minimizer. -/
theorem inner_to_minimizer_le_neg_potential
    (rho sigma psi : E) (minimum : ℝ)
    (hminimum : minimum = (1 / 2 : ℝ) * ‖psi - rho‖ ^ 2) :
    ⟪sigma - rho, psi - sigma⟫ ≤
      -frankWolfePotential rho minimum sigma := by
  have hexpand := norm_add_sq_real (sigma - rho) (psi - sigma)
  have hadd : sigma - rho + (psi - sigma) = psi - rho := by
    abel
  rw [hadd] at hexpand
  unfold frankWolfePotential
  rw [hminimum]
  nlinarith [sq_nonneg ‖psi - sigma‖]

/-- An approximate linear minimization oracle implies the descent inner
product bound used in Frank--Wolfe. -/
theorem approximateOracle_descent
    (rho sigma omega psi : E) (minimum tau : ℝ)
    (hminimum : minimum = (1 / 2 : ℝ) * ‖psi - rho‖ ^ 2)
    (horacle :
      ⟪sigma - rho, omega⟫ ≤
        ⟪sigma - rho, psi⟫ + 2 * tau) :
    ⟪sigma - rho, omega - sigma⟫ ≤
      -frankWolfePotential rho minimum sigma + 2 * tau := by
  have hmin :=
    inner_to_minimizer_le_neg_potential rho sigma psi minimum hminimum
  have hrewriteOmega :
      ⟪sigma - rho, omega - sigma⟫ =
        ⟪sigma - rho, omega⟫ -
          ⟪sigma - rho, sigma⟫ := by
    rw [inner_sub_right]
  have hrewritePsi :
      ⟪sigma - rho, psi - sigma⟫ =
        ⟪sigma - rho, psi⟫ -
          ⟪sigma - rho, sigma⟫ := by
    rw [inner_sub_right]
  rw [hrewriteOmega]
  linarith [hmin, hrewritePsi]

/-- One exact matrix-independent Frank--Wolfe potential step. -/
theorem frankWolfePotential_step
    (rho sigma omega psi next : E) (minimum tau step : ℝ)
    (hminimum : minimum = (1 / 2 : ℝ) * ‖psi - rho‖ ^ 2)
    (hstep0 : 0 ≤ step) (hstep1 : step ≤ 1)
    (hsigma : ‖sigma‖ ≤ 1) (homega : ‖omega‖ ≤ 1)
    (horacle :
      ⟪sigma - rho, omega⟫ ≤
        ⟪sigma - rho, psi⟫ + 2 * tau)
    (hnext : next = (1 - step) • sigma + step • omega) :
    frankWolfePotential rho minimum next ≤
      (1 - step) * frankWolfePotential rho minimum sigma +
        2 * tau * step + 2 * step ^ 2 := by
  have hdescent :=
    approximateOracle_descent rho sigma omega psi minimum tau
      hminimum horacle
  have hdiameter : ‖omega - sigma‖ ≤ 2 := by
    calc
      ‖omega - sigma‖ ≤ ‖omega‖ + ‖sigma‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add homega hsigma
      _ = 2 := by norm_num
  have hdiameterSq : ‖omega - sigma‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (omega - sigma)]
  have hnextSub :
      next - rho = (sigma - rho) + step • (omega - sigma) := by
    rw [hnext]
    module
  have hexpand :=
    norm_add_sq_real (sigma - rho) (step • (omega - sigma))
  have hinner :
      ⟪sigma - rho, step • (omega - sigma)⟫ =
        step * ⟪sigma - rho, omega - sigma⟫ := by
    rw [real_inner_smul_right]
  have hnorm :
      ‖step • (omega - sigma)‖ ^ 2 =
        step ^ 2 * ‖omega - sigma‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hinner, hnorm] at hexpand
  unfold frankWolfePotential
  rw [hnextSub, hexpand]
  have hcurvature :
      step ^ 2 * ‖omega - sigma‖ ^ 2 ≤ step ^ 2 * 4 :=
    mul_le_mul_of_nonneg_left hdiameterSq (sq_nonneg step)
  have hscaledDescent :
      step * ⟪sigma - rho, omega - sigma⟫ ≤
        step * (-frankWolfePotential rho minimum sigma + 2 * tau) :=
    mul_le_mul_of_nonneg_left hdescent hstep0
  rw [frankWolfePotential] at hscaledDescent
  nlinarith

/-- The shifted recurrence in precisely the form consumed by the numerical
`8/(t+2)` induction. -/
theorem frankWolfePotential_shifted_step
    (rho sigma omega psi next : E) (minimum tau step : ℝ)
    (hminimum : minimum = (1 / 2 : ℝ) * ‖psi - rho‖ ^ 2)
    (hstep0 : 0 ≤ step) (hstep1 : step ≤ 1)
    (hsigma : ‖sigma‖ ≤ 1) (homega : ‖omega‖ ≤ 1)
    (horacle :
      ⟪sigma - rho, omega⟫ ≤
        ⟪sigma - rho, psi⟫ + 2 * tau)
    (hnext : next = (1 - step) • sigma + step • omega) :
    frankWolfePotential rho minimum next - 2 * tau ≤
      (1 - step) *
          (frankWolfePotential rho minimum sigma - 2 * tau) +
        2 * step ^ 2 := by
  exact shifted_inexact_recurrence
    (frankWolfePotential rho minimum next)
    (frankWolfePotential rho minimum sigma)
    tau step 2
    (frankWolfePotential_step rho sigma omega psi next minimum tau step
      hminimum hstep0 hstep1 hsigma homega horacle hnext)

/-- A point of norm at most one starts below the required base value whenever
the reference point also has norm at most one and the minimum is nonnegative. -/
theorem frankWolfePotential_base
    (rho sigma : E) (minimum tau : ℝ)
    (hrho : ‖rho‖ ≤ 1) (hsigma : ‖sigma‖ ≤ 1)
    (hminimum : 0 ≤ minimum) (htau : 0 ≤ tau) :
    frankWolfePotential rho minimum sigma - 2 * tau ≤ 8 / 3 := by
  have hdist : ‖sigma - rho‖ ≤ 2 := by
    calc
      ‖sigma - rho‖ ≤ ‖sigma‖ + ‖rho‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hsigma hrho
      _ = 2 := by norm_num
  have hdistSq : ‖sigma - rho‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (sigma - rho)]
  unfold frankWolfePotential
  nlinarith

/-- Full Hilbert-space Frank--Wolfe rate for a sequence of feasible iterates
and successful approximate linear-oracle calls. -/
theorem frankWolfePotential_rate
    (rho psi : E) (sigma omega : ℕ → E)
    (minimum tau : ℝ)
    (hminimum : minimum = (1 / 2 : ℝ) * ‖psi - rho‖ ^ 2)
    (hrho : ‖rho‖ ≤ 1)
    (hminimum0 : 0 ≤ minimum) (htau : 0 ≤ tau)
    (hsigma : ∀ t, 1 ≤ t → ‖sigma t‖ ≤ 1)
    (homega : ∀ t, 1 ≤ t → ‖omega t‖ ≤ 1)
    (horacle : ∀ t, 1 ≤ t →
      ⟪sigma t - rho, omega t⟫ ≤
        ⟪sigma t - rho, psi⟫ + 2 * tau)
    (hupdate : ∀ t, 1 ≤ t →
      sigma (t + 1) =
        (1 - 2 / ((t : ℝ) + 2)) • sigma t +
          (2 / ((t : ℝ) + 2)) • omega t) :
    ∀ t, 1 ≤ t →
      frankWolfePotential rho minimum (sigma t) ≤
        2 * tau + 8 / ((t : ℝ) + 2) := by
  let g : ℕ → ℝ :=
    fun t => frankWolfePotential rho minimum (sigma t) - 2 * tau
  have hbase : g 1 ≤ 8 / 3 :=
    frankWolfePotential_base rho (sigma 1) minimum tau
      hrho (hsigma 1 (by omega)) hminimum0 htau
  have hrec : ∀ t : ℕ, 1 ≤ t →
      g (t + 1) ≤
        (t : ℝ) / ((t : ℝ) + 2) * g t +
          8 / ((t : ℝ) + 2) ^ 2 := by
    intro t ht
    have hden : 0 < (t : ℝ) + 2 := by positivity
    have hstep0 : 0 ≤ 2 / ((t : ℝ) + 2) := by positivity
    have hstep1 : 2 / ((t : ℝ) + 2) ≤ 1 := by
      apply (div_le_one hden).mpr
      have ht0 : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
      linarith
    have hs :=
      frankWolfePotential_shifted_step
        rho (sigma t) (omega t) psi (sigma (t + 1))
        minimum tau (2 / ((t : ℝ) + 2))
        hminimum hstep0 hstep1 (hsigma t ht) (homega t ht)
        (horacle t ht) (hupdate t ht)
    dsimp [g]
    convert hs using 1 <;> field_simp <;> ring
  have hrate := recurrence_rate g hbase hrec
  intro t ht
  have := hrate t ht
  dsimp [g] at this
  linarith

/-- Finite-horizon Frank--Wolfe rate.  It requires feasibility through the
terminal iterate and successful oracle calls only at the preceding steps. -/
theorem frankWolfePotential_rate_at
    (rho psi : E) (sigma omega : ℕ → E)
    (minimum tau : ℝ) (T : ℕ)
    (hminimum : minimum = (1 / 2 : ℝ) * ‖psi - rho‖ ^ 2)
    (hrho : ‖rho‖ ≤ 1)
    (hminimum0 : 0 ≤ minimum) (htau : 0 ≤ tau)
    (hsigma : ∀ t, 1 ≤ t → t ≤ T → ‖sigma t‖ ≤ 1)
    (homega : ∀ t, 1 ≤ t → t < T → ‖omega t‖ ≤ 1)
    (horacle : ∀ t, 1 ≤ t → t < T →
      ⟪sigma t - rho, omega t⟫ ≤
        ⟪sigma t - rho, psi⟫ + 2 * tau)
    (hupdate : ∀ t, 1 ≤ t → t < T →
      sigma (t + 1) =
        (1 - 2 / ((t : ℝ) + 2)) • sigma t +
          (2 / ((t : ℝ) + 2)) • omega t)
    (hT : 1 ≤ T) :
    frankWolfePotential rho minimum (sigma T) ≤
      2 * tau + 8 / ((T : ℝ) + 2) := by
  let g : ℕ → ℝ :=
    fun t => frankWolfePotential rho minimum (sigma t) - 2 * tau
  have hbase : g 1 ≤ 8 / 3 :=
    frankWolfePotential_base rho (sigma 1) minimum tau
      hrho (hsigma 1 (by omega) hT) hminimum0 htau
  have hrec : ∀ t : ℕ, 1 ≤ t → t < T →
      g (t + 1) ≤
        (t : ℝ) / ((t : ℝ) + 2) * g t +
          8 / ((t : ℝ) + 2) ^ 2 := by
    intro t ht htT
    have hden : 0 < (t : ℝ) + 2 := by positivity
    have hstep0 : 0 ≤ 2 / ((t : ℝ) + 2) := by positivity
    have hstep1 : 2 / ((t : ℝ) + 2) ≤ 1 := by
      apply (div_le_one hden).mpr
      have ht0 : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
      linarith
    have hs :=
      frankWolfePotential_shifted_step
        rho (sigma t) (omega t) psi (sigma (t + 1))
        minimum tau (2 / ((t : ℝ) + 2))
        hminimum hstep0 hstep1
        (hsigma t ht (Nat.le_of_lt htT)) (homega t ht htT)
        (horacle t ht htT) (hupdate t ht htT)
    dsimp [g]
    convert hs using 1 <;> field_simp <;> ring
  have hrate := recurrence_rate_at g T hT hbase hrec
  dsimp [g] at hrate
  linarith

/-- A convex combination update preserves feasibility. -/
theorem frankWolfe_update_mem
    (K : Set E) (hK : Convex ℝ K)
    (sigma omega : E) (step : ℝ)
    (hsigma : sigma ∈ K) (homega : omega ∈ K)
    (hstep0 : 0 ≤ step) (hstep1 : step ≤ 1) :
    (1 - step) • sigma + step • omega ∈ K := by
  exact hK hsigma homega (by linarith) hstep0 (by ring)

/-- The terminal potential allocation gives the `η/2` acceptance radius. -/
theorem frankWolfe_terminal_acceptance
    (rho sigma : E) (tau eta iterations : ℝ)
    (heta : 0 < eta)
    (htau : tau = eta ^ 2 / 64)
    (hiterations : 256 / eta ^ 2 ≤ iterations)
    (hpotential :
      frankWolfePotential rho 0 sigma ≤
        2 * tau + 8 / (iterations + 2)) :
    ‖rho - sigma‖ ≤ eta / 2 := by
  have hbound :
      frankWolfePotential rho 0 sigma ≤ eta ^ 2 / 16 :=
    weakMembership_final_budget
      (frankWolfePotential rho 0 sigma) tau eta iterations
      heta htau hiterations hpotential
  apply potentialBound_to_halfGap
    ‖rho - sigma‖ (frankWolfePotential rho 0 sigma) eta
    (norm_nonneg _) heta.le
  · unfold frankWolfePotential
    rw [norm_sub_rev]
    ring
  · exact hbound

/-- Soundness of the terminal test needs only feasibility of the final
iterate. -/
theorem frankWolfe_terminal_sound
    (K : Set E) (rho sigma : E) (eta : ℝ)
    (heta : 0 ≤ eta) (hsigma : sigma ∈ K)
    (hfar : ∀ psi ∈ K, eta < ‖rho - psi‖) :
    ¬ ‖rho - sigma‖ ≤ eta / 2 :=
  farPoint_fails_halfGapTest ‖rho - sigma‖ eta heta
    (hfar sigma hsigma)

end

end QuantumSep
