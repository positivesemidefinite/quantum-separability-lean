import QuantumSep.SeparableOracle
import QuantumSep.ProbabilityAmplification

/-!
# Frank--Wolfe weak membership for separable states

This file connects the normalized separable support oracle to the
matrix-independent Frank--Wolfe recurrence and proves both terminal cases.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

noncomputable section

/-- A canonical feasible starting point. -/
def initialSeparableState (d : ℕ) : MatrixHilbert d :=
  matrixHilbertOf d
    (productDensityMatrix d (fun _ => 1) (fun _ => 1))

theorem initialSeparableState_mem
    (d : ℕ) :
    initialSeparableState d ∈ separableStates d := by
  apply pureProductState_mem_separable
  refine ⟨(fun _ => 1), (fun _ => 1), ?_, ?_, rfl⟩ <;>
    simp [vectorNormSq]

/-- The concrete Frank--Wolfe recursion, with index `1` as the manuscript's
initial iterate.  Index `0` is assigned the same harmless initial value. -/
def separableFrankWolfeIterate
    {d : ℕ}
    (omega : ℕ → MatrixHilbert d) :
    ℕ → MatrixHilbert d
  | 0 => initialSeparableState d
  | n + 1 =>
      if _hn : n = 0 then initialSeparableState d
      else
        (1 - 2 / ((n : ℝ) + 2)) •
            separableFrankWolfeIterate omega n +
          (2 / ((n : ℝ) + 2)) • omega n

theorem separableFrankWolfeIterate_update
    {d : ℕ}
    (omega : ℕ → MatrixHilbert d)
    (t : ℕ) (ht : 1 ≤ t) :
    separableFrankWolfeIterate omega (t + 1) =
      (1 - 2 / ((t : ℝ) + 2)) •
          separableFrankWolfeIterate omega t +
        (2 / ((t : ℝ) + 2)) • omega t := by
  rw [separableFrankWolfeIterate]
  simp [Nat.ne_of_gt ht]

theorem separableFrankWolfeIterate_mem
    {d : ℕ}
    (omega : ℕ → MatrixHilbert d)
    (homega : ∀ t, 1 ≤ t → omega t ∈ separableStates d) :
    ∀ t, separableFrankWolfeIterate omega t ∈ separableStates d := by
  intro t
  induction t with
  | zero =>
      exact initialSeparableState_mem d
  | succ n ih =>
      by_cases hn : n = 0
      · simp [separableFrankWolfeIterate, hn,
          initialSeparableState_mem d]
      · have hn1 : 1 ≤ n := (Nat.one_le_iff_ne_zero).2 hn
        have hden : 0 < (n : ℝ) + 2 := by positivity
        have hstep0 : 0 ≤ 2 / ((n : ℝ) + 2) := by positivity
        have hstep1 : 2 / ((n : ℝ) + 2) ≤ 1 := by
          apply (div_le_one hden).2
          exact_mod_cast (show 2 ≤ n + 2 by omega)
        rw [separableFrankWolfeIterate]
        simp only [dif_neg hn]
        exact frankWolfe_update_mem
          (separableStates d) (convex_separableStates d)
          (separableFrankWolfeIterate omega n) (omega n)
          (2 / ((n : ℝ) + 2)) ih (homega n hn1)
          hstep0 hstep1

/-- Finite-horizon feasibility.  Only oracle outputs preceding the requested
iterate are relevant. -/
theorem separableFrankWolfeIterate_mem_at
    {d : ℕ}
    (omega : ℕ → MatrixHilbert d)
    (T : ℕ)
    (homega : ∀ t, 1 ≤ t → t < T →
      omega t ∈ separableStates d) :
    separableFrankWolfeIterate omega T ∈ separableStates d := by
  induction T with
  | zero =>
      exact initialSeparableState_mem d
  | succ n ih =>
      by_cases hn : n = 0
      · simp [separableFrankWolfeIterate, hn,
          initialSeparableState_mem d]
      · have hn1 : 1 ≤ n := (Nat.one_le_iff_ne_zero).2 hn
        have hden : 0 < (n : ℝ) + 2 := by positivity
        have hstep0 : 0 ≤ 2 / ((n : ℝ) + 2) := by positivity
        have hstep1 : 2 / ((n : ℝ) + 2) ≤ 1 := by
          apply (div_le_one hden).2
          exact_mod_cast (show 2 ≤ n + 2 by omega)
        rw [separableFrankWolfeIterate]
        simp only [dif_neg hn]
        exact frankWolfe_update_mem
          (separableStates d) (convex_separableStates d)
          (separableFrankWolfeIterate omega n) (omega n)
          (2 / ((n : ℝ) + 2))
          (ih (fun t ht htlt =>
            homega t ht (htlt.trans (Nat.lt_succ_self n))))
          (homega n hn1 (Nat.lt_succ_self n))
          hstep0 hstep1

/-- The unit Frobenius direction queried by the weak-membership reduction. -/
def separableOracleDirection
    {d : ℕ} (rho sigma : MatrixHilbert d) :
    MatrixHilbert d :=
  ‖rho - sigma‖⁻¹ • (rho - sigma)

theorem separableOracleDirection_norm
    {d : ℕ} {rho sigma : MatrixHilbert d}
    (hne : rho ≠ sigma) :
    ‖separableOracleDirection rho sigma‖ = 1 := by
  have hnorm : ‖rho - sigma‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact sub_ne_zero.mpr hne
  unfold separableOracleDirection
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ hnorm]

theorem separableOracleDirection_hermitian
    {d : ℕ} {rho sigma : MatrixHilbert d}
    (hrho : rho ∈ hermitianMatrices d)
    (hsigma : sigma ∈ hermitianMatrices d) :
    separableOracleDirection rho sigma ∈ hermitianMatrices d :=
  hermitianMatrices_real_smul d ‖rho - sigma‖⁻¹
    (hermitianMatrices_sub d hrho hsigma)

/-- An additive support guarantee in the normalized direction has exactly the
sign and `2*tau` slack required by the Frank--Wolfe descent theorem. -/
theorem normalizedSeparableOracle_implies_descentOracle
    {d : ℕ} (hd : 0 < d)
    (rho sigma omega psi : MatrixHilbert d)
    (tau : ℝ) (htau : 0 ≤ tau)
    (hrhoNorm : ‖rho‖ ≤ 1)
    (hsigma : sigma ∈ separableStates d)
    (hpsi : psi ∈ separableStates d)
    (hne : rho ≠ sigma)
    (hopt :
      ⟪separableOracleDirection rho sigma, psi⟫ ≤
        ⟪separableOracleDirection rho sigma, omega⟫ + tau) :
    ⟪sigma - rho, omega⟫ ≤
      ⟪sigma - rho, psi⟫ + 2 * tau := by
  have hsigmaNorm : ‖sigma‖ ≤ 1 :=
    separableStates_norm_le d hd hsigma
  have hr : 0 < ‖rho - sigma‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hrle : ‖rho - sigma‖ ≤ 2 := by
    calc
      ‖rho - sigma‖ ≤ ‖rho‖ + ‖sigma‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hrhoNorm hsigmaNorm
      _ = 2 := by norm_num
  unfold separableOracleDirection at hopt
  rw [real_inner_smul_left, real_inner_smul_left] at hopt
  have hscaled :=
    mul_le_mul_of_nonneg_left hopt hr.le
  have hinv : ‖rho - sigma‖ * ‖rho - sigma‖⁻¹ = 1 :=
    mul_inv_cancel₀ hr.ne'
  rw [mul_add] at hscaled
  simp only [← mul_assoc, hinv, one_mul] at hscaled
  have hslack : ‖rho - sigma‖ * tau ≤ 2 * tau :=
    mul_le_mul_of_nonneg_right hrle htau
  have hraw :
      ⟪rho - sigma, psi⟫ ≤
        ⟪rho - sigma, omega⟫ + 2 * tau := by
    linarith
  have hnegOmega :
      ⟪sigma - rho, omega⟫ = -⟪rho - sigma, omega⟫ := by
    rw [show sigma - rho = -(rho - sigma) by abel, inner_neg_left]
  have hnegPsi :
      ⟪sigma - rho, psi⟫ = -⟪rho - sigma, psi⟫ := by
    rw [show sigma - rho = -(rho - sigma) by abel, inner_neg_left]
  rw [hnegOmega, hnegPsi]
  linarith

/-- On an execution in which every support-oracle call succeeds, the
Frank--Wolfe terminal iterate is within the acceptance radius whenever the
input is itself separable. -/
theorem separableFrankWolfe_complete_on_success
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrho : rho ∈ separableStates d)
    (sigma omega : ℕ → MatrixHilbert d)
    (eta tau : ℝ) (T : ℕ)
    (heta : 0 < eta)
    (htau : tau = eta ^ 2 / 64)
    (hT : 256 / eta ^ 2 ≤ (T : ℝ))
    (hsigma : ∀ t, 1 ≤ t → sigma t ∈ separableStates d)
    (homega : ∀ t, 1 ≤ t → omega t ∈ separableStates d)
    (hne : ∀ t, 1 ≤ t → rho ≠ sigma t)
    (horacle : ∀ t, 1 ≤ t →
      ∀ psi ∈ separableStates d,
        ⟪separableOracleDirection rho (sigma t), psi⟫ ≤
          ⟪separableOracleDirection rho (sigma t), omega t⟫ + tau)
    (hupdate : ∀ t, 1 ≤ t →
      sigma (t + 1) =
        (1 - 2 / ((t : ℝ) + 2)) • sigma t +
          (2 / ((t : ℝ) + 2)) • omega t)
    (hTone : 1 ≤ T) :
    ‖rho - sigma T‖ ≤ eta / 2 := by
  have hrhoNorm : ‖rho‖ ≤ 1 :=
    separableStates_norm_le d hd hrho
  have hsigmaNorm : ∀ t, 1 ≤ t → ‖sigma t‖ ≤ 1 :=
    fun t ht => separableStates_norm_le d hd (hsigma t ht)
  have homegaNorm : ∀ t, 1 ≤ t → ‖omega t‖ ≤ 1 :=
    fun t ht => separableStates_norm_le d hd (homega t ht)
  have htau0 : 0 ≤ tau := by
    rw [htau]
    positivity
  have hFWOracle : ∀ t, 1 ≤ t →
      ⟪sigma t - rho, omega t⟫ ≤
        ⟪sigma t - rho, rho⟫ + 2 * tau := by
    intro t ht
    exact normalizedSeparableOracle_implies_descentOracle
      hd rho (sigma t) (omega t) rho tau htau0 hrhoNorm
      (hsigma t ht) hrho (hne t ht)
      (horacle t ht rho hrho)
  have hrate :=
    frankWolfePotential_rate
      rho rho sigma omega 0 tau
      (by simp) hrhoNorm (by norm_num) htau0
      hsigmaNorm homegaNorm hFWOracle hupdate T hTone
  exact frankWolfe_terminal_acceptance
    rho (sigma T) tau eta T heta htau hT hrate

/-- Concrete-recursion form of completeness: feasibility and the update
equation are now derived rather than supplied as premises. -/
theorem concreteSeparableFrankWolfe_complete_on_success
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrho : rho ∈ separableStates d)
    (omega : ℕ → MatrixHilbert d)
    (eta tau : ℝ) (T : ℕ)
    (heta : 0 < eta)
    (htau : tau = eta ^ 2 / 64)
    (hT : 256 / eta ^ 2 ≤ (T : ℝ))
    (homega : ∀ t, 1 ≤ t → omega t ∈ separableStates d)
    (hne : ∀ t, 1 ≤ t →
      rho ≠ separableFrankWolfeIterate omega t)
    (horacle : ∀ t, 1 ≤ t →
      ∀ psi ∈ separableStates d,
        ⟪separableOracleDirection rho
            (separableFrankWolfeIterate omega t), psi⟫ ≤
          ⟪separableOracleDirection rho
              (separableFrankWolfeIterate omega t), omega t⟫ + tau)
    (hTone : 1 ≤ T) :
    ‖rho - separableFrankWolfeIterate omega T‖ ≤ eta / 2 := by
  exact separableFrankWolfe_complete_on_success
    d hd rho hrho (separableFrankWolfeIterate omega) omega
    eta tau T heta htau hT
    (fun t _ => separableFrankWolfeIterate_mem omega homega t)
    homega hne horacle
    (separableFrankWolfeIterate_update omega) hTone

/-- Finite-horizon concrete completeness.  This is the exact form needed for
a run making only the calls `1, ..., T-1`. -/
theorem concreteSeparableFrankWolfe_complete_on_success_until
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrho : rho ∈ separableStates d)
    (omega : ℕ → MatrixHilbert d)
    (eta tau : ℝ) (T : ℕ)
    (heta : 0 < eta)
    (htau : tau = eta ^ 2 / 64)
    (hTbound : 256 / eta ^ 2 ≤ (T : ℝ))
    (homega : ∀ t, 1 ≤ t → t < T →
      omega t ∈ separableStates d)
    (hne : ∀ t, 1 ≤ t → t ≤ T →
      rho ≠ separableFrankWolfeIterate omega t)
    (horacle : ∀ t, 1 ≤ t → t < T →
      ∀ psi ∈ separableStates d,
        ⟪separableOracleDirection rho
            (separableFrankWolfeIterate omega t), psi⟫ ≤
          ⟪separableOracleDirection rho
              (separableFrankWolfeIterate omega t), omega t⟫ + tau)
    (hTone : 1 ≤ T) :
    ‖rho - separableFrankWolfeIterate omega T‖ ≤ eta / 2 := by
  have hrhoNorm : ‖rho‖ ≤ 1 :=
    separableStates_norm_le d hd hrho
  have hsigmaMem : ∀ t, 1 ≤ t → t ≤ T →
      separableFrankWolfeIterate omega t ∈ separableStates d := by
    intro t _ht htT
    exact separableFrankWolfeIterate_mem_at omega t
      (fun s hs hst =>
        homega s hs (hst.trans_le htT))
  have hsigmaNorm : ∀ t, 1 ≤ t → t ≤ T →
      ‖separableFrankWolfeIterate omega t‖ ≤ 1 :=
    fun t ht htT =>
      separableStates_norm_le d hd (hsigmaMem t ht htT)
  have homegaNorm : ∀ t, 1 ≤ t → t < T →
      ‖omega t‖ ≤ 1 :=
    fun t ht htT =>
      separableStates_norm_le d hd (homega t ht htT)
  have htau0 : 0 ≤ tau := by
    rw [htau]
    positivity
  have hFWOracle : ∀ t, 1 ≤ t → t < T →
      ⟪separableFrankWolfeIterate omega t - rho, omega t⟫ ≤
        ⟪separableFrankWolfeIterate omega t - rho, rho⟫ +
          2 * tau := by
    intro t ht htT
    exact normalizedSeparableOracle_implies_descentOracle
      hd rho (separableFrankWolfeIterate omega t) (omega t) rho
      tau htau0 hrhoNorm
      (hsigmaMem t ht (Nat.le_of_lt htT)) hrho
      (hne t ht (Nat.le_of_lt htT))
      (horacle t ht htT rho hrho)
  have hrate :=
    frankWolfePotential_rate_at
      rho rho (separableFrankWolfeIterate omega) omega
      0 tau T (by simp) hrhoNorm (by norm_num) htau0
      hsigmaNorm homegaNorm hFWOracle
      (fun t ht _ => separableFrankWolfeIterate_update omega t ht)
      hTone
  exact frankWolfe_terminal_acceptance
    rho (separableFrankWolfeIterate omega T) tau eta T
    heta htau hTbound hrate

/-- The actual acceptance predicate, including the manuscript's immediate
acceptance branch when an iterate equals the input. -/
def separableWeakMembershipAccept
    {d : ℕ}
    (rho : MatrixHilbert d)
    (omega : ℕ → MatrixHilbert d)
    (eta : ℝ) (T : ℕ) : Prop :=
  (∃ t, 1 ≤ t ∧ t ≤ T ∧
      rho = separableFrankWolfeIterate omega t) ∨
    ‖rho - separableFrankWolfeIterate omega T‖ ≤ eta / 2

/-- Correctness predicate for one support-oracle call.  It is vacuous when
the algorithm has already reached the input exactly. -/
def separableOracleCallSucceeds
    {d : ℕ}
    (rho : MatrixHilbert d)
    (omega : ℕ → MatrixHilbert d)
    (tau : ℝ) (t : ℕ) : Prop :=
  rho = separableFrankWolfeIterate omega t ∨
    ∀ psi ∈ separableStates d,
      ⟪separableOracleDirection rho
          (separableFrankWolfeIterate omega t), psi⟫ ≤
        ⟪separableOracleDirection rho
            (separableFrankWolfeIterate omega t), omega t⟫ + tau

/-- Deterministic completeness of the finite weak-membership execution when
each call made before the terminal index succeeds. -/
theorem separableWeakMembership_complete_on_success
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrho : rho ∈ separableStates d)
    (omega : ℕ → MatrixHilbert d)
    (eta tau : ℝ) (T : ℕ)
    (heta : 0 < eta)
    (htau : tau = eta ^ 2 / 64)
    (hTbound : 256 / eta ^ 2 ≤ (T : ℝ))
    (homega : ∀ t, 1 ≤ t → t < T →
      omega t ∈ separableStates d)
    (hcalls : ∀ t, 1 ≤ t → t < T →
      separableOracleCallSucceeds rho omega tau t)
    (hTone : 1 ≤ T) :
    separableWeakMembershipAccept rho omega eta T := by
  by_cases heq : ∃ t, 1 ≤ t ∧ t ≤ T ∧
      rho = separableFrankWolfeIterate omega t
  · exact Or.inl heq
  · right
    apply concreteSeparableFrankWolfe_complete_on_success_until
      d hd rho hrho omega eta tau T heta htau hTbound homega
    · intro t ht htT hsame
      exact heq ⟨t, ht, htT, hsame⟩
    · intro t ht htT
      rcases hcalls t ht htT with hsame | hsuccess
      · exact False.elim
          (heq ⟨t, ht, Nat.le_of_lt htT, hsame⟩)
      · exact hsuccess
    · exact hTone

/-- Pointwise soundness: a state farther than `eta` from every separable
state is rejected for every sequence of feasible oracle outputs. -/
theorem separableWeakMembership_sound
    (d : ℕ)
    (rho : MatrixHilbert d)
    (omega : ℕ → MatrixHilbert d)
    (eta : ℝ) (T : ℕ)
    (heta : 0 ≤ eta)
    (homega : ∀ t, 1 ≤ t → t < T →
      omega t ∈ separableStates d)
    (hfar : ∀ psi ∈ separableStates d,
      eta < ‖rho - psi‖) :
    ¬ separableWeakMembershipAccept rho omega eta T := by
  rintro (hearly | hterminal)
  · obtain ⟨t, ht, htT, heq⟩ := hearly
    have hmem :=
      separableFrankWolfeIterate_mem_at omega t
        (fun s hs hst => homega s hs (hst.trans_le htT))
    have hpositive := hfar
      (separableFrankWolfeIterate omega t) hmem
    rw [← heq, sub_self, norm_zero] at hpositive
    linarith
  · exact
      (frankWolfe_terminal_sound
        (separableStates d) rho
        (separableFrankWolfeIterate omega T) eta heta
        (separableFrankWolfeIterate_mem_at omega T homega)
        hfar) hterminal

/-- Probability composition for any finite randomized execution living on a
common probability space.  This theorem handles adaptive output sequences:
the only required probabilistic data are measurable per-call success events
and their failure bounds. -/
theorem separableWeakMembership_complete_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrho : rho ∈ separableStates d)
    (omega : Ω → ℕ → MatrixHilbert d)
    (eta tau p : ℝ) (T : ℕ)
    (heta : 0 < eta)
    (htau : tau = eta ^ 2 / 64)
    (hTbound : 256 / eta ^ 2 ≤ (T : ℝ))
    (homega : ∀ z t, 1 ≤ t → t < T →
      omega z t ∈ separableStates d)
    (success : Fin T → Set Ω)
    (hsuccess_spec : ∀ i z,
      z ∈ success i ↔
        separableOracleCallSucceeds rho (omega z) tau (i.val + 1))
    (hsuccess_measurable : ∀ i, MeasurableSet (success i))
    (hfailure : ∀ i, mu.real (success i)ᶜ ≤ p)
    (hbudget : (T : ℝ) * p ≤ 1 / 3)
    (hTone : 1 ≤ T) :
    mu.real
        {z | separableWeakMembershipAccept rho (omega z) eta T} ≥
      2 / 3 := by
  let allSuccess : Set Ω := {z | ∀ i, z ∈ success i}
  have hallProbability :=
    measureReal_allSuccess_ge
      mu success hsuccess_measurable p hfailure
  have hcard : Fintype.card (Fin T) = T := Fintype.card_fin T
  rw [hcard] at hallProbability
  have hallLower : mu.real allSuccess ≥ 2 / 3 := by
    change mu.real {z | ∀ i, z ∈ success i} ≥ 2 / 3
    linarith
  have hsubset :
      allSuccess ⊆
        {z | separableWeakMembershipAccept rho (omega z) eta T} := by
    intro z hz
    apply separableWeakMembership_complete_on_success
      d hd rho hrho (omega z) eta tau T heta htau hTbound
      (homega z)
    · intro t ht htT
      have hsub : t - 1 < t := Nat.sub_lt (by omega) (by omega)
      let i : Fin T := ⟨t - 1, hsub.trans htT⟩
      have hi := (hsuccess_spec i z).1 (hz i)
      simpa [i, Nat.sub_add_cancel ht] using hi
    · exact hTone
  exact hallLower.trans
    (measureReal_mono hsubset (measure_ne_top _ _))

/-- Every execution rejects an input whose distance from all separable states
is larger than the promised gap, because all iterates stay feasible. -/
theorem separableFrankWolfe_sound
    (d : ℕ)
    (rho sigma : MatrixHilbert d) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hsigma : sigma ∈ separableStates d)
    (hfar :
      ∀ psi ∈ separableStates d, eta < ‖rho - psi‖) :
    ¬ ‖rho - sigma‖ ≤ eta / 2 :=
  frankWolfe_terminal_sound
    (separableStates d) rho sigma eta heta hsigma hfar

end

end QuantumSep
