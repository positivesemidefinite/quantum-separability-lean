import QuantumSep.AdaptiveWeakMembership
import QuantumSep.RuntimeAnalysis

/-!
# Runtime of adaptive weak membership

This file composes the already verified per-call product-optimizer runtime
with the explicit number of adaptive calls and repetitions used by weak
membership.  Accuracy is fixed in the usual PTAS sense, so the resulting
family is polynomial in the matrix dimension.
-/

namespace QuantumSep

noncomputable section

/-- Real-RAM operations outside one product-optimizer invocation.  The
fourth power accounts conservatively for forming and updating dense
`d² × d²` matrices, normalization, comparisons, and the Frank--Wolfe step. -/
def weakMembershipLinearAlgebraOverhead (d : ℕ) : ℕ :=
  64 * (d + 1) ^ 4 + 32

/-- Exact cost accounting for a finite adaptive execution once the runtime
of every optimizer invocation is supplied. -/
def weakMembershipExecutionCost
    (T d : ℕ)
    (callRuntime : Fin T → Fin (T + 1) → ℕ) : ℕ :=
  (∑ i, ∑ j,
    (callRuntime i j +
      weakMembershipLinearAlgebraOverhead d)) +
  T * weakMembershipLinearAlgebraOverhead d

/-- Closed uniform bound obtained by replacing every invocation by the
verified optimizer-family bound. -/
def weakMembershipRuntimeBound
    (assumptions : AllowedAssumptions)
    (eta : ℝ) (heta : 0 < eta)
    (d : ℕ) : ℕ :=
  let tau : ℝ := eta ^ 2 / 64
  let htau : 0 < tau := by
    dsimp [tau]
    positivity
  let T := weakMembershipIterations eta
  let C :=
    finalProductRuntimeConstant
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau
  let degree :=
    selectedHighRuntimeDegree
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau
  T * (T + 1) *
      (C * (d + 1) ^ degree +
        weakMembershipLinearAlgebraOverhead d) +
    T * weakMembershipLinearAlgebraOverhead d

/-- Summing all adaptive calls and repetitions gives the closed runtime
bound above. -/
theorem weakMembershipExecutionCost_le_bound
    (assumptions : AllowedAssumptions)
    (eta : ℝ) (heta : 0 < eta)
    (d : ℕ)
    (callRuntime :
      Fin (weakMembershipIterations eta) →
        Fin (weakMembershipIterations eta + 1) → ℕ)
    (hcall : ∀ i j,
      callRuntime i j ≤
        finalProductRuntimeConstant
            assumptions.efficient_haar_sampling
            assumptions.dense_max_four_csp_ptas
            assumptions.gaussian_hypercontractivity
            (eta ^ 2 / 64) (by positivity) *
          (d + 1) ^
            selectedHighRuntimeDegree
              assumptions.efficient_haar_sampling
              assumptions.dense_max_four_csp_ptas
              assumptions.gaussian_hypercontractivity
              (eta ^ 2 / 64) (by positivity)) :
    weakMembershipExecutionCost
        (weakMembershipIterations eta) d callRuntime ≤
      weakMembershipRuntimeBound assumptions eta heta d := by
  let T := weakMembershipIterations eta
  let tau : ℝ := eta ^ 2 / 64
  let htau : 0 < tau := by
    dsimp [tau]
    positivity
  let C :=
    finalProductRuntimeConstant
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau
  let degree :=
    selectedHighRuntimeDegree
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau
  have hsum :
      (∑ i : Fin T, ∑ j : Fin (T + 1),
          (callRuntime i j +
            weakMembershipLinearAlgebraOverhead d)) ≤
        T * (T + 1) *
          (C * (d + 1) ^ degree +
            weakMembershipLinearAlgebraOverhead d) := by
    calc
      (∑ i : Fin T, ∑ j : Fin (T + 1),
          (callRuntime i j +
            weakMembershipLinearAlgebraOverhead d)) ≤
          ∑ _i : Fin T, ∑ _j : Fin (T + 1),
            (C * (d + 1) ^ degree +
              weakMembershipLinearAlgebraOverhead d) := by
              exact Finset.sum_le_sum fun i _ =>
                Finset.sum_le_sum fun j _ => by
                  gcongr
                  simpa [T, C, degree, tau, htau] using hcall i j
      _ =
          T * (T + 1) *
            (C * (d + 1) ^ degree +
              weakMembershipLinearAlgebraOverhead d) := by
        simp
        ring
  unfold weakMembershipExecutionCost
  unfold weakMembershipRuntimeBound
  dsimp only
  dsimp [T, tau, C, degree] at hsum ⊢
  omega

/-- Each concrete product-optimizer invocation has exactly the uniform bound
used in the weak-membership cost composition. -/
theorem weakMembership_optimizer_call_runtime
    (assumptions : AllowedAssumptions)
    (eta : ℝ) (heta : 0 < eta)
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (seed :
      (productOptimizationProcedure
        assumptions.efficient_haar_sampling
        assumptions.dense_max_four_csp_ptas
        assumptions.gaussian_hypercontractivity
        (eta ^ 2 / 64) (by positivity)
        d hd M hMnorm).Seed) :
    (productOptimizationProcedure
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      (eta ^ 2 / 64) (by positivity)
      d hd M hMnorm).runtime () seed ≤
      finalProductRuntimeConstant
          assumptions.efficient_haar_sampling
          assumptions.dense_max_four_csp_ptas
          assumptions.gaussian_hypercontractivity
          (eta ^ 2 / 64) (by positivity) *
        (d + 1) ^
          selectedHighRuntimeDegree
            assumptions.efficient_haar_sampling
            assumptions.dense_max_four_csp_ptas
            assumptions.gaussian_hypercontractivity
            (eta ^ 2 / 64) (by positivity) := by
  have hbound :=
    productOptimizationProcedure_runtime_bound
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      assumptions.real_ram_model
      (eta ^ 2 / 64) (by positivity)
  exact hbound d hd M hMnorm seed

/-- Precise fixed-accuracy polynomial-runtime assertion for the complete
weak-membership execution. -/
def WeakMembershipPolynomialRuntime
    (assumptions : AllowedAssumptions)
    (eta : ℝ) (heta : 0 < eta) : Prop :=
  ∃ C degree : ℕ, ∀ d,
    weakMembershipRuntimeBound assumptions eta heta d ≤
      C * (d + 1) ^ degree

theorem randomizedSeparableWeakMembership_polynomial_runtime
    (assumptions : AllowedAssumptions)
    (eta : ℝ) (heta : 0 < eta) :
    WeakMembershipPolynomialRuntime assumptions eta heta := by
  let tau : ℝ := eta ^ 2 / 64
  let htau : 0 < tau := by
    dsimp [tau]
    positivity
  let T := weakMembershipIterations eta
  let C :=
    finalProductRuntimeConstant
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau
  let baseDegree :=
    selectedHighRuntimeDegree
      assumptions.efficient_haar_sampling
      assumptions.dense_max_four_csp_ptas
      assumptions.gaussian_hypercontractivity
      tau htau
  let degree := max baseDegree 4
  let totalConstant :=
    T * (T + 1) * (C + 96) + T * 96
  refine ⟨totalConstant, degree, ?_⟩
  intro d
  have hone : 1 ≤ d + 1 := by omega
  have hbaseDegree : baseDegree ≤ degree := by
    dsimp [degree]
    exact le_max_left _ _
  have hfour : 4 ≤ degree := by
    dsimp [degree]
    exact le_max_right _ _
  have hbasePow :
      (d + 1) ^ baseDegree ≤ (d + 1) ^ degree :=
    pow_le_pow_right' hone hbaseDegree
  have hfourPow :
      (d + 1) ^ 4 ≤ (d + 1) ^ degree :=
    pow_le_pow_right' hone hfour
  have honePow : 1 ≤ (d + 1) ^ degree :=
    one_le_pow₀ hone
  have hoverhead :
      weakMembershipLinearAlgebraOverhead d ≤
        96 * (d + 1) ^ degree := by
    unfold weakMembershipLinearAlgebraOverhead
    omega
  have hbase :
      C * (d + 1) ^ baseDegree ≤
        C * (d + 1) ^ degree :=
    Nat.mul_le_mul_left C hbasePow
  have honeCoeff :
      C * (d + 1) ^ baseDegree +
          weakMembershipLinearAlgebraOverhead d ≤
        (C + 96) * (d + 1) ^ degree := by
    calc
      C * (d + 1) ^ baseDegree +
          weakMembershipLinearAlgebraOverhead d ≤
        C * (d + 1) ^ degree +
          96 * (d + 1) ^ degree :=
        Nat.add_le_add hbase hoverhead
      _ = (C + 96) * (d + 1) ^ degree := by ring
  have hscaledMain :=
    Nat.mul_le_mul_left (T * (T + 1)) honeCoeff
  have hscaledOverhead :=
    Nat.mul_le_mul_left T hoverhead
  unfold weakMembershipRuntimeBound
  dsimp only
  change
    T * (T + 1) *
          (C * (d + 1) ^ baseDegree +
            weakMembershipLinearAlgebraOverhead d) +
        T * weakMembershipLinearAlgebraOverhead d ≤
      totalConstant * (d + 1) ^ degree
  calc
    _ ≤
        T * (T + 1) *
            ((C + 96) * (d + 1) ^ degree) +
          T * (96 * (d + 1) ^ degree) :=
      Nat.add_le_add hscaledMain hscaledOverhead
    _ = totalConstant * (d + 1) ^ degree := by
      dsimp [totalConstant]
      ring

end

end QuantumSep
