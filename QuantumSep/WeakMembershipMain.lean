import QuantumSep.WeakMembershipRuntime

/-!
# End-to-end weak-membership corollary

This is the final packaged statement: a measurable randomized decision,
probability-one feasibility, completeness, soundness, and fixed-accuracy
polynomial runtime, assembled from exactly `AllowedAssumptions`.
-/

namespace QuantumSep

open MeasureTheory

noncomputable section

/-- Fully instantiated weak membership for separability.

For a Hermitian Frobenius-unit-ball input, the algorithm:
* defines an actual probability law and measurable Boolean decision;
* accepts every separable input with probability at least `2/3`;
* never accepts an input at distance strictly greater than `eta` from the
  separable set; and
* runs in polynomial time in `d` for fixed positive `eta`.
-/
theorem randomizedSeparableWeakMembership_main
    (assumptions : AllowedAssumptions)
    (eta : ℝ) (heta : 0 < eta)
    (d : ℕ) (hd : 0 < d)
    (rho : MatrixHilbert d)
    (hrhoHerm : rho ∈ hermitianMatrices d)
    (hrhoNorm : ‖rho‖ ≤ 1) :
    let law :=
      randomizedSeparableWeakMembershipLaw
        assumptions eta heta d hd rho hrhoHerm hrhoNorm
    let T := weakMembershipIterations eta
    IsProbabilityMeasure law ∧
      Measurable
        (certifiedWeakDecision
          (d := d) (rho := rho)
          (tau := eta ^ 2 / 64)
          (stateIndex := T + 1) eta T) ∧
      (rho ∈ separableStates d →
        law.real
          {state |
            certifiedWeakDecision eta T state = true} ≥
          2 / 3) ∧
      ((∀ psi ∈ separableStates d,
          eta < ‖rho - psi‖) →
        law.real
          {state |
            certifiedWeakDecision eta T state = true} = 0) ∧
      WeakMembershipPolynomialRuntime assumptions eta heta := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact randomizedSeparableWeakMembershipLaw_probability
      assumptions eta heta d hd rho hrhoHerm hrhoNorm
  · exact measurable_certifiedWeakDecision eta
      (weakMembershipIterations eta)
  · intro hrho
    exact randomizedSeparableWeakMembership_complete
      assumptions eta heta d hd rho hrhoHerm hrhoNorm hrho
  · intro hfar
    exact randomizedSeparableWeakMembership_sound
      assumptions eta heta d hd rho hrhoHerm hrhoNorm hfar
  · exact randomizedSeparableWeakMembership_polynomial_runtime
      assumptions eta heta

end

end QuantumSep
