import QuantumSep.ScalarInequalities
import QuantumSep.CSPBridge

/-!
# Corrections required by formalization

The supplied manuscript contains two sign slips.  These lemmas record the
correct algebraic forms, so downstream files cannot silently use the erroneous
versions.
-/

namespace QuantumSep

/-- Correct form of the dense-CSP step in the final theorem: the optimum term
has a plus sign. -/
theorem corrected_csp_sign
    (α s opt value τ objective : ℝ)
    (hs : 0 ≤ s)
    (hvalue : value ≥ opt - τ / (8 * s))
    (hsne : s ≠ 0)
    (hobjective : objective = 2 * s * (value - 1 / 2)) :
    α + objective ≥ α + 2 * s * (opt - 1 / 2) - τ / 4 := by
  have hbridge := csp_value_to_objective_lower_bound
    s value opt (τ / (8 * s)) objective hs hvalue hobjective
  calc
    α + objective ≥ α + (2 * s * (opt - 1 / 2) - 2 * s * (τ / (8 * s))) := by
      linarith
    _ = α + 2 * s * (opt - 1 / 2) - τ / 4 := by
      field_simp [hsne]
      ring

/-- Correct sign of the approximate linear-minimization oracle after negating
an approximate maximization guarantee. -/
theorem corrected_frankWolfe_oracle_sign
    (maxValue observed ε : ℝ)
    (h : observed ≥ maxValue - ε) :
    -observed ≤ -maxValue + ε := by
  exact negate_approx_lower_bound observed maxValue ε h

end QuantumSep
