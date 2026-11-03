import QuantumSep.CompactOptimization

/-!
# Assembly lemmas and unconditional compact optimization

This file records the arithmetic assembly of a successful algorithmic
certificate.  Separately, compactness proves the manuscript's mathematical
product-state optimization statement with no certificate premise.  The
randomized polynomial-time theorem requires the algorithmic development and
is deliberately not conflated with compact existence.
-/

namespace QuantumSep

noncomputable section

/-- Numerical and witness data produced by one successful execution of the
manuscript's reduction.  Each field is one displayed inequality in the final
proof. -/
structure OptimizationCertificate
    {ι : Type*} [Fintype ι]
    (value : (ι → ℂ) → (ι → ℂ) → ℝ)
    (isUnit : (ι → ℂ) → Prop)
    (τ δ η localError : ℝ) where
  x : ι → ℂ
  y : ι → ℂ
  x_isUnit : isUnit x
  y_isUnit : isUnit y
  support : ℝ
  encoded : ℝ
  normalized : ℝ
  output : ℝ
  output_eq : output = value x y
  support_upper :
    ∀ u v, isUnit u → isUnit v → value u v ≤ support
  support_to_encoded :
    support ≤ encoded + δ + η + localError
  csp_and_discretization :
    encoded - τ / 4 - η ≤ normalized
  normalization_and_tail :
    normalized - δ - localError ≤ output

/-- The corrected final error chain.  It uses a plus sign for the encoded CSP
optimum, charges two truncation errors and two discretization errors, and
charges the two local terms through `2 * localError`. -/
theorem optimizationCertificate_output_lower_bound
    {ι : Type*} [Fintype ι]
    {value : (ι → ℂ) → (ι → ℂ) → ℝ}
    {isUnit : (ι → ℂ) → Prop}
    {τ δ η localError : ℝ}
    (cert : OptimizationCertificate value isUnit τ δ η localError)
    (hδ : δ = τ / 16)
    (hη : η = τ / 4)
    (hlocal : 2 * localError ≤ τ / 8) :
    cert.support ≤ cert.output + τ := by
  have hbudget :
      2 * δ + η + τ / 4 + 2 * localError + η ≤ τ :=
    final_error_budget τ δ η (2 * localError) hδ hη hlocal
  linarith [cert.support_to_encoded, cert.csp_and_discretization,
    cert.normalization_and_tail]

/-- A successful certificate yields the manuscript's product-state
approximation specification. -/
theorem optimizationCertificate_to_spec
    {ι : Type*} [Fintype ι]
    {value : (ι → ℂ) → (ι → ℂ) → ℝ}
    {isUnit : (ι → ℂ) → Prop}
    {τ δ η localError : ℝ}
    (cert : OptimizationCertificate value isUnit τ δ η localError)
    (hδ : δ = τ / 16)
    (hη : η = τ / 4)
    (hlocal : 2 * localError ≤ τ / 8) :
    ProductApproximationSpec value isUnit τ := by
  refine ⟨cert.x, cert.y, cert.x_isUnit, cert.y_isUnit, ?_⟩
  intro u v hu hv
  have hsupport := cert.support_upper u v hu hv
  have hlower :=
    optimizationCertificate_output_lower_bound cert hδ hη hlocal
  rw [cert.output_eq] at hlower
  linarith

/-- The mathematical product-state approximation conclusion, proved directly
from compactness.  Unlike the former conditional theorem, this has no
certificate-construction premise.  It is an existence theorem, not yet the
manuscript's randomized polynomial-time algorithm. -/
theorem main_matrix_optimization_exists
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) (τ : ℝ) (hτ : 0 ≤ τ) :
    ProductApproximationSpec
      (matrixQuarticForm M)
      (fun x => x ∈ scaledUnitVectors ι)
      τ :=
  productApproximationSpec_matrixQuarticForm M τ hτ

end

end QuantumSep
