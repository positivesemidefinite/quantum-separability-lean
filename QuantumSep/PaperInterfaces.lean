import QuantumSep.MatrixPrelim
import QuantumSep.ManuscriptCorrections
import QuantumSep.GaussianWick
import QuantumSep.AlgorithmicInterfaces

/-!
# Interfaces for the deep analytic and algorithmic inputs

These structures make the dependency boundary explicit.  They are the four
external contracts authorized by the manuscript; every other ingredient is
proved internally from Mathlib definitions.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory

/-- Squared Hilbert norm of a finite family of traceless complex Gaussian
quadratic forms.  A finite-dimensional Hilbert-valued quadratic polynomial is
represented by its coordinates in an orthonormal basis. -/
noncomputable def gaussianQuadraticFamilyNormSq
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (ω : Fin d → ℝ × ℝ) : ℝ :=
  ∑ k : κ,
    Complex.normSq
      (gaussianQuadraticForm (tracelessPart (A k)) ω)

/-- Each coordinate of the traceless Gaussian quadratic family has an
integrable squared norm.  This is derived from the exact Wick identity: if the
integral were undefined, it would be zero, forcing the matrix itself to
vanish. -/
theorem integrable_normSq_gaussianQuadraticForm_traceless
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : CMatrix ι) :
    Integrable
      (fun ω =>
        Complex.normSq
          (gaussianQuadraticForm (tracelessPart A) ω))
      (complexGaussianVectorMeasure ι) := by
  let B := tracelessPart A
  have htrace : B.trace = 0 := trace_tracelessPart A
  have hint :
      (∫ ω,
        Complex.normSq (gaussianQuadraticForm B ω)
        ∂complexGaussianVectorMeasure ι) =
      frobeniusSq B := by
    simpa [htrace] using
      integral_normSq_gaussianQuadraticForm_sub_trace B
  by_cases hB : B = 0
  · simp [B, hB, gaussianQuadraticForm]
  · by_contra hnot
    rw [integral_undef hnot] at hint
    exact hB ((frobeniusSq_eq_zero_iff B).mp hint.symm)

/-- The exact `L₂` norm of the finite family used by the hypercontractivity
interface.  No hypercontractivity assumption is involved in this calculation;
it is the finite sum of the proved Wick identities. -/
theorem integral_gaussianQuadraticFamilyNormSq
    {κ : Type*} [Fintype κ]
    (d : ℕ) [Nonempty (Fin d)] (A : κ → CMatrix (Fin d)) :
    (∫ ω : Fin d → ℝ × ℝ,
      gaussianQuadraticFamilyNormSq d A ω
      ∂complexGaussianVectorMeasure (Fin d)) =
    ∑ k : κ, frobeniusSq (tracelessPart (A k)) := by
  unfold gaussianQuadraticFamilyNormSq
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro k _
    simpa using
      integral_normSq_gaussianQuadraticForm_sub_trace
        (tracelessPart (A k))
  · intro k _
    exact integrable_normSq_gaussianQuadraticForm_traceless (A k)

/-- Removing scalar trace components coordinatewise cannot increase the
Frobenius square appearing in the exact family `L₂` norm. -/
theorem gaussianQuadraticFamily_frobeniusSq_le
    {κ : Type*} [Fintype κ]
    (d : ℕ) [Nonempty (Fin d)] (A : κ → CMatrix (Fin d)) :
    (∑ k : κ, frobeniusSq (tracelessPart (A k))) ≤
      ∑ k : κ, frobeniusSq (A k) := by
  exact Finset.sum_le_sum fun k _ =>
    tracelessPart_frobeniusSq_le (A k)

/-- Precise authorized Gaussian-hypercontractivity contract.

This is only the degree-two Hilbert-valued `L₂ → L_{2q}` estimate used in the
manuscript.  It contains no Wick identity, inverse-radius estimate, Haar fact,
tail estimate, or algorithmic statement; all of those remain internal proof
obligations. -/
structure GaussianHypercontractivityContract where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  degreeTwo_moment_integrable :
    ∀ (d : ℕ) (κ : Type) [Fintype κ]
      (A : κ → CMatrix (Fin d)) (q : ℕ), 1 ≤ q →
      Integrable
        (fun ω : Fin d → ℝ × ℝ =>
          gaussianQuadraticFamilyNormSq d A ω ^ q)
        (complexGaussianVectorMeasure (Fin d))
  degreeTwo_L2_to_L2q :
    ∀ (d : ℕ) (κ : Type) [Fintype κ]
      (A : κ → CMatrix (Fin d)) (q : ℕ), 1 ≤ q →
      ((∫ ω : Fin d → ℝ × ℝ,
          gaussianQuadraticFamilyNormSq d A ω ^ q
          ∂complexGaussianVectorMeasure (Fin d)) ^
        (((2 * q : ℕ) : ℝ)⁻¹)) ≤
      constant * q *
        ((∫ ω : Fin d → ℝ × ℝ,
            gaussianQuadraticFamilyNormSq d A ω
            ∂complexGaussianVectorMeasure (Fin d)) ^
          ((2 : ℝ)⁻¹))

/-- The permitted hypercontractivity input, combined with the internally
proved Wick calculation, yields the manuscript-ready Frobenius bound. -/
theorem GaussianHypercontractivityContract.degreeTwo_L2_to_frobenius
    (hc : GaussianHypercontractivityContract)
    {κ : Type} [Fintype κ]
    (d : ℕ) [Nonempty (Fin d)]
    (A : κ → CMatrix (Fin d)) (q : ℕ) (hq : 1 ≤ q) :
    ((∫ ω : Fin d → ℝ × ℝ,
        gaussianQuadraticFamilyNormSq d A ω ^ q
        ∂complexGaussianVectorMeasure (Fin d)) ^
      (((2 * q : ℕ) : ℝ)⁻¹)) ≤
    hc.constant * q *
      ((∑ k : κ, frobeniusSq (A k)) ^ ((2 : ℝ)⁻¹)) := by
  calc
    _ ≤ hc.constant * q *
        ((∫ ω : Fin d → ℝ × ℝ,
            gaussianQuadraticFamilyNormSq d A ω
            ∂complexGaussianVectorMeasure (Fin d)) ^
          ((2 : ℝ)⁻¹)) :=
      hc.degreeTwo_L2_to_L2q d κ A q hq
    _ = hc.constant * q *
        ((∑ k : κ, frobeniusSq (tracelessPart (A k))) ^
          ((2 : ℝ)⁻¹)) := by
      rw [integral_gaussianQuadraticFamilyNormSq]
    _ ≤ hc.constant * q *
        ((∑ k : κ, frobeniusSq (A k)) ^
          ((2 : ℝ)⁻¹)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow
          (Finset.sum_nonneg fun k _ =>
            frobeniusSq_nonneg (tracelessPart (A k)))
          (gaussianQuadraticFamily_frobeniusSq_le d A)
          (by norm_num)
      · exact mul_nonneg hc.constant_nonneg (Nat.cast_nonneg q)

/-- Proof-carrying version of the manuscript's Hermitian decomposition
package for a concrete bipartite matrix. -/
structure HermitianDecompositionPackage
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) : Prop where
  decomposition_unique :
    ∀ (alpha : ℂ) (A B : CMatrix ι) (C : BipartiteMatrix ι),
      M = alpha • tensor (1 : CMatrix ι) (1 : CMatrix ι) +
          tensor A (1 : CMatrix ι) +
          tensor (1 : CMatrix ι) B + C →
      A.trace = 0 →
      B.trace = 0 →
      partialTrace0 C = 0 →
      partialTrace1 C = 0 →
      alpha = scalarPart M ∧
        A = localA M ∧ B = localB M ∧ C = correlationPart M
  localA_trace_zero : (localA M).trace = 0
  localB_trace_zero : (localB M).trace = 0
  correlation_partialTrace0_zero : partialTrace0 (correlationPart M) = 0
  correlation_partialTrace1_zero : partialTrace1 (correlationPart M) = 0
  four_summands_pairwise_orthogonal :
    hsInner
      (scalarPart M • tensor (1 : CMatrix ι) (1 : CMatrix ι))
      (tensor (localA M) (1 : CMatrix ι)) = 0 ∧
    hsInner
      (scalarPart M • tensor (1 : CMatrix ι) (1 : CMatrix ι))
      (tensor (1 : CMatrix ι) (localB M)) = 0 ∧
    hsInner
      (tensor (localA M) (1 : CMatrix ι))
      (tensor (1 : CMatrix ι) (localB M)) = 0 ∧
    hsInner
      (scalarPart M • tensor (1 : CMatrix ι) (1 : CMatrix ι))
      (correlationPart M) = 0 ∧
    hsInner
      (tensor (localA M) (1 : CMatrix ι))
      (correlationPart M) = 0 ∧
    hsInner
      (tensor (1 : CMatrix ι) (localB M))
      (correlationPart M) = 0
  frobenius_pythagoras :
    frobeniusSq M =
      frobeniusSq
        (scalarPart M • tensor (1 : CMatrix ι) (1 : CMatrix ι)) +
      frobeniusSq (tensor (localA M) (1 : CMatrix ι)) +
      frobeniusSq (tensor (1 : CMatrix ι) (localB M)) +
      frobeniusSq (correlationPart M)

/-- The matrix-decomposition package is constructed from proved theorems, with
no remaining assumption. -/
theorem hermitianDecompositionPackage
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) :
    HermitianDecompositionPackage M where
  decomposition_unique :=
    fun alpha A B C hM hA hB hC0 hC1 =>
      localDecomposition_unique M alpha A B C hM hA hB hC0 hC1
  localA_trace_zero := trace_localA M
  localB_trace_zero := trace_localB M
  correlation_partialTrace0_zero := partialTrace0_correlationPart M
  correlation_partialTrace1_zero := partialTrace1_correlationPart M
  four_summands_pairwise_orthogonal :=
    localDecomposition_pairwiseOrthogonal M
  frobenius_pythagoras := localDecomposition_frobenius_pythagoras M

/-- The four—and only four—external inputs authorized for the completed
formalization.  Every field has a precise contract; no moment, truncation,
discretization, probability-amplification, error-budget, or weak-membership
claim is hidden here. -/
structure AllowedAssumptions where
  efficient_haar_sampling : EfficientHaarSamplingContract
  dense_max_four_csp_ptas : DenseMaxFourCSPPTASContract
  gaussian_hypercontractivity : GaussianHypercontractivityContract
  real_ram_model : RealRAMModelContract

/-- Formal specification of the optimization conclusion, independent of a
particular randomized-program semantics. -/
def ProductApproximationSpec
    {ι : Type*} [Fintype ι]
    (value : (ι → ℂ) → (ι → ℂ) → ℝ)
    (isUnit : (ι → ℂ) → Prop)
    (τ : ℝ) : Prop :=
  ∃ x y, isUnit x ∧ isUnit y ∧
    ∀ u v, isUnit u → isUnit v → value u v ≤ value x y + τ

/-- `ProductApproximationSpec` is impossible if its purported unit-vector
predicate has no witnesses. -/
theorem not_productApproximationSpec_of_no_unit
    {ι : Type*} [Fintype ι]
    (value : (ι → ℂ) → (ι → ℂ) → ℝ)
    (isUnit : (ι → ℂ) → Prop)
    (τ : ℝ)
    (hnoUnit : ∀ x, ¬ isUnit x) :
    ¬ ProductApproximationSpec value isUnit τ := by
  rintro ⟨x, _y, hx, _hy, _happrox⟩
  exact hnoUnit x hx

end QuantumSep
