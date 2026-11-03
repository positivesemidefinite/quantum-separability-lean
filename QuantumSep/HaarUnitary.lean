import QuantumSep.Normalization
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Haar probability measure on the finite-dimensional unitary group

Mathlib supplies the unitary group and the general Haar-measure construction.
This file proves the compactness instance needed to normalize Haar measure on
`U(d)`, then constructs its column laws and proves that every column is a unit
vector almost surely.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate Matrix.Norms.Elementwise

namespace QuantumSep

noncomputable section

/-- The finite-dimensional complex unitary group is compact.  It is closed,
and every matrix entry lies in the closed complex unit disk. -/
theorem isCompact_unitaryGroup_carrier (d : ℕ) :
    IsCompact
      (Matrix.unitaryGroup (Fin d) ℂ :
        Set (CMatrix (Fin d))) := by
  let K : Set (CMatrix (Fin d)) :=
    Set.pi Set.univ fun _ =>
      Set.pi Set.univ fun _ =>
        Metric.closedBall (0 : ℂ) 1
  have hK : IsCompact K := by
    exact isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ =>
        isCompact_closedBall (0 : ℂ) 1
  apply IsCompact.of_isClosed_subset hK isClosed_unitary
  intro U hU i _ j _
  simpa [Metric.mem_closedBall, dist_zero_right] using
    entry_norm_bound_of_unitary hU i j

noncomputable instance compactSpaceUnitaryGroup (d : ℕ) :
    CompactSpace (Matrix.unitaryGroup (Fin d) ℂ) :=
  isCompact_iff_compactSpace.mp
    (isCompact_unitaryGroup_carrier d)

/-- The Borel measurable structure on the unitary group. -/
noncomputable instance measurableSpaceUnitaryGroup (d : ℕ) :
    MeasurableSpace (Matrix.unitaryGroup (Fin d) ℂ) :=
  borel (Matrix.unitaryGroup (Fin d) ℂ)

instance borelSpaceUnitaryGroup (d : ℕ) :
    BorelSpace (Matrix.unitaryGroup (Fin d) ℂ) :=
  ⟨rfl⟩

/-- Haar measure on `U(d)`, normalized by assigning mass one to the whole
compact group. -/
noncomputable def unitaryHaarMeasure (d : ℕ) :
    Measure (Matrix.unitaryGroup (Fin d) ℂ) :=
  MeasureTheory.Measure.haarMeasure
    (⊤ : TopologicalSpace.PositiveCompacts
      (Matrix.unitaryGroup (Fin d) ℂ))

noncomputable instance isProbabilityMeasure_unitaryHaarMeasure
    (d : ℕ) :
    IsProbabilityMeasure (unitaryHaarMeasure d) := by
  constructor
  rw [← TopologicalSpace.PositiveCompacts.coe_top]
  exact MeasureTheory.Measure.haarMeasure_self

noncomputable instance isHaarMeasure_unitaryHaarMeasure
    (d : ℕ) :
    Measure.IsHaarMeasure (unitaryHaarMeasure d) := by
  unfold unitaryHaarMeasure
  infer_instance

/-- On the compact group `U(d)`, normalized left Haar measure is also
right-invariant.  This is derived by applying uniqueness of probability Haar
measure to a right translate. -/
noncomputable instance isMulRightInvariant_unitaryHaarMeasure
    (d : ℕ) :
    Measure.IsMulRightInvariant (unitaryHaarMeasure d) where
  map_mul_right_eq_self g := by
    let f :=
      (fun U : Matrix.unitaryGroup (Fin d) ℂ => U * g)
    have hf : Measurable f := by
      fun_prop
    let μ' := (unitaryHaarMeasure d).map f
    haveI : IsProbabilityMeasure μ' :=
      Measure.isProbabilityMeasure_map hf.aemeasurable
    haveI : Measure.IsHaarMeasure μ' := by
      dsimp [μ', f]
      infer_instance
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure
      μ' (unitaryHaarMeasure d)

/-- A permutation matrix, bundled as a unitary matrix. -/
def permutationUnitary (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    Matrix.unitaryGroup (Fin d) ℂ :=
  ⟨σ.permMatrix ℂ, by
    rw [Matrix.mem_unitaryGroup_iff,
      Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_permMatrix]
    rw [← Matrix.permMatrix_mul]
    simp⟩

/-- A specified column of a unitary matrix. -/
def unitaryColumn (d : ℕ) (a : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    Fin d → ℂ :=
  fun i => (U : CMatrix (Fin d)) i a

theorem measurable_unitaryColumn (d : ℕ) (a : Fin d) :
    Measurable (unitaryColumn d a) := by
  apply measurable_pi_lambda
  intro i
  have hi :
      Continuous (fun U : CMatrix (Fin d) => U i) :=
    continuous_apply i
  have hia :
      Continuous (fun U : CMatrix (Fin d) => U i a) :=
    (continuous_apply a).comp hi
  exact (hia.comp continuous_subtype_val).measurable

/-- Every column of a unitary matrix has squared Euclidean norm one. -/
theorem vectorNormSq_unitaryColumn
    (d : ℕ) (a : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    vectorNormSq (unitaryColumn d a U) = 1 := by
  have hU :
      Matrix.conjTranspose (U : CMatrix (Fin d)) *
        (U : CMatrix (Fin d)) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp U.property
  have haa := congrFun (congrFun hU a) a
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at haa
  change
    (∑ j : Fin d,
      star ((U : CMatrix (Fin d)) j a) *
        (U : CMatrix (Fin d)) j a) = 1 at haa
  have haa' := congrArg Complex.re haa
  rw [Complex.re_sum] at haa'
  have hterm (z : ℂ) :
      (star z * z).re = Complex.normSq z := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    exact Complex.ofReal_re _
  simp_rw [hterm] at haa'
  norm_num at haa'
  unfold vectorNormSq unitaryColumn
  exact haa'

/-- Right multiplication by a permutation matrix permutes the column
selected by `unitaryColumn`. -/
theorem unitaryColumn_mul_permutationUnitary
    (d : ℕ) (σ : Equiv.Perm (Fin d))
    (U : Matrix.unitaryGroup (Fin d) ℂ) (a : Fin d) :
    unitaryColumn d a (U * permutationUnitary d σ) =
      unitaryColumn d (σ.symm a) U := by
  funext i
  change
    ((U : CMatrix (Fin d)) * σ.permMatrix ℂ) i a =
      (U : CMatrix (Fin d)) i (σ.symm a)
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_apply]
  simp [← Equiv.toPEquiv_symm, Equiv.toPEquiv_apply]

/-- The law of a specified column of a Haar-random unitary matrix. -/
noncomputable def haarColumnMeasure (d : ℕ) (a : Fin d) :
    Measure (Fin d → ℂ) :=
  (unitaryHaarMeasure d).map (unitaryColumn d a)

noncomputable instance isProbabilityMeasure_haarColumnMeasure
    (d : ℕ) (a : Fin d) :
    IsProbabilityMeasure (haarColumnMeasure d a) := by
  unfold haarColumnMeasure
  exact Measure.isProbabilityMeasure_map
    (measurable_unitaryColumn d a).aemeasurable

/-- All specified columns of a Haar-random unitary have the same law. -/
theorem haarColumnMeasure_eq
    (d : ℕ) (a b : Fin d) :
    haarColumnMeasure d a = haarColumnMeasure d b := by
  let σ : Equiv.Perm (Fin d) := Equiv.swap a b
  let P := permutationUnitary d σ
  let R :=
    fun U : Matrix.unitaryGroup (Fin d) ℂ => U * P
  have hRmeas : Measurable R := by
    dsimp [R]
    fun_prop
  have hR :
      (unitaryHaarMeasure d).map R =
        unitaryHaarMeasure d :=
    Measure.IsMulRightInvariant.map_mul_right_eq_self P
  unfold haarColumnMeasure
  calc
    (unitaryHaarMeasure d).map (unitaryColumn d a) =
        ((unitaryHaarMeasure d).map R).map
          (unitaryColumn d a) := by rw [hR]
    _ = (unitaryHaarMeasure d).map
          (unitaryColumn d a ∘ R) := by
      rw [Measure.map_map
        (measurable_unitaryColumn d a) hRmeas]
    _ = (unitaryHaarMeasure d).map
          (unitaryColumn d b) := by
      congr 1
      funext U
      change unitaryColumn d a (U * P) =
        unitaryColumn d b U
      rw [unitaryColumn_mul_permutationUnitary]
      simp [σ]

/-- The natural action of a unitary matrix on a complex vector. -/
def unitaryVectorAction (d : ℕ)
    (W : Matrix.unitaryGroup (Fin d) ℂ)
    (x : Fin d → ℂ) : Fin d → ℂ :=
  fun i => ∑ j : Fin d, (W : CMatrix (Fin d)) i j * x j

theorem measurable_unitaryVectorAction
    (d : ℕ) (W : Matrix.unitaryGroup (Fin d) ℂ) :
    Measurable (unitaryVectorAction d W) := by
  apply measurable_pi_lambda
  intro i
  unfold unitaryVectorAction
  fun_prop

theorem unitaryVectorAction_unitaryColumn
    (d : ℕ) (W U : Matrix.unitaryGroup (Fin d) ℂ)
    (a : Fin d) :
    unitaryVectorAction d W (unitaryColumn d a U) =
      unitaryColumn d a (W * U) := by
  funext i
  simp [unitaryVectorAction, unitaryColumn, Matrix.mul_apply]

/-- The Haar-column law is invariant under every fixed unitary rotation. -/
theorem map_unitaryVectorAction_haarColumnMeasure
    (d : ℕ) (W : Matrix.unitaryGroup (Fin d) ℂ)
    (a : Fin d) :
    (haarColumnMeasure d a).map
        (unitaryVectorAction d W) =
      haarColumnMeasure d a := by
  let L :=
    fun U : Matrix.unitaryGroup (Fin d) ℂ => W * U
  have hLmeas : Measurable L := by
    dsimp [L]
    fun_prop
  have hL :
      (unitaryHaarMeasure d).map L =
        unitaryHaarMeasure d :=
    Measure.IsMulLeftInvariant.map_mul_left_eq_self W
  unfold haarColumnMeasure
  rw [Measure.map_map
    (measurable_unitaryVectorAction d W)
    (measurable_unitaryColumn d a)]
  have hcomp :
      unitaryVectorAction d W ∘ unitaryColumn d a =
        unitaryColumn d a ∘ L := by
    funext U
    exact unitaryVectorAction_unitaryColumn d W U a
  rw [hcomp, ← Measure.map_map
    (measurable_unitaryColumn d a) hLmeas, hL]

/-- A Haar-unitary column lies on the unit sphere almost surely. -/
theorem ae_vectorNormSq_haarColumnMeasure
    (d : ℕ) (a : Fin d) :
    ∀ᵐ x ∂haarColumnMeasure d a,
      vectorNormSq x = 1 := by
  have hp :
      MeasurableSet {x : Fin d → ℂ | vectorNormSq x = 1} := by
    have hv :
        Measurable (fun x : Fin d → ℂ => vectorNormSq x) := by
      unfold vectorNormSq
      fun_prop
    exact hv (measurableSet_singleton (1 : ℝ))
  unfold haarColumnMeasure
  rw [MeasureTheory.ae_map_iff
    (measurable_unitaryColumn d a).aemeasurable hp]
  filter_upwards with U
  exact vectorNormSq_unitaryColumn d a U

end

end QuantumSep
