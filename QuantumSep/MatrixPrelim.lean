import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic

/-!
# Matrix preliminaries for the quantum-separability paper

A bipartite operator is represented as a matrix indexed by pairs.  This avoids
choosing an explicit equivalence `Fin (d*d) ≃ Fin d × Fin d` and makes the two
partial traces entrywise definitions.
-/

open scoped BigOperators ComplexConjugate Matrix Matrix.Norms.Elementwise

namespace QuantumSep

universe u

variable {ι : Type u}

noncomputable section

abbrev CMatrix (ι : Type u) := Matrix ι ι ℂ
abbrev BipartiteMatrix (ι : Type u) := Matrix (ι × ι) (ι × ι) ℂ

/-- Entrywise tensor/Kronecker product. -/
def tensor (A B : CMatrix ι) : BipartiteMatrix ι :=
  fun ac be => A ac.1 be.1 * B ac.2 be.2

@[simp] theorem tensor_apply (A B : CMatrix ι) (a c b e : ι) :
    tensor A B (a, c) (b, e) = A a b * B c e := rfl

/-- Partial trace over the first tensor factor. -/
def partialTrace0 [Fintype ι] (M : BipartiteMatrix ι) : CMatrix ι :=
  fun c e => ∑ a : ι, M (a, c) (a, e)

/-- Partial trace over the second tensor factor. -/
def partialTrace1 [Fintype ι] (M : BipartiteMatrix ι) : CMatrix ι :=
  fun a b => ∑ c : ι, M (a, c) (b, c)

@[simp] theorem partialTrace0_apply [Fintype ι] (M : BipartiteMatrix ι) (c e : ι) :
    partialTrace0 M c e = ∑ a : ι, M (a, c) (a, e) := rfl

@[simp] theorem partialTrace1_apply [Fintype ι] (M : BipartiteMatrix ι) (a b : ι) :
    partialTrace1 M a b = ∑ c : ι, M (a, c) (b, c) := rfl

@[simp] theorem partialTrace0_zero [Fintype ι] :
    partialTrace0 (0 : BipartiteMatrix ι) = 0 := by
  ext c e
  simp [partialTrace0]

@[simp] theorem partialTrace1_zero [Fintype ι] :
    partialTrace1 (0 : BipartiteMatrix ι) = 0 := by
  ext a b
  simp [partialTrace1]

@[simp] theorem partialTrace0_add [Fintype ι] (M N : BipartiteMatrix ι) :
    partialTrace0 (M + N) = partialTrace0 M + partialTrace0 N := by
  ext c e
  simp [partialTrace0, Finset.sum_add_distrib]

@[simp] theorem partialTrace1_add [Fintype ι] (M N : BipartiteMatrix ι) :
    partialTrace1 (M + N) = partialTrace1 M + partialTrace1 N := by
  ext a b
  simp [partialTrace1, Finset.sum_add_distrib]

@[simp] theorem partialTrace0_sub [Fintype ι] (M N : BipartiteMatrix ι) :
    partialTrace0 (M - N) = partialTrace0 M - partialTrace0 N := by
  ext c e
  simp [partialTrace0, Finset.sum_sub_distrib]

@[simp] theorem partialTrace1_sub [Fintype ι] (M N : BipartiteMatrix ι) :
    partialTrace1 (M - N) = partialTrace1 M - partialTrace1 N := by
  ext a b
  simp [partialTrace1, Finset.sum_sub_distrib]

@[simp] theorem partialTrace0_smul [Fintype ι] (z : ℂ) (M : BipartiteMatrix ι) :
    partialTrace0 (z • M) = z • partialTrace0 M := by
  ext c e
  simp [partialTrace0, Finset.mul_sum]

@[simp] theorem partialTrace1_smul [Fintype ι] (z : ℂ) (M : BipartiteMatrix ι) :
    partialTrace1 (z • M) = z • partialTrace1 M := by
  ext a b
  simp [partialTrace1, Finset.mul_sum]

/-- The first partial trace of a tensor product. -/
theorem partialTrace0_tensor [Fintype ι] (A B : CMatrix ι) :
    partialTrace0 (tensor A B) = A.trace • B := by
  ext c e
  change (∑ a : ι, A a a * B c e) = A.trace * B c e
  simp only [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Finset.sum_mul]

/-- The second partial trace of a tensor product. -/
theorem partialTrace1_tensor [Fintype ι] (A B : CMatrix ι) :
    partialTrace1 (tensor A B) = B.trace • A := by
  ext a b
  change (∑ c : ι, A a b * B c c) = B.trace * A a b
  simp only [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

/-- The complex dimension, used in the paper's formulas. -/
def dimC [Fintype ι] : ℂ := (Fintype.card ι : ℂ)

/-- Scalar component `Tr M / d^2`. -/
def scalarPart [Fintype ι] (M : BipartiteMatrix ι) : ℂ :=
  M.trace / (dimC (ι := ι) * dimC (ι := ι))

/-- First local traceless candidate. -/
def localA [Fintype ι] [DecidableEq ι] (M : BipartiteMatrix ι) : CMatrix ι :=
  (dimC (ι := ι))⁻¹ • partialTrace1 M - scalarPart M • (1 : CMatrix ι)

/-- Second local traceless candidate. -/
def localB [Fintype ι] [DecidableEq ι] (M : BipartiteMatrix ι) : CMatrix ι :=
  (dimC (ι := ι))⁻¹ • partialTrace0 M - scalarPart M • (1 : CMatrix ι)

/-- The residual component in the local decomposition. -/
def correlationPart [Fintype ι] [DecidableEq ι] (M : BipartiteMatrix ι) :
    BipartiteMatrix ι :=
  M
    - scalarPart M • tensor (1 : CMatrix ι) (1 : CMatrix ι)
    - tensor (localA M) (1 : CMatrix ι)
    - tensor (1 : CMatrix ι) (localB M)

/-- Reconstruction is definitional once the residual has been introduced. -/
theorem localDecomposition_reconstruct [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) :
    M = scalarPart M • tensor (1 : CMatrix ι) (1 : CMatrix ι)
      + tensor (localA M) (1 : CMatrix ι)
      + tensor (1 : CMatrix ι) (localB M)
      + correlationPart M := by
  unfold correlationPart
  abel

@[simp] theorem scalarPart_add [Fintype ι]
    (M N : BipartiteMatrix ι) :
    scalarPart (M + N) = scalarPart M + scalarPart N := by
  unfold scalarPart
  rw [Matrix.trace_add]
  ring

@[simp] theorem scalarPart_sub [Fintype ι]
    (M N : BipartiteMatrix ι) :
    scalarPart (M - N) = scalarPart M - scalarPart N := by
  unfold scalarPart
  rw [Matrix.trace_sub]
  ring

@[simp] theorem scalarPart_smul [Fintype ι]
    (z : ℂ) (M : BipartiteMatrix ι) :
    scalarPart (z • M) = z * scalarPart M := by
  unfold scalarPart
  rw [Matrix.trace_smul]
  ring

@[simp] theorem localA_add [Fintype ι] [DecidableEq ι]
    (M N : BipartiteMatrix ι) :
    localA (M + N) = localA M + localA N := by
  unfold localA
  rw [partialTrace1_add, scalarPart_add]
  module

@[simp] theorem localB_add [Fintype ι] [DecidableEq ι]
    (M N : BipartiteMatrix ι) :
    localB (M + N) = localB M + localB N := by
  unfold localB
  rw [partialTrace0_add, scalarPart_add]
  module

@[simp] theorem correlationPart_add [Fintype ι] [DecidableEq ι]
    (M N : BipartiteMatrix ι) :
    correlationPart (M + N) =
      correlationPart M + correlationPart N := by
  unfold correlationPart
  rw [scalarPart_add, localA_add, localB_add]
  ext ac be
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    tensor]
  ring

/-- Hilbert--Schmidt pairing, written entrywise. -/
def hsInner [Fintype ι] (A B : CMatrix ι) : ℂ :=
  ∑ i : ι, ∑ j : ι, star (A i j) * B i j

/-- Squared Frobenius norm. -/
def frobeniusSq [Fintype ι] (A : CMatrix ι) : ℝ :=
  ∑ i : ι, ∑ j : ι, Complex.normSq (A i j)

/-- Entrywise maximum norm.  For a finite matrix, the function-space norm
is the maximum of the entry norms. -/
def entryNorm [Fintype ι] (A : CMatrix ι) : ℝ :=
  ‖A‖

/-- Taking either partial trace preserves the full trace. -/
theorem trace_partialTrace0 [Fintype ι] (M : BipartiteMatrix ι) :
    (partialTrace0 M).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, partialTrace0]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Taking either partial trace preserves the full trace. -/
theorem trace_partialTrace1 [Fintype ι] (M : BipartiteMatrix ι) :
    (partialTrace1 M).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag_apply, partialTrace1]
  rw [Fintype.sum_prod_type]

/-- The trace of a tensor product is the product of the traces. -/
theorem trace_tensor [Fintype ι] (A B : CMatrix ι) :
    (tensor A B).trace = A.trace * B.trace := by
  rw [← trace_partialTrace0 (tensor A B), partialTrace0_tensor,
    Matrix.trace_smul]
  rfl

/-- The complexified dimension is nonzero for a nonempty finite index type. -/
theorem dimC_ne_zero [Fintype ι] [Nonempty ι] :
    dimC (ι := ι) ≠ 0 := by
  unfold dimC
  exact_mod_cast Fintype.card_ne_zero

/-- A matrix with either vanishing partial trace has zero scalar component. -/
theorem scalarPart_eq_zero_of_partialTrace0_eq_zero
    [Fintype ι] (M : BipartiteMatrix ι)
    (hzero : partialTrace0 M = 0) :
    scalarPart M = 0 := by
  have htrace : M.trace = 0 := by
    rw [← trace_partialTrace0 M, hzero, Matrix.trace_zero]
  simp [scalarPart, htrace]

/-- A matrix with both partial traces zero is fixed by the correlation
projection. -/
theorem correlationPart_eq_self_of_partialTraces_zero
    [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι)
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0) :
    correlationPart M = M := by
  have hs := scalarPart_eq_zero_of_partialTrace0_eq_zero M hzero0
  have hA : localA M = 0 := by
    unfold localA
    rw [hzero1, hs]
    simp
  have hB : localB M = 0 := by
    unfold localB
    rw [hzero0, hs]
    simp
  unfold correlationPart
  rw [hs, hA, hB]
  ext ac be
  simp [tensor]

/-- If a zero-partial-trace matrix is split into flat and tail pieces, then
subtracting the projected flat piece leaves precisely the projected tail. -/
theorem sub_correlationPart_eq_correlationPart_tail
    [Fintype ι] [DecidableEq ι]
    (total flat tail : BipartiteMatrix ι)
    (hsplit : total = flat + tail)
    (hzero0 : partialTrace0 total = 0)
    (hzero1 : partialTrace1 total = 0) :
    total - correlationPart flat = correlationPart tail := by
  have hfixed :=
    correlationPart_eq_self_of_partialTraces_zero total hzero0 hzero1
  rw [hsplit, correlationPart_add] at hfixed
  rw [hsplit, ← hfixed]
  abel

/-- The explicit first local component is traceless. -/
theorem trace_localA [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) :
    (localA M).trace = 0 := by
  have hd := dimC_ne_zero (ι := ι)
  rw [localA, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, trace_partialTrace1]
  unfold scalarPart
  change (dimC (ι := ι))⁻¹ * M.trace -
    (M.trace / (dimC (ι := ι) * dimC (ι := ι))) * dimC (ι := ι) = 0
  field_simp [hd]
  ring

/-- The explicit second local component is traceless. -/
theorem trace_localB [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) :
    (localB M).trace = 0 := by
  have hd := dimC_ne_zero (ι := ι)
  rw [localB, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, trace_partialTrace0]
  unfold scalarPart
  change (dimC (ι := ι))⁻¹ * M.trace -
    (M.trace / (dimC (ι := ι) * dimC (ι := ι))) * dimC (ι := ι) = 0
  field_simp [hd]
  ring

/-- The correlation component has zero partial trace over the first factor. -/
theorem partialTrace0_correlationPart
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) :
    partialTrace0 (correlationPart M) = 0 := by
  have hd := dimC_ne_zero (ι := ι)
  rw [correlationPart, partialTrace0_sub, partialTrace0_sub, partialTrace0_sub,
    partialTrace0_smul, partialTrace0_tensor, partialTrace0_tensor,
    partialTrace0_tensor, Matrix.trace_one, trace_localA, zero_smul, sub_zero]
  ext c e
  simp only [localB]
  change partialTrace0 M c e -
      scalarPart M * (dimC (ι := ι) * (1 : CMatrix ι) c e) -
      dimC (ι := ι) *
        ((dimC (ι := ι))⁻¹ * partialTrace0 M c e -
          scalarPart M * (1 : CMatrix ι) c e) = 0
  field_simp [hd]
  ring

/-- The correlation component has zero partial trace over the second factor. -/
theorem partialTrace1_correlationPart
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) :
    partialTrace1 (correlationPart M) = 0 := by
  have hd := dimC_ne_zero (ι := ι)
  rw [correlationPart, partialTrace1_sub, partialTrace1_sub, partialTrace1_sub,
    partialTrace1_smul, partialTrace1_tensor, partialTrace1_tensor,
    partialTrace1_tensor, Matrix.trace_one, trace_localB, zero_smul, sub_zero]
  ext a b
  simp only [localA]
  change partialTrace1 M a b -
      scalarPart M * (dimC (ι := ι) * (1 : CMatrix ι) a b) -
      dimC (ι := ι) *
        ((dimC (ι := ι))⁻¹ * partialTrace1 M a b -
          scalarPart M * (1 : CMatrix ι) a b) = 0
  field_simp [hd]
  ring

/-- The decomposition with traceless local terms and a residual with vanishing
partial traces is unique.  In particular, every such decomposition agrees with
the explicit definitions `scalarPart`, `localA`, `localB`, and
`correlationPart`. -/
theorem localDecomposition_unique
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) (alpha : ℂ)
    (A B : CMatrix ι) (C : BipartiteMatrix ι)
    (hreconstruct :
      M = alpha • tensor (1 : CMatrix ι) (1 : CMatrix ι) +
        tensor A (1 : CMatrix ι) +
        tensor (1 : CMatrix ι) B + C)
    (htraceA : A.trace = 0)
    (htraceB : B.trace = 0)
    (hpartial0C : partialTrace0 C = 0)
    (hpartial1C : partialTrace1 C = 0) :
    alpha = scalarPart M ∧
      A = localA M ∧ B = localB M ∧ C = correlationPart M := by
  have hd := dimC_ne_zero (ι := ι)
  have htraceC : C.trace = 0 := by
    rw [← trace_partialTrace0 C, hpartial0C, Matrix.trace_zero]
  have htraceM :
      M.trace = alpha * (dimC (ι := ι) * dimC (ι := ι)) := by
    rw [hreconstruct, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_smul, trace_tensor, trace_tensor, trace_tensor,
      Matrix.trace_one, htraceA, htraceB, htraceC]
    simp only [dimC]
    ring
  have halpha : alpha = scalarPart M := by
    unfold scalarPart
    rw [htraceM]
    field_simp [hd]
  have hpartial1 :
      partialTrace1 M =
        alpha • (dimC (ι := ι) • (1 : CMatrix ι)) +
        dimC (ι := ι) • A := by
    rw [hreconstruct, partialTrace1_add, partialTrace1_add, partialTrace1_add,
      partialTrace1_smul, partialTrace1_tensor, partialTrace1_tensor,
      partialTrace1_tensor, Matrix.trace_one, htraceB, hpartial1C]
    simp
    abel
  have hA : A = localA M := by
    funext a b
    have hab := congrArg (fun X : CMatrix ι => X a b) hpartial1
    change partialTrace1 M a b =
      alpha * (dimC (ι := ι) * (1 : CMatrix ι) a b) +
        dimC (ι := ι) * A a b at hab
    simp only [localA, Matrix.sub_apply, Matrix.smul_apply]
    rw [← halpha]
    rw [hab]
    symm
    calc
      (dimC (ι := ι))⁻¹ *
            (alpha * (dimC (ι := ι) * (1 : CMatrix ι) a b) +
              dimC (ι := ι) * A a b) -
          alpha * (1 : CMatrix ι) a b =
          ((dimC (ι := ι))⁻¹ * dimC (ι := ι)) * A a b +
            (((dimC (ι := ι))⁻¹ * dimC (ι := ι)) - 1) *
              (alpha * (1 : CMatrix ι) a b) := by ring
      _ = A a b := by rw [inv_mul_cancel₀ hd]; ring
  have hpartial0 :
      partialTrace0 M =
        alpha • (dimC (ι := ι) • (1 : CMatrix ι)) +
        dimC (ι := ι) • B := by
    rw [hreconstruct, partialTrace0_add, partialTrace0_add, partialTrace0_add,
      partialTrace0_smul, partialTrace0_tensor, partialTrace0_tensor,
      partialTrace0_tensor, Matrix.trace_one, htraceA, hpartial0C]
    simp
    abel
  have hB : B = localB M := by
    funext c e
    have hce := congrArg (fun X : CMatrix ι => X c e) hpartial0
    change partialTrace0 M c e =
      alpha * (dimC (ι := ι) * (1 : CMatrix ι) c e) +
        dimC (ι := ι) * B c e at hce
    simp only [localB, Matrix.sub_apply, Matrix.smul_apply]
    rw [← halpha]
    rw [hce]
    symm
    calc
      (dimC (ι := ι))⁻¹ *
            (alpha * (dimC (ι := ι) * (1 : CMatrix ι) c e) +
              dimC (ι := ι) * B c e) -
          alpha * (1 : CMatrix ι) c e =
          ((dimC (ι := ι))⁻¹ * dimC (ι := ι)) * B c e +
            (((dimC (ι := ι))⁻¹ * dimC (ι := ι)) - 1) *
              (alpha * (1 : CMatrix ι) c e) := by ring
      _ = B c e := by rw [inv_mul_cancel₀ hd]; ring
  have hC : C = correlationPart M := by
    rw [correlationPart, ← halpha, ← hA, ← hB, hreconstruct]
    abel
  exact ⟨halpha, hA, hB, hC⟩

/-- Pairing the identity with a matrix gives its trace. -/
theorem hsInner_one_left [Fintype ι] [DecidableEq ι] (A : CMatrix ι) :
    hsInner (1 : CMatrix ι) A = A.trace := by
  simp [hsInner, Matrix.trace, Matrix.one_apply, apply_ite]

/-- Pairing a matrix with the identity gives the conjugate of its trace. -/
theorem hsInner_one_right [Fintype ι] [DecidableEq ι] (A : CMatrix ι) :
    hsInner A (1 : CMatrix ι) = star A.trace := by
  simp [hsInner, Matrix.trace, Matrix.one_apply, apply_ite]

/-- The Hilbert--Schmidt pairing factorizes over tensor products. -/
theorem hsInner_tensor [Fintype ι] (A B C D : CMatrix ι) :
    hsInner (tensor A B) (tensor C D) = hsInner A C * hsInner B D := by
  unfold hsInner tensor
  have hExpand :
      (∑ i : ι × ι, ∑ j : ι × ι,
        star (A i.1 j.1 * B i.2 j.2) * (C i.1 j.1 * D i.2 j.2)) =
      ∑ a, ∑ c, ∑ b, ∑ e,
        star (A a b * B c e) * (C a b * D c e) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    rw [Fintype.sum_prod_type]
  rw [hExpand]
  simp only [star_mul]
  have hreorder (a b c e : ι) :
      star (B c e) * star (A a b) * (C a b * D c e) =
      (star (A a b) * C a b) * (star (B c e) * D c e) := by ring
  simp_rw [hreorder]
  symm
  calc
    (∑ a, ∑ b, star (A a b) * C a b) *
        (∑ c, ∑ e, star (B c e) * D c e) =
      ∑ a, ∑ c,
        (∑ b, star (A a b) * C a b) *
        (∑ e, star (B c e) * D c e) :=
      Fintype.sum_mul_sum _ _
    _ = ∑ a, ∑ c, ∑ b, ∑ e,
        (star (A a b) * C a b) * (star (B c e) * D c e) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      exact Fintype.sum_mul_sum _ _

/-- The self-pairing is the squared Frobenius norm. -/
theorem hsInner_self [Fintype ι] (A : CMatrix ι) :
    hsInner A A = (frobeniusSq A : ℂ) := by
  unfold hsInner frobeniusSq
  calc
    (∑ i, ∑ j, star (A i j) * A i j) =
        ∑ i, ∑ j, (Complex.normSq (A i j) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact Complex.normSq_eq_conj_mul_self.symm
    _ = (∑ i, ∑ j, Complex.normSq (A i j) : ℝ) := by
      push_cast
      rfl

/-- Scalar multiplication in the first Hilbert--Schmidt argument. -/
theorem hsInner_smul_left [Fintype ι] (z : ℂ) (A B : CMatrix ι) :
    hsInner (z • A) B = star z * hsInner A B := by
  unfold hsInner
  change (∑ i, ∑ j, star (z * A i j) * B i j) =
    star z * ∑ i, ∑ j, star (A i j) * B i j
  simp only [star_mul]
  have hreorder (i j : ι) :
      star (A i j) * star z * B i j =
      star z * (star (A i j) * B i j) := by ring
  simp_rw [hreorder]
  symm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- Scalar multiplication in the second Hilbert--Schmidt argument. -/
theorem hsInner_smul_right [Fintype ι] (z : ℂ) (A B : CMatrix ι) :
    hsInner A (z • B) = z * hsInner A B := by
  unfold hsInner
  change (∑ i, ∑ j, star (A i j) * (z * B i j)) =
    z * ∑ i, ∑ j, star (A i j) * B i j
  have hreorder (i j : ι) :
      star (A i j) * (z * B i j) =
      z * (star (A i j) * B i j) := by ring
  simp_rw [hreorder]
  symm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]

/-- Pairing `A ⊗ I` against a bipartite matrix contracts its second
factor, producing the second partial trace. -/
theorem hsInner_tensor_one [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) (M : BipartiteMatrix ι) :
    hsInner (tensor A (1 : CMatrix ι)) M =
      hsInner A (partialTrace1 M) := by
  unfold hsInner tensor partialTrace1
  have hExpand :
      (∑ i : ι × ι, ∑ j : ι × ι,
        star (A i.1 j.1 * (1 : CMatrix ι) i.2 j.2) * M i j) =
      ∑ a, ∑ c, ∑ b, ∑ e,
        star (A a b * (1 : CMatrix ι) c e) * M (a, c) (b, e) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    rw [Fintype.sum_prod_type]
  rw [hExpand]
  simp [Matrix.one_apply, apply_ite]
  symm
  calc
    (∑ a, ∑ b, star (A a b) * ∑ c, M (a, c) (b, c)) =
        ∑ a, ∑ b, ∑ c, star (A a b) * M (a, c) (b, c) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ a, ∑ c, ∑ b, star (A a b) * M (a, c) (b, c) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]

/-- Pairing `I ⊗ B` against a bipartite matrix contracts its first
factor, producing the first partial trace. -/
theorem hsInner_one_tensor [Fintype ι] [DecidableEq ι]
    (B : CMatrix ι) (M : BipartiteMatrix ι) :
    hsInner (tensor (1 : CMatrix ι) B) M =
      hsInner B (partialTrace0 M) := by
  unfold hsInner tensor partialTrace0
  have hExpand :
      (∑ i : ι × ι, ∑ j : ι × ι,
        star ((1 : CMatrix ι) i.1 j.1 * B i.2 j.2) * M i j) =
      ∑ a, ∑ c, ∑ b, ∑ e,
        star ((1 : CMatrix ι) a b * B c e) * M (a, c) (b, e) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro c _
    rw [Fintype.sum_prod_type]
  rw [hExpand]
  simp [Matrix.one_apply, apply_ite]
  symm
  calc
    (∑ c, ∑ e, star (B c e) * ∑ a, M (a, c) (a, e)) =
        ∑ c, ∑ e, ∑ a, star (B c e) * M (a, c) (a, e) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ c, ∑ a, ∑ e, star (B c e) * M (a, c) (a, e) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ c, ∑ e, star (B c e) * M (a, c) (a, e) := by
      rw [Finset.sum_comm]

/-- The six pairings between distinct summands in the local decomposition
vanish.  This is the manuscript's pairwise Hilbert--Schmidt orthogonality
statement, with one orientation chosen for each unordered pair. -/
theorem localDecomposition_pairwiseOrthogonal
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) :
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
      (correlationPart M) = 0 := by
  constructor
  · rw [hsInner_smul_left, hsInner_tensor, hsInner_one_left, trace_localA,
      zero_mul, mul_zero]
  constructor
  · rw [hsInner_smul_left, hsInner_tensor, hsInner_one_left (localB M),
      trace_localB, mul_zero, mul_zero]
  constructor
  · rw [hsInner_tensor, hsInner_one_right, trace_localA, star_zero, zero_mul]
  constructor
  · rw [hsInner_smul_left, hsInner_tensor_one,
      partialTrace1_correlationPart]
    simp [hsInner]
  constructor
  · rw [hsInner_tensor_one, partialTrace1_correlationPart]
    simp [hsInner]
  · rw [hsInner_one_tensor, partialTrace0_correlationPart]
    simp [hsInner]

/-- Additivity in the first Hilbert--Schmidt argument. -/
theorem hsInner_add_left [Fintype ι] (A B C : CMatrix ι) :
    hsInner (A + B) C = hsInner A C + hsInner B C := by
  unfold hsInner
  change (∑ i, ∑ j, star (A i j + B i j) * C i j) =
    (∑ i, ∑ j, star (A i j) * C i j) +
    ∑ i, ∑ j, star (B i j) * C i j
  have hstar (i j : ι) :
      star (A i j + B i j) = star (A i j) + star (B i j) :=
    map_add (starAddEquiv : ℂ ≃+ ℂ) _ _
  simp_rw [hstar, add_mul, Finset.sum_add_distrib]

/-- Additivity in the second Hilbert--Schmidt argument. -/
theorem hsInner_add_right [Fintype ι] (A B C : CMatrix ι) :
    hsInner A (B + C) = hsInner A B + hsInner A C := by
  unfold hsInner
  change (∑ i, ∑ j, star (A i j) * (B i j + C i j)) =
    (∑ i, ∑ j, star (A i j) * B i j) +
    ∑ i, ∑ j, star (A i j) * C i j
  simp only [mul_add, Finset.sum_add_distrib]

/-- Conjugate symmetry of the Hilbert--Schmidt pairing. -/
theorem hsInner_conj_symm [Fintype ι] (A B : CMatrix ι) :
    hsInner B A = star (hsInner A B) := by
  unfold hsInner
  symm
  calc
    star (∑ i, ∑ j, star (A i j) * B i j) =
        ∑ i, star (∑ j, star (A i j) * B i j) := by
      exact star_sum Finset.univ (fun i => ∑ j, star (A i j) * B i j)
    _ = ∑ i, ∑ j, star (star (A i j) * B i j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact star_sum Finset.univ (fun j => star (A i j) * B i j)
    _ = ∑ i, ∑ j, star (B i j) * A i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [star_mul, star_star]

/-- Pythagoras for two Hilbert--Schmidt orthogonal matrices. -/
theorem frobeniusSq_add_of_hsInner_eq_zero [Fintype ι] (A B : CMatrix ι)
    (h : hsInner A B = 0) :
    frobeniusSq (A + B) = frobeniusSq A + frobeniusSq B := by
  have hBA : hsInner B A = 0 := by
    calc
      hsInner B A = star (hsInner A B) := hsInner_conj_symm A B
      _ = 0 := by rw [h, star_zero]
  have hc :
      (frobeniusSq (A + B) : ℂ) =
        (frobeniusSq A + frobeniusSq B : ℝ) := by
    calc
      (frobeniusSq (A + B) : ℂ) = hsInner (A + B) (A + B) :=
        (hsInner_self (A + B)).symm
      _ = hsInner A (A + B) + hsInner B (A + B) :=
        hsInner_add_left A B (A + B)
      _ = (hsInner A A + hsInner A B) +
          (hsInner B A + hsInner B B) := by
        rw [hsInner_add_right, hsInner_add_right]
      _ = hsInner A A + hsInner B B := by rw [h, hBA]; ring
      _ = (frobeniusSq A : ℂ) + (frobeniusSq B : ℂ) := by
        rw [hsInner_self, hsInner_self]
      _ = (frobeniusSq A + frobeniusSq B : ℝ) := by
        push_cast
        rfl
  exact_mod_cast hc

/-- Pythagoras for four pairwise Hilbert--Schmidt orthogonal matrices. -/
theorem frobeniusSq_add_four_of_pairwiseOrthogonal
    [Fintype ι] (A B C D : CMatrix ι)
    (hAB : hsInner A B = 0)
    (hAC : hsInner A C = 0)
    (hAD : hsInner A D = 0)
    (hBC : hsInner B C = 0)
    (hBD : hsInner B D = 0)
    (hCD : hsInner C D = 0) :
    frobeniusSq (A + B + C + D) =
      frobeniusSq A + frobeniusSq B + frobeniusSq C + frobeniusSq D := by
  have hAB_C : hsInner (A + B) C = 0 := by
    rw [hsInner_add_left, hAC, hBC]
    ring
  have hABC_D : hsInner (A + B + C) D = 0 := by
    rw [hsInner_add_left, hsInner_add_left, hAD, hBD, hCD]
    ring
  calc
    frobeniusSq (A + B + C + D) =
        frobeniusSq (A + B + C) + frobeniusSq D :=
      frobeniusSq_add_of_hsInner_eq_zero (A + B + C) D hABC_D
    _ = (frobeniusSq (A + B) + frobeniusSq C) + frobeniusSq D := by
      rw [frobeniusSq_add_of_hsInner_eq_zero (A + B) C hAB_C]
    _ = ((frobeniusSq A + frobeniusSq B) + frobeniusSq C) +
        frobeniusSq D := by
      rw [frobeniusSq_add_of_hsInner_eq_zero A B hAB]

/-- Frobenius Pythagoras for the manuscript's local decomposition. -/
theorem localDecomposition_frobenius_pythagoras
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) :
    frobeniusSq M =
      frobeniusSq
        (scalarPart M • tensor (1 : CMatrix ι) (1 : CMatrix ι)) +
      frobeniusSq (tensor (localA M) (1 : CMatrix ι)) +
      frobeniusSq (tensor (1 : CMatrix ι) (localB M)) +
      frobeniusSq (correlationPart M) := by
  rcases localDecomposition_pairwiseOrthogonal M with
    ⟨hSA, hSB, hAB, hSC, hAC, hBC⟩
  calc
    frobeniusSq M = frobeniusSq
        (scalarPart M • tensor (1 : CMatrix ι) (1 : CMatrix ι) +
          tensor (localA M) (1 : CMatrix ι) +
          tensor (1 : CMatrix ι) (localB M) +
          correlationPart M) :=
      congrArg frobeniusSq (localDecomposition_reconstruct M)
    _ = _ := frobeniusSq_add_four_of_pairwiseOrthogonal
      _ _ _ _ hSA hSB hSC hAB hAC hBC

theorem frobeniusSq_nonneg [Fintype ι] (M : CMatrix ι) :
    0 ≤ frobeniusSq M := by
  unfold frobeniusSq
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (M i j)

/-- The squared Frobenius norm detects the zero matrix. -/
theorem frobeniusSq_eq_zero_iff
    [Fintype ι] (M : CMatrix ι) :
    frobeniusSq M = 0 ↔ M = 0 := by
  unfold frobeniusSq
  simp only [
    Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ =>
        Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (M i j)),
    Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (M _ j)),
    Complex.normSq_eq_zero]
  constructor
  · intro h
    funext i j
    exact h i (Finset.mem_univ i) j (Finset.mem_univ j)
  · intro h i _ j _
    simp [h]

/-- Orthogonal projection of a matrix onto the scalar matrices. -/
def traceScalarMatrix [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) : CMatrix ι :=
  (A.trace / dimC (ι := ι)) • (1 : CMatrix ι)

/-- Orthogonal projection onto the traceless matrices. -/
def tracelessPart [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) : CMatrix ι :=
  A - traceScalarMatrix A

@[simp] theorem trace_tracelessPart
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : CMatrix ι) :
    (tracelessPart A).trace = 0 := by
  have hd := dimC_ne_zero (ι := ι)
  rw [tracelessPart, Matrix.trace_sub, traceScalarMatrix,
    Matrix.trace_smul, Matrix.trace_one]
  change A.trace - (A.trace / dimC (ι := ι)) * dimC (ι := ι) = 0
  field_simp [hd]
  ring

/-- Decomposition into scalar and traceless parts. -/
theorem traceScalarMatrix_add_tracelessPart
    [Fintype ι] [DecidableEq ι]
    (A : CMatrix ι) :
    traceScalarMatrix A + tracelessPart A = A := by
  unfold tracelessPart
  abel

/-- Removing the scalar trace component cannot increase Frobenius norm. -/
theorem tracelessPart_frobeniusSq_le
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : CMatrix ι) :
    frobeniusSq (tracelessPart A) ≤ frobeniusSq A := by
  have horth :
      hsInner (traceScalarMatrix A) (tracelessPart A) = 0 := by
    rw [traceScalarMatrix, hsInner_smul_left, hsInner_one_left,
      trace_tracelessPart, mul_zero]
  have hpyth :=
    frobeniusSq_add_of_hsInner_eq_zero
      (traceScalarMatrix A) (tracelessPart A) horth
  rw [traceScalarMatrix_add_tracelessPart] at hpyth
  have hnonneg := frobeniusSq_nonneg (traceScalarMatrix A)
  linarith

/-- The zero-partial-trace projection cannot increase squared Frobenius norm. -/
theorem correlationPart_frobeniusSq_le
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : BipartiteMatrix ι) :
    frobeniusSq (correlationPart M) ≤ frobeniusSq M := by
  have hp := localDecomposition_frobenius_pythagoras M
  have hscalar := frobeniusSq_nonneg
    (scalarPart M • tensor (1 : CMatrix ι) (1 : CMatrix ι))
  have hA := frobeniusSq_nonneg (tensor (localA M) (1 : CMatrix ι))
  have hB := frobeniusSq_nonneg (tensor (1 : CMatrix ι) (localB M))
  linarith

/-- Partial trace over the first factor preserves Hermiticity. -/
theorem partialTrace0_isHermitian [Fintype ι]
    (M : BipartiteMatrix ι) (hM : M.IsHermitian) :
    (partialTrace0 M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro c e
  unfold partialTrace0
  rw [star_sum Finset.univ]
  apply Finset.sum_congr rfl
  intro a _
  exact hM.apply (a, c) (a, e)

/-- Partial trace over the second factor preserves Hermiticity. -/
theorem partialTrace1_isHermitian [Fintype ι]
    (M : BipartiteMatrix ι) (hM : M.IsHermitian) :
    (partialTrace1 M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro a b
  unfold partialTrace1
  rw [star_sum Finset.univ]
  apply Finset.sum_congr rfl
  intro c _
  exact hM.apply (a, c) (b, c)

/-- A tensor product of Hermitian matrices is Hermitian. -/
theorem tensor_isHermitian [Fintype ι] (A B : CMatrix ι)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (tensor A B).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro ac be
  simp only [tensor, star_mul]
  rw [hA.apply, hB.apply]
  exact mul_comm _ _

/-- The scalar coefficient of a Hermitian matrix is real/self-adjoint. -/
theorem scalarPart_isSelfAdjoint [Fintype ι]
    (M : BipartiteMatrix ι) (hM : M.IsHermitian) :
    IsSelfAdjoint (scalarPart M) := by
  have htrace : IsSelfAdjoint M.trace := by
    rw [IsSelfAdjoint]
    rw [← Matrix.trace_conjTranspose, hM.eq]
  have hdim : IsSelfAdjoint (dimC (ι := ι)) := by
    rw [IsSelfAdjoint]
    simp [dimC]
  unfold scalarPart
  exact htrace.div (hdim.mul hdim)

/-- The first explicit local component of a Hermitian matrix is Hermitian. -/
theorem localA_isHermitian [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (hM : M.IsHermitian) :
    (localA M).IsHermitian := by
  have hdimInv : IsSelfAdjoint (dimC (ι := ι))⁻¹ := by
    rw [IsSelfAdjoint]
    simp [dimC]
  exact ((partialTrace1_isHermitian M hM).smul hdimInv).sub
    (Matrix.isHermitian_one.smul (scalarPart_isSelfAdjoint M hM))

/-- The second explicit local component of a Hermitian matrix is Hermitian. -/
theorem localB_isHermitian [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (hM : M.IsHermitian) :
    (localB M).IsHermitian := by
  have hdimInv : IsSelfAdjoint (dimC (ι := ι))⁻¹ := by
    rw [IsSelfAdjoint]
    simp [dimC]
  exact ((partialTrace0_isHermitian M hM).smul hdimInv).sub
    (Matrix.isHermitian_one.smul (scalarPart_isSelfAdjoint M hM))

/-- The residual correlation component of a Hermitian matrix is Hermitian. -/
theorem correlationPart_isHermitian [Fintype ι] [DecidableEq ι]
    (M : BipartiteMatrix ι) (hM : M.IsHermitian) :
    (correlationPart M).IsHermitian := by
  unfold correlationPart
  have hOne : (1 : CMatrix ι).IsHermitian := Matrix.isHermitian_one
  have hScalarTensor :
      (scalarPart M • tensor (1 : CMatrix ι) (1 : CMatrix ι)).IsHermitian :=
    (tensor_isHermitian _ _ hOne hOne).smul (scalarPart_isSelfAdjoint M hM)
  have hLocalA :
      (tensor (localA M) (1 : CMatrix ι)).IsHermitian :=
    tensor_isHermitian _ _ (localA_isHermitian M hM) hOne
  have hLocalB :
      (tensor (1 : CMatrix ι) (localB M)).IsHermitian :=
    tensor_isHermitian _ _ hOne (localB_isHermitian M hM)
  exact ((hM.sub hScalarTensor).sub hLocalA).sub hLocalB

end

end QuantumSep
