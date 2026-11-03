import QuantumSep.HaarFlatTail

/-!
# Product objectives under local unitary conjugation
-/

namespace QuantumSep

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Unnormalized tensor product of two coordinate vectors. -/
def productVector (d : ℕ) (x y : Fin d → ℂ) :
    Fin d × Fin d → ℂ :=
  fun ac => x ac.1 * y ac.2

/-- Real quadratic form of a complex matrix. -/
def matrixQuadraticFormReal
    {κ : Type*} [Fintype κ]
    (M : CMatrix κ) (z : κ → ℂ) : ℝ :=
  (star z ⬝ᵥ (M *ᵥ z)).re

theorem matrixQuarticForm_eq_productQuadratic
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (x y : Fin d → ℂ) :
    matrixQuarticForm M x y =
      matrixQuadraticFormReal M (productVector d x y) / (d : ℝ) ^ 2 := by
  unfold matrixQuarticForm
  rw [show
      (∑ a, ∑ b, ∑ c, ∑ e, quarticSummand M x y a b c e) =
        ∑ a, ∑ c, ∑ b, ∑ e, quarticSummand M x y a b c e by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]]
  unfold matrixQuadraticFormReal productVector
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_mul,
    Complex.star_def]
  rw [Fintype.sum_prod_type]
  simp_rw [Complex.re_sum]
  unfold cardR
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_prod_type]
  simp_rw [quarticSummand]
  have hcomplex :
      star (y c) * star (x a) *
          (∑ b : Fin d, ∑ e : Fin d,
            M (a, c) (b, e) * (x b * y e)) =
        ∑ b : Fin d, ∑ e : Fin d,
          M (a, c) (b, e) * star (x a) * x b *
            star (y c) * y e := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro e _
    ring
  change
    (∑ b : Fin d, ∑ e : Fin d,
      (M (a, c) (b, e) * star (x a) * x b *
        star (y c) * y e).re) =
      (star (y c) * star (x a) *
        (∑ b : Fin d, ∑ e : Fin d,
          M (a, c) (b, e) * (x b * y e))).re
  rw [hcomplex, Complex.re_sum]
  simp_rw [Complex.re_sum]
  norm_num

theorem matrixQuadraticFormReal_conjTranspose_mul
    {κ : Type*} [Fintype κ]
    (W M : CMatrix κ) (z : κ → ℂ) :
    matrixQuadraticFormReal (Matrix.conjTranspose W * (M * W)) z =
      matrixQuadraticFormReal M (W *ᵥ z) := by
  unfold matrixQuadraticFormReal
  rw [← Matrix.mulVec_mulVec z
      (Matrix.conjTranspose W) (M * W)]
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_conjTranspose]
  rw [← Matrix.mulVec_mulVec z M W]
  simp

theorem tensor_mulVec_productVector
    (d : ℕ) (U V : CMatrix (Fin d))
    (x y : Fin d → ℂ) :
    tensor U V *ᵥ productVector d x y =
      productVector d (U *ᵥ x) (V *ᵥ y) := by
  funext ac
  change
    (∑ be : Fin d × Fin d,
      (U ac.1 be.1 * V ac.2 be.2) *
        (x be.1 * y be.2)) =
      (∑ b : Fin d, U ac.1 b * x b) *
        ∑ e : Fin d, V ac.2 e * y e
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ b e : Fin d,
      U ac.1 b * V ac.2 e * (x b * y e) =
        (U ac.1 b * x b) * (V ac.2 e * y e) by
      intros
      ring]
  rw [Fintype.sum_mul_sum]

/-- The quartic objective of the conjugated matrix equals the original
objective evaluated on the locally rotated vectors. -/
theorem matrixQuarticForm_bipartiteUnitaryConjugate
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
    (x y : Fin d → ℂ) :
    matrixQuarticForm (bipartiteUnitaryConjugate d M UV) x y =
      matrixQuarticForm M
        (unitaryVectorAction d UV.1 x)
        (unitaryVectorAction d UV.2 y) := by
  rw [matrixQuarticForm_eq_productQuadratic,
    matrixQuarticForm_eq_productQuadratic]
  unfold bipartiteUnitaryConjugate unitaryVectorAction
  rw [matrixQuadraticFormReal_conjTranspose_mul,
    tensor_mulVec_productVector]
  rfl

theorem vectorNormSq_productVector
    (d : ℕ) (x y : Fin d → ℂ) :
    vectorNormSq (productVector d x y) =
      vectorNormSq x * vectorNormSq y := by
  unfold vectorNormSq productVector
  rw [Fintype.sum_prod_type]
  simp_rw [Complex.normSq_mul]
  exact
    (Fintype.sum_mul_sum
      (fun i : Fin d => Complex.normSq (x i))
      (fun j : Fin d => Complex.normSq (y j))).symm

/-- Hilbert--Schmidt Cauchy--Schwarz for a matrix quadratic form. -/
theorem abs_matrixQuadraticFormReal_le
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (M : CMatrix κ) (z : κ → ℂ) :
    |matrixQuadraticFormReal M z| ≤
      frobeniusNorm M * vectorNormSq z := by
  let f : κ × κ → ℝ := fun ij => ‖M ij.1 ij.2‖
  let g : κ × κ → ℝ := fun ij => ‖z ij.1‖ * ‖z ij.2‖
  have htriangle :
      ‖star z ⬝ᵥ (M *ᵥ z)‖ ≤ ∑ ij : κ × κ, f ij * g ij := by
    unfold dotProduct Matrix.mulVec
    calc
      ‖∑ i, star (z i) * ∑ j, M i j * z j‖ ≤
          ∑ i, ‖star (z i) * ∑ j, M i j * z j‖ :=
        norm_sum_le (Finset.univ : Finset κ)
          (fun i : κ => star (z i) * ∑ j, M i j * z j)
      _ ≤ ∑ i, ∑ j, ‖star (z i) * (M i j * z j)‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_mul, norm_star]
        calc
          ‖z i‖ * ‖∑ j, M i j * z j‖ ≤
              ‖z i‖ * ∑ j, ‖M i j * z j‖ := by
            gcongr
            exact norm_sum_le (Finset.univ : Finset κ)
              (fun j : κ => M i j * z j)
          _ = ∑ j, ‖star (z i) * (M i j * z j)‖ := by
            simp_rw [norm_mul, norm_star, Finset.mul_sum]
      _ = ∑ ij : κ × κ, f ij * g ij := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp [f, g, norm_mul]
        ring
  have hcs :
      (∑ ij : κ × κ, f ij * g ij) ≤
        Real.sqrt (∑ ij : κ × κ, f ij ^ 2) *
          Real.sqrt (∑ ij : κ × κ, g ij ^ 2) := by
    simpa using
      (Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ : Finset (κ × κ)) f g)
  have hf :
      Real.sqrt (∑ ij : κ × κ, f ij ^ 2) =
        frobeniusNorm M := by
    unfold frobeniusNorm frobeniusSq f
    rw [Fintype.sum_prod_type]
    simp only [Complex.normSq_eq_norm_sq]
  have hg :
      Real.sqrt (∑ ij : κ × κ, g ij ^ 2) =
        vectorNormSq z := by
    unfold g vectorNormSq
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow]
    rw [← Fintype.sum_mul_sum]
    simp only [Complex.normSq_eq_norm_sq]
    have hz0 : 0 ≤ ∑ i : κ, ‖z i‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [← pow_two, Real.sqrt_sq hz0]
  unfold matrixQuadraticFormReal
  calc
    |(star z ⬝ᵥ (M *ᵥ z)).re| ≤
        ‖star z ⬝ᵥ (M *ᵥ z)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ∑ ij : κ × κ, f ij * g ij := htriangle
    _ ≤ Real.sqrt (∑ ij : κ × κ, f ij ^ 2) *
        Real.sqrt (∑ ij : κ × κ, g ij ^ 2) := hcs
    _ = frobeniusNorm M * vectorNormSq z := by rw [hf, hg]

/-- A Frobenius-small tail changes every normalized product objective by at
most its Frobenius norm. -/
theorem abs_matrixQuarticForm_le_frobeniusNorm
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d)) (x y : Fin d → ℂ)
    (hx : vectorNormSq x = d) (hy : vectorNormSq y = d) :
    |matrixQuarticForm M x y| ≤ frobeniusNorm M := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  rw [matrixQuarticForm_eq_productQuadratic, abs_div]
  have hquad :=
    abs_matrixQuadraticFormReal_le M (productVector d x y)
  rw [vectorNormSq_productVector, hx, hy] at hquad
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [abs_of_pos (sq_pos_of_pos hdR)]
  apply (div_le_iff₀ (sq_pos_of_pos hdR)).mpr
  nlinarith

end

end QuantumSep
