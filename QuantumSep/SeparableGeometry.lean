import QuantumSep.ProductOptimizationAlgorithm
import QuantumSep.FrankWolfe
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Separable states in the Frobenius Hilbert space

Bipartite matrices are embedded isometrically into a finite Euclidean space.
The separable set is the real convex hull of normalized product projectors.
-/

namespace QuantumSep

open scoped BigOperators RealInnerProductSpace

noncomputable section

abbrev MatrixHilbert (d : ℕ) :=
  EuclideanSpace ℂ
    ((Fin d × Fin d) × (Fin d × Fin d))

def matrixHilbertOf
    (d : ℕ) (M : BipartiteMatrix (Fin d)) :
    MatrixHilbert d :=
  WithLp.toLp 2 (fun ij => M ij.1 ij.2)

def matrixOfHilbert
    (d : ℕ) (A : MatrixHilbert d) :
    BipartiteMatrix (Fin d) :=
  fun i j => A.ofLp (i, j)

@[simp] theorem matrixHilbertOf_apply
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (i j : Fin d × Fin d) :
    (matrixHilbertOf d M).ofLp (i, j) = M i j :=
  rfl

@[simp] theorem matrixOfHilbert_apply
    (d : ℕ) (A : MatrixHilbert d)
    (i j : Fin d × Fin d) :
    matrixOfHilbert d A i j = A.ofLp (i, j) :=
  rfl

@[simp] theorem matrixOfHilbert_matrixHilbertOf
    (d : ℕ) (M : BipartiteMatrix (Fin d)) :
    matrixOfHilbert d (matrixHilbertOf d M) = M := by
  rfl

@[simp] theorem matrixHilbertOf_matrixOfHilbert
    (d : ℕ) (A : MatrixHilbert d) :
    matrixHilbertOf d (matrixOfHilbert d A) = A := by
  exact WithLp.toLp_ofLp 2 A

@[simp] theorem matrixHilbertOf_zero (d : ℕ) :
    matrixHilbertOf d (0 : BipartiteMatrix (Fin d)) = 0 := by
  apply WithLp.ofLp_injective 2
  rfl

@[simp] theorem matrixHilbertOf_add
    (d : ℕ) (A B : BipartiteMatrix (Fin d)) :
    matrixHilbertOf d (A + B) =
      matrixHilbertOf d A + matrixHilbertOf d B := by
  apply WithLp.ofLp_injective 2
  rfl

@[simp] theorem matrixHilbertOf_sub
    (d : ℕ) (A B : BipartiteMatrix (Fin d)) :
    matrixHilbertOf d (A - B) =
      matrixHilbertOf d A - matrixHilbertOf d B := by
  apply WithLp.ofLp_injective 2
  rfl

@[simp] theorem matrixHilbertOf_real_smul
    (d : ℕ) (r : ℝ) (A : BipartiteMatrix (Fin d)) :
    matrixHilbertOf d ((r : ℂ) • A) =
      r • matrixHilbertOf d A := by
  apply WithLp.ofLp_injective 2
  rfl

@[simp] theorem matrixOfHilbert_add
    (d : ℕ) (A B : MatrixHilbert d) :
    matrixOfHilbert d (A + B) =
      matrixOfHilbert d A + matrixOfHilbert d B := by
  rfl

@[simp] theorem matrixOfHilbert_sub
    (d : ℕ) (A B : MatrixHilbert d) :
    matrixOfHilbert d (A - B) =
      matrixOfHilbert d A - matrixOfHilbert d B := by
  rfl

@[simp] theorem matrixOfHilbert_real_smul
    (d : ℕ) (r : ℝ) (A : MatrixHilbert d) :
    matrixOfHilbert d (r • A) =
      (r : ℂ) • matrixOfHilbert d A := by
  rfl

theorem matrixHilbertOf_norm_sq
    (d : ℕ) (M : BipartiteMatrix (Fin d)) :
    ‖matrixHilbertOf d M‖ ^ 2 = frobeniusSq M := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold matrixHilbertOf frobeniusSq
  rw [Fintype.sum_prod_type]
  simp only [WithLp.ofLp_toLp, Complex.normSq_eq_norm_sq]

theorem matrixHilbertOf_norm
    (d : ℕ) (M : BipartiteMatrix (Fin d)) :
    ‖matrixHilbertOf d M‖ = frobeniusNorm M := by
  have hsquare := matrixHilbertOf_norm_sq d M
  have hroot :
      Real.sqrt (frobeniusSq M) ^ 2 = frobeniusSq M :=
    Real.sq_sqrt (frobeniusSq_nonneg M)
  unfold frobeniusNorm
  nlinarith [norm_nonneg (matrixHilbertOf d M),
    Real.sqrt_nonneg (frobeniusSq M)]

theorem matrixHilbertOf_real_inner
    (d : ℕ) (A B : BipartiteMatrix (Fin d)) :
    ⟪matrixHilbertOf d A, matrixHilbertOf d B⟫ =
      (hsInner A B).re := by
  rw [PiLp.inner_apply]
  simp_rw [real_inner_eq_re_inner ℂ]
  unfold matrixHilbertOf hsInner
  rw [Fintype.sum_prod_type]
  simp only [RCLike.inner_apply, starRingEnd_apply]
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (B i j * star (A i j)).re =
    (star (A i j) * B i j).re
  congr 1
  ring

/-- The normalized projector onto a scaled product vector. -/
def productDensityMatrix
    (d : ℕ) (x y : Fin d → ℂ) :
    BipartiteMatrix (Fin d) :=
  fun i j =>
    productVector d x y i * star (productVector d x y j) /
      (d : ℂ) ^ 2

theorem productDensityMatrix_isHermitian
    (d : ℕ) (x y : Fin d → ℂ) :
    (productDensityMatrix d x y).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  unfold productDensityMatrix
  simp only [Matrix.conjTranspose_apply]
  simp [div_eq_mul_inv, star_mul, star_inv₀, star_pow, star_natCast]
  ring

theorem productDensityMatrix_frobeniusSq
    (d : ℕ) (hd : 0 < d)
    (x y : Fin d → ℂ)
    (hx : vectorNormSq x = d)
    (hy : vectorNormSq y = d) :
    frobeniusSq (productDensityMatrix d x y) = 1 := by
  let z := productVector d x y
  have hz : vectorNormSq z = (d : ℝ) ^ 2 := by
    rw [vectorNormSq_productVector, hx, hy]
    ring
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  unfold frobeniusSq productDensityMatrix
  simp_rw [Complex.normSq_eq_norm_sq, norm_div, norm_mul, norm_star,
    norm_pow]
  simp only [Complex.norm_natCast]
  simp_rw [div_pow, mul_pow]
  simp_rw [div_eq_mul_inv]
  rw [show
      (∑ i : Fin d × Fin d, ∑ j : Fin d × Fin d,
        ‖productVector d x y i‖ ^ 2 *
          ‖productVector d x y j‖ ^ 2 *
          (((d : ℝ) ^ 2) ^ 2)⁻¹) =
      (∑ i : Fin d × Fin d, ∑ j : Fin d × Fin d,
        ‖productVector d x y i‖ ^ 2 *
          ‖productVector d x y j‖ ^ 2) *
          (((d : ℝ) ^ 2) ^ 2)⁻¹ by
    symm
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]]
  field_simp [hdR]
  rw [← Fintype.sum_mul_sum]
  unfold vectorNormSq at hz
  simp only [Complex.normSq_eq_norm_sq] at hz
  rw [hz]
  ring

theorem productDensityMatrix_frobeniusNorm
    (d : ℕ) (hd : 0 < d)
    (x y : Fin d → ℂ)
    (hx : vectorNormSq x = d)
    (hy : vectorNormSq y = d) :
    frobeniusNorm (productDensityMatrix d x y) = 1 := by
  unfold frobeniusNorm
  rw [productDensityMatrix_frobeniusSq d hd x y hx hy]
  norm_num

/-- Pairing a Hermitian observable with a normalized product projector is
exactly the scaled product-vector objective used by the optimizer. -/
theorem real_inner_productDensityMatrix_eq_matrixQuarticForm
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d)) (hM : M.IsHermitian)
    (x y : Fin d → ℂ) :
    ⟪matrixHilbertOf d M,
        matrixHilbertOf d (productDensityMatrix d x y)⟫ =
      matrixQuarticForm M x y := by
  let z := productVector d x y
  have hdC : (d : ℂ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hd
  have hsum :
      hsInner M (productDensityMatrix d x y) =
        dotProduct (star z) (Matrix.mulVec M z) / (d : ℂ) ^ 2 := by
    change
      (∑ i : Fin d × Fin d, ∑ j : Fin d × Fin d,
        star (M i j) *
          (productVector d x y i *
            star (productVector d x y j) / (d : ℂ) ^ 2)) =
      (∑ i : Fin d × Fin d,
        star (productVector d x y i) *
          ∑ j : Fin d × Fin d,
            M i j * productVector d x y j) / (d : ℂ) ^ 2
    simp_rw [Finset.mul_sum]
    rw [show
        (∑ i : Fin d × Fin d, ∑ j : Fin d × Fin d,
          star (M i j) *
            (productVector d x y i *
              star (productVector d x y j) / (d : ℂ) ^ 2)) =
        (∑ i : Fin d × Fin d, ∑ j : Fin d × Fin d,
          star (productVector d x y i) *
            (M i j * productVector d x y j)) / (d : ℂ) ^ 2 by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [hM.apply j i]
      ring]
  rw [matrixHilbertOf_real_inner, hsum,
    matrixQuarticForm_eq_productQuadratic]
  unfold matrixQuadraticFormReal
  dsimp [z]
  rw [Complex.div_re]
  simp only [pow_two, Complex.mul_re, Complex.mul_im,
    Complex.natCast_re, Complex.natCast_im]
  norm_num
  field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hd]

/-- Pure normalized product states in Frobenius coordinates. -/
def pureProductStates (d : ℕ) : Set (MatrixHilbert d) :=
  {P | ∃ x y : Fin d → ℂ,
    vectorNormSq x = d ∧ vectorNormSq y = d ∧
      P = matrixHilbertOf d (productDensityMatrix d x y)}

/-- The separable state set is, by definition, the real convex hull of pure
product projectors. -/
def separableStates (d : ℕ) : Set (MatrixHilbert d) :=
  convexHull ℝ (pureProductStates d)

/-- The real subspace of Hermitian matrices, viewed inside Frobenius
coordinates. -/
def hermitianMatrices (d : ℕ) : Set (MatrixHilbert d) :=
  {A | (matrixOfHilbert d A).IsHermitian}

theorem convex_hermitianMatrices (d : ℕ) :
    Convex ℝ (hermitianMatrices d) := by
  intro A hA B hB a b _ha _hb _hab
  change
    (matrixOfHilbert d (a • A + b • B)).IsHermitian
  rw [matrixOfHilbert_add, matrixOfHilbert_real_smul,
    matrixOfHilbert_real_smul]
  change
    (a • matrixOfHilbert d A +
      b • matrixOfHilbert d B).IsHermitian
  exact (hA.smul (IsSelfAdjoint.all a)).add
    (hB.smul (IsSelfAdjoint.all b))

theorem hermitianMatrices_sub
    (d : ℕ) {A B : MatrixHilbert d}
    (hA : A ∈ hermitianMatrices d)
    (hB : B ∈ hermitianMatrices d) :
    A - B ∈ hermitianMatrices d := by
  change (matrixOfHilbert d (A - B)).IsHermitian
  rw [matrixOfHilbert_sub]
  exact hA.sub hB

theorem hermitianMatrices_real_smul
    (d : ℕ) (r : ℝ) {A : MatrixHilbert d}
    (hA : A ∈ hermitianMatrices d) :
    r • A ∈ hermitianMatrices d := by
  change (matrixOfHilbert d (r • A)).IsHermitian
  rw [matrixOfHilbert_real_smul]
  change (r • matrixOfHilbert d A).IsHermitian
  exact hA.smul (IsSelfAdjoint.all r)

theorem pureProductStates_hermitian
    (d : ℕ) :
    pureProductStates d ⊆ hermitianMatrices d := by
  intro P hP
  rcases hP with ⟨x, y, _hx, _hy, rfl⟩
  exact productDensityMatrix_isHermitian d x y

theorem separableStates_hermitian
    (d : ℕ) {P : MatrixHilbert d}
    (hP : P ∈ separableStates d) :
    (matrixOfHilbert d P).IsHermitian := by
  have hsub :
      separableStates d ⊆ hermitianMatrices d :=
    convexHull_min (pureProductStates_hermitian d)
      (convex_hermitianMatrices d)
  exact hsub hP

theorem convex_separableStates (d : ℕ) :
    Convex ℝ (separableStates d) :=
  convex_convexHull ℝ _

theorem pureProductStates_norm
    (d : ℕ) (hd : 0 < d)
    {P : MatrixHilbert d} (hP : P ∈ pureProductStates d) :
    ‖P‖ = 1 := by
  rcases hP with ⟨x, y, hx, hy, rfl⟩
  rw [matrixHilbertOf_norm,
    productDensityMatrix_frobeniusNorm d hd x y hx hy]

theorem separableStates_norm_le
    (d : ℕ) (hd : 0 < d)
    {P : MatrixHilbert d} (hP : P ∈ separableStates d) :
    ‖P‖ ≤ 1 := by
  have hpure :
      pureProductStates d ⊆ Metric.closedBall (0 : MatrixHilbert d) 1 := by
    intro Q hQ
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (pureProductStates_norm d hd hQ).le
  have hhull :
      separableStates d ⊆ Metric.closedBall (0 : MatrixHilbert d) 1 := by
    exact convexHull_min hpure (convex_closedBall 0 1)
  have := hhull hP
  simpa [Metric.mem_closedBall, dist_zero_right] using this

theorem pureProductState_mem_separable
    (d : ℕ) {P : MatrixHilbert d}
    (hP : P ∈ pureProductStates d) :
    P ∈ separableStates d :=
  subset_convexHull ℝ _ hP

/-- A real linear functional bounded on every pure product projector is
bounded by the same constant on their entire convex hull. -/
theorem inner_le_on_separable_of_pure
    (d : ℕ) (A : MatrixHilbert d) (c : ℝ)
    (hpure :
      ∀ P ∈ pureProductStates d, ⟪A, P⟫ ≤ c)
    {P : MatrixHilbert d} (hP : P ∈ separableStates d) :
    ⟪A, P⟫ ≤ c := by
  let H : Set (MatrixHilbert d) := {Q | ⟪A, Q⟫ ≤ c}
  have hconvex : Convex ℝ H := by
    intro X hX Y hY a b ha hb hab
    change
      ⟪A, a • X + b • Y⟫ ≤ c
    rw [inner_add_right, real_inner_smul_right,
      real_inner_smul_right]
    change a * ⟪A, X⟫ + b * ⟪A, Y⟫ ≤ c
    have hscaleX := mul_le_mul_of_nonneg_left hX ha
    have hscaleY := mul_le_mul_of_nonneg_left hY hb
    calc
      a * ⟪A, X⟫ + b * ⟪A, Y⟫ ≤ a * c + b * c :=
        add_le_add hscaleX hscaleY
      _ = c := by rw [← add_mul, hab, one_mul]
  have hsub : separableStates d ⊆ H :=
    convexHull_min (fun P hP => hpure P hP) hconvex
  exact hsub hP

/-- The optimizer's quartic guarantee is exactly a support-functional
guarantee over the separable convex hull. -/
theorem product_quartic_bound_extends_to_separable
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d)) (hM : M.IsHermitian)
    (x₀ y₀ : Fin d → ℂ)
    (hx₀ : vectorNormSq x₀ = d)
    (hy₀ : vectorNormSq y₀ = d)
    (tau : ℝ)
    (hopt :
      ∀ x y : Fin d → ℂ,
        vectorNormSq x = d →
        vectorNormSq y = d →
        matrixQuarticForm M x y ≤
          matrixQuarticForm M x₀ y₀ + tau)
    {P : MatrixHilbert d} (hP : P ∈ separableStates d) :
    ⟪matrixHilbertOf d M, P⟫ ≤
      ⟪matrixHilbertOf d M,
        matrixHilbertOf d (productDensityMatrix d x₀ y₀)⟫ + tau := by
  apply inner_le_on_separable_of_pure d
    (matrixHilbertOf d M)
    (⟪matrixHilbertOf d M,
      matrixHilbertOf d (productDensityMatrix d x₀ y₀)⟫ + tau)
    _ hP
  intro Q hQ
  rcases hQ with ⟨x, y, hx, hy, rfl⟩
  rw [real_inner_productDensityMatrix_eq_matrixQuarticForm d hd M hM,
    real_inner_productDensityMatrix_eq_matrixQuarticForm d hd M hM]
  exact hopt x y hx hy

end

end QuantumSep
