import QuantumSep.UnitaryObjective

/-!
# Deterministic comparison lemmas for the main reduction

This file supplies the estimates between a flat/tail decomposition and the
zero-partial-trace matrix sent to the dense-CSP reduction.
-/

namespace QuantumSep

open scoped BigOperators ComplexConjugate Matrix Matrix.Norms.Elementwise

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every entry is bounded by the finite matrix's entrywise supremum norm. -/
theorem norm_entry_le_entryNorm (A : CMatrix ι) (i j : ι) :
    ‖A i j‖ ≤ entryNorm A := by
  unfold entryNorm
  exact (Matrix.norm_le_iff (norm_nonneg A)).mp le_rfl i j

/-- Averaging a partial trace by the dimension does not increase the
entrywise norm. -/
theorem norm_invDim_mul_partialTrace0_le_entryNorm
    (A : BipartiteMatrix ι) (c e : ι) :
    ‖(dimC (ι := ι))⁻¹ * partialTrace0 A c e‖ ≤ entryNorm A := by
  have hd : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hsum :
      ‖partialTrace0 A c e‖ ≤
        (Fintype.card ι : ℝ) * entryNorm A := by
    unfold partialTrace0
    calc
      ‖∑ a : ι, A (a, c) (a, e)‖ ≤
          ∑ a : ι, ‖A (a, c) (a, e)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _a : ι, entryNorm A := by
        gcongr with a
        exact norm_entry_le_entryNorm A (a, c) (a, e)
      _ = (Fintype.card ι : ℝ) * entryNorm A := by
        simp [nsmul_eq_mul]
  simp only [norm_mul, norm_inv, dimC, Complex.norm_natCast]
  change ((Fintype.card ι : ℝ)⁻¹) *
      ‖partialTrace0 A c e‖ ≤ entryNorm A
  calc
    (Fintype.card ι : ℝ)⁻¹ * ‖partialTrace0 A c e‖ ≤
        (Fintype.card ι : ℝ)⁻¹ *
          ((Fintype.card ι : ℝ) * entryNorm A) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = entryNorm A := by field_simp [ne_of_gt hd]

theorem norm_invDim_mul_partialTrace1_le_entryNorm
    (A : BipartiteMatrix ι) (a b : ι) :
    ‖(dimC (ι := ι))⁻¹ * partialTrace1 A a b‖ ≤ entryNorm A := by
  have hd : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hsum :
      ‖partialTrace1 A a b‖ ≤
        (Fintype.card ι : ℝ) * entryNorm A := by
    unfold partialTrace1
    calc
      ‖∑ c : ι, A (a, c) (b, c)‖ ≤
          ∑ c : ι, ‖A (a, c) (b, c)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _c : ι, entryNorm A := by
        gcongr with c
        exact norm_entry_le_entryNorm A (a, c) (b, c)
      _ = (Fintype.card ι : ℝ) * entryNorm A := by
        simp [nsmul_eq_mul]
  simp only [norm_mul, norm_inv, dimC, Complex.norm_natCast]
  change ((Fintype.card ι : ℝ)⁻¹) *
      ‖partialTrace1 A a b‖ ≤ entryNorm A
  calc
    (Fintype.card ι : ℝ)⁻¹ * ‖partialTrace1 A a b‖ ≤
        (Fintype.card ι : ℝ)⁻¹ *
          ((Fintype.card ι : ℝ) * entryNorm A) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = entryNorm A := by field_simp [ne_of_gt hd]

/-- The normalized full trace is an average of diagonal entries. -/
theorem norm_scalarPart_le_entryNorm
    (A : BipartiteMatrix ι) :
    ‖scalarPart A‖ ≤ entryNorm A := by
  have hd : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have htrace :
      ‖A.trace‖ ≤
        (Fintype.card ι : ℝ) ^ 2 * entryNorm A := by
    unfold Matrix.trace
    calc
      ‖∑ i : ι × ι, Matrix.diag A i‖ ≤
          ∑ i : ι × ι, ‖Matrix.diag A i‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i : ι × ι, entryNorm A := by
        gcongr with i
        exact norm_entry_le_entryNorm A i i
      _ = (Fintype.card ι : ℝ) ^ 2 * entryNorm A := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_prod, Nat.cast_mul]
        ring
  unfold scalarPart dimC
  simp only [norm_div, norm_mul, Complex.norm_natCast]
  change ‖A.trace‖ /
      ((Fintype.card ι : ℝ) * Fintype.card ι) ≤ entryNorm A
  apply (div_le_iff₀ (mul_pos hd hd)).2
  calc
    ‖A.trace‖ ≤
        (Fintype.card ι : ℝ) ^ 2 * entryNorm A := htrace
    _ = entryNorm A *
        ((Fintype.card ι : ℝ) * Fintype.card ι) := by ring

/-- Entrywise formula for the zero-partial-trace projection. -/
theorem correlationPart_apply
    (A : BipartiteMatrix ι) (a b c e : ι) :
    correlationPart A (a, c) (b, e) =
      A (a, c) (b, e) -
        ((dimC (ι := ι))⁻¹ * partialTrace1 A a b) *
          (1 : CMatrix ι) c e -
        (1 : CMatrix ι) a b *
          ((dimC (ι := ι))⁻¹ * partialTrace0 A c e) +
        scalarPart A *
          ((1 : CMatrix ι) a b * (1 : CMatrix ι) c e) := by
  unfold correlationPart localA localB tensor
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- The correlation projection multiplies the entrywise norm by at most four.
This is the constant used in the manuscript's alphabet-size estimate. -/
theorem correlationPart_entryNorm_le
    (A : BipartiteMatrix ι) :
    entryNorm (correlationPart A) ≤ 4 * entryNorm A := by
  unfold entryNorm
  rw [Matrix.norm_le_iff (mul_nonneg (by norm_num) (norm_nonneg A))]
  intro ac be
  rcases ac with ⟨a, c⟩
  rcases be with ⟨b, e⟩
  rw [correlationPart_apply]
  have hOneAB : ‖(1 : CMatrix ι) a b‖ ≤ 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hOneCE : ‖(1 : CMatrix ι) c e‖ ≤ 1 := by
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hA := norm_entry_le_entryNorm A (a, c) (b, e)
  have hP1 := norm_invDim_mul_partialTrace1_le_entryNorm A a b
  have hP0 := norm_invDim_mul_partialTrace0_le_entryNorm A c e
  have hS := norm_scalarPart_le_entryNorm A
  have hEntryNonneg : 0 ≤ entryNorm A := norm_nonneg A
  have hTermP1 :
      ‖((dimC (ι := ι))⁻¹ * partialTrace1 A a b) *
          (1 : CMatrix ι) c e‖ ≤ entryNorm A := by
    rw [norm_mul]
    calc
      ‖(dimC (ι := ι))⁻¹ * partialTrace1 A a b‖ *
          ‖(1 : CMatrix ι) c e‖ ≤ entryNorm A * 1 :=
        mul_le_mul hP1 hOneCE (norm_nonneg _) hEntryNonneg
      _ = entryNorm A := mul_one _
  have hTermP0 :
      ‖(1 : CMatrix ι) a b *
          ((dimC (ι := ι))⁻¹ * partialTrace0 A c e)‖ ≤
        entryNorm A := by
    rw [norm_mul]
    calc
      ‖(1 : CMatrix ι) a b‖ *
          ‖(dimC (ι := ι))⁻¹ * partialTrace0 A c e‖ ≤
        1 * entryNorm A :=
          mul_le_mul hOneAB hP0 (norm_nonneg _) (by norm_num)
      _ = entryNorm A := one_mul _
  have hOneProd :
      ‖(1 : CMatrix ι) a b * (1 : CMatrix ι) c e‖ ≤ 1 := by
    rw [norm_mul]
    calc
      ‖(1 : CMatrix ι) a b‖ * ‖(1 : CMatrix ι) c e‖ ≤ 1 * 1 :=
        mul_le_mul hOneAB hOneCE (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hTermS :
      ‖scalarPart A *
          ((1 : CMatrix ι) a b * (1 : CMatrix ι) c e)‖ ≤
        entryNorm A := by
    rw [norm_mul]
    calc
      ‖scalarPart A‖ *
          ‖(1 : CMatrix ι) a b * (1 : CMatrix ι) c e‖ ≤
        entryNorm A * 1 :=
          mul_le_mul hS hOneProd (norm_nonneg _) hEntryNonneg
      _ = entryNorm A := mul_one _
  calc
    ‖A (a, c) (b, e) -
        ((dimC (ι := ι))⁻¹ * partialTrace1 A a b) *
          (1 : CMatrix ι) c e -
        (1 : CMatrix ι) a b *
          ((dimC (ι := ι))⁻¹ * partialTrace0 A c e) +
        scalarPart A *
          ((1 : CMatrix ι) a b * (1 : CMatrix ι) c e)‖ ≤
      ‖A (a, c) (b, e)‖ +
        ‖((dimC (ι := ι))⁻¹ * partialTrace1 A a b) *
          (1 : CMatrix ι) c e‖ +
        ‖(1 : CMatrix ι) a b *
          ((dimC (ι := ι))⁻¹ * partialTrace0 A c e)‖ +
        ‖scalarPart A *
          ((1 : CMatrix ι) a b * (1 : CMatrix ι) c e)‖ := by
      calc
        ‖_ - _ - _ + _‖ ≤ ‖_ - _ - _‖ + ‖_‖ := norm_add_le _ _
        _ ≤ (‖_ - _‖ + ‖_‖) + ‖_‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ((‖_‖ + ‖_‖) + ‖_‖) + ‖_‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = _ := by ring
    _ ≤ entryNorm A + entryNorm A + entryNorm A + entryNorm A := by
      gcongr
    _ = 4 * entryNorm A := by ring

/-- The zero-partial-trace projection is contractive in Frobenius norm. -/
theorem correlationPart_frobeniusNorm_le
    (A : BipartiteMatrix ι) :
    frobeniusNorm (correlationPart A) ≤ frobeniusNorm A := by
  unfold frobeniusNorm
  exact Real.sqrt_le_sqrt (correlationPart_frobeniusSq_le A)

/-- Orthogonality of the rows of a unitary matrix. -/
theorem unitary_row_orthogonality
    {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (i j : Fin d) :
    (∑ a : Fin d,
      star ((U : CMatrix (Fin d)) i a) *
        (U : CMatrix (Fin d)) j a) =
      if i = j then 1 else 0 := by
  have hUU :
      (U : CMatrix (Fin d)) * Matrix.conjTranspose U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp U.property
  have hentry := congrFun (congrFun hUU j) i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply] at hentry
  by_cases hij : i = j
  · subst j
    simpa [mul_comm] using hentry
  · have hji : j ≠ i := Ne.symm hij
    simpa [hij, hji, mul_comm] using hentry

/-- Conjugating by local unitaries preserves a zero partial trace over the
first subsystem. -/
theorem partialTrace0_bipartiteUnitaryConjugate_eq_zero
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero : partialTrace0 M = 0)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    partialTrace0 (bipartiteUnitaryConjugate d M UV) = 0 := by
  ext c e
  change
    (∑ a : Fin d,
      bipartiteUnitaryConjugate d M UV (a, c) (a, e)) = 0
  simp_rw [← bipartiteHaarEntry_eq_unitaryConjugate_apply]
  unfold bipartiteHaarEntry unitaryColumn
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [show
      (∑ a : Fin d, ∑ r : Fin d, ∑ s : Fin d,
        ∑ i : Fin d, ∑ j : Fin d,
          star ((UV.2 : CMatrix (Fin d)) r c) *
            (star ((UV.1 : CMatrix (Fin d)) i a) *
              M (i, r) (j, s) *
              (UV.1 : CMatrix (Fin d)) j a) *
            (UV.2 : CMatrix (Fin d)) s e) =
      ∑ r : Fin d, ∑ s : Fin d, ∑ i : Fin d, ∑ j : Fin d,
        star ((UV.2 : CMatrix (Fin d)) r c) *
          (M (i, r) (j, s) *
            (∑ a : Fin d,
              star ((UV.1 : CMatrix (Fin d)) i a) *
                (UV.1 : CMatrix (Fin d)) j a)) *
          (UV.2 : CMatrix (Fin d)) s e by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro a _
    ring]
  simp_rw [unitary_row_orthogonality]
  simp only [ite_mul, mul_ite, mul_one, mul_zero]
  simp only [zero_mul]
  rw [show
      (∑ r : Fin d, ∑ s : Fin d, ∑ i : Fin d, ∑ j : Fin d,
        if i = j then
          star ((UV.2 : CMatrix (Fin d)) r c) *
            M (i, r) (j, s) *
            (UV.2 : CMatrix (Fin d)) s e
        else 0) =
      ∑ r : Fin d, ∑ s : Fin d, ∑ i : Fin d,
        star ((UV.2 : CMatrix (Fin d)) r c) *
          M (i, r) (i, s) *
          (UV.2 : CMatrix (Fin d)) s e by
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp]
  have hz (r s : Fin d) :
      (∑ i : Fin d, M (i, r) (i, s)) = 0 := by
    simpa [partialTrace0] using
      congrFun (congrFun hzero r) s
  calc
    (∑ r : Fin d, ∑ s : Fin d, ∑ i : Fin d,
      star ((UV.2 : CMatrix (Fin d)) r c) *
        M (i, r) (i, s) *
        (UV.2 : CMatrix (Fin d)) s e) =
      ∑ r : Fin d, ∑ s : Fin d,
        star ((UV.2 : CMatrix (Fin d)) r c) *
          (∑ i : Fin d, M (i, r) (i, s)) *
          (UV.2 : CMatrix (Fin d)) s e := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
    _ = 0 := by simp [hz]

/-- Conjugating by local unitaries preserves a zero partial trace over the
second subsystem. -/
theorem partialTrace1_bipartiteUnitaryConjugate_eq_zero
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero : partialTrace1 M = 0)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    partialTrace1 (bipartiteUnitaryConjugate d M UV) = 0 := by
  ext a b
  change
    (∑ c : Fin d,
      bipartiteUnitaryConjugate d M UV (a, c) (b, c)) = 0
  simp_rw [← bipartiteHaarEntry_eq_unitaryConjugate_apply]
  unfold bipartiteHaarEntry unitaryColumn
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [show
      (∑ c : Fin d, ∑ r : Fin d, ∑ s : Fin d,
        ∑ i : Fin d, ∑ j : Fin d,
          star ((UV.2 : CMatrix (Fin d)) r c) *
            (star ((UV.1 : CMatrix (Fin d)) i a) *
              M (i, r) (j, s) *
              (UV.1 : CMatrix (Fin d)) j b) *
            (UV.2 : CMatrix (Fin d)) s c) =
      ∑ r : Fin d, ∑ s : Fin d, ∑ i : Fin d, ∑ j : Fin d,
        star ((UV.1 : CMatrix (Fin d)) i a) *
          (M (i, r) (j, s) *
            (∑ c : Fin d,
              star ((UV.2 : CMatrix (Fin d)) r c) *
                (UV.2 : CMatrix (Fin d)) s c)) *
          (UV.1 : CMatrix (Fin d)) j b by
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro c _
    ring]
  simp_rw [unitary_row_orthogonality]
  simp only [ite_mul, mul_ite, mul_one, mul_zero]
  simp only [zero_mul]
  rw [show
      (∑ r : Fin d, ∑ s : Fin d, ∑ i : Fin d, ∑ j : Fin d,
        if r = s then
          star ((UV.1 : CMatrix (Fin d)) i a) *
            M (i, r) (j, s) *
            (UV.1 : CMatrix (Fin d)) j b
        else 0) =
      ∑ r : Fin d, ∑ i : Fin d, ∑ j : Fin d,
        star ((UV.1 : CMatrix (Fin d)) i a) *
          M (i, r) (j, r) *
          (UV.1 : CMatrix (Fin d)) j b by
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_eq_single r]
    · simp
    · intro s _ hsr
      simp [Ne.symm hsr]
    · simp
  ]
  rw [show
      (∑ r : Fin d, ∑ i : Fin d, ∑ j : Fin d,
        star ((UV.1 : CMatrix (Fin d)) i a) *
          M (i, r) (j, r) *
          (UV.1 : CMatrix (Fin d)) j b) =
      ∑ i : Fin d, ∑ j : Fin d, ∑ r : Fin d,
        star ((UV.1 : CMatrix (Fin d)) i a) *
          M (i, r) (j, r) *
          (UV.1 : CMatrix (Fin d)) j b by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]]
  have hz (i j : Fin d) :
      (∑ r : Fin d, M (i, r) (j, r)) = 0 := by
    simpa [partialTrace1] using
      congrFun (congrFun hzero i) j
  calc
    (∑ i : Fin d, ∑ j : Fin d, ∑ r : Fin d,
      star ((UV.1 : CMatrix (Fin d)) i a) *
        M (i, r) (j, r) *
        (UV.1 : CMatrix (Fin d)) j b) =
      ∑ i : Fin d, ∑ j : Fin d,
        star ((UV.1 : CMatrix (Fin d)) i a) *
          (∑ r : Fin d, M (i, r) (j, r)) *
          (UV.1 : CMatrix (Fin d)) j b := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
    _ = 0 := by simp [hz]

/-- Frobenius square factorizes over tensor products. -/
theorem frobeniusSq_tensor
    (A B : CMatrix ι) :
    frobeniusSq (tensor A B) =
      frobeniusSq A * frobeniusSq B := by
  apply Complex.ofReal_injective
  rw [← hsInner_self, hsInner_tensor, hsInner_self, hsInner_self]
  norm_cast

@[simp] theorem frobeniusSq_one :
    frobeniusSq (1 : CMatrix ι) = Fintype.card ι := by
  unfold frobeniusSq
  simp [Matrix.one_apply, Complex.normSq_apply]

/-- The complex quadratic form of a tensor matrix on a product vector
factorizes. -/
theorem productVector_dot_tensor_mulVec
    (d : ℕ) (A B : CMatrix (Fin d))
    (x y : Fin d → ℂ) :
    star (productVector d x y) ⬝ᵥ
        (tensor A B *ᵥ productVector d x y) =
      (star x ⬝ᵥ (A *ᵥ x)) *
        (star y ⬝ᵥ (B *ᵥ y)) := by
  rw [tensor_mulVec_productVector]
  unfold dotProduct productVector
  rw [Fintype.sum_prod_type]
  simp only [Pi.star_apply, star_mul]
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem star_dot_self_eq_vectorNormSq
    (x : ι → ℂ) :
    star x ⬝ᵥ x = (vectorNormSq x : ℂ) := by
  unfold dotProduct vectorNormSq
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.star_apply, Complex.star_def,
    Complex.normSq_eq_conj_mul_self]

/-- A local term on the first subsystem only contributes its normalized
one-party quadratic form. -/
theorem matrixQuarticForm_tensor_one
    (d : ℕ) [Nonempty (Fin d)] (A : CMatrix (Fin d))
    (x y : Fin d → ℂ) :
    matrixQuarticForm (tensor A (1 : CMatrix (Fin d))) x y =
      matrixQuadraticFormReal A x * vectorNormSq y / (d : ℝ) ^ 2 := by
  rw [matrixQuarticForm_eq_productQuadratic]
  unfold matrixQuadraticFormReal
  rw [productVector_dot_tensor_mulVec]
  rw [Matrix.one_mulVec, star_dot_self_eq_vectorNormSq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

/-- The analogous formula for a local term on the second subsystem. -/
theorem matrixQuarticForm_one_tensor
    (d : ℕ) [Nonempty (Fin d)] (B : CMatrix (Fin d))
    (x y : Fin d → ℂ) :
    matrixQuarticForm (tensor (1 : CMatrix (Fin d)) B) x y =
      vectorNormSq x * matrixQuadraticFormReal B y / (d : ℝ) ^ 2 := by
  rw [matrixQuarticForm_eq_productQuadratic]
  unfold matrixQuadraticFormReal
  rw [productVector_dot_tensor_mulVec]
  rw [Matrix.one_mulVec, star_dot_self_eq_vectorNormSq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

/-- Under a unit Frobenius bound on the bipartite matrix, the sum of the two
local product-objective contributions is at most `2 / sqrt d` in absolute
value. -/
theorem abs_localTerms_quartic_le
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (hMnorm : frobeniusNorm M ≤ 1)
    (x y : Fin d → ℂ)
    (hx : vectorNormSq x = d)
    (hy : vectorNormSq y = d) :
    |matrixQuarticForm
        (tensor (localA M) (1 : CMatrix (Fin d)) +
          tensor (1 : CMatrix (Fin d)) (localB M)) x y| ≤
      2 / Real.sqrt d := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hMsq : frobeniusSq M ≤ 1 := by
    have hsqrtSq :
        frobeniusNorm M ^ 2 = frobeniusSq M := by
      unfold frobeniusNorm
      rw [Real.sq_sqrt (frobeniusSq_nonneg M)]
    have hnorm0 : 0 ≤ frobeniusNorm M := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (frobeniusNorm M)]
  have hp := localDecomposition_frobenius_pythagoras M
  have hAprod :
      (d : ℝ) * frobeniusSq (localA M) ≤ 1 := by
    simp only [frobeniusSq_tensor, frobeniusSq_one,
      Fintype.card_fin] at hp
    have hscalar := frobeniusSq_nonneg
      (scalarPart M •
        tensor (1 : CMatrix (Fin d)) (1 : CMatrix (Fin d)))
    have hB :
        0 ≤ (d : ℝ) * frobeniusSq (localB M) :=
      mul_nonneg (Nat.cast_nonneg d)
        (frobeniusSq_nonneg (localB M))
    have hC := frobeniusSq_nonneg (correlationPart M)
    nlinarith
  have hBprod :
      (d : ℝ) * frobeniusSq (localB M) ≤ 1 := by
    simp only [frobeniusSq_tensor, frobeniusSq_one,
      Fintype.card_fin] at hp
    have hscalar := frobeniusSq_nonneg
      (scalarPart M •
        tensor (1 : CMatrix (Fin d)) (1 : CMatrix (Fin d)))
    have hA :
        0 ≤ frobeniusSq (localA M) * (d : ℝ) :=
      mul_nonneg (frobeniusSq_nonneg (localA M))
        (Nat.cast_nonneg d)
    have hC := frobeniusSq_nonneg (correlationPart M)
    nlinarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrtd : 0 < Real.sqrt (d : ℝ) :=
    Real.sqrt_pos.2 hdR
  have hAnorm : frobeniusNorm (localA M) ≤ 1 / Real.sqrt d := by
    apply (le_div_iff₀ hsqrtd).2
    have hsqrt := Real.sqrt_le_sqrt hAprod
    rw [Real.sqrt_mul (Nat.cast_nonneg d),
      Real.sqrt_one] at hsqrt
    simpa [frobeniusNorm, mul_comm] using hsqrt
  have hBnorm : frobeniusNorm (localB M) ≤ 1 / Real.sqrt d := by
    apply (le_div_iff₀ hsqrtd).2
    have hsqrt := Real.sqrt_le_sqrt hBprod
    rw [Real.sqrt_mul (Nat.cast_nonneg d),
      Real.sqrt_one] at hsqrt
    simpa [frobeniusNorm, mul_comm] using hsqrt
  have hQA :
      |matrixQuarticForm
        (tensor (localA M) (1 : CMatrix (Fin d))) x y| ≤
          frobeniusNorm (localA M) := by
    rw [matrixQuarticForm_tensor_one, hy]
    have hquad := abs_matrixQuadraticFormReal_le (localA M) x
    rw [hx] at hquad
    have hdR0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
    rw [show
      matrixQuadraticFormReal (localA M) x * (d : ℝ) /
          (d : ℝ) ^ 2 =
        matrixQuadraticFormReal (localA M) x / (d : ℝ) by
      field_simp [hdR0]]
    rw [abs_div, abs_of_pos hdR]
    exact (div_le_iff₀ hdR).2 (by simpa [mul_comm] using hquad)
  have hQB :
      |matrixQuarticForm
        (tensor (1 : CMatrix (Fin d)) (localB M)) x y| ≤
          frobeniusNorm (localB M) := by
    rw [matrixQuarticForm_one_tensor, hx]
    have hquad := abs_matrixQuadraticFormReal_le (localB M) y
    rw [hy] at hquad
    have hdR0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
    rw [show
      (d : ℝ) * matrixQuadraticFormReal (localB M) y /
          (d : ℝ) ^ 2 =
        matrixQuadraticFormReal (localB M) y / (d : ℝ) by
      field_simp [hdR0]]
    rw [abs_div, abs_of_pos hdR]
    exact (div_le_iff₀ hdR).2 (by simpa [mul_comm] using hquad)
  have hadd :
      matrixQuarticForm
        (tensor (localA M) (1 : CMatrix (Fin d)) +
          tensor (1 : CMatrix (Fin d)) (localB M)) x y =
        matrixQuarticForm
          (tensor (localA M) (1 : CMatrix (Fin d))) x y +
        matrixQuarticForm
          (tensor (1 : CMatrix (Fin d)) (localB M)) x y := by
    unfold matrixQuarticForm quarticSummand
    simp_rw [Matrix.add_apply, add_mul, Complex.add_re,
      Finset.sum_add_distrib]
    ring
  rw [hadd]
  calc
    |_ + _| ≤
        |matrixQuarticForm
          (tensor (localA M) (1 : CMatrix (Fin d))) x y| +
        |matrixQuarticForm
          (tensor (1 : CMatrix (Fin d)) (localB M)) x y| :=
      abs_add_le _ _
    _ ≤ frobeniusNorm (localA M) +
        frobeniusNorm (localB M) := add_le_add hQA hQB
    _ ≤ 1 / Real.sqrt d + 1 / Real.sqrt d :=
      add_le_add hAnorm hBnorm
    _ = 2 / Real.sqrt d := by ring

/-- The quartic objective is linear in its matrix argument. -/
theorem matrixQuarticForm_add
    (M N : BipartiteMatrix ι) (x y : ι → ℂ) :
    matrixQuarticForm (M + N) x y =
      matrixQuarticForm M x y + matrixQuarticForm N x y := by
  unfold matrixQuarticForm quarticSummand
  simp_rw [Matrix.add_apply, add_mul, Complex.add_re,
    Finset.sum_add_distrib]
  ring

theorem matrixQuarticForm_sub
    (M N : BipartiteMatrix ι) (x y : ι → ℂ) :
    matrixQuarticForm (M - N) x y =
      matrixQuarticForm M x y - matrixQuarticForm N x y := by
  unfold matrixQuarticForm quarticSummand
  simp_rw [Matrix.sub_apply, sub_mul, Complex.sub_re,
    Finset.sum_sub_distrib]
  ring

/-- The scalar summand of the local decomposition has the same value on
every normalized product vector. -/
theorem matrixQuarticForm_scalar_tensor_one
    (d : ℕ) (hd : 0 < d) (s : ℂ)
    (x y : Fin d → ℂ)
    (hx : vectorNormSq x = d)
    (hy : vectorNormSq y = d) :
    matrixQuarticForm
        (s • tensor (1 : CMatrix (Fin d)) (1 : CMatrix (Fin d))) x y =
      s.re := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  rw [matrixQuarticForm_eq_productQuadratic]
  unfold matrixQuadraticFormReal
  rw [Matrix.smul_mulVec, tensor_mulVec_productVector]
  simp only [Matrix.one_mulVec]
  rw [dotProduct_smul, star_dot_self_eq_vectorNormSq,
    vectorNormSq_productVector, hx, hy]
  simp [smul_eq_mul, Complex.mul_re, pow_two]
  field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hd]

/-- The local decomposition rewritten directly at the normalized product
objective level. -/
theorem matrixQuarticForm_localDecomposition
    (d : ℕ) (hd : 0 < d)
    (M : BipartiteMatrix (Fin d))
    (x y : Fin d → ℂ)
    (hx : vectorNormSq x = d)
    (hy : vectorNormSq y = d) :
    matrixQuarticForm M x y =
      (scalarPart M).re +
        matrixQuarticForm
          (tensor (localA M) (1 : CMatrix (Fin d)) +
            tensor (1 : CMatrix (Fin d)) (localB M)) x y +
        matrixQuarticForm (correlationPart M) x y := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  calc
    matrixQuarticForm M x y =
        matrixQuarticForm
          (scalarPart M •
              tensor (1 : CMatrix (Fin d)) (1 : CMatrix (Fin d)) +
            tensor (localA M) (1 : CMatrix (Fin d)) +
            tensor (1 : CMatrix (Fin d)) (localB M) +
            correlationPart M) x y := by
      rw [← localDecomposition_reconstruct M]
    _ = _ := by
      rw [matrixQuarticForm_add, matrixQuarticForm_add,
        matrixQuarticForm_add,
        matrixQuarticForm_scalar_tensor_one d hd _ x y hx hy,
        matrixQuarticForm_add]
      ring

/-- Projecting the flat piece changes a normalized product objective only by
the projected Haar tail. -/
theorem abs_total_sub_projectedFlat_quartic_le
    (d : ℕ) (hd : 0 < d)
    (total reference flat tail : BipartiteMatrix (Fin d))
    (γ δ : ℝ)
    (hdecomp :
      FlatTailDecomposition total reference flat tail
        γ δ)
    (hzero0 : partialTrace0 total = 0)
    (hzero1 : partialTrace1 total = 0)
    (x y : Fin d → ℂ)
    (hx : vectorNormSq x = d)
    (hy : vectorNormSq y = d) :
    |matrixQuarticForm total x y -
        matrixQuarticForm (correlationPart flat) x y| ≤
      δ * frobeniusNorm reference := by
  letI : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hsplit : total = flat + tail := hdecomp.1.symm
  have hmatrix :
      total - correlationPart flat = correlationPart tail :=
    sub_correlationPart_eq_correlationPart_tail
      total flat tail hsplit hzero0 hzero1
  rw [← matrixQuarticForm_sub, hmatrix]
  calc
    |matrixQuarticForm (correlationPart tail) x y| ≤
        frobeniusNorm (correlationPart tail) :=
      abs_matrixQuarticForm_le_frobeniusNorm
        d hd (correlationPart tail) x y hx hy
    _ ≤ frobeniusNorm tail :=
      correlationPart_frobeniusNorm_le tail
    _ ≤ δ * frobeniusNorm reference := hdecomp.2.2.2.2

end

end QuantumSep
