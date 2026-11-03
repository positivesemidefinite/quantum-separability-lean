import QuantumSep.HaarMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

namespace QuantumSep

noncomputable section

def quadraticFamilyVector
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (x : Fin d → ℂ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2
    (fun k => vectorQuadraticForm (tracelessPart (A k)) x)

theorem norm_quadraticFamilyVector
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (x : Fin d → ℂ) :
    ‖quadraticFamilyVector d A x‖ =
      sphereQuadraticFamilyNorm d A x := by
  have hs :
      ‖quadraticFamilyVector d A x‖ ^ 2 =
        ∑ k : κ,
          Complex.normSq
            (vectorQuadraticForm (tracelessPart (A k)) x) := by
    rw [EuclideanSpace.norm_sq_eq]
    unfold quadraticFamilyVector
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.normSq_eq_norm_sq]
  unfold sphereQuadraticFamilyNorm
  rw [← hs, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

theorem continuous_quadraticFamilyVector
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d)) :
    Continuous (quadraticFamilyVector d A) := by
  unfold quadraticFamilyVector
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  unfold vectorQuadraticForm
  fun_prop

theorem memLp_continuous_on_unitaryGroup
    {E : Type*} [NormedAddCommGroup E]
    [SecondCountableTopology E]
    (d : ℕ)
    (F : Matrix.unitaryGroup (Fin d) ℂ → E)
    (hF : Continuous F) (p : ℝ≥0∞) :
    MemLp F p (unitaryHaarMeasure d) := by
  let F' :
      C(Matrix.unitaryGroup (Fin d) ℂ, E) :=
    ⟨F, hF⟩
  apply MemLp.of_bound hF.aestronglyMeasurable ‖F'‖
  filter_upwards with U
  exact F'.norm_coe_le_norm U

def orbitQuadraticFamilyVector
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (w : Fin d → ℂ)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    EuclideanSpace ℂ κ :=
  quadraticFamilyVector d A (unitaryVectorAction d U w)

theorem continuous_orbitQuadraticFamilyVector
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (w : Fin d → ℂ) :
    Continuous (orbitQuadraticFamilyVector d A w) := by
  apply (continuous_quadraticFamilyVector d A).comp
  apply continuous_pi
  intro i
  unfold unitaryVectorAction
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · have hi :
        Continuous (fun U : CMatrix (Fin d) => U i) :=
      continuous_apply i
    have hij :
        Continuous (fun U : CMatrix (Fin d) => U i j) :=
      (continuous_apply j).comp hi
    exact hij.comp continuous_subtype_val
  · fun_prop

theorem continuous_unitaryOrbitVector
    (d : ℕ) (w : Fin d → ℂ) :
    Continuous
      (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
        unitaryVectorAction d U w) := by
  apply continuous_pi
  intro i
  unfold unitaryVectorAction
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · have hi :
        Continuous (fun U : CMatrix (Fin d) => U i) :=
      continuous_apply i
    have hij :
        Continuous (fun U : CMatrix (Fin d) => U i j) :=
      (continuous_apply j).comp hi
    exact hij.comp continuous_subtype_val
  · fun_prop

noncomputable def haarOrbitMeasure
    (d : ℕ) (w : Fin d → ℂ) :
    Measure (Fin d → ℂ) :=
  (unitaryHaarMeasure d).map
    (fun U => unitaryVectorAction d U w)

theorem haarOrbitMeasure_eq_haarColumnMeasure
    (d : ℕ) (a : Fin d) (w : Fin d → ℂ)
    (hw : vectorNormSq w = 1) :
    haarOrbitMeasure d w = haarColumnMeasure d a := by
  obtain ⟨W, hW⟩ :=
    exists_unitaryColumn_eq_of_vectorNormSq_eq_one
      d a w hw
  let R :=
    fun U : Matrix.unitaryGroup (Fin d) ℂ => U * W
  have hRmeas : Measurable R := by
    dsimp [R]
    fun_prop
  have hmap :
      (unitaryHaarMeasure d).map R =
        unitaryHaarMeasure d :=
    Measure.IsMulRightInvariant.map_mul_right_eq_self W
  have hfun :
      (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
        unitaryVectorAction d U w) =
      unitaryColumn d a ∘ R := by
    funext U
    change
      unitaryVectorAction d U w =
        unitaryColumn d a (U * W)
    rw [← hW, unitaryVectorAction_unitaryColumn]
  unfold haarOrbitMeasure haarColumnMeasure
  rw [hfun, ← Measure.map_map
    (measurable_unitaryColumn d a) hRmeas, hmap]

theorem onePartyHaar_rankOne_orbit_lpNorm_le
    (hc : GaussianHypercontractivityContract)
    {κ : Type} [Fintype κ]
    (d : ℕ) (a : Fin d)
    (A : κ → CMatrix (Fin d))
    (w : Fin d → ℂ) (hw : vectorNormSq w = 1)
    (q : ℕ) (hq : 0 < q) (hfour : 4 * q ≤ d) :
    lpNorm (orbitQuadraticFamilyVector d A w)
        (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤
      (2 * hc.constant * q / (d : ℝ)) *
        ((∑ k : κ, frobeniusSq (A k)) ^
          ((2 : ℝ)⁻¹)) := by
  have hcont :=
    continuous_orbitQuadraticFamilyVector d A w
  have hlp :
      lpNorm (orbitQuadraticFamilyVector d A w)
          (q : ℝ≥0∞) (unitaryHaarMeasure d) =
        ((∫ x : Fin d → ℂ,
            sphereQuadraticFamilyNorm d A x ^ q
            ∂haarColumnMeasure d a) ^
          (((q : ℝ))⁻¹)) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (by simp [hq.ne']) (by simp) hcont.aestronglyMeasurable]
    have htoReal :
        ENNReal.toReal (q : ℝ≥0∞) = (q : ℝ) := by
      simp
    rw [htoReal]
    unfold orbitQuadraticFamilyVector
    simp_rw [norm_quadraticFamilyVector]
    simp only [Real.rpow_natCast]
    congr 1
    have horbit :=
      haarOrbitMeasure_eq_haarColumnMeasure d a w hw
    calc
      (∫ U : Matrix.unitaryGroup (Fin d) ℂ,
          sphereQuadraticFamilyNorm d A
              (unitaryVectorAction d U w) ^ q
          ∂unitaryHaarMeasure d) =
          ∫ x : Fin d → ℂ,
            sphereQuadraticFamilyNorm d A x ^ q
            ∂haarOrbitMeasure d w := by
        unfold haarOrbitMeasure
        rw [integral_map
          (continuous_unitaryOrbitVector d w).measurable.aemeasurable
          (((measurable_sphereQuadraticFamilyNorm d A).pow_const q)
            |>.aestronglyMeasurable)]
      _ = ∫ x : Fin d → ℂ,
            sphereQuadraticFamilyNorm d A x ^ q
            ∂haarColumnMeasure d a := by
        rw [horbit]
  rw [hlp]
  exact onePartyHaar_rankOne_moment_le
    hc d a A q hq hfour

def standardBasisVector
    (d : ℕ) (a : Fin d) : Fin d → ℂ :=
  fun i => if i = a then 1 else 0

def polarizationBasisVector
    (d : ℕ) (a b : Fin d) (z : ℂ) :
    Fin d → ℂ :=
  fun i =>
    ((1 / Real.sqrt 2 : ℝ) : ℂ) *
      (standardBasisVector d a i +
        z * standardBasisVector d b i)

theorem vectorNormSq_polarizationBasisVector
    (d : ℕ) (a b : Fin d) (z : ℂ)
    (hab : a ≠ b) (hz : Complex.normSq z = 1) :
    vectorNormSq
      (polarizationBasisVector d a b z) = 1 := by
  classical
  let c : ℝ := 1 / Real.sqrt 2
  have hc : c * c = 1 / 2 := by
    dsimp [c]
    rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  have hpoint (i : Fin d) :
      polarizationBasisVector d a b z i =
        if i = a then (c : ℂ)
        else if i = b then (c : ℂ) * z
        else 0 := by
    unfold polarizationBasisVector standardBasisVector
    dsimp [c]
    by_cases hia : i = a
    · subst i
      simp [hab]
    · by_cases hib : i = b
      · subst i
        simp [hia, mul_comm]
      · simp [hia, hib]
  unfold vectorNormSq
  simp_rw [hpoint]
  have hnormpoint (i : Fin d) :
      Complex.normSq
          (if i = a then (c : ℂ)
          else if i = b then (c : ℂ) * z
          else 0) =
        if i = a then Complex.normSq (c : ℂ)
        else if i = b then Complex.normSq ((c : ℂ) * z)
        else 0 := by
    split_ifs <;> simp
  simp_rw [hnormpoint]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal,
    hc, hz, mul_one]
  calc
    (∑ x : Fin d,
      if x = a then (1 / 2 : ℝ)
      else if x = b then 1 / 2
      else 0) =
        ∑ x : Fin d,
          ((if x = a then (1 / 2 : ℝ) else 0) +
            if x = b then 1 / 2 else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hxa : x = a
      · subst x
        simp [hab]
      · simp [hxa]
    _ = 1 := by
      rw [Finset.sum_add_distrib]
      simp
      norm_num

def polarizedVector
    {ι : Type*} (z : ℂ) (x y : ι → ℂ) :
    ι → ℂ :=
  fun i =>
    ((1 / Real.sqrt 2 : ℝ) : ℂ) *
      (x i + z * y i)

def vectorSesquilinearForm
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) (x y : ι → ℂ) : ℂ :=
  ∑ i : ι, ∑ j : ι, star (x i) * A i j * y j

theorem vectorSesquilinearForm_add_left
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) (x y z : ι → ℂ) :
    vectorSesquilinearForm A (x + y) z =
      vectorSesquilinearForm A x z +
        vectorSesquilinearForm A y z := by
  unfold vectorSesquilinearForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply, star_add]
  ring

theorem vectorSesquilinearForm_add_right
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) (x y z : ι → ℂ) :
    vectorSesquilinearForm A x (y + z) =
      vectorSesquilinearForm A x y +
        vectorSesquilinearForm A x z := by
  unfold vectorSesquilinearForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply]
  ring

theorem vectorSesquilinearForm_smul_left
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) (c : ℂ) (x y : ι → ℂ) :
    vectorSesquilinearForm A (c • x) y =
      star c * vectorSesquilinearForm A x y := by
  unfold vectorSesquilinearForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul, star_mul]
  ring

theorem vectorSesquilinearForm_smul_right
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) (c : ℂ) (x y : ι → ℂ) :
    vectorSesquilinearForm A x (c • y) =
      c * vectorSesquilinearForm A x y := by
  unfold vectorSesquilinearForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem vectorSesquilinearForm_self
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) (x : ι → ℂ) :
    vectorSesquilinearForm A x x =
      vectorQuadraticForm A x := by
  rfl

theorem vectorQuadraticForm_polarized
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) (x y : ι → ℂ) (z : ℂ) :
    vectorQuadraticForm A (polarizedVector z x y) =
      (1 / 2 : ℂ) *
        (vectorQuadraticForm A x +
          z * vectorSesquilinearForm A x y +
          star z * vectorSesquilinearForm A y x +
          star z * z * vectorQuadraticForm A y) := by
  let c : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  have hc :
      c * c = (1 / 2 : ℂ) := by
    dsimp [c]
    push_cast
    norm_cast
    rw [div_mul_div_comm, one_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast
    norm_num
  have hstarc : star c = c := by
    simp [c]
  have hp :
      polarizedVector z x y =
        c • x + (c * z) • y := by
    funext i
    simp [polarizedVector, c]
    ring
  change
    vectorSesquilinearForm A
        (polarizedVector z x y)
        (polarizedVector z x y) =
      _
  rw [hp, vectorSesquilinearForm_add_left,
    vectorSesquilinearForm_add_right,
    vectorSesquilinearForm_add_right]
  simp only [vectorSesquilinearForm_smul_left,
    vectorSesquilinearForm_smul_right]
  simp only [vectorSesquilinearForm_self]
  rw [hstarc, star_mul, hstarc]
  ring_nf at hc ⊢
  rw [hc]
  ring

theorem vectorSesquilinearForm_polarization
    {ι : Type*} [Fintype ι]
    (A : CMatrix ι) (x y : ι → ℂ) :
    vectorSesquilinearForm A x y =
      (1 / 2 : ℂ) *
        (vectorQuadraticForm A (polarizedVector 1 x y) -
          vectorQuadraticForm A (polarizedVector (-1) x y)) +
      (1 / (2 * Complex.I) : ℂ) *
        (vectorQuadraticForm A (polarizedVector Complex.I x y) -
          vectorQuadraticForm A (polarizedVector (-Complex.I) x y)) := by
  set_option maxRecDepth 10000 in
  rw [vectorQuadraticForm_polarized,
    vectorQuadraticForm_polarized,
    vectorQuadraticForm_polarized,
    vectorQuadraticForm_polarized]
  norm_num [Complex.star_def, Complex.conj_I,
    Complex.conj_neg_I]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem unitaryVectorAction_add
    (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (x y : Fin d → ℂ) :
    unitaryVectorAction d U (x + y) =
      unitaryVectorAction d U x +
        unitaryVectorAction d U y := by
  funext i
  unfold unitaryVectorAction
  change
    (∑ j : Fin d, (U : CMatrix (Fin d)) i j *
      (x j + y j)) =
      (∑ j : Fin d, (U : CMatrix (Fin d)) i j * x j) +
        ∑ j : Fin d, (U : CMatrix (Fin d)) i j * y j
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]

theorem unitaryVectorAction_smul
    (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (c : ℂ) (x : Fin d → ℂ) :
    unitaryVectorAction d U (c • x) =
      c • unitaryVectorAction d U x := by
  funext i
  unfold unitaryVectorAction
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem unitaryVectorAction_standardBasisVector
    (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (a : Fin d) :
    unitaryVectorAction d U (standardBasisVector d a) =
      unitaryColumn d a U := by
  funext i
  unfold unitaryVectorAction standardBasisVector unitaryColumn
  simp

theorem polarizationBasisVector_eq
    (d : ℕ) (a b : Fin d) (z : ℂ) :
    polarizationBasisVector d a b z =
      (((1 / Real.sqrt 2 : ℝ) : ℂ) •
          standardBasisVector d a) +
        ((((1 / Real.sqrt 2 : ℝ) : ℂ) * z) •
          standardBasisVector d b) := by
  funext i
  simp only [polarizationBasisVector, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem unitaryVectorAction_polarizationBasisVector
    (d : ℕ) (U : Matrix.unitaryGroup (Fin d) ℂ)
    (a b : Fin d) (z : ℂ) :
    unitaryVectorAction d U
        (polarizationBasisVector d a b z) =
      polarizedVector z
        (unitaryColumn d a U)
        (unitaryColumn d b U) := by
  rw [polarizationBasisVector_eq,
    unitaryVectorAction_add,
    unitaryVectorAction_smul,
    unitaryVectorAction_smul,
    unitaryVectorAction_standardBasisVector,
    unitaryVectorAction_standardBasisVector]
  funext i
  simp [polarizedVector, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

def sesquilinearFamilyVector
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (x y : Fin d → ℂ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2
    (fun k =>
      vectorSesquilinearForm
    (tracelessPart (A k)) x y)

def offDiagonalFamilyVector
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (a b : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    EuclideanSpace ℂ κ :=
  sesquilinearFamilyVector d A
    (unitaryColumn d a U) (unitaryColumn d b U)

theorem offDiagonalFamilyVector_polarization
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (a b : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    offDiagonalFamilyVector d A a b U =
      (1 / 2 : ℂ) •
        (orbitQuadraticFamilyVector d A
            (polarizationBasisVector d a b 1) U -
          orbitQuadraticFamilyVector d A
            (polarizationBasisVector d a b (-1)) U) +
      (1 / (2 * Complex.I) : ℂ) •
        (orbitQuadraticFamilyVector d A
            (polarizationBasisVector d a b Complex.I) U -
          orbitQuadraticFamilyVector d A
            (polarizationBasisVector d a b (-Complex.I)) U) := by
  ext k
  change
    vectorSesquilinearForm (tracelessPart (A k))
        (unitaryColumn d a U) (unitaryColumn d b U) =
      (1 / 2 : ℂ) *
        (vectorQuadraticForm (tracelessPart (A k))
            (unitaryVectorAction d U
              (polarizationBasisVector d a b 1)) -
          vectorQuadraticForm (tracelessPart (A k))
            (unitaryVectorAction d U
              (polarizationBasisVector d a b (-1)))) +
      (1 / (2 * Complex.I) : ℂ) *
        (vectorQuadraticForm (tracelessPart (A k))
            (unitaryVectorAction d U
              (polarizationBasisVector d a b Complex.I)) -
          vectorQuadraticForm (tracelessPart (A k))
            (unitaryVectorAction d U
              (polarizationBasisVector d a b (-Complex.I))))
  rw [unitaryVectorAction_polarizationBasisVector,
    unitaryVectorAction_polarizationBasisVector,
    unitaryVectorAction_polarizationBasisVector,
    unitaryVectorAction_polarizationBasisVector]
  exact vectorSesquilinearForm_polarization
    (tracelessPart (A k))
    (unitaryColumn d a U) (unitaryColumn d b U)

theorem onePartyHaar_offDiagonal_lpNorm_le
    (hc : GaussianHypercontractivityContract)
    {κ : Type} [Fintype κ]
    (d : ℕ) (a b : Fin d) (hab : a ≠ b)
    (A : κ → CMatrix (Fin d))
    (q : ℕ) (hq : 0 < q) (hfour : 4 * q ≤ d) :
    lpNorm (offDiagonalFamilyVector d A a b)
        (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤
      4 * ((2 * hc.constant * q / (d : ℝ)) *
        ((∑ k : κ, frobeniusSq (A k)) ^
          ((2 : ℝ)⁻¹))) := by
  let w1 := polarizationBasisVector d a b 1
  let wm1 := polarizationBasisVector d a b (-1)
  let wi := polarizationBasisVector d a b Complex.I
  let wmi := polarizationBasisVector d a b (-Complex.I)
  let F1 := orbitQuadraticFamilyVector d A w1
  let Fm1 := orbitQuadraticFamilyVector d A wm1
  let Fi := orbitQuadraticFamilyVector d A wi
  let Fmi := orbitQuadraticFamilyVector d A wmi
  let c1 : ℂ := 1 / 2
  let ci : ℂ := 1 / (2 * Complex.I)
  let B : ℝ :=
    (2 * hc.constant * q / (d : ℝ)) *
      ((∑ k : κ, frobeniusSq (A k)) ^
        ((2 : ℝ)⁻¹))
  have hw1 : vectorNormSq w1 = 1 := by
    apply vectorNormSq_polarizationBasisVector d a b 1 hab
    norm_num
  have hwm1 : vectorNormSq wm1 = 1 := by
    apply vectorNormSq_polarizationBasisVector d a b (-1) hab
    norm_num
  have hwi : vectorNormSq wi = 1 := by
    apply vectorNormSq_polarizationBasisVector d a b Complex.I hab
    norm_num [Complex.normSq_apply]
  have hwmi : vectorNormSq wmi = 1 := by
    apply vectorNormSq_polarizationBasisVector d a b (-Complex.I) hab
    norm_num [Complex.normSq_apply]
  have hF1 :
      MemLp F1 (q : ℝ≥0∞) (unitaryHaarMeasure d) :=
    memLp_continuous_on_unitaryGroup d F1
      (continuous_orbitQuadraticFamilyVector d A w1) _
  have hFm1 :
      MemLp Fm1 (q : ℝ≥0∞) (unitaryHaarMeasure d) :=
    memLp_continuous_on_unitaryGroup d Fm1
      (continuous_orbitQuadraticFamilyVector d A wm1) _
  have hFi :
      MemLp Fi (q : ℝ≥0∞) (unitaryHaarMeasure d) :=
    memLp_continuous_on_unitaryGroup d Fi
      (continuous_orbitQuadraticFamilyVector d A wi) _
  have hFmi :
      MemLp Fmi (q : ℝ≥0∞) (unitaryHaarMeasure d) :=
    memLp_continuous_on_unitaryGroup d Fmi
      (continuous_orbitQuadraticFamilyVector d A wmi) _
  have hF1_bound :
      lpNorm F1 (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤ B := by
    dsimp [F1, B]
    exact onePartyHaar_rankOne_orbit_lpNorm_le
      hc d a A w1 hw1 q hq hfour
  have hFm1_bound :
      lpNorm Fm1 (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤ B := by
    dsimp [Fm1, B]
    exact onePartyHaar_rankOne_orbit_lpNorm_le
      hc d a A wm1 hwm1 q hq hfour
  have hFi_bound :
      lpNorm Fi (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤ B := by
    dsimp [Fi, B]
    exact onePartyHaar_rankOne_orbit_lpNorm_le
      hc d a A wi hwi q hq hfour
  have hFmi_bound :
      lpNorm Fmi (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤ B := by
    dsimp [Fmi, B]
    exact onePartyHaar_rankOne_orbit_lpNorm_le
      hc d a A wmi hwmi q hq hfour
  have hd : 0 < d := by omega
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hc.constant_nonneg)
          (Nat.cast_nonneg q))
        (Nat.cast_nonneg d))
      (Real.rpow_nonneg
        (Finset.sum_nonneg fun k _ =>
          frobeniusSq_nonneg (A k)) _)
  have hc1 : (‖c1‖₊ : ℝ) ≤ 1 := by
    dsimp [c1]
    norm_num
  have hci : (‖ci‖₊ : ℝ) ≤ 1 := by
    dsimp [ci]
    change ‖(1 / (2 * Complex.I) : ℂ)‖ ≤ 1
    rw [norm_div, norm_mul, Complex.norm_I]
    norm_num
  have hp : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    exact_mod_cast hq
  have hD1 :
      MemLp (c1 • (F1 - Fm1))
        (q : ℝ≥0∞) (unitaryHaarMeasure d) :=
    (hF1.sub hFm1).const_smul' c1
  have hDi :
      MemLp (ci • (Fi - Fmi))
        (q : ℝ≥0∞) (unitaryHaarMeasure d) :=
    (hFi.sub hFmi).const_smul' ci
  have hD1_bound :
      lpNorm (c1 • (F1 - Fm1))
          (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤ 2 * B := by
    rw [lpNorm_const_smul]
    have hsub :=
      lpNorm_sub_le (g := Fm1) hF1 hp
    have hsum :
        lpNorm F1 (q : ℝ≥0∞) (unitaryHaarMeasure d) +
          lpNorm Fm1 (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤
        2 * B := by linarith
    nlinarith [lpNorm_nonneg
      (f := F1 - Fm1) (p := (q : ℝ≥0∞))
      (μ := unitaryHaarMeasure d)]
  have hDi_bound :
      lpNorm (ci • (Fi - Fmi))
          (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤ 2 * B := by
    rw [lpNorm_const_smul]
    have hsub :=
      lpNorm_sub_le (g := Fmi) hFi hp
    have hsum :
        lpNorm Fi (q : ℝ≥0∞) (unitaryHaarMeasure d) +
          lpNorm Fmi (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤
        2 * B := by linarith
    nlinarith [lpNorm_nonneg
      (f := Fi - Fmi) (p := (q : ℝ≥0∞))
      (μ := unitaryHaarMeasure d)]
  have hoff :
      offDiagonalFamilyVector d A a b =
        c1 • (F1 - Fm1) + ci • (Fi - Fmi) := by
    funext U
    exact offDiagonalFamilyVector_polarization d A a b U
  rw [hoff]
  change
    lpNorm (c1 • (F1 - Fm1) + ci • (Fi - Fmi))
      (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤ 4 * B
  have hadd :=
    lpNorm_add_le hD1 (g := ci • (Fi - Fmi)) hp
  linarith

theorem standardBasisVector_eq_unitaryColumn_one
    (d : ℕ) (a : Fin d) :
    standardBasisVector d a =
      unitaryColumn d a
        (1 : Matrix.unitaryGroup (Fin d) ℂ) := by
  funext i
  simp [standardBasisVector, unitaryColumn,
    Matrix.one_apply]

theorem vectorNormSq_standardBasisVector
    (d : ℕ) (a : Fin d) :
    vectorNormSq (standardBasisVector d a) = 1 := by
  rw [standardBasisVector_eq_unitaryColumn_one]
  exact vectorNormSq_unitaryColumn d a 1

theorem offDiagonalFamilyVector_diagonal
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (a : Fin d) :
    offDiagonalFamilyVector d A a a =
      orbitQuadraticFamilyVector d A
        (standardBasisVector d a) := by
  funext U
  ext k
  change
    vectorSesquilinearForm
        (tracelessPart (A k))
        (unitaryColumn d a U)
        (unitaryColumn d a U) =
      vectorQuadraticForm
        (tracelessPart (A k))
        (unitaryVectorAction d U
          (standardBasisVector d a))
  rw [unitaryVectorAction_standardBasisVector]
  rfl

theorem onePartyHaar_matrixUnit_lpNorm_le
    (hc : GaussianHypercontractivityContract)
    {κ : Type} [Fintype κ]
    (d : ℕ) (a b : Fin d)
    (A : κ → CMatrix (Fin d))
    (q : ℕ) (hq : 0 < q) (hfour : 4 * q ≤ d) :
    lpNorm (offDiagonalFamilyVector d A a b)
        (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤
      4 * ((2 * hc.constant * q / (d : ℝ)) *
        ((∑ k : κ, frobeniusSq (A k)) ^
          ((2 : ℝ)⁻¹))) := by
  by_cases hab : a = b
  · subst b
    rw [offDiagonalFamilyVector_diagonal]
    have hbase :=
      onePartyHaar_rankOne_orbit_lpNorm_le
        hc d a A (standardBasisVector d a)
        (vectorNormSq_standardBasisVector d a)
        q hq hfour
    have hd : 0 < d := by omega
    have hB :
        0 ≤ (2 * hc.constant * q / (d : ℝ)) *
          ((∑ k : κ, frobeniusSq (A k)) ^
            ((2 : ℝ)⁻¹)) := by
      exact mul_nonneg
        (div_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num) hc.constant_nonneg)
            (Nat.cast_nonneg q))
          (Nat.cast_nonneg d))
        (Real.rpow_nonneg
          (Finset.sum_nonneg fun k _ =>
            frobeniusSq_nonneg (A k)) _)
    linarith
  · exact onePartyHaar_offDiagonal_lpNorm_le
      hc d a b hab A q hq hfour

end

end QuantumSep
