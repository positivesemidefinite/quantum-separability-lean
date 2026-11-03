import QuantumSep.HaarPolarization
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal

namespace QuantumSep

noncomputable section

def firstSlice
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (ce : Fin d × Fin d) : CMatrix (Fin d) :=
  fun a b => M (a, ce.1) (b, ce.2)

theorem firstSlice_trace
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (c e : Fin d) :
    (firstSlice d M (c, e)).trace =
      partialTrace0 M c e := by
  rfl

theorem firstSlice_tracelessPart_eq
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero : partialTrace0 M = 0)
    (ce : Fin d × Fin d) :
    tracelessPart (firstSlice d M ce) =
      firstSlice d M ce := by
  have ht : (firstSlice d M ce).trace = 0 := by
    rw [firstSlice_trace]
    simpa using congrFun (congrFun hzero ce.1) ce.2
  unfold tracelessPart traceScalarMatrix
  rw [ht]
  simp

def firstContractedMatrix
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    CMatrix (Fin d) :=
  fun c e =>
    vectorSesquilinearForm
      (tracelessPart (firstSlice d M (c, e)))
      (unitaryColumn d a U) (unitaryColumn d b U)

theorem firstContractedMatrix_trace
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    (firstContractedMatrix d M a b U).trace = 0 := by
  let x := unitaryColumn d a U
  let y := unitaryColumn d b U
  have hz (i j : Fin d) :
      (∑ c : Fin d, M (i, c) (j, c)) = 0 := by
    simpa [partialTrace1] using
      congrFun (congrFun hzero1 i) j
  change
    (∑ c : Fin d,
      vectorSesquilinearForm
        (tracelessPart (firstSlice d M (c, c))) x y) = 0
  simp_rw [firstSlice_tracelessPart_eq d M hzero0]
  unfold vectorSesquilinearForm firstSlice
  calc
    (∑ c : Fin d,
        ∑ i : Fin d, ∑ j : Fin d,
          star (x i) * M (i, c) (j, c) * y j) =
        ∑ i : Fin d, ∑ j : Fin d,
          star (x i) *
            (∑ c : Fin d, M (i, c) (j, c)) * y j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul]
      congr 1
      rw [← Finset.mul_sum]
    _ = 0 := by simp [hz]

theorem firstContractedMatrix_tracelessPart_eq
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    tracelessPart (firstContractedMatrix d M a b U) =
      firstContractedMatrix d M a b U := by
  unfold tracelessPart traceScalarMatrix
  rw [firstContractedMatrix_trace d M hzero0 hzero1]
  simp

theorem offDiagonalFamilyVector_firstSlice_apply
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (ce : Fin d × Fin d) :
    offDiagonalFamilyVector d (firstSlice d M) a b U ce =
      firstContractedMatrix d M a b U ce.1 ce.2 := by
  rfl

theorem norm_offDiagonalFamilyVector_firstSlice_sq
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖offDiagonalFamilyVector d (firstSlice d M) a b U‖ ^ 2 =
      frobeniusSq (firstContractedMatrix d M a b U) := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold frobeniusSq
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro e _
  rw [offDiagonalFamilyVector_firstSlice_apply,
    Complex.normSq_eq_norm_sq]

theorem norm_offDiagonalFamilyVector_firstSlice
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b : Fin d)
    (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖offDiagonalFamilyVector d (firstSlice d M) a b U‖ =
      (frobeniusSq (firstContractedMatrix d M a b U) ^
        ((2 : ℝ)⁻¹)) := by
  calc
    ‖offDiagonalFamilyVector d (firstSlice d M) a b U‖ =
        √(frobeniusSq (firstContractedMatrix d M a b U)) := by
      rw [← norm_offDiagonalFamilyVector_firstSlice_sq]
      exact
        (Real.sqrt_sq
          (norm_nonneg
            (offDiagonalFamilyVector
              d (firstSlice d M) a b U))).symm
    _ = (frobeniusSq (firstContractedMatrix d M a b U) ^
          ((2 : ℝ)⁻¹)) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      norm_num

theorem continuous_offDiagonalFamilyVector
    {κ : Type*} [Fintype κ]
    (d : ℕ) (A : κ → CMatrix (Fin d))
    (a b : Fin d) :
    Continuous (offDiagonalFamilyVector d A a b) := by
  have hcol (r i : Fin d) :
      Continuous
        (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
          unitaryColumn d r U i) := by
    unfold unitaryColumn
    have hi :
        Continuous (fun U : CMatrix (Fin d) => U i) :=
      continuous_apply i
    have hir :
        Continuous (fun U : CMatrix (Fin d) => U i r) :=
      (continuous_apply r).comp hi
    exact hir.comp continuous_subtype_val
  unfold offDiagonalFamilyVector sesquilinearFamilyVector
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  unfold vectorSesquilinearForm
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact
    ((continuous_star.comp (hcol a i)).mul continuous_const)
      |>.mul (hcol b j)

theorem continuous_firstContractedMatrix
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b : Fin d) :
    Continuous (firstContractedMatrix d M a b) := by
  apply continuous_pi
  intro c
  apply continuous_pi
  intro e
  have h :=
    (PiLp.continuous_apply
      (p := 2) (β := fun _ : Fin d × Fin d => ℂ) (c, e)).comp
      (continuous_offDiagonalFamilyVector
        d (firstSlice d M) a b)
  simpa [Function.comp_def,
    offDiagonalFamilyVector_firstSlice_apply] using h

theorem frobeniusSq_firstSlices
    (d : ℕ) (M : BipartiteMatrix (Fin d)) :
    (∑ ce : Fin d × Fin d,
        frobeniusSq (firstSlice d M ce)) =
      frobeniusSq M := by
  unfold frobeniusSq firstSlice
  simp_rw [Fintype.sum_prod_type]
  calc
    (∑ c : Fin d, ∑ e : Fin d,
        ∑ a : Fin d, ∑ b : Fin d,
          Complex.normSq (M (a, c) (b, e))) =
        ∑ c : Fin d, ∑ a : Fin d,
          ∑ e : Fin d, ∑ b : Fin d,
            Complex.normSq (M (a, c) (b, e)) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = ∑ a : Fin d, ∑ c : Fin d,
          ∑ e : Fin d, ∑ b : Fin d,
            Complex.normSq (M (a, c) (b, e)) := by
      rw [Finset.sum_comm]
    _ = ∑ a : Fin d, ∑ c : Fin d,
          ∑ b : Fin d, ∑ e : Fin d,
            Complex.normSq (M (a, c) (b, e)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

def twoPartyHaarVector
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b c e : Fin d)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    EuclideanSpace ℂ Unit :=
  offDiagonalFamilyVector d
    (fun _ : Unit =>
      firstContractedMatrix d M a b UV.1)
    c e UV.2

def bipartiteHaarEntry
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b c e : Fin d)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) : ℂ :=
  ∑ r : Fin d, ∑ s : Fin d,
    star (unitaryColumn d c UV.2 r) *
      (∑ i : Fin d, ∑ j : Fin d,
        star (unitaryColumn d a UV.1 i) *
          M (i, r) (j, s) *
          unitaryColumn d b UV.1 j) *
      unitaryColumn d e UV.2 s

def bipartiteUnitaryConjugate
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    BipartiteMatrix (Fin d) :=
  let W :=
    tensor (UV.1 : CMatrix (Fin d))
      (UV.2 : CMatrix (Fin d))
  Matrix.conjTranspose W * (M * W)

theorem bipartiteHaarEntry_eq_unitaryConjugate_apply
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b c e : Fin d)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    bipartiteHaarEntry d M a b c e UV =
      bipartiteUnitaryConjugate d M UV (a, c) (b, e) := by
  unfold bipartiteHaarEntry bipartiteUnitaryConjugate
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    tensor, unitaryColumn]
  simp_rw [Fintype.sum_prod_type, star_mul,
    Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ r : Fin d, ∑ s : Fin d, ∑ i : Fin d, ∑ j : Fin d,
        star ((UV.2 : CMatrix (Fin d)) r c) *
          (star ((UV.1 : CMatrix (Fin d)) i a) *
            M (i, r) (j, s) *
            (UV.1 : CMatrix (Fin d)) j b) *
          (UV.2 : CMatrix (Fin d)) s e) =
      ∑ r : Fin d, ∑ s : Fin d, ∑ i : Fin d, ∑ j : Fin d,
        star ((UV.2 : CMatrix (Fin d)) r c) *
          star ((UV.1 : CMatrix (Fin d)) i a) *
          M (i, r) (j, s) *
          (UV.1 : CMatrix (Fin d)) j b *
          (UV.2 : CMatrix (Fin d)) s e := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ r : Fin d, ∑ i : Fin d, ∑ s : Fin d, ∑ j : Fin d,
        star ((UV.2 : CMatrix (Fin d)) r c) *
          star ((UV.1 : CMatrix (Fin d)) i a) *
          M (i, r) (j, s) *
          (UV.1 : CMatrix (Fin d)) j b *
          (UV.2 : CMatrix (Fin d)) s e := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin d, ∑ r : Fin d, ∑ s : Fin d, ∑ j : Fin d,
        star ((UV.2 : CMatrix (Fin d)) r c) *
          star ((UV.1 : CMatrix (Fin d)) i a) *
          M (i, r) (j, s) *
          (UV.1 : CMatrix (Fin d)) j b *
          (UV.2 : CMatrix (Fin d)) s e := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin d, ∑ r : Fin d, ∑ j : Fin d, ∑ s : Fin d,
        star ((UV.2 : CMatrix (Fin d)) r c) *
          star ((UV.1 : CMatrix (Fin d)) i a) *
          M (i, r) (j, s) *
          (UV.1 : CMatrix (Fin d)) j b *
          (UV.2 : CMatrix (Fin d)) s e := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ i : Fin d, ∑ r : Fin d, ∑ j : Fin d, ∑ s : Fin d,
        star ((UV.2 : CMatrix (Fin d)) r c) *
          star ((UV.1 : CMatrix (Fin d)) i a) *
          (M (i, r) (j, s) *
            ((UV.1 : CMatrix (Fin d)) j b *
              (UV.2 : CMatrix (Fin d)) s e)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro s _
      ring

theorem twoPartyHaarVector_apply_eq_bipartiteHaarEntry
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b c e : Fin d)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    twoPartyHaarVector d M a b c e UV () =
      bipartiteHaarEntry d M a b c e UV := by
  change
    vectorSesquilinearForm
        (tracelessPart
          (firstContractedMatrix d M a b UV.1))
        (unitaryColumn d c UV.2)
        (unitaryColumn d e UV.2) =
      _
  rw [firstContractedMatrix_tracelessPart_eq
    d M hzero0 hzero1]
  unfold vectorSesquilinearForm firstContractedMatrix
    bipartiteHaarEntry
  simp_rw [firstSlice_tracelessPart_eq d M hzero0]
  rfl

theorem norm_twoPartyHaarVector_eq_norm_bipartiteHaarEntry
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b c e : Fin d)
    (UV :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :
    ‖twoPartyHaarVector d M a b c e UV‖ =
      ‖bipartiteHaarEntry d M a b c e UV‖ := by
  have hs :
      ‖twoPartyHaarVector d M a b c e UV‖ ^ 2 =
        ‖bipartiteHaarEntry d M a b c e UV‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_unique,
      twoPartyHaarVector_apply_eq_bipartiteHaarEntry
        d M hzero0 hzero1]
  nlinarith [norm_nonneg
      (twoPartyHaarVector d M a b c e UV),
    norm_nonneg (bipartiteHaarEntry d M a b c e UV)]

theorem measurable_twoPartyHaarVector
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b c e : Fin d) :
    Measurable (twoPartyHaarVector d M a b c e) := by
  have hcol (r i : Fin d) :
      Measurable
        (fun UV :
          Matrix.unitaryGroup (Fin d) ℂ ×
            Matrix.unitaryGroup (Fin d) ℂ =>
          unitaryColumn d r UV.2 i) :=
    ((measurable_pi_apply i).comp
      (measurable_unitaryColumn d r)).comp measurable_snd
  have htless (r s : Fin d) :
      Measurable
        (fun UV :
          Matrix.unitaryGroup (Fin d) ℂ ×
            Matrix.unitaryGroup (Fin d) ℂ =>
          tracelessPart
            (firstContractedMatrix d M a b UV.1) r s) := by
    have hC :=
      continuous_firstContractedMatrix d M a b
    have hentry (i j : Fin d) :
        Continuous
          (fun U =>
            firstContractedMatrix d M a b U i j) :=
      (continuous_apply j).comp
        ((continuous_apply i).comp hC)
    have htrace :
        Continuous
          (fun U =>
            (firstContractedMatrix d M a b U).trace) := by
      unfold Matrix.trace
      apply continuous_finsetSum
      intro i _
      exact hentry i i
    have hsingle :
        Continuous
          (fun U =>
            tracelessPart
              (firstContractedMatrix d M a b U) r s) := by
      unfold tracelessPart traceScalarMatrix
      simp only [Matrix.sub_apply, Matrix.smul_apply]
      exact (hentry r s).sub
        ((htrace.div_const (dimC (ι := Fin d))).mul
          continuous_const)
    exact hsingle.measurable.comp measurable_fst
  unfold twoPartyHaarVector offDiagonalFamilyVector
    sesquilinearFamilyVector
  apply (PiLp.continuous_toLp 2 _).measurable.comp
  apply measurable_pi_lambda
  intro _
  unfold vectorSesquilinearForm
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  exact
    ((((continuous_star.measurable.comp (hcol c i))
      |>.mul (htless i j))).mul
      (hcol e j))

theorem continuous_twoPartyHaarVector
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b c e : Fin d) :
    Continuous (twoPartyHaarVector d M a b c e) := by
  have hcol (r i : Fin d) :
      Continuous
        (fun UV :
          Matrix.unitaryGroup (Fin d) ℂ ×
            Matrix.unitaryGroup (Fin d) ℂ =>
          unitaryColumn d r UV.2 i) := by
    unfold unitaryColumn
    have hi :
        Continuous (fun U : CMatrix (Fin d) => U i) :=
      continuous_apply i
    have hir :
        Continuous (fun U : CMatrix (Fin d) => U i r) :=
      (continuous_apply r).comp hi
    exact
      (hir.comp continuous_subtype_val).comp continuous_snd
  have htless (r s : Fin d) :
      Continuous
        (fun UV :
          Matrix.unitaryGroup (Fin d) ℂ ×
            Matrix.unitaryGroup (Fin d) ℂ =>
          tracelessPart
            (firstContractedMatrix d M a b UV.1) r s) := by
    have hC :=
      continuous_firstContractedMatrix d M a b
    have hentry (i j : Fin d) :
        Continuous
          (fun U =>
            firstContractedMatrix d M a b U i j) :=
      (continuous_apply j).comp
        ((continuous_apply i).comp hC)
    have htrace :
        Continuous
          (fun U =>
            (firstContractedMatrix d M a b U).trace) := by
      unfold Matrix.trace
      apply continuous_finsetSum
      intro i _
      exact hentry i i
    have hsingle :
        Continuous
          (fun U =>
            tracelessPart
              (firstContractedMatrix d M a b U) r s) := by
      unfold tracelessPart traceScalarMatrix
      simp only [Matrix.sub_apply, Matrix.smul_apply]
      exact (hentry r s).sub
        ((htrace.div_const (dimC (ι := Fin d))).mul
          continuous_const)
    exact hsingle.comp continuous_fst
  unfold twoPartyHaarVector offDiagonalFamilyVector
    sesquilinearFamilyVector
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro _
  unfold vectorSesquilinearForm
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact
    (((continuous_star.comp (hcol c i)).mul (htless i j)).mul
      (hcol e j))

theorem integrable_norm_twoPartyHaarVector_pow
    (d q : ℕ) (M : BipartiteMatrix (Fin d))
    (a b c e : Fin d) :
    Integrable
      (fun UV => ‖twoPartyHaarVector d M a b c e UV‖ ^ q)
      ((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d)) := by
  let F' :
      C(Matrix.unitaryGroup (Fin d) ℂ ×
          Matrix.unitaryGroup (Fin d) ℂ, EuclideanSpace ℂ Unit) :=
    ⟨twoPartyHaarVector d M a b c e,
      continuous_twoPartyHaarVector d M a b c e⟩
  apply Integrable.of_bound
    ((measurable_twoPartyHaarVector d M a b c e).norm
      |>.pow_const q |>.aestronglyMeasurable)
    (‖F'‖ ^ q)
  filter_upwards with UV
  rw [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) q)]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (F'.norm_coe_le_norm UV) q

theorem measurable_bipartiteHaarEntry
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b c e : Fin d) :
    Measurable (bipartiteHaarEntry d M a b c e) := by
  have hv :
      Measurable
        (fun UV =>
          twoPartyHaarVector d M a b c e UV ()) := by
    exact
      (PiLp.continuous_apply
        (p := 2) (β := fun _ : Unit => ℂ) ()).measurable.comp
        (measurable_twoPartyHaarVector d M a b c e)
  rw [show
    bipartiteHaarEntry d M a b c e =
      fun UV => twoPartyHaarVector d M a b c e UV () by
        funext UV
        exact
          (twoPartyHaarVector_apply_eq_bipartiteHaarEntry
            d M hzero0 hzero1 a b c e UV).symm]
  exact hv

theorem lpNorm_bipartiteHaarEntry_eq_vector
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b c e : Fin d) (q : ℕ) :
    lpNorm (bipartiteHaarEntry d M a b c e)
        (q : ℝ≥0∞)
        ((unitaryHaarMeasure d).prod
          (unitaryHaarMeasure d)) =
      lpNorm (twoPartyHaarVector d M a b c e)
        (q : ℝ≥0∞)
        ((unitaryHaarMeasure d).prod
          (unitaryHaarMeasure d)) := by
  rw [← toReal_eLpNorm
      (measurable_bipartiteHaarEntry
        d M hzero0 hzero1 a b c e).aestronglyMeasurable,
    ← toReal_eLpNorm
      (measurable_twoPartyHaarVector
        d M a b c e).aestronglyMeasurable]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards with UV
  exact norm_twoPartyHaarVector_eq_norm_bipartiteHaarEntry
    d M hzero0 hzero1 a b c e UV |>.symm

theorem measurable_unitary_inner_lpNorm
    {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (d q : ℕ) (hq : 0 < q)
    (F :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ → E)
    (hF : Measurable F) :
    Measurable
      (fun U =>
        lpNorm (fun V => F (U, V))
          (q : ℝ≥0∞) (unitaryHaarMeasure d)) := by
  let G :=
    fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      ∫ V : Matrix.unitaryGroup (Fin d) ℂ,
        ‖F (U, V)‖ ^ q ∂unitaryHaarMeasure d
  have hpow :
      StronglyMeasurable
        (fun z :
          Matrix.unitaryGroup (Fin d) ℂ ×
            Matrix.unitaryGroup (Fin d) ℂ =>
          ‖F z‖ ^ q) := by
    exact (hF.norm.pow_const q).stronglyMeasurable
  have hG : StronglyMeasurable G := by
    exact hpow.integral_prod_right'
  have hformula :
      (fun U =>
        lpNorm (fun V => F (U, V))
          (q : ℝ≥0∞) (unitaryHaarMeasure d)) =
      fun U => G U ^ ((q : ℝ)⁻¹) := by
    funext U
    have hsection :
        Measurable (fun V => F (U, V)) :=
      hF.comp measurable_prodMk_left
    rw [lpNorm_eq_integral_norm_rpow_toReal
      (by simp [hq.ne']) (by simp)
      hsection.aestronglyMeasurable]
    simp [G]
  rw [hformula]
  exact
    (Real.continuous_rpow_const (by positivity)).measurable.comp
      hG.measurable

theorem unitary_lpNorm_prod_eq_iterated
    {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (d q : ℕ) (hq : 0 < q)
    (F :
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ → E)
    (hF : Measurable F)
    (hint : Integrable (fun z => ‖F z‖ ^ q)
      ((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d))) :
    lpNorm F (q : ℝ≥0∞)
        ((unitaryHaarMeasure d).prod (unitaryHaarMeasure d)) =
      lpNorm
        (fun U =>
          lpNorm (fun V => F (U, V))
            (q : ℝ≥0∞) (unitaryHaarMeasure d))
        (q : ℝ≥0∞) (unitaryHaarMeasure d) := by
  have hinner :=
    measurable_unitary_inner_lpNorm d q hq F hF
  rw [lpNorm_eq_integral_norm_rpow_toReal
      (by simp [hq.ne']) (by simp)
      hF.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal
      (by simp [hq.ne']) (by simp)
      hinner.aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
  congr 1
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards with U
  have hsection :
      Measurable (fun V => F (U, V)) :=
    hF.comp measurable_prodMk_left
  rw [lpNorm_eq_integral_norm_rpow_toReal
      (by simp [hq.ne']) (by simp)
      hsection.aestronglyMeasurable]
  simp only [ENNReal.toReal_natCast, Real.norm_eq_abs,
    Real.rpow_natCast]
  have hnonneg :
      0 ≤ ∫ V : Matrix.unitaryGroup (Fin d) ℂ,
        ‖F (U, V)‖ ^ q ∂unitaryHaarMeasure d :=
    integral_nonneg fun V =>
      pow_nonneg (norm_nonneg (F (U, V))) q
  rw [abs_of_nonneg (Real.rpow_nonneg hnonneg _)]
  exact
    (Real.rpow_inv_natCast_pow hnonneg hq.ne').symm

theorem twoPartyHaarVector_lpNorm_le
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (a b c e : Fin d)
    (q : ℕ) (hq : 0 < q) (hfour : 4 * q ≤ d) :
    lpNorm (twoPartyHaarVector d M a b c e)
        (q : ℝ≥0∞)
        ((unitaryHaarMeasure d).prod
          (unitaryHaarMeasure d)) ≤
      (4 * (2 * hc.constant * q / (d : ℝ))) ^ 2 *
        (frobeniusSq M ^ ((2 : ℝ)⁻¹)) := by
  let K : ℝ :=
    4 * (2 * hc.constant * q / (d : ℝ))
  let X :=
    fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      offDiagonalFamilyVector d (firstSlice d M) a b U
  have hd : 0 < d := by omega
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num)
      (div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) hc.constant_nonneg)
          (Nat.cast_nonneg q))
        (Nat.cast_nonneg d))
  have hprod :
      lpNorm (twoPartyHaarVector d M a b c e)
          (q : ℝ≥0∞)
          ((unitaryHaarMeasure d).prod
            (unitaryHaarMeasure d)) =
        lpNorm
          (fun U =>
            lpNorm
              (fun V =>
                twoPartyHaarVector d M a b c e (U, V))
              (q : ℝ≥0∞) (unitaryHaarMeasure d))
          (q : ℝ≥0∞) (unitaryHaarMeasure d) := by
    exact unitary_lpNorm_prod_eq_iterated
      d q hq (twoPartyHaarVector d M a b c e)
      (measurable_twoPartyHaarVector d M a b c e)
      (integrable_norm_twoPartyHaarVector_pow
        d q M a b c e)
  have hinner :
      ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        lpNorm
            (fun V =>
              twoPartyHaarVector d M a b c e (U, V))
            (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤
          K * ‖X U‖ := by
    intro U
    have h :=
      onePartyHaar_matrixUnit_lpNorm_le
        hc d c e
        (fun _ : Unit =>
          firstContractedMatrix d M a b U)
        q hq hfour
    convert h using 1
    · rfl
    · rw [Fintype.sum_unique,
        norm_offDiagonalFamilyVector_firstSlice]
      dsimp [K, X]
      ring
  have hXcont : Continuous X := by
    exact continuous_offDiagonalFamilyVector
      d (firstSlice d M) a b
  have hg :
      MemLp (fun U => K * ‖X U‖)
        (q : ℝ≥0∞) (unitaryHaarMeasure d) := by
    apply memLp_continuous_on_unitaryGroup
    exact continuous_const.mul hXcont.norm
  have hmono :
      lpNorm
          (fun U =>
            lpNorm
              (fun V =>
                twoPartyHaarVector d M a b c e (U, V))
              (q : ℝ≥0∞) (unitaryHaarMeasure d))
          (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤
        lpNorm (fun U => K * ‖X U‖)
          (q : ℝ≥0∞) (unitaryHaarMeasure d) := by
    apply lpNorm_mono_real hg
    intro U
    rw [Real.norm_eq_abs,
      abs_of_nonneg lpNorm_nonneg]
    exact hinner U
  have hscale :
      lpNorm (fun U => K * ‖X U‖)
          (q : ℝ≥0∞) (unitaryHaarMeasure d) =
        K * lpNorm X
          (q : ℝ≥0∞) (unitaryHaarMeasure d) := by
    change
      lpNorm (K • (fun U => ‖X U‖))
          (q : ℝ≥0∞) (unitaryHaarMeasure d) =
        _
    rw [lpNorm_const_smul,
      lpNorm_norm hXcont.aestronglyMeasurable]
    simp [Real.nnnorm_of_nonneg hK]
  have hfirst :
      lpNorm X (q : ℝ≥0∞) (unitaryHaarMeasure d) ≤
        K * (frobeniusSq M ^ ((2 : ℝ)⁻¹)) := by
    have h :=
      onePartyHaar_matrixUnit_lpNorm_le
        hc d a b (firstSlice d M) q hq hfour
    convert h using 1
    rw [frobeniusSq_firstSlices]
    dsimp [K]
    ring
  rw [hprod]
  calc
    _ ≤ lpNorm (fun U => K * ‖X U‖)
          (q : ℝ≥0∞) (unitaryHaarMeasure d) := hmono
    _ = K * lpNorm X
          (q : ℝ≥0∞) (unitaryHaarMeasure d) := hscale
    _ ≤ K * (K *
          (frobeniusSq M ^ ((2 : ℝ)⁻¹))) :=
      mul_le_mul_of_nonneg_left hfirst hK
    _ = (4 * (2 * hc.constant * q / (d : ℝ))) ^ 2 *
          (frobeniusSq M ^ ((2 : ℝ)⁻¹)) := by
      dsimp [K]
      ring

theorem twoPartyHaar_moment_le
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b c e : Fin d)
    (q : ℕ) (hq : 0 < q) (hfour : 4 * q ≤ d) :
    lpNorm (bipartiteHaarEntry d M a b c e)
        (q : ℝ≥0∞)
        ((unitaryHaarMeasure d).prod
          (unitaryHaarMeasure d)) ≤
      (4 * (2 * hc.constant * q / (d : ℝ))) ^ 2 *
        (frobeniusSq M ^ ((2 : ℝ)⁻¹)) := by
  rw [lpNorm_bipartiteHaarEntry_eq_vector
    d M hzero0 hzero1]
  exact twoPartyHaarVector_lpNorm_le
    hc d M a b c e q hq hfour

theorem twoPartyHaar_manuscript_moment_le
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (M : BipartiteMatrix (Fin d))
    (hzero0 : partialTrace0 M = 0)
    (hzero1 : partialTrace1 M = 0)
    (a b c e : Fin d)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d) :
    lpNorm (bipartiteHaarEntry d M a b c e)
        ((2 * p : ℕ) : ℝ≥0∞)
        ((unitaryHaarMeasure d).prod
          (unitaryHaarMeasure d)) ≤
      (256 * hc.constant ^ 2 * (p : ℝ) ^ 2 /
          (d : ℝ) ^ 2) *
        (frobeniusSq M ^ ((2 : ℝ)⁻¹)) := by
  have hq : 0 < 2 * p := by omega
  have hfour : 4 * (2 * p) ≤ d := by omega
  have h :=
    twoPartyHaar_moment_le
      hc d M hzero0 hzero1 a b c e
      (2 * p) hq hfour
  convert h using 1
  have hd : (d : ℝ) ≠ 0 := by
    have : 0 < d := by omega
    positivity
  field_simp [hd]
  push_cast
  ring

end

end QuantumSep
