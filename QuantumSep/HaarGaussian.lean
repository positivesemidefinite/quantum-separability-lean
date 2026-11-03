import QuantumSep.GaussianDirection
import QuantumSep.GaussianProduct
import QuantumSep.HaarUnitary
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace QuantumSep

noncomputable section

def pairRealCoordinate (k : Fin 2) (p : ℝ × ℝ) : ℝ :=
  if k = 0 then p.1 else p.2

theorem measurable_pairRealCoordinate (k : Fin 2) :
    Measurable (pairRealCoordinate k) := by
  unfold pairRealCoordinate
  split_ifs <;> fun_prop

def realGaussianCoordinate (d : ℕ) (a : Fin d × Fin 2)
    (ω : Fin d → ℝ × ℝ) : ℝ :=
  pairRealCoordinate a.2 (ω a.1)

def realGaussianCoordinatesLM (d : ℕ) :
    (Fin d → ℝ × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin d × Fin 2) where
  toFun ω := WithLp.toLp 2 (fun a => realGaussianCoordinate d a ω)
  map_add' x y := by
    ext a
    simp only [realGaussianCoordinate, pairRealCoordinate]
    split_ifs with h <;> simp [h]
  map_smul' c x := by
    ext a
    simp only [realGaussianCoordinate, pairRealCoordinate]
    split_ifs with h <;> simp [h, smul_eq_mul]

def realGaussianCoordinatesCLM (d : ℕ) :
    (Fin d → ℝ × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin d × Fin 2) :=
  (realGaussianCoordinatesLM d).toContinuousLinearMap

@[simp] theorem realGaussianCoordinatesCLM_apply
    (d : ℕ) (ω : Fin d → ℝ × ℝ) :
    realGaussianCoordinatesCLM d ω =
      WithLp.toLp 2 (fun a => realGaussianCoordinate d a ω) := rfl

theorem memLp_pairRealCoordinate (k : Fin 2) :
    MemLp (pairRealCoordinate k) 2 complexGaussianPairMeasure := by
  fin_cases k
  · change MemLp (fun p : ℝ × ℝ => p.1) 2
      (realGaussianHalf.prod realGaussianHalf)
    exact (memLp_id_gaussianReal (μ := 0) (v := gaussianHalfVariance) 2).comp_fst
      realGaussianHalf
  · change MemLp (fun p : ℝ × ℝ => p.2) 2
      (realGaussianHalf.prod realGaussianHalf)
    exact (memLp_id_gaussianReal (μ := 0) (v := gaussianHalfVariance) 2).comp_snd
      realGaussianHalf

theorem memLp_realGaussianCoordinate (d : ℕ) (a : Fin d × Fin 2) :
    MemLp (realGaussianCoordinate d a) 2
      (complexGaussianVectorMeasure (Fin d)) := by
  exact (memLp_pairRealCoordinate a.2).comp_measurePreserving
    (measurePreserving_eval
      (fun _ : Fin d => complexGaussianPairMeasure) a.1)

theorem covariance_realGaussianCoordinate
    (d : ℕ) (a b : Fin d × Fin 2) :
    cov[realGaussianCoordinate d a, realGaussianCoordinate d b;
      complexGaussianVectorMeasure (Fin d)] =
      if a = b then 1 / 2 else 0 := by
  classical
  rcases a with ⟨ai, ak⟩
  rcases b with ⟨bi, bk⟩
  by_cases hab₁ : ai = bi
  · subst bi
    have heval :
        MeasurePreserving (fun ω : Fin d → ℝ × ℝ => ω ai)
          (complexGaussianVectorMeasure (Fin d))
          complexGaussianPairMeasure := by
      exact measurePreserving_eval
        (fun _ : Fin d => complexGaussianPairMeasure) ai
    rw [show
      cov[realGaussianCoordinate d (ai, ak),
          realGaussianCoordinate d (ai, bk);
          complexGaussianVectorMeasure (Fin d)] =
        cov[pairRealCoordinate ak, pairRealCoordinate bk;
          complexGaussianPairMeasure] by
      change cov[pairRealCoordinate ak ∘ (fun ω : Fin d → ℝ × ℝ => ω ai),
          pairRealCoordinate bk ∘ (fun ω : Fin d → ℝ × ℝ => ω ai);
          complexGaussianVectorMeasure (Fin d)] = _
      rw [← covariance_map
        (measurable_pairRealCoordinate ak).aestronglyMeasurable
        (measurable_pairRealCoordinate bk).aestronglyMeasurable
        heval.aemeasurable, heval.map_eq]]
    fin_cases ak <;> fin_cases bk
    · rw [if_pos rfl,
        covariance_self (measurable_pairRealCoordinate _).aemeasurable]
      change Var[fun p : ℝ × ℝ => p.1; complexGaussianPairMeasure] = 1 / 2
      rw [← variance_id_map measurable_fst.aemeasurable,
        complexGaussianPairMeasure,
        (measurePreserving_fst
          (μ := realGaussianHalf) (ν := realGaussianHalf)).map_eq,
        realGaussianHalf,
        variance_id_gaussianReal]
      rfl
    · rw [if_neg (by simp)]
      change cov[fun p : ℝ × ℝ => p.1, fun p => p.2;
        realGaussianHalf.prod realGaussianHalf] = 0
      exact covariance_fst_snd_prod
        (X := id) (Y := id)
        (memLp_id_gaussianReal 2)
        (memLp_id_gaussianReal 2)
    · rw [if_neg (by simp)]
      change cov[fun p : ℝ × ℝ => p.2, fun p => p.1;
        realGaussianHalf.prod realGaussianHalf] = 0
      rw [covariance_comm]
      exact covariance_fst_snd_prod
        (X := id) (Y := id)
        (memLp_id_gaussianReal 2)
        (memLp_id_gaussianReal 2)
    · rw [if_pos rfl,
        covariance_self (measurable_pairRealCoordinate _).aemeasurable]
      change Var[fun p : ℝ × ℝ => p.2; complexGaussianPairMeasure] = 1 / 2
      rw [← variance_id_map measurable_snd.aemeasurable,
        complexGaussianPairMeasure,
        (measurePreserving_snd
          (μ := realGaussianHalf) (ν := realGaussianHalf)).map_eq,
        realGaussianHalf,
        variance_id_gaussianReal]
      rfl
  · have hab : (ai, ak) ≠ (bi, bk) :=
      fun h => hab₁ (congrArg Prod.fst h)
    rw [if_neg hab]
    have hi :=
      (iIndepFun_pi
        (X := fun _ : Fin d => id)
        (μ := fun _ : Fin d => complexGaussianPairMeasure)
        (fun _ => aemeasurable_id)).indepFun hab₁
    have hc := hi.comp
      (measurable_pairRealCoordinate ak)
      (measurable_pairRealCoordinate bk)
    exact hc.covariance_eq_zero
      (memLp_realGaussianCoordinate d (ai, ak))
      (memLp_realGaussianCoordinate d (bi, bk))

theorem integral_realGaussianCoordinate
    (d : ℕ) (a : Fin d × Fin 2) :
    (∫ ω, realGaussianCoordinate d a ω
      ∂complexGaussianVectorMeasure (Fin d)) = 0 := by
  rcases a with ⟨i, k⟩
  fin_cases k
  · change (∫ ω : Fin d → ℝ × ℝ,
      pairRealCoordinate 0 (ω i)
      ∂Measure.pi (fun _ : Fin d => complexGaussianPairMeasure)) = 0
    rw [integral_comp_eval
      (measurable_pairRealCoordinate 0).aestronglyMeasurable]
    change (∫ p : ℝ × ℝ, p.1
      ∂realGaussianHalf.prod realGaussianHalf) = 0
    calc
      _ = (realGaussianHalf.real Set.univ) •
          ∫ x : ℝ, id x ∂realGaussianHalf := by
        simpa using
          (integral_fun_fst (μ := realGaussianHalf)
            (ν := realGaussianHalf) (f := id))
      _ = 0 := by simp [realGaussianHalf]
  · change (∫ ω : Fin d → ℝ × ℝ,
      pairRealCoordinate 1 (ω i)
      ∂Measure.pi (fun _ : Fin d => complexGaussianPairMeasure)) = 0
    rw [integral_comp_eval
      (measurable_pairRealCoordinate 1).aestronglyMeasurable]
    change (∫ p : ℝ × ℝ, p.2
      ∂realGaussianHalf.prod realGaussianHalf) = 0
    calc
      _ = (realGaussianHalf.real Set.univ) •
          ∫ x : ℝ, id x ∂realGaussianHalf := by
        simpa using
          (integral_fun_snd (μ := realGaussianHalf)
            (ν := realGaussianHalf) (f := id))
      _ = 0 := by simp [realGaussianHalf]

noncomputable def realGaussianCoordinatesMeasure (d : ℕ) :
    Measure (EuclideanSpace ℝ (Fin d × Fin 2)) :=
  (complexGaussianVectorMeasure (Fin d)).map
    (realGaussianCoordinatesCLM d)

noncomputable instance isProbabilityMeasure_realGaussianCoordinatesMeasure
    (d : ℕ) :
    IsProbabilityMeasure (realGaussianCoordinatesMeasure d) := by
  unfold realGaussianCoordinatesMeasure
  exact Measure.isProbabilityMeasure_map
    (realGaussianCoordinatesCLM d).measurable.aemeasurable

noncomputable instance isGaussian_realGaussianCoordinatesMeasure
    (d : ℕ) :
    IsGaussian (realGaussianCoordinatesMeasure d) := by
  unfold realGaussianCoordinatesMeasure
  exact isGaussian_map (realGaussianCoordinatesCLM d)

theorem integral_id_realGaussianCoordinatesMeasure (d : ℕ) :
    ∫ x, x ∂realGaussianCoordinatesMeasure d = 0 := by
  apply PiLp.ext
  intro a
  rw [MeasureTheory.eval_integral_piLp]
  · unfold realGaussianCoordinatesMeasure
    rw [integral_map (realGaussianCoordinatesCLM d).measurable.aemeasurable
      (by fun_prop)]
    exact integral_realGaussianCoordinate d a
  · intro i
    exact IsGaussian.integrable_id.eval_piLp i

theorem covarianceBilin_realGaussianCoordinatesMeasure (d : ℕ) :
    covarianceBilin (realGaussianCoordinatesMeasure d) =
      (1 / 2 : ℝ) • innerSL ℝ := by
  change covarianceBilin
      ((complexGaussianVectorMeasure (Fin d)).map
        (fun ω => WithLp.toLp 2
          (fun a => realGaussianCoordinate d a ω))) =
    (1 / 2 : ℝ) • innerSL ℝ
  ext x y
  rw [covarianceBilin_apply_pi
    (fun a => memLp_realGaussianCoordinate d a)]
  simp_rw [covariance_realGaussianCoordinate]
  simp only [smul_apply, one_div]
  classical
  simp
  rw [innerSL_apply_apply, PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp
  ring

theorem map_realGaussianCoordinatesMeasure_linearIsometryEquiv
    (d : ℕ)
    (L : EuclideanSpace ℝ (Fin d × Fin 2) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin d × Fin 2)) :
    (realGaussianCoordinatesMeasure d).map L =
      realGaussianCoordinatesMeasure d := by
  change (realGaussianCoordinatesMeasure d).map
      (L : EuclideanSpace ℝ (Fin d × Fin 2) →L[ℝ]
        EuclideanSpace ℝ (Fin d × Fin 2)) =
    realGaussianCoordinatesMeasure d
  apply IsGaussian.ext
  · change (∫ x, x
        ∂(realGaussianCoordinatesMeasure d).map
          (L : EuclideanSpace ℝ (Fin d × Fin 2) →L[ℝ]
            EuclideanSpace ℝ (Fin d × Fin 2))) =
      ∫ x, x ∂realGaussianCoordinatesMeasure d
    calc
      _ = L (∫ x, x ∂realGaussianCoordinatesMeasure d) :=
        L.toContinuousLinearEquiv.toContinuousLinearMap.integral_id_map
          IsGaussian.integrable_id
      _ = 0 := by rw [integral_id_realGaussianCoordinatesMeasure, map_zero]
      _ = ∫ x, x ∂realGaussianCoordinatesMeasure d :=
        (integral_id_realGaussianCoordinatesMeasure d).symm
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_realGaussianCoordinatesMeasure]
    simp only [smul_apply]
    rw [L.adjoint_eq_symm]
    exact congrArg ((1 / 2 : ℝ) * ·)
      (L.symm.inner_map_map u v)

/-- The real-imaginary orthonormal coordinate identification
`ℝ^(d × 2) ≃ ℂ^d`. -/
noncomputable def realToComplexEuclidean (d : ℕ) :
    EuclideanSpace ℝ (Fin d × Fin 2) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : Fin d => ℂ) :=
  (Pi.orthonormalBasis
    (fun _ : Fin d => Complex.orthonormalBasisOneI)).reindex
      (Equiv.sigmaEquivProd (Fin d) (Fin 2)) |>.repr.symm

theorem realToComplexEuclidean_realGaussianCoordinates
    (d : ℕ) (ω : Fin d → ℝ × ℝ) :
    realToComplexEuclidean d (realGaussianCoordinatesCLM d ω) =
      WithLp.toLp 2 (complexGaussianVector ω) := by
  apply (Pi.orthonormalBasis
    (fun _ : Fin d => Complex.orthonormalBasisOneI)).reindex
      (Equiv.sigmaEquivProd (Fin d) (Fin 2)) |>.repr.injective
  ext a
  rcases a with ⟨i, k⟩
  fin_cases k
  all_goals
    simp [realToComplexEuclidean, realGaussianCoordinate,
      Pi.orthonormalBasis_repr,
      Complex.orthonormalBasisOneI_repr_apply,
      complexGaussianVector, complexGaussianCoordinate,
      complexGaussianOfPair, pairRealCoordinate]

noncomputable def complexGaussianEuclideanMeasure (d : ℕ) :
    Measure (EuclideanSpace ℂ (Fin d)) :=
  (complexGaussianVectorMeasure (Fin d)).map
    (fun ω => WithLp.toLp 2 (complexGaussianVector ω))

theorem complexGaussianEuclideanMeasure_eq_map_real
    (d : ℕ) :
    complexGaussianEuclideanMeasure d =
      (realGaussianCoordinatesMeasure d).map
        (realToComplexEuclidean d) := by
  unfold complexGaussianEuclideanMeasure realGaussianCoordinatesMeasure
  rw [Measure.map_map
    (realToComplexEuclidean d).continuous.measurable
    (realGaussianCoordinatesCLM d).measurable]
  congr 1
  funext ω
  exact
    (realToComplexEuclidean_realGaussianCoordinates d ω).symm

noncomputable def unitaryEuclideanLinearIsometryEquiv
    (d : ℕ) (W : Matrix.unitaryGroup (Fin d) ℂ) :
    EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin d) :=
  Unitary.linearIsometryEquiv
    (Unitary.map
      (StarMonoidHom.ofClass
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))) W)

@[simp] theorem unitaryEuclideanLinearIsometryEquiv_apply
    (d : ℕ) (W : Matrix.unitaryGroup (Fin d) ℂ)
    (x : Fin d → ℂ) :
    unitaryEuclideanLinearIsometryEquiv d W
        (WithLp.toLp 2 x) =
      WithLp.toLp 2 (unitaryVectorAction d W x) := by
  change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
      (W : CMatrix (Fin d))
      (WithLp.toLp 2 x) =
    WithLp.toLp 2 (unitaryVectorAction d W x)
  rw [Matrix.toEuclideanCLM_toLp]
  rfl

noncomputable def complexLinearIsometryEquivRestrictReal
    {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    (L : E ≃ₗᵢ[ℂ] E) : E ≃ₗᵢ[ℝ] E :=
  { L.toLinearEquiv.restrictScalars ℝ with
    norm_map' := L.norm_map }

@[simp] theorem complexLinearIsometryEquivRestrictReal_apply
    {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E]
    (L : E ≃ₗᵢ[ℂ] E) (x : E) :
    complexLinearIsometryEquivRestrictReal L x = L x := rfl

theorem map_unitary_complexGaussianEuclideanMeasure
    (d : ℕ) (W : Matrix.unitaryGroup (Fin d) ℂ) :
    (complexGaussianEuclideanMeasure d).map
        (unitaryEuclideanLinearIsometryEquiv d W) =
      complexGaussianEuclideanMeasure d := by
  let e := realToComplexEuclidean d
  let uR := complexLinearIsometryEquivRestrictReal
    (unitaryEuclideanLinearIsometryEquiv d W)
  let K : EuclideanSpace ℝ (Fin d × Fin 2) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin d × Fin 2) :=
    e.trans (uR.trans e.symm)
  rw [complexGaussianEuclideanMeasure_eq_map_real]
  calc
    ((realGaussianCoordinatesMeasure d).map e).map uR =
        (realGaussianCoordinatesMeasure d).map (e.trans uR) := by
      rw [Measure.map_map uR.continuous.measurable
        e.continuous.measurable]
      rfl
    _ = ((realGaussianCoordinatesMeasure d).map K).map e := by
      rw [Measure.map_map e.continuous.measurable
        K.continuous.measurable]
      congr 1
      funext x
      simp [K, e, uR]
    _ = (realGaussianCoordinatesMeasure d).map e := by
      rw [map_realGaussianCoordinatesMeasure_linearIsometryEquiv d K]

noncomputable def complexGaussianRawMeasure (d : ℕ) :
    Measure (Fin d → ℂ) :=
  (complexGaussianVectorMeasure (Fin d)).map
    (complexGaussianVector :
      (Fin d → ℝ × ℝ) → (Fin d → ℂ))

noncomputable instance isProbabilityMeasure_complexGaussianRawMeasure
    (d : ℕ) :
    IsProbabilityMeasure (complexGaussianRawMeasure d) := by
  unfold complexGaussianRawMeasure
  exact Measure.isProbabilityMeasure_map
    measurable_complexGaussianVector.aemeasurable

theorem complexGaussianEuclideanMeasure_eq_map_raw
    (d : ℕ) :
    complexGaussianEuclideanMeasure d =
      (complexGaussianRawMeasure d).map
        (MeasurableEquiv.toLp 2 (Fin d → ℂ)) := by
  unfold complexGaussianEuclideanMeasure complexGaussianRawMeasure
  rw [Measure.map_map
    (MeasurableEquiv.toLp 2 (Fin d → ℂ)).measurable
    measurable_complexGaussianVector]
  rfl

theorem map_unitary_complexGaussianRawMeasure
    (d : ℕ) (W : Matrix.unitaryGroup (Fin d) ℂ) :
    (complexGaussianRawMeasure d).map
        (unitaryVectorAction d W) =
      complexGaussianRawMeasure d := by
  let eLp := MeasurableEquiv.toLp 2 (Fin d → ℂ)
  apply eLp.map_measurableEquiv_injective
  calc
    ((complexGaussianRawMeasure d).map
        (unitaryVectorAction d W)).map eLp =
      ((complexGaussianRawMeasure d).map eLp).map
        (unitaryEuclideanLinearIsometryEquiv d W) := by
      rw [Measure.map_map eLp.measurable
        (measurable_unitaryVectorAction d W),
        Measure.map_map
          (unitaryEuclideanLinearIsometryEquiv d W).continuous.measurable
          eLp.measurable]
      congr 1
    _ = (complexGaussianEuclideanMeasure d).map
        (unitaryEuclideanLinearIsometryEquiv d W) := by
      rw [← complexGaussianEuclideanMeasure_eq_map_raw]
    _ = complexGaussianEuclideanMeasure d :=
      map_unitary_complexGaussianEuclideanMeasure d W
    _ = (complexGaussianRawMeasure d).map eLp :=
      complexGaussianEuclideanMeasure_eq_map_raw d

theorem vectorNormSq_unitaryVectorAction
    (d : ℕ) (W : Matrix.unitaryGroup (Fin d) ℂ)
    (x : Fin d → ℂ) :
    vectorNormSq (unitaryVectorAction d W x) =
      vectorNormSq x := by
  have hnorm :=
    (unitaryEuclideanLinearIsometryEquiv d W).norm_map
      (WithLp.toLp 2 x)
  have hsq := congrArg (fun r : ℝ => r ^ 2) hnorm
  simp only [EuclideanSpace.norm_sq_eq] at hsq
  simpa [vectorNormSq, Complex.normSq_eq_norm_sq] using hsq

def unitNormalizeComplexVector
    {ι : Type*} [Fintype ι] (x : ι → ℂ) : ι → ℂ :=
  fun i =>
    ((1 / Real.sqrt (vectorNormSq x) : ℝ) : ℂ) * x i

theorem measurable_unitNormalizeComplexVector
    {ι : Type*} [Fintype ι] :
    Measurable
      (unitNormalizeComplexVector : (ι → ℂ) → (ι → ℂ)) := by
  apply measurable_pi_lambda
  intro i
  have hv :
      Measurable (fun x : ι → ℂ => vectorNormSq x) := by
    unfold vectorNormSq
    fun_prop
  exact
    (Complex.measurable_ofReal.comp
      (measurable_const.div
        (Real.continuous_sqrt.measurable.comp
          hv))).mul
      (measurable_pi_apply i)

theorem unitNormalizeComplexVector_complexGaussianVector
    (d : ℕ) (ω : Fin d → ℝ × ℝ) :
    unitNormalizeComplexVector (complexGaussianVector ω) =
      complexGaussianDirection ω := by
  funext i
  simp only [unitNormalizeComplexVector,
    complexGaussianDirection]
  rw [vectorNormSq_complexGaussianVector]

theorem unitaryVectorAction_unitNormalizeComplexVector
    (d : ℕ) (W : Matrix.unitaryGroup (Fin d) ℂ)
    (x : Fin d → ℂ) :
    unitaryVectorAction d W (unitNormalizeComplexVector x) =
      unitNormalizeComplexVector (unitaryVectorAction d W x) := by
  funext i
  simp only [unitaryVectorAction, unitNormalizeComplexVector,
    vectorNormSq_unitaryVectorAction]
  calc
    (∑ j : Fin d,
      (W : CMatrix (Fin d)) i j *
        (((1 / Real.sqrt (vectorNormSq x) : ℝ) : ℂ) * x j)) =
      ∑ j : Fin d,
        (((1 / Real.sqrt (vectorNormSq x) : ℝ) : ℂ) *
          ((W : CMatrix (Fin d)) i j * x j)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (((1 / Real.sqrt (vectorNormSq x) : ℝ) : ℂ) *
        ∑ j : Fin d, (W : CMatrix (Fin d)) i j * x j) := by
      rw [Finset.mul_sum]

theorem complexGaussianDirectionMeasure_eq_map_raw
    (d : ℕ) :
    complexGaussianDirectionMeasure d =
      (complexGaussianRawMeasure d).map
        (unitNormalizeComplexVector :
          (Fin d → ℂ) → (Fin d → ℂ)) := by
  unfold complexGaussianDirectionMeasure complexGaussianRawMeasure
  rw [Measure.map_map measurable_unitNormalizeComplexVector
    measurable_complexGaussianVector]
  congr 1
  funext ω
  exact
    (unitNormalizeComplexVector_complexGaussianVector d ω).symm

theorem map_unitary_complexGaussianDirectionMeasure
    (d : ℕ) (W : Matrix.unitaryGroup (Fin d) ℂ) :
    (complexGaussianDirectionMeasure d).map
        (unitaryVectorAction d W) =
      complexGaussianDirectionMeasure d := by
  rw [complexGaussianDirectionMeasure_eq_map_raw]
  calc
    ((complexGaussianRawMeasure d).map
        unitNormalizeComplexVector).map
        (unitaryVectorAction d W) =
      ((complexGaussianRawMeasure d).map
        (unitaryVectorAction d W)).map
        unitNormalizeComplexVector := by
      rw [Measure.map_map
        (measurable_unitaryVectorAction d W)
        measurable_unitNormalizeComplexVector,
        Measure.map_map measurable_unitNormalizeComplexVector
          (measurable_unitaryVectorAction d W)]
      congr 1
      funext x
      exact unitaryVectorAction_unitNormalizeComplexVector d W x
    _ = (complexGaussianRawMeasure d).map
        unitNormalizeComplexVector := by
      rw [map_unitary_complexGaussianRawMeasure d W]

theorem exists_unitaryColumn_eq_of_vectorNormSq_eq_one
    (d : ℕ) (a : Fin d) (x : Fin d → ℂ)
    (hx : vectorNormSq x = 1) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      unitaryColumn d a U = x := by
  let vx : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 x
  have hvx_sq : ‖vx‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [vx, vectorNormSq, Complex.normSq_eq_norm_sq] using hx
  have hvx : ‖vx‖ = 1 := by
    nlinarith [norm_nonneg vx]
  let v : Fin d → EuclideanSpace ℂ (Fin d) := fun _ => vx
  have hv : Orthonormal ℂ
      (({a} : Set (Fin d)).restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : Fin d) = a :=
      Set.mem_singleton_iff.mp i.property
    have hj : (j : Fin d) = a :=
      Set.mem_singleton_iff.mp j.property
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    simp [Set.restrict_apply, v, hij, hvx]
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq
      (ι := Fin d) (E := EuclideanSpace ℂ (Fin d))
      (by simp [finrank_euclideanSpace])
  let M : CMatrix (Fin d) :=
    (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b
  let U : Matrix.unitaryGroup (Fin d) ℂ :=
    ⟨M,
      (EuclideanSpace.basisFun (Fin d) ℂ)
        |>.toMatrix_orthonormalBasis_mem_unitary b⟩
  refine ⟨U, ?_⟩
  funext i
  change M i a = x i
  rw [show M i a =
      (EuclideanSpace.basisFun (Fin d) ℂ).repr (b a) i by
    rfl]
  rw [hb a (by simp)]
  simp [v, vx]

theorem unitaryVectorAction_assoc
    (d : ℕ) (U W : Matrix.unitaryGroup (Fin d) ℂ)
    (x : Fin d → ℂ) :
    unitaryVectorAction d U (unitaryVectorAction d W x) =
      unitaryVectorAction d (U * W) x := by
  funext i
  change
    ∑ j : Fin d, (U : CMatrix (Fin d)) i j *
      (∑ k : Fin d, (W : CMatrix (Fin d)) j k * x k) =
    ∑ k : Fin d,
      ((U : CMatrix (Fin d)) * (W : CMatrix (Fin d))) i k * x k
  simp_rw [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext k
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem exists_unitaryVectorAction_eq_of_unit
    (d : ℕ) (a : Fin d) (x y : Fin d → ℂ)
    (hx : vectorNormSq x = 1) (hy : vectorNormSq y = 1) :
    ∃ W : Matrix.unitaryGroup (Fin d) ℂ,
      unitaryVectorAction d W x = y := by
  obtain ⟨Ux, hUx⟩ :=
    exists_unitaryColumn_eq_of_vectorNormSq_eq_one d a x hx
  obtain ⟨Uy, hUy⟩ :=
    exists_unitaryColumn_eq_of_vectorNormSq_eq_one d a y hy
  refine ⟨Uy * Ux⁻¹, ?_⟩
  rw [← hUx, unitaryVectorAction_unitaryColumn]
  simpa using hUy

theorem measurable_unitaryVectorAction_joint (d : ℕ) :
    Measurable
      (fun p : Matrix.unitaryGroup (Fin d) ℂ × (Fin d → ℂ) =>
        unitaryVectorAction d p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  unfold unitaryVectorAction
  apply Finset.measurable_sum
  intro j _
  apply Measurable.mul
  · have hi :
        Continuous (fun U : CMatrix (Fin d) => U i) :=
      continuous_apply i
    have hij :
        Continuous (fun U : CMatrix (Fin d) => U i j) :=
      (continuous_apply j).comp hi
    exact ((hij.comp continuous_subtype_val).measurable).comp
      measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

def unitaryOrbitIndicator (d : ℕ)
    (s : Set (Fin d → ℂ))
    (U : Matrix.unitaryGroup (Fin d) ℂ)
    (x : Fin d → ℂ) : ℝ≥0∞ :=
  s.indicator (fun _ => 1) (unitaryVectorAction d U x)

theorem measurable_unitaryOrbitIndicator
    (d : ℕ) {s : Set (Fin d → ℂ)}
    (hs : MeasurableSet s) :
    Measurable
      (Function.uncurry (unitaryOrbitIndicator d s)) := by
  exact (measurable_const.indicator hs).comp
    (measurable_unitaryVectorAction_joint d)

theorem lintegral_unitaryOrbitIndicator_eq_of_unit
    (d : ℕ) (a : Fin d) {s : Set (Fin d → ℂ)}
    (hs : MeasurableSet s)
    (x y : Fin d → ℂ)
    (hx : vectorNormSq x = 1) (hy : vectorNormSq y = 1) :
    (∫⁻ U, unitaryOrbitIndicator d s U x
      ∂unitaryHaarMeasure d) =
    ∫⁻ U, unitaryOrbitIndicator d s U y
      ∂unitaryHaarMeasure d := by
  obtain ⟨W, hW⟩ :=
    exists_unitaryVectorAction_eq_of_unit d a x y hx hy
  let R :=
    fun U : Matrix.unitaryGroup (Fin d) ℂ => U * W
  have hRmeas : Measurable R := by
    dsimp [R]
    fun_prop
  have hmap :
      (unitaryHaarMeasure d).map R =
        unitaryHaarMeasure d :=
    Measure.IsMulRightInvariant.map_mul_right_eq_self W
  have hg :
      Measurable
        (fun U : Matrix.unitaryGroup (Fin d) ℂ =>
          unitaryOrbitIndicator d s U x) := by
    exact (measurable_const.indicator hs).comp
      ((measurable_unitaryVectorAction_joint d).comp
        (measurable_id.prodMk measurable_const))
  calc
    (∫⁻ U, unitaryOrbitIndicator d s U x
      ∂unitaryHaarMeasure d) =
      ∫⁻ U, unitaryOrbitIndicator d s (U * W) x
        ∂unitaryHaarMeasure d := by
      rw [← lintegral_map hg hRmeas, hmap]
    _ = ∫⁻ U, unitaryOrbitIndicator d s U y
        ∂unitaryHaarMeasure d := by
      apply lintegral_congr
      intro U
      unfold unitaryOrbitIndicator
      rw [← hW, unitaryVectorAction_assoc]

theorem measure_apply_eq_unitaryOrbitIntegral
    (d : ℕ) (a : Fin d)
    (μ : Measure (Fin d → ℂ)) [IsProbabilityMeasure μ]
    (hinv : ∀ W : Matrix.unitaryGroup (Fin d) ℂ,
      μ.map (unitaryVectorAction d W) = μ)
    (hsphere : ∀ᵐ x ∂μ, vectorNormSq x = 1)
    {s : Set (Fin d → ℂ)} (hs : MeasurableSet s) :
    μ s =
      ∫⁻ U, unitaryOrbitIndicator d s U
        (unitaryColumn d a
          (1 : Matrix.unitaryGroup (Fin d) ℂ))
        ∂unitaryHaarMeasure d := by
  let x₀ :=
    unitaryColumn d a
      (1 : Matrix.unitaryGroup (Fin d) ℂ)
  have hx₀ : vectorNormSq x₀ = 1 :=
    vectorNormSq_unitaryColumn d a 1
  have hinner :
      ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
        (∫⁻ x, unitaryOrbitIndicator d s U x ∂μ) = μ s := by
    intro U
    have haction :
        Measurable (unitaryVectorAction d U) :=
      measurable_unitaryVectorAction d U
    calc
      (∫⁻ x, unitaryOrbitIndicator d s U x ∂μ) =
          μ ((unitaryVectorAction d U) ⁻¹' s) := by
        rw [← lintegral_indicator_one
          (hs.preimage haction)]
        apply lintegral_congr
        intro x
        rfl
      _ = (μ.map (unitaryVectorAction d U)) s := by
        rw [Measure.map_apply haction hs]
      _ = μ s := by rw [hinv U]
  calc
    μ s =
        ∫⁻ U : Matrix.unitaryGroup (Fin d) ℂ, μ s
          ∂unitaryHaarMeasure d := by simp
    _ = ∫⁻ U, ∫⁻ x, unitaryOrbitIndicator d s U x ∂μ
          ∂unitaryHaarMeasure d := by
      apply lintegral_congr
      intro U
      exact (hinner U).symm
    _ = ∫⁻ x, ∫⁻ U, unitaryOrbitIndicator d s U x
          ∂unitaryHaarMeasure d ∂μ := by
      exact lintegral_lintegral_swap
        (measurable_unitaryOrbitIndicator d hs).aemeasurable
    _ = ∫⁻ _x, ∫⁻ U, unitaryOrbitIndicator d s U x₀
          ∂unitaryHaarMeasure d ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hsphere] with x hx
      exact lintegral_unitaryOrbitIndicator_eq_of_unit
        d a hs x x₀ hx hx₀
    _ = ∫⁻ U, unitaryOrbitIndicator d s U x₀
          ∂unitaryHaarMeasure d := by simp

theorem invariant_unitSphere_probability_unique
    (d : ℕ) (a : Fin d)
    (μ ν : Measure (Fin d → ℂ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hinvμ : ∀ W : Matrix.unitaryGroup (Fin d) ℂ,
      μ.map (unitaryVectorAction d W) = μ)
    (hinvν : ∀ W : Matrix.unitaryGroup (Fin d) ℂ,
      ν.map (unitaryVectorAction d W) = ν)
    (hsphereμ : ∀ᵐ x ∂μ, vectorNormSq x = 1)
    (hsphereν : ∀ᵐ x ∂ν, vectorNormSq x = 1) :
    μ = ν := by
  ext s hs
  rw [measure_apply_eq_unitaryOrbitIntegral
        d a μ hinvμ hsphereμ hs,
      measure_apply_eq_unitaryOrbitIntegral
        d a ν hinvν hsphereν hs]

theorem complexGaussianDirectionMeasure_eq_haarColumnMeasure
    (d : ℕ) (hd : 0 < d) (a : Fin d) :
    complexGaussianDirectionMeasure d =
      haarColumnMeasure d a := by
  exact invariant_unitSphere_probability_unique d a
    (complexGaussianDirectionMeasure d)
    (haarColumnMeasure d a)
    (map_unitary_complexGaussianDirectionMeasure d)
    (fun W => map_unitaryVectorAction_haarColumnMeasure d W a)
    (ae_vectorNormSq_complexGaussianDirectionMeasure_eq_one d hd)
    (ae_vectorNormSq_haarColumnMeasure d a)

end

end QuantumSep
