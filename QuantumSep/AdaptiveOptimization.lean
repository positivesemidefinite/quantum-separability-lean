import QuantumSep.PhysicalOptimization
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Measurable fresh-coin semantics for adaptive optimization

This file supplies the joint measurability and random-input probability
statements needed to invoke the product optimizer at directions determined by
earlier random outputs.
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace

noncomputable section

/-- A Hermitian unit-ball query for the separable support oracle.  The
subtype carries exactly the deterministic preconditions of the optimizer;
its measurable structure is inherited from the finite-dimensional Hilbert
space. -/
def SeparableOracleQuery (d : ℕ) :=
  {A : MatrixHilbert d //
    (matrixOfHilbert d A).IsHermitian ∧ ‖A‖ ≤ 1}

instance (d : ℕ) : MeasurableSpace (SeparableOracleQuery d) :=
  MeasurableSpace.comap Subtype.val inferInstance

instance (d : ℕ) : Nonempty (SeparableOracleQuery d) := by
  refine ⟨⟨0, ?_, by simp⟩⟩
  change (matrixOfHilbert d 0).IsHermitian
  rw [show matrixOfHilbert d 0 = 0 by rfl]
  exact Matrix.isHermitian_zero

theorem SeparableOracleQuery.hermitian
    {d : ℕ} (A : SeparableOracleQuery d) :
    (matrixOfHilbert d A.1).IsHermitian :=
  A.2.1

theorem SeparableOracleQuery.norm_le
    {d : ℕ} (A : SeparableOracleQuery d) :
    ‖A.1‖ ≤ 1 :=
  A.2.2

theorem SeparableOracleQuery.frobeniusNorm_le
    {d : ℕ} (A : SeparableOracleQuery d) :
    frobeniusNorm (matrixOfHilbert d A.1) ≤ 1 := by
  rw [← matrixHilbertOf_norm,
    matrixHilbertOf_matrixOfHilbert]
  exact A.norm_le

/-- Coordinatewise measurability is enough for a random bipartite matrix to
be measurable as an element of the Frobenius Hilbert space. -/
theorem measurable_matrixHilbertOf
    {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (M : Ω → BipartiteMatrix (Fin d))
    (hM : ∀ i j, Measurable fun ω => M ω i j) :
    Measurable fun ω => matrixHilbertOf d (M ω) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro ij
  exact hM ij.1 ij.2

/-- Every matrix coordinate is a measurable functional on the
finite-dimensional Frobenius Hilbert space. -/
theorem measurable_matrixOfHilbert_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (A : Ω → MatrixHilbert d)
    (hA : Measurable A)
    (i j : Fin d × Fin d) :
    Measurable fun ω => matrixOfHilbert d (A ω) i j := by
  exact
    (PiLp.continuous_apply 2
      (fun _ : ((Fin d × Fin d) × (Fin d × Fin d)) => ℂ)
      (i, j)).measurable.comp hA

theorem measurable_unitary_entry
    (d : ℕ) (i j : Fin d) :
    Measurable fun U : Matrix.unitaryGroup (Fin d) ℂ =>
      (U : CMatrix (Fin d)) i j := by
  have hi :
      Continuous (fun U : CMatrix (Fin d) => U i) :=
    continuous_apply i
  have hij :
      Continuous (fun U : CMatrix (Fin d) => U i j) :=
    (continuous_apply j).comp hi
  exact (hij.comp continuous_subtype_val).measurable

/-- Joint measurability of applying a random unitary to a random vector. -/
theorem measurable_unitaryVectorAction_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ)
    (U : Ω → Matrix.unitaryGroup (Fin d) ℂ)
    (x : Ω → Fin d → ℂ)
    (hU : Measurable U)
    (hx : ∀ i, Measurable fun ω => x ω i)
    (i : Fin d) :
    Measurable fun ω => unitaryVectorAction d (U ω) (x ω) i := by
  unfold unitaryVectorAction
  apply Finset.measurable_sum
  intro j _hj
  exact
    ((measurable_unitary_entry d i j).comp hU).mul (hx j)

/-- Joint measurability of the pure product density matrix produced from two
random coordinate vectors. -/
theorem measurable_productDensityMatrix_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (x y : Ω → Fin d → ℂ)
    (hx : ∀ i, Measurable fun ω => x ω i)
    (hy : ∀ i, Measurable fun ω => y ω i)
    (i j : Fin d × Fin d) :
    Measurable fun ω => productDensityMatrix d (x ω) (y ω) i j := by
  unfold productDensityMatrix productVector
  fun_prop

/-- Matrix-Hilbert-valued version of
`measurable_productDensityMatrix_apply`. -/
theorem measurable_pureProductState
    {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (x y : Ω → Fin d → ℂ)
    (hx : ∀ i, Measurable fun ω => x ω i)
    (hy : ∀ i, Measurable fun ω => y ω i) :
    Measurable fun ω =>
      matrixHilbertOf d (productDensityMatrix d (x ω) (y ω)) :=
  measurable_matrixHilbertOf d _ fun i j =>
    measurable_productDensityMatrix_apply d x y hx hy i j

/-- The pure separable state returned by the direct (bounded-dimensional)
branch, jointly as a function of the query and fresh PTAS coins. -/
def directSeparableOracleOutput
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (z : SeparableOracleQuery d × ptas.Seed) :
    MatrixHilbert d := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let eta := effectiveAccuracy tau
  let gamma := directGamma d
  let kappa := (d : ℝ)
  let mesh := directMesh gamma kappa eta
  let net := explicitComplexDiskNet kappa mesh
    (directMesh_pos
      (by
        dsimp [gamma, directGamma]
        positivity)
      (by
        dsimp [kappa]
        positivity)
      (effectiveAccuracy_pos htau))
  letI : Nonempty (MatrixCSPAlphabet net) :=
    matrixCSPAlphabet_nonempty net (by
      dsimp [kappa]
      positivity)
  let csp :=
    matrixDenseMaxFourCSP net (matrixOfHilbert d z.1.1)
      (directPenalty gamma kappa eta) gamma
      (by
        dsimp [gamma, directGamma]
        positivity)
      (by
        dsimp [kappa]
        positivity)
      (directPenalty_pos (effectiveAccuracy_pos htau)).le
      (directMatrix_entry_bound d hd
        (matrixOfHilbert d z.1.1) z.1.frobeniusNorm_le)
  let assignment :=
    ptas.solve (Fin d) (MatrixCSPAlphabet net) csp
      (directCSPError gamma kappa eta) z.2
  exact matrixHilbertOf d
    (productDensityMatrix d
      (normalizedCSPOutputX net assignment)
      (normalizedCSPOutputY net assignment))

/-- The measurable PTAS core which certifies correctness of the direct
branch. -/
def directSeparableOracleCore
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (z : SeparableOracleQuery d × ptas.Seed) : Prop :=
  directOptimizationCoreSuccess ptas tau htau d hd
    (matrixOfHilbert d z.1.1) z.1.frobeniusNorm_le z.2

set_option maxHeartbeats 1000000 in
theorem measurable_directSeparableOracleOutput
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d) :
    @Measurable
      (SeparableOracleQuery d × ptas.Seed) (MatrixHilbert d)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) ptas.Seed inferInstance
        ptas.seedMeasurableSpace)
      inferInstance
      (directSeparableOracleOutput ptas tau htau d hd) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let eta := effectiveAccuracy tau
  let gamma := directGamma d
  let kappa := (d : ℝ)
  let mesh := directMesh gamma kappa eta
  have hgamma : 0 ≤ gamma := by
    dsimp [gamma, directGamma]
    positivity
  have hkappa : 0 ≤ kappa := by
    dsimp [kappa]
    positivity
  have hpenalty :
      0 ≤ directPenalty gamma kappa eta :=
    (directPenalty_pos (effectiveAccuracy_pos htau)).le
  let net := explicitComplexDiskNet kappa mesh
    (directMesh_pos hgamma hkappa
      (effectiveAccuracy_pos htau))
  letI : Nonempty (MatrixCSPAlphabet net) :=
    matrixCSPAlphabet_nonempty net hkappa
  have hentry (A : SeparableOracleQuery d) :
      ∀ a b c e,
        ‖matrixOfHilbert d A.1 (a, c) (b, e)‖ ≤
          gamma / cardR (ι := Fin d) ^ 2 :=
    directMatrix_entry_bound d hd
      (matrixOfHilbert d A.1) A.frobeniusNorm_le
  let randomCSP : SeparableOracleQuery d →
      DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) :=
    fun A =>
      matrixDenseMaxFourCSP net (matrixOfHilbert d A.1)
        (directPenalty gamma kappa eta) gamma
        hgamma hkappa hpenalty (hentry A)
  have hA : Measurable fun A : SeparableOracleQuery d => A.1 :=
    measurable_subtype_coe
  have hM : ∀ a b c e,
      Measurable fun A : SeparableOracleQuery d =>
        matrixOfHilbert d A.1 (a, c) (b, e) :=
    fun a b c e =>
      measurable_matrixOfHilbert_apply d _ hA (a, c) (b, e)
  have hcsp : @Measurable
      (SeparableOracleQuery d)
      (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net))
      inferInstance
      (denseMaxFourCSPMeasurableSpace
        (Fin d) (MatrixCSPAlphabet net))
      randomCSP := by
    have hcsp0 := measurable_matrixDenseMaxFourCSP net
      (fun A : SeparableOracleQuery d => matrixOfHilbert d A.1)
      (directPenalty gamma kappa eta) gamma
      hgamma hkappa hpenalty hentry
      hM
    simpa only [randomCSP] using hcsp0
  let assignment : SeparableOracleQuery d × ptas.Seed →
      (Fin d → MatrixCSPAlphabet net) :=
    fun z =>
      ptas.solve (Fin d) (MatrixCSPAlphabet net)
        (randomCSP z.1) (directCSPError gamma kappa eta) z.2
  have hpair : @Measurable
      (SeparableOracleQuery d × ptas.Seed)
      (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) × ptas.Seed)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) ptas.Seed inferInstance
        ptas.seedMeasurableSpace)
      (@Prod.instMeasurableSpace
        (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net)) ptas.Seed
        (denseMaxFourCSPMeasurableSpace
          (Fin d) (MatrixCSPAlphabet net))
        ptas.seedMeasurableSpace)
      (fun z => (randomCSP z.1, z.2)) :=
    (hcsp.comp measurable_fst).prodMk measurable_snd
  have hassignment : @Measurable
      (SeparableOracleQuery d × ptas.Seed)
      (Fin d → MatrixCSPAlphabet net)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) ptas.Seed inferInstance
        ptas.seedMeasurableSpace)
      ⊤ assignment :=
    (ptas.solve_jointly_measurable
      (Fin d) (MatrixCSPAlphabet net)
      (directCSPError gamma kappa eta)).comp hpair
  let outputOfAssignment :
      (Fin d → MatrixCSPAlphabet net) → MatrixHilbert d :=
    fun a =>
      matrixHilbertOf d
        (productDensityMatrix d
          (normalizedCSPOutputX net a)
          (normalizedCSPOutputY net a))
  have houtputOfAssignment : @Measurable
      (Fin d → MatrixCSPAlphabet net) (MatrixHilbert d)
      ⊤ inferInstance outputOfAssignment := by
    letI : MeasurableSpace (Fin d → MatrixCSPAlphabet net) := ⊤
    exact Measurable.of_discrete
  have hfinal := houtputOfAssignment.comp hassignment
  have heq :
      directSeparableOracleOutput ptas tau htau d hd =
        outputOfAssignment ∘ assignment := by
    funext z
    unfold directSeparableOracleOutput
    dsimp [outputOfAssignment, assignment, randomCSP,
      eta, gamma, kappa, mesh, net]
  rw [heq]
  exact hfinal

theorem measurableSet_directSeparableOracleCore
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d) :
    @MeasurableSet
      (SeparableOracleQuery d × ptas.Seed)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) ptas.Seed inferInstance
        ptas.seedMeasurableSpace)
      {z | directSeparableOracleCore ptas tau htau d hd z} := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let eta := effectiveAccuracy tau
  let gamma := directGamma d
  let kappa := (d : ℝ)
  let mesh := directMesh gamma kappa eta
  have hgamma : 0 ≤ gamma := by
    dsimp [gamma, directGamma]
    positivity
  have hkappa : 0 ≤ kappa := by
    dsimp [kappa]
    positivity
  have hpenalty :
      0 ≤ directPenalty gamma kappa eta :=
    (directPenalty_pos (effectiveAccuracy_pos htau)).le
  let net := explicitComplexDiskNet kappa mesh
    (directMesh_pos hgamma hkappa
      (effectiveAccuracy_pos htau))
  letI : Nonempty (MatrixCSPAlphabet net) :=
    matrixCSPAlphabet_nonempty net hkappa
  have hentry (A : SeparableOracleQuery d) :
      ∀ a b c e,
        ‖matrixOfHilbert d A.1 (a, c) (b, e)‖ ≤
          gamma / cardR (ι := Fin d) ^ 2 :=
    directMatrix_entry_bound d hd
      (matrixOfHilbert d A.1) A.frobeniusNorm_le
  let randomCSP : SeparableOracleQuery d →
      DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) :=
    fun A =>
      matrixDenseMaxFourCSP net (matrixOfHilbert d A.1)
        (directPenalty gamma kappa eta) gamma
        hgamma hkappa hpenalty (hentry A)
  simpa [directSeparableOracleCore, directOptimizationCoreSuccess,
    randomCSP, eta, gamma, kappa, mesh, net] using
    ptas.independent_success_event_measurable
      (SeparableOracleQuery d) (Fin d) (MatrixCSPAlphabet net)
      (Measure.dirac (Classical.arbitrary (SeparableOracleQuery d)))
      randomCSP (directCSPError gamma kappa eta)

theorem directSeparableOracleOutput_eq
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (A : SeparableOracleQuery d) (seed : ptas.Seed) :
    directSeparableOracleOutput ptas tau htau d hd (A, seed) =
      matrixHilbertOf d
        (productDensityMatrix d
          ((directOptimizationProcedure ptas tau htau d hd
            (matrixOfHilbert d A.1) A.frobeniusNorm_le).run ()
              seed).1
          ((directOptimizationProcedure ptas tau htau d hd
            (matrixOfHilbert d A.1) A.frobeniusNorm_le).run ()
              seed).2) := by
  unfold directSeparableOracleOutput directOptimizationProcedure
  rfl

theorem directSeparableOracleCore_probability
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (A : SeparableOracleQuery d) :
    @Measure.real ptas.Seed ptas.seedMeasurableSpace
      ptas.seedMeasure
      {seed |
        directSeparableOracleCore ptas tau htau d hd (A, seed)} ≥
      5 / 6 := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let eta := effectiveAccuracy tau
  let gamma := directGamma d
  let kappa := (d : ℝ)
  let mesh := directMesh gamma kappa eta
  let net := explicitComplexDiskNet kappa mesh
    (directMesh_pos
      (by
        dsimp [gamma, directGamma]
        positivity)
      (by
        dsimp [kappa]
        positivity)
      (effectiveAccuracy_pos htau))
  letI : Nonempty (MatrixCSPAlphabet net) :=
    matrixCSPAlphabet_nonempty net (by
      dsimp [kappa]
      positivity)
  let csp :=
    matrixDenseMaxFourCSP net (matrixOfHilbert d A.1)
      (directPenalty gamma kappa eta) gamma
      (by
        dsimp [gamma, directGamma]
        positivity)
      (by
        dsimp [kappa]
        positivity)
      (directPenalty_pos (effectiveAccuracy_pos htau)).le
      (directMatrix_entry_bound d hd
        (matrixOfHilbert d A.1) A.frobeniusNorm_le)
  simpa [directSeparableOracleCore, directOptimizationCoreSuccess,
    csp, eta, gamma, kappa, mesh, net] using
    ptas.success (Fin d) (MatrixCSPAlphabet net) csp
      (directCSPError gamma kappa eta)
      (directCSPError_pos
        (by
          dsimp [gamma, directGamma]
          positivity)
        (by
          dsimp [kappa]
          positivity)
        (effectiveAccuracy_pos htau))

theorem directSeparableOracleOutput_mem
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (A : SeparableOracleQuery d) (seed : ptas.Seed) :
    directSeparableOracleOutput ptas tau htau d hd (A, seed) ∈
      separableStates d := by
  let alg :=
    directOptimizationProcedure ptas tau htau d hd
      (matrixOfHilbert d A.1) A.frobeniusNorm_le
  have hnorm :=
    directOptimizationProcedure_output_normalized
      ptas tau htau d hd (matrixOfHilbert d A.1)
        A.frobeniusNorm_le seed
  rw [directSeparableOracleOutput_eq]
  apply pureProductState_mem_separable
  exact
    ⟨(alg.run () seed).1, (alg.run () seed).2,
      hnorm.1, hnorm.2, rfl⟩

/-- A true direct core flag is a pointwise certificate for the support
inequality over the entire separable convex hull. -/
theorem directSeparableOracleCore_correct
    (ptas : DenseMaxFourCSPPTASContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hd : 0 < d)
    (A : SeparableOracleQuery d) (seed : ptas.Seed)
    (hcore :
      directSeparableOracleCore ptas tau htau d hd (A, seed)) :
    ∀ P ∈ separableStates d,
      ⟪A.1, P⟫ ≤
        ⟪A.1,
          directSeparableOracleOutput ptas tau htau d hd
            (A, seed)⟫ + tau := by
  let M := matrixOfHilbert d A.1
  let alg :=
    directOptimizationProcedure ptas tau htau d hd
      M A.frobeniusNorm_le
  have hproduct :=
    directOptimizationProcedure_correct_of_core
      ptas tau htau d hd M A.frobeniusNorm_le seed hcore
  have hnorm :=
    directOptimizationProcedure_output_normalized
      ptas tau htau d hd M A.frobeniusNorm_le seed
  intro P hP
  have hbound :=
    product_quartic_bound_extends_to_separable
      d hd M A.hermitian
      (alg.run () seed).1 (alg.run () seed).2
      hnorm.1 hnorm.2 tau hproduct hP
  rw [directSeparableOracleOutput_eq]
  simpa [M] using hbound

/-- The fixed numerical parameter package used by the high-dimensional
branch at accuracy `tau`. -/
def adaptiveHighParameters
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d) :
    HighDimensionalParameters hc d (mainMomentOrder hc tau) :=
  let hdata := mainDimensionCutoff_data hc htau hlarge
  selectedHighDimensionalParameters hc (mainMomentOrder hc tau)
    (mainDiscretizationAccuracy tau)
    (by
      unfold mainDiscretizationAccuracy
      exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
    d (by simpa using hdata.2.2.1)

/-- The projected correlation matrix constructed from a query and a pair of
Haar samples. -/
def adaptiveHighProjectedMatrix
    (sampler : EfficientHaarSamplingContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (d : ℕ)
    (z : SeparableOracleQuery d ×
      (efficientHaarPairProcedure sampler d).Seed) :
    BipartiteMatrix (Fin d) :=
  let haar := efficientHaarPairProcedure sampler d
  mainProjectedMatrix hc d (matrixOfHilbert d z.1.1)
    (mainMomentOrder hc tau) (haar.run () z.2)

/-- The concrete random CSP obtained from a query and fresh Haar coins. -/
def adaptiveHighCSP
    (sampler : EfficientHaarSamplingContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (z : SeparableOracleQuery d ×
      (efficientHaarPairProcedure sampler d).Seed) :
    DenseMaxFourCSP (Fin d)
      (MatrixCSPAlphabet
        (highDimensionalNet
          (adaptiveHighParameters hc tau htau d hlarge))) := by
  let hdata := mainDimensionCutoff_data hc htau hlarge
  letI : Nonempty (Fin d) := ⟨⟨0, hdata.1⟩⟩
  let p := mainMomentOrder hc tau
  let params := adaptiveHighParameters hc tau htau d hlarge
  let net := highDimensionalNet params
  exact matrixDenseMaxFourCSP net
    (adaptiveHighProjectedMatrix sampler hc tau d z)
    params.penalty (mainCSPGamma hc p)
    (mainCSPGamma_nonneg hc p)
    (by
      have := params.sigma_pos
      positivity)
    params.penalty_pos.le
    (by
      intro a b c e
      simpa [adaptiveHighProjectedMatrix, cardR] using
        mainProjectedMatrix_entry_bound hc d hdata.1
          (matrixOfHilbert d z.1.1) z.1.frobeniusNorm_le
          p ((efficientHaarPairProcedure sampler d).run () z.2)
          a b c e)

/-- The assignment returned by the PTAS on the random high-dimensional
CSP. -/
def adaptiveHighAssignment
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (z : SeparableOracleQuery d ×
      ((efficientHaarPairProcedure sampler d).Seed × ptas.Seed)) :
    Fin d → MatrixCSPAlphabet
      (highDimensionalNet
        (adaptiveHighParameters hc tau htau d hlarge)) :=
  let params := adaptiveHighParameters hc tau htau d hlarge
  letI : Nonempty (MatrixCSPAlphabet (highDimensionalNet params)) :=
    matrixCSPAlphabet_nonempty (highDimensionalNet params) (by
      have := params.sigma_pos
      positivity)
  ptas.solve (Fin d)
    (MatrixCSPAlphabet (highDimensionalNet params))
    (adaptiveHighCSP sampler hc tau htau d hlarge (z.1, z.2.1))
    params.cspError z.2.2

/-- The two rotated vectors returned by the high-dimensional branch. -/
def adaptiveHighOutputVectors
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (z : SeparableOracleQuery d ×
      ((efficientHaarPairProcedure sampler d).Seed × ptas.Seed)) :
    (Fin d → ℂ) × (Fin d → ℂ) :=
  let params := adaptiveHighParameters hc tau htau d hlarge
  let haar := efficientHaarPairProcedure sampler d
  let UV := haar.run () z.2.1
  let assignment :=
    adaptiveHighAssignment sampler ptas hc tau htau d hlarge z
  rotateProductOutput d UV
    (normalizedCSPOutputX (highDimensionalNet params) assignment)
    (normalizedCSPOutputY (highDimensionalNet params) assignment)

/-- The pure separable state returned by the instantiated
high-dimensional branch, jointly as a function of the query, Haar coins, and
PTAS coins. -/
def highSeparableOracleOutput
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (z : SeparableOracleQuery d ×
      ((efficientHaarPairProcedure sampler d).Seed × ptas.Seed)) :
    MatrixHilbert d :=
  matrixHilbertOf d
    (productDensityMatrix d
      (adaptiveHighOutputVectors sampler ptas hc tau htau d hlarge z).1
      (adaptiveHighOutputVectors sampler ptas hc tau htau d hlarge z).2)

/-- The conjunction of the measurable Haar flat-tail event and the
measurable dense-CSP success event for the high-dimensional branch. -/
def highSeparableOracleCore
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (z : SeparableOracleQuery d ×
      ((efficientHaarPairProcedure sampler d).Seed × ptas.Seed)) : Prop :=
  let p := mainMomentOrder hc tau
  let params := adaptiveHighParameters hc tau htau d hlarge
  let haar := efficientHaarPairProcedure sampler d
  let UV := haar.run () z.2.1
  let csp :=
    adaptiveHighCSP sampler hc tau htau d hlarge (z.1, z.2.1)
  HaarFlatTailConclusion d
        (correlationPart (matrixOfHilbert d z.1.1))
        (flatThreshold hc d
          (correlationPart (matrixOfHilbert d z.1.1)) p)
        (mainTailAccuracy tau) UV ∧
      ∀ assignment,
        csp.value assignment ≤
          csp.value
            (adaptiveHighAssignment sampler ptas hc tau htau d hlarge z) +
          params.cspError

/- Moved below the foundational projected-matrix measurability lemmas.
set_option maxHeartbeats 5000000 in
theorem measurable_highSeparableOracleOutput
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d) :
    let haar := efficientHaarPairProcedure sampler d
    @Measurable
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed))
      (MatrixHilbert d)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) (haar.Seed × ptas.Seed)
        inferInstance
        (@Prod.instMeasurableSpace haar.Seed ptas.Seed
          haar.seedMeasurableSpace ptas.seedMeasurableSpace))
      inferInstance
      (highSeparableOracleOutput sampler ptas hc tau htau d hlarge) := by
  dsimp only
  let hdata := mainDimensionCutoff_data hc htau hlarge
  letI : Nonempty (Fin d) := ⟨⟨0, hdata.1⟩⟩
  let p := mainMomentOrder hc tau
  let eta := mainDiscretizationAccuracy tau
  let params :=
    selectedHighDimensionalParameters hc p eta
      (by
        dsimp [eta, mainDiscretizationAccuracy]
        exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
      d (by simpa [p, eta] using hdata.2.2.1)
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  let history := SeparableOracleQuery d × haar.Seed
  let UV : history →
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ :=
    fun z => haar.run () z.2
  have hUV : Measurable UV :=
    (efficientHaarPairProcedure_run_measurable sampler d).comp
      measurable_snd
  have hA : Measurable fun z : history => z.1.1 :=
    measurable_subtype_coe.comp measurable_fst
  let projected : history → BipartiteMatrix (Fin d) :=
    fun z =>
      mainProjectedMatrix hc d (matrixOfHilbert d z.1.1) p (UV z)
  have hMcoord : ∀ a b c e,
      Measurable fun z : history =>
        matrixOfHilbert d z.1.1 (a, c) (b, e) :=
    fun a b c e =>
      measurable_matrixOfHilbert_apply d _ hA (a, c) (b, e)
  have hprojected : ∀ a b c e,
      Measurable fun z : history =>
        projected z (a, c) (b, e) :=
    fun a b c e =>
      measurable_mainProjectedMatrix_apply hc d p
        (fun z => matrixOfHilbert d z.1.1) UV
        hMcoord hUV a b c e
  let net := highDimensionalNet params
  have hgamma : 0 ≤ mainCSPGamma hc p :=
    mainCSPGamma_nonneg hc p
  have hkappa : 0 ≤ 2 * (params.sigma + 1) := by
    have := params.sigma_pos
    positivity
  letI : Nonempty (MatrixCSPAlphabet net) :=
    matrixCSPAlphabet_nonempty net hkappa
  have hpenalty : 0 ≤ params.penalty := params.penalty_pos.le
  have hentry (z : history) :
      ∀ a b c e,
        ‖projected z (a, c) (b, e)‖ ≤
          mainCSPGamma hc p / cardR (ι := Fin d) ^ 2 := by
    intro a b c e
    simpa [projected, cardR] using
      mainProjectedMatrix_entry_bound hc d hdata.1
        (matrixOfHilbert d z.1.1) z.1.frobeniusNorm_le
        p (UV z) a b c e
  let randomCSP : history →
      DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) :=
    fun z =>
      matrixDenseMaxFourCSP net (projected z)
        params.penalty (mainCSPGamma hc p)
        hgamma hkappa hpenalty (hentry z)
  have hcsp : @Measurable history
      (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net))
      inferInstance
      (denseMaxFourCSPMeasurableSpace
        (Fin d) (MatrixCSPAlphabet net))
      randomCSP := by
    omitted
  let sourceToHistory :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) → history :=
    fun z => (z.1, z.2.1)
  have hsourceToHistory : Measurable sourceToHistory :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  let assignment :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) →
        (Fin d → MatrixCSPAlphabet net) :=
    fun z =>
      ptas.solve (Fin d) (MatrixCSPAlphabet net)
        (randomCSP (sourceToHistory z)) params.cspError z.2.2
  have hpair : @Measurable
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed))
      (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) × ptas.Seed)
      inferInstance
      (@Prod.instMeasurableSpace
        (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net)) ptas.Seed
        (denseMaxFourCSPMeasurableSpace
          (Fin d) (MatrixCSPAlphabet net))
        ptas.seedMeasurableSpace)
      (fun z => (randomCSP (sourceToHistory z), z.2.2)) :=
    (hcsp.comp hsourceToHistory).prodMk
      (measurable_snd.comp measurable_snd)
  have hassignment : @Measurable
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed))
      (Fin d → MatrixCSPAlphabet net)
      inferInstance ⊤ assignment :=
    (ptas.solve_jointly_measurable
      (Fin d) (MatrixCSPAlphabet net) params.cspError).comp hpair
  have hx (i : Fin d) :
      Measurable fun z =>
        normalizedCSPOutputX net (assignment z) i := by
    have hdisc : @Measurable
        (Fin d → MatrixCSPAlphabet net) ℂ ⊤ inferInstance
        (fun a => normalizedCSPOutputX net a i) := by
      letI : MeasurableSpace (Fin d → MatrixCSPAlphabet net) := ⊤
      exact Measurable.of_discrete
    exact hdisc.comp hassignment
  have hy (i : Fin d) :
      Measurable fun z =>
        normalizedCSPOutputY net (assignment z) i := by
    have hdisc : @Measurable
        (Fin d → MatrixCSPAlphabet net) ℂ ⊤ inferInstance
        (fun a => normalizedCSPOutputY net a i) := by
      letI : MeasurableSpace (Fin d → MatrixCSPAlphabet net) := ⊤
      exact Measurable.of_discrete
    exact hdisc.comp hassignment
  let sourceUV :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) →
        Matrix.unitaryGroup (Fin d) ℂ ×
          Matrix.unitaryGroup (Fin d) ℂ :=
    fun z => UV (sourceToHistory z)
  have hsourceUV : Measurable sourceUV :=
    hUV.comp hsourceToHistory
  let outputX :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) →
        Fin d → ℂ :=
    fun z =>
      unitaryVectorAction d (sourceUV z).1
        (normalizedCSPOutputX net (assignment z))
  let outputY :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) →
        Fin d → ℂ :=
    fun z =>
      unitaryVectorAction d (sourceUV z).2
        (normalizedCSPOutputY net (assignment z))
  have houtputX : ∀ i, Measurable fun z => outputX z i :=
    fun i =>
      measurable_unitaryVectorAction_apply d
        (fun z => (sourceUV z).1)
        (fun z => normalizedCSPOutputX net (assignment z))
        hsourceUV.fst hx i
  have houtputY : ∀ i, Measurable fun z => outputY z i :=
    fun i =>
      measurable_unitaryVectorAction_apply d
        (fun z => (sourceUV z).2)
        (fun z => normalizedCSPOutputY net (assignment z))
        hsourceUV.snd hy i
  have hfinal :=
    measurable_pureProductState d outputX outputY houtputX houtputY
  have heq :
      highSeparableOracleOutput sampler ptas hc tau htau d hlarge =
        fun z =>
          matrixHilbertOf d
            (productDensityMatrix d (outputX z) (outputY z)) := by
    omitted
  rw [heq]
  exact hfinal
-/

theorem measurable_bipartiteUnitaryConjugate_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ)
    (M : Ω → BipartiteMatrix (Fin d))
    (UV : Ω →
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
    (hM : ∀ a b c e, Measurable fun ω => M ω (a, c) (b, e))
    (hUV : Measurable UV)
    (a b c e : Fin d) :
    Measurable fun ω =>
      bipartiteUnitaryConjugate d (M ω) (UV ω) (a, c) (b, e) := by
  unfold bipartiteUnitaryConjugate
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, tensor]
  apply Finset.measurable_sum
  intro i _hi
  apply Measurable.mul
  · apply Complex.continuous_conj.measurable.comp
    exact
      ((measurable_unitary_entry d i.1 a).comp hUV.fst).mul
        ((measurable_unitary_entry d i.2 c).comp hUV.snd)
  · apply Finset.measurable_sum
    intro j _hj
    apply Measurable.mul
    · exact hM i.1 j.1 i.2 j.2
    · exact
        ((measurable_unitary_entry d j.1 b).comp hUV.fst).mul
          ((measurable_unitary_entry d j.2 e).comp hUV.snd)

theorem measurable_thresholdTail_apply
    {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι]
    (tau : Ω → ℝ) (A : Ω → CMatrix ι)
    (htau : Measurable tau)
    (hA : ∀ i j, Measurable fun ω => A ω i j)
    (i j : ι) :
    Measurable fun ω => thresholdTail (tau ω) (A ω) i j := by
  unfold thresholdTail
  exact (hA i j).ite
    (measurableSet_lt htau (hA i j).norm) measurable_const

theorem measurable_frobeniusSq_of_apply
    {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι]
    (A : Ω → CMatrix ι)
    (hA : ∀ i j, Measurable fun ω => A ω i j) :
    Measurable fun ω => frobeniusSq (A ω) := by
  unfold frobeniusSq
  fun_prop

theorem measurable_frobeniusNorm_of_apply
    {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι]
    (A : Ω → CMatrix ι)
    (hA : ∀ i j, Measurable fun ω => A ω i j) :
    Measurable fun ω => frobeniusNorm (A ω) := by
  unfold frobeniusNorm
  exact (measurable_frobeniusSq_of_apply A hA).sqrt

theorem measurable_correlationPart_apply
    {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Ω → BipartiteMatrix ι)
    (hM : ∀ a b c e, Measurable fun ω => M ω (a, c) (b, e))
    (a b c e : ι) :
    Measurable fun ω => correlationPart (M ω) (a, c) (b, e) := by
  have htrace : Measurable fun ω => (M ω).trace := by
    unfold Matrix.trace
    apply Finset.measurable_sum
    intro i _hi
    exact hM i.1 i.1 i.2 i.2
  have hscalar : Measurable fun ω => scalarPart (M ω) := by
    unfold scalarPart
    fun_prop
  have hpartial0 (c e : ι) :
      Measurable fun ω => partialTrace0 (M ω) c e := by
    unfold partialTrace0
    apply Finset.measurable_sum
    intro i _hi
    exact hM i i c e
  have hpartial1 (a b : ι) :
      Measurable fun ω => partialTrace1 (M ω) a b := by
    unfold partialTrace1
    apply Finset.measurable_sum
    intro i _hi
    exact hM a b i i
  have hlocalA (a b : ι) :
      Measurable fun ω => localA (M ω) a b := by
    unfold localA
    change Measurable fun ω =>
      (dimC (ι := ι))⁻¹ * partialTrace1 (M ω) a b -
        scalarPart (M ω) * (1 : CMatrix ι) a b
    exact
      (measurable_const.mul (hpartial1 a b)).sub
        (hscalar.mul measurable_const)
  have hlocalB (c e : ι) :
      Measurable fun ω => localB (M ω) c e := by
    unfold localB
    change Measurable fun ω =>
      (dimC (ι := ι))⁻¹ * partialTrace0 (M ω) c e -
        scalarPart (M ω) * (1 : CMatrix ι) c e
    exact
      (measurable_const.mul (hpartial0 c e)).sub
        (hscalar.mul measurable_const)
  unfold correlationPart
  change Measurable fun ω =>
    M ω (a, c) (b, e) -
      scalarPart (M ω) *
        tensor (1 : CMatrix ι) (1 : CMatrix ι) (a, c) (b, e) -
      tensor (localA (M ω)) (1 : CMatrix ι) (a, c) (b, e) -
      tensor (1 : CMatrix ι) (localB (M ω)) (a, c) (b, e)
  exact
    (((hM a b c e).sub
      (hscalar.mul measurable_const)).sub
      ((hlocalA a b).mul measurable_const)).sub
      (measurable_const.mul (hlocalB c e))

theorem measurable_mainProjectedMatrix_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (hc : GaussianHypercontractivityContract)
    (d p : ℕ)
    (M : Ω → BipartiteMatrix (Fin d))
    (UV : Ω →
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
    (hM : ∀ a b c e, Measurable fun ω => M ω (a, c) (b, e))
    (hUV : Measurable UV)
    (a b c e : Fin d) :
    Measurable fun ω =>
      mainProjectedMatrix hc d (M ω) p (UV ω) (a, c) (b, e) := by
  let C : Ω → BipartiteMatrix (Fin d) :=
    fun ω => correlationPart (M ω)
  have hC : ∀ a b c e,
      Measurable fun ω => C ω (a, c) (b, e) :=
    fun a b c e => measurable_correlationPart_apply M hM a b c e
  let total : Ω → BipartiteMatrix (Fin d) :=
    fun ω => bipartiteUnitaryConjugate d (C ω) (UV ω)
  have htotal : ∀ a b c e,
      Measurable fun ω => total ω (a, c) (b, e) :=
    fun a b c e =>
      measurable_bipartiteUnitaryConjugate_apply
        d C UV hC hUV a b c e
  let threshold : Ω → ℝ :=
    fun ω => flatThreshold hc d (C ω) p
  have hCnorm : Measurable fun ω => frobeniusNorm (C ω) :=
    measurable_frobeniusNorm_of_apply C
      (fun i j => hC i.1 j.1 i.2 j.2)
  have hthreshold : Measurable threshold := by
    dsimp [threshold, flatThreshold, flatMomentScale]
    fun_prop
  let tail : Ω → BipartiteMatrix (Fin d) :=
    fun ω => thresholdTail (threshold ω) (total ω)
  have htail : ∀ i j, Measurable fun ω => tail ω i j :=
    fun i j =>
      measurable_thresholdTail_apply threshold total hthreshold
        (fun i j => htotal i.1 j.1 i.2 j.2) i j
  let flat : Ω → BipartiteMatrix (Fin d) :=
    fun ω => total ω - tail ω
  have hflat : ∀ a b c e,
      Measurable fun ω => flat ω (a, c) (b, e) := by
    intro a b c e
    exact (htotal a b c e).sub (htail (a, c) (b, e))
  simpa [mainProjectedMatrix, mainFlatMatrix, C, total, threshold,
    tail, flat, haarThresholdFlat, haarThresholdTail,
    thresholdFlat] using
    measurable_correlationPart_apply flat hflat a b c e

/- Superseded by the split measurable pipeline below.
set_option maxHeartbeats 5000000 in
theorem measurable_highSeparableOracleOutput
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d) :
    let haar := efficientHaarPairProcedure sampler d
    @Measurable
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed))
      (MatrixHilbert d)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) (haar.Seed × ptas.Seed)
        inferInstance
        (@Prod.instMeasurableSpace haar.Seed ptas.Seed
          haar.seedMeasurableSpace ptas.seedMeasurableSpace))
      inferInstance
      (highSeparableOracleOutput sampler ptas hc tau htau d hlarge) := by
  dsimp only
  let hdata := mainDimensionCutoff_data hc htau hlarge
  letI : Nonempty (Fin d) := ⟨⟨0, hdata.1⟩⟩
  let p := mainMomentOrder hc tau
  let eta := mainDiscretizationAccuracy tau
  let params :=
    selectedHighDimensionalParameters hc p eta
      (by
        dsimp [eta, mainDiscretizationAccuracy]
        exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
      d (by simpa [p, eta] using hdata.2.2.1)
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  let history := SeparableOracleQuery d × haar.Seed
  let UV : history →
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ :=
    fun z => haar.run () z.2
  have hUV : Measurable UV :=
    (efficientHaarPairProcedure_run_measurable sampler d).comp
      measurable_snd
  have hA : Measurable fun z : history => z.1.1 :=
    measurable_subtype_coe.comp measurable_fst
  let projected : history → BipartiteMatrix (Fin d) :=
    fun z =>
      mainProjectedMatrix hc d (matrixOfHilbert d z.1.1) p (UV z)
  have hMcoord : ∀ a b c e,
      Measurable fun z : history =>
        matrixOfHilbert d z.1.1 (a, c) (b, e) :=
    fun a b c e =>
      measurable_matrixOfHilbert_apply d _ hA (a, c) (b, e)
  have hprojected : ∀ a b c e,
      Measurable fun z : history =>
        projected z (a, c) (b, e) :=
    fun a b c e =>
      measurable_mainProjectedMatrix_apply hc d p
        (fun z => matrixOfHilbert d z.1.1) UV
        hMcoord hUV a b c e
  let net := highDimensionalNet params
  have hgamma : 0 ≤ mainCSPGamma hc p :=
    mainCSPGamma_nonneg hc p
  have hkappa : 0 ≤ 2 * (params.sigma + 1) := by
    have := params.sigma_pos
    positivity
  letI : Nonempty (MatrixCSPAlphabet net) :=
    matrixCSPAlphabet_nonempty net hkappa
  have hpenalty : 0 ≤ params.penalty := params.penalty_pos.le
  have hentry (z : history) :
      ∀ a b c e,
        ‖projected z (a, c) (b, e)‖ ≤
          mainCSPGamma hc p / cardR (ι := Fin d) ^ 2 := by
    intro a b c e
    simpa [projected, cardR] using
      mainProjectedMatrix_entry_bound hc d hdata.1
        (matrixOfHilbert d z.1.1) z.1.frobeniusNorm_le
        p (UV z) a b c e
  let randomCSP : history →
      DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) :=
    fun z =>
      matrixDenseMaxFourCSP net (projected z)
        params.penalty (mainCSPGamma hc p)
        hgamma hkappa hpenalty (hentry z)
  have hcsp : @Measurable history
      (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net))
      inferInstance
      (denseMaxFourCSPMeasurableSpace
        (Fin d) (MatrixCSPAlphabet net))
      randomCSP := by
    omitted
  let sourceToHistory :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) → history :=
    fun z => (z.1, z.2.1)
  have hsourceToHistory : Measurable sourceToHistory :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  let assignment :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) →
        (Fin d → MatrixCSPAlphabet net) :=
    fun z =>
      ptas.solve (Fin d) (MatrixCSPAlphabet net)
        (randomCSP (sourceToHistory z)) params.cspError z.2.2
  have hpair : @Measurable
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed))
      (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) × ptas.Seed)
      inferInstance
      (@Prod.instMeasurableSpace
        (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net)) ptas.Seed
        (denseMaxFourCSPMeasurableSpace
          (Fin d) (MatrixCSPAlphabet net))
        ptas.seedMeasurableSpace)
      (fun z => (randomCSP (sourceToHistory z), z.2.2)) :=
    (hcsp.comp hsourceToHistory).prodMk
      (measurable_snd.comp measurable_snd)
  have hassignment : @Measurable
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed))
      (Fin d → MatrixCSPAlphabet net)
      inferInstance ⊤ assignment :=
    (ptas.solve_jointly_measurable
      (Fin d) (MatrixCSPAlphabet net) params.cspError).comp hpair
  have hx (i : Fin d) :
      Measurable fun z =>
        normalizedCSPOutputX net (assignment z) i := by
    have hdisc : @Measurable
        (Fin d → MatrixCSPAlphabet net) ℂ ⊤ inferInstance
        (fun a => normalizedCSPOutputX net a i) := by
      letI : MeasurableSpace (Fin d → MatrixCSPAlphabet net) := ⊤
      exact Measurable.of_discrete
    exact hdisc.comp hassignment
  have hy (i : Fin d) :
      Measurable fun z =>
        normalizedCSPOutputY net (assignment z) i := by
    have hdisc : @Measurable
        (Fin d → MatrixCSPAlphabet net) ℂ ⊤ inferInstance
        (fun a => normalizedCSPOutputY net a i) := by
      letI : MeasurableSpace (Fin d → MatrixCSPAlphabet net) := ⊤
      exact Measurable.of_discrete
    exact hdisc.comp hassignment
  let sourceUV :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) →
        Matrix.unitaryGroup (Fin d) ℂ ×
          Matrix.unitaryGroup (Fin d) ℂ :=
    fun z => UV (sourceToHistory z)
  have hsourceUV : Measurable sourceUV :=
    hUV.comp hsourceToHistory
  let outputX :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) →
        Fin d → ℂ :=
    fun z =>
      unitaryVectorAction d (sourceUV z).1
        (normalizedCSPOutputX net (assignment z))
  let outputY :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) →
        Fin d → ℂ :=
    fun z =>
      unitaryVectorAction d (sourceUV z).2
        (normalizedCSPOutputY net (assignment z))
  have houtputX : ∀ i, Measurable fun z => outputX z i :=
    fun i =>
      measurable_unitaryVectorAction_apply d
        (fun z => (sourceUV z).1)
        (fun z => normalizedCSPOutputX net (assignment z))
        hsourceUV.fst hx i
  have houtputY : ∀ i, Measurable fun z => outputY z i :=
    fun i =>
      measurable_unitaryVectorAction_apply d
        (fun z => (sourceUV z).2)
        (fun z => normalizedCSPOutputY net (assignment z))
        hsourceUV.snd hy i
  have hfinal :=
    measurable_pureProductState d outputX outputY houtputX houtputY
  have heq :
      highSeparableOracleOutput sampler ptas hc tau htau d hlarge =
        fun z =>
          matrixHilbertOf d
            (productDensityMatrix d (outputX z) (outputY z)) := by
    omitted
  rw [heq]
  exact hfinal
-/

/-- Coordinatewise joint measurability of the projected matrix in the query
and Haar coins. -/
theorem measurable_adaptiveHighProjectedMatrix_apply
    (sampler : EfficientHaarSamplingContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (d : ℕ)
    (a b c e : Fin d) :
    let haar := efficientHaarPairProcedure sampler d
    @Measurable
      (SeparableOracleQuery d × haar.Seed) ℂ
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) haar.Seed inferInstance
        haar.seedMeasurableSpace)
      inferInstance
      (fun z =>
        adaptiveHighProjectedMatrix sampler hc tau d z
          (a, c) (b, e)) := by
  dsimp only
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  let UV : SeparableOracleQuery d × haar.Seed →
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ :=
    fun z => haar.run () z.2
  have hUV : Measurable UV :=
    (efficientHaarPairProcedure_run_measurable sampler d).comp
      measurable_snd
  have hA :
      Measurable fun z : SeparableOracleQuery d × haar.Seed => z.1.1 :=
    measurable_subtype_coe.comp measurable_fst
  have hMcoord : ∀ i j k l,
      Measurable fun z : SeparableOracleQuery d × haar.Seed =>
        matrixOfHilbert d z.1.1 (i, k) (j, l) :=
    fun i j k l =>
      measurable_matrixOfHilbert_apply d _ hA (i, k) (j, l)
  simpa [adaptiveHighProjectedMatrix, UV] using
    measurable_mainProjectedMatrix_apply hc d
      (mainMomentOrder hc tau)
      (fun z : SeparableOracleQuery d × haar.Seed =>
        matrixOfHilbert d z.1.1)
      UV hMcoord hUV a b c e

set_option maxHeartbeats 1000000 in
/-- Joint measurability of the concrete high-dimensional CSP in its query
and Haar coins. -/
theorem measurable_adaptiveHighCSP
    (sampler : EfficientHaarSamplingContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d) :
    let haar := efficientHaarPairProcedure sampler d
    let net := highDimensionalNet
      (adaptiveHighParameters hc tau htau d hlarge)
    @Measurable
      (SeparableOracleQuery d × haar.Seed)
      (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net))
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) haar.Seed inferInstance
        haar.seedMeasurableSpace)
      (denseMaxFourCSPMeasurableSpace
        (Fin d) (MatrixCSPAlphabet net))
      (adaptiveHighCSP sampler hc tau htau d hlarge) := by
  dsimp only
  let hdata := mainDimensionCutoff_data hc htau hlarge
  letI : Nonempty (Fin d) := ⟨⟨0, hdata.1⟩⟩
  let p := mainMomentOrder hc tau
  let params := adaptiveHighParameters hc tau htau d hlarge
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  let projected :
      SeparableOracleQuery d × haar.Seed →
        BipartiteMatrix (Fin d) :=
    adaptiveHighProjectedMatrix sampler hc tau d
  have hprojected : ∀ a b c e,
      Measurable fun z =>
        projected z (a, c) (b, e) :=
    fun a b c e =>
      measurable_adaptiveHighProjectedMatrix_apply
        sampler hc tau d a b c e
  let net := highDimensionalNet params
  have hgamma : 0 ≤ mainCSPGamma hc p :=
    mainCSPGamma_nonneg hc p
  have hkappa : 0 ≤ 2 * (params.sigma + 1) := by
    have := params.sigma_pos
    positivity
  have hpenalty : 0 ≤ params.penalty := params.penalty_pos.le
  have hentry (z : SeparableOracleQuery d × haar.Seed) :
      ∀ a b c e,
        ‖projected z (a, c) (b, e)‖ ≤
          mainCSPGamma hc p / cardR (ι := Fin d) ^ 2 := by
    intro a b c e
    simpa [projected, adaptiveHighProjectedMatrix, cardR] using
      mainProjectedMatrix_entry_bound hc d hdata.1
        (matrixOfHilbert d z.1.1) z.1.frobeniusNorm_le
        p (haar.run () z.2) a b c e
  have hcsp0 := measurable_matrixDenseMaxFourCSP net projected
    params.penalty (mainCSPGamma hc p)
    hgamma hkappa hpenalty hentry hprojected
  have heq :
      adaptiveHighCSP sampler hc tau htau d hlarge =
        fun z =>
          matrixDenseMaxFourCSP net (projected z)
            params.penalty (mainCSPGamma hc p)
            hgamma hkappa hpenalty (hentry z) := by
    funext z
    unfold adaptiveHighCSP
    dsimp [projected, p, params, net]
  rw [heq]
  exact hcsp0

/-- Joint measurability of the PTAS assignment in all fresh high-branch
coins. -/
theorem measurable_adaptiveHighAssignment
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d) :
    let haar := efficientHaarPairProcedure sampler d
    let net := highDimensionalNet
      (adaptiveHighParameters hc tau htau d hlarge)
    @Measurable
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed))
      (Fin d → MatrixCSPAlphabet net)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) (haar.Seed × ptas.Seed)
        inferInstance
        (@Prod.instMeasurableSpace haar.Seed ptas.Seed
          haar.seedMeasurableSpace ptas.seedMeasurableSpace))
      ⊤
      (adaptiveHighAssignment
        sampler ptas hc tau htau d hlarge) := by
  dsimp only
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  let params := adaptiveHighParameters hc tau htau d hlarge
  let net := highDimensionalNet params
  letI : Nonempty (MatrixCSPAlphabet net) :=
    matrixCSPAlphabet_nonempty net (by
      have := params.sigma_pos
      positivity)
  let toHistory :
      SeparableOracleQuery d × (haar.Seed × ptas.Seed) →
        SeparableOracleQuery d × haar.Seed :=
    fun z => (z.1, z.2.1)
  have hhistory : Measurable toHistory :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hcsp :=
    measurable_adaptiveHighCSP sampler hc tau htau d hlarge
  have hpair : @Measurable
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed))
      (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) × ptas.Seed)
      inferInstance
      (@Prod.instMeasurableSpace
        (DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net)) ptas.Seed
        (denseMaxFourCSPMeasurableSpace
          (Fin d) (MatrixCSPAlphabet net))
        ptas.seedMeasurableSpace)
      (fun z =>
        (adaptiveHighCSP sampler hc tau htau d hlarge
            (toHistory z),
          z.2.2)) :=
    (hcsp.comp hhistory).prodMk
      (measurable_snd.comp measurable_snd)
  have hsolve :=
    (ptas.solve_jointly_measurable
      (Fin d) (MatrixCSPAlphabet net) params.cspError).comp hpair
  have heq :
      adaptiveHighAssignment sampler ptas hc tau htau d hlarge =
        fun z =>
          ptas.solve (Fin d) (MatrixCSPAlphabet net)
            (adaptiveHighCSP sampler hc tau htau d hlarge
              (toHistory z))
            params.cspError z.2.2 := by
    funext z
    rfl
  rw [heq]
  exact hsolve

/-- Each coordinate of the two rotated high-branch output vectors is
jointly measurable. -/
theorem measurable_adaptiveHighOutputVectors_apply
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (side : Bool) (i : Fin d) :
    let haar := efficientHaarPairProcedure sampler d
    @Measurable
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed)) ℂ
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) (haar.Seed × ptas.Seed)
        inferInstance
        (@Prod.instMeasurableSpace haar.Seed ptas.Seed
          haar.seedMeasurableSpace ptas.seedMeasurableSpace))
      inferInstance
      (fun z =>
        if side then
          (adaptiveHighOutputVectors
            sampler ptas hc tau htau d hlarge z).1 i
        else
          (adaptiveHighOutputVectors
            sampler ptas hc tau htau d hlarge z).2 i) := by
  dsimp only
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  let params := adaptiveHighParameters hc tau htau d hlarge
  let net := highDimensionalNet params
  let assignment :=
    adaptiveHighAssignment sampler ptas hc tau htau d hlarge
  have hassignment :=
    measurable_adaptiveHighAssignment
      sampler ptas hc tau htau d hlarge
  have hx (j : Fin d) :
      Measurable fun z => normalizedCSPOutputX net (assignment z) j := by
    have hdisc : @Measurable
        (Fin d → MatrixCSPAlphabet net) ℂ ⊤ inferInstance
        (fun a => normalizedCSPOutputX net a j) := by
      letI : MeasurableSpace (Fin d → MatrixCSPAlphabet net) := ⊤
      exact Measurable.of_discrete
    exact hdisc.comp hassignment
  have hy (j : Fin d) :
      Measurable fun z => normalizedCSPOutputY net (assignment z) j := by
    have hdisc : @Measurable
        (Fin d → MatrixCSPAlphabet net) ℂ ⊤ inferInstance
        (fun a => normalizedCSPOutputY net a j) := by
      letI : MeasurableSpace (Fin d → MatrixCSPAlphabet net) := ⊤
      exact Measurable.of_discrete
    exact hdisc.comp hassignment
  let UV : SeparableOracleQuery d × (haar.Seed × ptas.Seed) →
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ :=
    fun z => haar.run () z.2.1
  have hUV : Measurable UV :=
    (efficientHaarPairProcedure_run_measurable sampler d).comp
      (measurable_fst.comp measurable_snd)
  by_cases hside : side
  · simp only [hside, ↓reduceIte]
    simpa [adaptiveHighOutputVectors, assignment, UV, params, net,
      rotateProductOutput] using
      measurable_unitaryVectorAction_apply d
        (fun z => (UV z).1)
        (fun z => normalizedCSPOutputX net (assignment z))
        hUV.fst hx i
  · have hfalse : side = false := Bool.eq_false_of_not_eq_true hside
    simp only [hfalse, ↓reduceIte]
    simpa [adaptiveHighOutputVectors, assignment, UV, params, net,
      rotateProductOutput] using
      measurable_unitaryVectorAction_apply d
        (fun z => (UV z).2)
        (fun z => normalizedCSPOutputY net (assignment z))
        hUV.snd hy i

/-- The complete high-branch pure-state output is jointly measurable. -/
theorem measurable_highSeparableOracleOutput
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d) :
    let haar := efficientHaarPairProcedure sampler d
    @Measurable
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed))
      (MatrixHilbert d)
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) (haar.Seed × ptas.Seed)
        inferInstance
        (@Prod.instMeasurableSpace haar.Seed ptas.Seed
          haar.seedMeasurableSpace ptas.seedMeasurableSpace))
      inferInstance
      (highSeparableOracleOutput
        sampler ptas hc tau htau d hlarge) := by
  dsimp only
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  let output :=
    adaptiveHighOutputVectors sampler ptas hc tau htau d hlarge
  exact measurable_pureProductState d
    (fun z => (output z).1) (fun z => (output z).2)
    (fun i => by
      simpa [output] using
        measurable_adaptiveHighOutputVectors_apply
          sampler ptas hc tau htau d hlarge true i)
    (fun i => by
      simpa [output] using
        measurable_adaptiveHighOutputVectors_apply
          sampler ptas hc tau htau d hlarge false i)

/-- A sectionwise lower probability bound transfers to the product
probability measure. -/
theorem measureReal_prod_ge_of_forall
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (nu : Measure S) [IsProbabilityMeasure nu]
    (event : Set (Ω × S))
    (hevent : MeasurableSet event)
    (q : ℝ)
    (hsection : ∀ ω,
      nu.real (Prod.mk ω ⁻¹' event) ≥ q) :
    (mu.prod nu).real event ≥ q := by
  have hsectionENN : ∀ ω,
      ENNReal.ofReal q ≤ nu (Prod.mk ω ⁻¹' event) := by
    intro ω
    rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
    exact hsection ω
  have hprodENN :
      ENNReal.ofReal q ≤ (mu.prod nu) event := by
    calc
      ENNReal.ofReal q =
          ∫⁻ _ω : Ω, ENNReal.ofReal q ∂mu := by simp
      _ ≤ ∫⁻ ω, nu (Prod.mk ω ⁻¹' event) ∂mu :=
        lintegral_mono hsectionENN
      _ = (mu.prod nu) event :=
        (Measure.prod_apply hevent).symm
  exact
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp
      hprodENN

/-- Joint measurability of the Haar flat/tail success condition when the
matrix itself is a measurable function of an earlier random history. -/
theorem measurableSet_randomHaarFlatTailConclusion
    {Ω : Type*} [MeasurableSpace Ω]
    (hc : GaussianHypercontractivityContract)
    (d p : ℕ)
    (M : Ω → BipartiteMatrix (Fin d))
    (UV : Ω →
      Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
    (delta : ℝ)
    (hMcoord : ∀ a b c e,
      Measurable fun ω => M ω (a, c) (b, e))
    (hUV : Measurable UV)
    (hMherm : ∀ ω, (M ω).IsHermitian) :
    MeasurableSet
      {ω |
        HaarFlatTailConclusion d (correlationPart (M ω))
          (flatThreshold hc d (correlationPart (M ω)) p)
          delta (UV ω)} := by
  let C : Ω → BipartiteMatrix (Fin d) :=
    fun ω => correlationPart (M ω)
  have hCcoord : ∀ a b c e,
      Measurable fun ω => C ω (a, c) (b, e) :=
    fun a b c e =>
      measurable_correlationPart_apply M hMcoord a b c e
  let total : Ω → BipartiteMatrix (Fin d) :=
    fun ω => bipartiteUnitaryConjugate d (C ω) (UV ω)
  have htotal : ∀ a b c e,
      Measurable fun ω => total ω (a, c) (b, e) :=
    fun a b c e =>
      measurable_bipartiteUnitaryConjugate_apply
        d C UV hCcoord hUV a b c e
  let threshold : Ω → ℝ :=
    fun ω => flatThreshold hc d (C ω) p
  have hCnorm : Measurable fun ω => frobeniusNorm (C ω) :=
    measurable_frobeniusNorm_of_apply C
      (fun i j => hCcoord i.1 j.1 i.2 j.2)
  have hthreshold : Measurable threshold := by
    dsimp [threshold, flatThreshold, flatMomentScale]
    fun_prop
  let tail : Ω → BipartiteMatrix (Fin d) :=
    fun ω => thresholdTail (threshold ω) (total ω)
  have htailCoord : ∀ i j, Measurable fun ω => tail ω i j :=
    fun i j =>
      measurable_thresholdTail_apply threshold total hthreshold
        (fun i j => htotal i.1 j.1 i.2 j.2) i j
  have htailNorm : Measurable fun ω => frobeniusNorm (tail ω) :=
    measurable_frobeniusNorm_of_apply tail htailCoord
  have heq :
      {ω |
        HaarFlatTailConclusion d (correlationPart (M ω))
          (flatThreshold hc d (correlationPart (M ω)) p)
          delta (UV ω)} =
      {ω | frobeniusNorm (tail ω) ≤
        delta * frobeniusNorm (C ω)} := by
    ext ω
    constructor
    · intro h
      exact h.2.2.2.2
    · intro h
      have hCherm : (C ω).IsHermitian :=
        correlationPart_isHermitian (M ω) (hMherm ω)
      exact
        ⟨haarThreshold_decomposition d (C ω) (threshold ω) (UV ω),
          haarThresholdFlat_isHermitian d (C ω) hCherm
            (threshold ω) (UV ω),
          haarThresholdTail_isHermitian d (C ω) hCherm
            (threshold ω) (UV ω),
          haarThresholdFlat_entryNorm_le d (C ω)
            (threshold ω)
            (by
              dsimp [threshold]
              exact flatThreshold_nonneg hc d (C ω) p)
            (UV ω),
          h⟩
  rw [heq]
  exact measurableSet_le htailNorm
    (measurable_const.mul hCnorm)

/-- The high-probability Haar conclusion remains valid when the input matrix
is selected measurably from an independent earlier history. -/
theorem random_mainHaarConclusion_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu]
    (sampler : EfficientHaarSamplingContract)
    (hc : GaussianHypercontractivityContract)
    (d : ℕ) (hd : 0 < d)
    (M : Ω → BipartiteMatrix (Fin d))
    (hMcoord : ∀ a b c e,
      Measurable fun ω => M ω (a, c) (b, e))
    (hMherm : ∀ ω, (M ω).IsHermitian)
    (hMnorm : ∀ ω, frobeniusNorm (M ω) ≤ 1)
    (p : ℕ) (hp : 0 < p) (height : 8 * p ≤ d)
    (delta : ℝ) (hdelta : 0 < delta)
    (hdecay :
      64 * flatMomentConstant hc ^ 2 * (p : ℝ) ^ 4 /
          (8 : ℝ) ^ (2 * p) ≤ delta ^ 4) :
    let haar := efficientHaarPairProcedure sampler d
    let event : Set (Ω × haar.Seed) :=
      {z |
        HaarFlatTailConclusion d (correlationPart (M z.1))
          (flatThreshold hc d (correlationPart (M z.1)) p)
          delta (haar.run () z.2)}
    @MeasurableSet (Ω × haar.Seed)
        (@Prod.instMeasurableSpace Ω haar.Seed
          inferInstance haar.seedMeasurableSpace) event ∧
      @Measure.real (Ω × haar.Seed)
        (@Prod.instMeasurableSpace Ω haar.Seed
          inferInstance haar.seedMeasurableSpace)
        (@MeasureTheory.Measure.prod Ω haar.Seed
          inferInstance haar.seedMeasurableSpace
          mu haar.seedMeasure) event ≥ 1 - delta ^ 2 := by
  dsimp only
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : IsProbabilityMeasure haar.seedMeasure := haar.seedProbability
  let event : Set (Ω × haar.Seed) :=
    {z |
      HaarFlatTailConclusion d (correlationPart (M z.1))
        (flatThreshold hc d (correlationPart (M z.1)) p)
        delta (haar.run () z.2)}
  have hevent : MeasurableSet event := by
    exact measurableSet_randomHaarFlatTailConclusion
      hc d p (fun z : Ω × haar.Seed => M z.1)
      (fun z => haar.run () z.2) delta
      (fun a b c e => (hMcoord a b c e).comp measurable_fst)
      ((efficientHaarPairProcedure_run_measurable sampler d).comp
        measurable_snd)
      (fun z => hMherm z.1)
  refine ⟨hevent, ?_⟩
  apply measureReal_prod_ge_of_forall
    mu haar.seedMeasure event hevent (1 - delta ^ 2)
  intro ω
  let conclusion : Set
      (Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :=
    {UV |
      HaarFlatTailConclusion d (correlationPart (M ω))
        (flatThreshold hc d (correlationPart (M ω)) p)
        delta UV}
  have hCherm :
      (correlationPart (M ω)).IsHermitian :=
    correlationPart_isHermitian (M ω) (hMherm ω)
  have hconclusionMeas : MeasurableSet conclusion :=
    measurableSet_haarFlatTailConclusion
      d (correlationPart (M ω)) hCherm
      (partialTrace0_correlationPart (M ω))
      (partialTrace1_correlationPart (M ω))
      (flatThreshold hc d (correlationPart (M ω)) p)
      (flatThreshold_nonneg hc d (correlationPart (M ω)) p)
      delta
  have hfixed :=
    mainHaarConclusion_probability
      hc d hd (M ω) (hMherm ω)
      p hp height delta hdelta hdecay
  have hlaw :=
    efficientHaarPairProcedure_eventProbability
      sampler d conclusion hconclusionMeas
  change haar.seedMeasure.real ((haar.run ()) ⁻¹' conclusion) =
      ((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d)).real conclusion at hlaw
  have hseed :
      haar.seedMeasure.real
          ((haar.run ()) ⁻¹' conclusion) ≥ 1 - delta ^ 2 := by
    rw [hlaw]
    simpa [conclusion] using hfixed
  simpa [event, conclusion] using hseed

/-- The high-branch certification core is measurable jointly in the query
and both fresh random sources. -/
theorem measurableSet_highSeparableOracleCore
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d) :
    let haar := efficientHaarPairProcedure sampler d
    @MeasurableSet
      (SeparableOracleQuery d × (haar.Seed × ptas.Seed))
      (@Prod.instMeasurableSpace
        (SeparableOracleQuery d) (haar.Seed × ptas.Seed)
        inferInstance
        (@Prod.instMeasurableSpace haar.Seed ptas.Seed
          haar.seedMeasurableSpace ptas.seedMeasurableSpace))
      {z |
        highSeparableOracleCore
          sampler ptas hc tau htau d hlarge z} := by
  dsimp only
  let hdata := mainDimensionCutoff_data hc htau hlarge
  letI : Nonempty (Fin d) := ⟨⟨0, hdata.1⟩⟩
  let p := mainMomentOrder hc tau
  let delta := mainTailAccuracy tau
  let params := adaptiveHighParameters hc tau htau d hlarge
  let net := highDimensionalNet params
  letI : Nonempty (MatrixCSPAlphabet net) :=
    matrixCSPAlphabet_nonempty net (by
      have := params.sigma_pos
      positivity)
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : IsProbabilityMeasure haar.seedMeasure := haar.seedProbability
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  letI : IsProbabilityMeasure ptas.seedMeasure := ptas.seedProbability
  let source :=
    SeparableOracleQuery d × (haar.Seed × ptas.Seed)
  let goodHaar : Set source :=
    {z |
      HaarFlatTailConclusion d
        (correlationPart (matrixOfHilbert d z.1.1))
        (flatThreshold hc d
          (correlationPart (matrixOfHilbert d z.1.1)) p)
        delta (haar.run () z.2.1)}
  have hquery :
      Measurable fun z : source => z.1.1 :=
    measurable_subtype_coe.comp measurable_fst
  have hMcoord : ∀ a b c e,
      Measurable fun z : source =>
        matrixOfHilbert d z.1.1 (a, c) (b, e) :=
    fun a b c e =>
      measurable_matrixOfHilbert_apply d _ hquery (a, c) (b, e)
  have hgoodHaar : MeasurableSet goodHaar := by
    exact measurableSet_randomHaarFlatTailConclusion
      hc d p (fun z : source => matrixOfHilbert d z.1.1)
      (fun z => haar.run () z.2.1) delta hMcoord
      ((efficientHaarPairProcedure_run_measurable sampler d).comp
        (measurable_fst.comp measurable_snd))
      (fun z => z.1.hermitian)
  let history := SeparableOracleQuery d × haar.Seed
  let randomCSP : history →
      DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) :=
    adaptiveHighCSP sampler hc tau htau d hlarge
  let goodCSPLeft : Set (history × ptas.Seed) :=
    {z |
      ∀ assignment,
        (randomCSP z.1).value assignment ≤
          (randomCSP z.1).value
            (ptas.solve (Fin d) (MatrixCSPAlphabet net)
              (randomCSP z.1) params.cspError z.2) +
          params.cspError}
  have hgoodCSPLeft : MeasurableSet goodCSPLeft := by
    simpa [goodCSPLeft] using
      ptas.independent_success_event_measurable
        history (Fin d) (MatrixCSPAlphabet net)
        ((Measure.dirac
          (Classical.arbitrary (SeparableOracleQuery d))).prod
            haar.seedMeasure)
        randomCSP params.cspError
  let assoc : source → history × ptas.Seed :=
    fun z => ((z.1, z.2.1), z.2.2)
  have hassoc : Measurable assoc :=
    (measurable_fst.prodMk
      (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)
  have hgoodCSP : MeasurableSet (assoc ⁻¹' goodCSPLeft) :=
    hgoodCSPLeft.preimage hassoc
  have hcore :
      {z : source |
        highSeparableOracleCore
          sampler ptas hc tau htau d hlarge z} =
        goodHaar ∩ assoc ⁻¹' goodCSPLeft := by
    ext z
    simp [highSeparableOracleCore, goodHaar, goodCSPLeft,
      adaptiveHighAssignment, assoc, randomCSP,
      p, delta, params, net, haar, history]
  rw [hcore]
  exact hgoodHaar.inter hgoodCSP

/-- For every fixed query, the high-dimensional certification core has
probability at least `2/3`. -/
theorem highSeparableOracleCore_probability
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (A : SeparableOracleQuery d) :
    let haar := efficientHaarPairProcedure sampler d
    @Measure.real (haar.Seed × ptas.Seed)
      (@Prod.instMeasurableSpace haar.Seed ptas.Seed
        haar.seedMeasurableSpace ptas.seedMeasurableSpace)
      (@Measure.prod haar.Seed ptas.Seed
        haar.seedMeasurableSpace ptas.seedMeasurableSpace
        haar.seedMeasure ptas.seedMeasure)
      {seed |
        highSeparableOracleCore
          sampler ptas hc tau htau d hlarge (A, seed)} ≥
      2 / 3 := by
  dsimp only
  let hdata := mainDimensionCutoff_data hc htau hlarge
  letI : Nonempty (Fin d) := ⟨⟨0, hdata.1⟩⟩
  let p := mainMomentOrder hc tau
  let delta := mainTailAccuracy tau
  let params := adaptiveHighParameters hc tau htau d hlarge
  let net := highDimensionalNet params
  letI : Nonempty (MatrixCSPAlphabet net) :=
    matrixCSPAlphabet_nonempty net (by
      have := params.sigma_pos
      positivity)
  let haar := efficientHaarPairProcedure sampler d
  letI : MeasurableSpace haar.Seed := haar.seedMeasurableSpace
  letI : IsProbabilityMeasure haar.seedMeasure := haar.seedProbability
  letI : MeasurableSpace ptas.Seed := ptas.seedMeasurableSpace
  letI : IsProbabilityMeasure ptas.seedMeasure := ptas.seedProbability
  let conclusion : Set
      (Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) :=
    {UV |
      HaarFlatTailConclusion d
        (correlationPart (matrixOfHilbert d A.1))
        (flatThreshold hc d
          (correlationPart (matrixOfHilbert d A.1)) p)
        delta UV}
  have hCherm :
      (correlationPart (matrixOfHilbert d A.1)).IsHermitian :=
    correlationPart_isHermitian _ A.hermitian
  have hconclusionMeas : MeasurableSet conclusion :=
    measurableSet_haarFlatTailConclusion d
      (correlationPart (matrixOfHilbert d A.1)) hCherm
      (partialTrace0_correlationPart _)
      (partialTrace1_correlationPart _)
      (flatThreshold hc d
        (correlationPart (matrixOfHilbert d A.1)) p)
      (flatThreshold_nonneg hc d
        (correlationPart (matrixOfHilbert d A.1)) p)
      delta
  let goodHaarSeed : Set haar.Seed :=
    (haar.run ()) ⁻¹' conclusion
  let goodHaar : Set (haar.Seed × ptas.Seed) :=
    goodHaarSeed ×ˢ Set.univ
  let randomCSP : haar.Seed →
      DenseMaxFourCSP (Fin d) (MatrixCSPAlphabet net) :=
    fun seed =>
      adaptiveHighCSP sampler hc tau htau d hlarge (A, seed)
  let goodCSP : Set (haar.Seed × ptas.Seed) :=
    {seed |
      ∀ assignment,
        (randomCSP seed.1).value assignment ≤
          (randomCSP seed.1).value
            (ptas.solve (Fin d) (MatrixCSPAlphabet net)
              (randomCSP seed.1) params.cspError seed.2) +
          params.cspError}
  have hgoodHaarMeas : MeasurableSet goodHaar := by
    exact
      (hconclusionMeas.preimage
        (efficientHaarPairProcedure_run_measurable sampler d)).prod
        MeasurableSet.univ
  have hgoodCSPMeas : MeasurableSet goodCSP := by
    simpa [goodCSP] using
      ptas.independent_success_event_measurable
        haar.Seed (Fin d) (MatrixCSPAlphabet net)
        haar.seedMeasure randomCSP params.cspError
  have hhaarBase :
      haar.seedMeasure.real goodHaarSeed ≥ 1 - delta ^ 2 := by
    have hlaw :=
      efficientHaarPairProcedure_eventProbability
        sampler d conclusion hconclusionMeas
    change haar.seedMeasure.real goodHaarSeed =
      ((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d)).real conclusion at hlaw
    rw [hlaw]
    exact mainHaarConclusion_probability hc d hdata.1
      (matrixOfHilbert d A.1) A.hermitian
      p (mainMomentOrder_pos hc htau) hdata.2.1
      delta (mainTailAccuracy_pos htau)
      (mainMomentOrder_decay hc htau)
  have hgoodHaarProbability :
      (haar.seedMeasure.prod ptas.seedMeasure).real goodHaar ≥
        1 - delta ^ 2 := by
    rw [show goodHaar = goodHaarSeed ×ˢ Set.univ by rfl,
      measureReal_prod_prod, probReal_univ, mul_one]
    exact hhaarBase
  have hgoodCSPProbability :
      (haar.seedMeasure.prod ptas.seedMeasure).real goodCSP ≥
        5 / 6 := by
    simpa [goodCSP] using
      ptas.success_on_independent_random_instance
        haar.Seed (Fin d) (MatrixCSPAlphabet net)
        haar.seedMeasure randomCSP params.cspError
        params.cspError_pos
  have hboth :
      (haar.seedMeasure.prod ptas.seedMeasure).real
          (goodHaar ∩ goodCSP) ≥
        1 - delta ^ 2 - 1 / 6 :=
    probability_inter_ge
      (haar.seedMeasure.prod ptas.seedMeasure)
      goodHaar goodCSP hgoodHaarMeas hgoodCSPMeas
      (delta ^ 2) (1 / 6)
      hgoodHaarProbability
      (by
        convert hgoodCSPProbability using 1 <;> norm_num)
  have hdeltaSq : delta ^ 2 ≤ 1 / 6 := by
    simpa [delta] using mainTailAccuracy_probability htau
  have hcoreEq :
      {seed |
        highSeparableOracleCore
          sampler ptas hc tau htau d hlarge (A, seed)} =
        goodHaar ∩ goodCSP := by
    ext seed
    simp [highSeparableOracleCore, goodHaar, goodHaarSeed,
      adaptiveHighAssignment, conclusion, goodCSP, randomCSP,
      p, delta, params, net, haar]
  rw [hcoreEq]
  linarith

theorem adaptiveHighOutputVectors_normalized
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (z : SeparableOracleQuery d ×
      ((efficientHaarPairProcedure sampler d).Seed × ptas.Seed)) :
    vectorNormSq
        (adaptiveHighOutputVectors
          sampler ptas hc tau htau d hlarge z).1 = d ∧
      vectorNormSq
        (adaptiveHighOutputVectors
          sampler ptas hc tau htau d hlarge z).2 = d := by
  let hdata := mainDimensionCutoff_data hc htau hlarge
  letI : Nonempty (Fin d) := ⟨⟨0, hdata.1⟩⟩
  let params := adaptiveHighParameters hc tau htau d hlarge
  let net := highDimensionalNet params
  let haar := efficientHaarPairProcedure sampler d
  let assignment :=
    adaptiveHighAssignment sampler ptas hc tau htau d hlarge z
  exact rotateProductOutput_normalized d (haar.run () z.2.1)
    (normalizedCSPOutputX net assignment)
    (normalizedCSPOutputY net assignment)
    (by
      simpa using normalizedCSPOutputX_normSq net assignment)
    (by
      simpa using normalizedCSPOutputY_normSq net assignment)

theorem highSeparableOracleOutput_mem
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (z : SeparableOracleQuery d ×
      ((efficientHaarPairProcedure sampler d).Seed × ptas.Seed)) :
    highSeparableOracleOutput
        sampler ptas hc tau htau d hlarge z ∈
      separableStates d := by
  let output :=
    adaptiveHighOutputVectors sampler ptas hc tau htau d hlarge z
  have hnorm :=
    adaptiveHighOutputVectors_normalized
      sampler ptas hc tau htau d hlarge z
  apply pureProductState_mem_separable
  exact
    ⟨output.1, output.2, hnorm.1, hnorm.2, rfl⟩

set_option maxHeartbeats 1000000 in
/-- A true high-dimensional core flag certifies the requested product-vector
support inequality, including all numerical error reductions. -/
theorem highSeparableOracleCore_product_correct
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (A : SeparableOracleQuery d)
    (seed :
      (efficientHaarPairProcedure sampler d).Seed × ptas.Seed)
    (hcore :
      highSeparableOracleCore
        sampler ptas hc tau htau d hlarge (A, seed)) :
    ∀ x y : Fin d → ℂ,
      vectorNormSq x = d →
      vectorNormSq y = d →
      matrixQuarticForm (matrixOfHilbert d A.1) x y ≤
        matrixQuarticForm (matrixOfHilbert d A.1)
          (adaptiveHighOutputVectors
            sampler ptas hc tau htau d hlarge (A, seed)).1
          (adaptiveHighOutputVectors
            sampler ptas hc tau htau d hlarge (A, seed)).2 +
        tau := by
  let hdata := mainDimensionCutoff_data hc htau hlarge
  letI : Nonempty (Fin d) := ⟨⟨0, hdata.1⟩⟩
  let alpha := effectiveAccuracy tau
  let delta := mainTailAccuracy tau
  let eta := mainDiscretizationAccuracy tau
  let p := mainMomentOrder hc tau
  let params := adaptiveHighParameters hc tau htau d hlarge
  let M := matrixOfHilbert d A.1
  let alg :=
    highDimensionalOptimizationProcedure sampler ptas hc d hdata.1
      M A.frobeniusNorm_le p params
  have hhaar :
      let haar := efficientHaarPairProcedure sampler d
      HaarFlatTailConclusion d (correlationPart M)
        (flatThreshold hc d (correlationPart M) p) delta
        (haar.run () seed.1) := by
    simpa [highSeparableOracleCore, M, p, delta, params] using
      hcore.1
  have hcsp :
      let haar := efficientHaarPairProcedure sampler d
      let net := highDimensionalNet params
      letI : Nonempty (MatrixCSPAlphabet net) :=
        matrixCSPAlphabet_nonempty net (by
          have := params.sigma_pos
          positivity)
      let UV := haar.run () seed.1
      let csp :=
        highDimensionalCSP hc d hdata.1 M A.frobeniusNorm_le
          p params UV
      ∀ assignment,
        csp.value assignment ≤
          csp.value
            (ptas.solve (Fin d) (MatrixCSPAlphabet net)
              csp params.cspError seed.2) +
          params.cspError := by
    simpa [highSeparableOracleCore, adaptiveHighCSP,
      highDimensionalCSP,
      adaptiveHighProjectedMatrix, adaptiveHighAssignment,
      M, p, delta, params] using hcore.2
  have hprecise :=
    highDimensionalOptimizationProcedure_correct_of_core
      sampler ptas hc d hdata.1 M A.frobeniusNorm_le
      p delta (mainTailAccuracy_pos htau).le params seed
      hhaar hcsp
  have hdisc :
      discretizedOptimizationError
          params.sigma params.mesh params.penalty
          (mainCSPGamma hc p) params.cspError
          params.boundedError ≤ eta := by
    simpa [params, adaptiveHighParameters,
      selectedHighDimensionalParameters, p, eta] using
      selected_discretizedOptimizationError_le
        (mainCSPGamma_nonneg hc p)
        (by
          dsimp [eta, mainDiscretizationAccuracy]
          exact div_pos (effectiveAccuracy_pos htau) (by norm_num))
  have hlocal :
      4 / Real.sqrt d ≤ alpha / 2 :=
    local_error_le_of_dimension
      (effectiveAccuracy_pos htau) hdata.2.2.2
  have htotal :
      discretizedOptimizationError
          params.sigma params.mesh params.penalty
          (mainCSPGamma hc p) params.cspError
          params.boundedError +
          2 * delta + 4 / Real.sqrt d ≤ tau := by
    have halpha := effectiveAccuracy_le_tau tau
    dsimp [eta, mainDiscretizationAccuracy,
      delta, mainTailAccuracy] at hdisc ⊢
    dsimp [alpha] at hlocal
    linarith
  intro x y hx hy
  have hp := hprecise x y hx hy
  have hout :
      (alg.run () seed) =
        adaptiveHighOutputVectors
          sampler ptas hc tau htau d hlarge (A, seed) := by
    unfold alg highDimensionalOptimizationProcedure
    unfold adaptiveHighOutputVectors adaptiveHighAssignment
    unfold adaptiveHighCSP adaptiveHighProjectedMatrix
    unfold highDimensionalCSP
    dsimp [M, p, params]
  rw [hout] at hp
  linarith

/-- A true high-dimensional core flag extends from pure products to the
entire separable convex hull. -/
theorem highSeparableOracleCore_correct
    (sampler : EfficientHaarSamplingContract)
    (ptas : DenseMaxFourCSPPTASContract)
    (hc : GaussianHypercontractivityContract)
    (tau : ℝ) (htau : 0 < tau)
    (d : ℕ) (hlarge : mainDimensionCutoff hc tau ≤ d)
    (A : SeparableOracleQuery d)
    (seed :
      (efficientHaarPairProcedure sampler d).Seed × ptas.Seed)
    (hcore :
      highSeparableOracleCore
        sampler ptas hc tau htau d hlarge (A, seed)) :
    ∀ P ∈ separableStates d,
      ⟪A.1, P⟫ ≤
        ⟪A.1,
          highSeparableOracleOutput
            sampler ptas hc tau htau d hlarge (A, seed)⟫ + tau := by
  let hdata := mainDimensionCutoff_data hc htau hlarge
  let output :=
    adaptiveHighOutputVectors
      sampler ptas hc tau htau d hlarge (A, seed)
  have hnorm :=
    adaptiveHighOutputVectors_normalized
      sampler ptas hc tau htau d hlarge (A, seed)
  have hproduct :=
    highSeparableOracleCore_product_correct
      sampler ptas hc tau htau d hlarge A seed hcore
  intro P hP
  have hbound :=
    product_quartic_bound_extends_to_separable
      d hdata.1 (matrixOfHilbert d A.1) A.hermitian
      output.1 output.2 hnorm.1 hnorm.2 tau hproduct hP
  simpa [highSeparableOracleOutput, output] using hbound

end

end QuantumSep
