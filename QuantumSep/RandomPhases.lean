import QuantumSep.BoundedAmplitude
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Integration

/-!
# Explicit random phases

Four uniformly random fourth roots of unity suffice for the refill step.  This
file constructs their probability law and proves the first and mixed second
moments, including independence across coordinates.
-/

open scoped BigOperators ComplexConjugate Matrix

open MeasureTheory ProbabilityTheory Set

namespace QuantumSep

noncomputable section

/-- The four phases `1, i, -1, -i`. -/
def fourthRootPhase : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]

@[simp] theorem norm_fourthRootPhase (k : Fin 4) :
    ‖fourthRootPhase k‖ = 1 := by
  fin_cases k <;> simp [fourthRootPhase]

theorem sum_fourthRootPhase :
    ∑ k : Fin 4, fourthRootPhase k = 0 := by
  simp [fourthRootPhase, Fin.sum_univ_succ]

/-- Uniform probability measure on the four phases' indices. -/
def fourthRootPhaseMeasure : Measure (Fin 4) :=
  ProbabilityTheory.uniformOn Set.univ

instance : IsProbabilityMeasure fourthRootPhaseMeasure := by
  unfold fourthRootPhaseMeasure
  infer_instance

theorem fourthRootPhaseMeasure_eq :
    fourthRootPhaseMeasure =
      ((4 : ENNReal)⁻¹) • (Measure.count : Measure (Fin 4)) := by
  unfold fourthRootPhaseMeasure ProbabilityTheory.uniformOn
  simp [ProbabilityTheory.cond, Measure.restrict_univ]

theorem integral_fourthRootPhase :
    ∫ k, fourthRootPhase k ∂fourthRootPhaseMeasure = 0 := by
  rw [fourthRootPhaseMeasure_eq, integral_smul_measure]
  simp [sum_fourthRootPhase]

theorem integral_star_fourthRootPhase :
    ∫ k, star (fourthRootPhase k) ∂fourthRootPhaseMeasure = 0 := by
  rw [fourthRootPhaseMeasure_eq, integral_smul_measure]
  simp [← map_sum, sum_fourthRootPhase]

theorem integral_normSq_fourthRootPhase :
    ∫ k, star (fourthRootPhase k) * fourthRootPhase k
        ∂fourthRootPhaseMeasure = 1 := by
  rw [fourthRootPhaseMeasure_eq, integral_smul_measure]
  norm_num [fourthRootPhase, Fin.sum_univ_succ]

/-- Product law for independent random phases indexed by `ι`. -/
def phaseVectorMeasure (ι : Type*) [Fintype ι] :
    Measure (ι → Fin 4) :=
  Measure.pi (fun _ => fourthRootPhaseMeasure)

instance {ι : Type*} [Fintype ι] :
    IsProbabilityMeasure (phaseVectorMeasure ι) := by
  unfold phaseVectorMeasure
  infer_instance

/-- The complex random phase in one coordinate. -/
def phaseCoordinate {ι : Type*} (i : ι) (ω : ι → Fin 4) : ℂ :=
  fourthRootPhase (ω i)

theorem integral_phaseCoordinate
    {ι : Type*} [Fintype ι] (i : ι) :
    ∫ ω, phaseCoordinate i ω ∂phaseVectorMeasure ι = 0 := by
  have h := integral_comp_eval
    (μ := fun _ : ι => fourthRootPhaseMeasure)
    (i := i) (f := fourthRootPhase) (by fun_prop)
  rw [integral_fourthRootPhase] at h
  simpa [phaseVectorMeasure, phaseCoordinate] using h

theorem integral_star_phaseCoordinate
    {ι : Type*} [Fintype ι] (i : ι) :
    ∫ ω, star (phaseCoordinate i ω) ∂phaseVectorMeasure ι = 0 := by
  have h := integral_comp_eval
    (μ := fun _ : ι => fourthRootPhaseMeasure)
    (i := i) (f := fun k => star (fourthRootPhase k)) (by fun_prop)
  rw [integral_star_fourthRootPhase] at h
  simpa [phaseVectorMeasure, phaseCoordinate] using h

/-- The covariance of two random phase coordinates is the Kronecker delta. -/
theorem integral_star_phase_mul_phase
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    (∫ ω, star (phaseCoordinate a ω) * phaseCoordinate b ω
        ∂phaseVectorMeasure ι) =
      if a = b then 1 else 0 := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    have h := integral_comp_eval
      (μ := fun _ : ι => fourthRootPhaseMeasure)
      (i := a)
      (f := fun k => star (fourthRootPhase k) * fourthRootPhase k)
      (by fun_prop)
    rw [integral_normSq_fourthRootPhase] at h
    simpa [phaseVectorMeasure, phaseCoordinate] using h
  · rw [if_neg hab]
    have hindepAll :
        iIndepFun
          (fun i (ω : ι → Fin 4) => id (ω i))
          (phaseVectorMeasure ι) := by
      unfold phaseVectorMeasure
      exact iIndepFun_pi
        (X := fun _ : ι => id)
        (μ := fun _ : ι => fourthRootPhaseMeasure)
        (fun _ => aemeasurable_id)
    have hindep := hindepAll.indepFun hab
    have hfactor := hindep.integral_comp_mul_comp
      (measurable_pi_apply a).aemeasurable
      (measurable_pi_apply b).aemeasurable
      (f := fun k => star (fourthRootPhase k))
      (g := fourthRootPhase)
      (by fun_prop) (by fun_prop)
    have hfactor' :
        (∫ ω, star (phaseCoordinate a ω) * phaseCoordinate b ω
            ∂phaseVectorMeasure ι) =
          (∫ ω, star (phaseCoordinate a ω) ∂phaseVectorMeasure ι) *
            ∫ ω, phaseCoordinate b ω ∂phaseVectorMeasure ι := by
      simpa [phaseCoordinate, Function.comp_def] using hfactor
    rw [integral_star_phaseCoordinate, integral_phaseCoordinate] at hfactor'
    simpa using hfactor'

end

end QuantumSep
