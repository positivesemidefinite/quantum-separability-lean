import QuantumSep.AlgorithmicInterfaces
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Two independent efficient Haar samples
-/

namespace QuantumSep

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Run the permitted exact-Haar sampler twice with independent seeds. -/
def efficientHaarPairProcedure
    (sampler : EfficientHaarSamplingContract) (d : ℕ) :
    RandomizedProcedure Unit
      (Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ) := by
  let base := sampler.sample d
  letI := base.seedMeasurableSpace
  letI := base.seedProbability
  exact {
    Seed := base.Seed × base.Seed
    seedMeasurableSpace := Prod.instMeasurableSpace
    seedMeasure := base.seedMeasure.prod base.seedMeasure
    seedProbability := inferInstance
    run := fun _ seed =>
      (base.run () seed.1, base.run () seed.2)
    runtime := fun _ seed =>
      base.runtime () seed.1 + base.runtime () seed.2
  }

theorem efficientHaarPairProcedure_exact_law
    (sampler : EfficientHaarSamplingContract) (d : ℕ) :
    let alg := efficientHaarPairProcedure sampler d
    @Measure.map
      alg.Seed
      (Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
      alg.seedMeasurableSpace
      (Prod.instMeasurableSpace :
        MeasurableSpace
          (Matrix.unitaryGroup (Fin d) ℂ ×
            Matrix.unitaryGroup (Fin d) ℂ))
      (alg.run ()) alg.seedMeasure =
        (unitaryHaarMeasure d).prod (unitaryHaarMeasure d) := by
  dsimp only
  let base := sampler.sample d
  letI := base.seedMeasurableSpace
  letI := base.seedProbability
  have hmeas := sampler.sample_measurable d
  change
    @Measure.map
      (base.Seed × base.Seed)
      (Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
      (@Prod.instMeasurableSpace base.Seed base.Seed
        base.seedMeasurableSpace base.seedMeasurableSpace)
      (@Prod.instMeasurableSpace
        (Matrix.unitaryGroup (Fin d) ℂ)
        (Matrix.unitaryGroup (Fin d) ℂ)
        (measurableSpaceUnitaryGroup d)
        (measurableSpaceUnitaryGroup d))
      (Prod.map (base.run ()) (base.run ()))
      (base.seedMeasure.prod base.seedMeasure) =
        (unitaryHaarMeasure d).prod (unitaryHaarMeasure d)
  rw [← Measure.map_prod_map base.seedMeasure base.seedMeasure hmeas hmeas]
  rw [sampler.exact_law d]

theorem efficientHaarPairProcedure_run_measurable
    (sampler : EfficientHaarSamplingContract) (d : ℕ) :
    let alg := efficientHaarPairProcedure sampler d
    @Measurable
      alg.Seed
      (Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ)
      alg.seedMeasurableSpace
      (Prod.instMeasurableSpace :
        MeasurableSpace
          (Matrix.unitaryGroup (Fin d) ℂ ×
            Matrix.unitaryGroup (Fin d) ℂ))
      (alg.run ()) := by
  dsimp only
  exact (sampler.sample_measurable d).prodMap
    (sampler.sample_measurable d)

/-- Every measurable Haar event has exactly the same probability when the
two efficient samplers are run on independent seeds. -/
theorem efficientHaarPairProcedure_eventProbability
    (sampler : EfficientHaarSamplingContract) (d : ℕ)
    (event : Set
      (Matrix.unitaryGroup (Fin d) ℂ ×
        Matrix.unitaryGroup (Fin d) ℂ))
    (hevent : MeasurableSet event) :
    let alg := efficientHaarPairProcedure sampler d
    alg.eventProbability ((alg.run ()) ⁻¹' event) =
      ((unitaryHaarMeasure d).prod
        (unitaryHaarMeasure d)).real event := by
  dsimp only
  let alg := efficientHaarPairProcedure sampler d
  have hmeas := efficientHaarPairProcedure_run_measurable sampler d
  have hmap := efficientHaarPairProcedure_exact_law sampler d
  letI := alg.seedMeasurableSpace
  have hreal :=
    map_measureReal_apply hmeas hevent
      (μ := alg.seedMeasure)
  rw [hmap] at hreal
  exact hreal.symm

theorem efficientHaarPairProcedure_runtime
    (sampler : EfficientHaarSamplingContract) (d : ℕ)
    (seed : (efficientHaarPairProcedure sampler d).Seed) :
    (efficientHaarPairProcedure sampler d).runtime () seed ≤
      2 * sampler.runtimeConstant * (d + 1) ^ sampler.runtimeDegree := by
  have h1 := sampler.polynomial_runtime d seed.1
  have h2 := sampler.polynomial_runtime d seed.2
  dsimp [efficientHaarPairProcedure]
  calc
    (sampler.sample d).runtime () seed.1 +
        (sampler.sample d).runtime () seed.2 ≤
      sampler.runtimeConstant * (d + 1) ^ sampler.runtimeDegree +
        sampler.runtimeConstant * (d + 1) ^ sampler.runtimeDegree :=
      Nat.add_le_add h1 h2
    _ = 2 * sampler.runtimeConstant *
        (d + 1) ^ sampler.runtimeDegree := by ring

end

end QuantumSep
