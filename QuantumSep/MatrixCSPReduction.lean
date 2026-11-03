import QuantumSep.AlgorithmicInterfaces
import QuantumSep.Discretization
import QuantumSep.MatrixObjective

/-!
# The concrete finite-alphabet dense Max-4-CSP

An alphabet symbol stores one rounded complex coordinate for each of the two
product vectors.  This keeps the variable set equal to the matrix index set;
the alphabet size is the square of the disk-net size.
-/

namespace QuantumSep

noncomputable section

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A CSP symbol consists of one disk-net point for `x` and one for `y`. -/
abbrev MatrixCSPAlphabet {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon) :=
  (↥net.points) × (↥net.points)

/-- A net of a disk with nonnegative radius supplies a nonempty CSP alphabet. -/
theorem matrixCSPAlphabet_nonempty
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (hkappa : 0 ≤ kappa) : Nonempty (MatrixCSPAlphabet net) := by
  obtain ⟨z, hz, _⟩ := net.approximates 0 (by simpa using hkappa)
  exact ⟨(⟨z, hz⟩, ⟨z, hz⟩)⟩

theorem matrixCSPAlphabet_card
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon) :
    Fintype.card (MatrixCSPAlphabet net) = net.points.card ^ 2 := by
  simp [MatrixCSPAlphabet, pow_two]

/-- Extract the two complex vectors encoded by an assignment. -/
def matrixCSPAssignmentX {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon)
    (assignment : ι → MatrixCSPAlphabet net) : ι → ℂ :=
  fun i => (assignment i).1.1

def matrixCSPAssignmentY {kappa epsilon : ℝ}
    (net : ComplexDiskNet kappa epsilon)
    (assignment : ι → MatrixCSPAlphabet net) : ι → ℂ :=
  fun i => (assignment i).2.1

/-- The assignment obtained by coordinatewise rounding of two disk-bounded
vectors. -/
def matrixCSPRoundedAssignment
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (x y : ι → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ kappa)
    (hy : ∀ i, ‖y i‖ ≤ kappa) :
    ι → MatrixCSPAlphabet net :=
  fun i =>
    (⟨net.round (x i), net.round_mem (hx i)⟩,
      ⟨net.round (y i), net.round_mem (hy i)⟩)

@[simp] theorem matrixCSPAssignmentX_rounded
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (x y : ι → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ kappa)
    (hy : ∀ i, ‖y i‖ ≤ kappa) :
    matrixCSPAssignmentX net
      (matrixCSPRoundedAssignment net x y hx hy) =
        net.roundVector x := by
  rfl

@[simp] theorem matrixCSPAssignmentY_rounded
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (x y : ι → ℂ)
    (hx : ∀ i, ‖x i‖ ≤ kappa)
    (hy : ∀ i, ‖y i‖ ≤ kappa) :
    matrixCSPAssignmentY net
      (matrixCSPRoundedAssignment net x y hx hy) =
        net.roundVector y := by
  rfl

/-- One predicate written only in terms of its four alphabet symbols. -/
def matrixAlphabetPredicate
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (M : BipartiteMatrix ι) (penalty gamma : ℝ)
    (a b c e : ι)
    (za zb zc ze : MatrixCSPAlphabet net) : ℝ :=
  rescaledPredicate (matrixPredicateScale gamma kappa penalty)
    (cardR (ι := ι) ^ 2 *
        (M (a, c) (b, e) *
          star za.1.1 * zb.1.1 * star zc.2.1 * ze.2.1).re -
      penalty *
        ((Complex.normSq za.1.1 - 1) *
          (Complex.normSq zb.1.1 - 1)) -
      penalty *
        ((Complex.normSq zc.2.1 - 1) *
          (Complex.normSq ze.2.1 - 1)))

theorem matrixAlphabetPredicate_assignment_eq
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (M : BipartiteMatrix ι) (penalty gamma : ℝ)
    (assignment : ι → MatrixCSPAlphabet net)
    (a b c e : ι) :
    matrixAlphabetPredicate net M penalty gamma a b c e
        (assignment a) (assignment b) (assignment c) (assignment e) =
      matrixCSPPredicate M penalty
        (matrixPredicateScale gamma kappa penalty)
        (matrixCSPAssignmentX net assignment)
        (matrixCSPAssignmentY net assignment) a b c e := by
  rfl

/-- The actual finite dense Max-4-CSP emitted by the deterministic reduction. -/
def matrixDenseMaxFourCSP
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (M : BipartiteMatrix ι) (penalty gamma : ℝ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hpenalty : 0 ≤ penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2) :
    DenseMaxFourCSP ι (MatrixCSPAlphabet net) where
  predicate := matrixAlphabetPredicate net M penalty gamma
  predicate_mem := by
    intro assignment a b c e
    rw [matrixAlphabetPredicate_assignment_eq]
    apply matrixCSPPredicate_mem_unitInterval
      M (matrixCSPAssignmentX net assignment)
        (matrixCSPAssignmentY net assignment)
      gamma kappa penalty a b c e
      hgamma hkappa hpenalty (hentry a b c e)
    · intro i
      exact net.points_mem _ (assignment i).1.2
    · intro i
      exact net.points_mem _ (assignment i).2.2

/-- The finite CSP construction is measurable in every matrix coordinate.
This supplies the input-side measurability needed to call the PTAS as a
probability kernel on adaptively selected matrices. -/
theorem measurable_matrixDenseMaxFourCSP
    {Ω : Type*} [MeasurableSpace Ω]
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (M : Ω → BipartiteMatrix ι) (penalty gamma : ℝ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hpenalty : 0 ≤ penalty)
    (hentry : ∀ ω a b c e,
      ‖M ω (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (hM : ∀ a b c e, Measurable fun ω => M ω (a, c) (b, e)) :
    @Measurable Ω
      (DenseMaxFourCSP ι (MatrixCSPAlphabet net))
      inferInstance
      (denseMaxFourCSPMeasurableSpace
        ι (MatrixCSPAlphabet net))
      (fun ω =>
        matrixDenseMaxFourCSP net (M ω) penalty gamma
          hgamma hkappa hpenalty (hentry ω)) := by
  let A := MatrixCSPAlphabet net
  letI : MeasurableSpace (A → ℝ) := MeasurableSpace.pi
  letI : MeasurableSpace (A → A → ℝ) := MeasurableSpace.pi
  letI : MeasurableSpace (A → A → A → ℝ) :=
    MeasurableSpace.pi
  letI : MeasurableSpace (A → A → A → A → ℝ) :=
    MeasurableSpace.pi
  letI : MeasurableSpace (ι → A → A → A → A → ℝ) :=
    MeasurableSpace.pi
  letI : MeasurableSpace (ι → ι → A → A → A → A → ℝ) :=
    MeasurableSpace.pi
  letI :
      MeasurableSpace (ι → ι → ι → A → A → A → A → ℝ) :=
    MeasurableSpace.pi
  letI :
      MeasurableSpace (ι → ι → ι → ι → A → A → A → A → ℝ) :=
    MeasurableSpace.pi
  apply Measurable.of_comap_le
  rw [MeasurableSpace.comap_comp]
  apply measurable_iff_comap_le.mp
  change @Measurable Ω
    (ι → ι → ι → ι →
      MatrixCSPAlphabet net → MatrixCSPAlphabet net →
      MatrixCSPAlphabet net → MatrixCSPAlphabet net → ℝ)
    inferInstance
    (denseMaxFourCSPPredicateMeasurableSpace
      ι (MatrixCSPAlphabet net))
    (fun ω =>
      (matrixDenseMaxFourCSP net (M ω) penalty gamma
        hgamma hkappa hpenalty (hentry ω)).predicate)
  apply measurable_pi_lambda
  intro a
  apply measurable_pi_lambda
  intro b
  apply measurable_pi_lambda
  intro c
  apply measurable_pi_lambda
  intro e
  apply measurable_pi_lambda
  intro za
  apply measurable_pi_lambda
  intro zb
  apply measurable_pi_lambda
  intro zc
  apply measurable_pi_lambda
  intro ze
  change Measurable fun ω =>
    matrixAlphabetPredicate net (M ω) penalty gamma
      a b c e za zb zc ze
  unfold matrixAlphabetPredicate rescaledPredicate
  fun_prop

/-- The CSP value is exactly the affine rescaling of the concrete penalized
matrix objective—there is no approximation in the reduction itself. -/
theorem matrixDenseMaxFourCSP_value_eq
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (M : BipartiteMatrix ι) (penalty gamma : ℝ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hpenalty : 0 ≤ penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (assignment : ι → MatrixCSPAlphabet net) :
    (matrixDenseMaxFourCSP net M penalty gamma
        hgamma hkappa hpenalty hentry).value assignment =
      rescaledPredicate (matrixPredicateScale gamma kappa penalty)
        (matrixPenalizedObjective M penalty
          (matrixCSPAssignmentX net assignment)
          (matrixCSPAssignmentY net assignment)) := by
  unfold DenseMaxFourCSP.value
  rw [show
      (fun a b c e =>
        (matrixDenseMaxFourCSP net M penalty gamma
          hgamma hkappa hpenalty hentry).predicate a b c e
            (assignment a) (assignment b) (assignment c) (assignment e)) =
        matrixCSPPredicate M penalty
          (matrixPredicateScale gamma kappa penalty)
          (matrixCSPAssignmentX net assignment)
          (matrixCSPAssignmentY net assignment) by
    funext a b c e
    exact matrixAlphabetPredicate_assignment_eq
      net M penalty gamma assignment a b c e]
  exact matrixCSPValue_eq_rescaled_objective
    M penalty (matrixPredicateScale gamma kappa penalty)
      (matrixCSPAssignmentX net assignment)
      (matrixCSPAssignmentY net assignment)
      (by
        unfold matrixPredicateScale
        positivity)

/-- A successful PTAS assignment gives the corresponding additive guarantee
for the unscaled penalized matrix objective. -/
theorem matrixCSP_success_to_penalized
    {kappa epsilon : ℝ} (net : ComplexDiskNet kappa epsilon)
    (M : BipartiteMatrix ι) (penalty gamma cspError : ℝ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 ≤ kappa)
    (hpenalty : 0 ≤ penalty)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤ gamma / cardR (ι := ι) ^ 2)
    (output : ι → MatrixCSPAlphabet net)
    (hsuccess : ∀ assignment,
      (matrixDenseMaxFourCSP net M penalty gamma
        hgamma hkappa hpenalty hentry).value assignment ≤
      (matrixDenseMaxFourCSP net M penalty gamma
        hgamma hkappa hpenalty hentry).value output + cspError) :
    ∀ assignment,
      matrixPenalizedObjective M penalty
          (matrixCSPAssignmentX net assignment)
          (matrixCSPAssignmentY net assignment) ≤
        matrixPenalizedObjective M penalty
          (matrixCSPAssignmentX net output)
          (matrixCSPAssignmentY net output) +
        2 * matrixPredicateScale gamma kappa penalty * cspError := by
  intro assignment
  have hs := hsuccess assignment
  rw [matrixDenseMaxFourCSP_value_eq,
    matrixDenseMaxFourCSP_value_eq] at hs
  unfold rescaledPredicate at hs
  have hscale : 0 < matrixPredicateScale gamma kappa penalty := by
    unfold matrixPredicateScale
    positivity
  have hdiv :
      (matrixPenalizedObjective M penalty
          (matrixCSPAssignmentX net assignment)
          (matrixCSPAssignmentY net assignment) -
        matrixPenalizedObjective M penalty
          (matrixCSPAssignmentX net output)
          (matrixCSPAssignmentY net output)) /
          (2 * matrixPredicateScale gamma kappa penalty) ≤ cspError := by
    rw [sub_div]
    linarith
  have hmul := (div_le_iff₀ (by positivity :
      0 < 2 * matrixPredicateScale gamma kappa penalty)).mp hdiv
  linarith

end

end QuantumSep
