import Mathlib

/-!
# Scalar inequalities used by the discretization and Frank--Wolfe arguments
-/

namespace QuantumSep

/-- Completing the square: `a b - penalty * b² ≤ a²/(4 * penalty)`
for a positive penalty. -/
theorem linear_mul_sub_quadratic_le (a b penalty : ℝ) (hpenalty : 0 < penalty) :
    a * b - penalty * b ^ 2 ≤ a ^ 2 / (4 * penalty) := by
  apply (le_div_iff₀ (by positivity : 0 < 4 * penalty)).2
  nlinarith [sq_nonneg (a - 2 * penalty * b)]

/-- The scalar core of Claim 1 in the discretization proof.  Normalizing two
vectors can lose at most the two completing-square errors. -/
theorem penalized_to_normalized_lower_bound
    (q qNormalized rx ry gamma kappa penalty : ℝ)
    (hgamma : 0 ≤ gamma)
    (hpenalty : 0 < penalty)
    (hrx0 : 0 ≤ rx) (hrx : rx ≤ kappa ^ 2)
    (hproduct : q = rx * ry * qNormalized)
    (hqNormalized : |qNormalized| ≤ gamma) :
    q - penalty * (rx - 1) ^ 2 - penalty * (ry - 1) ^ 2 ≤
      qNormalized +
        (gamma ^ 2 + gamma ^ 2 * kappa ^ 4) / (4 * penalty) := by
  let ax := |rx - 1|
  let ay := |ry - 1|
  have hqdiff :
      |q - qNormalized| ≤ gamma * ax + gamma * kappa ^ 2 * ay := by
    have hid :
        q - qNormalized =
          (rx - 1) * qNormalized +
            rx * (ry - 1) * qNormalized := by
      rw [hproduct]
      ring
    rw [hid]
    calc
      |(rx - 1) * qNormalized +
          rx * (ry - 1) * qNormalized| ≤
        |(rx - 1) * qNormalized| +
          |rx * (ry - 1) * qNormalized| := abs_add_le _ _
      _ = ax * |qNormalized| + rx * ay * |qNormalized| := by
        simp [ax, ay, abs_mul, abs_of_nonneg hrx0]
      _ ≤ ax * gamma + rx * ay * gamma := by
        gcongr
      _ ≤ gamma * ax + gamma * kappa ^ 2 * ay := by
        have hay : 0 ≤ ay := abs_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right hrx
          (mul_nonneg hay hgamma)]
  have hqUpper :
      q ≤ qNormalized + gamma * ax + gamma * kappa ^ 2 * ay := by
    have := le_abs_self (q - qNormalized)
    linarith
  have hxSquare : ax ^ 2 = (rx - 1) ^ 2 := by
    simp [ax, sq_abs]
  have hySquare : ay ^ 2 = (ry - 1) ^ 2 := by
    simp [ay, sq_abs]
  have hx :=
    linear_mul_sub_quadratic_le gamma ax penalty hpenalty
  have hy :=
    linear_mul_sub_quadratic_le
      (gamma * kappa ^ 2) ay penalty hpenalty
  rw [hxSquare] at hx
  rw [hySquare] at hy
  have hsquare :
      (gamma * kappa ^ 2) ^ 2 = gamma ^ 2 * kappa ^ 4 := by ring
  rw [hsquare] at hy
  have hsplit :
      (gamma ^ 2 + gamma ^ 2 * kappa ^ 4) / (4 * penalty) =
        gamma ^ 2 / (4 * penalty) +
          (gamma ^ 2 * kappa ^ 4) / (4 * penalty) := by ring
  rw [hsplit]
  nlinarith [sq_nonneg gamma, sq_nonneg kappa]

/-- The manuscript's choice of penalty makes Claim 1 cost at most `η/4`. -/
theorem discretization_penalty_choice
    (gamma kappa η : ℝ) (hη : 0 < η) :
    let penalty :=
      1 + (gamma ^ 2 + gamma ^ 2 * kappa ^ 4) / η
    (gamma ^ 2 + gamma ^ 2 * kappa ^ 4) / (4 * penalty) ≤ η / 4 := by
  dsimp
  let A := gamma ^ 2 + gamma ^ 2 * kappa ^ 4
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hden : 0 < 4 * (1 + A / η) := by
    have : 0 ≤ A / η := div_nonneg hA hη.le
    positivity
  apply (div_le_iff₀ hden).2
  dsimp [A] at *
  field_simp [ne_of_gt hη]
  nlinarith

/-- The manuscript's net mesh makes the objective-plus-penalty Lipschitz loss
at most `η/4`. -/
theorem discretization_mesh_choice
    (gamma kappa penalty η : ℝ)
    (hgamma : 0 ≤ gamma) (hkappa : 0 < kappa)
    (hpenalty : 0 < penalty) :
    let lipschitz :=
      4 * gamma * kappa ^ 3 +
        8 * penalty * kappa * (kappa ^ 2 + 1)
    let epsilon :=
      η /
        (16 * gamma * kappa ^ 3 +
          32 * penalty * kappa * (kappa ^ 2 + 1))
    lipschitz * epsilon = η / 4 := by
  dsimp
  have hpositive :
      0 <
        4 * gamma * kappa ^ 3 +
          8 * penalty * kappa * (kappa ^ 2 + 1) := by
    have : 0 < 8 * penalty * kappa * (kappa ^ 2 + 1) := by positivity
    positivity
  field_simp
  ring

/-- A two-sided deviation bound implies the normalization factor is positive. -/
theorem one_sub_pos_of_deviation {t x : ℝ}
    (ht : t < 1) (hx : |x - 1| ≤ t) : 0 < x := by
  rw [abs_le] at hx
  linarith

/-- The renormalization estimate used in the bounded-amplitude lemma:
if both squared-norm ratios are within `t ≤ 1/2` of one, then their inverse
product is within `8t` of one. -/
theorem inverse_product_deviation
    {t x y : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2)
    (hx : |x - 1| ≤ t) (hy : |y - 1| ≤ t) :
    |1 / (x * y) - 1| ≤ 8 * t := by
  rw [abs_le] at hx hy ⊢
  have hxLower : 1 - t ≤ x := by linarith [hx.1]
  have hxUpper : x ≤ 1 + t := by linarith [hx.2]
  have hyLower : 1 - t ≤ y := by linarith [hy.1]
  have hyUpper : y ≤ 1 + t := by linarith [hy.2]
  have honeMinus : 0 < 1 - t := by linarith
  have hxPos : 0 < x := lt_of_lt_of_le honeMinus hxLower
  have hyPos : 0 < y := lt_of_lt_of_le honeMinus hyLower
  have hxyPos : 0 < x * y := mul_pos hxPos hyPos
  have hxyLower : (1 - t) ^ 2 ≤ x * y := by
    nlinarith [mul_le_mul hxLower hyLower honeMinus.le hxPos.le]
  have hxyUpper : x * y ≤ (1 + t) ^ 2 := by
    have hnonneg : 0 ≤ 1 + t := by linarith
    nlinarith [mul_le_mul hxUpper hyUpper hyPos.le hnonneg]
  have hrewrite :
      1 / (x * y) - 1 = (1 - x * y) / (x * y) := by
    field_simp [ne_of_gt hxyPos]
  rw [hrewrite]
  constructor
  · apply (le_div_iff₀ hxyPos).2
    by_cases hsmall : t ≤ 1 / 8
    · have hfactor : 0 ≤ (1 - 8 * t) := by linarith
      have hmul :
          (1 - 8 * t) * (x * y) ≤
            (1 - 8 * t) * (1 + t) ^ 2 :=
        mul_le_mul_of_nonneg_left hxyUpper hfactor
      have hpoly :
          (1 - 8 * t) * (1 + t) ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg ht0 (sq_nonneg t),
          mul_nonneg (sq_nonneg t) ht0]
      nlinarith
    · have hfactor : 1 - 8 * t < 0 := by linarith
      have : (1 - 8 * t) * (x * y) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hfactor.le hxyPos.le
      nlinarith
  · apply (div_le_iff₀ hxyPos).2
    have hquadratic :
        0 ≤ 8 * t ^ 2 - 15 * t + 6 := by
      have hproduct :
          0 ≤ (1 / 2 - t) * (11 - 8 * t) := by
        apply mul_nonneg <;> linarith
      nlinarith
    have hbase :
        1 ≤ (1 + 8 * t) * (1 - t) ^ 2 := by
      nlinarith [mul_nonneg ht0 hquadratic]
    have hfactor : 0 ≤ 1 + 8 * t := by positivity
    have hmul :
        (1 + 8 * t) * (1 - t) ^ 2 ≤
          (1 + 8 * t) * (x * y) :=
      mul_le_mul_of_nonneg_left hxyLower hfactor
    nlinarith

/-- A slightly slackened version of the manuscript's bounded-refill parameter
budget.  The four error contributions are each allocated at most `η/4`,
except the explicit selection slack, which is `η/8`. -/
theorem bounded_refill_error_budget
    (gamma sigma t d B η : ℝ)
    (_hgamma : 0 ≤ gamma) (hsigma : 0 < sigma)
    (ht : 0 < t) (hd : 0 < d) (hB : 0 ≤ B) (hη : 0 < η)
    (hden16 : 16 < t ^ 2 * d)
    (htrunc : 16 * gamma ≤ η * sigma)
    (hnormalize : 32 * t * B ≤ η)
    (hconditional : 128 * (B + 1) ≤ η * t ^ 2 * d) :
    let r := 8 / (t ^ 2 * d)
    4 * gamma / sigma +
        (2 * B * r / (1 - r) + η / 8) +
        8 * t * B < η := by
  dsimp only
  let den := t ^ 2 * d
  have hden : 0 < den := by dsimp [den]; positivity
  have hden8 : 0 < den - 8 := by
    dsimp [den] at *
    linarith
  have htruncBound : 4 * gamma / sigma ≤ η / 4 := by
    apply (div_le_iff₀ hsigma).2
    nlinarith
  have hnormBound : 8 * t * B ≤ η / 4 := by
    nlinarith
  have hB1 : 0 < B + 1 := by linarith
  have hcondRaw : 32 * B / den ≤ η / 4 := by
    apply (div_le_iff₀ hden).2
    have hB_le : B ≤ B + 1 := by linarith
    have hscaled : 128 * B ≤ η * den := by
      dsimp [den] at hconditional ⊢
      nlinarith
    nlinarith
  have hrForm :
      2 * B * (8 / den) / (1 - 8 / den) =
        16 * B / (den - 8) := by
    field_simp [ne_of_gt hden, ne_of_gt hden8]
    ring
  have hcondCompare :
      16 * B / (den - 8) < 32 * B / den ∨ B = 0 := by
    by_cases hBzero : B = 0
    · exact Or.inr hBzero
    · left
      have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
      apply (div_lt_div_iff₀ hden8 hden).2
      nlinarith
  have hcondBound :
      2 * B * (8 / den) / (1 - 8 / den) ≤ η / 4 := by
    rw [hrForm]
    rcases hcondCompare with hlt | rfl
    · exact le_trans hlt.le hcondRaw
    · simp
      positivity
  change
    4 * gamma / sigma +
        (2 * B * (8 / den) / (1 - 8 / den) + η / 8) +
        8 * t * B < η
  nlinarith

/-- Algebraic shifted form of the inexact Frank--Wolfe recurrence. -/
theorem shifted_inexact_recurrence
    (fnext f τ step curvature : ℝ)
    (h : fnext ≤ (1 - step) * f + 2 * τ * step + curvature * step ^ 2) :
    fnext - 2 * τ ≤
      (1 - step) * (f - 2 * τ) + curvature * step ^ 2 := by
  linarith

/-- The numerical induction step in the manuscript's Frank--Wolfe analysis. -/
theorem recurrence_rate_step
    (t current next : ℝ)
    (ht : 0 ≤ t)
    (hcurrent : current ≤ 8 / (t + 2))
    (hnext :
      next ≤ t / (t + 2) * current + 8 / (t + 2) ^ 2) :
    next ≤ 8 / (t + 3) := by
  have ht2 : 0 < t + 2 := by linarith
  have ht3 : 0 < t + 3 := by linarith
  have hcoef : 0 ≤ t / (t + 2) := div_nonneg ht ht2.le
  calc
    next ≤ t / (t + 2) * current + 8 / (t + 2) ^ 2 := hnext
    _ ≤ t / (t + 2) * (8 / (t + 2)) + 8 / (t + 2) ^ 2 := by
      gcongr
    _ ≤ 8 / (t + 3) := by
      field_simp [ne_of_gt ht2, ne_of_gt ht3]
      nlinarith [sq_nonneg (t + 2)]

/-- Iterating the shifted recurrence yields the dimension-independent
`8/(t+2)` rate used in the weak-membership reduction. -/
theorem recurrence_rate
    (g : ℕ → ℝ)
    (hbase : g 1 ≤ 8 / 3)
    (hstep : ∀ t : ℕ, 1 ≤ t →
      g (t + 1) ≤
        (t : ℝ) / ((t : ℝ) + 2) * g t +
          8 / ((t : ℝ) + 2) ^ 2) :
    ∀ t : ℕ, 1 ≤ t → g t ≤ 8 / ((t : ℝ) + 2) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => norm_num at hbase ⊢; exact hbase
  | succ t ht ih =>
      have hs := hstep t ht
      have hrate :=
        recurrence_rate_step (t : ℝ) (g t) (g (t + 1))
          (Nat.cast_nonneg t) ih hs
      norm_num [Nat.cast_add, Nat.cast_one] at hrate ⊢
      convert hrate using 1
      ring

/-- Finite-horizon form of `recurrence_rate`.  Only the recurrence steps
strictly before the requested terminal index are needed. -/
theorem recurrence_rate_at
    (g : ℕ → ℝ) (T : ℕ)
    (hT : 1 ≤ T)
    (hbase : g 1 ≤ 8 / 3)
    (hstep : ∀ t : ℕ, 1 ≤ t → t < T →
      g (t + 1) ≤
        (t : ℝ) / ((t : ℝ) + 2) * g t +
          8 / ((t : ℝ) + 2) ^ 2) :
    g T ≤ 8 / ((T : ℝ) + 2) := by
  induction T, hT using Nat.le_induction with
  | base =>
      norm_num at hbase ⊢
      exact hbase
  | succ t ht ih =>
      have ih' : g t ≤ 8 / ((t : ℝ) + 2) :=
        ih (fun s hs hslt => hstep s hs (hslt.trans (Nat.lt_succ_self t)))
      have hs := hstep t ht (Nat.lt_succ_self t)
      have hrate :=
        recurrence_rate_step (t : ℝ) (g t) (g (t + 1))
          (Nat.cast_nonneg t) ih' hs
      norm_num [Nat.cast_add, Nat.cast_one] at hrate ⊢
      convert hrate using 1
      ring

/-- The manuscript's terminal error allocation for weak membership. -/
theorem weakMembership_final_budget
    (potential τ η iterations : ℝ)
    (hη : 0 < η)
    (hτ : τ = η ^ 2 / 64)
    (hiterations : 256 / η ^ 2 ≤ iterations)
    (hpotential : potential ≤ 2 * τ + 8 / (iterations + 2)) :
    potential ≤ η ^ 2 / 16 := by
  have hηsq : 0 < η ^ 2 := sq_pos_of_pos hη
  have hit : 0 < iterations := by
    have : 0 < 256 / η ^ 2 := div_pos (by norm_num) hηsq
    linarith
  have htail : 8 / (iterations + 2) ≤ η ^ 2 / 32 := by
    apply (div_le_iff₀ (by linarith : 0 < iterations + 2)).2
    have hscaled : 256 ≤ iterations * η ^ 2 := by
      exact (div_le_iff₀ hηsq).1 hiterations
    nlinarith
  rw [hτ] at hpotential
  nlinarith

/-- The scalar inequality chain in the rank-one part of the one-party Haar
moment bound: Hölder, the inverse Gaussian moment, hypercontractivity, and the
`L₂` estimate combine with the advertised constant. -/
theorem oneParty_rankOne_chain
    (output inverseFactor polynomialFactor l2Norm operatorNorm c q d : ℝ)
    (hd : 0 < d) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hpoly : 0 ≤ polynomialFactor)
    (hholder : output ≤ inverseFactor * polynomialFactor)
    (hinverse : inverseFactor ≤ 2 / d)
    (hhypercontractive : polynomialFactor ≤ c * q * l2Norm)
    (hwickProjection : l2Norm ≤ operatorNorm) :
    output ≤ (2 * c * q / d) * operatorNorm := by
  have hinvNonneg : 0 ≤ 2 / d := by positivity
  calc
    output ≤ inverseFactor * polynomialFactor := hholder
    _ ≤ (2 / d) * polynomialFactor :=
      mul_le_mul_of_nonneg_right hinverse hpoly
    _ ≤ (2 / d) * (c * q * l2Norm) :=
      mul_le_mul_of_nonneg_left hhypercontractive hinvNonneg
    _ ≤ (2 / d) * (c * q * operatorNorm) := by
      gcongr
    _ = (2 * c * q / d) * operatorNorm := by ring

/-- Applying the one-party estimate independently in both tensor factors gives
the `q²/d²` two-party moment scaling. -/
theorem twoParty_moment_chain
    (output intermediate matrixNorm c q d : ℝ)
    (hd : 0 < d) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hfirst : output ≤ (c * q / d) * intermediate)
    (hsecond : intermediate ≤ (c * q / d) * matrixNorm) :
    output ≤ (c ^ 2 * q ^ 2 / d ^ 2) * matrixNorm := by
  have hcoef : 0 ≤ c * q / d := by positivity
  calc
    output ≤ (c * q / d) * intermediate := hfirst
    _ ≤ (c * q / d) * ((c * q / d) * matrixNorm) :=
      mul_le_mul_of_nonneg_left hsecond hcoef
    _ = (c ^ 2 * q ^ 2 / d ^ 2) * matrixNorm := by ring

/-- Summing the single-entry truncation estimate over `d⁴` entries gives the
Frobenius tail estimate. -/
theorem entryTail_to_frobeniusTail
    (entryCount expectedEntryTail expectedFrobeniusTail normSq δ : ℝ)
    (hsum : expectedFrobeniusTail ≤ entryCount * expectedEntryTail)
    (hentry :
      expectedEntryTail ≤ (1 / 2) * normSq / entryCount * δ ^ 4)
    (hcountPos : 0 < entryCount) :
    expectedFrobeniusTail ≤ (1 / 2) * normSq * δ ^ 4 := by
  have hmul :=
    mul_le_mul_of_nonneg_left hentry hcountPos.le
  calc
    expectedFrobeniusTail ≤ entryCount * expectedEntryTail := hsum
    _ ≤ entryCount * ((1 / 2) * normSq / entryCount * δ ^ 4) := hmul
    _ ≤ (1 / 2) * normSq * δ ^ 4 := by
      field_simp [ne_of_gt hcountPos]
      rfl

/-- The final Markov step in the flat/tail lemma, stated as the exact scalar
implication used after bounding the expected squared Frobenius tail. -/
theorem frobeniusTail_markov_chain
    (expectedTailSq normSq δ failureProbability : ℝ)
    (hnorm : 0 < normSq) (hδ : 0 < δ)
    (hexpect : expectedTailSq ≤ (1 / 2) * normSq * δ ^ 4)
    (hmarkov :
      failureProbability ≤ expectedTailSq / (normSq * δ ^ 2)) :
    failureProbability ≤ δ ^ 2 := by
  have hden : 0 < normSq * δ ^ 2 := mul_pos hnorm (sq_pos_of_pos hδ)
  have hdiv :
      expectedTailSq / (normSq * δ ^ 2) ≤ δ ^ 2 / 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  linarith [sq_nonneg δ]

/-- Converting the terminal potential bound into the manuscript's
`η/2` Frobenius-distance acceptance threshold. -/
theorem potentialBound_to_halfGap
    (distance potential η : ℝ)
    (hdistance : 0 ≤ distance) (hη : 0 ≤ η)
    (hdistanceSq : distance ^ 2 = 2 * potential)
    (hpotential : potential ≤ η ^ 2 / 16) :
    distance ≤ η / 2 := by
  nlinarith [sq_nonneg (distance + η / 2)]

/-- A point farther than `η` from every feasible point cannot pass the
`η/2` acceptance test for a feasible iterate. -/
theorem farPoint_fails_halfGapTest
    (distance η : ℝ) (hη : 0 ≤ η) (hfar : η < distance) :
    ¬ distance ≤ η / 2 := by
  intro haccept
  linarith

/-- Negating an approximate lower bound produces a *positive* additive error. -/
theorem negate_approx_lower_bound (a b ε : ℝ) (h : a ≥ b - ε) :
    -a ≤ -b + ε := by
  linarith

/-- The elementary probability amplification estimate used in the paper. -/
theorem union_bound_constant {T ℓ : ℕ}
    (h : (T : ℝ) * (1 / 3 : ℝ) ^ ℓ ≤ 1 / 3) :
    (T : ℝ) * (1 / 3 : ℝ) ^ ℓ ≤ 1 / 3 := h

/-- The error allocation used in the corrected final theorem closes exactly:
two truncation errors, two discretization errors, the CSP error, and the
high-dimensional local-term error sum to at most the target accuracy. -/
theorem final_error_budget
    (τ δ η dimensionError : ℝ)
    (hδ : δ = τ / 16)
    (hη : η = τ / 4)
    (hdimension : dimensionError ≤ τ / 8) :
    2 * δ + η + τ / 4 + dimensionError + η ≤ τ := by
  rw [hδ, hη]
  linarith

/-- A single flat-tail constant must dominate the constants from both
dimension branches. -/
def flatTailConstant (lowDimensionConstant highDimensionConstant : ℝ) : ℝ :=
  max lowDimensionConstant highDimensionConstant

theorem lowDimensionConstant_le_flatTailConstant (low high : ℝ) :
    low ≤ flatTailConstant low high :=
  le_max_left _ _

theorem highDimensionConstant_le_flatTailConstant (low high : ℝ) :
    high ≤ flatTailConstant low high :=
  le_max_right _ _

end QuantumSep
