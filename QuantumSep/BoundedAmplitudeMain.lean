import QuantumSep.Normalization

/-!
# Complete bounded-amplitude witness theorem

This assembles truncation, phase refill, simultaneous good-event selection,
and renormalization into one witness theorem.
-/

namespace QuantumSep

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Quantitative bounded-amplitude theorem before fixing the manuscript's
parameters.  The harmless positive `slack` comes from selecting a point from a
strict finite conditional average; it can be made arbitrarily small. -/
theorem exists_bounded_normalized_quartic_witness
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (gamma sigma t slack : ℝ)
    (hgamma : 0 ≤ gamma) (hsigma : 0 < sigma)
    (ht0 : 0 ≤ t) (htpos : 0 < t) (ht : t ≤ 1 / 2)
    (hslack : 0 < slack)
    (hnormX : vectorNormSq x = Fintype.card ι)
    (hnormY : vectorNormSq y = Fintype.card ι)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤
        gamma / cardR (ι := ι) ^ 2)
    (htrace0 : partialTrace0 M = 0)
    (htrace1 : partialTrace1 M = 0)
    (hdimension : 8 < t ^ 2 * Fintype.card ι) :
    let r := 8 / (t ^ 2 * Fintype.card ι)
    let B := gamma * (sigma + 1) ^ 4
    ∃ xhat yhat,
      vectorNormSq xhat = Fintype.card ι ∧
      vectorNormSq yhat = Fintype.card ι ∧
      (∀ i, ‖xhat i‖ ≤ 2 * (sigma + 1)) ∧
      (∀ i, ‖yhat i‖ ≤ 2 * (sigma + 1)) ∧
      matrixQuarticForm M xhat yhat >
        matrixQuarticForm M x y -
          (4 * gamma / sigma +
            (2 * B * r / (1 - r) + slack) +
            8 * t * B) := by
  dsimp only
  let xt := truncateVector sigma x
  let yt := truncateVector sigma y
  let ampX := refillAmplitude xt
  let ampY := refillAmplitude yt
  have hnormXt :
      vectorNormSq xt ≤ Fintype.card ι := by
    dsimp [xt]
    calc
      vectorNormSq (truncateVector sigma x) ≤ vectorNormSq x :=
        vectorNormSq_truncate_le sigma x
      _ = Fintype.card ι := hnormX
  have hnormYt :
      vectorNormSq yt ≤ Fintype.card ι := by
    dsimp [yt]
    calc
      vectorNormSq (truncateVector sigma y) ≤ vectorNormSq y :=
        vectorNormSq_truncate_le sigma y
      _ = Fintype.card ι := hnormY
  have hcoordXt : ∀ i, ‖xt i‖ ≤ sigma := by
    intro i
    exact truncateVector_norm_le_threshold sigma x hsigma.le i
  have hcoordYt : ∀ i, ‖yt i‖ ≤ sigma := by
    intro i
    exact truncateVector_norm_le_threshold sigma y hsigma.le i
  obtain ⟨ξ, ζ, hdevX, hdevY, hvalue⟩ :=
    exists_refill_pair_good_norms_and_value
      M xt yt gamma sigma t slack
      hgamma hsigma.le htpos hslack
      hnormXt hnormYt hcoordXt hcoordYt
      hentry htrace0 htrace1 hdimension
  let breveX := refillVector xt ampX ξ
  let breveY := refillVector yt ampY ζ
  let xhat := normalizeVectorToCard breveX
  let yhat := normalizeVectorToCard breveY
  have htlt : t < 1 := by linarith
  have hbreveXPos : 0 < vectorNormSq breveX :=
    vectorNormSq_pos_of_raw_deviation breveX t htlt hdevX
  have hbreveYPos : 0 < vectorNormSq breveY :=
    vectorNormSq_pos_of_raw_deviation breveY t htlt hdevY
  have hcoordBreveX : ∀ i, ‖breveX i‖ ≤ sigma + 1 := by
    intro i
    exact refillVector_norm_le xt sigma ξ hcoordXt i
  have hcoordBreveY : ∀ i, ‖breveY i‖ ≤ sigma + 1 := by
    intro i
    exact refillVector_norm_le yt sigma ζ hcoordYt i
  have hBnonneg : 0 ≤ gamma * (sigma + 1) ^ 4 := by positivity
  have hQBreve :
      |matrixQuarticForm M breveX breveY| ≤
        gamma * (sigma + 1) ^ 4 :=
    abs_matrixQuarticForm_le_of_coordinate_bound
      M breveX breveY gamma (sigma + 1)
      hgamma (by linarith) hentry hcoordBreveX hcoordBreveY
  have hnormalize :
      matrixQuarticForm M xhat yhat ≥
        matrixQuarticForm M breveX breveY -
          8 * t * (gamma * (sigma + 1) ^ 4) :=
    matrixQuarticForm_normalize_lower_bound
      M breveX breveY t (gamma * (sigma + 1) ^ 4)
      ht0 ht hdevX hdevY hQBreve
  have htruncate :=
    abs_matrixQuarticForm_sub_truncate_le
      M x y gamma sigma hgamma hsigma
      hentry hnormX hnormY
  refine ⟨xhat, yhat, ?_, ?_, ?_, ?_, ?_⟩
  · exact vectorNormSq_normalizeVectorToCard breveX hbreveXPos
  · exact vectorNormSq_normalizeVectorToCard breveY hbreveYPos
  · intro i
    exact norm_normalizeVectorToCard_le_two_mul
      breveX (sigma + 1) t ht0 ht hcoordBreveX hdevX i
  · intro i
    exact norm_normalizeVectorToCard_le_two_mul
      breveY (sigma + 1) t ht0 ht hcoordBreveY hdevY i
  · dsimp [xt, yt, ampX, ampY, breveX, breveY] at hvalue
    dsimp [xhat, yhat]
    have htruncateLower :
        matrixQuarticForm M
            (truncateVector sigma x) (truncateVector sigma y) ≥
          matrixQuarticForm M x y - 4 * gamma / sigma := by
      have hh := (abs_le.mp htruncate).2
      linarith
    linarith

/-- Error-budget form of the bounded-amplitude lemma.  The hypotheses are
explicit polynomial inequalities in the chosen parameters. -/
theorem exists_bounded_normalized_quartic_witness_within
    (M : BipartiteMatrix ι) (x y : ι → ℂ)
    (gamma sigma t η : ℝ)
    (hgamma : 0 ≤ gamma) (hsigma : 0 < sigma)
    (htpos : 0 < t) (ht : t ≤ 1 / 2)
    (hη : 0 < η)
    (hnormX : vectorNormSq x = Fintype.card ι)
    (hnormY : vectorNormSq y = Fintype.card ι)
    (hentry : ∀ a b c e,
      ‖M (a, c) (b, e)‖ ≤
        gamma / cardR (ι := ι) ^ 2)
    (htrace0 : partialTrace0 M = 0)
    (htrace1 : partialTrace1 M = 0)
    (hden16 : 16 < t ^ 2 * Fintype.card ι)
    (htrunc : 16 * gamma ≤ η * sigma)
    (hnormalize :
      32 * t * (gamma * (sigma + 1) ^ 4) ≤ η)
    (hconditional :
      128 * (gamma * (sigma + 1) ^ 4 + 1) ≤
        η * t ^ 2 * Fintype.card ι) :
    ∃ xhat yhat,
      vectorNormSq xhat = Fintype.card ι ∧
      vectorNormSq yhat = Fintype.card ι ∧
      (∀ i, ‖xhat i‖ ≤ 2 * (sigma + 1)) ∧
      (∀ i, ‖yhat i‖ ≤ 2 * (sigma + 1)) ∧
      matrixQuarticForm M xhat yhat >
        matrixQuarticForm M x y - η := by
  have hd : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have ht0 : 0 ≤ t := htpos.le
  have hdimension : 8 < t ^ 2 * Fintype.card ι := by
    linarith
  obtain ⟨xhat, yhat, hxnorm, hynorm, hxcoord, hycoord, hvalue⟩ :=
    exists_bounded_normalized_quartic_witness
      M x y gamma sigma t (η / 8)
      hgamma hsigma ht0 htpos ht (by positivity)
      hnormX hnormY hentry htrace0 htrace1 hdimension
  have hB : 0 ≤ gamma * (sigma + 1) ^ 4 := by positivity
  have hbudget :=
    bounded_refill_error_budget
      gamma sigma t (Fintype.card ι)
      (gamma * (sigma + 1) ^ 4) η
      hgamma hsigma htpos hd hB hη
      hden16 htrunc hnormalize hconditional
  refine ⟨xhat, yhat, hxnorm, hynorm, hxcoord, hycoord, ?_⟩
  linarith

end

end QuantumSep
