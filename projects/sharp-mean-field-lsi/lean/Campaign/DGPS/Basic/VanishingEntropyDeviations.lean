import DGPS.Basic.Tightening

/-!
# Vanishing entropy: normalized deviations and tail estimates (LIP082)

Setting: the abstract tightening hypotheses `TighteningHyp P E S R` of LIP079 and a sequence of
nonnegative mass-one tests `f k ∈ S (n k)` with `Ent(f k ^ 2) = h k > 0` and `2 E (f k) < r h k`
(the output of LIP079), with `h k → 0`.

* `∫ (f k - 1)^2 ≤ h k` (from `Φ(s) ≥ (s-1)²`), and `∫ f k - 1 = -(1/2) ∫ (f k - 1)^2`.
* `v k = (f k - 1) / √(h k)` lies in `S (n k)`, has `∫ v k ^ 2 ≤ 1`, `E (v k) < r / 2`, and
  `v k ^ 2` is uniformly integrable (LIP050).
* For every `A0 > 1`, with `t = (f - A0)⁺` and `g = min f A0`, the quantities `∫ t² / h`,
  `∫ t / h` and `(∫ g - 1)² / h` tend to zero.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Analysis

/-- Pointwise: `(s-1)² ≤ s² log s² - s² + 1` for `s ≥ 0`. -/
theorem sub_one_sq_le_entropyIntegrand {s : ℝ} (hs : 0 ≤ s) :
    (s - 1) ^ 2 ≤ entropyIntegrand 1 (s ^ 2) := by
  have h := self_mul_log_sub_add_one_nonneg hs
  have hl : Real.log (s ^ 2) = 2 * Real.log s := by
    rw [Real.log_pow]; push_cast; ring
  simp only [entropyIntegrand, div_one, hl]
  nlinarith [mul_nonneg hs h]

/-- `∫ (f-1)² ≤ h` for a nonnegative mass-one `f` with `Ent(f²) = h`. -/
theorem integral_sub_one_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {h : ℝ} (hm : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hsi : Integrable (fun x => f x ^ 2) P) (hmass : ∫ x, f x ^ 2 ∂P = 1) (h0 : 0 ≤ h)
    (hent : homogeneousEntropy P (fun x => f x ^ 2) = ENNReal.ofReal h) :
    Integrable (fun x => (f x - 1) ^ 2) P ∧ ∫ x, (f x - 1) ^ 2 ∂P ≤ h := by
  have hint : Integrable (fun x => (f x - 1) ^ 2) P := by
    refine Integrable.mono' ((hsi.const_mul 2).add (integrable_const (2 : ℝ))) (by fun_prop)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (f x + 1)]
  refine ⟨hint, ?_⟩
  rw [homogeneousEntropy_of_integral_ne_zero (by rw [hmass]; exact one_ne_zero), hmass] at hent
  have h1 : ENNReal.ofReal (∫ x, (f x - 1) ^ 2 ∂P) ≤ ENNReal.ofReal h := by
    rw [← hent, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    exact lintegral_mono fun x =>
      ENNReal.ofReal_le_ofReal (sub_one_sq_le_entropyIntegrand (hnn x))
  exact (ENNReal.ofReal_le_ofReal_iff h0).mp h1

/-- `∫ f = 1 - (1/2) ∫ (f-1)²` for a mass-one `f`. -/
theorem integral_eq_one_sub_half {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hm : Measurable f)
    (hsi : Integrable (fun x => f x ^ 2) P) (hmass : ∫ x, f x ^ 2 ∂P = 1) :
    ∫ x, f x ∂P = 1 - (1 / 2) * ∫ x, (f x - 1) ^ 2 ∂P := by
  have hfi : Integrable f P := by
    refine Integrable.mono' (hsi.add (integrable_const (1 : ℝ))) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith [abs_nonneg (f x), sq_abs (f x), sq_nonneg (|f x| - 1)]
  have e : (fun x => (f x - 1) ^ 2) = fun x => (f x ^ 2 - 2 * f x) + 1 := by
    funext x; ring
  have h1 : ∫ x, (f x ^ 2 - 2 * f x + 1) ∂P
      = ∫ x, f x ^ 2 ∂P - 2 * ∫ x, f x ∂P + 1 := by
    rw [integral_add (f := fun x => f x ^ 2 - 2 * f x) (g := fun _ => (1 : ℝ))
      (hsi.sub (hfi.const_mul 2)) (integrable_const _),
      integral_sub (f := fun x => f x ^ 2) (g := fun x => 2 * f x) hsi (hfi.const_mul 2),
      integral_const_mul]
    simp
  rw [e, h1, hmass]
  ring

/-- Tail estimates for a single test, in terms of a threshold `K ≤ (A0-1)²/h`. -/
theorem tail_integrals_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {h A0 K : ℝ} (hm : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hsi : Integrable (fun x => f x ^ 2) P) (hh : 0 < h) (hA : 1 < A0)
    (hK : K ≤ (A0 - 1) ^ 2 / h) :
    ∫ x, (max (f x - A0) 0) ^ 2 ∂P
        ≤ h * ∫ x in {x | K < ((f x - 1) / Real.sqrt h) ^ 2}, ((f x - 1) / Real.sqrt h) ^ 2 ∂P ∧
    ∫ x, max (f x - A0) 0 ∂P
        ≤ h / (A0 - 1) *
          ∫ x in {x | K < ((f x - 1) / Real.sqrt h) ^ 2}, ((f x - 1) / Real.sqrt h) ^ 2 ∂P := by
  have hsq : Real.sqrt h ^ 2 = h := Real.sq_sqrt hh.le
  have hV : ∀ x, ((f x - 1) / Real.sqrt h) ^ 2 = (f x - 1) ^ 2 / h := fun x => by
    rw [div_pow, hsq]
  have hVm : Measurable fun x => ((f x - 1) / Real.sqrt h) ^ 2 := by fun_prop
  have hsi1 : Integrable (fun x => (f x - 1) ^ 2) P := by
    refine Integrable.mono' ((hsi.const_mul 2).add (integrable_const (2 : ℝ))) (by fun_prop)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (f x + 1)]
  have hVi : Integrable (fun x => ((f x - 1) / Real.sqrt h) ^ 2) P := by
    simp only [hV]; exact hsi1.div_const h
  have hset : MeasurableSet {x | K < ((f x - 1) / Real.sqrt h) ^ 2} :=
    measurableSet_lt measurable_const hVm
  have htm : Measurable fun x => max (f x - A0) 0 := (hm.sub_const A0).max measurable_const
  have htle : ∀ x, max (f x - A0) 0 ≤ f x := fun x => max_le (by linarith) (hnn x)
  have ht0 : ∀ x, 0 ≤ max (f x - A0) 0 := fun x => le_max_right _ _
  have hti : Integrable (fun x => max (f x - A0) 0) P := by
    refine Integrable.mono' (hsi.add (integrable_const (1 : ℝ))) htm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (ht0 x)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (f x - 1), htle x]
  have hti2 : Integrable (fun x => (max (f x - A0) 0) ^ 2) P := by
    refine Integrable.mono' hsi (htm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (ht0 x) (htle x) 2
  -- on the tail the threshold is exceeded
  have hin : ∀ x, A0 < f x → K < ((f x - 1) / Real.sqrt h) ^ 2 := by
    intro x hx
    rw [hV]
    have h1 : (A0 - 1) ^ 2 < (f x - 1) ^ 2 :=
      pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
    have h2 : (A0 - 1) ^ 2 / h < (f x - 1) ^ 2 / h := div_lt_div_of_pos_right h1 hh
    linarith
  constructor
  · have hG : Integrable ({x | K < ((f x - 1) / Real.sqrt h) ^ 2}.indicator
        (fun x => h * ((f x - 1) / Real.sqrt h) ^ 2)) P :=
      (hVi.const_mul h).indicator hset
    calc ∫ x, (max (f x - A0) 0) ^ 2 ∂P
        ≤ ∫ x, {x | K < ((f x - 1) / Real.sqrt h) ^ 2}.indicator
            (fun x => h * ((f x - 1) / Real.sqrt h) ^ 2) x ∂P := by
          refine integral_mono hti2 hG fun x => ?_
          by_cases hx : A0 < f x
          · rw [Set.indicator_of_mem (show x ∈ {x | K < ((f x - 1) / Real.sqrt h) ^ 2} from hin x hx), hV]
            have : max (f x - A0) 0 = f x - A0 := max_eq_left (by linarith)
            rw [this]
            have e : h * ((f x - 1) ^ 2 / h) = (f x - 1) ^ 2 := by field_simp
            rw [e]
            exact pow_le_pow_left₀ (by linarith) (by linarith) 2
          · have : max (f x - A0) 0 = 0 := max_eq_right (by linarith [not_lt.mp hx])
            rw [this]
            exact le_trans (by norm_num) (Set.indicator_nonneg
              (fun y _ => mul_nonneg hh.le (sq_nonneg _)) x)
      _ = h * ∫ x in {x | K < ((f x - 1) / Real.sqrt h) ^ 2},
            ((f x - 1) / Real.sqrt h) ^ 2 ∂P := by
          rw [integral_indicator hset, integral_const_mul]
  · have hA1 : 0 < A0 - 1 := by linarith
    have hG : Integrable ({x | K < ((f x - 1) / Real.sqrt h) ^ 2}.indicator
        (fun x => h / (A0 - 1) * ((f x - 1) / Real.sqrt h) ^ 2)) P :=
      (hVi.const_mul (h / (A0 - 1))).indicator hset
    calc ∫ x, max (f x - A0) 0 ∂P
        ≤ ∫ x, {x | K < ((f x - 1) / Real.sqrt h) ^ 2}.indicator
            (fun x => h / (A0 - 1) * ((f x - 1) / Real.sqrt h) ^ 2) x ∂P := by
          refine integral_mono hti hG fun x => ?_
          by_cases hx : A0 < f x
          · rw [Set.indicator_of_mem (show x ∈ {x | K < ((f x - 1) / Real.sqrt h) ^ 2} from hin x hx), hV]
            have : max (f x - A0) 0 = f x - A0 := max_eq_left (by linarith)
            rw [this]
            have e : h / (A0 - 1) * ((f x - 1) ^ 2 / h) = (f x - 1) ^ 2 / (A0 - 1) := by
              field_simp
            rw [e, le_div_iff₀ hA1]
            nlinarith
          · have : max (f x - A0) 0 = 0 := max_eq_right (by linarith [not_lt.mp hx])
            rw [this]
            exact le_trans (le_refl _) (Set.indicator_nonneg
              (fun y _ => mul_nonneg (div_nonneg hh.le hA1.le) (sq_nonneg _)) x)
      _ = h / (A0 - 1) * ∫ x in {x | K < ((f x - 1) / Real.sqrt h) ^ 2},
            ((f x - 1) / Real.sqrt h) ^ 2 ∂P := by
          rw [integral_indicator hset, integral_const_mul]

theorem tendsto_zero_of_eventually_le {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k)
    (H : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, u k ≤ ε) : Tendsto u atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun k => lt_of_lt_of_le ha (hu k),
    fun a ha => (H (a / 2) (by linarith)).mono fun k hk => by linarith⟩

/-- LIP082.  Under the abstract tightening hypotheses, let `f k ∈ S (n k)` be nonnegative with
`∫ (f k)² = 1`, `Ent((f k)²) = h k > 0`, `2 E (f k) < r h k`, and `h k → 0`.  Then the normalized
deviations `v k = (f k - 1)/√(h k)` lie in `S (n k)`, satisfy `∫ (v k)² ≤ 1`, `E (v k) < r/2`, and
have uniformly integrable squares; and for every `A0 > 1`, with `t = (f - A0)⁺` and
`g = min f A0`, `∫ t² = o(h_k)`, `∫ t = o(h_k)` and `(∫ g - 1)² = o(h_k)`. -/
theorem vanishing_entropy_normalized_deviations_and_tail_estimates
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)] {E : ∀ n, (Ω n → ℝ) → ℝ}
    {S : ∀ n, Set (Ω n → ℝ)} {R : ℝ} (hyp : TighteningHyp P E S R) {r : ℝ} (hr : 0 < r)
    (hrR : r < R) (n : ℕ → ℕ) (f : ∀ k, Ω (n k) → ℝ) (h : ℕ → ℝ)
    (hf : ∀ k, f k ∈ S (n k) ∧ (∀ x, 0 ≤ f k x) ∧ ∫ x, f k x ^ 2 ∂P (n k) = 1 ∧
      homogeneousEntropy (P (n k)) (fun x => f k x ^ 2) = ENNReal.ofReal (h k) ∧ 0 < h k ∧
      2 * E (n k) (f k) < r * h k)
    (hh : Tendsto h atTop (𝓝 0)) :
    (∀ k, (fun x => (f k x - 1) / Real.sqrt (h k)) ∈ S (n k)) ∧
    (∀ k, ∫ x, ((f k x - 1) / Real.sqrt (h k)) ^ 2 ∂P (n k) ≤ 1) ∧
    (∀ k, E (n k) (fun x => (f k x - 1) / Real.sqrt (h k)) < r / 2) ∧
    UniformSquareIntegrable (fun k => P (n k)) (fun k x => (f k x - 1) / Real.sqrt (h k)) ∧
    ∀ A0 : ℝ, 1 < A0 →
      Tendsto (fun k => (∫ x, (max (f k x - A0) 0) ^ 2 ∂P (n k)) / h k) atTop (𝓝 0) ∧
      Tendsto (fun k => (∫ x, max (f k x - A0) 0 ∂P (n k)) / h k) atTop (𝓝 0) ∧
      Tendsto (fun k => (∫ x, min (f k x) A0 ∂P (n k) - 1) ^ 2 / h k) atTop (𝓝 0) := by
  have hsq : ∀ k, Real.sqrt (h k) ^ 2 = h k := fun k => Real.sq_sqrt (hf k).2.2.2.2.1.le
  have hsp : ∀ k, 0 < Real.sqrt (h k) := fun k => Real.sqrt_pos.2 (hf k).2.2.2.2.1
  have hmem : ∀ k, (fun x => (f k x - 1) / Real.sqrt (h k)) ∈ S (n k) := by
    intro k
    have := hyp.affine_mem (n k) (f k) (hf k).1 (1 / Real.sqrt (h k)) (-(1 / Real.sqrt (h k)))
    convert this using 1
    funext x
    field_simp
    ring
  have hen : ∀ k, E (n k) (fun x => (f k x - 1) / Real.sqrt (h k)) < r / 2 := by
    intro k
    have := hyp.energy_affine (n k) (f k) (hf k).1 (1 / Real.sqrt (h k)) (-(1 / Real.sqrt (h k)))
    have e : (fun x => (f k x - 1) / Real.sqrt (h k))
        = fun x => 1 / Real.sqrt (h k) * f k x + -(1 / Real.sqrt (h k)) := by
      funext x; field_simp; ring
    rw [e, this, div_pow, hsq, one_pow]
    have hk := (hf k).2.2.2.2.2
    have hpos := (hf k).2.2.2.2.1
    rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
    linarith
  have hmeas : ∀ k, Measurable (f k) := fun k => hyp.measurable _ _ (hf k).1
  have hdev : ∀ k, Integrable (fun x => (f k x - 1) ^ 2) (P (n k)) ∧
      ∫ x, (f k x - 1) ^ 2 ∂P (n k) ≤ h k := fun k =>
    integral_sub_one_sq_le (hmeas k) (hf k).2.1 (hyp.sq_integrable _ _ (hf k).1)
      (hf k).2.2.1 (hf k).2.2.2.2.1.le (hf k).2.2.2.1
  have hV : ∀ k, ∫ x, ((f k x - 1) / Real.sqrt (h k)) ^ 2 ∂P (n k)
      = (∫ x, (f k x - 1) ^ 2 ∂P (n k)) / h k := by
    intro k
    simp only [div_pow, hsq]
    exact integral_div _ _
  have hV1 : ∀ k, ∫ x, ((f k x - 1) / Real.sqrt (h k)) ^ 2 ∂P (n k) ≤ 1 := by
    intro k
    rw [hV, div_le_one (hf k).2.2.2.2.1]
    exact (hdev k).2
  have hUI : UniformSquareIntegrable (fun k => P (n k)) (fun k x => (f k x - 1) / Real.sqrt (h k)) := by
    obtain ⟨Cd, hCd⟩ := hyp.defective ((r + R) / 2) (by linarith) (by linarith)
    refine uniform_square_integrability_from_a_defective_entropy_bound P E S
      (2 / ((r + R) / 2)) Cd hyp.measurable hyp.sq_integrable ?_ n
      (fun k x => (f k x - 1) / Real.sqrt (h k)) hmem 1 (r / 2) hV1 (fun k => ?_)
    · intro m g hg
      rw [show 2 / ((r + R) / 2) * E m g = 2 * E m g / ((r + R) / 2) by ring]
      exact hCd m g hg
    · rw [abs_of_nonneg (by
        have := hyp.energy_nonneg (n k) _ (hmem k)
        exact this)]
      exact (hen k).le
  refine ⟨hmem, hV1, hen, hUI, fun A0 hA => ?_⟩
  have hA1 : 0 < A0 - 1 := by linarith
  -- eventually the threshold is exceeded
  have hthr : ∀ K : ℝ, ∀ᶠ k in atTop, K ≤ (A0 - 1) ^ 2 / h k := by
    intro K
    have hδ : 0 < (A0 - 1) ^ 2 / (|K| + 1) := by positivity
    filter_upwards [hh.eventually (gt_mem_nhds hδ)] with k hk
    have hpos := (hf k).2.2.2.2.1
    have h1 : (A0 - 1) ^ 2 / ((A0 - 1) ^ 2 / (|K| + 1)) ≤ (A0 - 1) ^ 2 / h k :=
      div_le_div_of_nonneg_left (by positivity) hpos hk.le
    have h2 : (A0 - 1) ^ 2 / ((A0 - 1) ^ 2 / (|K| + 1)) = |K| + 1 := by
      field_simp
    linarith [le_abs_self K]
  -- the two tail estimates
  have hT2 : Tendsto (fun k => (∫ x, (max (f k x - A0) 0) ^ 2 ∂P (n k)) / h k) atTop (𝓝 0) := by
    refine tendsto_zero_of_eventually_le (fun k => ?_) fun ε hε => ?_
    · exact div_nonneg (integral_nonneg fun x => sq_nonneg _) (hf k).2.2.2.2.1.le
    · obtain ⟨K, hK⟩ := hUI ε hε
      filter_upwards [hthr K] with k hk
      have := (tail_integrals_le (hmeas k) (hf k).2.1 (hyp.sq_integrable _ _ (hf k).1)
        (hf k).2.2.2.2.1 hA hk).1
      rw [div_le_iff₀ (hf k).2.2.2.2.1]
      have h3 := hK k
      calc _ ≤ _ := this
        _ ≤ ε * h k := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right h3 (hf k).2.2.2.2.1.le
  have hT1 : Tendsto (fun k => (∫ x, max (f k x - A0) 0 ∂P (n k)) / h k) atTop (𝓝 0) := by
    refine tendsto_zero_of_eventually_le (fun k => ?_) fun ε hε => ?_
    · exact div_nonneg (integral_nonneg fun x => le_max_right _ _) (hf k).2.2.2.2.1.le
    · obtain ⟨K, hK⟩ := hUI (ε * (A0 - 1)) (by positivity)
      filter_upwards [hthr K] with k hk
      have hpos := (hf k).2.2.2.2.1
      have := (tail_integrals_le (hmeas k) (hf k).2.1 (hyp.sq_integrable _ _ (hf k).1)
        hpos hA hk).2
      rw [div_le_iff₀ hpos]
      have h3 := hK k
      have h4 : h k / (A0 - 1) * ∫ x in {x | K < ((f k x - 1) / Real.sqrt (h k)) ^ 2},
          ((f k x - 1) / Real.sqrt (h k)) ^ 2 ∂P (n k) ≤ ε * h k := by
        calc _ ≤ h k / (A0 - 1) * (ε * (A0 - 1)) :=
              mul_le_mul_of_nonneg_left h3 (div_nonneg hpos.le hA1.le)
          _ = ε * h k := by field_simp
      exact this.trans h4
  refine ⟨hT2, hT1, ?_⟩
  -- the truncated mean
  have hmin : ∀ k, ∫ x, min (f k x) A0 ∂P (n k) - 1
      = -((1 / 2) * ∫ x, (f k x - 1) ^ 2 ∂P (n k) + ∫ x, max (f k x - A0) 0 ∂P (n k)) := by
    intro k
    have hsi := hyp.sq_integrable _ _ (hf k).1
    have hfi : Integrable (f k) (P (n k)) := by
      refine Integrable.mono' (hsi.add (integrable_const (1 : ℝ))) (hmeas k).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs]
      simp only [Pi.add_apply]
      nlinarith [abs_nonneg (f k x), sq_abs (f k x), sq_nonneg (|f k x| - 1)]
    have htm : Measurable fun x => max (f k x - A0) 0 :=
      ((hmeas k).sub_const A0).max measurable_const
    have hti : Integrable (fun x => max (f k x - A0) 0) (P (n k)) := by
      refine Integrable.mono' (hsi.add (integrable_const (1 : ℝ))) htm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      have : max (f k x - A0) 0 ≤ f k x := max_le (by linarith) ((hf k).2.1 x)
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (f k x - 1)]
    have e : (fun x => min (f k x) A0) = fun x => f k x - max (f k x - A0) 0 := by
      funext x
      rcases le_total (f k x) A0 with h1 | h1
      · rw [min_eq_left h1, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h1, max_eq_left (by linarith)]; ring
    rw [e, integral_sub hfi hti, integral_eq_one_sub_half (hmeas k) hsi (hf k).2.2.1]
    ring
  have hmax0 : ∀ k, 0 ≤ ∫ x, max (f k x - A0) 0 ∂P (n k) :=
    fun k => integral_nonneg fun x => le_max_right _ _
  have hD0 : ∀ k, 0 ≤ ∫ x, (f k x - 1) ^ 2 ∂P (n k) :=
    fun k => integral_nonneg fun x => sq_nonneg _
  have hup : Tendsto (fun k => h k * (1 / 2 + (∫ x, max (f k x - A0) 0 ∂P (n k)) / h k) ^ 2)
      atTop (𝓝 0) := by
    have := hh.mul (((tendsto_const_nhds (x := (1 / 2 : ℝ))).add hT1).pow 2)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun k => div_nonneg (sq_nonneg _) (hf k).2.2.2.2.1.le) (fun k => ?_)
  have hpos := (hf k).2.2.2.2.1
  rw [hmin k, neg_sq, div_le_iff₀ hpos]
  have e : h k * (1 / 2 + (∫ x, max (f k x - A0) 0 ∂P (n k)) / h k) ^ 2 * h k
      = (h k / 2 + ∫ x, max (f k x - A0) 0 ∂P (n k)) ^ 2 := by
    field_simp
  rw [e]
  have h1 := (hdev k).2
  have h2 := hD0 k
  have h3 := hmax0 k
  nlinarith

end DGPS.Analysis
