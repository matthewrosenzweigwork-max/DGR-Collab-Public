import SharpSymmetricLSI.Paper.GaussLaw5

/-!
# R27 groundwork: truncation and uniform `L^q` bounds (`q > 1`)

* `w - min(w, M) ≤ M^{1-q} w^q` for `w ≥ 0`, so `|∫ h w - ∫ h min(w,M)| ≤ c M^{1-q} ∫ w^q`
  for `|h| ≤ c`.
* Fatou: a.e. limits of nonnegative functions with `∫ f_k ≤ B` are integrable with `∫ ≤ B`.
* Vitali for `L^q`-bounded nonnegative sequences converging a.e.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal

namespace SharpLSI

theorem sub_min_le_rpow {w M q : ℝ} (hw : 0 ≤ w) (hM : 0 < M) (hq : 1 ≤ q) :
    w - min w M ≤ M ^ (1 - q) * w ^ q := by
  rcases le_or_gt w M with h | h
  · rw [min_eq_left h, sub_self]; positivity
  · rw [min_eq_right h.le]
    have hw' : 0 < w := hM.trans h
    have h1 : w ^ q = w * w ^ (q - 1) := by
      rw [← Real.rpow_one_add' hw'.le (by linarith), add_sub_cancel]
    have h2 : M ^ (1 - q) * w ^ (q - 1) = (w / M) ^ (q - 1) := by
      rw [Real.div_rpow hw'.le hM.le, show 1 - q = -(q - 1) by ring, Real.rpow_neg hM.le]
      ring
    have h3 : 1 ≤ (w / M) ^ (q - 1) :=
      Real.one_le_rpow ((one_le_div hM).2 h.le) (by linarith)
    rw [h1, mul_left_comm, h2]
    nlinarith

theorem abs_integral_sub_min_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {w h : Ω → ℝ} (hw0 : ∀ x, 0 ≤ w x) (hwi : Integrable w P) {q : ℝ}
    (hq : 1 ≤ q) (hwq : Integrable (fun x => w x ^ q) P) {M : ℝ} (hM : 0 < M) {c : ℝ}
    (hh : ∀ x, |h x| ≤ c) (hhm : AEStronglyMeasurable h P) :
    |∫ x, h x * w x ∂P - ∫ x, h x * min (w x) M ∂P| ≤ c * M ^ (1 - q) * ∫ x, w x ^ q ∂P := by
  have hb : ∀ x, ‖h x‖ ≤ c := fun x => by rw [Real.norm_eq_abs]; exact hh x
  have hmin : Integrable (fun x => min (w x) M) P :=
    hwi.inf (integrable_const M)
  have i1 : Integrable (fun x => h x * w x) P := hwi.bdd_mul hhm (Eventually.of_forall hb)
  have i2 : Integrable (fun x => h x * min (w x) M) P :=
    hmin.bdd_mul hhm (Eventually.of_forall hb)
  rw [← integral_sub i1 i2, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono (i1.sub i2).abs
    (hwq.const_mul _) fun x => ?_)
  have hc : 0 ≤ c := (abs_nonneg _).trans (hh x)
  simp only [← mul_sub, abs_mul]
  have h1 : |w x - min (w x) M| = w x - min (w x) M := abs_of_nonneg (by simp)
  rw [h1, mul_assoc]
  exact mul_le_mul (hh x) (sub_min_le_rpow (hw0 x) hM hq) (by simp) hc

theorem le_one_add_rpow {w q : ℝ} (hw : 0 ≤ w) (hq : 1 ≤ q) : w ≤ 1 + w ^ q := by
  rcases le_or_gt w 1 with h | h
  · have := Real.rpow_nonneg hw q; linarith
  · have := Real.rpow_le_rpow_of_exponent_le h.le hq
    rw [Real.rpow_one] at this; linarith

/-- **Fatou** for nonnegative a.e. limits with bounded integrals. -/
theorem integrable_of_ae_tendsto_of_integral_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hf0 : ∀ k x, 0 ≤ f k x)
    (hfi : ∀ k, Integrable (f k) P) {B : ℝ} (hB : ∀ k, ∫ x, f k x ∂P ≤ B)
    (hlim : ∀ᵐ x ∂P, Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    Integrable g P ∧ ∫ x, g x ∂P ≤ B := by
  have hgm : AEStronglyMeasurable g P :=
    aestronglyMeasurable_of_tendsto_ae _ (fun k => (hfi k).1) hlim
  have hg0 : 0 ≤ᵐ[P] g := hlim.mono fun x hx => ge_of_tendsto' hx fun k => hf0 k x
  have hlin : ∫⁻ x, ENNReal.ofReal (g x) ∂P ≤ ENNReal.ofReal B := by
    have h1 : ∀ᵐ x ∂P, ENNReal.ofReal (g x) =
        liminf (fun k => ENNReal.ofReal (f k x)) atTop := hlim.mono fun x hx =>
      ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq.symm
    rw [lintegral_congr_ae h1]
    refine (lintegral_liminf_le' fun k => (hfi k).1.aemeasurable.ennreal_ofReal).trans ?_
    refine (liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_))
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi k) (Eventually.of_forall (hf0 k))]
    exact ENNReal.ofReal_le_ofReal (hB k)
  have hint : Integrable g P := by
    refine ⟨hgm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hg0]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  have hB0 : 0 ≤ B := (integral_nonneg (hf0 0)).trans (hB 0)
  rw [integral_eq_lintegral_of_nonneg_ae hg0 hgm]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hlin

/-- Elementary truncation: uniform approximation by convergent sequences. -/
theorem tendsto_of_trunc {a : ℕ → ℝ} {a0 : ℝ} {b : ℝ → ℕ → ℝ} {b0 : ℝ → ℝ}
    (hb : ∀ M, Tendsto (b M) atTop (𝓝 (b0 M)))
    (herr : ∀ ε > 0, ∃ M, (∀ n, |a n - b M n| ≤ ε) ∧ |a0 - b0 M| ≤ ε) :
    Tendsto a atTop (𝓝 a0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, h1, h2⟩ := herr (ε / 4) (by positivity)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hb M) (ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h3 := hN n hn
  rw [Real.dist_eq] at h3 ⊢
  have := h1 n
  have t1 := abs_sub_le (a n) (b M n) a0
  have t2 := abs_sub_le (b M n) (b0 M) a0
  have t3 : |b0 M - a0| = |a0 - b0 M| := abs_sub_comm _ _
  linarith

/-- **Vitali** for nonnegative sequences bounded in `L^q`, `q > 1`, converging a.e. -/
theorem tendsto_integral_of_ae_of_rpow_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : ℕ → Ω → ℝ} {g : Ω → ℝ} (hf0 : ∀ k x, 0 ≤ f k x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : ∀ k, Integrable (f k) P) {q : ℝ} (hq : 1 < q)
    (hfq : ∀ k, Integrable (fun x => f k x ^ q) P) {B : ℝ} (hB : ∀ k, ∫ x, f k x ^ q ∂P ≤ B)
    (hlim : ∀ᵐ x ∂P, Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    Integrable g P ∧ Tendsto (fun k => ∫ x, f k x ∂P) atTop (𝓝 (∫ x, g x ∂P)) := by
  have hgm : AEStronglyMeasurable g P :=
    aestronglyMeasurable_of_tendsto_ae _ (fun k => (hfi k).1) hlim
  obtain ⟨hgq, hgqB⟩ := integrable_of_ae_tendsto_of_integral_le
    (f := fun k x => f k x ^ q) (g := fun x => g x ^ q)
    (fun k x => Real.rpow_nonneg (hf0 k x) q) hfq hB
    (hlim.mono fun x hx => hx.rpow_const (Or.inr (by linarith)))
  have hgi : Integrable g P := by
    refine Integrable.mono' ((integrable_const 1).add hgq) hgm (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    exact le_one_add_rpow (hg0 x) hq.le
  refine ⟨hgi, ?_⟩
  set B' := max B 0
  have hbd : ∀ (k : ℕ) (M : ℝ) x, |min (f k x) M| ≤ |M| := fun k M x => by
    rcases le_or_gt 0 M with h | h
    · rw [abs_of_nonneg (le_min (hf0 _ x) h), abs_of_nonneg h]; exact min_le_right _ _
    · rw [min_eq_right (h.le.trans (hf0 _ x))]
  refine tendsto_of_trunc (b := fun M k => ∫ x, min (f k x) M ∂P)
    (b0 := fun M => ∫ x, min (g x) M ∂P) (fun M => ?_) (fun ε hε => ?_)
  · refine tendsto_integral_of_dominated_convergence (fun _ => |M|)
      (fun k => ((hfi k).inf (integrable_const M)).1) (integrable_const _)
      (fun k => Eventually.of_forall fun x => ?_) (hlim.mono fun x hx => hx.min tendsto_const_nhds)
    rw [Real.norm_eq_abs]; exact hbd k M x
  · have h1 : Tendsto (fun M : ℝ => M ^ (1 - q) * B') atTop (𝓝 (0 * B')) := by
      have := tendsto_rpow_neg_atTop (y := q - 1) (by linarith)
      rw [show -(q - 1) = 1 - q by ring] at this
      exact this.mul_const B'
    rw [zero_mul] at h1
    obtain ⟨M, hM1, hM0⟩ := ((h1.eventually (gt_mem_nhds hε)).and (eventually_gt_atTop 0)).exists
    have hB' : ∀ y, y ≤ B → M ^ (1 - q) * y ≤ M ^ (1 - q) * B' := fun y hy =>
      mul_le_mul_of_nonneg_left (hy.trans (le_max_left _ _)) (by positivity)
    have key : ∀ w : Ω → ℝ, (∀ x, 0 ≤ w x) → Integrable w P → Integrable (fun x => w x ^ q) P →
        ∫ x, w x ^ q ∂P ≤ B → |∫ x, w x ∂P - ∫ x, min (w x) M ∂P| ≤ ε := by
      intro w hw0 hwi hwq hwB
      have := abs_integral_sub_min_le (h := fun _ => (1 : ℝ)) hw0 hwi hq.le hwq hM0 (c := 1)
        (fun _ => by simp) aestronglyMeasurable_const
      simp only [one_mul] at this
      exact this.trans ((hB' _ hwB).trans hM1.le)
    exact ⟨M, fun k => key _ (hf0 k) (hfi k) (hfq k) (hB k), key g hg0 hgi hgq hgqB⟩

end SharpLSI
