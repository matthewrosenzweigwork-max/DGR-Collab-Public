import SharpSymmetricLSI.Paper.AppAFisher4
import SharpSymmetricLSI.Infra.HeatTorus8
import SharpSymmetricLSI.Paper.L2Conv

/-!
# Appendix A.1, heat approximation: general tools

* Jensen for the heat flow: `klFun (e^{tΔ}f) ≤ e^{tΔ}(klFun f)`, hence `H(ρ_t|m) ≤ H(ρ|m)`.
* Common a.e. convergent subsequences of `e^{s_n Δ} fᵢ → fᵢ` for finitely many `fᵢ ∈ L¹`.
* The vector form of `tendsto_L2_of_ae` (a.e. convergence plus `‖fₙ‖₂ ≤ ‖g‖₂` for the
  Euclidean norm of a vector field).
* Reduction of limits along `𝓝[>] 0` to subsequences of positive sequences.
-/

open MeasureTheory Set Filter Topology InformationTheory
open scoped ENNReal

namespace SharpLSI

section Heat

variable {ι : Type*} [Fintype ι]

theorem isProbabilityMeasure_heatMeasure {t : ℝ} (ht : 0 < t) :
    IsProbabilityMeasure (heatMeasure (ι := ι) t) := by
  constructor
  rw [heatMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_heatP ht)
      (Eventually.of_forall fun z => (heatP_pos ht z).le), integral_heatP ht, ENNReal.ofReal_one]

theorem heatT_eq_heatMeasure {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf : AEStronglyMeasurable f volume) (x : UnitAddTorus ι) :
    heatT t f x = ∫ z, f (x - z) ∂heatMeasure t := by
  rw [heatT_eq ht hf, integral_heatMeasure ht]
  simp only [smul_eq_mul]

theorem integrable_heatMeasure {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf : Integrable f)
    (x : UnitAddTorus ι) : Integrable (fun z => f (x - z)) (heatMeasure t) := by
  obtain ⟨M, hM⟩ := heatP_bdd (ι := ι) ht
  have hle : heatMeasure (ι := ι) t ≤ ENNReal.ofReal M • volume := by
    rw [heatMeasure, ← withDensity_const]
    exact withDensity_mono (Eventually.of_forall fun z =>
      ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM z)))
  exact ((hf.comp_sub_left x).smul_measure ENNReal.ofReal_ne_top).mono_measure hle

/-- Jensen: `klFun (e^{tΔ}f) ≤ e^{tΔ}(klFun ∘ f)`. -/
theorem klFun_heatT_le {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf0 : ∀ y, 0 ≤ f y)
    (hf : Integrable f) (hK : Integrable fun y => klFun (f y)) (x : UnitAddTorus ι) :
    klFun (heatT t f x) ≤ heatT t (fun y => klFun (f y)) x := by
  have := isProbabilityMeasure_heatMeasure (ι := ι) ht
  rw [heatT_eq_heatMeasure ht hf.aestronglyMeasurable,
    heatT_eq_heatMeasure ht hK.aestronglyMeasurable]
  exact convexOn_klFun.map_integral_le continuous_klFun.continuousOn isClosed_Ici
    (Eventually.of_forall fun z => hf0 _) (integrable_heatMeasure ht hf x)
    (integrable_heatMeasure ht hK x)

theorem heatT_nonneg {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf0 : ∀ y, 0 ≤ f y)
    (hf : AEStronglyMeasurable f volume) (x : UnitAddTorus ι) : 0 ≤ heatT t f x := by
  rw [heatT_eq ht hf]
  exact integral_nonneg fun z => mul_nonneg (heatP_pos ht z).le (hf0 _)

/-- The entropy decreases along the heat flow. -/
theorem lintegral_klFun_heatT_le {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    (hf0 : ∀ y, 0 ≤ f y) (hf : Integrable f) :
    ∫⁻ x, ENNReal.ofReal (klFun (heatT t f x)) ≤ ∫⁻ x, ENNReal.ofReal (klFun (f x)) := by
  by_cases hfin : ∫⁻ x, ENNReal.ofReal (klFun (f x)) = ⊤
  · rw [hfin]; exact le_top
  have hK : Integrable fun y => klFun (f y) := by
    refine ⟨continuous_klFun.comp_aestronglyMeasurable hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => klFun_nonneg (hf0 y))]
    exact lt_top_iff_ne_top.2 hfin
  have hHK := integrable_heatT ht hK
  calc ∫⁻ x, ENNReal.ofReal (klFun (heatT t f x))
      ≤ ∫⁻ x, ENNReal.ofReal (heatT t (fun y => klFun (f y)) x) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (klFun_heatT_le ht hf0 hf hK x)
    _ = ENNReal.ofReal (∫ x, heatT t (fun y => klFun (f y)) x) :=
        (ofReal_integral_eq_lintegral_ofReal hHK (Eventually.of_forall fun x =>
          heatT_nonneg ht (fun y => klFun_nonneg (hf0 y)) hK.aestronglyMeasurable x)).symm
    _ = ENNReal.ofReal (∫ x, klFun (f x)) := by rw [integral_heatT ht hK]
    _ = ∫⁻ x, ENNReal.ofReal (klFun (f x)) :=
        ofReal_integral_eq_lintegral_ofReal hK (Eventually.of_forall fun y => klFun_nonneg (hf0 y))

/-- A common a.e. convergent subsequence of `e^{s_n Δ} fᵢ → fᵢ` for finitely many `fᵢ`. -/
theorem exists_subseq_heatT_ae {κ : Type*} [Fintype κ] {f : κ → UnitAddTorus ι → ℝ}
    (hf : ∀ i, Integrable (f i)) {s : ℕ → ℝ} (hs0 : ∀ n, 0 < s n)
    (hs : Tendsto s atTop (𝓝[>] 0)) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ x ∂(volume : Measure (UnitAddTorus ι)), ∀ i,
      Tendsto (fun n => heatT (s (ms n)) (f i) x) atTop (𝓝 (f i x)) := by
  set F : ℕ → UnitAddTorus ι → ℝ := fun n x => ∑ i, |heatT (s n) (f i) x - f i x| with hF
  have hFm : ∀ n, AEStronglyMeasurable (F n) volume := fun n =>
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      ((continuous_heatT (hs0 n) (hf i)).aestronglyMeasurable.sub (hf i).aestronglyMeasurable).norm
  have hb : ∀ n, ∫⁻ x, ‖F n x - (fun _ => (0 : ℝ)) x‖ₑ ≤
      ∑ i, ∫⁻ x, ‖heatT (s n) (f i) x - f i x‖ₑ := fun n => by
    rw [← lintegral_finsetSum' (f := fun i x => ‖heatT (s n) (f i) x - f i x‖ₑ) _ fun i _ =>
      ((continuous_heatT (hs0 n) (hf i)).aestronglyMeasurable.sub
        (hf i).aestronglyMeasurable).enorm]
    refine lintegral_mono fun x => ?_
    simp only [sub_zero, hF]
    refine (enorm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_abs]
  have hz : Tendsto (fun n => ∑ i, ∫⁻ x, ‖heatT (s n) (f i) x - f i x‖ₑ) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset κ) fun i _ =>
      (tendsto_heatT_L1 (hf i)).comp hs
    simpa using this
  have hlim := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    (fun _ => zero_le) hb
  obtain ⟨ms, hms, hae⟩ := exists_subseq_ae_of_tendsto_lintegral hFm
    (aestronglyMeasurable_const (b := (0 : ℝ))) hlim
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae] with x hx i
  have hle : ∀ n, |heatT (s (ms n)) (f i) x - f i x| ≤ F (ms n) x := fun n =>
    Finset.single_le_sum (f := fun i => |heatT (s (ms n)) (f i) x - f i x|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hle n) hx

end Heat

/-- Limits along `𝓝[>] 0` from subsequences of positive sequences. -/
theorem tendsto_nhdsGT_of_subseq {X : Type*} [TopologicalSpace X] {f : ℝ → X} {L : X}
    (h : ∀ s : ℕ → ℝ, (∀ n, 0 < s n) → Tendsto s atTop (𝓝[>] 0) →
      ∃ ms : ℕ → ℕ, StrictMono ms ∧ Tendsto (fun n => f (s (ms n))) atTop (𝓝 L)) :
    Tendsto f (𝓝[>] 0) (𝓝 L) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hns.eventually self_mem_nhdsWithin)
  have hsh : Tendsto (fun n : ℕ => n + N) atTop atTop := tendsto_add_atTop_nat N
  obtain ⟨ms, -, hms⟩ := h (fun n => ns (n + N)) (fun n => hN _ (by omega)) (hns.comp hsh)
  exact ⟨fun n => ms n + N, hms⟩

section Vec

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ] {μ : Measure α}

theorem sum_enorm_sub_sq_le (a b : κ → ℝ) :
    ∑ k, ‖a k - b k‖ₑ ^ 2 ≤ 2 * ∑ k, ‖a k‖ₑ ^ 2 + 2 * ∑ k, ‖b k‖ₑ ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => enorm_sub_sq_le _ _

/-- `tendsto_L2_of_ae` for vector fields. -/
theorem tendsto_L2_of_ae_vec {f : ℕ → α → κ → ℝ} {g : α → κ → ℝ}
    (hfm : ∀ n k, AEMeasurable (fun x => f n x k) μ) (hgm : ∀ k, AEMeasurable (fun x => g x k) μ)
    (hae : ∀ᵐ x ∂μ, ∀ k, Tendsto (fun n => f n x k) atTop (𝓝 (g x k)))
    (hle : ∀ n, ∫⁻ x, ∑ k, ‖f n x k‖ₑ ^ 2 ∂μ ≤ ∫⁻ x, ∑ k, ‖g x k‖ₑ ^ 2 ∂μ)
    (hfin : ∫⁻ x, ∑ k, ‖g x k‖ₑ ^ 2 ∂μ ≠ ⊤) :
    Tendsto (fun n => ∫⁻ x, ∑ k, ‖f n x k - g x k‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  set G := ∫⁻ x, ∑ k, ‖g x k‖ₑ ^ 2 ∂μ with hG
  set a : ℕ → ℝ≥0∞ := fun n => ∫⁻ x, ∑ k, ‖f n x k - g x k‖ₑ ^ 2 ∂μ with ha
  have hgm2 : AEMeasurable (fun x => ∑ k, ‖g x k‖ₑ ^ 2) μ :=
    Finset.aemeasurable_fun_sum _ fun k _ => (hgm k).enorm.pow_const 2
  have hfm2 : ∀ n, AEMeasurable (fun x => ∑ k, ‖f n x k‖ₑ ^ 2) μ := fun n =>
    Finset.aemeasurable_fun_sum _ fun k _ => (hfm n k).enorm.pow_const 2
  have hdm : ∀ n, AEMeasurable (fun x => ∑ k, ‖f n x k - g x k‖ₑ ^ 2) μ := fun n =>
    Finset.aemeasurable_fun_sum _ fun k _ => ((hfm n k).sub (hgm k)).enorm.pow_const 2
  have hsum : ∀ n, ∫⁻ x, (2 * ∑ k, ‖f n x k‖ₑ ^ 2 + 2 * ∑ k, ‖g x k‖ₑ ^ 2) ∂μ ≤ 4 * G :=
    fun n => by
    rw [lintegral_add_left' ((hfm2 n).const_mul 2), lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
    calc 2 * ∫⁻ x, ∑ k, ‖f n x k‖ₑ ^ 2 ∂μ + 2 * G ≤ 2 * G + 2 * G := by gcongr; exact hle n
      _ = 4 * G := by ring
  have ha_le : ∀ n, a n ≤ 4 * G := fun n =>
    (lintegral_mono fun x => sum_enorm_sub_sq_le _ _).trans (hsum n)
  have h4G : 4 * G ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hfin
  set h : ℕ → α → ℝ≥0∞ := fun n x =>
    (2 * ∑ k, ‖f n x k‖ₑ ^ 2 + 2 * ∑ k, ‖g x k‖ₑ ^ 2) - ∑ k, ‖f n x k - g x k‖ₑ ^ 2 with hh
  have hhm : ∀ n, AEMeasurable (h n) μ := fun n =>
    (((hfm2 n).const_mul 2).add (hgm2.const_mul 2)).sub (hdm n)
  have hlim : ∀ᵐ x ∂μ, liminf (fun n => h n x) atTop = 4 * ∑ k, ‖g x k‖ₑ ^ 2 := by
    filter_upwards [hae] with x hx
    have h1 : Tendsto (fun n => ∑ k, ‖f n x k‖ₑ ^ 2) atTop (𝓝 (∑ k, ‖g x k‖ₑ ^ 2)) :=
      tendsto_finsetSum _ fun k _ =>
        (ENNReal.continuous_pow 2).continuousAt.tendsto.comp (continuous_enorm.tendsto _ |>.comp (hx k))
    have h2 : Tendsto (fun n => ∑ k, ‖f n x k - g x k‖ₑ ^ 2) atTop (𝓝 0) := by
      have : ∀ k, Tendsto (fun n => ‖f n x k - g x k‖ₑ ^ 2) atTop (𝓝 0) := fun k => by
        have : Tendsto (fun n => f n x k - g x k) atTop (𝓝 0) := by
          simpa using (hx k).sub_const (g x k)
        have := (ENNReal.continuous_pow 2).continuousAt.tendsto.comp
          ((continuous_enorm.tendsto _).comp this)
        simp only [enorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
        exact this
      simpa using tendsto_finsetSum (Finset.univ : Finset κ) fun k _ => this k
    have h3 : Tendsto (fun n => 2 * ∑ k, ‖f n x k‖ₑ ^ 2 + 2 * ∑ k, ‖g x k‖ₑ ^ 2) atTop
        (𝓝 (2 * ∑ k, ‖g x k‖ₑ ^ 2 + 2 * ∑ k, ‖g x k‖ₑ ^ 2)) :=
      (ENNReal.Tendsto.const_mul h1 (Or.inr (by norm_num))).add_const _
    have h4 := ENNReal.Tendsto.sub h3 h2 (Or.inr ENNReal.zero_ne_top)
    rw [tsub_zero] at h4
    rw [h4.liminf_eq]; ring
  have hF := lintegral_liminf_le' hhm (μ := μ) (u := atTop)
  rw [lintegral_congr_ae hlim, lintegral_const_mul' _ _ (by norm_num)] at hF
  have hint : ∀ n, ∫⁻ x, h n x ∂μ ≤ 4 * G - a n := fun n => by
    simp only [hh]
    rw [lintegral_sub' (hdm n) ((ha_le n).trans_lt h4G.lt_top).ne
      (Eventually.of_forall fun x => sum_enorm_sub_sq_le _ _)]
    exact tsub_le_tsub_right (hsum n) _
  have hF2 : 4 * G ≤ 4 * G - limsup a atTop := by
    calc 4 * G ≤ liminf (fun n => ∫⁻ x, h n x ∂μ) atTop := hF
      _ ≤ liminf (fun n => 4 * G - a n) atTop := liminf_le_liminf (Eventually.of_forall hint)
      _ = 4 * G - limsup a atTop := ENNReal.liminf_const_sub _ _ h4G
  have hL : limsup a atTop = 0 := by
    by_contra hne
    rcases eq_or_ne G 0 with hG0 | hG0
    · have : limsup a atTop ≤ 0 := by
        refine limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n => ?_)
        have := ha_le n; rw [hG0, mul_zero] at this; exact this
      exact hne (le_antisymm this zero_le)
    · have hpos : 0 < 4 * G := by positivity
      have := ENNReal.sub_lt_self h4G hpos.ne' hne
      exact absurd hF2 (not_le.mpr this)
  exact tendsto_of_le_liminf_of_limsup_le zero_le hL.le

/-- `L²` plus a.e. convergence give convergence of `∫ fₙ²`. -/
theorem L2Tendsto.tendsto_lintegral_sq {f : ℕ → α → ℝ} {g : α → ℝ} (h : L2Tendsto μ f g)
    (hfm : ∀ n, AEMeasurable (f n) μ) (hgm : AEMeasurable g μ)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hg : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ≠ ⊤) :
    Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ 2 ∂μ) atTop (𝓝 (∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ)) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ (h.limsup_le hgm hg)
  refine le_trans (le_of_eq ?_) (lintegral_liminf_le' fun n => (hfm n).enorm.pow_const 2)
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  exact ((ENNReal.continuous_pow 2).continuousAt.tendsto.comp
    (continuous_enorm.tendsto _ |>.comp hx)).liminf_eq.symm

end Vec

end SharpLSI
