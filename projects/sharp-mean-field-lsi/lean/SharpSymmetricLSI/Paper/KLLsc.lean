import Mathlib

/-!
# Weak lower semicontinuity of the relative entropy (D5 sanity lemma, infrastructure)

Donsker–Varadhan: for probability measures `ρ, ν`,
* (Gibbs) `∫ g dρ - log ∫ eᵍ dν ≤ H(ρ|ν)` for bounded measurable `g`;
* (approximation) every real `c < H(ρ|ν)` is exceeded by `∫ g dρ - log ∫ eᵍ dν` for some bounded
  continuous `g` (truncate `log dρ/dν`, then approximate in `L¹(ρ + ν)`).
Hence `ρ ↦ H(ρ|ν)` is lower semicontinuous for the weak topology on probability measures.
This file imports only Mathlib.
-/

noncomputable section
open MeasureTheory InformationTheory Filter Topology Real
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

section dv
variable {α : Type*} [MeasurableSpace α] {ρ ν : Measure α} [IsProbabilityMeasure ρ]
  [IsProbabilityMeasure ν]

/-- The Donsker–Varadhan functional. -/
def dvFun (ρ ν : Measure α) (g : α → ℝ) : ℝ := ∫ x, g x ∂ρ - Real.log (∫ x, Real.exp (g x) ∂ν)

theorem integrable_of_bdd' {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

/-- **Gibbs' inequality.** -/
theorem dvFun_le_klDiv {g : α → ℝ} (hgm : Measurable g) {B : ℝ} (hgB : ∀ x, |g x| ≤ B) :
    ((dvFun ρ ν g : ℝ) : EReal) ≤ ((klDiv ρ ν : ℝ≥0∞) : EReal) := by
  by_cases hK : klDiv ρ ν = ⊤
  · rw [hK]; exact le_top
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hK
  have hgρ : Integrable g ρ := integrable_of_bdd' hgm hgB
  have hgν : Integrable (fun x => exp (g x)) ν := integrable_of_bdd' (measurable_exp.comp hgm)
    (C := exp B) fun x => by
      rw [abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr ((le_abs_self _).trans (hgB x))
  haveI : IsProbabilityMeasure (ν.tilted g) := isProbabilityMeasure_tilted hgν
  have hac' : ρ ≪ ν.tilted g := hac.trans (absolutelyContinuous_tilted hgν)
  have hK' := klDiv_ne_top hac' (integrable_llr_tilted_right hac hgρ hint hgν)
  have e : (klDiv ρ (ν.tilted g)).toReal =
      (klDiv ρ ν).toReal - ∫ x, g x ∂ρ + Real.log (∫ x, exp (g x) ∂ν) := by
    rw [toReal_klDiv_of_measure_eq hac' (by simp), toReal_klDiv_of_measure_eq hac (by simp),
      integral_llr_tilted_right hac hgρ hgν hint]
  have h0 : 0 ≤ (klDiv ρ (ν.tilted g)).toReal := ENNReal.toReal_nonneg
  rw [← ENNReal.ofReal_toReal hK, EReal.coe_ennreal_ofReal, max_eq_left ENNReal.toReal_nonneg]
  exact EReal.coe_le_coe_iff.mpr (by unfold dvFun; linarith)

theorem klFun_monotoneOn : MonotoneOn klFun (Set.Ici 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 1) continuous_klFun.continuousOn
    (fun x hx => ?_) (fun x hx => ?_)
  · have hx' : x ≠ 0 := by
      have : (1 : ℝ) < x := by simpa using hx
      linarith
    exact (hasDerivAt_klFun hx').differentiableAt.differentiableWithinAt
  · rw [deriv_klFun]
    have : (1 : ℝ) < x := by simpa using hx
    exact Real.log_nonneg this.le

/-- **Approximation by bounded measurable functions.** -/
theorem exists_bdd_dvFun_gt {c : ℝ} (hc : (c : EReal) < ((klDiv ρ ν : ℝ≥0∞) : EReal)) :
    ∃ (g : α → ℝ) (B : ℝ), Measurable g ∧ (∀ x, |g x| ≤ B) ∧ c < dvFun ρ ν g := by
  by_cases hc0 : c < 0
  · refine ⟨fun _ => 0, 0, measurable_const, fun _ => by simp, ?_⟩
    simp [dvFun, hc0]
  push_neg at hc0
  by_cases hac : ρ ≪ ν
  · set p : α → ℝ := fun x => (ρ.rnDeriv ν x).toReal
    have hpm : Measurable p := (Measure.measurable_rnDeriv ρ ν).ennreal_toReal
    have hp0 : ∀ x, 0 ≤ p x := fun _ => ENNReal.toReal_nonneg
    have hpi : Integrable p ν := Measure.integrable_toReal_rnDeriv
    have hp1 : ∫ x, p x ∂ν = 1 := by
      rw [Measure.integral_toReal_rnDeriv hac]; simp
    -- monotone truncation of the entropy density
    set F : ℕ → α → ℝ≥0∞ := fun M x => ENNReal.ofReal (klFun (min (p x) ((M : ℝ) + 1)))
    have hFm : ∀ M, Measurable (F M) := fun M =>
      ENNReal.measurable_ofReal.comp (measurable_klFun.comp (hpm.min measurable_const))
    have hmono : ∀ x, Monotone fun M => F M x := by
      intro x M M' hMM'
      refine ENNReal.ofReal_le_ofReal ?_
      have hM : ((M : ℝ) + 1) ≤ (M' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hMM' 1
      by_cases hpx : p x ≤ (M : ℝ) + 1
      · rw [min_eq_left hpx, min_eq_left (hpx.trans hM)]
      · push_neg at hpx
        rw [min_eq_right hpx.le]
        refine klFun_monotoneOn (by simp only [Set.mem_Ici]; linarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)]) ?_ (le_min hpx.le hM)
        simp only [Set.mem_Ici, le_min_iff]
        constructor <;> [linarith; (have : (0 : ℝ) ≤ M' := Nat.cast_nonneg _; linarith)]
    have hlim : ∀ x, Tendsto (fun M => F M x) atTop (𝓝 (ENNReal.ofReal (klFun (p x)))) := by
      intro x
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge (p x)
      filter_upwards [eventually_ge_atTop N] with M hM
      have : p x ≤ (M : ℝ) + 1 := by
        have : (N : ℝ) ≤ M := by exact_mod_cast hM
        linarith
      simp only [F, min_eq_left this]
    have hT := lintegral_tendsto_of_tendsto_of_monotone (μ := ν) (fun M => (hFm M).aemeasurable)
      (Eventually.of_forall hmono) (Eventually.of_forall hlim)
    rw [← klDiv_eq_lintegral_klFun_of_ac hac] at hT
    have hcK : ENNReal.ofReal c < klDiv ρ ν := by
      rw [← EReal.coe_ennreal_lt_coe_ennreal_iff, EReal.coe_ennreal_ofReal, max_eq_left hc0]
      exact hc
    obtain ⟨M, hM⟩ := (hT.eventually (lt_mem_nhds hcK)).exists
    -- the truncated density `q`
    set q : α → ℝ := fun x => min (p x) ((M : ℝ) + 1)
    have hqm : Measurable q := hpm.min measurable_const
    have hq0 : ∀ x, 0 ≤ q x := fun x => le_min (hp0 x) (by positivity)
    have hqM : ∀ x, q x ≤ (M : ℝ) + 1 := fun x => min_le_right _ _
    have hkb : ∀ x, |klFun (q x)| ≤ ((M : ℝ) + 1) ^ 2 + 1 := fun x => by
      rw [abs_of_nonneg (klFun_nonneg (hq0 x)), klFun_apply]
      have h1 : q x * Real.log (q x) ≤ q x * (q x - 1) := by
        rcases eq_or_lt_of_le (hq0 x) with h | h
        · rw [← h]; simp
        · exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) (hq0 x)
      nlinarith [hq0 x, hqM x]
    have hki : Integrable (fun x => klFun (q x)) ν :=
      integrable_of_bdd' (measurable_klFun.comp hqm) hkb
    set I := ∫ x, klFun (q x) ∂ν
    have hcI : c < I := by
      have := hM
      simp only [F] at this
      rw [← ofReal_integral_eq_lintegral_ofReal hki (Eventually.of_forall fun x =>
        klFun_nonneg (hq0 x))] at this
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc0).mp this
    set ε : ℝ := min (1 / 2) ((I - c) / 2)
    have hε : 0 < ε := lt_min (by norm_num) (by linarith)
    have hε1 : ε ≤ 1 / 2 := min_le_left _ _
    have hεI : ε ≤ (I - c) / 2 := min_le_right _ _
    set g : α → ℝ := fun x => Real.log (q x + ε)
    have hgm : Measurable g := Real.measurable_log.comp (hqm.add_const _)
    have hqε : ∀ x, 0 < q x + ε := fun x => by linarith [hq0 x]
    set B : ℝ := |Real.log ε| + |Real.log ((M : ℝ) + 2)|
    have hgB : ∀ x, |g x| ≤ B := fun x => by
      have h1 : Real.log ε ≤ g x := Real.log_le_log hε (by linarith [hq0 x])
      have h2 : g x ≤ Real.log ((M : ℝ) + 2) :=
        Real.log_le_log (hqε x) (by linarith [hqM x])
      rw [abs_le]
      constructor
      · linarith [neg_abs_le (Real.log ε), abs_nonneg (Real.log ((M : ℝ) + 2))]
      · linarith [le_abs_self (Real.log ((M : ℝ) + 2)), abs_nonneg (Real.log ε)]
    refine ⟨g, B, hgm, hgB, ?_⟩
    -- the lower bound
    have hpg : Integrable (fun x => p x * g x) ν := by
      refine (hpi.const_mul B).mono' (hpm.mul hgm).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 x), mul_comm B]
      exact mul_le_mul_of_nonneg_left (hgB x) (hp0 x)
    have hqlog : Integrable (fun x => q x * Real.log (q x)) ν := by
      refine integrable_of_bdd' (hqm.mul (Real.measurable_log.comp hqm))
        (C := ((M : ℝ) + 1) ^ 2 + 1 + ((M : ℝ) + 1) + 1) fun x => ?_
      have := hkb x
      rw [klFun_apply] at this
      have hq := hqM x
      rw [abs_le] at this ⊢
      constructor <;> nlinarith [hq0 x]
    have hqi : Integrable q ν := integrable_of_bdd' hqm (C := (M : ℝ) + 1) fun x => by
      rw [abs_of_nonneg (hq0 x)]; exact hqM x
    have hpt : ∀ x, q x * Real.log (q x) ≤ p x * g x := fun x => by
      simp only [g, q]
      by_cases hpx : p x ≤ (M : ℝ) + 1
      · rw [min_eq_left hpx]
        rcases eq_or_lt_of_le (hp0 x) with h | h
        · rw [← h]; simp
        · exact mul_le_mul_of_nonneg_left (Real.log_le_log h (by linarith)) (hp0 x)
      · push_neg at hpx
        rw [min_eq_right hpx.le]
        have hl0 : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by
          have : (0 : ℝ) ≤ M := Nat.cast_nonneg _; linarith)
        have hl1 : Real.log ((M : ℝ) + 1) ≤ Real.log ((M : ℝ) + 1 + ε) :=
          Real.log_le_log (by positivity) (by linarith)
        calc ((M : ℝ) + 1) * Real.log ((M : ℝ) + 1)
            ≤ ((M : ℝ) + 1) * Real.log ((M : ℝ) + 1 + ε) :=
              mul_le_mul_of_nonneg_left hl1 (by positivity)
          _ ≤ p x * Real.log ((M : ℝ) + 1 + ε) :=
              mul_le_mul_of_nonneg_right hpx.le (hl0.trans hl1)
    have h1 : ∫ x, g x ∂ρ = ∫ x, p x * g x ∂ν := (integral_toReal_rnDeriv_mul hac).symm
    have h2 : ∫ x, Real.exp (g x) ∂ν = ∫ x, q x ∂ν + ε := by
      have : ∀ x, Real.exp (g x) = q x + ε := fun x => Real.exp_log (hqε x)
      simp_rw [this]
      rw [integral_add hqi (integrable_const _)]
      simp
    have h3 : Real.log (∫ x, q x ∂ν + ε) ≤ ∫ x, q x ∂ν + ε - 1 :=
      Real.log_le_sub_one_of_pos (by linarith [integral_nonneg (μ := ν) (f := q) (fun x => hq0 x)])
    have h4 : ∫ x, q x * Real.log (q x) ∂ν ≤ ∫ x, p x * g x ∂ν := integral_mono hqlog hpg hpt
    have h5 : I = ∫ x, q x * Real.log (q x) ∂ν + 1 - ∫ x, q x ∂ν := by
      simp only [I, klFun_apply]
      rw [integral_sub (f := fun x => q x * Real.log (q x) + 1) (g := q)
        (hqlog.add (integrable_const _)) hqi,
        integral_add (f := fun x => q x * Real.log (q x)) (g := fun _ => (1 : ℝ)) hqlog
          (integrable_const _)]
      simp
    unfold dvFun
    rw [h1, h2]
    linarith
  · -- `ρ` is not absolutely continuous: put a large weight on a `ν`-null set
    rw [Measure.AbsolutelyContinuous] at hac
    push_neg at hac
    obtain ⟨s, hνs, hρs⟩ := hac
    set t := toMeasurable ν s
    have htm : MeasurableSet t := measurableSet_toMeasurable ν s
    have hνt : ν t = 0 := by rw [measure_toMeasurable]; exact hνs
    have hρt : 0 < (ρ t).toReal := ENNReal.toReal_pos
      (fun h => hρs (measure_mono_null (subset_toMeasurable ν s) h)) (measure_ne_top _ _)
    set K : ℝ := (c + 1) / (ρ t).toReal
    have hK0 : 0 ≤ K := div_nonneg (by linarith) hρt.le
    refine ⟨t.indicator fun _ => K, K, measurable_const.indicator htm, fun x => ?_, ?_⟩
    · by_cases hx : x ∈ t <;> simp [hx, abs_of_nonneg hK0, hK0]
    · have he : (fun x => Real.exp (t.indicator (fun _ => K) x)) =ᵐ[ν] fun _ => 1 := by
        have : ∀ᵐ x ∂ν, x ∉ t := measure_eq_zero_iff_ae_notMem.mp hνt
        filter_upwards [this] with x hx
        simp [hx]
      unfold dvFun
      rw [integral_congr_ae he, integral_indicator htm]
      simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ, probReal_univ,
        mul_one, Real.log_one, sub_zero]
      rw [Measure.real_def]
      rw [show (ρ t).toReal * K = c + 1 by simp only [K]; field_simp]
      linarith

end dv

theorem abs_exp_sub_exp_le' {a b B : ℝ} (ha : a ≤ B) (hb : b ≤ B) :
    |Real.exp a - Real.exp b| ≤ Real.exp B * |a - b| := by
  wlog hab : b ≤ a generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a]; exact this hb ha (le_of_not_ge hab)
  rw [abs_of_nonneg (by linarith [Real.exp_le_exp.mpr hab]), abs_of_nonneg (by linarith)]
  have h1 : 1 - Real.exp (-(a - b)) ≤ a - b := by linarith [Real.add_one_le_exp (-(a - b))]
  have h2 : Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (-(a - b))) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  rw [h2]
  have h3 : 0 ≤ 1 - Real.exp (-(a - b)) := by
    rw [sub_nonneg]; exact Real.exp_le_one_iff.mpr (by linarith)
  calc Real.exp a * (1 - Real.exp (-(a - b))) ≤ Real.exp B * (1 - Real.exp (-(a - b))) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha) h3
    _ ≤ Real.exp B * (a - b) := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

section bcf
variable {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
  {ρ ν : Measure α} [IsProbabilityMeasure ρ] [IsProbabilityMeasure ν]

/-- **Approximation by bounded continuous functions.** -/
theorem exists_bcf_dvFun_gt {c : ℝ} (hc : (c : EReal) < ((klDiv ρ ν : ℝ≥0∞) : EReal)) :
    ∃ g : α →ᵇ ℝ, c < dvFun ρ ν g := by
  obtain ⟨f, B, hfm, hfB, hcf⟩ := exists_bdd_dvFun_gt hc
  haveI : Nonempty α := nonempty_of_isProbabilityMeasure ρ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hfB (Classical.arbitrary α))
  set μ := ρ + ν
  have hfL : MemLp f 1 μ := MemLp.of_bound hfm.aestronglyMeasurable B
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hfB x)
  have hex : ∀ n : ℕ, ∃ h : α →ᵇ ℝ, eLpNorm (f - (h : α → ℝ)) 1 μ ≤ ENNReal.ofReal (1 / (n + 1)) :=
    fun n => by
      obtain ⟨h, hh, -⟩ := hfL.exists_boundedContinuous_eLpNorm_sub_le ENNReal.one_ne_top
        (ε := ENNReal.ofReal (1 / (n + 1))) (by simp; positivity)
      exact ⟨h, hh⟩
  choose h hh using hex
  set cl : ℝ → ℝ := fun t => max (-B) (min B t)
  have hcl : LipschitzWith 1 cl := (LipschitzWith.id.const_min B).const_max (-B)
  set k : ℕ → α →ᵇ ℝ := fun n => BoundedContinuousFunction.comp cl hcl (h n)
  have hfcl : ∀ x, cl (f x) = f x := fun x => by
    have := abs_le.mp (hfB x)
    simp only [cl]; rw [min_eq_right this.2, max_eq_right this.1]
  have hkB : ∀ n x, |k n x| ≤ B := fun n x => by
    simp only [k, BoundedContinuousFunction.comp_apply, cl]
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hpt : ∀ n x, |f x - k n x| ≤ |f x - h n x| := fun n x => by
    have := hcl.dist_le_mul (f x) (h n x)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, hfcl x] at this
    exact this
  have hfi : ∀ (m : Measure α) [IsFiniteMeasure m], Integrable f m := fun m _ =>
    integrable_of_bdd' hfm hfB
  have hdi : ∀ n (m : Measure α) [IsFiniteMeasure m], Integrable (fun x => |f x - h n x|) m :=
    fun n m _ => ((hfi m).sub ((h n).integrable m)).abs
  have hdk : ∀ n (m : Measure α) [IsFiniteMeasure m], Integrable (fun x => |f x - k n x|) m :=
    fun n m _ => ((hfi m).sub ((k n).integrable m)).abs
  have hE : ∀ n, ∫ x, |f x - h n x| ∂μ ≤ 1 / (n + 1) := fun n => by
    have e1 : ∫ x, |f x - h n x| ∂μ = (eLpNorm (f - (h n : α → ℝ)) 1 μ).toReal := by
      have hm : AEStronglyMeasurable (f - (h n : α → ℝ)) μ :=
        ((hfi μ).sub ((h n).integrable μ)).aestronglyMeasurable
      rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hm]
      all_goals first | rfl | exact hm
    rw [e1]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (hh n)
  have hEρ : ∀ n, ∫ x, |f x - k n x| ∂ρ ≤ 1 / (n + 1) := fun n => by
    refine le_trans ?_ ((integral_mono (hdk n μ) (hdi n μ) (hpt n)).trans (hE n))
    rw [integral_add_measure (hdk n ρ) (hdk n ν)]
    linarith [integral_nonneg (μ := ν) (f := fun x => |f x - k n x|) fun x => abs_nonneg _]
  have hEν : ∀ n, ∫ x, |f x - k n x| ∂ν ≤ 1 / (n + 1) := fun n => by
    refine le_trans ?_ ((integral_mono (hdk n μ) (hdi n μ) (hpt n)).trans (hE n))
    rw [integral_add_measure (hdk n ρ) (hdk n ν)]
    linarith [integral_nonneg (μ := ρ) (f := fun x => |f x - k n x|) fun x => abs_nonneg _]
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have T1 : Tendsto (fun n => ∫ x, k n x ∂ρ) atTop (𝓝 (∫ x, f x ∂ρ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
    rw [Real.norm_eq_abs, ← integral_sub ((k n).integrable ρ) (hfi ρ)]
    refine (abs_integral_le_integral_abs).trans ((le_of_eq ?_).trans (hEρ n))
    congr 1; funext x; rw [abs_sub_comm]
  have hei : ∀ (g : α → ℝ), Measurable g → (∀ x, |g x| ≤ B) → Integrable (fun x => Real.exp (g x)) ν :=
    fun g hg hgB => integrable_of_bdd' (Real.measurable_exp.comp hg) (C := Real.exp B) fun x => by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hgB x))
  have T2 : Tendsto (fun n => ∫ x, Real.exp (k n x) ∂ν) atTop (𝓝 (∫ x, Real.exp (f x) ∂ν)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h0.const_mul (Real.exp B))
    rw [Real.norm_eq_abs, ← integral_sub (hei _ (k n).continuous.measurable (hkB n)) (hei f hfm hfB)]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |Real.exp (k n x) - Real.exp (f x)| ∂ν ≤ ∫ x, Real.exp B * |f x - k n x| ∂ν := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            ((hdk n ν).const_mul _) (Eventually.of_forall fun x => ?_)
          show |Real.exp (k n x) - Real.exp (f x)| ≤ Real.exp B * |f x - k n x|
          rw [abs_sub_comm (f x)]
          exact abs_exp_sub_exp_le' (abs_le.mp (hkB n x)).2 (abs_le.mp (hfB x)).2
      _ ≤ Real.exp B * (1 / (n + 1)) := by
          rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (hEν n) (Real.exp_pos _).le
      _ = _ := by rw [one_div]
  have hpos : 0 < ∫ x, Real.exp (f x) ∂ν := integral_exp_pos (hei f hfm hfB)
  have T3 := (Real.continuousAt_log hpos.ne').tendsto.comp T2
  have T := T1.sub T3
  obtain ⟨n, hn⟩ := (T.eventually (lt_mem_nhds hcf)).exists
  exact ⟨k n, hn⟩

/-- **`ρ ↦ H(ρ|ν)` is weakly lower semicontinuous.** -/
theorem lowerSemicontinuous_klDiv (ν : Measure α) [IsProbabilityMeasure ν] :
    LowerSemicontinuous fun ρ : ProbabilityMeasure α => ((klDiv (ρ : Measure α) ν : ℝ≥0∞) : EReal) := by
  intro ρ y hy
  induction y using EReal.rec with
  | bot => exact Eventually.of_forall fun ρ' => bot_lt_iff_ne_bot.mpr (EReal.coe_ennreal_ne_bot _)
  | top => exact absurd hy not_top_lt
  | coe c =>
    obtain ⟨g, hg⟩ := exists_bcf_dvFun_gt hy
    have hcont : Continuous fun ρ' : ProbabilityMeasure α => dvFun (ρ' : Measure α) ν g :=
      (ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).sub continuous_const
    filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hg)] with ρ' h
    exact (EReal.coe_lt_coe_iff.mpr h).trans_le
      (dvFun_le_klDiv g.continuous.measurable fun x => by
        rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm x)

end bcf

end SharpLSI
