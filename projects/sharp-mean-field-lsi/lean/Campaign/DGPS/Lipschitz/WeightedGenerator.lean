import DGPS.Analysis.CompactResolvent
import DGPS.Analysis.WeightedForms
import DGPS.Analysis.PeriodicEllipticH2
import DGPS.Lipschitz.Representatives
open MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace DGPS.Lipschitz.WeightedGenerator

section Abstract
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- The constant function one as an element of `L²(μ)`. -/
noncomputable def oneLp (μ : Measure α) [IsFiniteMeasure μ] : Lp ℝ 2 μ :=
  (memLp_const (1 : ℝ)).toLp _

lemma coeFn_oneLp : (oneLp μ : α → ℝ) =ᵐ[μ] fun _ => 1 :=
  MemLp.coeFn_toLp _

/-- A symmetric operator on `L²(μ)` that maps functions with values in `[0,1]` to functions with
values in `[0,1]` and fixes the constant one. -/
structure MarkovSym (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Prop where
  symm : ∀ f g, ⟪T f, g⟫ = ⟪f, T g⟫
  unit : ∀ f : Lp ℝ 2 μ, (0 ≤ᵐ[μ] f) → (f ≤ᵐ[μ] fun _ => (1 : ℝ)) →
    (0 ≤ᵐ[μ] T f) ∧ (T f ≤ᵐ[μ] fun _ => (1 : ℝ))
  one : T (oneLp μ) = oneLp μ

variable {T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ}

lemma integrable_Lp2 (f : Lp ℝ 2 μ) : Integrable f μ :=
  (Lp.memLp f).integrable (by norm_num)

lemma MarkovSym.pos (hT : MarkovSym T) (f : Lp ℝ 2 μ) (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] T f := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (integrable_Lp2 _)
  intro s hs _
  have hμs : μ s ≠ ∞ := measure_ne_top _ _
  set g : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs (1 : ℝ) with hg
  have hg0 : 0 ≤ᵐ[μ] g := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1:ℝ))] with x hx
    rw [hx]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
  have hg1 : g ≤ᵐ[μ] fun _ => (1 : ℝ) := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1:ℝ))] with x hx
    rw [hx]; exact Set.indicator_le_self' (fun _ _ => zero_le_one) x
  obtain ⟨h0, -⟩ := hT.unit g hg0 hg1
  have h1 : ⟪g, T f⟫ = ∫ x in s, (T f) x ∂μ := L2.inner_indicatorConstLp_one hs hμs (T f)
  have h2 : ⟪T f, g⟫ = ⟪f, T g⟫ := hT.symm f g
  have h3 : 0 ≤ ⟪f, T g⟫ := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hf, h0] with x hx hy
    simpa [mul_comm] using mul_nonneg hx hy
  rw [← h1, real_inner_comm, h2]; exact h3


lemma MarkovSym.mono (hT : MarkovSym T) {f g : Lp ℝ 2 μ} (h : f ≤ᵐ[μ] g) :
    T f ≤ᵐ[μ] T g := by
  have h0 : 0 ≤ᵐ[μ] g - f := by
    filter_upwards [h, Lp.coeFn_sub g f] with x hx hy
    rw [hy]; simp only [Pi.sub_apply, Pi.zero_apply]; linarith
  have h1 := hT.pos _ h0
  filter_upwards [h1, Lp.coeFn_sub (T g) (T f)] with x hx hy
  have e : T (g - f) = T g - T f := map_sub T g f
  rw [e, hy] at hx
  simp only [Pi.sub_apply, Pi.zero_apply] at hx
  linarith

lemma tangent_rpow {p : ℝ} (hp : 1 < p) {s q : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q) :
    q ^ p + p * q ^ (p - 1) * (s - q) ≤ s ^ p := by
  rcases hq.eq_or_lt with rfl | hq
  · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
    simp only [zero_add, mul_zero, zero_mul]; exact Real.rpow_nonneg hs _
  · have h1 := one_add_mul_self_le_rpow_one_add (s := s / q - 1) (p := p)
      (by have : 0 ≤ s / q := div_nonneg hs hq.le; linarith) hp.le
    have h2 : (1 + (s / q - 1)) = s / q := by ring
    rw [h2, Real.div_rpow hs hq.le] at h1
    have h3 : q ^ p ≤ 0 ∨ 0 < q ^ p := le_or_gt _ _
    have hqp : 0 < q ^ p := Real.rpow_pos_of_pos hq p
    have h4 : q ^ p * (1 + p * (s / q - 1)) ≤ q ^ p * (s ^ p / q ^ p) :=
      mul_le_mul_of_nonneg_left h1 hqp.le
    rw [mul_div_cancel₀ _ hqp.ne'] at h4
    have h5 : q ^ (p - 1) = q ^ p / q := by
      rw [Real.rpow_sub hq, Real.rpow_one]
    have h6 : q ^ p * (1 + p * (s / q - 1)) = q ^ p + p * q ^ (p - 1) * (s - q) := by
      rw [h5]; field_simp
    linarith


lemma sup_tangent {p : ℝ} (hp : 1 < p) {s Y : ℝ} (hs : 0 ≤ s)
    (h : ∀ r : ℚ, 0 ≤ (r : ℝ) → (r : ℝ) ^ p + p * (r : ℝ) ^ (p - 1) * (s - r) ≤ Y) :
    s ^ p ≤ Y := by
  have hc : Continuous fun q : ℝ => q ^ p + p * q ^ (p - 1) * (s - q) := by
    have h1 : Continuous fun q : ℝ => q ^ p := Real.continuous_rpow_const (by linarith)
    have h2 : Continuous fun q : ℝ => q ^ (p - 1) := Real.continuous_rpow_const (by linarith)
    fun_prop
  have hS : IsClosed {q : ℝ | q ^ p + p * q ^ (p - 1) * (s - q) ≤ Y} :=
    isClosed_le hc continuous_const
  have hsub : {q : ℝ | ∃ r : ℚ, 0 ≤ (r : ℝ) ∧ (r : ℝ) = q} ⊆
      {q : ℝ | q ^ p + p * q ^ (p - 1) * (s - q) ≤ Y} := by
    rintro q ⟨r, hr, rfl⟩; exact h r hr
  have hcl : s ∈ closure {q : ℝ | ∃ r : ℚ, 0 ≤ (r : ℝ) ∧ (r : ℝ) = q} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show s < s + ε by linarith)
    refine ⟨(r : ℝ), ⟨r, by linarith, rfl⟩, ?_⟩
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by linarith)]
    linarith
  have := closure_minimal hsub hS hcl
  simpa using this

lemma MarkovSym.jensen (hT : MarkovSym T) {p : ℝ} (hp : 1 < p) (g gp : Lp ℝ 2 μ)
    (hg0 : 0 ≤ᵐ[μ] g) (hgp : (gp : α → ℝ) =ᵐ[μ] fun x => (g x) ^ p) :
    (fun x => ((T g : α → ℝ) x) ^ p) ≤ᵐ[μ] T gp := by
  have hTg0 := hT.pos g hg0
  have hq : ∀ r : ℚ, ∀ᵐ x ∂μ, 0 ≤ (r : ℝ) →
      p * (r : ℝ) ^ (p - 1) * (T g : α → ℝ) x + ((r : ℝ) ^ p - p * (r : ℝ) ^ (p - 1) * r)
        ≤ (T gp : α → ℝ) x := by
    intro r
    by_cases hr : 0 ≤ (r : ℝ)
    · set a : ℝ := p * (r : ℝ) ^ (p - 1)
      set c0 : ℝ := (r : ℝ) ^ p - a * r
      set k : Lp ℝ 2 μ := gp - a • g - c0 • oneLp μ with hk
      have hk0 : 0 ≤ᵐ[μ] k := by
        filter_upwards [Lp.coeFn_sub (gp - a • g) (c0 • oneLp μ), Lp.coeFn_sub gp (a • g),
          Lp.coeFn_smul a g, Lp.coeFn_smul c0 (oneLp μ), coeFn_oneLp (μ := μ), hgp, hg0]
          with x h1 h2 h3 h4 h5 h6 h7
        simp only [Pi.zero_apply] at h7
        have h8 := tangent_rpow hp h7 hr
        rw [hk]
        simp only [h1, h2, h3, h4, h5, h6, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one,
          Pi.zero_apply]
        have : c0 = (r : ℝ) ^ p - a * r := rfl
        nlinarith [h8]
      have hTk := hT.pos _ hk0
      have e : T k = T gp - a • T g - c0 • oneLp μ := by
        rw [hk, map_sub, map_sub, map_smul, map_smul, hT.one]
      filter_upwards [hTk, Lp.coeFn_sub (T gp - a • T g) (c0 • oneLp μ),
        Lp.coeFn_sub (T gp) (a • T g), Lp.coeFn_smul a (T g), Lp.coeFn_smul c0 (oneLp μ),
        coeFn_oneLp (μ := μ)] with x h1 h2 h3 h4 h5 h6
      intro _
      rw [e] at h1
      simp only [h2, h3, h4, h5, h6, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one,
        Pi.zero_apply] at h1
      linarith
    · exact Filter.Eventually.of_forall fun x h => absurd h hr
  have hall : ∀ᵐ x ∂μ, ∀ r : ℚ, 0 ≤ (r : ℝ) →
      p * (r : ℝ) ^ (p - 1) * (T g : α → ℝ) x + ((r : ℝ) ^ p - p * (r : ℝ) ^ (p - 1) * r)
        ≤ (T gp : α → ℝ) x := ae_all_iff.2 hq
  filter_upwards [hall, hTg0] with x h1 h2
  simp only [Pi.zero_apply] at h2
  apply sup_tangent hp h2
  intro r hr
  have := h1 r hr
  linarith


lemma inner_oneLp (f : Lp ℝ 2 μ) : ⟪f, oneLp μ⟫ = ∫ x, (f : α → ℝ) x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_oneLp (μ := μ)] with x hx
  simp [hx]

lemma coeFn_smul_oneLp (M : ℝ) : ((M • oneLp μ : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ] fun _ => M := by
  filter_upwards [Lp.coeFn_smul M (oneLp μ), coeFn_oneLp (μ := μ)] with x h1 h2
  rw [h1]; simp [h2]

lemma MarkovSym.norm_le_const (hT : MarkovSym T) {f : Lp ℝ 2 μ} {M : ℝ}
    (h : ∀ᵐ x ∂μ, ‖(f : α → ℝ) x‖ ≤ M) : ∀ᵐ x ∂μ, ‖(T f : α → ℝ) x‖ ≤ M := by
  have h1 : f ≤ᵐ[μ] (M • oneLp μ : Lp ℝ 2 μ) := by
    filter_upwards [h, coeFn_smul_oneLp (μ := μ) M] with x hx hy
    rw [hy]; exact (abs_le.1 (by simpa using hx)).2
  have h2 : (-(M • oneLp μ) : Lp ℝ 2 μ) ≤ᵐ[μ] f := by
    filter_upwards [h, coeFn_smul_oneLp (μ := μ) M, Lp.coeFn_neg (M • oneLp μ)] with x hx hy hz
    rw [hz]; simp only [Pi.neg_apply, hy]; exact (abs_le.1 (by simpa using hx)).1
  have e : T (M • oneLp μ) = M • oneLp μ := by rw [map_smul, hT.one]
  have m1 := hT.mono h1
  have m2 := hT.mono h2
  filter_upwards [m1, m2, coeFn_smul_oneLp (μ := μ) M, Lp.coeFn_neg (M • oneLp μ)] with x a b c d
  rw [e] at a
  rw [map_neg, e] at b
  rw [Real.norm_eq_abs, abs_le]
  simp only [Pi.neg_apply, c] at a b d
  exact ⟨by linarith, a⟩

lemma MarkovSym.integral_rpow_le (hT : MarkovSym T) {p : ℝ} (hp : 1 < p) (g : Lp ℝ 2 μ)
    (hg0 : 0 ≤ᵐ[μ] g) {M : ℝ} (hgM : ∀ᵐ x ∂μ, ‖(g : α → ℝ) x‖ ≤ M) :
    ∫ x, ((T g : α → ℝ) x) ^ p ∂μ ≤ ∫ x, ((g : α → ℝ) x) ^ p ∂μ := by
  have hgm : Measurable (g : α → ℝ) := (Lp.stronglyMeasurable g).measurable
  have hbd : ∀ᵐ x ∂μ, ‖(g x) ^ p‖ ≤ M ^ p := by
    filter_upwards [hg0, hgM] with x h0 h1
    simp only [Pi.zero_apply] at h0
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)]
    rw [Real.norm_eq_abs, abs_of_nonneg h0] at h1
    exact Real.rpow_le_rpow h0 h1 (by linarith)
  have hmp : MemLp (fun x => (g x) ^ p) 2 μ :=
    MemLp.of_bound (hgm.pow_const p).aestronglyMeasurable _ hbd
  set gp : Lp ℝ 2 μ := hmp.toLp _ with hgp_def
  have hgp : (gp : α → ℝ) =ᵐ[μ] fun x => (g x) ^ p := MemLp.coeFn_toLp hmp
  have hJ := hT.jensen hp g gp hg0 hgp
  have hTg0 := hT.pos g hg0
  have hTgM := hT.norm_le_const hgM
  have hTm : Measurable (T g : α → ℝ) := (Lp.stronglyMeasurable (T g)).measurable
  have hint1 : Integrable (fun x => ((T g : α → ℝ) x) ^ p) μ := by
    refine Integrable.of_bound (hTm.pow_const p).aestronglyMeasurable (M ^ p) ?_
    filter_upwards [hTg0, hTgM] with x h0 h1
    simp only [Pi.zero_apply] at h0
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)]
    rw [Real.norm_eq_abs, abs_of_nonneg h0] at h1
    exact Real.rpow_le_rpow h0 h1 (by linarith)
  calc ∫ x, ((T g : α → ℝ) x) ^ p ∂μ ≤ ∫ x, (T gp : α → ℝ) x ∂μ :=
        integral_mono_ae hint1 (integrable_Lp2 _) hJ
    _ = ⟪T gp, oneLp μ⟫ := (inner_oneLp _).symm
    _ = ⟪gp, T (oneLp μ)⟫ := hT.symm _ _
    _ = ∫ x, (gp : α → ℝ) x ∂μ := by rw [hT.one, inner_oneLp]
    _ = ∫ x, ((g : α → ℝ) x) ^ p ∂μ := integral_congr_ae hgp


omit [IsFiniteMeasure μ] in
lemma lintegral_enorm_rpow_eq {u : α → ℝ} {q : ℝ} (hq : 0 ≤ q) (hu0 : 0 ≤ᵐ[μ] u)
    (hi : Integrable (fun x => (u x) ^ q) μ) :
    ∫⁻ x, ‖u x‖ₑ ^ q ∂μ = ENNReal.ofReal (∫ x, (u x) ^ q ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (by filter_upwards [hu0] with x hx; exact Real.rpow_nonneg hx _)]
  apply lintegral_congr_ae
  filter_upwards [hu0] with x hx
  simp only [Pi.zero_apply] at hx
  rw [Real.enorm_eq_ofReal hx, ENNReal.ofReal_rpow_of_nonneg hx hq]

lemma integrable_rpow_of_bound {u : α → ℝ} (hu : Measurable u) (q : ℝ) (hq : 0 ≤ q) {M : ℝ}
    (h0 : 0 ≤ᵐ[μ] u) (hM : ∀ᵐ x ∂μ, ‖u x‖ ≤ M) : Integrable (fun x => (u x) ^ q) μ := by
  refine Integrable.of_bound (hu.pow_const q).aestronglyMeasurable (M ^ q) ?_
  filter_upwards [h0, hM] with x h0 h1
  simp only [Pi.zero_apply] at h0
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h0 _)]
  rw [Real.norm_eq_abs, abs_of_nonneg h0] at h1
  exact Real.rpow_le_rpow h0 h1 hq

lemma MarkovSym.eLpNorm_le_of_bdd (hT : MarkovSym T) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (g : Lp ℝ 2 μ) (hg0 : 0 ≤ᵐ[μ] g) {M : ℝ} (hgM : ∀ᵐ x ∂μ, ‖(g : α → ℝ) x‖ ≤ M) :
    eLpNorm (T g) p μ ≤ eLpNorm g p μ := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; simp at hp
  have hq1 : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp; simpa using this
  set q := p.toReal with hq
  have hTg0 := hT.pos g hg0
  have hTgM := hT.norm_le_const hgM
  have hgm : Measurable (g : α → ℝ) := (Lp.stronglyMeasurable g).measurable
  have hTm : Measurable (T g : α → ℝ) := (Lp.stronglyMeasurable (T g)).measurable
  have hi1 := integrable_rpow_of_bound hTm q (by linarith) hTg0 hTgM
  have hi2 := integrable_rpow_of_bound hgm q (by linarith) hg0 hgM
  have hint : ∫ x, ((T g : α → ℝ) x) ^ q ∂μ ≤ ∫ x, ((g : α → ℝ) x) ^ q ∂μ := by
    rcases hq1.eq_or_lt with h | h
    · rw [← h]
      simp only [Real.rpow_one]
      rw [← inner_oneLp, ← inner_oneLp, hT.symm, hT.one]
    · exact hT.integral_rpow_le h g hg0 hgM
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (Lp.aestronglyMeasurable _),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (Lp.aestronglyMeasurable _)]
  rw [lintegral_enorm_rpow_eq (by linarith) hTg0 hi1, lintegral_enorm_rpow_eq (by linarith) hg0 hi2]
  gcongr


lemma memLp_clip (g : Lp ℝ 2 μ) (n : ℕ) :
    MemLp (fun x => max (-(n : ℝ)) (min ((g : α → ℝ) x) (n : ℝ))) 2 μ := by
  refine MemLp.of_bound
    (measurable_const.max ((Lp.stronglyMeasurable g).measurable.min
      measurable_const)).aestronglyMeasurable (n : ℝ) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

/-- Truncation of an `L²` function at height `n`. -/
noncomputable def clipLp (g : Lp ℝ 2 μ) (n : ℕ) : Lp ℝ 2 μ := (memLp_clip g n).toLp _

lemma coeFn_clipLp (g : Lp ℝ 2 μ) (n : ℕ) :
    (clipLp g n : α → ℝ) =ᵐ[μ] fun x => max (-(n : ℝ)) (min ((g : α → ℝ) x) (n : ℝ)) :=
  MemLp.coeFn_toLp _

lemma clipLp_bound (g : Lp ℝ 2 μ) (n : ℕ) : ∀ᵐ x ∂μ, ‖(clipLp g n : α → ℝ) x‖ ≤ n := by
  filter_upwards [coeFn_clipLp g n] with x hx
  rw [hx, Real.norm_eq_abs, abs_le]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

lemma clipLp_nonneg (g : Lp ℝ 2 μ) (hg : 0 ≤ᵐ[μ] g) (n : ℕ) : 0 ≤ᵐ[μ] clipLp g n := by
  filter_upwards [coeFn_clipLp g n, hg] with x hx h0
  simp only [Pi.zero_apply] at h0 ⊢
  rw [hx]
  exact le_max_of_le_right (le_min h0 (Nat.cast_nonneg n))

lemma clipLp_le (g : Lp ℝ 2 μ) (hg : 0 ≤ᵐ[μ] g) (n : ℕ) :
    ∀ᵐ x ∂μ, ‖(clipLp g n : α → ℝ) x‖ ≤ ‖(g : α → ℝ) x‖ := by
  filter_upwards [coeFn_clipLp g n, hg] with x hx h0
  simp only [Pi.zero_apply] at h0
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
    abs_of_nonneg (le_max_of_le_right (le_min h0 (Nat.cast_nonneg n)))]
  exact max_le (by linarith) (min_le_left _ _)

lemma tendsto_clipLp (g : Lp ℝ 2 μ) (hg : 0 ≤ᵐ[μ] g) :
    Tendsto (fun n => clipLp g n) atTop (𝓝 g) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ n : ℕ, ‖clipLp g n - g‖ ^ 2 = ∫ x, ((clipLp g n : α → ℝ) x - (g : α → ℝ) x) ^ 2 ∂μ := by
    intro n
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (clipLp g n) g] with x hx
    rw [hx]; simp [sq]
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x => ((clipLp g n : α → ℝ) x - (g : α → ℝ) x) ^ 2) μ := fun n =>
    (((Lp.aestronglyMeasurable (clipLp g n)).sub (Lp.aestronglyMeasurable g)).pow 2)
  have hlim : Tendsto (fun n : ℕ => ∫ x, ((clipLp g n : α → ℝ) x - (g : α → ℝ) x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, ∀ᵐ x ∂μ, ‖((clipLp g n : α → ℝ) x - (g : α → ℝ) x) ^ 2‖ ≤
        ((g : α → ℝ) x) ^ 2 := by
      intro n
      filter_upwards [coeFn_clipLp g n, hg] with x hx h0
      simp only [Pi.zero_apply] at h0
      have h1 : 0 ≤ max (-(n : ℝ)) (min ((g : α → ℝ) x) (n : ℝ)) :=
        le_max_of_le_right (le_min h0 (Nat.cast_nonneg n))
      have h2 : max (-(n : ℝ)) (min ((g : α → ℝ) x) (n : ℝ)) ≤ (g : α → ℝ) x :=
        max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_left _ _)
      rw [hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith
    have hl : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ =>
        ((clipLp g n : α → ℝ) x - (g : α → ℝ) x) ^ 2) atTop (𝓝 0) := by
      have hae : ∀ᵐ x ∂μ, ∀ n : ℕ, (clipLp g n : α → ℝ) x =
          max (-(n : ℝ)) (min ((g : α → ℝ) x) (n : ℝ)) := ae_all_iff.2 (coeFn_clipLp g)
      filter_upwards [hae, hg] with x hx h0
      simp only [Pi.zero_apply] at h0
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ⌈(g : α → ℝ) x⌉₊] with n hn
      have hn' : (g : α → ℝ) x ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
      rw [hx n, min_eq_left hn', max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) n])]
      simp
    have := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun (n : ℕ) x => ((clipLp g n : α → ℝ) x - (g : α → ℝ) x) ^ 2)
      (f := fun _ => (0 : ℝ)) (fun x => ((g : α → ℝ) x) ^ 2) hmeas
      (Lp.memLp g).integrable_sq hb hl
    simpa using this
  have hsq' : Tendsto (fun n : ℕ => ‖clipLp g n - g‖ ^ 2) atTop (𝓝 0) := by
    simpa [hsq] using hlim
  have := (Real.continuous_sqrt.tendsto 0).comp hsq'
  rw [Real.sqrt_zero] at this
  exact this.congr fun n => Real.sqrt_sq (norm_nonneg _)


lemma MarkovSym.eLpNorm_le_nonneg (hT : MarkovSym T) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (g : Lp ℝ 2 μ) (hg0 : 0 ≤ᵐ[μ] g) : eLpNorm (T g) p μ ≤ eLpNorm g p μ := by
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp; simp at hp
  have hconv : Tendsto (fun n => T (clipLp g n)) atTop (𝓝 (T g)) :=
    (T.continuous.tendsto g).comp (tendsto_clipLp g hg0)
  have hconv2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (p := 2) _ _).1 hconv
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) (f := fun n =>
    ((T (clipLp g n) : Lp ℝ 2 μ) : α → ℝ)) (g := (T g : α → ℝ)) (l := atTop) hconv2
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun k => ((T (clipLp g (ns k)) : Lp ℝ 2 μ) : α → ℝ))
    (Filter.Eventually.of_forall fun k => ?_) (fun k => Lp.aestronglyMeasurable _)
    (Lp.aestronglyMeasurable _) hae
  calc eLpNorm (T (clipLp g (ns k))) p μ ≤ eLpNorm (clipLp g (ns k)) p μ :=
        hT.eLpNorm_le_of_bdd hp hpt _ (clipLp_nonneg g hg0 _) (clipLp_bound g _)
    _ ≤ eLpNorm g p μ := eLpNorm_mono_ae (Lp.aestronglyMeasurable _) (clipLp_le g hg0 _)


lemma MarkovSym.eLpNorm_le (hT : MarkovSym T) {p : ℝ≥0∞} (hp : 1 ≤ p) (f : Lp ℝ 2 μ) :
    eLpNorm (T f) p μ ≤ eLpNorm f p μ := by
  by_cases hpt : p = ∞
  · subst hpt
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _),
      eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
    by_cases htop : eLpNormEssSup (f : α → ℝ) μ = ∞
    · rw [htop]; exact le_top
    · have hb : ∀ᵐ x ∂μ, ‖(f : α → ℝ) x‖ ≤ (eLpNormEssSup (f : α → ℝ) μ).toReal := by
        filter_upwards [enorm_ae_le_eLpNormEssSup (f : α → ℝ) μ] with x hx
        rw [← ofReal_norm] at hx
        exact (ENNReal.ofReal_le_iff_le_toReal htop).1 hx
      have := hT.norm_le_const hb
      calc eLpNormEssSup (T f : α → ℝ) μ ≤ ENNReal.ofReal (eLpNormEssSup (f : α → ℝ) μ).toReal :=
            eLpNormEssSup_le_of_ae_bound this
        _ = _ := ENNReal.ofReal_toReal htop
  · set g : Lp ℝ 2 μ := (Lp.memLp f).norm.toLp _ with hg
    have hgc : (g : α → ℝ) =ᵐ[μ] fun x => ‖(f : α → ℝ) x‖ := MemLp.coeFn_toLp _
    have hg0 : 0 ≤ᵐ[μ] g := by
      filter_upwards [hgc] with x hx; rw [hx]; exact norm_nonneg _
    have h1 : f ≤ᵐ[μ] g := by
      filter_upwards [hgc] with x hx; rw [hx]; exact Real.le_norm_self _
    have h2 : (-g : Lp ℝ 2 μ) ≤ᵐ[μ] f := by
      filter_upwards [hgc, Lp.coeFn_neg g] with x hx hy
      rw [hy]; simp only [Pi.neg_apply, hx]; exact neg_le_of_abs_le (by simp)
    have m1 := hT.mono h1
    have m2 := hT.mono h2
    have hTg0 := hT.pos g hg0
    have hle : ∀ᵐ x ∂μ, ‖(T f : α → ℝ) x‖ ≤ ‖(T g : α → ℝ) x‖ := by
      filter_upwards [m1, m2, hTg0, Lp.coeFn_neg (T g)] with x a b c d
      rw [map_neg] at b
      simp only [Pi.zero_apply] at c
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg c, abs_le]
      rw [d] at b
      simp only [Pi.neg_apply] at b
      exact ⟨b, a⟩
    calc eLpNorm (T f) p μ ≤ eLpNorm (T g) p μ := eLpNorm_mono_ae (Lp.aestronglyMeasurable _) hle
      _ ≤ eLpNorm g p μ := hT.eLpNorm_le_nonneg hp hpt g hg0
      _ = eLpNorm f p μ := by
        rw [eLpNorm_congr_ae hgc, eLpNorm_norm _ (Lp.aestronglyMeasurable _)]

end Abstract

section Weight

open DGPS DGPS.Lipschitz DGPS.Analysis
open scoped InnerProductSpace

variable {d : ℕ}

theorem abs_exp_sub_exp_le {a b M : ℝ} (ha : a ≤ M) (hb : b ≤ M) :
    |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
  have key : ∀ a b : ℝ, a ≤ b → b ≤ M → |Real.exp a - Real.exp b| ≤ Real.exp M * |a - b| := by
    intro a b hab hbM
    have h1 : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    have h2 : 1 - (b - a) ≤ Real.exp (a - b) := by
      have := Real.add_one_le_exp (a - b); linarith
    have h3 : Real.exp b * Real.exp (a - b) = Real.exp a := by
      rw [← Real.exp_add]; congr 1; ring
    have h4 : Real.exp b ≤ Real.exp M := Real.exp_le_exp.mpr hbM
    have h5 : 0 ≤ b - a := by linarith
    nlinarith [Real.exp_pos b, mul_le_mul_of_nonneg_right h4 h5]
  rcases le_total a b with h | h
  · exact key a b h hb
  · rw [abs_sub_comm, abs_sub_comm a b]; exact key b a h ha

theorem torusLipschitz_exp {Φ : Torus d → ℝ} {L M : ℝ} (hΦ : TorusLipschitzWith L Φ)
    (hM : ∀ x, |Φ x| ≤ M) (κ σ : ℝ) :
    TorusLipschitzWith (|κ| * (Real.exp (|σ| * M) * (|σ| * L)))
      (fun x => κ * Real.exp (σ * Φ x)) := by
  intro x y
  have hx : σ * Φ x ≤ |σ| * M := by
    calc σ * Φ x ≤ |σ * Φ x| := le_abs_self _
      _ = |σ| * |Φ x| := abs_mul _ _
      _ ≤ |σ| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
  have hy : σ * Φ y ≤ |σ| * M := by
    calc σ * Φ y ≤ |σ * Φ y| := le_abs_self _
      _ = |σ| * |Φ y| := abs_mul _ _
      _ ≤ |σ| * M := mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _)
  have h1 := abs_exp_sub_exp_le hx hy
  have h2 := hΦ x y
  have h3 : |σ * Φ x - σ * Φ y| = |σ| * |Φ x - Φ y| := by rw [← mul_sub, abs_mul]
  rw [← mul_sub, abs_mul]
  rw [h3] at h1
  calc |κ| * |Real.exp (σ * Φ x) - Real.exp (σ * Φ y)|
      ≤ |κ| * (Real.exp (|σ| * M) * (|σ| * |Φ x - Φ y|)) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ ≤ |κ| * (Real.exp (|σ| * M) * (|σ| * (L * torusDist x y))) := by
        gcongr
    _ = _ := by ring

theorem coordPartial_exp_comp {Φ : Torus d → ℝ} (κ σ : ℝ) (j : Fin d) (x : Torus d)
    (hx : DifferentiableAt ℝ (Φ ∘ torusLift) (SharpLSI.secT x)) :
    coordPartial j (fun y => κ * Real.exp (σ * Φ y)) x =
      (κ * σ * Real.exp (σ * Φ x)) * coordPartial j Φ x := by
  have hF := ((hx.hasFDerivAt.const_mul σ).exp).const_mul κ
  have e : ((fun y => κ * Real.exp (σ * Φ y)) ∘ torusLift) =
      fun z => κ * Real.exp (σ * (Φ ∘ torusLift) z) := rfl
  unfold coordPartial
  rw [e, hF.fderiv]
  simp only [smul_apply, smul_eq_mul, Function.comp_apply,
    SharpLSI.liftT_secT]
  ring


theorem isWeakGradientLp_congr_grad {p : ℝ≥0∞} {u : Torus d → ℝ} {g g' : Torus d → Tangent d}
    (h : IsWeakGradientLp p u g) (hg : g =ᵐ[haar d] g') : IsWeakGradientLp p u g' where
  memLp := h.memLp
  memLp_grad := h.memLp_grad.ae_eq hg
  ibp φ hφ j := by
    rw [h.ibp φ hφ j]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hg] with x hx
    rw [hx]

theorem isWeakGradientLp_exp {Φ : Torus d → ℝ} {L M : ℝ} (hL : 0 ≤ L)
    (hΦ : TorusLipschitzWith L Φ) (hM : ∀ x, |Φ x| ≤ M) (κ σ : ℝ) :
    IsWeakGradientLp ∞ (fun x => κ * Real.exp (σ * Φ x))
      (fun x => (κ * σ * Real.exp (σ * Φ x)) • smoothGrad Φ x) := by
  have hL' : 0 ≤ |κ| * (Real.exp (|σ| * M) * (|σ| * L)) := by positivity
  obtain ⟨h, -⟩ := exists_weak_gradient hL' (torusLipschitz_exp hΦ hM κ σ)
  refine isWeakGradientLp_congr_grad h ?_
  filter_upwards [ae_differentiableAt_secT hL hΦ] with x hx
  ext j
  simp only [smoothGrad_apply, PiLp.smul_apply, smul_eq_mul]
  exact coordPartial_exp_comp κ σ j x hx


/-- The Gibbs density `w = e^{-Φ} / ∫ e^{-Φ}` with respect to Haar measure. -/
noncomputable def gibbsW (Φ : Torus d → ℝ) (x : Torus d) : ℝ :=
  Real.exp (-Φ x) / ∫ y, Real.exp (-Φ y) ∂haar d

/-- Analytic data of a weight `w` with logarithmic gradient `b`: two-sided bounds, `w` and `1/w`
in `W^{1,∞}` with gradients `w b` and `-(1/w) b`, and `b` essentially bounded. -/
structure WData (d : ℕ) (w : Torus d → ℝ) (b : Torus d → Tangent d) (c C : ℝ) : Prop where
  meas : Measurable w
  pos : 0 < c
  bound : ∀ x, c ≤ w x ∧ w x ≤ C
  grad_w : IsWeakGradientLp ∞ w (fun x => w x • b x)
  grad_inv : IsWeakGradientLp ∞ (fun x => (w x)⁻¹) (fun x => -((w x)⁻¹ • b x))
  b_bdd : MemLp b ∞ (haar d)

theorem normConst_bounds {Φ : Torus d → ℝ} {M : ℝ} (hc : Continuous Φ) (hM : ∀ x, |Φ x| ≤ M) :
    Real.exp (-M) ≤ ∫ y, Real.exp (-Φ y) ∂haar d ∧ ∫ y, Real.exp (-Φ y) ∂haar d ≤ Real.exp M := by
  have hi : Integrable (fun y => Real.exp (-Φ y)) (haar d) :=
    (Real.continuous_exp.comp hc.neg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlo : ∀ y, Real.exp (-M) ≤ Real.exp (-Φ y) := fun y =>
    Real.exp_le_exp.mpr (by have := (abs_le.mp (hM y)).2; linarith)
  have hhi : ∀ y, Real.exp (-Φ y) ≤ Real.exp M := fun y =>
    Real.exp_le_exp.mpr (by have := (abs_le.mp (hM y)).1; linarith)
  constructor
  · calc Real.exp (-M) = ∫ _y, Real.exp (-M) ∂haar d := by simp
      _ ≤ _ := integral_mono (integrable_const _) hi hlo
  · calc _ ≤ ∫ _y, Real.exp M ∂haar d := integral_mono hi (integrable_const _) hhi
      _ = _ := by simp

theorem gibbs_eq {Φ : Torus d → ℝ} :
    gibbsW Φ = fun x => (∫ y, Real.exp (-Φ y) ∂haar d)⁻¹ * Real.exp ((-1) * Φ x) := by
  funext x
  unfold gibbsW
  rw [div_eq_inv_mul]
  simp

theorem log_gibbsW {Φ : Torus d → ℝ} {M : ℝ} (hc : Continuous Φ) (hM : ∀ x, |Φ x| ≤ M) (x : Torus d) :
    Real.log (gibbsW Φ x) = -Φ x - Real.log (∫ y, Real.exp (-Φ y) ∂haar d) := by
  obtain ⟨h1, -⟩ := normConst_bounds hc hM
  have hZ : 0 < ∫ y, Real.exp (-Φ y) ∂haar d := lt_of_lt_of_le (Real.exp_pos _) h1
  unfold gibbsW
  rw [Real.log_div (Real.exp_pos _).ne' hZ.ne', Real.log_exp]

theorem gibbs_wdata {Φ : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hΦ : TorusLipschitzWith L Φ) :
    ∃ c C : ℝ, WData d (gibbsW Φ) (fun x => -smoothGrad Φ x) c C := by
  have hc := torusLipschitz_continuous hΦ
  obtain ⟨M, hM⟩ := exists_bound_continuous hc
  obtain ⟨h1, h2⟩ := normConst_bounds hc hM
  set Z := ∫ y, Real.exp (-Φ y) ∂haar d with hZdef
  have hZ : 0 < Z := lt_of_lt_of_le (Real.exp_pos _) h1
  have hlo : ∀ x, Real.exp (-M) ≤ Real.exp (-Φ x) := fun x =>
    Real.exp_le_exp.mpr (by have := (abs_le.mp (hM x)).2; linarith)
  have hhi : ∀ x, Real.exp (-Φ x) ≤ Real.exp M := fun x =>
    Real.exp_le_exp.mpr (by have := (abs_le.mp (hM x)).1; linarith)
  have hwpos : ∀ x, 0 < gibbsW Φ x := fun x => div_pos (Real.exp_pos _) hZ
  refine ⟨Real.exp (-M) / Real.exp M, Real.exp M / Real.exp (-M), ?_⟩
  have hgw := isWeakGradientLp_exp hL hΦ hM Z⁻¹ (-1)
  have hgi := isWeakGradientLp_exp hL hΦ hM Z 1
  have hge : gibbsW Φ = fun x => Z⁻¹ * Real.exp ((-1) * Φ x) := gibbs_eq
  refine ⟨?_, by positivity, fun x => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hge]
    exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))).measurable
  · unfold gibbsW
    calc Real.exp (-M) / Real.exp M ≤ Real.exp (-Φ x) / Real.exp M :=
          div_le_div_of_nonneg_right (hlo x) (Real.exp_pos _).le
      _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le hZ h2
  · unfold gibbsW
    calc Real.exp (-Φ x) / Z ≤ Real.exp M / Z := div_le_div_of_nonneg_right (hhi x) hZ.le
      _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le (Real.exp_pos _) h1
  · rw [hge]
    refine isWeakGradientLp_congr_grad hgw ?_
    refine Eventually.of_forall fun x => ?_
    ext j
    simp only [PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, smoothGrad_apply]
    ring
  · have hinv : ∀ x, (gibbsW Φ x)⁻¹ = Z * Real.exp (1 * Φ x) := by
      intro x
      unfold gibbsW
      rw [inv_div, one_mul, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    have he : (fun x => (gibbsW Φ x)⁻¹) = fun x => Z * Real.exp (1 * Φ x) := funext hinv
    rw [he]
    refine isWeakGradientLp_congr_grad hgi ?_
    refine Eventually.of_forall fun x => ?_
    ext j
    simp only [PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul, smoothGrad_apply, hinv x]
    ring
  · obtain ⟨-, hb⟩ := exists_weak_gradient hL hΦ
    exact memLp_top_of_bound measurable_smoothGrad.neg.aestronglyMeasurable L
      (hb.mono fun x hx => by simpa using hx)

end Weight

section IBP

open DGPS DGPS.Lipschitz DGPS.Analysis
open scoped InnerProductSpace

variable {d : ℕ}

theorem tendsto_integral_mul_L2 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {F : ℕ → α → ℝ} {F0 : α → ℝ} (hf : MemLp f 2 μ) (hF : ∀ k, MemLp (F k) 2 μ)
    (hF0 : MemLp F0 2 μ) (h : Tendsto (fun k => eLpNorm (fun x => F k x - F0 x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, f x * F k x ∂μ) atTop (𝓝 (∫ x, f x * F0 x ∂μ)) := by
  have : Fact ((1:ENNReal) ≤ 2) := ⟨one_le_two⟩
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF F0 hF0).2 h
  have h2 := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hf.toLp f)) h1
  have e : ∀ g : α → ℝ, ∀ hg : MemLp g 2 μ, ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ x, f x * g x ∂μ := by
    intro g hg
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]; simp [mul_comm]
  simp_rw [e] at h2
  exact h2

/-- Integration by parts between two `H¹` functions. -/
theorem ibp_H1 {u y : Torus d → ℝ} {g Y : Torus d → Tangent d} (hu : IsWeakGradient u g)
    (hy : IsWeakGradient y Y) (j : Fin d) :
    ∫ x, u x * Y x j ∂haar d = -∫ x, g x j * y x ∂haar d := by
  obtain ⟨v, hvs, hvw, hv0, hv1⟩ := exists_smooth_tendsto_H1 hy
  have hvm : ∀ k, MemLp (v k) 2 (haar d) := fun k => (hvw k).memLp
  have hvg : ∀ k, MemLp (fun x => smoothGrad (v k) x j) 2 (haar d) := fun k =>
    memLp_coord (hvw k).memLp_grad j
  have hYj := memLp_coord hy.memLp_grad j
  have hgj := memLp_coord hu.memLp_grad j
  have t1 := tendsto_integral_mul_L2 hu.memLp hvg hYj (hv1 j)
  have t2 := tendsto_integral_mul_L2 hgj hvm hy.memLp hv0
  have t3 : Tendsto (fun k => ∫ x, u x * smoothGrad (v k) x j ∂haar d) atTop
      (𝓝 (-∫ x, g x j * y x ∂haar d)) := by
    have := t2.neg
    refine this.congr fun k => ?_
    rw [← hu.ibp (v k) (hvs k) j]
    simp only [smoothGrad_apply]
  exact tendsto_nhds_unique t1 t3


/-- The vector field with coordinate functions `f i`. -/
noncomputable def vecOf (f : Fin d → Torus d → ℝ) (x : Torus d) : Tangent d :=
  WithLp.toLp 2 fun i => f i x

theorem memLp_vecOf {μ : Measure (Torus d)} {f : Fin d → Torus d → ℝ}
    (h : ∀ i, MemLp (f i) 2 μ) : MemLp (vecOf f) 2 μ := by
  have e : vecOf f = fun x => ∑ i, f i x • (EuclideanSpace.single i (1 : ℝ) : Tangent d) := by
    funext x; ext j; simp [vecOf, Pi.single_apply]
  rw [e]
  refine memLp_finsetSum _ fun i _ => ?_
  exact ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i (1 : ℝ) : Tangent d) :
      ℝ →L[ℝ] Tangent d).comp_memLp' (h i)

theorem hessian_col {u : Torus d → ℝ} {G : Torus d → Tangent d} {H : Fin d → Fin d → Torus d → ℝ}
    (hH : IsWeakHessian u G H) (j : Fin d) :
    IsWeakGradient (fun x => G x j) (vecOf fun i => H i j) where
  memLp := memLp_coord hH.grad.memLp_grad j
  memLp_grad := memLp_vecOf fun i => hH.memLp_hess i j
  ibp φ hφ i := by
    simpa [vecOf] using hH.ibp i j φ hφ


theorem forward_identity {w : Torus d → ℝ} {b : Torus d → Tangent d} {c C : ℝ}
    (hwd : WData d w b c C) {f : Torus d → ℝ} {G : Torus d → Tangent d}
    {H : Fin d → Fin d → Torus d → ℝ} (hH : IsWeakHessian f G H)
    {y : Torus d → ℝ} {Y : Torus d → Tangent d} (hy : IsWeakGradient y Y) :
    ∫ x, ⟪G x, Y x⟫_ℝ * w x ∂haar d =
      -∫ x, (∑ i, H i i x + ⟪b x, G x⟫_ℝ) * y x * w x ∂haar d := by
  have hprod : ∀ j : Fin d, IsWeakGradient (fun x => G x j * w x)
      (fun x => w x • vecOf (fun i => H i j) x + G x j • (w x • b x)) := fun j =>
    IsWeakGradient.mul_W1infty (hessian_col hH j) hwd.grad_w
  have key : ∀ j : Fin d, ∫ x, G x j * w x * Y x j ∂haar d =
      -∫ x, (w x * H j j x + G x j * (w x * b x j)) * y x ∂haar d := by
    intro j
    have := ibp_H1 (hprod j) hy j
    simpa [vecOf] using this
  have hint1 : ∀ j : Fin d, Integrable (fun x => G x j * w x * Y x j) (haar d) := by
    intro j
    have h1 : MemLp (fun x => G x j * w x) 2 (haar d) := (hprod j).memLp
    exact h1.integrable_mul (memLp_coord hy.memLp_grad j)
  have hint2 : ∀ j : Fin d, Integrable
      (fun x => (w x * H j j x + G x j * (w x * b x j)) * y x) (haar d) := by
    intro j
    have h1 := (hprod j).memLp_grad
    have h2 := memLp_coord h1 j
    have h3 : MemLp (fun x => w x * H j j x + G x j * (w x * b x j)) 2 (haar d) := by
      simpa [vecOf] using h2
    exact h3.integrable_mul hy.memLp
  have e1 : ∀ x, ⟪G x, Y x⟫_ℝ * w x = ∑ j, G x j * w x * Y x j := by
    intro x
    rw [PiLp.inner_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [mul_comm, mul_assoc]
  have e2 : ∀ x, (∑ i, H i i x + ⟪b x, G x⟫_ℝ) * y x * w x =
      ∑ j, (w x * H j j x + G x j * (w x * b x j)) * y x := by
    intro x
    have hi : ⟪b x, G x⟫_ℝ = ∑ j, G x j * b x j := by
      rw [PiLp.inner_apply]; simp [mul_comm]
    rw [hi, ← Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e1, e2]
  rw [integral_finsetSum _ (fun j _ => hint1 j), integral_finsetSum _ (fun j _ => hint2 j),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => key j


theorem inner_tangent (u v : Tangent d) : ⟪u, v⟫_ℝ = ∑ j, u j * v j := by
  rw [PiLp.inner_apply]; simp [mul_comm]

theorem memLp_top_coord {b : Torus d → Tangent d} (hb : MemLp b ∞ (haar d)) (j : Fin d) :
    MemLp (fun x => b x j) ∞ (haar d) :=
  (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).comp_memLp' hb

theorem memLp_inner_top {b G : Torus d → Tangent d} (hb : MemLp b ∞ (haar d))
    (hG : MemLp G 2 (haar d)) : MemLp (fun x => ⟪b x, G x⟫_ℝ) 2 (haar d) := by
  have e : (fun x => ⟪b x, G x⟫_ℝ) = fun x => ∑ j, G x j * b x j := by
    funext x; rw [inner_tangent]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [e]
  exact memLp_finsetSum _ fun j _ => memLp_mul_top (memLp_top_coord hb j) (memLp_coord hG j)

theorem integrable_inner_smooth {G : Torus d → Tangent d} (hG : MemLp G 2 (haar d))
    {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    Integrable (fun x => ⟪G x, smoothGrad φ x⟫_ℝ) (haar d) := by
  have e : (fun x => ⟪G x, smoothGrad φ x⟫_ℝ) =
      fun x => ∑ j, G x j * coordPartial j φ x := by
    funext x; rw [inner_tangent]; rfl
  rw [e]
  exact integrable_finsetSum _ fun j _ =>
    integrable_mul_of_memLp_two (memLp_coord hG j) (hφ.memLp_top_coordPartial j)

theorem converse_laplacian {w : Torus d → ℝ} {b : Torus d → Tangent d} {c C : ℝ}
    (hwd : WData d w b c C) {x : Torus d → ℝ} {G : Torus d → Tangent d}
    (hx : IsWeakGradient x G) {g : Torus d → ℝ} (hg : MemLp g 2 (haar d))
    (H : ∀ (y : Torus d → ℝ) (Y : Torus d → Tangent d), IsWeakGradient y Y →
      ∫ z, ⟪G z, Y z⟫_ℝ * w z ∂haar d = ∫ z, g z * y z * w z ∂haar d) :
    IsWeakLaplacian x (fun z => -(g z + ⟪b z, G z⟫_ℝ)) where
  memLp := hx.memLp
  memLp_lap := (hg.add (memLp_inner_top hwd.b_bdd hx.memLp_grad)).neg
  ibp φ hφ := by
    have hy := IsWeakGradient.mul_smooth hφ hwd.grad_inv
    have H1 := H _ _ hy
    have hw0 : ∀ z, w z ≠ 0 := fun z => (lt_of_lt_of_le hwd.pos (hwd.bound z).1).ne'
    have p1 : ∀ z, ⟪G z, (w z)⁻¹ • smoothGrad φ z + φ z • (-((w z)⁻¹ • b z))⟫_ℝ * w z =
        ⟪G z, smoothGrad φ z⟫_ℝ - φ z * ⟪b z, G z⟫_ℝ := by
      intro z
      rw [inner_add_right, inner_smul_right, inner_smul_right, inner_neg_right, inner_smul_right,
        real_inner_comm (b z) (G z)]
      field_simp [hw0 z]
      ring
    have p2 : ∀ z, g z * (φ z * (w z)⁻¹) * w z = g z * φ z := by
      intro z; field_simp [hw0 z]
    simp_rw [p1, p2] at H1
    have i1 := integrable_inner_smooth hx.memLp_grad hφ
    have i2 : Integrable (fun z => φ z * ⟪b z, G z⟫_ℝ) (haar d) := by
      have := integrable_mul_of_memLp_two (memLp_inner_top hwd.b_bdd hx.memLp_grad) hφ.memLp_top
      simpa [mul_comm] using this
    have i3 : Integrable (fun z => g z * φ z) (haar d) := integrable_mul_of_memLp_two hg hφ.memLp_top
    have i4 : Integrable (fun z => ⟪b z, G z⟫_ℝ * φ z) (haar d) :=
      integrable_mul_of_memLp_two (memLp_inner_top hwd.b_bdd hx.memLp_grad) hφ.memLp_top
    rw [integral_sub i1 i2] at H1
    have lap : ∫ z, x z * periodicLaplacian φ z ∂haar d = -∫ z, ⟪G z, smoothGrad φ z⟫_ℝ ∂haar d := by
      have e1 : ∀ z, x z * periodicLaplacian φ z =
          ∑ j, x z * coordPartial j (coordPartial j φ) z := by
        intro z; unfold periodicLaplacian; rw [Finset.mul_sum]
      have e2 : ∀ z, ⟪G z, smoothGrad φ z⟫_ℝ = ∑ j, G z j * coordPartial j φ z := by
        intro z; rw [inner_tangent]; rfl
      simp_rw [e1, e2]
      rw [integral_finsetSum _ (fun j _ => integrable_mul_of_memLp_two hx.memLp
        ((hφ.isSmoothPeriodic_coordPartial j).memLp_top_coordPartial j |> fun _ =>
          (hφ.isSmoothPeriodic_coordPartial j).memLp_top_coordPartial j)),
        integral_finsetSum _ (fun j _ => integrable_mul_of_memLp_two (memLp_coord hx.memLp_grad j)
          (hφ.memLp_top_coordPartial j)), ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j _ => hx.ibp _ (hφ.isSmoothPeriodic_coordPartial j) j
    rw [lap]
    have : ∫ z, -(g z + ⟪b z, G z⟫_ℝ) * φ z ∂haar d =
        -(∫ z, g z * φ z ∂haar d + ∫ z, ⟪b z, G z⟫_ℝ * φ z ∂haar d) := by
      rw [← integral_add i3 i4, ← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun z => by ring)
    rw [this]
    have h5 : ∫ z, φ z * ⟪b z, G z⟫_ℝ ∂haar d = ∫ z, ⟪b z, G z⟫_ℝ * φ z ∂haar d :=
      integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _)
    rw [h5] at H1
    linarith

end IBP

section Domain

open DGPS DGPS.Lipschitz DGPS.Analysis DGPS.Analysis.CompactResolvent
open scoped InnerProductSpace

variable {d : ℕ} {w : Torus d → ℝ} {b : Torus d → Tangent d} {c C : ℝ}

theorem exists_kspace (hc : 0 < c) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    {y : Torus d → ℝ} {Y : Torus d → Tangent d} (hy : IsWeakGradient y Y) :
    ∃ k : Kspace hc hwb, (formJ hc hwb k : Torus d → ℝ) =ᵐ[haar d] y ∧
      formGrad hc hwb k =ᵐ[haar d] Y := by
  have hvμ : MemLp y 2 (wMeasure d w) := (memLp_wMeasure_iff hc hwb).mpr hy.memLp
  have hGμ : MemLp Y 2 (wMeasure d w) := (memLp_wMeasure_iff hc hwb).mpr hy.memLp_grad
  let q : Amb d w := WithLp.toLp 2 (hvμ.toLp y, hGμ.toLp Y)
  have hq : q ∈ Kspace hc hwb := by
    refine hy.congr_ae ?_ ?_
    · exact (ae_eq_haar hc hwb hvμ.coeFn_toLp).symm
    · exact (ae_eq_haar hc hwb hGμ.coeFn_toLp).symm
  exact ⟨⟨q, hq⟩, ae_eq_haar hc hwb hvμ.coeFn_toLp, ae_eq_haar hc hwb hGμ.coeFn_toLp⟩

theorem hess_mem_domain (hwd : WData d w b c C) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (A : Hw d w →ₗ.[ℝ] Hw d w)
    (hA : ∀ (x : Kspace hwd.pos hwb) (g : Hw d w),
      (∀ y, formE (formJ hwd.pos hwb) x y = ⟪g, formJ hwd.pos hwb y⟫_ℝ) →
        ∃ hx : formJ hwd.pos hwb x ∈ A.domain, A ⟨formJ hwd.pos hwb x, hx⟩ = g)
    (f : Hw d w) {G : Torus d → Tangent d} {H : Fin d → Fin d → Torus d → ℝ}
    (hH : IsWeakHessian (f : Torus d → ℝ) G H) :
    ∃ hf : f ∈ A.domain, (A ⟨f, hf⟩ : Torus d → ℝ) =ᵐ[haar d]
      fun x => -(∑ i, H i i x + ⟪b x, G x⟫_ℝ) := by
  have hc := hwd.pos
  obtain ⟨k, hk1, hk2⟩ := exists_kspace hc hwb hH.grad
  have hfJ : formJ hc hwb k = f := by
    refine Lp.ext ?_
    exact ae_eq_wMeasure hk1
  have hgL : MemLp (fun x => -(∑ i, H i i x + ⟪b x, G x⟫_ℝ)) 2 (haar d) := by
    have h1 : MemLp (fun x => ∑ i, H i i x) 2 (haar d) :=
      memLp_finsetSum _ fun i _ => hH.memLp_hess i i
    exact (h1.add (memLp_inner_top hwd.b_bdd hH.grad.memLp_grad)).neg
  have hgμ : MemLp (fun x => -(∑ i, H i i x + ⟪b x, G x⟫_ℝ)) 2 (wMeasure d w) :=
    (memLp_wMeasure_iff hc hwb).mpr hgL
  set g : Hw d w := hgμ.toLp _ with hg
  have hgae : (g : Torus d → ℝ) =ᵐ[haar d] fun x => -(∑ i, H i i x + ⟪b x, G x⟫_ℝ) :=
    ae_eq_haar hc hwb hgμ.coeFn_toLp
  have key : ∀ y : Kspace hc hwb, formE (formJ hc hwb) k y = ⟪g, formJ hc hwb y⟫_ℝ := by
    intro y
    rw [formE_formJ hwd.meas hc hwb, inner_Lp_wMeasure hwd.meas hc hwb]
    unfold weightedForm
    have hid := forward_identity hwd hH (isWeakGradient_formJ hc hwb y)
    have e1 : ∫ x, ⟪formGrad hc hwb k x, formGrad hc hwb y x⟫_ℝ * w x ∂haar d =
        ∫ x, ⟪G x, formGrad hc hwb y x⟫_ℝ * w x ∂haar d := by
      refine integral_congr_ae ?_
      filter_upwards [hk2] with x hx
      rw [hx]
    rw [e1, hid]
    rw [← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hgae] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  obtain ⟨hx, hAx⟩ := hA k g key
  have hf : f ∈ A.domain := hfJ ▸ hx
  refine ⟨hf, ?_⟩
  have hsub : (⟨f, hf⟩ : A.domain) = ⟨formJ hc hwb k, hx⟩ := Subtype.ext hfJ.symm
  rw [hsub, hAx]
  exact hgae

theorem domain_mem_h2 (hwd : WData d w b c C) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (A : Hw d w →ₗ.[ℝ] Hw d w)
    (hA : ∀ f : A.domain, ∃ x : Kspace hwd.pos hwb, formJ hwd.pos hwb x = (f : Hw d w) ∧
      ∀ y, formE (formJ hwd.pos hwb) x y = ⟪A f, formJ hwd.pos hwb y⟫_ℝ)
    (f : Hw d w) (hf : f ∈ A.domain) :
    ∃ (G : Torus d → Tangent d) (H : Fin d → Fin d → Torus d → ℝ),
      IsWeakHessian (f : Torus d → ℝ) G H ∧
      (A ⟨f, hf⟩ : Torus d → ℝ) =ᵐ[haar d] fun x => -(∑ i, H i i x + ⟪b x, G x⟫_ℝ) := by
  have hc := hwd.pos
  obtain ⟨x, hxJ, hxE⟩ := hA ⟨f, hf⟩
  have hxJ' : formJ hc hwb x = f := hxJ
  have hu : IsWeakGradient (f : Torus d → ℝ) (formGrad hc hwb x) := by
    rw [← hxJ']; exact isWeakGradient_formJ hc hwb x
  have hg : MemLp ((A ⟨f, hf⟩ : Hw d w) : Torus d → ℝ) 2 (haar d) :=
    (memLp_wMeasure_iff hc hwb).mp (Lp.memLp _)
  have hid : ∀ (y : Torus d → ℝ) (Y : Torus d → Tangent d), IsWeakGradient y Y →
      ∫ z, ⟪formGrad hc hwb x z, Y z⟫_ℝ * w z ∂haar d =
        ∫ z, ((A ⟨f, hf⟩ : Hw d w) : Torus d → ℝ) z * y z * w z ∂haar d := by
    intro y Y hy
    obtain ⟨k, hk1, hk2⟩ := exists_kspace hc hwb hy
    have h := hxE k
    rw [formE_formJ hwd.meas hc hwb, inner_Lp_wMeasure hwd.meas hc hwb] at h
    unfold weightedForm at h
    refine (integral_congr_ae ?_).trans (h.trans (integral_congr_ae ?_))
    · filter_upwards [hk2] with z hz
      rw [hz]
    · filter_upwards [hk1] with z hz
      rw [hz]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
  have hlap := converse_laplacian hwd hu hg hid
  obtain ⟨C0, -, h1, h2⟩ := periodic_laplacian_h2_regularity d
  obtain ⟨-, G', H', hH', -⟩ := h1 _ _ ⟨_, hu⟩ hlap
  have hlap' := (h2 _ G' H' hH').1
  have hGae : formGrad hc hwb x =ᵐ[haar d] G' := hu.ae_eq hH'.grad
  have hdiff : (fun z => ∑ i, H' i i z - (-(((A ⟨f, hf⟩ : Hw d w) : Torus d → ℝ) z +
      ⟪b z, formGrad hc hwb x z⟫_ℝ))) =ᵐ[haar d] 0 := by
    refine ae_eq_zero_of_forall_integral_mul_eq_zero (hlap'.memLp_lap.sub hlap.memLp_lap) ?_
    intro φ hφ
    have e1 := hlap'.ibp φ hφ
    have e2 := hlap.ibp φ hφ
    have i1 : Integrable (fun z => (∑ i, H' i i z) * φ z) (haar d) :=
      integrable_mul_of_memLp_two hlap'.memLp_lap hφ.memLp_top
    have i2 : Integrable (fun z => (-(((A ⟨f, hf⟩ : Hw d w) : Torus d → ℝ) z +
        ⟪b z, formGrad hc hwb x z⟫_ℝ)) * φ z) (haar d) :=
      integrable_mul_of_memLp_two hlap.memLp_lap hφ.memLp_top
    simp only [sub_mul]
    rw [integral_sub i1 i2, ← e1, ← e2, sub_self]
  refine ⟨G', H', hH', ?_⟩
  filter_upwards [hdiff, hGae] with z hz hz2
  simp only [Pi.zero_apply] at hz
  rw [← hz2]
  linarith

theorem clip_sq_le {a f : ℝ} (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    (min (max a 0) 1 - f) ^ 2 ≤ (a - f) ^ 2 := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, min_eq_left zero_le_one]; nlinarith
  · rw [max_eq_left h]
    rcases le_total a 1 with h' | h'
    · rw [min_eq_left h']
    · rw [min_eq_right h']; nlinarith

theorem integrable_sq_mul_w (hwd : WData d w b c C) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (a : Hw d w) : Integrable (fun z => ((a : Hw d w) : Torus d → ℝ) z ^ 2 * w z) (haar d) := by
  have ha : MemLp ((a : Hw d w) : Torus d → ℝ) 2 (haar d) :=
    (memLp_wMeasure_iff hwd.pos hwb).mp (Lp.memLp a)
  have h1 := ha.integrable_sq.const_mul C
  refine h1.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact ((ha.aestronglyMeasurable.pow 2).mul hwd.meas.aestronglyMeasurable)
  · have hw := hwd.bound z
    have : 0 ≤ w z := (hwd.pos.le.trans hw.1)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) this)]
    nlinarith [sq_nonneg (((a : Hw d w) : Torus d → ℝ) z)]

theorem resolvent_unit (hwd : WData d w b c C) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    {h : ℝ} (hh : 0 < h) (f r : Hw d w) (hf0 : 0 ≤ᵐ[wMeasure d w] f)
    (hf1 : f ≤ᵐ[wMeasure d w] fun _ => (1 : ℝ))
    (hx : ∃ x : Kspace hwd.pos hwb, ∀ y, Spec.obj (formJ hwd.pos hwb) h f x ≤
      Spec.obj (formJ hwd.pos hwb) h f y)
    (hr : ∀ x : Kspace hwd.pos hwb, (∀ y, Spec.obj (formJ hwd.pos hwb) h f x ≤
      Spec.obj (formJ hwd.pos hwb) h f y) → formJ hwd.pos hwb x = r) :
    (0 ≤ᵐ[wMeasure d w] r) ∧ (r ≤ᵐ[wMeasure d w] fun _ => (1 : ℝ)) := by
  have hc := hwd.pos
  obtain ⟨x, hx⟩ := hx
  have hf0' : ∀ᵐ z ∂haar d, 0 ≤ f z := (ae_wMeasure_iff hc hwb).mp hf0
  have hf1' : ∀ᵐ z ∂haar d, f z ≤ 1 := (ae_wMeasure_iff hc hwb).mp hf1
  have hu := isWeakGradient_formJ hc hwb x
  obtain ⟨g', hg', hE⟩ := markov_unit_contraction hwd.meas hwb hc hu
  obtain ⟨k, hk1, hk2⟩ := exists_kspace hc hwb hg'
  have hobj : Spec.obj (formJ hc hwb) h f k ≤ Spec.obj (formJ hc hwb) h f x := by
    unfold Spec.obj
    have hn : ∀ a : Hw d w, ‖a‖ ^ 2 = ∫ z, (a : Torus d → ℝ) z ^ 2 * w z ∂haar d :=
      norm_sq_Hw hwd.meas hc hwb
    have e1 : ‖formJ hc hwb k - f‖ ^ 2 ≤ ‖formJ hc hwb x - f‖ ^ 2 := by
      rw [hn, hn]
      have s1 := ae_eq_haar hc hwb (Lp.coeFn_sub (formJ hc hwb k) f)
      have s2 := ae_eq_haar hc hwb (Lp.coeFn_sub (formJ hc hwb x) f)
      have hi := integrable_sq_mul_w hwd hwb (formJ hc hwb x - f)
      refine integral_mono_of_nonneg (Eventually.of_forall fun z => ?_) hi ?_
      · exact mul_nonneg (sq_nonneg _) (hc.le.trans (hwd.bound z).1)
      · filter_upwards [s1, s2, hk1, hf0', hf1'] with z h1 h2 h3 h4 h5
        rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3]
        exact mul_le_mul_of_nonneg_right (clip_sq_le h4 h5) (hc.le.trans (hwd.bound z).1)
    have e2 : formE (formJ hc hwb) k k ≤ formE (formJ hc hwb) x x := by
      rw [formE_formJ hwd.meas hc hwb, formE_formJ hwd.meas hc hwb, weightedForm_self,
        weightedForm_self]
      refine le_trans (le_of_eq (integral_congr_ae ?_)) hE
      filter_upwards [hk2] with z hz
      rw [hz]
    nlinarith
  have hmin : ∀ y, Spec.obj (formJ hc hwb) h f k ≤ Spec.obj (formJ hc hwb) h f y :=
    fun y => hobj.trans (hx y)
  have hkr := hr k hmin
  have hxr := hr x hx
  have heq : formJ hc hwb k = formJ hc hwb x := hkr.trans hxr.symm
  have hc1 : ∀ᵐ z ∂haar d, (formJ hc hwb x : Torus d → ℝ) z =
      min (max ((formJ hc hwb x : Torus d → ℝ) z) 0) 1 := by
    filter_upwards [hk1] with z hz
    rw [← hz, heq]
  rw [← hxr]
  have hb0 : ∀ᵐ z ∂haar d, 0 ≤ (formJ hc hwb x : Torus d → ℝ) z ∧
      (formJ hc hwb x : Torus d → ℝ) z ≤ 1 := by
    filter_upwards [hc1] with z hz
    rw [hz]
    exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  have := (ae_wMeasure_iff hc hwb).mpr hb0
  exact ⟨this.mono fun z hz => hz.1, this.mono fun z hz => hz.2⟩

theorem isFiniteMeasure_wMeasure (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C) :
    IsFiniteMeasure (wMeasure d w) :=
  haveI : IsFiniteMeasure (ENNReal.ofReal C • haar d) :=
    Measure.smul_finite (haar d) ENNReal.ofReal_ne_top
  isFiniteMeasure_of_le (ENNReal.ofReal C • haar d) (wMeasure_le hwb)

theorem resolvent_one (hwd : WData d w b c C) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    [IsFiniteMeasure (wMeasure d w)] {h : ℝ} (hh : 0 < h) (r : Hw d w)
    (hr : ∀ x : Kspace hwd.pos hwb, (∀ y, Spec.obj (formJ hwd.pos hwb) h (oneLp (wMeasure d w)) x ≤
      Spec.obj (formJ hwd.pos hwb) h (oneLp (wMeasure d w)) y) → formJ hwd.pos hwb x = r) :
    r = oneLp (wMeasure d w) := by
  have hc := hwd.pos
  obtain ⟨k, hk1, hk2⟩ := exists_kspace hc hwb (isWeakGradient_const (d := d) 1)
  have hJ : formJ hc hwb k = oneLp (wMeasure d w) := by
    refine Lp.ext ?_
    exact (ae_eq_wMeasure hk1).trans coeFn_oneLp.symm
  have hE : formE (formJ hc hwb) k k = 0 := by
    rw [formE_formJ hwd.meas hc hwb, weightedForm_self]
    have : ∀ᵐ z ∂haar d, ‖formGrad hc hwb k z‖ ^ 2 * w z = 0 := by
      filter_upwards [hk2] with z hz
      rw [hz]; simp
    rw [integral_congr_ae this]; simp
  have hobj : ∀ y, Spec.obj (formJ hc hwb) h (oneLp (wMeasure d w)) k ≤
      Spec.obj (formJ hc hwb) h (oneLp (wMeasure d w)) y := by
    intro y
    unfold Spec.obj
    rw [hJ, hE, sub_self, norm_zero]
    have h0 : 0 ≤ formE (formJ hc hwb) y y := by
      rw [formE_formJ hwd.meas hc hwb, weightedForm_self]
      exact integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hc.le.trans (hwd.bound z).1)
    nlinarith [sq_nonneg ‖formJ hc hwb y - oneLp (wMeasure d w)‖]
  exact (hJ.symm.trans (hr k hobj)).symm

end Domain


section Semigroup

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem unit_iff_le (f : Lp ℝ 2 μ) :
    ((0 ≤ᵐ[μ] f) ∧ (f ≤ᵐ[μ] fun _ => (1 : ℝ))) ↔ (0 ≤ f ∧ f ≤ oneLp μ) := by
  rw [← Lp.coeFn_nonneg, ← Lp.coeFn_le]
  refine and_congr Iff.rfl ?_
  constructor
  · intro h
    filter_upwards [h, coeFn_oneLp (μ := μ)] with x h1 h2
    rw [h2]; exact h1
  · intro h
    filter_upwards [h, coeFn_oneLp (μ := μ)] with x h1 h2
    rw [← h2]; exact h1

theorem semigroup_markov (R : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (T : NNReal → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hR : ∀ h : ℝ, 0 < h → ∀ f : Lp ℝ 2 μ, (0 ≤ᵐ[μ] f) → (f ≤ᵐ[μ] fun _ => (1 : ℝ)) →
      (0 ≤ᵐ[μ] R h f) ∧ (R h f ≤ᵐ[μ] fun _ => (1 : ℝ)))
    (hR1 : ∀ h : ℝ, 0 < h → R h (oneLp μ) = oneLp μ)
    (hT0 : ∀ f, T 0 f = f)
    (hprod : ∀ (t : NNReal) (f : Lp ℝ 2 μ), Tendsto (fun n : ℕ => ((R ((t : ℝ) / n)) ^ n) f) atTop
      (𝓝 (T t f))) (t : NNReal) :
    (∀ f : Lp ℝ 2 μ, (0 ≤ᵐ[μ] f) → (f ≤ᵐ[μ] fun _ => (1 : ℝ)) →
      (0 ≤ᵐ[μ] T t f) ∧ (T t f ≤ᵐ[μ] fun _ => (1 : ℝ))) ∧ T t (oneLp μ) = oneLp μ := by
  rcases eq_or_ne t 0 with rfl | ht
  · refine ⟨fun f h0 h1 => by rw [hT0]; exact ⟨h0, h1⟩, hT0 _⟩
  have htpos : (0 : ℝ) < t := by exact_mod_cast pos_iff_ne_zero.mpr ht
  have hev : ∀ᶠ n : ℕ in atTop, 0 < (t : ℝ) / n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact div_pos htpos (by exact_mod_cast hn)
  have hpow : ∀ (h : ℝ), 0 < h → ∀ (n : ℕ) (f : Lp ℝ 2 μ), (0 ≤ f ∧ f ≤ oneLp μ) →
      (0 ≤ (R h ^ n) f ∧ (R h ^ n) f ≤ oneLp μ) := by
    intro h hh n
    induction n with
    | zero => intro f hf; simpa using hf
    | succ n ih =>
      intro f hf
      rw [pow_succ, mul_apply_eq_comp]
      apply ih
      exact (unit_iff_le _).mp (hR h hh f ((unit_iff_le f).mpr hf).1 ((unit_iff_le f).mpr hf).2)
  have hpow1 : ∀ (h : ℝ), 0 < h → ∀ n : ℕ, (R h ^ n) (oneLp μ) = oneLp μ := by
    intro h hh n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_apply_eq_comp, hR1 h hh, ih]
  refine ⟨fun f h0 h1 => ?_, ?_⟩
  · have hf := (unit_iff_le f).mp ⟨h0, h1⟩
    have hl := hprod t f
    rw [unit_iff_le]
    refine ⟨ge_of_tendsto hl ?_, le_of_tendsto hl ?_⟩
    · filter_upwards [hev] with n hn using (hpow _ hn n f hf).1
    · filter_upwards [hev] with n hn using (hpow _ hn n f hf).2
  · have hl := hprod t (oneLp μ)
    refine tendsto_nhds_unique hl ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    rw [hpow1 _ hn n]

end Semigroup

section Neg

open scoped LinearPMap InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem adjoint_neg (A : E →ₗ.[ℝ] E) (hA : Dense (A.domain : Set E)) : (-A)† = -(A†) := by
  have hA' : Dense ((-A).domain : Set E) := hA
  have hdom : ∀ y : E, y ∈ ((-A)†).domain ↔ y ∈ (A†).domain := by
    intro y
    rw [LinearPMap.mem_adjoint_domain_iff, LinearPMap.mem_adjoint_domain_iff]
    constructor
    · intro h
      have := h.neg
      convert this using 1
      ext x; simp
    · intro h
      have := h.neg
      convert this using 1
      ext x; simp
  refine LinearPMap.ext ?_ ?_
  · ext y; exact (hdom y).trans Iff.rfl
  · intro y z w
    have hy : y ∈ (A†).domain := (hdom y).1 z
    have h1 : ((-A)† ⟨y, z⟩) = -(A† ⟨y, hy⟩) := by
      apply LinearPMap.adjoint_apply_eq hA' ⟨y, z⟩
      intro x
      have := LinearPMap.adjoint_isFormalAdjoint hA ⟨y, hy⟩ ⟨(x:E), x.2⟩
      simp only [LinearPMap.neg_apply, inner_neg_left, inner_neg_right] at this ⊢
      rw [this]; rfl
    rw [h1]; rfl

end Neg

section Final

open DGPS DGPS.Lipschitz DGPS.Analysis DGPS.Analysis.CompactResolvent
open scoped InnerProductSpace LinearPMap

variable {d : ℕ}

theorem wdata_congr_b {w : Torus d → ℝ} {b b' : Torus d → Tangent d} {c C : ℝ}
    (h : WData d w b c C) (hb : b =ᵐ[haar d] b') : WData d w b' c C where
  meas := h.meas
  pos := h.pos
  bound := h.bound
  grad_w := isWeakGradientLp_congr_grad h.grad_w (hb.mono fun x hx => by simp [hx])
  grad_inv := isWeakGradientLp_congr_grad h.grad_inv (hb.mono fun x hx => by simp [hx])
  b_bdd := h.b_bdd.ae_eq hb

theorem log_gibbs_grad {Φ : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L) (hΦ : TorusLipschitzWith L Φ)
    {b : Torus d → Tangent d}
    (hb : IsWeakGradient (fun x => Real.log (gibbsW Φ x)) b) :
    b =ᵐ[haar d] fun x => -smoothGrad Φ x := by
  have hc := torusLipschitz_continuous hΦ
  obtain ⟨M, hM⟩ := exists_bound_continuous hc
  obtain ⟨hg', -⟩ := exists_weak_gradient hL hΦ
  have h2' : IsWeakGradient Φ (smoothGrad Φ) := isWeakGradient_iff_isWeakGradientLp.mpr
    ⟨hg'.memLp.mono_exponent (by simp), hg'.memLp_grad.mono_exponent (by simp), hg'.ibp⟩
  have h3 := h2'.affine (-1) (-Real.log (∫ y, Real.exp (-Φ y) ∂haar d))
  have hfun : (fun x => Real.log (gibbsW Φ x)) =
      fun x => (-1) * Φ x + -Real.log (∫ y, Real.exp (-Φ y) ∂haar d) := by
    funext x; rw [log_gibbsW hc hM x]; ring
  rw [hfun] at hb
  refine (hb.ae_eq h3).mono fun x hx => ?_
  rw [hx]; simp

theorem form_generator_relation {w : Torus d → ℝ} {b : Torus d → Tangent d} {c C : ℝ}
    (hwd : WData d w b c C) (hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C)
    (A : Hw d w →ₗ.[ℝ] Hw d w)
    (hA : ∀ f : A.domain, ∃ x : Kspace hwd.pos hwb, formJ hwd.pos hwb x = (f : Hw d w) ∧
      ∀ y, formE (formJ hwd.pos hwb) x y = ⟪A f, formJ hwd.pos hwb y⟫_ℝ)
    (f : Hw d w) (hf : f ∈ A.domain) {Gf : Torus d → Tangent d}
    (hGf : IsWeakGradient (f : Torus d → ℝ) Gf)
    (v : Hw d w) {Gv : Torus d → Tangent d} (hGv : IsWeakGradient (v : Torus d → ℝ) Gv) :
    weightedForm w Gf Gv = ⟪A ⟨f, hf⟩, v⟫_ℝ := by
  have hc := hwd.pos
  obtain ⟨x, hxJ, hxE⟩ := hA ⟨f, hf⟩
  obtain ⟨k, hk1, hk2⟩ := exists_kspace hc hwb hGv
  have hkJ : formJ hc hwb k = v := Lp.ext (ae_eq_wMeasure hk1)
  have hxJ' : formJ hc hwb x = f := hxJ
  have hx1 := isWeakGradient_formJ hc hwb x
  rw [hxJ'] at hx1
  have hgx : formGrad hc hwb x =ᵐ[haar d] Gf := hx1.ae_eq hGf
  rw [← hkJ, ← hxE k, formE_formJ hwd.meas hc hwb]
  unfold weightedForm
  refine integral_congr_ae ?_
  filter_upwards [hgx, hk2] with z h1 h2
  rw [h1, h2]

theorem closed_weighted_form_and_generator_domain {Φ : Torus d → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hΦ : TorusLipschitzWith L Φ) {b : Torus d → Tangent d}
    (hb : IsWeakGradient (fun x => Real.log (gibbsW Φ x)) b) :
    -- the form is densely defined, symmetric, closed and Markov
    Dense {f : Hw d (gibbsW Φ) | MemH1 (f : Torus d → ℝ)} ∧
    (∀ g h : Torus d → Tangent d,
      weightedForm (gibbsW Φ) g h = weightedForm (gibbsW Φ) h g) ∧
    IsClosed {p : Amb d (gibbsW Φ) |
      IsWeakGradient (p.ofLp.1 : Torus d → ℝ) (p.ofLp.2 : Torus d → Tangent d)} ∧
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      ∃ g' : Torus d → Tangent d, IsWeakGradient (fun x => min (max (u x) 0) 1) g' ∧
        ∫ x, ‖g' x‖ ^ 2 * gibbsW Φ x ∂haar d ≤ ∫ x, ‖g x‖ ^ 2 * gibbsW Φ x ∂haar d) ∧
    -- generator and semigroup
    ∃ (Lg : Hw d (gibbsW Φ) →ₗ.[ℝ] Hw d (gibbsW Φ))
      (S : NNReal → Hw d (gibbsW Φ) →L[ℝ] Hw d (gibbsW Φ)),
      IsSelfAdjoint Lg ∧ Dense (Lg.domain : Set (Hw d (gibbsW Φ))) ∧
      (∀ f : Hw d (gibbsW Φ), f ∈ Lg.domain ↔ MemH2 (f : Torus d → ℝ)) ∧
      (∀ (f : Hw d (gibbsW Φ)) (hf : f ∈ Lg.domain) (G : Torus d → Tangent d)
        (H : Fin d → Fin d → Torus d → ℝ), IsWeakHessian (f : Torus d → ℝ) G H →
        (Lg ⟨f, hf⟩ : Torus d → ℝ) =ᵐ[haar d] fun x => ∑ i, H i i x + ⟪b x, G x⟫_ℝ) ∧
      (∀ (f : Hw d (gibbsW Φ)) (hf : f ∈ Lg.domain) (Gf : Torus d → Tangent d),
        IsWeakGradient (f : Torus d → ℝ) Gf → ∀ (v : Hw d (gibbsW Φ)) (Gv : Torus d → Tangent d),
        IsWeakGradient (v : Torus d → ℝ) Gv →
          weightedForm (gibbsW Φ) Gf Gv = -⟪Lg ⟨f, hf⟩, v⟫_ℝ) ∧
      (∀ f, S 0 f = f) ∧ (∀ (s t : NNReal) f, S (s + t) f = S s (S t f)) ∧
      (∀ t, ∀ f g : Hw d (gibbsW Φ), ⟪S t f, g⟫_ℝ = ⟪f, S t g⟫_ℝ) ∧
      (∀ f, Continuous fun t : NNReal => S t f) ∧
      (∀ f : Lg.domain, Tendsto (fun t : NNReal => (t : ℝ)⁻¹ • (S t (f : Hw d (gibbsW Φ)) - f))
        (𝓝[≠] (0 : NNReal)) (𝓝 (Lg f))) ∧
      (∀ t, ∀ f : Hw d (gibbsW Φ), (0 ≤ᵐ[wMeasure d (gibbsW Φ)] f) →
          (f ≤ᵐ[wMeasure d (gibbsW Φ)] fun _ => (1 : ℝ)) →
          (0 ≤ᵐ[wMeasure d (gibbsW Φ)] S t f) ∧ (S t f ≤ᵐ[wMeasure d (gibbsW Φ)] fun _ => (1 : ℝ))) ∧
      (∀ t, ∀ f : Hw d (gibbsW Φ), (f : Torus d → ℝ) =ᵐ[wMeasure d (gibbsW Φ)] (fun _ => (1 : ℝ)) →
          (S t f : Torus d → ℝ) =ᵐ[wMeasure d (gibbsW Φ)] fun _ => (1 : ℝ)) ∧
      (∀ (t : NNReal) (p : ℝ≥0∞), 1 ≤ p → ∀ f : Hw d (gibbsW Φ),
        eLpNorm (S t f) p (wMeasure d (gibbsW Φ)) ≤ eLpNorm f p (wMeasure d (gibbsW Φ))) := by
  obtain ⟨c, C, hwd0⟩ := gibbs_wdata hL hΦ
  have hwd := wdata_congr_b hwd0 (log_gibbs_grad hL hΦ hb).symm
  have hc := hwd.pos
  have hwb : ∀ᵐ x ∂haar d, c ≤ gibbsW Φ x ∧ gibbsW Φ x ≤ C := Eventually.of_forall hwd.bound
  have := isFiniteMeasure_wMeasure hwb
  obtain ⟨-, -, -, -, ι, bas, lam, R, T, A, -, hmin, -, -, hSA, hdense, -, -, hAform, hAconv, -,
    hT0, hTadd, hTsym, -, -, hTcont, hTderiv, -, -, hprod⟩ :=
    compact_resolvent_and_semigroup_construction hwd.meas hc hwb
  have hRu : ∀ h : ℝ, 0 < h → ∀ f : Hw d (gibbsW Φ), (0 ≤ᵐ[wMeasure d (gibbsW Φ)] f) →
      (f ≤ᵐ[wMeasure d (gibbsW Φ)] fun _ => (1 : ℝ)) →
      (0 ≤ᵐ[wMeasure d (gibbsW Φ)] R h f) ∧ (R h f ≤ᵐ[wMeasure d (gibbsW Φ)] fun _ => (1 : ℝ)) := by
    intro h hh f hf0 hf1
    obtain ⟨⟨x, hx, -⟩, hr⟩ := hmin h hh f
    exact resolvent_unit hwd hwb hh f (R h f) hf0 hf1 ⟨x, hx⟩ hr
  have hR1 : ∀ h : ℝ, 0 < h → R h (oneLp (wMeasure d (gibbsW Φ))) =
      oneLp (wMeasure d (gibbsW Φ)) := fun h hh =>
    resolvent_one hwd hwb hh _ (hmin h hh _).2
  have hsm := fun t => semigroup_markov R T hRu hR1 hT0 hprod t
  have hmk : ∀ t, MarkovSym (T t) := fun t => ⟨fun f g => hTsym t f g, (hsm t).1, (hsm t).2⟩
  have hdom : ∀ f : Hw d (gibbsW Φ), f ∈ A.domain → MemH1 (f : Torus d → ℝ) := by
    intro f hf
    obtain ⟨G, H, hH, -⟩ := domain_mem_h2 hwd hwb A hAform f hf
    exact ⟨G, hH.grad⟩
  refine ⟨hdense.mono hdom, fun g h => weightedForm_comm g h, ?_,
    fun u g hug => markov_unit_contraction hwd.meas hwb hc hug, -A, T, ?_, ?_, ?_, ?_, ?_, hT0,
    hTadd, fun t f g => hTsym t f g, hTcont, fun f => hTderiv f, fun t => (hmk t).unit, ?_,
    fun t p hp f => (hmk t).eLpNorm_le hp f⟩
  · have hcl : IsClosed (Kspace hc hwb : Set (Amb d (gibbsW Φ))) :=
      (completeSpace_coe_iff_isComplete.mp (completeSpace_Kspace hwd.meas hc hwb)).isClosed
    exact hcl
  · show (-A)† = -A
    rw [adjoint_neg A hdense]
    have : A† = A := hSA
    rw [this]
  · exact hdense
  · intro f
    constructor
    · intro hf
      obtain ⟨G, H, hH, -⟩ := domain_mem_h2 hwd hwb A hAform f hf
      exact ⟨G, H, hH⟩
    · rintro ⟨G, H, hH⟩
      exact (hess_mem_domain hwd hwb A hAconv f hH).1
  · intro f hf G H hH
    obtain ⟨hf', hval⟩ := hess_mem_domain hwd hwb A hAconv f hH
    have e : (-A) ⟨f, hf⟩ = -(A ⟨f, hf'⟩) := rfl
    rw [e]
    have h1 := (ae_wMeasure_iff hc hwb).mp (Lp.coeFn_neg (A ⟨f, hf'⟩))
    filter_upwards [h1, hval] with x h1 h2
    rw [h1, Pi.neg_apply, h2, neg_neg]
  · intro f hf Gf hGf v Gv hGv
    rw [form_generator_relation hwd hwb A hAform f hf hGf v hGv]
    show _ = -⟪-(A ⟨f, hf⟩), v⟫_ℝ
    rw [inner_neg_left, neg_neg]
  · intro t f hf
    have : f = oneLp (wMeasure d (gibbsW Φ)) := Lp.ext (hf.trans coeFn_oneLp.symm)
    rw [this, (hsm t).2]
    exact coeFn_oneLp

end Final

end DGPS.Lipschitz.WeightedGenerator
