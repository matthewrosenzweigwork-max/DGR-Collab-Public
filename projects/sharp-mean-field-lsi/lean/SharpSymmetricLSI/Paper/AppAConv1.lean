import Mathlib

/-!
# Convergence toolkit (1): `L²` convergence of products

`L²` convergence is stated as `∫ (X_b - X)² → 0`. Products of `L²`-convergent families have
convergent integrals (`tendsto_integral_mul_of_L2_appA`); sums and bounded multipliers preserve `L²`
convergence; a uniformly bounded multiplier that is small in `L¹` is small against any `L¹`
function (`tendsto_integral_abs_mul_of_L1`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {β : Type*} {l : Filter β}

theorem eLpNorm_two_eq_sqrt {f : α → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ a, f a ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  congr 1
  · refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  · norm_num

theorem tendsto_eLpNorm_of_L2 {X : β → α → ℝ} {X0 : α → ℝ}
    (hX : ∀ᶠ b in l, MemLp (X b) 2 μ) (hX0 : MemLp X0 2 μ)
    (hXc : Tendsto (fun b => ∫ a, (X b a - X0 a) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun b => eLpNorm (X b - X0) 2 μ) l (𝓝 0) := by
  have h1 : Tendsto (fun b => ENNReal.ofReal (Real.sqrt (∫ a, (X b a - X0 a) ^ 2 ∂μ))) l (𝓝 0) := by
    have := ENNReal.tendsto_ofReal ((Real.continuous_sqrt.tendsto 0).comp hXc)
    simpa using this
  refine h1.congr' ?_
  filter_upwards [hX] with b hb
  rw [eLpNorm_two_eq_sqrt (hb.sub hX0)]
  rfl

/-- **Products of `L²`-convergent families.** -/
theorem tendsto_integral_mul_of_L2_appA {X Y : β → α → ℝ} {X0 Y0 : α → ℝ}
    (hX : ∀ᶠ b in l, MemLp (X b) 2 μ) (hY : ∀ᶠ b in l, MemLp (Y b) 2 μ)
    (hX0 : MemLp X0 2 μ) (hY0 : MemLp Y0 2 μ)
    (hXc : Tendsto (fun b => ∫ a, (X b a - X0 a) ^ 2 ∂μ) l (𝓝 0))
    (hYc : Tendsto (fun b => ∫ a, (Y b a - Y0 a) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun b => ∫ a, X b a * Y b a ∂μ) l (𝓝 (∫ a, X0 a * Y0 a ∂μ)) := by
  classical
  set Xl : β → Lp ℝ 2 μ := fun b => if h : MemLp (X b) 2 μ then h.toLp else 0
  set Yl : β → Lp ℝ 2 μ := fun b => if h : MemLp (Y b) 2 μ then h.toLp else 0
  have conv : ∀ {Z : β → α → ℝ} {Z0 : α → ℝ} (hZ : ∀ᶠ b in l, MemLp (Z b) 2 μ) (hZ0 : MemLp Z0 2 μ),
      Tendsto (fun b => ∫ a, (Z b a - Z0 a) ^ 2 ∂μ) l (𝓝 0) →
      Tendsto (fun b => if h : MemLp (Z b) 2 μ then h.toLp else (0 : Lp ℝ 2 μ)) l
        (𝓝 (hZ0.toLp Z0)) := fun {Z} {Z0} hZ hZ0 hZc => by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine (tendsto_eLpNorm_of_L2 hZ hZ0 hZc).congr' ?_
    filter_upwards [hZ] with b hb
    simp only [dif_pos hb]
    exact (eLpNorm_congr_ae (hb.coeFn_toLp.sub hZ0.coeFn_toLp)).symm
  have hlim := (conv hX hX0 hXc).inner (𝕜 := ℝ) (conv hY hY0 hYc)
  have e : ∀ {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ),
      inner ℝ (hf.toLp f) (hg.toLp g) = ∫ a, f a * g a ∂μ := fun {f g} hf hg => by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with a h1 h2
    rw [h1, h2]; simp [mul_comm]
  rw [e hX0 hY0] at hlim
  refine hlim.congr' ?_
  filter_upwards [hX, hY] with b h1 h2
  simp only [dif_pos h1, dif_pos h2]
  exact e h1 h2

theorem tendsto_L2_add {X Y : β → α → ℝ} {X0 Y0 : α → ℝ}
    (hX : ∀ᶠ b in l, MemLp (X b) 2 μ) (hY : ∀ᶠ b in l, MemLp (Y b) 2 μ)
    (hX0 : MemLp X0 2 μ) (hY0 : MemLp Y0 2 μ)
    (hXc : Tendsto (fun b => ∫ a, (X b a - X0 a) ^ 2 ∂μ) l (𝓝 0))
    (hYc : Tendsto (fun b => ∫ a, (Y b a - Y0 a) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun b => ∫ a, ((X b a + Y b a) - (X0 a + Y0 a)) ^ 2 ∂μ) l (𝓝 0) := by
  have hup := (hXc.const_mul 2).add (hYc.const_mul 2)
  simp only [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun b => integral_nonneg fun a => sq_nonneg _) ?_
  filter_upwards [hX, hY] with b h1 h2
  have i1 : Integrable (fun a => (X b a - X0 a) ^ 2) μ := (h1.sub hX0).integrable_sq
  have i2 : Integrable (fun a => (Y b a - Y0 a) ^ 2) μ := (h2.sub hY0).integrable_sq
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun a => sq_nonneg _)
    ((i1.const_mul 2).add (i2.const_mul 2)) (Eventually.of_forall fun a => ?_)
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (X b a - X0 a - (Y b a - Y0 a))]

/-- A bounded multiplier preserves `L²` convergence. -/
theorem tendsto_L2_mul_bdd [IsFiniteMeasure μ] {m : β → α → ℝ} {m0 : α → ℝ} {X : β → α → ℝ}
    {X0 : α → ℝ} {B : ℝ} (hm : ∀ᶠ b in l, AEStronglyMeasurable (m b) μ ∧ ∀ a, |m b a| ≤ B)
    (hm0 : AEStronglyMeasurable m0 μ) (hm0b : ∀ a, |m0 a| ≤ B)
    (hX : ∀ᶠ b in l, MemLp (X b) 2 μ) (hX0 : MemLp X0 2 μ)
    (hXc : Tendsto (fun b => ∫ a, (X b a - X0 a) ^ 2 ∂μ) l (𝓝 0))
    (hmc : Tendsto (fun b => ∫ a, (m b a - m0 a) ^ 2 * X0 a ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun b => ∫ a, (m b a * X b a - m0 a * X0 a) ^ 2 ∂μ) l (𝓝 0) := by
  have hup := (hXc.const_mul (2 * B ^ 2)).add (hmc.const_mul 2)
  simp only [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun b => integral_nonneg fun a => sq_nonneg _) ?_
  filter_upwards [hX, hm] with b h1 ⟨h2m, h2⟩
  have i1 : Integrable (fun a => (X b a - X0 a) ^ 2) μ := (h1.sub hX0).integrable_sq
  have i2 : Integrable (fun a => (m b a - m0 a) ^ 2 * X0 a ^ 2) μ := by
    refine hX0.integrable_sq.bdd_mul (c := (2 * B) ^ 2) ((h2m.sub hm0).pow 2)
      (Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    refine pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans ?_) 2
    linarith [h2 a, hm0b a]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (i1.const_mul (2 * B ^ 2)) (i2.const_mul 2)]
  refine integral_mono_of_nonneg (Eventually.of_forall fun a => sq_nonneg _)
    ((i1.const_mul _).add (i2.const_mul 2)) (Eventually.of_forall fun a => ?_)
  have hb : m b a ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h2 a) 2
  have e : m b a * X b a - m0 a * X0 a = m b a * (X b a - X0 a) + (m b a - m0 a) * X0 a := by ring
  show (m b a * X b a - m0 a * X0 a) ^ 2 ≤ 2 * B ^ 2 * (X b a - X0 a) ^ 2 + 2 * ((m b a - m0 a) ^ 2 * X0 a ^ 2)
  rw [e]
  have h3 := sq_nonneg (m b a * (X b a - X0 a) - (m b a - m0 a) * X0 a)
  have h4 : (m b a * (X b a - X0 a)) ^ 2 ≤ B ^ 2 * (X b a - X0 a) ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  nlinarith

/-- A uniformly bounded multiplier that is small in `L¹` is small against an `L¹` function. -/
theorem tendsto_integral_abs_mul_of_L1 [IsFiniteMeasure μ] {m : β → α → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ᶠ b in l, AEStronglyMeasurable (m b) μ ∧ ∀ a, |m b a| ≤ B)
    (hmc : Tendsto (fun b => ∫ a, |m b a| ∂μ) l (𝓝 0)) {h : α → ℝ} (hh : Integrable h μ) :
    Tendsto (fun b => ∫ a, |m b a| * |h a| ∂μ) l (𝓝 0) := by
  -- the tail `∫ (|h| - M)⁺ → 0`
  have htail : Tendsto (fun M : ℝ => ∫ a, max (|h a| - M) 0 ∂μ) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
      (F := fun M a => max (|h a| - M) 0) (f := fun _ => 0) (bound := fun a => |h a|)
      (Eventually.of_forall fun M => (hh.abs.aestronglyMeasurable.sub
        aestronglyMeasurable_const).sup aestronglyMeasurable_const)
      (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with M hM
        refine Eventually.of_forall fun a => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (abs_nonneg _))
      hh.abs (Eventually.of_forall fun a => ?_)
    · simpa using this
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (|h a|)] with M hM
      rw [max_eq_right (by linarith)]
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη2 : 0 < η / (2 * (B + 1)) := by positivity
  obtain ⟨M, hM1, hM0⟩ := ((htail.eventually (gt_mem_nhds hη2)).and
    (eventually_ge_atTop (0 : ℝ))).exists
  have hη3 : 0 < η / (2 * (M + 1)) := by positivity
  filter_upwards [hm, hmc.eventually (gt_mem_nhds hη3)] with b hbmB hb
  obtain ⟨hbm, hbB⟩ := hbmB
  have hbma : AEStronglyMeasurable (fun a => |m b a|) μ := continuous_abs.comp_aestronglyMeasurable hbm
  have hi1 : Integrable (fun a => |m b a| * |h a|) μ :=
    hh.abs.bdd_mul (c := B) hbma (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_abs]; exact hbB a)
  have hi2 : Integrable (fun a => |m b a|) μ :=
    (integrable_const B).mono' hbma (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_abs]; exact hbB a)
  have hi3 : Integrable (fun a => max (|h a| - M) 0) μ :=
    hh.abs.mono' ((hh.abs.aestronglyMeasurable.sub aestronglyMeasurable_const).sup
      aestronglyMeasurable_const) (Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (abs_nonneg _))
  have hle : ∫ a, |m b a| * |h a| ∂μ ≤
      M * (∫ a, |m b a| ∂μ) + B * ∫ a, max (|h a| - M) 0 ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hi2.const_mul M) (hi3.const_mul B)]
    refine integral_mono hi1 ((hi2.const_mul M).add (hi3.const_mul B)) fun a => ?_
    show |m b a| * |h a| ≤ M * |m b a| + B * max (|h a| - M) 0
    have h1 := hbB a
    have h0 := abs_nonneg (m b a)
    rcases le_total (|h a|) M with hle | hle
    · have : |m b a| * |h a| ≤ |m b a| * M := mul_le_mul_of_nonneg_left hle h0
      nlinarith [le_max_right (|h a| - M) 0]
    · rw [max_eq_left (by linarith)]
      nlinarith
  have hpos : 0 ≤ ∫ a, |m b a| * |h a| ∂μ := integral_nonneg fun a => by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
  have hmpos : 0 ≤ ∫ a, |m b a| ∂μ := integral_nonneg fun a => abs_nonneg _
  have hb' : ∫ a, |m b a| ∂μ < η / (2 * (M + 1)) := by
    simpa [Real.dist_eq, abs_of_nonneg hmpos] using hb
  have k1 : M * (∫ a, |m b a| ∂μ) ≤ η / 2 * (M / (M + 1)) := by
    calc M * (∫ a, |m b a| ∂μ) ≤ M * (η / (2 * (M + 1))) :=
          mul_le_mul_of_nonneg_left hb'.le hM0
      _ = η / 2 * (M / (M + 1)) := by field_simp
  have k2 : B * ∫ a, max (|h a| - M) 0 ∂μ ≤ η / 2 * (B / (B + 1)) := by
    calc B * ∫ a, max (|h a| - M) 0 ∂μ ≤ B * (η / (2 * (B + 1))) :=
          mul_le_mul_of_nonneg_left hM1.le hB
      _ = η / 2 * (B / (B + 1)) := by field_simp
  have q1 : M / (M + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have q2 : B / (B + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  nlinarith

end SharpLSI
