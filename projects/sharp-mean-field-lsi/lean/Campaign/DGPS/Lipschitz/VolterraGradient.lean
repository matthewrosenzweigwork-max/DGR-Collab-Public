import DGPS.Lipschitz.WeightedMildSemigroup

/-!
# Volterra gradient estimate and semigroup convergence (LIP008)
-/
open MeasureTheory Set Filter Topology
open scoped Real RealInnerProductSpace NNReal
namespace DGPS.Lipschitz
variable {d : ℕ}

theorem gauss_sing {lam t : ℝ} (hl : 0 < lam) (ht : 0 < t) :
    ∫ s in Ioo 0 t, (t - s) ^ (-(1 : ℝ) / 2) * Real.exp (lam * s) ≤
      Real.exp (lam * t) * Real.sqrt (Real.pi / lam) := by
  have h1 : ∀ s ∈ Ioo 0 t, (t - s) ^ (-(1 : ℝ) / 2) * Real.exp (lam * s) =
      Real.exp (lam * t) * ((t - s) ^ (-(1 : ℝ) / 2) * Real.exp (-(lam * (t - s)))) := by
    intro s hs
    have : Real.exp (lam * s) = Real.exp (lam * t) * Real.exp (-(lam * (t - s))) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  rw [setIntegral_congr_fun measurableSet_Ioo h1, integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hg : IntegrableOn (fun u : ℝ => u ^ (-(1 : ℝ) / 2) * Real.exp (-(lam * u))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -1/2) (b := lam) (by norm_num) (by norm_num) hl
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp
  have hnn : ∀ u ∈ Ioi (0:ℝ), 0 ≤ u ^ (-(1 : ℝ) / 2) * Real.exp (-(lam * u)) :=
    fun u hu => by have : 0 < u := hu; positivity
  have e1 : ∫ s in Ioo 0 t, (t - s) ^ (-(1 : ℝ) / 2) * Real.exp (-(lam * (t - s))) =
      ∫ u in Ioo 0 t, u ^ (-(1 : ℝ) / 2) * Real.exp (-(lam * u)) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le ht.le, ← intervalIntegral.integral_of_le ht.le]
    have := intervalIntegral.integral_comp_sub_left
      (fun u : ℝ => u ^ (-(1 : ℝ) / 2) * Real.exp (-(lam * u))) (a := 0) (b := t) t
    simpa using this
  rw [e1]
  calc _ ≤ ∫ u in Ioi (0:ℝ), u ^ (-(1 : ℝ) / 2) * Real.exp (-(lam * u)) :=
        setIntegral_mono_set hg (ae_restrict_of_forall_mem measurableSet_Ioi hnn)
          (Eventually.of_forall fun u hu => hu.1)
    _ = Real.sqrt (Real.pi / lam) := by
        have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1/2) (r := lam) (by norm_num) hl
        rw [show (1/2 : ℝ) - 1 = -(1:ℝ)/2 by norm_num] at this
        rw [this, Real.Gamma_one_half_eq, Real.sqrt_div Real.pi_pos.le, one_div,
          Real.inv_rpow hl.le, ← Real.sqrt_eq_rpow]
        rw [div_eq_mul_inv, ← one_div, mul_comm]

/-- Weighted contraction: if `‖v - w‖ ≤ V e^{λ s}` on the slab then `Φ v - Φ w` is bounded by
`B0 / √λ · V e^{λ t}`. -/
theorem duhamelOp_sub_weighted {T B0 V lam Mw : ℝ} {b : Torus d → Tangent d}
    {F v w : ℝ × Torus d → Tangent d} (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    (hv : Measurable v) (hw : Measurable w) (hl : 0 < lam) (hV : 0 ≤ V)
    (hwb : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖w p‖ ≤ Mw)
    (hm : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖v p - w p‖ ≤ V * Real.exp (lam * p.1))
    {p : ℝ × Torus d} (hp : p.1 ∈ Ioo 0 T) :
    ‖duhamelOp b F v p - duhamelOp b F w p‖ ≤ B0 / Real.sqrt lam * V * Real.exp (lam * p.1) := by
  obtain ⟨t, x⟩ := p
  have ht : 0 < t := hp.1
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  have h0 : ∀ᵐ q ∂stMeasure d T, ‖v q - w q‖ ≤ V * Real.exp (lam * q.1) ∧ ‖w q‖ ≤ Mw :=
    ae_of_forall_mem fun q hq => ⟨hm q hq, hwb q hq⟩
  have h1 : ∀ᵐ s ∂(volume.restrict (Ioo 0 T)), ∀ᵐ w' ∂haar d,
      ‖v (s, w') - w (s, w')‖ ≤ V * Real.exp (lam * s) ∧ ‖w (s, w')‖ ≤ Mw :=
    Measure.ae_ae_of_ae_prod h0
  have h2 := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hp.2.le) h1
  have h3 : ∀ᵐ s ∂(volume.restrict (Ioo 0 t)), s ∈ Ioo 0 t := ae_restrict_mem measurableSet_Ioo
  have hsl : ∀ (u : ℝ × Torus d → Tangent d), Measurable u → ∀ s : ℝ,
      Measurable fun w' : Torus d => u (s, w') := fun u hu s =>
    hu.comp (measurable_const.prodMk measurable_id)
  have hmeas : ∀ (u : ℝ × Torus d → Tangent d), Measurable u →
      AEStronglyMeasurable (fun s => kerGrad (t - s) (fun w' => ⟪b w', u (s, w')⟫) x)
        (volume.restrict (Ioo 0 t)) := fun u hu =>
    ((stronglyMeasurable_Jint hb hu).comp_measurable
      ((measurable_const (a := ((t, x) : ℝ × Torus d))).prodMk
        (measurable_id : Measurable (id : ℝ → ℝ)))).aestronglyMeasurable
  have hbd : ∀ (u : ℝ × Torus d → Tangent d) (hu : Measurable u) (K : ℝ),
      (∀ s, s ∈ Ioo 0 t → (∀ᵐ w' ∂haar d,
          ‖v (s, w') - w (s, w')‖ ≤ V * Real.exp (lam * s) ∧ ‖w (s, w')‖ ≤ Mw) →
        ∀ᵐ w' ∂haar d, ‖u (s, w')‖ ≤ K) →
      Integrable (fun s => kerGrad (t - s) (fun w' => ⟪b w', u (s, w')⟫) x)
        (volume.restrict (Ioo 0 t)) := fun u hu K hK =>
    (time_integral_bound ht (hmeas u hu) (C := B0 * K)
      ((h2.and h3).mono fun s hs => norm_kerGrad_inner_le (by linarith [hs.2.2]) hb hbB (hsl u hu s)
        (hK s hs.2 hs.1) x)).1
  have hexp : ∀ s ∈ Ioo 0 t, Real.exp (lam * s) ≤ Real.exp (lam * t) := fun s hs =>
    Real.exp_le_exp.2 (by nlinarith [hs.2])
  have hJv := hbd v hv (Mw + V * Real.exp (lam * t)) fun s hs hh => hh.mono fun w' hw' => by
    have := norm_le_norm_add_norm_sub' (v (s, w')) (w (s, w'))
    have h5 := mul_le_mul_of_nonneg_left (hexp s hs) hV
    linarith [hw'.1, hw'.2, norm_sub_rev (v (s, w')) (w (s, w'))]
  have hJw := hbd w hw Mw fun s hs hh => hh.mono fun w' hw' => hw'.2
  set g : ℝ → ℝ := fun s => π ^ (-(1 : ℝ) / 2) * (B0 * V) * ((t - s) ^ (-(1 : ℝ) / 2) *
    Real.exp (lam * s)) with hg
  have hgi : Integrable g (volume.restrict (Ioo 0 t)) := by
    have hI := ((integrableOn_sing ht).mul_const (Real.exp (lam * t))).const_mul
      (π ^ (-(1 : ℝ) / 2) * (B0 * V))
    refine Integrable.mono' hI ?_ ?_
    · refine (Measurable.aestronglyMeasurable ?_)
      simp only [hg]
      fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun s hs => ?_)
      have h6 : 0 ≤ π ^ (-(1 : ℝ) / 2) * (B0 * V) := by positivity
      have h7 : 0 ≤ (t - s) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (by linarith [hs.2]) _
      simp only [hg, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      calc _ ≤ π ^ (-(1 : ℝ) / 2) * (B0 * V) * ((t - s) ^ (-(1 : ℝ) / 2) * Real.exp (lam * t)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hexp s hs) h7) h6
        _ = _ := rfl
  have hfin : ‖∫ s in Ioo 0 t, (kerGrad (t - s) (fun w' => ⟪b w', v (s, w')⟫) x -
      kerGrad (t - s) (fun w' => ⟪b w', w (s, w')⟫) x)‖ ≤ ∫ s in Ioo 0 t, g s := by
    refine norm_integral_le_of_norm_le hgi ?_
    filter_upwards [h2, h3] with s hs1 hs2
    have hτ : 0 < t - s := by linarith [hs2.2]
    have := norm_kerGrad_inner_sub_le hτ hb hbB (hsl v hv s) (hsl w hw s) (M := Mw)
      (m := V * Real.exp (lam * s)) (hs1.mono fun w' hw' => hw'.2)
      (hs1.mono fun w' hw' => hw'.1) x
    refine this.trans (le_of_eq ?_)
    simp only [hg]
    rw [Real.mul_rpow Real.pi_pos.le hτ.le]
    ring
  have hint : ∫ s in Ioo 0 t, g s ≤ B0 / Real.sqrt lam * V * Real.exp (lam * t) := by
    simp only [hg]
    rw [integral_const_mul]
    have h8 := gauss_sing hl ht
    have hpi : π ^ (-(1 : ℝ) / 2) = (Real.sqrt π)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg Real.pi_pos.le]; norm_num
    have h9 : 0 ≤ π ^ (-(1 : ℝ) / 2) * (B0 * V) := by positivity
    refine (mul_le_mul_of_nonneg_left h8 h9).trans (le_of_eq ?_)
    rw [hpi, Real.sqrt_div Real.pi_pos.le]
    have : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
    have : 0 < Real.sqrt lam := Real.sqrt_pos.2 hl
    field_simp
  unfold duhamelOp
  rw [add_sub_add_left_eq_sub, ← integral_sub hJv hJw]
  exact hfin.trans hint


section GlobalPicard

variable {T B0 L : ℝ} {b : Torus d → Tangent d} {F : ℝ × Torus d → Tangent d}

theorem half_le_of_lam (_hB0 : 0 ≤ B0) :
    B0 / Real.sqrt (4 * B0 ^ 2 + 1) ≤ 1 / 2 := by
  have hs : 0 < Real.sqrt (4 * B0 ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
  rw [div_le_iff₀ hs]
  have : 2 * B0 ≤ Real.sqrt (4 * B0 ^ 2 + 1) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  linarith

theorem picard_global_props (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) (hF : Measurable F)
    (hFM : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖F p‖ ≤ L) (hL : 0 ≤ L) :
    ∀ n, Measurable (picard T b F n) ∧
      (∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T →
        ‖picard T b F n p‖ ≤ 2 * L * Real.exp ((4 * B0 ^ 2 + 1) * p.1)) ∧
      (∀ p : ℝ × Torus d, p.1 ∉ Ioo 0 T → picard T b F n p = 0) ∧
      ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T →
        ‖picard T b F (n + 1) p - picard T b F n p‖ ≤
          2 * L * (1 / 2) ^ n * Real.exp ((4 * B0 ^ 2 + 1) * p.1) := by
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  have hl : 0 < 4 * B0 ^ 2 + 1 := by positivity
  have hρ := half_le_of_lam hB0
  set lam := 4 * B0 ^ 2 + 1 with hlam
  have hone : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → 1 ≤ Real.exp (lam * p.1) := fun p hp =>
    Real.one_le_exp (by have := hp.1; positivity)
  have hmeasu : ∀ u : ℝ × Torus d → Tangent d, Measurable u →
      Measurable (Set.indicator {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} (duhamelOp b F u)) :=
    fun u hu => (measurable_duhamelOp hb hF hu).indicator (measurableSet_slab T)
  have hfix : ∀ u : ℝ × Torus d → Tangent d, ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T →
      Set.indicator {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} (duhamelOp b F u) p = duhamelOp b F u p :=
    fun u p hp => Set.indicator_of_mem (show p ∈ {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} from hp) _
  have hout : ∀ u : ℝ × Torus d → Tangent d, ∀ p : ℝ × Torus d, p.1 ∉ Ioo 0 T →
      Set.indicator {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} (duhamelOp b F u) p = 0 :=
    fun u p hp => Set.indicator_of_notMem (show p ∉ {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} from hp) _
  intro n
  induction n with
  | zero =>
    have h0 : Measurable (0 : ℝ × Torus d → Tangent d) := measurable_const
    refine ⟨by simpa [picard] using h0, fun p hp => ?_, fun p _ => by simp [picard], fun p hp => ?_⟩
    · simp only [picard, Pi.zero_apply, norm_zero]; positivity
    · have h1 : picard T b F 1 p = F p := by
        simp only [picard]; rw [hfix _ p hp, duhamelOp_zero]
      rw [h1]
      simp only [picard, Pi.zero_apply, sub_zero, pow_zero, mul_one]
      refine (hFM p hp).trans ?_
      have := hone p hp
      nlinarith
  | succ n ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have hmeas : Measurable (picard T b F (n + 1)) := hmeasu _ h1
    have hbnd : ∀ k, (∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T →
        ‖picard T b F k p‖ ≤ 2 * L * Real.exp (lam * p.1)) →
        Measurable (picard T b F k) → ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T →
        ‖picard T b F (k + 1) p‖ ≤ 2 * L * Real.exp (lam * p.1) := by
      intro k hk hkm p hp
      have hw := duhamelOp_sub_weighted (T := T) (F := F) (V := 2 * L) (lam := lam) (Mw := 0) hb hbB
        hkm (measurable_const : Measurable (0 : ℝ × Torus d → Tangent d)) hl (by positivity)
        (fun q _ => by simp) (fun q hq => by simpa using hk q hq) hp
      have hw0 : ‖duhamelOp b F (picard T b F k) p - F p‖ ≤
          B0 / Real.sqrt lam * (2 * L) * Real.exp (lam * p.1) := by
        rw [← duhamelOp_zero b F p]; exact hw
      have hw' : ‖duhamelOp b F (picard T b F k) p - F p‖ ≤ L * Real.exp (lam * p.1) := by
        refine hw0.trans ?_
        have : 0 ≤ 2 * L * Real.exp (lam * p.1) := by positivity
        calc B0 / Real.sqrt lam * (2 * L) * Real.exp (lam * p.1)
            = (B0 / Real.sqrt lam) * (2 * L * Real.exp (lam * p.1)) := by ring
          _ ≤ (1 / 2) * (2 * L * Real.exp (lam * p.1)) := mul_le_mul_of_nonneg_right hρ this
          _ = _ := by ring
      simp only [picard]
      rw [hfix _ p hp]
      calc ‖duhamelOp b F (picard T b F k) p‖
          ≤ ‖F p‖ + ‖duhamelOp b F (picard T b F k) p - F p‖ := norm_le_norm_add_norm_sub' _ _
        _ ≤ L + L * Real.exp (lam * p.1) := add_le_add (hFM p hp) hw'
        _ ≤ _ := by nlinarith [hone p hp]
    refine ⟨hmeas, hbnd n h2 h1, fun p hp => hout _ p hp, fun p hp => ?_⟩
    have hTb : ∀ q : ℝ × Torus d, q.1 ∈ Ioo 0 T →
        ‖picard T b F n q‖ ≤ 2 * L * Real.exp (lam * T) := fun q hq =>
      (h2 q hq).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hq.2.le hl.le)) (by positivity))
    have hw := duhamelOp_sub_weighted (T := T) (F := F) (V := 2 * L * (1 / 2) ^ n) (lam := lam)
      (Mw := 2 * L * Real.exp (lam * T)) hb hbB hmeas h1 hl (by positivity) hTb
      (fun q hq => h4 q hq) hp
    simp only [picard]
    rw [hfix _ p hp, hfix _ p hp]
    refine hw.trans ?_
    have : 0 ≤ 2 * L * (1 / 2) ^ n * Real.exp (lam * p.1) := by positivity
    calc B0 / Real.sqrt lam * (2 * L * (1 / 2) ^ n) * Real.exp (lam * p.1)
        = (B0 / Real.sqrt lam) * (2 * L * (1 / 2) ^ n * Real.exp (lam * p.1)) := by ring
      _ ≤ (1 / 2) * (2 * L * (1 / 2) ^ n * Real.exp (lam * p.1)) :=
          mul_le_mul_of_nonneg_right hρ this
      _ = _ := by ring

theorem exists_global_fixed_point (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0) (hF : Measurable F)
    (hFM : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖F p‖ ≤ L) (hL : 0 ≤ L) :
    ∃ v : ℝ × Torus d → Tangent d, Measurable v ∧
      (∀ p, ‖v p‖ ≤ 2 * L * Real.exp ((4 * B0 ^ 2 + 1) * T)) ∧
      ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b F v p = v p := by
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  have hl : 0 < 4 * B0 ^ 2 + 1 := by positivity
  have hρ := half_le_of_lam hB0
  set lam := 4 * B0 ^ 2 + 1 with hlam
  have hP := picard_global_props (T := T) hb hbB hF hFM hL
  set K := 2 * L * Real.exp (lam * T) with hK
  have hK0 : 0 ≤ K := by positivity
  have hwt : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → Real.exp (lam * p.1) ≤ Real.exp (lam * T) :=
    fun p hp => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hp.2.le hl.le)
  have hu : ∀ p n, dist (picard T b F n p) (picard T b F (n + 1) p) ≤ K * (1 / 2) ^ n := by
    intro p n
    rw [dist_comm, dist_eq_norm]
    by_cases hp : p.1 ∈ Ioo 0 T
    · refine ((hP n).2.2.2 p hp).trans ?_
      calc 2 * L * (1 / 2) ^ n * Real.exp (lam * p.1) ≤ 2 * L * (1 / 2) ^ n * Real.exp (lam * T) :=
            mul_le_mul_of_nonneg_left (hwt p hp) (by positivity)
        _ = _ := by rw [hK]; ring
    · have h1 : picard T b F (n + 1) p = 0 := (picard_global_props (T := T) hb hbB hF hFM hL
        (n + 1)).2.2.1 p hp
      rw [h1, (hP n).2.2.1 p hp]; simp; positivity
  have hc : ∀ p, ∃ a, Tendsto (fun n => picard T b F n p) atTop (𝓝 a) := fun p =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric (1 / 2 : ℝ) K (by norm_num) (hu p))
  choose v hv using hc
  have hvm : Measurable v :=
    measurable_of_tendsto_metrizable (fun n => (hP n).1) (tendsto_pi_nhds.2 hv)
  have hun : ∀ p n, ‖picard T b F n p‖ ≤ K := by
    intro p n
    by_cases hp : p.1 ∈ Ioo 0 T
    · exact ((hP n).2.1 p hp).trans (by
        rw [hK]; exact mul_le_mul_of_nonneg_left (hwt p hp) (by positivity))
    · rw [(hP n).2.2.1 p hp]; simpa using hK0
  have hvb : ∀ p, ‖v p‖ ≤ K := fun p =>
    le_of_tendsto (hv p).norm (Eventually.of_forall fun n => hun p n)
  refine ⟨v, hvm, hvb, fun p hp => ?_⟩
  -- weighted tail bound
  have hd : ∀ q : ℝ × Torus d, q.1 ∈ Ioo 0 T → ∀ n,
      ‖v q - picard T b F n q‖ ≤ 4 * L * (1 / 2) ^ n * Real.exp (lam * q.1) := by
    intro q hq n
    have hu' : ∀ n, dist (picard T b F n q) (picard T b F (n + 1) q) ≤
        2 * L * Real.exp (lam * q.1) * (1 / 2) ^ n := fun n => by
      rw [dist_comm, dist_eq_norm]
      refine ((hP n).2.2.2 q hq).trans (le_of_eq (by ring))
    have := dist_le_of_le_geometric_of_tendsto (1 / 2 : ℝ) (2 * L * Real.exp (lam * q.1))
      (by norm_num) hu' (hv q) n
    rw [dist_eq_norm, norm_sub_rev] at this
    refine this.trans (le_of_eq ?_)
    ring
  have hbound : ∀ n, ‖duhamelOp b F v p - v p‖ ≤ 6 * L * (1 / 2) ^ n * Real.exp (lam * p.1) := by
    intro n
    have hpic : duhamelOp b F (picard T b F n) p = picard T b F (n + 1) p := by
      simp only [picard]
      rw [Set.indicator_of_mem (show p ∈ {p : ℝ × Torus d | p.1 ∈ Ioo 0 T} from hp)]
    have h1 := duhamelOp_sub_weighted (T := T) (F := F) (V := 4 * L * (1 / 2) ^ n) (lam := lam)
      (Mw := K) hb hbB hvm (hP n).1 hl (by positivity) (fun q _ => hun q n)
      (fun q hq => hd q hq n) hp
    have h2 : B0 / Real.sqrt lam * (4 * L * (1 / 2) ^ n) * Real.exp (lam * p.1) ≤
        2 * L * (1 / 2) ^ n * Real.exp (lam * p.1) := by
      have : 0 ≤ 4 * L * (1 / 2) ^ n * Real.exp (lam * p.1) := by positivity
      calc B0 / Real.sqrt lam * (4 * L * (1 / 2) ^ n) * Real.exp (lam * p.1)
          = (B0 / Real.sqrt lam) * (4 * L * (1 / 2) ^ n * Real.exp (lam * p.1)) := by ring
        _ ≤ (1 / 2) * (4 * L * (1 / 2) ^ n * Real.exp (lam * p.1)) :=
            mul_le_mul_of_nonneg_right hρ this
        _ = _ := by ring
    have h3 : ‖duhamelOp b F (picard T b F n) p - v p‖ ≤
        2 * L * (1 / 2) ^ n * Real.exp (lam * p.1) := by
      rw [hpic, norm_sub_rev]
      refine (hd p hp (n + 1)).trans (le_of_eq ?_)
      rw [pow_succ]; ring
    calc ‖duhamelOp b F v p - v p‖
        ≤ ‖duhamelOp b F v p - duhamelOp b F (picard T b F n) p‖ +
          ‖duhamelOp b F (picard T b F n) p - v p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 6 * L * (1 / 2) ^ n * Real.exp (lam * p.1) := by
        have hpos : 0 ≤ L * (1 / 2) ^ n * Real.exp (lam * p.1) := by positivity
        nlinarith [hpos]
  have hlim : Tendsto (fun n : ℕ => 6 * L * (1 / 2) ^ n * Real.exp (lam * p.1)) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul
      (6 * L)
    simpa using this.mul_const (Real.exp (lam * p.1))
  have := le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end GlobalPicard

open DGPS.Analysis DGPS.Analysis.CompactResolvent DGPS.Lipschitz.ParabolicChainRule

/-- Global-in-time version of `mild_step`: on every slab `(0,T)` the Duhamel fixed point exists
(weighted Picard) and its slices are the gradients of `C¹` representatives of `S t f`. -/
theorem mild_global {T B0 L c C : ℝ} (hd : 0 < d) (_hT : 0 < T) (hL : 0 ≤ L)
    {w : Torus d → ℝ} {b : Torus d → Tangent d} (hW : WeightedGenerator.WData d w b c C)
    (hint : ∫ x, w x ∂haar d = 1) (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    {Lg : Hw d w →ₗ.[ℝ] Hw d w} {S : ℝ≥0 → Hw d w →L[ℝ] Hw d w}
    (hS : IsWeightedSemigroup w Lg S) {f : Torus d → ℝ} (hf : TorusLipschitzWith L f) :
    ∃ v : ℝ × Torus d → Tangent d, Measurable v ∧
      (∀ p, ‖v p‖ ≤ 2 * L * Real.exp ((4 * B0 ^ 2 + 1) * T)) ∧
      (∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b (heatGrad f) v p = v p) ∧
      ∀ t ∈ Ioo 0 T, IsWeakGradient (duhamelPotential b f v t) (fun x => v (t, x)) ∧
        Continuous (fun x => v (t, x)) ∧
        ∃ ũ : Torus d → ℝ, IsC1Periodic ũ ∧ ũ =ᵐ[haar d] duhamelPotential b f v t ∧
          (∀ x j, coordPartial j ũ x = v (t, x) j) ∧
          ∀ F : Hw d w, ((F : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] f →
            ũ =ᵐ[wMeasure d w] ((S t.toNNReal F : Hw d w) : Torus d → ℝ) := by
  have hfc := continuous_of_torusLipschitz hL hf
  have hF : Measurable (heatGrad f) := measurable_heatGrad hfc.measurable
  have hFM : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖heatGrad f p‖ ≤ L := fun p hp =>
    norm_heatGrad_le hL hf hp.1
  obtain ⟨v, hvm, hvb, hvf⟩ := exists_global_fixed_point hb hbB hF hFM hL
  have hgrad : ∀ t ∈ Ioo 0 T, IsWeakGradient (duhamelPotential b f v t) (fun x => v (t, x)) :=
    fun t ht => weakGradient_duhamelPotential hb hbB hfc hvm hvb hvf ht
  have hfm : MemLp f 2 (haar d) :=
    hfc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  obtain ⟨e, lam, G, -, -, -, -, -, hG, hE, -, -⟩ :=
    WeightedSpectrum.weighted_eigenbasis_and_growth hd hW.meas hW.pos hwb hint
  obtain ⟨-, -, -, huniq⟩ := SemigroupEigen.lip007d1_semigroup_eigen Lg S hS.selfAdjoint
    (fun f hf => (hS.mem_domain_iff f).mp hf) hS.form hS.zero hS.add hS.symm hS.cont hS.deriv
    e lam G hG hE
  refine ⟨v, hvm, hvb, hvf, fun t ht => ⟨hgrad t ht, ?_⟩⟩
  have hcv := continuous_duhamel_gradient hb hbB hfc hvm hvb hvf ht
  refine ⟨hcv, ?_⟩
  obtain ⟨ũ, h1, h2, h3⟩ := exists_isC1Periodic_of_continuous_weakGradient (hgrad t ht) hcv
    (memLp_top_duhamelPotential hb hbB hfc hvm hvb ht.1)
  refine ⟨ũ, h1, h2, h3, fun F hF => ?_⟩
  have hmemU : MemLp (duhamelPotential b f v t) 2 (wMeasure d w) :=
    (memLp_wMeasure_iff hW.pos hwb).mpr (hgrad t ht).memLp
  set U : Hw d w := hmemU.toLp _ with hU
  have hUae : (U : Torus d → ℝ) =ᵐ[wMeasure d w] duhamelPotential b f v t :=
    MemLp.coeFn_toLp hmemU
  have hcoef : ∀ j, ∫ x, duhamelPotential b f v t x * ((e j : Hw d w) : Torus d → ℝ) x
        ∂wMeasure d w =
      Real.exp (-lam j * t) * ∫ x, f x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w := by
    intro j
    have h := duhamel_eigen_coeff_ode hW hb hbB hfm hvm hvb hgrad (e j) (hG j) (hE j) t ht
    rw [integral_wMeasure hW.meas hW.pos hwb, integral_wMeasure hW.meas hW.pos hwb]
    simpa only [smul_eq_mul, mul_comm (w _), mul_assoc] using h
  have hUF : U = S t.toNNReal F := by
    refine huniq F U t.toNNReal fun j => ?_
    rw [Real.coe_toNNReal _ ht.1.le, inner_Hw_eq_integral, inner_Hw_eq_integral]
    have h1 : ∫ x, (U : Torus d → ℝ) x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w =
        ∫ x, duhamelPotential b f v t x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w := by
      refine integral_congr_ae ?_
      filter_upwards [hUae] with x hx
      rw [hx]
    have h2 : ∫ x, (F : Torus d → ℝ) x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w =
        ∫ x, f x * ((e j : Hw d w) : Torus d → ℝ) x ∂wMeasure d w := by
      refine integral_congr_ae ?_
      filter_upwards [hF] with x hx
      rw [hx]
    rw [h1, h2]
    exact hcoef j
  have : (U : Torus d → ℝ) =ᵐ[wMeasure d w] ((S t.toNNReal F : Hw d w) : Torus d → ℝ) := by
    rw [hUF]
  exact (ae_eq_wMeasure h2).trans (hUae.symm.trans this)

section Weighted

variable {T B0 L : ℝ} {b : Torus d → Tangent d} {F : ℝ × Torus d → Tangent d}

/-- One Volterra step with an exponential weight. -/
theorem gradient_step_weighted (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    (hFM : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖F p‖ ≤ L) {v : ℝ × Torus d → Tangent d}
    (hvm : Measurable v) (hvf : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b F v p = v p)
    {N mu : ℝ} (hmu : 0 < mu) (hN : 0 ≤ N)
    (hvN : ∀ q : ℝ × Torus d, q.1 ∈ Ioo 0 T → ‖v q‖ ≤ N * Real.exp (mu * q.1))
    {p : ℝ × Torus d} (hp : p.1 ∈ Ioo 0 T) :
    ‖v p‖ ≤ L + B0 / Real.sqrt mu * N * Real.exp (mu * p.1) := by
  have h := duhamelOp_sub_weighted (T := T) (F := F) (V := N) (lam := mu) (Mw := 0) hb hbB hvm
    (measurable_const : Measurable (0 : ℝ × Torus d → Tangent d)) hmu hN (fun q _ => by simp)
    (fun q hq => by simpa using hvN q hq) hp
  have h0 : ‖duhamelOp b F v p - F p‖ ≤ B0 / Real.sqrt mu * N * Real.exp (mu * p.1) := by
    rw [← duhamelOp_zero b F p]; exact h
  rw [hvf p hp] at h0
  calc ‖v p‖ ≤ ‖F p‖ + ‖v p - F p‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ _ := add_le_add (hFM p hp) h0

theorem gradient_bound_weighted (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    (hFM : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → ‖F p‖ ≤ L) (hL : 0 ≤ L)
    {v : ℝ × Torus d → Tangent d} (hvm : Measurable v) {V : ℝ} (hvb : ∀ p, ‖v p‖ ≤ V)
    (hvf : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 T → duhamelOp b F v p = v p)
    {p : ℝ × Torus d} (hp : p.1 ∈ Ioo 0 T) :
    ‖v p‖ ≤ 2 * L * Real.exp (4 * B0 ^ 2 * p.1) := by
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  have hV : 0 ≤ V := (norm_nonneg _).trans (hvb p)
  have hε : ∀ ε : ℝ, 0 < ε → ‖v p‖ ≤ 2 * L * Real.exp ((4 * B0 ^ 2 + ε) * p.1) := by
    intro ε hε
    have hmu : 0 < 4 * B0 ^ 2 + ε := by positivity
    set mu := 4 * B0 ^ 2 + ε with hmudef
    have hρ : B0 / Real.sqrt mu ≤ 1 / 2 := by
      have hs : 0 < Real.sqrt mu := Real.sqrt_pos.2 hmu
      rw [div_le_iff₀ hs]
      have : 2 * B0 ≤ Real.sqrt mu := Real.le_sqrt_of_sq_le (by nlinarith)
      linarith
    have hone : ∀ q : ℝ × Torus d, q.1 ∈ Ioo 0 T → 1 ≤ Real.exp (mu * q.1) := fun q hq =>
      Real.one_le_exp (by have := hq.1; positivity)
    have key : ∀ k : ℕ, ∀ q : ℝ × Torus d, q.1 ∈ Ioo 0 T →
        ‖v q‖ ≤ (2 * L + V * (1 / 2) ^ k) * Real.exp (mu * q.1) := by
      intro k
      induction k with
      | zero =>
        intro q hq
        have := hone q hq
        simp only [pow_zero, mul_one]
        calc ‖v q‖ ≤ V := hvb q
          _ ≤ V * Real.exp (mu * q.1) := by nlinarith
          _ ≤ _ := by nlinarith [Real.exp_pos (mu * q.1)]
      | succ k ih =>
        intro q hq
        have hN : 0 ≤ 2 * L + V * (1 / 2) ^ k := by positivity
        have h1 := gradient_step_weighted (T := T) hb hbB hFM hvm hvf hmu hN ih hq
        have h2 : B0 / Real.sqrt mu * (2 * L + V * (1 / 2) ^ k) * Real.exp (mu * q.1) ≤
            (1 / 2) * (2 * L + V * (1 / 2) ^ k) * Real.exp (mu * q.1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hρ hN) (Real.exp_pos _).le
        have h3 := hone q hq
        refine h1.trans ?_
        have : (1 / 2) * (2 * L + V * (1 / 2) ^ k) * Real.exp (mu * q.1) + L ≤
            (2 * L + V * (1 / 2) ^ (k + 1)) * Real.exp (mu * q.1) := by
          rw [pow_succ]
          nlinarith [mul_nonneg hL (sub_nonneg.2 h3)]
        linarith
    have hlim : Filter.Tendsto (fun k : ℕ => (2 * L + V * (1 / 2) ^ k) * Real.exp (mu * p.1))
        Filter.atTop (𝓝 ((2 * L + V * 0) * Real.exp (mu * p.1))) :=
      (((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul V).const_add (2 * L)).mul_const _
    have := ge_of_tendsto' hlim fun k => key k p hp
    simpa using this
  have hlim : Filter.Tendsto (fun ε : ℝ => 2 * L * Real.exp ((4 * B0 ^ 2 + ε) * p.1))
      (𝓝[>] 0) (𝓝 (2 * L * Real.exp (4 * B0 ^ 2 * p.1))) := by
    have : Continuous fun ε : ℝ => 2 * L * Real.exp ((4 * B0 ^ 2 + ε) * p.1) := by fun_prop
    have h2 := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using h2
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun ε hε' => hε ε hε')

end Weighted

section LipschitzBound

/-- **Gradient estimate (weak constant).** For every `t > 0`, the semigroup applied to a
`L`-Lipschitz `f` has a `C¹` representative that is `2 L exp(4 B0² t)`-Lipschitz. -/
theorem semigroup_lipschitz_bound {B0 L c C : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    {w : Torus d → ℝ} {b : Torus d → Tangent d} (hW : WeightedGenerator.WData d w b c C)
    (hint : ∫ x, w x ∂haar d = 1) (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    {Lg : Hw d w →ₗ.[ℝ] Hw d w} {S : ℝ≥0 → Hw d w →L[ℝ] Hw d w}
    (hS : IsWeightedSemigroup w Lg S) {f : Torus d → ℝ} (hf : TorusLipschitzWith L f)
    {t : ℝ} (ht : 0 < t) (F : Hw d w) (hF : ((F : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] f) :
    ∃ ũ : Torus d → ℝ, IsC1Periodic ũ ∧
      ũ =ᵐ[wMeasure d w] ((S t.toNNReal F : Hw d w) : Torus d → ℝ) ∧
      TorusLipschitzWith (2 * L * Real.exp (4 * B0 ^ 2 * t)) ũ := by
  have hT : 0 < t + 1 := by linarith
  obtain ⟨v, hvm, hvb, hvf, hv⟩ := mild_global hd hT hL hW hint hb hbB hS hf
  have htm : t ∈ Ioo 0 (t + 1) := ⟨ht, by linarith⟩
  obtain ⟨hwg, -, ũ, h1, h2, -, h4⟩ := hv t htm
  have hFM : ∀ p : ℝ × Torus d, p.1 ∈ Ioo 0 (t + 1) → ‖heatGrad f p‖ ≤ L := fun p hp =>
    norm_heatGrad_le hL hf hp.1
  refine ⟨ũ, h1, h4 F hF, ?_⟩
  refine torusLipschitz_of_weakGradient_bound h1.continuous_torus
    (hwg.congr_ae h2.symm Filter.EventuallyEq.rfl) fun x => ?_
  exact gradient_bound_weighted hb hbB hFM hL hvm hvb hvf (p := (t, x)) htm

end LipschitzBound

section Approx

open Metric

theorem exists_ball_lower {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] {r : ℝ}
    (hr : 0 < r) : ∃ m : ENNReal, 0 < m ∧ ∀ x : X, m ≤ μ (ball x r) := by
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_univ (X := X))
    (half_pos hr)
  have htne : t.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    have := hcov (mem_univ x)
    simp only [mem_iUnion] at this
    obtain ⟨c, hc, -⟩ := this
    exact ⟨c, hc⟩
  obtain ⟨c0, hc0, hmin⟩ := ht.exists_minimalFor (fun c => μ (ball c (r / 2))) t htne
  refine ⟨μ (ball c0 (r / 2)), (isOpen_ball).measure_pos μ ⟨c0, mem_ball_self (half_pos hr)⟩, fun x => ?_⟩
  have := hcov (mem_univ x)
  simp only [mem_iUnion] at this
  obtain ⟨c, hc, hxc⟩ := this
  have h1 : μ (ball c0 (r / 2)) ≤ μ (ball c (r / 2)) :=
    (le_total (μ (ball c (r / 2))) (μ (ball c0 (r / 2)))).elim (fun h => hmin hc h) id
  refine h1.trans (measure_mono fun y hy => ?_)
  rw [mem_ball] at hy hxc ⊢
  calc dist y x ≤ dist y c + dist c x := dist_triangle _ _ _
    _ < r / 2 + r / 2 := by rw [dist_comm c x]; exact add_lt_add hy hxc
    _ = r := by ring

theorem uniform_of_lipschitz_L2 {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ h : X → ℝ, (∀ x y, |h x - h y| ≤ K * dist x y) →
      ∫ x, h x ^ 2 ∂μ ≤ η → ∀ x, |h x| ≤ ε := by
  set r : ℝ := ε / (2 * (K + 1)) with hr
  have hr0 : 0 < r := by positivity
  obtain ⟨m, hm0, hm⟩ := exists_ball_lower μ hr0
  have hmt : m ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ (ball (Classical.arbitrary X) r)) (hm _)
  set m' : ℝ := m.toReal with hm'
  have hm'0 : 0 < m' := ENNReal.toReal_pos hm0.ne' hmt
  refine ⟨ε ^ 2 / 8 * m', by positivity, fun h hl hint x0 => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hhc : Continuous h := by
    have : LipschitzWith (Real.toNNReal K) h := LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.coe_toNNReal _ hK]; exact hl x y
    exact this.continuous
  have hKr : K * r ≤ ε / 2 := by
    rw [hr]
    have : K * (ε / (2 * (K + 1))) = ε / 2 * (K / (K + 1)) := by field_simp
    rw [this]
    have : K / (K + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  have hsub : ∀ y ∈ ball x0 r, ε / 2 ≤ |h y| := by
    intro y hy
    rw [mem_ball] at hy
    have h1 := hl x0 y
    have h2 : K * dist x0 y ≤ K * r := mul_le_mul_of_nonneg_left (by rw [dist_comm]; exact hy.le) hK
    have h3 : |h x0| ≤ |h y| + |h x0 - h y| := by
      calc |h x0| = |h y + (h x0 - h y)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have hint2 : Integrable (fun x => h x ^ 2) μ :=
    (hhc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlow : ε ^ 2 / 4 * m' ≤ ∫ x, h x ^ 2 ∂μ := by
    calc ε ^ 2 / 4 * m' ≤ ε ^ 2 / 4 * (μ (ball x0 r)).toReal := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact ENNReal.toReal_mono (measure_ne_top μ _) (hm x0)
      _ = ∫ x in ball x0 r, ε ^ 2 / 4 ∂μ := by
          rw [setIntegral_const]; simp [mul_comm, Measure.real]
      _ ≤ ∫ x in ball x0 r, h x ^ 2 ∂μ := by
          refine setIntegral_mono_on (integrable_const _).integrableOn hint2.integrableOn
            isOpen_ball.measurableSet fun y hy => ?_
          have := hsub y hy
          have h0 : 0 ≤ ε / 2 := by positivity
          calc ε ^ 2 / 4 = (ε / 2) ^ 2 := by ring
            _ ≤ |h y| ^ 2 := pow_le_pow_left₀ h0 this 2
            _ = h y ^ 2 := sq_abs _
      _ ≤ ∫ x, h x ^ 2 ∂μ :=
          setIntegral_le_integral hint2 (Eventually.of_forall fun x => sq_nonneg _)
  nlinarith [mul_pos (by positivity : (0:ℝ) < ε ^ 2) hm'0]

theorem exists_lipschitz_approx {X : Type*} [MetricSpace X] [CompactSpace X] {f : X → ℝ}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℝ, (∃ K : ℝ, 0 ≤ K ∧ ∀ x y, |g x - g y| ≤ K * dist x y) ∧ ∀ x, |f x - g x| ≤ ε := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x, |f x| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_univ (X := X)).exists_bound_of_continuousOn hf.continuousOn
    exact ⟨M, fun x => by simpa using hM x (mem_univ x)⟩
  have hM0 : ∀ x, 0 ≤ M := fun x => (abs_nonneg _).trans (hM x)
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hf) (ε / 2) (half_pos hε)
  by_cases hX : Nonempty X
  swap
  · exact ⟨fun _ => 0, ⟨0, le_refl _, fun x => (hX ⟨x⟩).elim⟩, fun x => (hX ⟨x⟩).elim⟩
  obtain ⟨x₀⟩ := hX
  have : Nonempty X := ⟨x₀⟩
  have hM00 : 0 ≤ M := hM0 x₀
  set n : ℝ := 2 * M / δ with hn
  have hn0 : 0 ≤ n := by positivity
  have hbdd : ∀ x, BddBelow (range fun y => f y + n * dist x y) := fun x =>
    ⟨-M, by rintro _ ⟨y, rfl⟩; have := (abs_le.1 (hM y)).1; have := mul_nonneg hn0 (dist_nonneg (x := x) (y := y)); linarith⟩
  set g : X → ℝ := fun x => ⨅ y, (f y + n * dist x y) with hg
  have hgle : ∀ x, g x ≤ f x := fun x => by
    have := ciInf_le (hbdd x) x
    simpa using this
  have hglow : ∀ x y, g x ≤ f y + n * dist x y := fun x y => ciInf_le (hbdd x) y
  refine ⟨g, ⟨n, hn0, fun x x' => ?_⟩, fun x => ?_⟩
  · have h1 : ∀ x x', g x - g x' ≤ n * dist x x' := by
      intro x x'
      have : g x - n * dist x x' ≤ g x' := by
        refine le_ciInf fun y => ?_
        have h2 := hglow x y
        have h3 : dist x y ≤ dist x x' + dist x' y := dist_triangle _ _ _
        have : n * dist x y ≤ n * dist x x' + n * dist x' y := by nlinarith
        linarith
      linarith
    rw [abs_le]
    refine ⟨?_, h1 x x'⟩
    have := h1 x' x
    rw [dist_comm] at this
    linarith
  · have hlow : f x - ε / 2 ≤ g x := by
      refine le_ciInf fun y => ?_
      by_cases hy : dist x y < δ
      · have := hδf (a := x) (b := y) hy
        rw [Real.dist_eq] at this
        have := (abs_lt.1 this).2
        have := mul_nonneg hn0 (dist_nonneg (x := x) (y := y))
        linarith [(abs_lt.1 ‹|f x - f y| < ε / 2›).1, (abs_lt.1 ‹|f x - f y| < ε / 2›).2]
      · push Not at hy
        have h1 : n * δ ≤ n * dist x y := mul_le_mul_of_nonneg_left hy hn0
        have h2 : n * δ = 2 * M := by rw [hn]; field_simp
        have h3 := (abs_le.1 (hM y)).1
        have h4 := (abs_le.1 (hM x)).2
        linarith
    rw [abs_le]
    constructor <;> linarith [hgle x]

end Approx

section Uniqueness

open DGPS.Analysis DGPS.Analysis.CompactResolvent

/-- A weighted semigroup is determined by its generator data: two semigroups satisfying
`IsWeightedSemigroup` for the same weight coincide. -/
theorem semigroup_unique {c C : ℝ} (hd : 0 < d) {w : Torus d → ℝ} {b : Torus d → Tangent d}
    (hW : WeightedGenerator.WData d w b c C) (hint : ∫ x, w x ∂haar d = 1)
    {Lg1 Lg2 : Hw d w →ₗ.[ℝ] Hw d w} {S1 S2 : ℝ≥0 → Hw d w →L[ℝ] Hw d w}
    (h1 : IsWeightedSemigroup w Lg1 S1) (h2 : IsWeightedSemigroup w Lg2 S2) (t : ℝ≥0)
    (F : Hw d w) : S1 t F = S2 t F := by
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  obtain ⟨e, lam, G, -, -, -, -, -, hG, hE, -, -⟩ :=
    WeightedSpectrum.weighted_eigenbasis_and_growth hd hW.meas hW.pos hwb hint
  obtain ⟨-, -, hc1, -⟩ := SemigroupEigen.lip007d1_semigroup_eigen Lg1 S1 h1.selfAdjoint
    (fun f hf => (h1.mem_domain_iff f).mp hf) h1.form h1.zero h1.add h1.symm h1.cont h1.deriv
    e lam G hG hE
  obtain ⟨-, -, hc2, hu2⟩ := SemigroupEigen.lip007d1_semigroup_eigen Lg2 S2 h2.selfAdjoint
    (fun f hf => (h2.mem_domain_iff f).mp hf) h2.form h2.zero h2.add h2.symm h2.cont h2.deriv
    e lam G hG hE
  exact hu2 F (S1 t F) t fun j => by rw [hc1 F t j]

/-- Sup-norm contraction of the Gibbs semigroup (Markov property, transferred by uniqueness). -/
theorem gibbs_semigroup_sup_contraction {Φ : Torus d → ℝ} {LΦ : ℝ} (hd : 0 < d) (hL : 0 ≤ LΦ)
    (hΦ : TorusLipschitzWith LΦ Φ) {b : Torus d → Tangent d}
    (hb : IsWeakGradient (fun x => Real.log (WeightedGenerator.gibbsW Φ x)) b)
    {Lg : Hw d (WeightedGenerator.gibbsW Φ) →ₗ.[ℝ] Hw d (WeightedGenerator.gibbsW Φ)}
    {S : ℝ≥0 → Hw d (WeightedGenerator.gibbsW Φ) →L[ℝ] Hw d (WeightedGenerator.gibbsW Φ)}
    (hS : IsWeightedSemigroup (WeightedGenerator.gibbsW Φ) Lg S) (t : ℝ≥0)
    (F : Hw d (WeightedGenerator.gibbsW Φ)) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ᵐ x ∂wMeasure d (WeightedGenerator.gibbsW Φ), ‖((F : Hw d _) : Torus d → ℝ) x‖ ≤ M) :
    ∀ᵐ x ∂wMeasure d (WeightedGenerator.gibbsW Φ), ‖((S t F : Hw d _) : Torus d → ℝ) x‖ ≤ M := by
  obtain ⟨-, -, -, -, Lg0, S0, hsa, -, hdomiff, -, hform, hS0, hadd, hsymm, hcont, hder, -, -,
    hLp⟩ := WeightedGenerator.closed_weighted_form_and_generator_domain hL hΦ hb
  have hSS0 : IsWeightedSemigroup (WeightedGenerator.gibbsW Φ) Lg0 S0 :=
    ⟨hsa, hdomiff, hform, hS0, hadd, hsymm, hcont, hder⟩
  obtain ⟨c, C, hW⟩ := WeightedGenerator.gibbs_wdata hL hΦ
  have heq := semigroup_unique hd hW (integral_gibbsW_eq_one hΦ) hS hSS0 t F
  have h1 := hLp t ⊤ le_top F
  have h2 : eLpNorm (F : Torus d → ℝ) ⊤ (wMeasure d (WeightedGenerator.gibbsW Φ)) ≤
      ENNReal.ofReal M := by
    rw [eLpNorm_exponent_top]
    · exact eLpNormEssSup_le_of_ae_bound (C := M) hF
    · exact Lp.aestronglyMeasurable F
  have h3 := ae_le_eLpNormEssSup (f := ((S0 t F : Hw d _) : Torus d → ℝ))
    (μ := wMeasure d (WeightedGenerator.gibbsW Φ))
  rw [heq]
  filter_upwards [h3] with x hx
  have h4 : eLpNormEssSup ((S0 t F : Hw d _) : Torus d → ℝ)
      (wMeasure d (WeightedGenerator.gibbsW Φ)) ≤ ENNReal.ofReal M := by
    rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
    exact h1.trans h2
  have h5 := hx.trans h4
  rw [← ofReal_norm] at h5
  exact (ENNReal.ofReal_le_ofReal_iff hM).1 h5

end Uniqueness

section UniformLipschitz

open DGPS.Analysis DGPS.Analysis.CompactResolvent

theorem torusLipschitz_dist {K : ℝ} (hK : 0 ≤ K) {h : Torus d → ℝ} (hh : TorusLipschitzWith K h) :
    ∀ x y, |h x - h y| ≤ K * Real.sqrt d * dist x y := by
  intro x y
  calc |h x - h y| ≤ K * torusDist x y := hh x y
    _ ≤ K * (Real.sqrt d * dist x y) :=
        mul_le_mul_of_nonneg_left (torusDist_comparison x y).2 hK
    _ = K * Real.sqrt d * dist x y := by ring

theorem integral_sq_eq_norm_sq {w : Torus d → ℝ} (g : Hw d w) {h : Torus d → ℝ}
    (hg : (g : Torus d → ℝ) =ᵐ[wMeasure d w] h) :
    ∫ x, h x ^ 2 ∂wMeasure d w = ‖g‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_Hw_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hg] with x hx
  rw [hx, sq]

/-- **Uniform convergence for Lipschitz data.** -/
theorem lipschitz_uniform_convergence {B0 L c C : ℝ} (hd : 0 < d) (hL : 0 ≤ L)
    {w : Torus d → ℝ} {b : Torus d → Tangent d} (hW : WeightedGenerator.WData d w b c C)
    (hint : ∫ x, w x ∂haar d = 1) (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    {Lg : Hw d w →ₗ.[ℝ] Hw d w} {S : ℝ≥0 → Hw d w →L[ℝ] Hw d w}
    (hS : IsWeightedSemigroup w Lg S) {f : Torus d → ℝ} (hf : TorusLipschitzWith L f)
    (F : Hw d w) (hF : ((F : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∃ ũ : Torus d → ℝ, Continuous ũ ∧
      ũ =ᵐ[wMeasure d w] ((S t.toNNReal F : Hw d w) : Torus d → ℝ) ∧ ∀ x, |ũ x - f x| ≤ ε := by
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  have hfin : IsFiniteMeasure (wMeasure d w) := WeightedGenerator.isFiniteMeasure_wMeasure hwb
  have hopen : (wMeasure d w).IsOpenPosMeasure :=
    (haar_ac_wMeasure hW.pos hwb).isOpenPosMeasure
  set K1 : ℝ := 2 * L * Real.exp (4 * B0 ^ 2 * 1) with hK1
  have hK10 : 0 ≤ K1 := by positivity
  set K : ℝ := (K1 + L) * Real.sqrt d with hK
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨η, hη, hηp⟩ := uniform_of_lipschitz_L2 (wMeasure d w) hK0 hε
  have hcont := (hS.cont F).continuousAt (x := 0)
  obtain ⟨δ0, hδ0, hδ0p⟩ := Metric.continuousAt_iff.mp hcont (Real.sqrt η) (Real.sqrt_pos.2 hη)
  refine ⟨min δ0 1, lt_min hδ0 one_pos, fun t ht htd => ?_⟩
  have htδ : t < δ0 := lt_of_lt_of_le htd (min_le_left _ _)
  have ht1 : t < 1 := lt_of_lt_of_le htd (min_le_right _ _)
  obtain ⟨ũ, h1, h2, h3⟩ := semigroup_lipschitz_bound hd hL hW hint hb hbB hS hf ht F hF
  refine ⟨ũ, h1.continuous_torus, h2, ?_⟩
  have hB0 : 0 ≤ B0 := (norm_nonneg _).trans (hbB 0)
  have hKt : 2 * L * Real.exp (4 * B0 ^ 2 * t) ≤ K1 := by
    rw [hK1]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    nlinarith [sq_nonneg B0]
  have hlip : TorusLipschitzWith (K1 + L) (fun x => ũ x - f x) := by
    intro x y
    have a := h3 x y
    have b' := hf x y
    have : |(ũ x - f x) - (ũ y - f y)| ≤ |ũ x - ũ y| + |f x - f y| := by
      calc |(ũ x - f x) - (ũ y - f y)| = |(ũ x - ũ y) - (f x - f y)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    have h4 : (2 * L * Real.exp (4 * B0 ^ 2 * t)) * torusDist x y ≤ K1 * torusDist x y :=
      mul_le_mul_of_nonneg_right hKt (by
        have := (torusDist_comparison x y).1
        exact (dist_nonneg).trans this)
    nlinarith
  have hl2 := torusLipschitz_dist (by positivity) hlip
  have hnorm : ‖S t.toNNReal F - F‖ < Real.sqrt η := by
    have := hδ0p (x := t.toNNReal) (by
      rw [NNReal.dist_eq]
      simp only [NNReal.coe_zero, sub_zero, NNReal.abs_eq]
      rw [Real.coe_toNNReal _ ht.le]; exact htδ)
    rw [dist_eq_norm, hS.zero] at this
    exact this
  have hint2 : ∫ x, (ũ x - f x) ^ 2 ∂wMeasure d w ≤ η := by
    have hg : ((S t.toNNReal F - F : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w]
        fun x => ũ x - f x := by
      filter_upwards [Lp.coeFn_sub (S t.toNNReal F) F, h2, hF] with x a b' c'
      rw [a]; simp only [Pi.sub_apply]; rw [← b', c']
    rw [integral_sq_eq_norm_sq _ hg]
    have h0 := norm_nonneg (S t.toNNReal F - F)
    calc ‖S t.toNNReal F - F‖ ^ 2 ≤ (Real.sqrt η) ^ 2 := by gcongr
      _ = η := Real.sq_sqrt hη.le
  exact hηp (fun x => ũ x - f x) (by simpa [hK, mul_assoc] using hl2) hint2

end UniformLipschitz

section HOne

open DGPS.Analysis DGPS.Analysis.CompactResolvent
open scoped LinearPMap InnerProductSpace

theorem lam_mul_exp_le {l t : ℝ} (_hl : 0 ≤ l) (ht : 0 < t) : l * Real.exp (-l * t) ≤ 1 / t := by
  rw [le_div_iff₀ ht]
  have h1 : l * t ≤ Real.exp (l * t) := by linarith [Real.add_one_le_exp (l * t)]
  have h2 : Real.exp (-l * t) * Real.exp (l * t) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : 0 ≤ Real.exp (-l * t) := (Real.exp_pos _).le
  calc l * Real.exp (-l * t) * t = Real.exp (-l * t) * (l * t) := by ring
    _ ≤ Real.exp (-l * t) * Real.exp (l * t) := mul_le_mul_of_nonneg_left h1 h3
    _ = 1 := h2

/-- For `t > 0` the semigroup maps `L²(w m)` into the domain of the generator. -/
theorem semigroup_mem_domain {c C : ℝ} (hd : 0 < d) {w : Torus d → ℝ} {b : Torus d → Tangent d}
    (hW : WeightedGenerator.WData d w b c C) (hint : ∫ x, w x ∂haar d = 1)
    {Lg : Hw d w →ₗ.[ℝ] Hw d w} {S : ℝ≥0 → Hw d w →L[ℝ] Hw d w}
    (hS : IsWeightedSemigroup w Lg S) (t : ℝ≥0) (ht : 0 < t) (F : Hw d w) :
    S t F ∈ Lg.domain := by
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  obtain ⟨e, lam, G, -, hl0, -, hmono, -, hG, hE, -, -⟩ :=
    WeightedSpectrum.weighted_eigenbasis_and_growth hd hW.meas hW.pos hwb hint
  obtain ⟨-, -, hc1, -⟩ := SemigroupEigen.lip007d1_semigroup_eigen Lg S hS.selfAdjoint
    (fun f hf => (hS.mem_domain_iff f).mp hf) hS.form hS.zero hS.add hS.symm hS.cont hS.deriv
    e lam G hG hE
  have hlam : ∀ j, 0 ≤ lam j := fun j => hl0 ▸ hmono (Nat.zero_le j)
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  set cf : ℕ → ℝ := fun j => -(lam j * (Real.exp (-lam j * (t : ℝ)) * ⟪F, e j⟫_ℝ)) with hcf
  have hsum : Summable fun j => cf j ^ 2 := by
    have h0 : Summable fun j => (1 / (t : ℝ)) ^ 2 * ⟪e j, F⟫_ℝ ^ 2 :=
      (coeff_sq_summable e F).mul_left _
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_) h0
    have hb := lam_mul_exp_le (hlam j) htr
    have hb0 : 0 ≤ lam j * Real.exp (-lam j * t) := mul_nonneg (hlam j) (Real.exp_pos _).le
    have h5 : cf j ^ 2 = (lam j * Real.exp (-lam j * t)) ^ 2 * ⟪e j, F⟫_ℝ ^ 2 := by
      rw [hcf]; simp only [neg_sq]; rw [real_inner_comm]; ring
    rw [h5]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb0 hb 2) (sq_nonneg _)
  set z : Hw d w := ofSq e cf hsum with hz
  have hK : ∀ (x : Lg.domain) (j : ℕ), ⟪e j, Lg x⟫_ℝ = -lam j * ⟪e j, (x : Hw d w)⟫_ℝ := by
    intro x j
    obtain ⟨Gx, Hx, hGx⟩ := (hS.mem_domain_iff x).mp x.2
    have h1 := hS.form x x.2 Gx hGx.grad (e j) (G j) (hG j)
    have h2 := hE j x Gx hGx.grad
    rw [weightedForm_comm] at h1
    rw [h2] at h1
    have h3 := real_inner_comm (Lg x : Hw d w) (e j)
    have : Lg ⟨(x : Hw d w), x.2⟩ = Lg x := rfl
    rw [this] at h1
    linarith
  have hmem : S t F ∈ Lg†.domain := by
    refine LinearPMap.mem_adjoint_domain_of_exists _ ⟨z, fun x => ?_⟩
    have a1 := hasSum_coeff_mul e z (x : Hw d w)
    have a2 := hasSum_coeff_mul e (S t F) (Lg x)
    refine a1.unique ?_
    convert a2 using 1
    funext j
    rw [hK x j, coeff_ofSq, real_inner_comm (S t F) (e j), hc1 F t j]
    simp only [hcf]
    ring
  have hAdj : Lg† = Lg := hS.selfAdjoint
  rw [← hAdj]; exact hmem

end HOne


section HOneConv

open DGPS.Analysis DGPS.Analysis.CompactResolvent
open scoped LinearPMap InnerProductSpace

/-- **Strong `H¹(μ)` convergence.** For `F ∈ L²(w m)` with `L²` weak gradient `Y`, `S t F`
has a weak gradient `Yt` for `t > 0` and `‖S t F - F‖² + E_w(Y - Yt) → 0` as `t → 0`. -/
theorem semigroup_H1_convergence {c C : ℝ} (hd : 0 < d) {w : Torus d → ℝ} {b : Torus d → Tangent d}
    (hW : WeightedGenerator.WData d w b c C) (hint : ∫ x, w x ∂haar d = 1)
    {Lg : Hw d w →ₗ.[ℝ] Hw d w} {S : ℝ≥0 → Hw d w →L[ℝ] Hw d w}
    (hS : IsWeightedSemigroup w Lg S) (F : Hw d w) {Y : Torus d → Tangent d}
    (hY : IsWeakGradient ((F : Hw d w) : Torus d → ℝ) Y) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∃ Yt : Torus d → Tangent d,
      IsWeakGradient ((S t.toNNReal F : Hw d w) : Torus d → ℝ) Yt ∧
      ‖S t.toNNReal F - F‖ ^ 2 + weightedForm w (fun x => Y x - Yt x) (fun x => Y x - Yt x)
        ≤ ε := by
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  obtain ⟨e, lam, G, -, hl0, -, hmono, -, hG, hE, hSum, -⟩ :=
    WeightedSpectrum.weighted_eigenbasis_and_growth hd hW.meas hW.pos hwb hint
  obtain ⟨-, -, hc1, -⟩ := SemigroupEigen.lip007d1_semigroup_eigen Lg S hS.selfAdjoint
    (fun f hf => (hS.mem_domain_iff f).mp hf) hS.form hS.zero hS.add hS.symm hS.cont hS.deriv
    e lam G hG hE
  have hlam : ∀ j, 0 ≤ lam j := fun j => hl0 ▸ hmono (Nat.zero_le j)
  have core : ∀ t : ℝ≥0, 0 < t → ∃ Yt : Torus d → Tangent d,
      IsWeakGradient ((S t F : Hw d w) : Torus d → ℝ) Yt ∧
      HasSum (fun j => lam j * ((1 - Real.exp (-lam j * (t : ℝ))) * ⟪F, e j⟫_ℝ) ^ 2)
        (weightedForm w (fun x => Y x - Yt x) (fun x => Y x - Yt x)) := by
    intro t ht
    have hm := semigroup_mem_domain hd hW hint hS t ht F
    obtain ⟨Yt, Ht, hess⟩ := (hS.mem_domain_iff _).mp hm
    refine ⟨Yt, hess.grad, ?_⟩
    have hgrad : IsWeakGradient (((F - S t F : Hw d w)) : Torus d → ℝ) (fun x => Y x - Yt x) := by
      have h1 := hY.add (hess.grad.smul (-1))
      refine h1.congr_ae ?_ ?_
      · filter_upwards [ae_eq_haar hW.pos hwb (Lp.coeFn_sub F (S t F))] with x hx
        rw [hx]; simp [sub_eq_add_neg]
      · exact Eventually.of_forall fun x => by simp [sub_eq_add_neg]
    have h2 := hSum (F - S t F) _ hgrad
    have hfun : (fun j => lam j * ((1 - Real.exp (-lam j * (t : ℝ))) * ⟪F, e j⟫_ℝ) ^ 2) =
        fun j => lam j * ⟪e j, F - S t F⟫_ℝ ^ 2 := by
      funext j
      rw [inner_sub_right, real_inner_comm (S t F) (e j), hc1 F t j, real_inner_comm F (e j)]
      ring
    rw [hfun]; exact h2
  have hsm : Summable fun j => lam j * ⟪e j, F⟫_ℝ ^ 2 := (hSum F Y hY).summable
  have hlim : Tendsto (fun t : ℝ≥0 =>
      ∑' j, lam j * ((1 - Real.exp (-lam j * (t : ℝ))) * ⟪F, e j⟫_ℝ) ^ 2) (𝓝 0) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 (0 : ℝ≥0))
      (f := fun (t : ℝ≥0) j => lam j * ((1 - Real.exp (-lam j * (t : ℝ))) * ⟪F, e j⟫_ℝ) ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun j => lam j * ⟪e j, F⟫_ℝ ^ 2) hsm ?_ ?_
    · simpa using this
    · intro j
      have hc : Continuous fun t : ℝ≥0 =>
          lam j * ((1 - Real.exp (-lam j * (t : ℝ))) * ⟪F, e j⟫_ℝ) ^ 2 := by
        fun_prop
      simpa using hc.tendsto 0
    · refine Eventually.of_forall fun t j => ?_
      have h0 : 0 ≤ lam j * ((1 - Real.exp (-lam j * (t : ℝ))) * ⟪F, e j⟫_ℝ) ^ 2 :=
        mul_nonneg (hlam j) (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0, real_inner_comm F (e j)]
      refine mul_le_mul_of_nonneg_left ?_ (hlam j)
      have hx1 : Real.exp (-lam j * (t : ℝ)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [hlam j, t.2]
      have hx0 := Real.exp_pos (-lam j * (t : ℝ))
      have hsq : (1 - Real.exp (-lam j * (t : ℝ))) ^ 2 ≤ 1 := by nlinarith
      calc ((1 - Real.exp (-lam j * (t : ℝ))) * ⟪F, e j⟫_ℝ) ^ 2
          = (1 - Real.exp (-lam j * (t : ℝ))) ^ 2 * ⟪F, e j⟫_ℝ ^ 2 := by ring
        _ ≤ 1 * ⟪F, e j⟫_ℝ ^ 2 := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
        _ = ⟪F, e j⟫_ℝ ^ 2 := one_mul _
  have hL2 : Tendsto (fun t : ℝ≥0 => ‖S t F - F‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have h := (hS.cont F).tendsto 0
    rw [hS.zero] at h
    have h3 : Tendsto (fun t : ℝ≥0 => S t F - F) (𝓝 0) (𝓝 0) := by
      simpa using h.sub_const F
    simpa using h3.norm.pow 2
  have hev := Filter.Tendsto.eventually_lt_const (u := ε) (by simpa using hε) (hL2.add hlim)
  obtain ⟨δ, hδ, hp⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun t ht htd => ?_⟩
  have htp : (0 : ℝ≥0) < t.toNNReal := Real.toNNReal_pos.mpr ht
  obtain ⟨Yt, hYt, hsum⟩ := core t.toNNReal htp
  refine ⟨Yt, hYt, ?_⟩
  have hd0 : dist t.toNNReal 0 < δ := by
    rw [NNReal.dist_eq]
    simp only [NNReal.coe_zero, sub_zero, NNReal.abs_eq]
    rw [Real.coe_toNNReal _ ht.le]; exact htd
  have h5 := hp hd0
  rw [← hsum.tsum_eq]
  exact h5.le

end HOneConv


section ContinuousData

open DGPS.Analysis DGPS.Analysis.CompactResolvent

theorem le_of_ae_le_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] {h : X → ℝ} (hh : Continuous h) {ε : ℝ}
    (ha : ∀ᵐ x ∂μ, |h x| ≤ ε) : ∀ x, |h x| ≤ ε := by
  intro x
  by_contra hx
  have hx := not_le.1 hx
  have hU : IsOpen {y | ε < |h y|} := isOpen_lt continuous_const (continuous_abs.comp hh)
  have h0 : μ {y | ε < |h y|} = 0 := by
    rw [ae_iff] at ha
    simpa [not_le] using ha
  have hx' : x ∈ {y | ε < |h y|} := hx
  rw [(hU.measure_eq_zero_iff μ).1 h0] at hx'
  exact hx'

/-- A function uniformly approximable a.e. by continuous functions has a continuous version. -/
theorem exists_continuous_rep {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] {φ : X → ℝ}
    (h : ∀ η : ℝ, 0 < η → ∃ v : X → ℝ, Continuous v ∧ ∀ᵐ x ∂μ, |φ x - v x| ≤ η) :
    ∃ u : X → ℝ, Continuous u ∧ φ =ᵐ[μ] u := by
  choose v hvc hva using fun n : ℕ => h (1 / ((n : ℝ) + 1)) (by positivity)
  have hpair : ∀ n m x, |v n x - v m x| ≤ 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
    intro n m
    refine le_of_ae_le_continuous μ (h := fun x => v n x - v m x) ((hvc n).sub (hvc m)) ?_
    filter_upwards [hva n, hva m] with x h1 h2
    have : v n x - v m x = (φ x - v m x) - (φ x - v n x) := by ring
    rw [this]
    calc _ ≤ |φ x - v m x| + |φ x - v n x| := abs_sub _ _
      _ ≤ _ := by linarith
  have h4 : ∀ a : ℝ, Tendsto (fun n : ℕ => a / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    intro a
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul a
    simpa [div_eq_mul_inv] using this
  have hcs : ∀ x, CauchySeq fun n => v n x := by
    intro x
    refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => 2 / ((N : ℝ) + 1)) (fun n m N hn hm => ?_)
      (h4 2)
    rw [Real.dist_eq]
    refine (hpair n m x).trans ?_
    have a1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by have := Nat.cast_le (α := ℝ).2 hn; linarith)
    have a2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by have := Nat.cast_le (α := ℝ).2 hm; linarith)
    have e : 2 / ((N : ℝ) + 1) = 1 / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) := by ring
    linarith
  choose u hu using fun x => cauchySeq_tendsto_of_complete (hcs x)
  have hbd : ∀ n x, |v n x - u x| ≤ 2 / ((n : ℝ) + 1) := by
    intro n x
    have ht : Tendsto (fun m => |v n x - v m x|) atTop (𝓝 |v n x - u x|) :=
      (continuous_abs.tendsto _).comp ((tendsto_const_nhds).sub (hu x))
    refine le_of_tendsto ht (Filter.eventually_atTop.2 ⟨n, fun m hm => ?_⟩)
    refine (hpair n m x).trans ?_
    have a2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by have := Nat.cast_le (α := ℝ).2 hm; linarith)
    have e : 2 / ((n : ℝ) + 1) = 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by ring
    linarith
  have hunif : TendstoUniformly v u atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    refine lt_of_le_of_lt (hbd n x) ?_
    rw [div_lt_iff₀ (by positivity)]
    have h6 : 2 / ε < (n : ℝ) + 1 := by
      have := Nat.cast_le (α := ℝ).2 hn
      linarith
    rw [div_lt_iff₀ hε] at h6
    linarith
  refine ⟨u, hunif.continuous (Filter.Eventually.of_forall hvc).frequently, ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, |φ x - v n x| ≤ 1 / ((n : ℝ) + 1) := ae_all_iff.2 hva
  filter_upwards [hall] with x hx
  have h3 : ∀ n : ℕ, |φ x - u x| ≤ 3 / ((n : ℝ) + 1) := fun n => by
    calc |φ x - u x| ≤ |φ x - v n x| + |v n x - u x| := by
          have : φ x - u x = (φ x - v n x) + (v n x - u x) := by ring
          rw [this]; exact abs_add_le _ _
      _ ≤ 1 / ((n : ℝ) + 1) + 2 / ((n : ℝ) + 1) := add_le_add (hx n) (hbd n x)
      _ = 3 / ((n : ℝ) + 1) := by ring
  have h5 : |φ x - u x| ≤ 0 := ge_of_tendsto' (h4 3) h3
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h5)

/-- **Uniform convergence for continuous data**, given the sup-norm contraction. -/
theorem continuous_uniform_convergence {B0 c C : ℝ} (hd : 0 < d)
    {w : Torus d → ℝ} {b : Torus d → Tangent d} (hW : WeightedGenerator.WData d w b c C)
    (hint : ∫ x, w x ∂haar d = 1) (hb : Measurable b) (hbB : ∀ x, ‖b x‖ ≤ B0)
    {Lg : Hw d w →ₗ.[ℝ] Hw d w} {S : ℝ≥0 → Hw d w →L[ℝ] Hw d w}
    (hS : IsWeightedSemigroup w Lg S)
    (hsup : ∀ (t : ℝ≥0) (F : Hw d w) {M : ℝ}, 0 ≤ M →
      (∀ᵐ x ∂wMeasure d w, ‖((F : Hw d w) : Torus d → ℝ) x‖ ≤ M) →
      ∀ᵐ x ∂wMeasure d w, ‖((S t F : Hw d w) : Torus d → ℝ) x‖ ≤ M)
    {f : Torus d → ℝ} (hf : Continuous f) (F : Hw d w)
    (hF : ((F : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∃ u : Torus d → ℝ, Continuous u ∧
      u =ᵐ[wMeasure d w] ((S t.toNNReal F : Hw d w) : Torus d → ℝ) ∧ ∀ x, |u x - f x| ≤ ε := by
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  have hfin : IsFiniteMeasure (wMeasure d w) := WeightedGenerator.isFiniteMeasure_wMeasure hwb
  have hopen : (wMeasure d w).IsOpenPosMeasure :=
    (haar_ac_wMeasure hW.pos hwb).isOpenPosMeasure
  have approx : ∀ η : ℝ, 0 < η → ∃ (g : Torus d → ℝ) (K : ℝ) (G : Hw d w), 0 ≤ K ∧
      TorusLipschitzWith K g ∧ (∀ x, |f x - g x| ≤ η) ∧
      ((G : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] g := by
    intro η hη
    obtain ⟨g, ⟨K, hK0, hK⟩, hfg⟩ := exists_lipschitz_approx hf hη
    have hgc : Continuous g := by
      have : LipschitzWith ⟨K, hK0⟩ g := LipschitzWith.of_dist_le_mul fun x y => by
        rw [Real.dist_eq]; exact hK x y
      exact this.continuous
    obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hgc.continuousOn
    have hmem : MemLp g 2 (wMeasure d w) :=
      MemLp.of_bound hgc.aestronglyMeasurable M
        (Eventually.of_forall fun x => by simpa using hM x (mem_univ x))
    refine ⟨g, K, hmem.toLp g, hK0, fun x y => ?_, hfg, hmem.coeFn_toLp⟩
    calc |g x - g y| ≤ K * dist x y := hK x y
      _ ≤ K * torusDist x y := mul_le_mul_of_nonneg_left (torusDist_comparison x y).1 hK0
  have supclose : ∀ {g : Torus d → ℝ} {G : Hw d w} {η : ℝ}, 0 < η → (∀ x, |f x - g x| ≤ η) →
      ((G : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] g → ∀ t : ℝ≥0,
      ∀ᵐ x ∂wMeasure d w, |((S t F : Hw d w) : Torus d → ℝ) x - ((S t G : Hw d w) : Torus d → ℝ) x|
        ≤ η := by
    intro g G η hη hfg hG t
    have h1 : ∀ᵐ x ∂wMeasure d w, ‖(((F - G : Hw d w)) : Torus d → ℝ) x‖ ≤ η := by
      filter_upwards [Lp.coeFn_sub F G, hF, hG] with x a b' c'
      rw [a]; simp only [Pi.sub_apply, Real.norm_eq_abs]
      rw [b', c']; exact hfg x
    have h2 := hsup t (F - G) hη.le h1
    filter_upwards [h2, Lp.coeFn_sub (S t F) (S t G)] with x a b'
    rw [map_sub, b'] at a
    simpa [Real.norm_eq_abs] using a
  have repA : ∀ t : ℝ, 0 < t → ∃ u : Torus d → ℝ, Continuous u ∧
      u =ᵐ[wMeasure d w] ((S t.toNNReal F : Hw d w) : Torus d → ℝ) := by
    intro t ht
    obtain ⟨u, hu, hue⟩ := exists_continuous_rep (wMeasure d w)
      (φ := ((S t.toNNReal F : Hw d w) : Torus d → ℝ)) (fun η hη => by
        obtain ⟨g, K, G, hK0, hgL, hfg, hG⟩ := approx η hη
        obtain ⟨ũ, h1, h2, -⟩ := semigroup_lipschitz_bound hd hK0 hW hint hb hbB hS hgL ht G hG
        refine ⟨ũ, h1.continuous_torus, ?_⟩
        filter_upwards [supclose hη hfg hG t.toNNReal, h2] with x a b'
        rw [b']; exact a)
    exact ⟨u, hu, hue.symm⟩
  obtain ⟨g, K, G, hK0, hgL, hfg, hG⟩ := approx (ε / 3) (by positivity)
  obtain ⟨δ, hδ, hp⟩ := lipschitz_uniform_convergence hd hK0 hW hint hb hbB hS hgL G hG
    (ε := ε / 3) (by positivity)
  refine ⟨δ, hδ, fun t ht htd => ?_⟩
  obtain ⟨u, hu, hue⟩ := repA t ht
  obtain ⟨ũ, hũc, hũe, hũb⟩ := hp t ht htd
  refine ⟨u, hu, hue, ?_⟩
  have := le_of_ae_le_continuous (wMeasure d w) (h := fun x => u x - f x) (hu.sub hf) (ε := ε) (by
    filter_upwards [hue, hũe, supclose (by positivity : 0 < ε / 3) hfg hG t.toNNReal] with x a b' c'
    have e1 := hũb x
    have e2 := hfg x
    have c2 : |u x - ũ x| ≤ ε / 3 := by rw [a, b']; exact c'
    have e2' : |g x - f x| ≤ ε / 3 := by rw [abs_sub_comm]; exact e2
    have : u x - f x = (u x - ũ x) + (ũ x - g x) + (g x - f x) := by ring
    rw [this]
    have h3 := abs_add_le ((u x - ũ x) + (ũ x - g x)) (g x - f x)
    have h4 := abs_add_le (u x - ũ x) (ũ x - g x)
    linarith)
  exact fun x => this x

end ContinuousData


section Final

open DGPS.Analysis DGPS.Analysis.CompactResolvent

/-- A continuous function on the torus defines an element of `Hw d w`. -/
theorem exists_Hw_rep {c C : ℝ} {w : Torus d → ℝ} {b : Torus d → Tangent d}
    (hW : WeightedGenerator.WData d w b c C) {f : Torus d → ℝ} (hf : Continuous f) :
    ∃ F : Hw d w, ((F : Hw d w) : Torus d → ℝ) =ᵐ[wMeasure d w] f := by
  have hwb : ∀ᵐ x ∂haar d, c ≤ w x ∧ w x ≤ C := Eventually.of_forall hW.bound
  have hfin : IsFiniteMeasure (wMeasure d w) := WeightedGenerator.isFiniteMeasure_wMeasure hwb
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hf.continuousOn
  have hmem : MemLp f 2 (wMeasure d w) :=
    MemLp.of_bound hf.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa using hM x (mem_univ x))
  exact ⟨hmem.toLp f, hmem.coeFn_toLp⟩

/-- **Volterra gradient estimate and semigroup convergence** (weak-constant form, PARTIAL:
the Lipschitz constant is `2 L exp(4 B0² t)` instead of `2 L exp(B0² t)`). -/
theorem volterra_gradient_estimate_and_semigroup_convergence {Φ : Torus d → ℝ} {LΦ : ℝ}
    (hd : 0 < d) (hL : 0 ≤ LΦ) (hΦ : TorusLipschitzWith LΦ Φ) {b : Torus d → Tangent d}
    (hb : IsWeakGradient (fun x => Real.log (WeightedGenerator.gibbsW Φ x)) b) :
    ∃ (Lg : Hw d (WeightedGenerator.gibbsW Φ) →ₗ.[ℝ] Hw d (WeightedGenerator.gibbsW Φ))
      (S : ℝ≥0 → Hw d (WeightedGenerator.gibbsW Φ) →L[ℝ] Hw d (WeightedGenerator.gibbsW Φ)),
      IsWeightedSemigroup (WeightedGenerator.gibbsW Φ) Lg S ∧
      (∀ L : ℝ, 0 ≤ L → ∀ f : Torus d → ℝ, TorusLipschitzWith L f →
        ∀ t : ℝ, 0 < t → ∀ F : Hw d (WeightedGenerator.gibbsW Φ),
          ((F : Hw d (WeightedGenerator.gibbsW Φ)) : Torus d → ℝ) =ᵐ[
            wMeasure d (WeightedGenerator.gibbsW Φ)] f →
          ∃ ũ : Torus d → ℝ, IsC1Periodic ũ ∧
            ũ =ᵐ[wMeasure d (WeightedGenerator.gibbsW Φ)]
              ((S t.toNNReal F : Hw d (WeightedGenerator.gibbsW Φ)) : Torus d → ℝ) ∧
            TorusLipschitzWith (2 * L * Real.exp (4 * LΦ ^ 2 * t)) ũ) ∧
      (∀ f : Torus d → ℝ, Continuous f →
        ∃ F : Hw d (WeightedGenerator.gibbsW Φ),
          ((F : Hw d (WeightedGenerator.gibbsW Φ)) : Torus d → ℝ) =ᵐ[
            wMeasure d (WeightedGenerator.gibbsW Φ)] f ∧
          ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
            ∃ u : Torus d → ℝ, Continuous u ∧
              u =ᵐ[wMeasure d (WeightedGenerator.gibbsW Φ)]
                ((S t.toNNReal F : Hw d (WeightedGenerator.gibbsW Φ)) : Torus d → ℝ) ∧
              ∀ x, |u x - f x| ≤ ε) ∧
      (∀ (F : Hw d (WeightedGenerator.gibbsW Φ)) (Y : Torus d → Tangent d),
        IsWeakGradient ((F : Hw d (WeightedGenerator.gibbsW Φ)) : Torus d → ℝ) Y →
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
          ∃ Yt : Torus d → Tangent d,
            IsWeakGradient ((S t.toNNReal F : Hw d (WeightedGenerator.gibbsW Φ)) :
              Torus d → ℝ) Yt ∧
            ‖S t.toNNReal F - F‖ ^ 2 + weightedForm (WeightedGenerator.gibbsW Φ)
              (fun x => Y x - Yt x) (fun x => Y x - Yt x) ≤ ε) := by
  obtain ⟨Lg, S, hS, b', hbm, hbB, hbae, -⟩ :=
    bounded_drift_mild_solution_with_continuous_gradient hd hL hΦ hb
  obtain ⟨c, C, hW0⟩ := WeightedGenerator.gibbs_wdata hL hΦ
  have hW := WeightedGenerator.wdata_congr_b hW0
    ((WeightedGenerator.log_gibbs_grad hL hΦ hb).symm.trans hbae.symm)
  have hint := integral_gibbsW_eq_one hΦ
  refine ⟨Lg, S, hS, ?_, ?_, ?_⟩
  · intro L hL0 f hf t ht F hF
    obtain ⟨ũ, h1, h2, h3⟩ := semigroup_lipschitz_bound hd hL0 hW hint hbm hbB hS hf ht F hF
    exact ⟨ũ, h1, h2, h3⟩
  · intro f hf
    obtain ⟨F, hF⟩ := exists_Hw_rep hW hf
    exact ⟨F, hF, fun ε hε => continuous_uniform_convergence hd hW hint hbm hbB hS
      (fun t F' => gibbs_semigroup_sup_contraction hd hL hΦ hb hS t F') hf F hF hε⟩
  · intro F Y hY ε hε
    exact semigroup_H1_convergence hd hW hint hS F hY hε

end Final

end DGPS.Lipschitz
