import SharpSymmetricLSI.Paper.AppAPos7
import SharpSymmetricLSI.Infra.HeatTorus8

/-!
# Positivity (8): Grönwall and the limit `ε → 0`

* `gronwall_zero`: `0 ≤ E ≤ M`, `E(t) ≤ c ∫₀ᵗ E` on `[0,T]` force `E = 0`.
* `tendsto_integral_abs_heatT_sub`: `∫|e^{εₘΔ}f - f| → 0` along `εₘ = 1/(m+1)`.
* `tendsto_integral_comp_of_L1`: `∫ Φ(gₘ) → ∫ Φ(g)` for `gₘ → g` in `L¹`, uniformly bounded,
  `Φ` Lipschitz on the range.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal Nat

namespace SharpLSI

theorem setIntegral_pow_Ioc {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∫ u in Ioc 0 t, u ^ n = t ^ (n + 1) / (n + 1) := by
  rw [← intervalIntegral.integral_of_le ht, integral_pow]
  simp

/-- **Grönwall** with zero data. -/
theorem gronwall_zero {E : ℝ → ℝ} {c M T : ℝ} (hc : 0 ≤ c) (hEm : Measurable E)
    (hE0 : ∀ t ∈ Icc 0 T, 0 ≤ E t) (hEM : ∀ t ∈ Icc 0 T, E t ≤ M)
    (hE : ∀ t ∈ Icc 0 T, E t ≤ c * ∫ u in Ioc 0 t, E u) : ∀ t ∈ Icc 0 T, E t = 0 := by
  have hM : ∀ t ∈ Icc 0 T, 0 ≤ M := fun t ht => (hE0 t ht).trans (hEM t ht)
  have hn : ∀ n : ℕ, ∀ t ∈ Icc 0 T, E t ≤ M * (c * t) ^ n / n ! := by
    intro n
    induction n with
    | zero => intro t ht; simpa using hEM t ht
    | succ n ih =>
      intro t ht
      have hM0 := hM t ht
      haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
        isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
      have hEi : IntegrableOn E (Ioc 0 t) := by
        refine (integrable_const M).mono' hEm.aestronglyMeasurable
          ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_))
        have hu : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.trans ht.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (hE0 u hu)]; exact hEM u hu
      have hgi : IntegrableOn (fun u => M * (c * u) ^ n / n !) (Ioc 0 t) :=
        (by fun_prop : Continuous fun u : ℝ => M * (c * u) ^ n / n !).integrableOn_Ioc
      calc E t ≤ c * ∫ u in Ioc 0 t, E u := hE t ht
        _ ≤ c * ∫ u in Ioc 0 t, M * (c * u) ^ n / n ! := by
            exact mul_le_mul_of_nonneg_left (setIntegral_mono_on hEi hgi measurableSet_Ioc fun u hu =>
              ih u ⟨hu.1.le, hu.2.trans ht.2⟩) hc
        _ = M * (c * t) ^ (n + 1) / (n + 1)! := by
            have e : (fun u : ℝ => M * (c * u) ^ n / n !) = fun u => (M * c ^ n / n !) * u ^ n := by
              funext u; rw [mul_pow]; ring
            rw [e, integral_const_mul, setIntegral_pow_Ioc ht.1, Nat.factorial_succ]
            push_cast
            field_simp
            ring
  intro t ht
  refine le_antisymm ?_ (hE0 t ht)
  have hlim : Tendsto (fun n : ℕ => M * (c * t) ^ n / n !) atTop (𝓝 0) := by
    have := (FloorSemiring.tendsto_pow_div_factorial_atTop (c * t)).const_mul M
    simp only [mul_zero] at this
    exact this.congr fun n => by ring
  exact ge_of_tendsto hlim (Eventually.of_forall fun n => hn n t ht)

/-- Lipschitz bound on `[-R, R]` from a derivative bound. -/
theorem exists_lip_on {G Gp : ℝ → ℝ} (hG : ∀ r, HasDerivAt G (Gp r) r) (hGp : Continuous Gp)
    (R : ℝ) : ∃ L, 0 ≤ L ∧ ∀ a b, |a| ≤ R → |b| ≤ R → |G a - G b| ≤ L * |a - b| := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_on_Icc hGp R
  refine ⟨L, hL0, fun a b ha hb => ?_⟩
  have := (convex_Icc (-R) R).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := G) (f' := Gp) (C := L) (fun r _ => (hG r).hasDerivWithinAt)
    (fun r hr => by rw [Real.norm_eq_abs]; exact hL r (abs_le.2 hr))
    (abs_le.1 hb) (abs_le.1 ha)
  simpa [Real.norm_eq_abs] using this

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tendsto_eps : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun m => by simp only [mem_Ioi]; positivity⟩

theorem tendsto_integral_abs_heatT_sub {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) :
    Tendsto (fun m : ℕ => ∫ x, |heatT (1 / ((m : ℝ) + 1)) f x - f x|) atTop (𝓝 0) := by
  have hfi := appA_integrable_of_abs_le' hf hB
  have h := (tendsto_heatT_L1 hfi).comp tendsto_eps
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simp only [ENNReal.toReal_zero] at h2
  refine h2.congr fun m => ?_
  simp only [Function.comp_apply]
  have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have hm : Measurable (heatT (1 / ((m : ℝ) + 1)) f) :=
    (measurable_heatT_joint hf).comp measurable_prodMk_left
  have := integral_norm_eq_lintegral_enorm (μ := volume)
    (f := fun x => heatT (1 / ((m : ℝ) + 1)) f x - f x) (hm.sub hf).aestronglyMeasurable
  rw [← this]
  simp only [Real.norm_eq_abs]

theorem tendsto_integral_comp_of_L1 {Φ : ℝ → ℝ} (hΦc : Continuous Φ) {L R : ℝ}
    (hΦ : ∀ a b, |a| ≤ R → |b| ≤ R → |Φ a - Φ b| ≤ L * |a - b|) {g : ℕ → UnitAddTorus ι → ℝ}
    {g₀ : UnitAddTorus ι → ℝ} (hgm : ∀ m, Measurable (g m)) (hg₀m : Measurable g₀)
    (hgb : ∀ m x, |g m x| ≤ R) (hg₀b : ∀ x, |g₀ x| ≤ R)
    (hconv : Tendsto (fun m => ∫ x, |g m x - g₀ x|) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, Φ (g m x)) atTop (𝓝 (∫ x, Φ (g₀ x))) := by
  obtain ⟨MΦ, -, hMΦ⟩ := exists_bound_on_Icc hΦc R
  have hi : ∀ {v : UnitAddTorus ι → ℝ}, Measurable v → (∀ x, |v x| ≤ R) →
      Integrable fun x => Φ (v x) := fun {v} hv hb =>
    appA_integrable_of_abs_le' (hΦc.measurable.comp hv) fun x => hMΦ _ (hb x)
  have hdi : ∀ m, Integrable fun x => |g m x - g₀ x| := fun m =>
    (appA_integrable_of_abs_le' ((hgm m).sub hg₀m) (fun x => (abs_sub _ _).trans
      (add_le_add (hgb m x) (hg₀b x)))).abs
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) (by simpa using hconv.const_mul L)
  rw [← integral_sub (hi (hgm m) (hgb m)) (hi hg₀m hg₀b), Real.norm_eq_abs]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  exact integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) ((hdi m).const_mul L)
    (Eventually.of_forall fun x => hΦ _ _ (hgb m x) (hg₀b x))

end SharpLSI
