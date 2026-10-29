import SharpSymmetricLSI.Paper.AppAStab4
import SharpSymmetricLSI.Paper.AppAGronwall

/-!
# Lemma A.1, (A.3): `L¹` stability of mild solutions

`sup_{t ≤ T} ‖ρ_t - η_t‖₁ ≤ C_T ‖ρ₀ - η₀‖₁` with `C_T` depending only on `T, d, B₀, L₀`
(`flow_stability_aux`): the Duhamel estimate `mild_diff_le` and the singular Grönwall lemma.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem IsProbDens.lintegral_sub_le_two {ρ η : Torus d → ℝ} (hρ : IsProbDens ρ)
    (hη : IsProbDens η) : ∫⁻ x, ‖ρ x - η x‖ₑ ∂haar d ≤ 2 := by
  calc ∫⁻ x, ‖ρ x - η x‖ₑ ∂haar d ≤ ∫⁻ x, (‖ρ x‖ₑ + ‖η x‖ₑ) ∂haar d :=
        lintegral_mono fun x => enorm_sub_le
    _ = ∫⁻ x, ‖ρ x‖ₑ ∂haar d + ∫⁻ x, ‖η x‖ₑ ∂haar d :=
        lintegral_add_left' hρ.int.aestronglyMeasurable.enorm _
    _ = 2 := by
        rw [← ofReal_integral_norm_eq_lintegral_enorm hρ.int,
          ← ofReal_integral_norm_eq_lintegral_enorm hη.int]
        simp_rw [Real.norm_eq_abs]
        rw [hρ.integral_abs, hη.integral_abs]
        norm_num

theorem lintegral_sub_eq_ofReal {ρ η : Torus d → ℝ} (hρ : Integrable ρ (haar d))
    (hη : Integrable η (haar d)) :
    ∫⁻ x, ‖ρ x - η x‖ₑ ∂haar d = ENNReal.ofReal (∫ x, |ρ x - η x| ∂haar d) := by
  rw [ofReal_integral_eq_lintegral_ofReal (f := fun x => |ρ x - η x|) (hρ.sub hη).abs
    (Eventually.of_forall fun _ => abs_nonneg _)]
  exact lintegral_congr fun x => by rw [← Real.norm_eq_abs, ofReal_norm]

/-- The Grönwall constant of (A.3). -/
noncomputable def stabK (d : ℕ) (B₀ L₀ : ℝ) : ℝ :=
  2 * (4 * π) ^ (-(1 : ℝ) / 2) * d * (max B₀ 0 + max L₀ 0)

/-- **(A.3).** -/
theorem flow_stability_aux (d : ℕ) (T B₀ L₀ : ℝ) :
    ∃ C : ℝ, ∀ (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (KV KW : ℝ), Hyp V W KV KW →
      (eLpNorm (fun x => Real.sqrt (sqNorm (weakGrad V x))) ⊤ (haar d) +
          eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume ≤
        ENNReal.ofReal B₀ ∧
        eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume ≤
          ENNReal.ofReal L₀) →
      ∀ ρ₀ η₀ ρ η, AppAMild V W ρ₀ ρ → AppAMild V W η₀ η →
        ∀ t ∈ Icc 0 T, eLpNorm (fun x => ρ t x - η t x) 1 (haar d) ≤
          ENNReal.ofReal C * eLpNorm (fun x => ρ₀ x - η₀ x) 1 (haar d) := by
  set K₀ := stabK d B₀ L₀ with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀, stabK]; positivity
  refine ⟨gronwallConst K₀ (max T 0), fun V W KV KW hyp hDB ρ₀ η₀ ρ η hρ hη t ht => ?_⟩
  have hT : 0 ≤ T := ht.1.trans ht.2
  rw [max_eq_left hT]
  obtain ⟨BV, BW, hBV0, hBW0, hsum, hBWL, hBV, hBW⟩ := drift_bounds hyp hDB
  -- the real error function
  set e : ℝ → ℝ := fun u => ∫ x, |ρ u x - η u x| ∂haar d with he
  have hE : ∀ u, 0 ≤ u → ∫⁻ x, ‖ρ u x - η u x‖ₑ ∂haar d = ENNReal.ofReal (e u) := fun u hu =>
    lintegral_sub_eq_ofReal (hρ.probDens hu).int (hη.probDens hu).int
  have he0 : ∀ u, 0 ≤ e u := fun u => integral_nonneg fun _ => abs_nonneg _
  have he2 : ∀ u, 0 ≤ u → e u ≤ 2 := fun u hu => by
    have h := (hρ.probDens hu).lintegral_sub_le_two (hη.probDens hu)
    rw [hE u hu] at h
    exact (ENNReal.ofReal_le_iff_le_toReal (by simp)).1 h |>.trans (by simp)
  have hinit : e 0 = ∫ x, |ρ₀ x - η₀ x| ∂haar d := by simp only [he, hρ.init, hη.init]
  -- continuity of `e`
  have hcont : ContinuousOn e (Icc 0 T) := by
    intro v hv
    have hdist : ∀ {ζ : ℝ → Torus d → ℝ} {ζ₀}, AppAMild V W ζ₀ ζ →
        Tendsto (fun u => ∫ x, |ζ u x - ζ v x| ∂haar d) (𝓝[Icc 0 T] v) (𝓝 0) := by
      intro ζ ζ₀ h
      have h1 := tendsto_nhdsWithin_mono_left (Icc_subset_Ici_self : Icc (0 : ℝ) T ⊆ Ici 0)
        (h.cont v hv.1)
      have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      simp only [ENNReal.toReal_zero] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u hu
      simp only [Function.comp_apply]
      rw [← lintegral_sub_eq_eLpNorm (h.probDens hu.1).int (h.probDens hv.1).int,
        lintegral_sub_eq_ofReal (h.probDens hu.1).int (h.probDens hv.1).int,
        ENNReal.toReal_ofReal (integral_nonneg fun _ => abs_nonneg _)]
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa using (hdist hρ).add (hdist hη))
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hiu := (hρ.probDens hu.1).int
    have hiv := (hρ.probDens hv.1).int
    have hju := (hη.probDens hu.1).int
    have hjv := (hη.probDens hv.1).int
    rw [Real.norm_eq_abs, he]
    simp only
    rw [← integral_sub (f := fun x => |ρ u x - η u x|) (g := fun x => |ρ v x - η v x|)
        (hiu.sub hju).abs (hiv.sub hjv).abs,
      ← integral_add (f := fun x => |ρ u x - ρ v x|) (g := fun x => |η u x - η v x|)
        (hiu.sub hiv).abs (hju.sub hjv).abs]
    refine (abs_integral_le_integral_abs).trans (integral_mono ((hiu.sub hju).abs.sub
      (hiv.sub hjv).abs).abs ((hiu.sub hiv).abs.add (hju.sub hjv).abs) fun x => ?_)
    refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    calc |ρ u x - η u x - (ρ v x - η v x)| = |(ρ u x - ρ v x) - (η u x - η v x)| := by ring_nf
      _ ≤ |ρ u x - ρ v x| + |η u x - η v x| := abs_sub _ _
  -- the integral inequality
  have hineq : ∀ s ∈ Ioc 0 T, e s ≤ e 0 + K₀ * ∫ u in Ioo 0 s, (s - u) ^ (-(1 : ℝ) / 2) * e u := by
    intro s hs
    have hd := mild_diff_le hyp hBV0 hBW0 hBV hBW hρ hη hs.1
    have hfi : IntegrableOn (fun u => (s - u) ^ (-(1 : ℝ) / 2) * e u) (Ioo 0 s) := by
      refine Integrable.mono' ((integrableOn_rsqrt hs.1).mul_const 2) ?_ ?_
      · exact ((continuousOn_const.sub continuousOn_id).rpow_const
          (fun u hu => Or.inl (sub_pos.2 hu.2).ne')).mul
          (hcont.mono fun u hu => ⟨hu.1.le, hu.2.le.trans hs.2⟩)
          |>.aestronglyMeasurable measurableSet_Ioo
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (sub_pos.2 hu.2).le _),
          abs_of_nonneg (he0 u)]
        exact mul_le_mul_of_nonneg_left (he2 u hu.1.le) (Real.rpow_nonneg (sub_pos.2 hu.2).le _)
    have hRHS : ∫⁻ u in Ioo 0 s, ENNReal.ofReal (divConst (s - u)) *
        (∑ _k : Fin d, ENNReal.ofReal (BV + 2 * BW) * ∫⁻ x, ‖ρ u x - η u x‖ₑ ∂haar d) ≤
        ENNReal.ofReal (K₀ * ∫ u in Ioo 0 s, (s - u) ^ (-(1 : ℝ) / 2) * e u) := by
      rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hfi.const_mul K₀)
        (by filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
            exact mul_nonneg hK₀0 (mul_nonneg (Real.rpow_nonneg (sub_pos.2 hu.2).le _) (he0 u)))]
      refine setLIntegral_mono' measurableSet_Ioo fun u hu => ?_
      have hBV2 : 0 ≤ BV + 2 * BW := by positivity
      have hsumeq : (∑ _k : Fin d, ENNReal.ofReal (BV + 2 * BW) *
          ∫⁻ x, ‖ρ u x - η u x‖ₑ ∂haar d) = ENNReal.ofReal (d * ((BV + 2 * BW) * e u)) := by
        rw [hE u hu.1.le, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_mul hBV2, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      rw [hsumeq, ← ENNReal.ofReal_mul (divConst_nonneg (sub_pos.2 hu.2))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [divConst_eq (sub_pos.2 hu.2)]
      have hr := Real.rpow_nonneg (sub_pos.2 hu.2).le (-(1 : ℝ) / 2)
      have hB : BV + 2 * BW ≤ max B₀ 0 + max L₀ 0 := by linarith
      have hc : 0 ≤ 2 * (4 * π) ^ (-(1 : ℝ) / 2) * (s - u) ^ (-(1 : ℝ) / 2) * d * e u := by
        have := he0 u; positivity
      calc 2 * (4 * π) ^ (-(1 : ℝ) / 2) * (s - u) ^ (-(1 : ℝ) / 2) * (d * ((BV + 2 * BW) * e u))
          = 2 * (4 * π) ^ (-(1 : ℝ) / 2) * (s - u) ^ (-(1 : ℝ) / 2) * d * e u * (BV + 2 * BW) := by
            ring
        _ ≤ 2 * (4 * π) ^ (-(1 : ℝ) / 2) * (s - u) ^ (-(1 : ℝ) / 2) * d * e u *
              (max B₀ 0 + max L₀ 0) := mul_le_mul_of_nonneg_left hB hc
        _ = K₀ * ((s - u) ^ (-(1 : ℝ) / 2) * e u) := by rw [hK₀, stabK]; ring
    have h1 := hd.trans (add_le_add le_rfl hRHS)
    have hI0 : 0 ≤ ∫ u in Ioo 0 s, (s - u) ^ (-(1 : ℝ) / 2) * e u :=
      integral_nonneg_of_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact mul_nonneg (Real.rpow_nonneg (sub_pos.2 hu.2).le _) (he0 u))
    rw [← hρ.init, ← hη.init] at h1
    rw [hE s hs.1.le, hE 0 le_rfl, ← ENNReal.ofReal_add (he0 0) (mul_nonneg hK₀0 hI0)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg (he0 0) (mul_nonneg hK₀0 hI0))).1 h1
  have hg := singular_gronwall (e := e) (a := e 0) (K := K₀) (T := T) (M := 2) hK₀0 (he0 0) hT
    (fun u _ => he0 u) (fun u hu => he2 u hu.1) hcont le_rfl hineq t ht
  rw [← lintegral_sub_eq_eLpNorm (hρ.probDens ht.1).int (hη.probDens ht.1).int, hE t ht.1,
    ← hρ.init, ← hη.init,
    ← lintegral_sub_eq_eLpNorm (hρ.probDens le_rfl).int (hη.probDens le_rfl).int, hE 0 le_rfl,
    ← ENNReal.ofReal_mul (gronwallConst_nonneg hK₀0 hT)]
  exact ENNReal.ofReal_le_ofReal hg

end SharpLSI
