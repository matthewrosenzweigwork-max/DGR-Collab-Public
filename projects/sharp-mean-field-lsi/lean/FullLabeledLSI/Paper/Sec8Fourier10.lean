import FullLabeledLSI.Paper.Sec8Fourier9

/-!
# Section 8.5 (Corollary 8.4), part 10: the multi-species inequality `2a G_θ ≤ D_θ`

For `W = G(x-y) - G(0)` with `G` smooth, even, `Ĝ(k) ≥ 0` for `k ≠ 0`, and every admissible family:
`G_θ = ∑ θ_a H(ρ_a|m) + ½ (∬ G ρ̄ρ̄ - ∫ G)` and
`D_θ ≥ ∑ θ_a 4 D2(ρ_a) - 2 ∬ ΔG ρ̄ρ̄`; the logarithmic Sobolev inequality bounds the first part and
the positive type of `K₂ = -2ΔG - a(G - ∫G)` the second.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

theorem inner_integrable {f : Torus d → ℝ} (hf : Continuous f) (ν : Measure (Torus d))
    [IsFiniteMeasure ν] : Integrable (fun y => ∫ x, f (x - y) ∂ν) ν :=
  (integrable_pair hf ν).integral_prod_right

theorem Qint_comb {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g) (α β : ℝ)
    (ν : Measure (Torus d)) [IsFiniteMeasure ν] :
    Qint ν (fun z => α * f z + β * g z) = α * Qint ν f + β * Qint ν g := by
  unfold Qint
  have h1 : ∀ y, ∫ x, (α * f (x - y) + β * g (x - y)) ∂ν =
      α * ∫ x, f (x - y) ∂ν + β * ∫ x, g (x - y) ∂ν := fun y => by
    have i1 : Integrable (fun x => α * f (x - y)) ν :=
      (integrable_cont_meas ν (hf.comp (continuous_id.sub continuous_const))).const_mul α
    have i2 : Integrable (fun x => β * g (x - y)) ν :=
      (integrable_cont_meas ν (hg.comp (continuous_id.sub continuous_const))).const_mul β
    rw [integral_add i1 i2, integral_const_mul, integral_const_mul]
  simp_rw [h1]
  rw [integral_add ((inner_integrable hf ν).const_mul α) ((inner_integrable hg ν).const_mul β),
    integral_const_mul, integral_const_mul]

theorem Qint_K2 {G : Torus d → ℝ} (hG : IsSmoothT G) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] :
    Qint ν (K2 G) = -2 * Qint ν (lap G) - aCos * (Qint ν G - meanT G) := by
  have e : K2 G = fun z => (-2) * lap G z + (-aCos) * K1 G z := by funext z; simp [K2]; ring
  rw [e, Qint_comb (continuous_of_isSmoothT (isSmoothT_lap hG))
    (continuous_of_isSmoothT (isSmoothT_K1 hG)), Qint_K1 (continuous_of_isSmoothT hG)]
  ring

theorem msGap_WG_toENNReal {G : Torus d → ℝ} (hG : IsSmoothT G)
    (hGk : ∀ k : Fin d → ℤ, k ≠ 0 → 0 ≤ (cf G k).re) (F : Family d) (hF : F.Admissible)
    (hH : ∀ a, klDiv (densMeasure (F.ρ a)) (haar d) ≠ ⊤) :
    (msGap (fun _ => (0 : ℝ)) (WG G) F).toENNReal =
      (∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d)) +
        ENNReal.ofReal ((Qint (densMeasure F.bar) G - meanT G) / 2) := by
  have hGc := continuous_of_isSmoothT hG
  have hν : IsProbabilityMeasure (densMeasure F.bar) :=
    isProbabilityMeasure_densMeasure' (bar_nonneg F hF) (bar_integral F hF)
  set Hθ : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d) with hHθ
  have hHθ' : Hθ ≠ ⊤ := ENNReal.sum_ne_top.mpr fun a _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hH a)
  have hr0 : 0 ≤ (Qint (densMeasure F.bar) G - meanT G) / 2 := by
    have := meanT_le_Qint hG hGk (densMeasure F.bar); linarith
  unfold msGap
  rw [interE_WG hGc, Fstar_WG hG hGk]
  have hp : potE (fun _ => (0 : ℝ)) (densMeasure F.bar) = 0 := by simp [potE]
  rw [hp]
  have e : ((Hθ : ℝ≥0∞) : EReal) + (((0 : ℝ) + (Qint (densMeasure F.bar) G - G 0) / 2 : ℝ) : EReal) -
      (((meanT G - G 0) / 2 : ℝ) : EReal) =
      ((Hθ + ENNReal.ofReal ((Qint (densMeasure F.bar) G - meanT G) / 2) : ℝ≥0∞) : EReal) := by
    rw [EReal.coe_ennreal_add, EReal.coe_ennreal_ofReal, max_eq_left hr0,
      ← EReal.coe_ennreal_toReal hHθ', ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_add]
    congr 1; ring
  rw [e, EReal.toENNReal_coe]

/-- **`2a G_θ ≤ D_θ`.** -/
theorem ms_lower {G : Torus d → ℝ} (hG : IsSmoothT G) (hGe : ∀ x, G (-x) = G x)
    (hGk : ∀ k : Fin d → ℤ, k ≠ 0 → 0 ≤ (cf G k).re) (F : Family d) (hF : F.Admissible) :
    ENNReal.ofReal (2 * aCos) * (msGap (fun _ => (0 : ℝ)) (WG G) F).toENNReal ≤
      msDiss (fun _ => (0 : ℝ)) (WG G) F := by
  obtain ⟨KW, hyp⟩ := hyp_WG hG hGe
  have ha0 : 0 < aCos := by unfold aCos; positivity
  have hν : IsProbabilityMeasure (densMeasure F.bar) :=
    isProbabilityMeasure_densMeasure' (bar_nonneg F hF) (bar_integral F hF)
  have hLSI : ∀ a, klDiv (densMeasure (F.ρ a)) (haar d) ≠ ⊤ ∧
      aCos * (klDiv (densMeasure (F.ρ a)) (haar d)).toReal ≤ 2 * D2 (F.ρ a) := fun a =>
    lsi_species (hF.2.2 a).1 (hF.2.2 a).2.1 (hF.2.2 a).2.2
  rw [msGap_WG_toENNReal hG hGk F hF fun a => (hLSI a).1]
  rw [msDiss_decomp F hyp hF]
  set Qlap := Qint (densMeasure F.bar) (lap G) with hQlap
  set Qg := Qint (densMeasure F.bar) G with hQg
  have hf := dissipation_WG_ge hG hGe (bar_nonneg F hF) (bar_integral F hF) (memH1_sqrtBar F hF)
  have hfish := fisher_identity_d F hF
  have hθ0 : ∀ a, 0 ≤ F.θ a := fun a => (hF.1 a).le
  -- the finite pieces
  set Hr : Fin F.q → ℝ := fun a => (klDiv (densMeasure (F.ρ a)) (haar d)).toReal with hHr
  have hHr0 : ∀ a, 0 ≤ Hr a := fun a => ENNReal.toReal_nonneg
  have hHθ : (∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar d)) =
      ENNReal.ofReal (∑ a, F.θ a * Hr a) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun a _ => mul_nonneg (hθ0 a) (hHr0 a)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.ofReal_mul (hθ0 a), hHr, ENNReal.ofReal_toReal (hLSI a).1]
  set Sθ : ℝ := ∑ a, F.θ a * (4 * D2 (F.ρ a)) with hSθ
  have hSθ0 : 0 ≤ Sθ := Finset.sum_nonneg fun a _ => mul_nonneg (hθ0 a)
    (mul_nonneg (by norm_num) (D2_nonneg _))
  have hS : (∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (4 * D2 (F.ρ a))) = ENNReal.ofReal Sθ := by
    rw [hSθ, ENNReal.ofReal_sum_of_nonneg fun a _ => mul_nonneg (hθ0 a)
      (mul_nonneg (by norm_num) (D2_nonneg _))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.ofReal_mul (hθ0 a)]
  set R : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar with hR
  rw [hS] at hfish
  have hRle : R ≤ ENNReal.ofReal Sθ := by rw [hfish]; exact le_add_self
  have hRtop : R ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRle
  have hD0 : 0 ≤ 4 * D2 F.bar := mul_nonneg (by norm_num) (D2_nonneg _)
  have hSR : Sθ = 4 * D2 F.bar + R.toReal := by
    have := congrArg ENNReal.toReal hfish
    rwa [ENNReal.toReal_ofReal hSθ0, ENNReal.toReal_add ENNReal.ofReal_ne_top hRtop,
      ENNReal.toReal_ofReal hD0] at this
  -- the real inequality
  have hK2 := Qint_nonneg_of_K (isSmoothT_K2 hG) (re_cf_K2_nonneg hG hGk) (densMeasure F.bar)
  rw [Qint_K2 hG] at hK2
  have hmeanle := meanT_le_Qint hG hGk (densMeasure F.bar)
  have hr0 : 0 ≤ (Qg - meanT G) / 2 := by linarith
  have hH : 2 * aCos * ∑ a, F.θ a * Hr a ≤ Sθ := by
    rw [hSθ, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have := (hLSI a).2
    have h2 : 2 * aCos * Hr a ≤ 4 * D2 (F.ρ a) := by simp only [hHr]; linarith
    calc 2 * aCos * (F.θ a * Hr a) = F.θ a * (2 * aCos * Hr a) := by ring
      _ ≤ F.θ a * (4 * D2 (F.ρ a)) := mul_le_mul_of_nonneg_left h2 (hθ0 a)
  have hreal : 2 * aCos * (∑ a, F.θ a * Hr a + (Qg - meanT G) / 2) ≤
      (4 * D2 F.bar - 2 * Qlap) + R.toReal := by
    have : 2 * aCos * ((Qg - meanT G) / 2) = aCos * (Qg - meanT G) := by ring
    nlinarith
  rw [hHθ, ← ENNReal.ofReal_add (Finset.sum_nonneg fun a _ => mul_nonneg (hθ0 a) (hHr0 a)) hr0,
    ← ENNReal.ofReal_mul (by positivity)]
  calc ENNReal.ofReal (2 * aCos * (∑ a, F.θ a * Hr a + (Qg - meanT G) / 2))
      ≤ ENNReal.ofReal ((4 * D2 F.bar - 2 * Qlap) + R.toReal) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ ENNReal.ofReal (4 * D2 F.bar - 2 * Qlap) + ENNReal.ofReal R.toReal :=
        ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (4 * D2 F.bar - 2 * Qlap) + R := by rw [ENNReal.ofReal_toReal hRtop]
    _ ≤ _ := add_le_add hf le_rfl

end Sec8
end SharpLSI.FL
