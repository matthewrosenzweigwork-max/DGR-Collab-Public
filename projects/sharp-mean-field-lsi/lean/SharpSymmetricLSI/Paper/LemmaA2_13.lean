import SharpSymmetricLSI.Paper.LemmaA2_12

/-!
# R25 (A.9), part 13: the eigen-coefficients of the limit resolvent

If `u` is Lipschitz and `∫ ρ(h - u)Θ = τ ∫ ρ ∇u·∇Θ` for all smooth periodic `Θ`, then testing
with the heat regularizations `e^{tΔ}e_j` (`t → 0`) and using the eigen-equation gives
`⟨h, e_j⟩_μ = (1 + τλ_j) ⟨u, e_j⟩_μ` (`coeff_of_limit_eq`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem tendsto_integral_mul_heatT {f a : Torus d → ℝ} (hf : Integrable f)
    (ha : AEStronglyMeasurable a volume) {B : ℝ} (hB : ∀ y, |a y| ≤ B) {s : ℕ → ℝ}
    (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, a y * heatT (s n) f y) atTop (𝓝 (∫ y, a y * f y)) := by
  have hs0' : Tendsto s atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hs0, Eventually.of_forall hs⟩
  have hL1 := (tendsto_heatT_L1 hf).comp hs0'
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hi : ∀ n, Integrable (heatT (s n) f) := fun n => integrable_heatT (hs n) hf
  have hai : ∀ {g : Torus d → ℝ}, Integrable g → Integrable fun y => a y * g y := fun hg =>
    hg.bdd_mul (c := B) ha (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hL1' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
  rw [ENNReal.toReal_zero, Metric.tendsto_atTop] at hL1'
  obtain ⟨N, hN⟩ := hL1' (ε / (B + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [Real.dist_eq, sub_zero, Function.comp_apply] at h1
  have heq : (∫⁻ x, ‖heatT (s n) f x - f x‖ₑ).toReal = ∫ x, |heatT (s n) f x - f x| := by
    have := integral_norm_eq_lintegral_enorm (μ := (volume : Measure (Torus d)))
      (f := fun x => heatT (s n) f x - f x) ((hi n).sub hf).aestronglyMeasurable
    rw [← this]
    simp_rw [Real.norm_eq_abs]
  change |(∫⁻ x, ‖heatT (s n) f x - f x‖ₑ).toReal| < _ at h1
  rw [heq, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at h1
  rw [Real.dist_eq, ← integral_sub (hai (hi n)) (hai hf)]
  calc |∫ y, (a y * heatT (s n) f y - a y * f y)| ≤ ∫ y, |a y * heatT (s n) f y - a y * f y| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, B * |heatT (s n) f y - f y| := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (((hi n).sub hf).abs.const_mul B) (Eventually.of_forall fun y => ?_)
        show |a y * heatT (s n) f y - a y * f y| ≤ B * |heatT (s n) f y - f y|
        rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_right (hB y) (abs_nonneg _)
    _ = B * ∫ y, |heatT (s n) f y - f y| := integral_const_mul _ _
    _ < ε := by
        calc B * ∫ y, |heatT (s n) f y - f y| ≤ B * (ε / (B + 1)) :=
              mul_le_mul_of_nonneg_left h1.le hB0
          _ < ε := by rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith

section coeff

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ)
include hρ hρc

theorem memH1_of_lipschitz {u : Torus d → ℝ} (hu : Continuous u) {L : ℝ≥0}
    (hL : LipschitzWith L (u ∘ liftT)) : MemH1 (densMeasure ρ) u := by
  have hw := isWeakGrad_lipGrad hu hL
  have hae : weakGrad u =ᵐ[volume] lipGrad u :=
    weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw⟩) hw
  refine memH1_of_vol hρ ⟨⟨_, hw⟩, hu.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_⟩
  refine MemLp.of_bound (f := fun x => Real.sqrt (sqNorm (weakGrad u x))) ?_
    (Real.sqrt (Fintype.card (Fin d) * L ^ 2)) ?_
  · have hm : Measurable fun y => Real.sqrt (sqNorm (lipGrad u y)) :=
      Real.continuous_sqrt.measurable.comp
        (Finset.measurable_sum _ fun k _ => (measurable_lipGrad hu k).pow_const 2)
    refine hm.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with y hy
    simp only [hy]
  · filter_upwards [hae] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hy]
    refine Real.sqrt_le_sqrt ?_
    calc sqNorm (lipGrad u y) ≤ ∑ _k : Fin d, (L : ℝ) ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_lipGrad_le hL y k) 2
      _ = _ := by simp

/-- **The eigen-coefficients of the limit.** -/
theorem coeff_of_limit_eq {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (hb : IsRefEigenbasis (densMeasure ρ) e lam) {h u : Torus d → ℝ} (hh : Continuous h)
    (hu : Continuous u) {L : ℝ≥0} (hL : LipschitzWith L (u ∘ liftT)) {τ : ℝ}
    (hlim : ∀ Θ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ Θ → IsPer Θ →
      ∫ y, ρ y * (h y - u y) * Θ (secT y) =
        τ * ∫ y, ρ y * ∑ k, lipGrad u y k * Dk Θ k (secT y)) (j : ℕ) :
    ∫ y, h y * e j y ∂densMeasure ρ = (1 + τ * lam j) * ∫ y, u y * e j y ∂densMeasure ρ := by
  haveI := hρ.isProb
  set P := densMeasure ρ
  have hej := hb.memH1 j
  have hev : MemLp (e j) 2 volume := memLp_vol hρ.haar_le_smul hej
  have hge : ∀ k, MemLp (fun y => weakGrad (e j) y k) 2 volume := fun k =>
    memLp_grad_vol hρ.haar_le_smul hρ.le_smul hej k
  have hw := isWeakGrad_lipGrad hu hL
  obtain ⟨Bρ, hBρ⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
  have hBρ' : ∀ y, |ρ y| ≤ Bρ := fun y => by simpa [Real.norm_eq_abs] using hBρ y (mem_univ _)
  have hBρ0 : 0 ≤ Bρ := (abs_nonneg _).trans (hBρ' 0)
  obtain ⟨Bh, hBh⟩ := isCompact_univ.exists_bound_of_continuousOn (hh.sub hu).continuousOn
  have hBh' : ∀ y, |h y - u y| ≤ Bh := fun y => by
    simpa [Real.norm_eq_abs] using hBh y (mem_univ _)
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hs : ∀ n, 0 < s n := fun n => by positivity
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- the identity for the heat regularizations
  have hn : ∀ n, ∫ y, (ρ y * (h y - u y)) * heatT (s n) (e j) y =
      ∑ k, ∫ y, (τ * ρ y * lipGrad u y k) * heatT (s n) (fun z => weakGrad (e j) z k) y := by
    intro n
    have hsm := isSmoothT_heatT (hs n) (hev.integrable one_le_two)
    set Θ := heatT (s n) (e j) ∘ liftT
    have hΘp : IsPer Θ := fun m x => by simp only [Θ, Function.comp, liftT_add_intVec]
    have hΘs : ∀ y, Θ (secT y) = heatT (s n) (e j) y := fun y => by simp [Θ, liftT_secT]
    have hDΘ : ∀ k, (fun y => Dk Θ k (secT y)) =ᵐ[volume]
        heatT (s n) (fun z => weakGrad (e j) z k) := fun k => by
      have := heat_grad hev (hs n) (isWeakGrad_weakGrad hej.1)
        (fun i => (hge i).integrable one_le_two) k
      filter_upwards [this] with y hy
      rw [← hy]; rfl
    have h1 := hlim Θ hsm (hΘp)
    simp only [hΘs] at h1
    rw [show (fun y => ρ y * (h y - u y) * heatT (s n) (e j) y) =
      fun y => (ρ y * (h y - u y)) * heatT (s n) (e j) y from rfl] at h1
    rw [h1, ← integral_const_mul]
    have hint : ∀ k ∈ Finset.univ, Integrable fun y =>
        (τ * ρ y * lipGrad u y k) * heatT (s n) (fun z => weakGrad (e j) z k) y := fun k _ =>
      (integrable_heatT (hs n) ((hge k).integrable one_le_two)).bdd_mul
        (c := |τ| * Bρ * L)
        ((continuous_const.mul hρc).aestronglyMeasurable.mul
          (measurable_lipGrad hu k).aestronglyMeasurable)
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hBρ' y) (abs_nonneg _))
            (abs_lipGrad_le hL y k) (abs_nonneg _) (mul_nonneg (abs_nonneg _) hBρ0))
    rw [← integral_finset_sum _ hint]
    refine integral_congr_ae ?_
    have hall : ∀ᵐ y ∂volume, ∀ k, Dk Θ k (secT y) =
        heatT (s n) (fun z => weakGrad (e j) z k) y := ae_all_iff.mpr hDΘ
    filter_upwards [hall] with y hy
    simp only [Finset.mul_sum, hy]
    refine Finset.sum_congr rfl fun k _ => by ring
  -- pass to the limit
  have hlimL := tendsto_integral_mul_heatT (hev.integrable one_le_two)
    (a := fun y => ρ y * (h y - u y)) (hρc.mul (hh.sub hu)).aestronglyMeasurable
    (B := Bρ * Bh) (fun y => by
      rw [abs_mul]; exact mul_le_mul (hBρ' y) (hBh' y) (abs_nonneg _)
        ((abs_nonneg _).trans (hBρ' y))) hs hs0
  have hlimR := tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun k _ =>
    tendsto_integral_mul_heatT ((hge k).integrable one_le_two)
      (a := fun y => τ * ρ y * lipGrad u y k)
      ((continuous_const.mul hρc).aestronglyMeasurable.mul
        (measurable_lipGrad hu k).aestronglyMeasurable) (B := |τ| * Bρ * L)
      (fun y => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hBρ' y) (abs_nonneg _))
          (abs_lipGrad_le hL y k) (abs_nonneg _) (mul_nonneg (abs_nonneg _) hBρ0)) hs hs0
  have hEq := tendsto_nhds_unique hlimL (hlimR.congr fun n => (hn n).symm)
  -- identify both sides
  have hae : weakGrad u =ᵐ[volume] lipGrad u := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw⟩) hw
  have huH := memH1_of_lipschitz hρ hρc hu hL
  have heig := hb.eigen j u huH
  have hdir : dirB P u (e j) = ∫ y, ρ y * ∑ k, lipGrad u y k * weakGrad (e j) y k := by
    unfold dirB
    rw [hρ.integral_eq]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    simp only [hy]
  have hsum : ∑ k, ∫ y, (τ * ρ y * lipGrad u y k) * weakGrad (e j) y k =
      τ * dirB P u (e j) := by
    rw [hdir, ← integral_const_mul, ← integral_finset_sum]
    · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    · intro k _
      exact ((hge k).integrable one_le_two).bdd_mul (c := |τ| * Bρ * L)
        ((continuous_const.mul hρc).aestronglyMeasurable.mul
          (measurable_lipGrad hu k).aestronglyMeasurable)
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (hBρ' y) (abs_nonneg _))
            (abs_lipGrad_le hL y k) (abs_nonneg _) (mul_nonneg (abs_nonneg _) hBρ0))
  rw [hsum] at hEq
  -- `dirB u e_j = λ_j ⟨u, e_j⟩`
  have hsym : dirB P u (e j) = lam j * ∫ y, u y * e j y ∂P := by
    rw [dirB_comm hρ]
    have : ∫ y, e j y * u y ∂P = ∫ y, u y * e j y ∂P := by
      congr 1; funext y; ring
    rw [← this]; exact heig
  rw [hsym] at hEq
  have hl : ∫ y, ρ y * (h y - u y) * e j y = ∫ y, h y * e j y ∂P - ∫ y, u y * e j y ∂P := by
    have hei : Integrable (e j) P := (hb.memH1 j).2.1.integrable one_le_two
    obtain ⟨Bh1, hBh1⟩ := isCompact_univ.exists_bound_of_continuousOn hh.continuousOn
    obtain ⟨Bu1, hBu1⟩ := isCompact_univ.exists_bound_of_continuousOn hu.continuousOn
    have hhi : Integrable (fun y => h y * e j y) P :=
      hei.bdd_mul (c := Bh1) hh.aestronglyMeasurable
        (Eventually.of_forall fun y => hBh1 y (mem_univ _))
    have hui : Integrable (fun y => u y * e j y) P :=
      hei.bdd_mul (c := Bu1) hu.aestronglyMeasurable
        (Eventually.of_forall fun y => hBu1 y (mem_univ _))
    rw [← integral_sub hhi hui, hρ.integral_eq]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only; ring
  have := hl.symm.trans hEq
  linear_combination this

end coeff

end SharpLSI
