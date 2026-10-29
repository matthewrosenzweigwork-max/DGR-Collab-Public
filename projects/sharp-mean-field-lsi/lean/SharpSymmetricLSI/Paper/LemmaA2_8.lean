import SharpSymmetricLSI.Paper.LemmaA2_7

/-!
# R25 (A.9), part 8: tools for the smooth Lipschitz estimate

* `uniform_heatT`: `e^{sΔ}g → g` uniformly for continuous `g` (compactness and dominated
  convergence along moving points, `tendsto_heatT_moving`);
* `semimono_of_hessian`: `D²Q ≥ -K` gives `(∇Q(x) - ∇Q(y))·(x - y) ≥ -K|x - y|²`;
* `weak_haar_of_resolvent`: the integrated resolvent equation for a `C¹` solution gives the Haar
  weak form `∫ ∇u·∇Θ dm = ∫ gΘ dm`, `g = (Φ - u)/τ + β·∇u`, `β = ∇ρ/ρ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

section heat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tendsto_heatT_moving {g : UnitAddTorus ι → ℝ} (hg : Continuous g) {s : ℕ → ℝ}
    (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0)) {y : ℕ → UnitAddTorus ι}
    {x : UnitAddTorus ι} (hy : Tendsto y atTop (𝓝 x)) :
    Tendsto (fun n => heatT (s n) g (y n)) atTop (𝓝 (g x)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have e : (fun n => heatT (s n) g (y n)) =
      fun n => ∫ z, g (y n - liftT (Real.sqrt (s n) • z)) * heatKernel 1 z :=
    funext fun n => heatT_rescale (hs n) g (y n)
  rw [e]
  have hlim : ∫ z : ι → ℝ, g x * heatKernel 1 z = g x := by
    rw [integral_const_mul, integral_heatKernel one_pos, mul_one]
  rw [← hlim]
  refine tendsto_integral_of_dominated_convergence (fun z => C * heatKernel 1 z) (fun n => ?_)
    ((integrable_heatKernel one_pos).const_mul C) (fun n => Eventually.of_forall fun z => ?_)
    (Eventually.of_forall fun z => ?_)
  · have hcz : Continuous fun z : ι → ℝ => g (y n - liftT (Real.sqrt (s n) • z)) :=
      hg.comp ((continuous_const (y := y n)).sub (continuous_liftT.comp
        (continuous_id.const_smul (Real.sqrt (s n)))))
    exact (hcz.mul (differentiable_heatKernel (ι := ι) 1).continuous).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (heatKernel_pos one_pos z)]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hC _ (mem_univ _))
      (heatKernel_pos one_pos z).le
  · refine Tendsto.mul_const _ ?_
    have h1 : Tendsto (fun n => Real.sqrt (s n) • z) atTop (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp hs0).smul_const z
      simpa using this
    have hc : Continuous fun p : UnitAddTorus ι × (ι → ℝ) => g (p.1 - liftT p.2) :=
      hg.comp (continuous_fst.sub (continuous_liftT.comp continuous_snd))
    have h2 := (hc.tendsto (x, 0)).comp (hy.prodMk_nhds h1)
    have e0 : liftT (0 : ι → ℝ) = 0 := by funext i; simp [liftT]
    simpa [Function.comp_def, e0] using h2

/-- **Uniform convergence of the heat flow for continuous data.** -/
theorem uniform_heatT {g : UnitAddTorus ι → ℝ} (hg : Continuous g) {s : ℕ → ℝ}
    (hs : ∀ n, 0 < s n) (hs0 : Tendsto s atTop (𝓝 0)) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |heatT (s n) g x - g x| ≤ ε := by
  by_contra h
  push_neg at h
  obtain ⟨ε, hε, hN⟩ := h
  choose n hn x hx using hN
  obtain ⟨x₀, -, φ, hφ, hxφ⟩ := isCompact_univ.tendsto_subseq (fun k => mem_univ (x k))
  have hnφ : Tendsto (fun k => n (φ k)) atTop atTop :=
    tendsto_atTop_mono (fun k => hn (φ k)) hφ.tendsto_atTop
  have h1 := tendsto_heatT_moving hg (fun k => hs (n (φ k))) (hs0.comp hnφ) hxφ
  have h2 := (hg.tendsto x₀).comp hxφ
  have h3 := h1.sub h2
  rw [sub_self] at h3
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp h3) ε hε
  have := hK K le_rfl
  rw [Real.dist_eq, sub_zero] at this
  exact absurd (hx (φ K)) (not_lt.mpr this.le)

end heat

section semimono

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem semimono_of_hessian {Q : (ι → ℝ) → ℝ} (hQ : ContDiff ℝ 2 Q) {K : ℝ}
    (hK : ∀ x v, -K * ∑ i, v i ^ 2 ≤ secondDirDeriv Q v x) (x y : ι → ℝ) :
    -K * dE x y ^ 2 ≤
      ∑ k, (fderiv ℝ Q x (Pi.single k 1) - fderiv ℝ Q y (Pi.single k 1)) * (x k - y k) := by
  set w := x - y
  have hD : Differentiable ℝ fun z => fderiv ℝ Q z w :=
    ((hQ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      (by norm_num)
  have hφ : ∀ s, HasDerivAt (fun s => fderiv ℝ Q (y + s • w) w)
      (secondDirDeriv Q w (y + s • w)) s := fun s => hasDerivAt_line hD y w s
  obtain ⟨ξ, -, hξ⟩ := exists_hasDerivAt_eq_slope (fun s => fderiv ℝ Q (y + s • w) w)
    (fun s => secondDirDeriv Q w (y + s • w)) zero_lt_one
    (continuous_iff_continuousAt.mpr fun s => (hφ s).continuousAt).continuousOn
    fun s _ => hφ s
  simp only [one_smul, zero_smul, add_zero, sub_zero, div_one] at hξ
  have hx : y + w = x := by simp [w]
  rw [hx] at hξ
  have h1 := hK (y + ξ • w) w
  have e1 : ∑ k, (fderiv ℝ Q x (Pi.single k 1) - fderiv ℝ Q y (Pi.single k 1)) * (x k - y k) =
      fderiv ℝ Q x w - fderiv ℝ Q y w := by
    rw [fderiv_apply_eq_sum Q x w, fderiv_apply_eq_sum Q y w, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [w, Pi.sub_apply]; ring
  rw [e1, ← hξ, dE_sq]
  simpa [w] using h1

end semimono

section weak

variable {d : ℕ} {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C)
  (hρs : ContDiff ℝ ∞ (ρ ∘ liftT))
include hρ hρs

/-- The lifted drift `β = ∇ρ/ρ`. -/
noncomputable def betaL (ρ : Torus d → ℝ) (k : Fin d) (x : Fin d → ℝ) : ℝ :=
  Dk (ρ ∘ liftT) k x / ρ (liftT x)

omit hρ hρs in
theorem isPer_betaL (k : Fin d) : IsPer (betaL ρ k) := fun m x => by
  simp only [betaL, liftT_add_intVec, (isPer_comp_liftT ρ).Dk k m x]

theorem contDiff_betaL (k : Fin d) : ContDiff ℝ ∞ (betaL ρ k) :=
  (contDiff_Dk hρs k).div hρs fun x => (hρ.pos.trans_le (hρ.lower _)).ne'

/-- **Haar weak form of the resolvent equation.** -/
theorem weak_haar_of_resolvent {τ : ℝ} (hτ : 0 < τ) {u : Torus d → ℝ}
    (hu : ContDiff ℝ 1 (u ∘ liftT)) {Φ : (Fin d → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦp : IsPer Φ)
    (hres : ∀ Θ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ Θ → IsPer Θ →
      ∫ y, ρ y * (Φ (secT y) - u y) * Θ (secT y) = -τ * ∫ y, u y * divRho ρ Θ (secT y))
    {Θ' : (Fin d → ℝ) → ℝ} (hΘ' : ContDiff ℝ ∞ Θ') (hp' : IsPer Θ') :
    ∫ y, ∑ k, dpart u k y * Dk Θ' k (secT y) =
      ∫ y, ((Φ (secT y) - u y) / τ + ∑ k, betaL ρ k (secT y) * dpart u k y) * Θ' (secT y) := by
  have hpos : ∀ y, 0 < ρ y := fun y => hρ.pos.trans_le (hρ.lower y)
  set ρL := ρ ∘ liftT
  have hρL0 : ∀ x, 0 < ρL x := fun x => hpos _
  set σL : (Fin d → ℝ) → ℝ := fun x => 1 / ρL x
  have hσ : ContDiff ℝ ∞ σL := contDiff_const.div hρs fun x => (hρL0 x).ne'
  have hρσ : ∀ x, ρL x * σL x = 1 := fun x => by simp only [σL]; field_simp [(hρL0 x).ne']
  have hρ1 : Differentiable ℝ ρL := hρs.differentiable (by simp)
  have hσ1 : Differentiable ℝ σL := hσ.differentiable (by simp)
  have hΘ1 : Differentiable ℝ Θ' := hΘ'.differentiable (by simp)
  -- `ρ ∂σ = -β`
  have hρdσ : ∀ k x, ρL x * Dk σL k x = -betaL ρ k x := by
    intro k x
    have h1 : Dk ρL k x * σL x + ρL x * Dk σL k x = 0 := by
      rw [← Dk_mul hρ1 hσ1]
      have : (fun z => ρL z * σL z) = fun _ => 1 := funext hρσ
      rw [this]; simp [Dk]
    have hσx : σL x = 1 / ρL x := rfl
    have hρx : ρL x = ρ (liftT x) := rfl
    rw [hσx] at h1
    simp only [betaL]
    rw [← hρx, div_eq_mul_one_div]
    linear_combination h1
  set Θ : (Fin d → ℝ) → ℝ := fun x => Θ' x * σL x
  have hΘ : ContDiff ℝ ∞ Θ := hΘ'.mul hσ
  have hΘp : IsPer Θ := fun m x => by
    simp only [Θ, σL, hp' m x, ρL, Function.comp, liftT_add_intVec]
  set Ψ : Fin d → (Fin d → ℝ) → ℝ := fun k z => Dk Θ' k z - Θ' z * betaL ρ k z
  have hΨ : ∀ k, ContDiff ℝ ∞ (Ψ k) := fun k =>
    (contDiff_Dk hΘ' k).sub (hΘ'.mul (contDiff_betaL hρ hρs k))
  have hΨp : ∀ k, IsPer (Ψ k) := fun k m z => by
    simp only [Ψ, hp'.Dk k m z, hp' m z, isPer_betaL k m z]
  have hdiv : ∀ x, divRho ρ Θ x = ∑ k, Dk (Ψ k) k x := by
    intro x
    simp only [divRho]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    funext z
    show ρL z * Dk Θ k z = Ψ k z
    rw [show Θ = fun z => Θ' z * σL z from rfl, Dk_mul hΘ1 hσ1]
    simp only [Ψ]
    have := hρdσ k z
    have h2 := hρσ z
    linear_combination (Dk Θ' k z) * h2 + Θ' z * this
  have h := hres Θ hΘ hΘp
  -- left side
  have hl : ∫ y, ρ y * (Φ (secT y) - u y) * Θ (secT y) = ∫ y, (Φ (secT y) - u y) * Θ' (secT y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hy : ρL (secT y) = ρ y := by simp [ρL, liftT_secT]
    have := hρσ (secT y)
    simp only [Θ]
    rw [hy] at this
    linear_combination (Φ (secT y) - u y) * Θ' (secT y) * this
  -- right side by parts
  have hw := isWeakGrad_of_contDiff hu
  have huc : Continuous u := continuous_of_liftT' hu.continuous
  have hdc : ∀ k, Continuous (dpart u k) := fun k =>
    continuous_of_liftT' (contDiff_dpart (n := 0) (by simpa using hu) k).continuous
  have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f := fun hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcomp : ∀ {F : (Fin d → ℝ) → ℝ}, Continuous F → IsPer F → Continuous fun y => F (secT y) :=
    fun {F} hF hp => continuous_of_liftT' (by
      rw [show (fun y => F (secT y)) ∘ liftT = F from comp_secT_comp_liftT hp]; exact hF)
  have hibp : ∀ k, ∫ y, u y * Dk (Ψ k) k (secT y) = -∫ y, dpart u k y * Ψ k (secT y) := by
    intro k
    have := integral_mul_Dk_eq hw (hint huc) (fun j => hint (hdc j)) (hΨ k) (hΨp k) k
    simpa [dpart] using this
  have hr : ∫ y, u y * divRho ρ Θ (secT y) = -∫ y, ∑ k, dpart u k y * Ψ k (secT y) := by
    simp_rw [hdiv, Finset.mul_sum]
    have hi1 : ∀ k ∈ Finset.univ, Integrable (fun y => u y * Dk (Ψ k) k (secT y)) := fun k _ =>
      hint (huc.mul (hcomp (contDiff_Dk (hΨ k) k).continuous ((hΨp k).Dk k)))
    have hi2 : ∀ k ∈ Finset.univ, Integrable (fun y => dpart u k y * Ψ k (secT y)) := fun k _ =>
      hint ((hdc k).mul (hcomp (hΨ k).continuous (hΨp k)))
    rw [integral_finset_sum _ hi1, integral_finset_sum _ hi2]
    simp_rw [hibp]
    rw [Finset.sum_neg_distrib]
  rw [hl, hr] at h
  -- rearrange
  have hβc : ∀ k, Continuous fun y => betaL ρ k (secT y) := fun k =>
    hcomp (contDiff_betaL hρ hρs k).continuous (isPer_betaL k)
  have hΘc : Continuous fun y => Θ' (secT y) := hcomp hΘ'.continuous hp'
  have hDΘc : ∀ k, Continuous fun y => Dk Θ' k (secT y) := fun k =>
    hcomp (contDiff_Dk hΘ' k).continuous (hp'.Dk k)
  have e1 : ∫ y, ∑ k, dpart u k y * Ψ k (secT y) =
      (∫ y, ∑ k, dpart u k y * Dk Θ' k (secT y)) -
        ∫ y, (∑ k, betaL ρ k (secT y) * dpart u k y) * Θ' (secT y) := by
    have hA : Integrable (fun y => ∑ k, dpart u k y * Dk Θ' k (secT y)) :=
      hint (continuous_finset_sum _ fun k _ => (hdc k).mul (hDΘc k))
    have hB : Integrable (fun y => (∑ k, betaL ρ k (secT y) * dpart u k y) * Θ' (secT y)) :=
      hint ((continuous_finset_sum _ fun k _ => (hβc k).mul (hdc k)).mul hΘc)
    rw [← integral_sub hA hB]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [Ψ, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [e1] at h
  have e2 : ∫ y, ((Φ (secT y) - u y) / τ + ∑ k, betaL ρ k (secT y) * dpart u k y) * Θ' (secT y) =
      (∫ y, (Φ (secT y) - u y) * Θ' (secT y)) / τ +
        ∫ y, (∑ k, betaL ρ k (secT y) * dpart u k y) * Θ' (secT y) := by
    have hA : Integrable (fun y => (Φ (secT y) - u y) * Θ' (secT y) / τ) :=
      hint ((((hcomp hΦ.continuous hΦp).sub huc).mul hΘc).div_const _)
    have hB : Integrable (fun y => (∑ k, betaL ρ k (secT y) * dpart u k y) * Θ' (secT y)) :=
      hint ((continuous_finset_sum _ fun k _ => (hβc k).mul (hdc k)).mul hΘc)
    rw [← integral_div, ← integral_add hA hB]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [e2]
  field_simp
  linarith

end weak

end SharpLSI
