import SharpSymmetricLSI.Paper.GaussLaw9
import SharpSymmetricLSI.Paper.ULimit10

/-!
# R27: from the reference law to the Gibbs law ((6.10), the Gibbs fluctuation limit)

With `∫ e^{-pU_N} dμ^{⊗N} ≤ B` (`p > 1`, from the partition estimates of Lemma 5.2), the
truncations `g(Z_N) min(e^{-U_N}, M)` are bounded continuous functions of `(U_N, Z_N)`; by (6.9)
they converge, and the truncation errors are `≤ ‖g‖ M^{1-p} B` uniformly in `N` (and `→ 0` as
`M → ∞` in the limit, by dominated convergence). Hence
`∫ g(Z_N) e^{-U_N} dμ^{⊗N} → ∫ g(z) e^{-U_∞} dγ`, in particular `K_N → K_∞`, and the fluctuation
laws under `P_N = K_N^{-1} e^{-U_N} μ^{⊗N}` converge to those under `γ_∞`.
-/

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped InnerProductSpace BoundedContinuousFunction

namespace SharpLSI

theorem abs_min_exp_le (u M : ℝ) : |min (rexp (-u)) M| ≤ |M| := by
  rcases le_or_gt 0 M with h | h
  · rw [abs_of_nonneg (le_min (Real.exp_pos _).le h), abs_of_nonneg h]; exact min_le_right _ _
  · rw [min_eq_right (h.le.trans (Real.exp_pos _).le)]

/-- `u ↦ min(e^{-u}, M)`. -/
noncomputable def truncExp (M : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun u => min (rexp (-u)) M, by fun_prop⟩ (2 * |M|)
    fun a b => by
      simp only [ContinuousMap.coe_mk, Real.dist_eq]
      have := abs_min_exp_le a M; have := abs_min_exp_le b M
      have := abs_sub (min (rexp (-a)) M) (min (rexp (-b)) M)
      linarith

/-- `(u, z) ↦ g(z) min(e^{-u}, M)`. -/
noncomputable def truncG {J : ℕ} (g : (Fin J → ℝ) →ᵇ ℝ) (M : ℝ) : ℝ × (Fin J → ℝ) →ᵇ ℝ :=
  g.compContinuous ⟨Prod.snd, continuous_snd⟩ * (truncExp M).compContinuous ⟨Prod.fst, continuous_fst⟩

theorem truncG_apply {J : ℕ} (g : (Fin J → ℝ) →ᵇ ℝ) (M : ℝ) (p : ℝ × (Fin J → ℝ)) :
    truncG g M p = g p.2 * min (rexp (-p.1)) M := rfl

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section gibbs
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

theorem aestronglyMeasurable_g_fluct {J : ℕ} (g : (Fin J → ℝ) →ᵇ ℝ) (N : ℕ) :
    AEStronglyMeasurable (fun X : Config N d => g fun n : Fin J => fluct e N n X)
      (Measure.pi fun _ : Fin N => (μ : Measure (Torus d))) := by
  have hm : Measurable fun X : Config N d => fun n : Fin J =>
      zSum (fun i => (he.memLp i).aestronglyMeasurable.mk (e i)) N n X := by
    unfold zSum
    refine measurable_pi_iff.mpr fun n => measurable_const.mul
      (Finset.measurable_sum _ fun l _ => ?_)
    exact (he.memLp _).aestronglyMeasurable.stronglyMeasurable_mk.measurable.comp
      (measurable_pi_apply l)
  have h := hm.aestronglyMeasurable.congr (fluct_ae_eq hyp hμ he N J).symm
  exact g.continuous.comp_aestronglyMeasurable h

/-- **The weighted limit.** -/
theorem tendsto_weighted {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos (Tmat W μ e) Q)
    (hint : Integrable (fun z => rexp (-Uinf W μ Q z)) gammaRef)
    {B p : ℝ} (hp : 1 < p)
    (hB : ∀ N : ℕ, 1 ≤ N → ∫ X, rexp (-Ucentered W μ N X) ^ p
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) ≤ B)
    {J : ℕ} (g : (Fin J → ℝ) →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ X, g (fun n => fluct e N n X) * rexp (-Ucentered W μ N X)
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))) atTop
      (𝓝 (∫ z, g (fun n => z n) * rexp (-Uinf W μ Q z) ∂gammaRef)) := by
  set μm := (μ : Measure (Torus d))
  have hlim := (U_limit_aux hyp hμ he).2.2.2 Q hQ J
  refine (tendsto_add_atTop_iff_nat 1).1 (tendsto_of_trunc
    (b := fun M N => ∫ X, truncG g M (Ucentered W μ (N + 1) X, fun n => fluct e (N + 1) n X)
      ∂Measure.pi (fun _ : Fin (N + 1) => μm))
    (b0 := fun M => ∫ z, truncG g M (Uinf W μ Q z, fun n => z n) ∂gammaRef)
    (fun M => (hlim (truncG g M)).comp (tendsto_add_atTop_nat 1)) fun ε hε => ?_)
  -- the limit side: dominated convergence in `M`
  have hUm : AEStronglyMeasurable (fun z => rexp (-Uinf W μ Q z)) gammaRef := hint.1
  have hgm : Continuous fun z : ℕ → ℝ => g fun n : Fin J => z n :=
    g.continuous.comp (continuous_pi fun n => continuous_apply _)
  have h0 : Tendsto (fun M : ℝ => ∫ z, truncG g M (Uinf W μ Q z, fun n => z n) ∂gammaRef) atTop
      (𝓝 (∫ z, g (fun n => z n) * rexp (-Uinf W μ Q z) ∂gammaRef)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖g‖ * rexp (-Uinf W μ Q z))
      (Eventually.of_forall fun M => ?_) ?_ (hint.const_mul _) (Eventually.of_forall fun z => ?_)
    · simp only [truncG_apply]
      exact hgm.aestronglyMeasurable.mul (hUm.inf aestronglyMeasurable_const)
    · filter_upwards [eventually_ge_atTop 0] with M hM
      refine Eventually.of_forall fun z => ?_
      rw [truncG_apply, norm_mul]
      refine mul_le_mul (g.norm_coe_le_norm _) ?_ (norm_nonneg _) (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (Real.exp_pos _).le hM)]
      exact min_le_left _ _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (rexp (-Uinf W μ Q z))] with M hM
      rw [truncG_apply, min_eq_left hM]
  have hev1 : ∀ᶠ M in atTop, |∫ z, g (fun n => z n) * rexp (-Uinf W μ Q z) ∂gammaRef -
      ∫ z, truncG g M (Uinf W μ Q z, fun n => z n) ∂gammaRef| ≤ ε := by
    filter_upwards [Metric.tendsto_nhds.1 h0 ε hε] with M hM
    rw [Real.dist_eq, abs_sub_comm] at hM; exact hM.le
  set B' := max B 0
  have h1 : Tendsto (fun M : ℝ => ‖g‖ * (M ^ (1 - p) * B')) atTop (𝓝 (‖g‖ * (0 * B'))) := by
    have := tendsto_rpow_neg_atTop (y := p - 1) (by linarith)
    rw [show -(p - 1) = 1 - p by ring] at this
    exact (this.mul_const B').const_mul ‖g‖
  rw [zero_mul, mul_zero] at h1
  obtain ⟨M, ⟨hM1, hM2⟩, hM0⟩ := ((hev1.and (h1.eventually (ge_mem_nhds hε))).and
    (eventually_gt_atTop 0)).exists
  refine ⟨M, fun n => ?_, hM1⟩
  set N := n + 1
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μm N
  have hUm := measurable_Ucentered hyp μm N
  have hw0 : ∀ X : Config N d, 0 ≤ rexp (-Ucentered W μ N X) := fun X => (Real.exp_pos _).le
  have hwb : ∀ X : Config N d, ‖rexp (-Ucentered W μ N X)‖ ≤ rexp BU := fun X => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 X)]
    exact Real.exp_le_exp.2 (by have := hBU X; rw [abs_le] at this; linarith)
  have hwi : Integrable (fun X : Config N d => rexp (-Ucentered W μ N X))
      (Measure.pi fun _ : Fin N => μm) :=
    Integrable.of_bound (hUm.neg.exp).aestronglyMeasurable _ (Eventually.of_forall hwb)
  have hwq : Integrable (fun X : Config N d => rexp (-Ucentered W μ N X) ^ p)
      (Measure.pi fun _ : Fin N => μm) := by
    refine Integrable.of_bound ((hUm.neg.exp).pow_const p).aestronglyMeasurable (rexp BU ^ p)
      (Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hw0 X) p)]
    have := hwb X
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 X)] at this
    exact Real.rpow_le_rpow (hw0 X) this (by linarith)
  have h2 := abs_integral_sub_min_le (h := fun X : Config N d => g fun n => fluct e N n X)
    hw0 hwi hp.le hwq hM0 (c := ‖g‖) (fun X => by
      rw [← Real.norm_eq_abs]; exact g.norm_coe_le_norm _)
    (aestronglyMeasurable_g_fluct hyp hμ he g N)
  simp only [truncG_apply]
  refine h2.trans ?_
  have h3 : ∫ X, rexp (-Ucentered W μ N X) ^ p ∂Measure.pi (fun _ : Fin N => μm) ≤ B' :=
    (hB N (Nat.le_add_left 1 n)).trans (le_max_left _ _)
  calc ‖g‖ * M ^ (1 - p) * ∫ X, rexp (-Ucentered W μ N X) ^ p ∂Measure.pi (fun _ : Fin N => μm)
      ≤ ‖g‖ * (M ^ (1 - p) * B') := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hM0.le _)) (norm_nonneg _)
    _ ≤ ε := hM2

end gibbs

end SharpLSI
