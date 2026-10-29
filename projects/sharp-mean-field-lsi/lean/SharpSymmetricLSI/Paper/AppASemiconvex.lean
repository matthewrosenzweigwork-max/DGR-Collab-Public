import SharpSymmetricLSI.Paper.SemiconvexLip2
import SharpSymmetricLSI.Paper.AscoliSeq
import SharpSymmetricLSI.Paper.TorusLipschitz

/-!
# Appendix A.1: semiconvex periodic functions have bounded Lipschitz representatives

Let `u` be a function on `𝕋^ι` whose lift is locally integrable, with `∂_ξ²u ≥ -K|ξ|²` in the
sense of distributions. The mollifications `uₙ = φₙ ⋆ (u ∘ liftT)` are smooth, periodic, and
satisfy `|∂ₖuₙ| ≤ K/2` (periodicity and Taylor's formula, as in `Paper/SemiconvexLip`; only local
integrability of `u` is needed), hence are uniformly Lipschitz. They converge to `u` almost
everywhere (Lebesgue differentiation), hence are uniformly bounded; by Arzelà–Ascoli a subsequence
converges uniformly to a Lipschitz `v`, and `v = u` a.e.

Route: mollification instead of the heat flow of the TeX (recorded in
`Audit/statement_map_appA.md`).
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal Convolution

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Directional semiconvexity implies coordinate semiconvexity. -/
theorem coordSemiconvex_of_dir {u : UnitAddTorus ι → ℝ} {K : ℝ}
    (hsc : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : ι → ℝ, -K * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤ ∫ x, u (liftT x) * secondDirDeriv φ ξ x) :
    CoordSemiconvex u K := by
  intro φ hφ hφc hφ0 k
  have h := hsc φ hφ hφc hφ0 (Pi.single k 1)
  have : ∑ j, (Pi.single k (1 : ℝ) : ι → ℝ) j ^ 2 = 1 := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  rwa [this, mul_one] at h

/-- `-K ≤ ∂ₖ²(u ⋆ φₙ)` (no continuity needed). -/
theorem secondDeriv_moll_ge' {u : UnitAddTorus ι → ℝ} {K : ℝ}
    (hK : CoordSemiconvex u K) (n : ℕ) (k : ι) (y : ι → ℝ) :
    -K ≤ convR (u ∘ liftT) (fun z => secondDirDeriv (phiSeq n) (Pi.single k 1) z) y := by
  set ψ := phiSeq (ι := ι) n
  have hψ : ContDiff ℝ ∞ ψ := contDiff_phiSeq n
  have hψc : HasCompactSupport ψ := hasCompactSupport_phiSeq n
  have hφ : ContDiff ℝ ∞ (fun t => ψ (y - t)) := hψ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun t => ψ (y - t)) := by
    have := hψc.comp_homeomorph (Homeomorph.subLeft y)
    exact this
  have h := hK (fun t => ψ (y - t)) hφ hφc (fun t => phiSeq_nonneg n _) k
  have hint : ∫ t, ψ (y - t) = 1 := by
    rw [integral_sub_left_eq_self (fun t => ψ t) volume y]; exact integral_phiSeq n
  rw [hint, mul_one] at h
  simp_rw [secondDirDeriv_comp_sub hψ y] at h
  rw [convR_apply]
  exact h

/-- `|∂ₖ (u ⋆ φₙ)| ≤ K/2` for locally integrable `u`. -/
theorem abs_fderiv_mollL_le' {u : UnitAddTorus ι → ℝ} (hF : LocallyIntegrable (u ∘ liftT) volume)
    {K : ℝ} (hK : CoordSemiconvex u K) (n : ℕ) (k : ι) (x : ι → ℝ) :
    |fderiv ℝ (mollL n (u ∘ liftT)) x (Pi.single k 1)| ≤ K / 2 := by
  set F := u ∘ liftT with hFdef
  set ψ := phiSeq (ι := ι) n
  have hψ : ContDiff ℝ ∞ ψ := contDiff_phiSeq n
  have hψc : HasCompactSupport ψ := hasCompactSupport_phiSeq n
  set v : ι → ℝ := Pi.single k 1
  set ψv : (ι → ℝ) → ℝ := fun z => fderiv ℝ ψ z v
  have hψv : ContDiff ℝ ∞ ψv := fderiv_phiSeq_dir_contDiff n v
  have hψvc : HasCompactSupport ψv := hψc.fderiv_apply (𝕜 := ℝ) v
  have hmol : mollL n (u ∘ liftT) = convR F ψ := rfl
  set G : ℝ → ℝ := fun s => convR F ψ (x + s • v)
  set G' : ℝ → ℝ := fun s => convR F ψv (x + s • v)
  set G'' : ℝ → ℝ := fun s => convR F (fun z => fderiv ℝ ψv z v) (x + s • v)
  have dG : ∀ s, HasDerivAt G (G' s) s := hasDerivAt_convR_line hF hψ hψc x v
  have dG' : ∀ s, HasDerivAt G' (G'' s) s := hasDerivAt_convR_line hF hψv hψvc x v
  have hG'' : ∀ s, -K ≤ G'' s := fun s => secondDeriv_moll_ge' hK n k (x + s • v)
  have hper : ∀ m : ℤ, G m = G 0 := fun m => by
    simp only [G, zero_smul, add_zero]
    have : x + (m : ℝ) • v = x + intVec (Pi.single k m) := by
      funext i; simp only [v, intVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    rw [this, ← hmol]
    exact mollL_comp_liftT_add n u x _
  have t1 := taylor2 (f := fun s => -G s) (f' := fun s => -G' s) (f'' := fun s => -G'' s)
    (x₀ := 0) (x := 1) (K := K) (fun s _ => (dG s).neg) (fun s _ => (dG' s).neg)
    (fun s _ => by linarith [hG'' s])
  have t2 := taylor2 (f := fun s => -G s) (f' := fun s => -G' s) (f'' := fun s => -G'' s)
    (x₀ := 0) (x := -1) (K := K) (fun s _ => (dG s).neg) (fun s _ => (dG' s).neg)
    (fun s _ => by linarith [hG'' s])
  have p1 := hper 1
  have p2 := hper (-1)
  push_cast at p1 p2
  have e : fderiv ℝ (mollL n (u ∘ liftT)) x v = G' 0 := by
    have := (hasFDerivAt_convR_dir hF hψ hψc x v).2
    simp only [G', zero_smul, add_zero, hmol]
    exact this
  rw [e, abs_le]
  norm_num at t1 t2 p1 p2
  constructor <;> linarith

/-- Uniform Lipschitz bound for the mollifications. -/
theorem lipschitz_mollL' {u : UnitAddTorus ι → ℝ} (hF : LocallyIntegrable (u ∘ liftT) volume)
    {K : ℝ} (hK0 : 0 ≤ K) (hK : CoordSemiconvex u K) (n : ℕ) :
    LipschitzWith (Real.toNNReal (K * Fintype.card ι / 2)) (mollL n (u ∘ liftT)) := by
  have hd : Differentiable ℝ (mollL n (u ∘ liftT)) :=
    (contDiff_mollL n hF).differentiable (by simp)
  refine lipschitzWith_of_nnnorm_fderiv_le hd fun x => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = ∑ k, v k • (Pi.single k 1 : ι → ℝ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun k _ => ?_
    funext j; by_cases h : j = k
    · subst h; simp
    · simp [h]
  rw [hv, map_sum]
  simp_rw [map_smul, smul_eq_mul]
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |v k * fderiv ℝ (mollL n (u ∘ liftT)) x (Pi.single k 1)|
      ≤ ∑ _k : ι, ‖∑ k, v k • (Pi.single k 1 : ι → ℝ)‖ * (K / 2) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        refine mul_le_mul ?_ (abs_fderiv_mollL_le' hF hK n k x) (abs_nonneg _) (by positivity)
        rw [← hv]; exact norm_le_pi_norm v k
    _ = K * Fintype.card ι / 2 * ‖∑ k, v k • (Pi.single k 1 : ι → ℝ)‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

omit [DecidableEq ι] in
/-- Mollifications converge almost everywhere (Lebesgue differentiation). -/
theorem ae_tendsto_mollL {F : (ι → ℝ) → ℝ} (hF : LocallyIntegrable F volume) :
    ∀ᵐ x, Tendsto (fun n => mollL n F x) atTop (𝓝 (F x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun n : ℕ => bumpSeq (ι := ι) n) (l := atTop) (K := 2) tendsto_rOut_bumpSeq
    (Eventually.of_forall fun n => by
      simp only [bumpSeq]; rw [mul_one_div]) hF
  filter_upwards [h] with x hx
  refine hx.congr fun n => ?_
  rw [mollL_apply', convolution_def]
  rfl

/-- If `K < 0` on a nonempty index type, there are no such functions; in general the
mollification bound forces `0 ≤ K` once `ι` is nonempty. -/
theorem K_nonneg_of_coordSemiconvex [Nonempty ι] {u : UnitAddTorus ι → ℝ}
    (hF : LocallyIntegrable (u ∘ liftT) volume) {K : ℝ} (hK : CoordSemiconvex u K) : 0 ≤ K := by
  obtain ⟨k⟩ := ‹Nonempty ι›
  have := abs_fderiv_mollL_le' hF hK 0 k 0
  linarith [abs_nonneg (fderiv ℝ (mollL 0 (u ∘ liftT)) 0 (Pi.single k 1))]

instance isOpenPosMeasure_torus : (volume : Measure (UnitAddTorus ι)).IsOpenPosMeasure :=
  Measure.pi.isOpenPosMeasure _

/-- **Appendix A.1, semiconvex functions.** -/
theorem semiconvex_lipschitz_aux {u : UnitAddTorus ι → ℝ} {K : ℝ}
    (hloc : LocallyIntegrable (u ∘ liftT))
    (hsc : ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
      ∀ ξ : ι → ℝ, -K * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤ ∫ x, u (liftT x) * secondDirDeriv φ ξ x) :
    ∃ v : UnitAddTorus ι → ℝ, (∃ L, LipschitzWith L v) ∧ (∃ B, ∀ x, |v x| ≤ B) ∧
      v =ᵐ[volume] u ∧ ∀ w : UnitAddTorus ι → ℝ, Continuous w → w =ᵐ[volume] u → w = v := by
  have hK := coordSemiconvex_of_dir hsc
  -- The constant.
  set K' : ℝ := max K 0
  have hK' : CoordSemiconvex u K' := fun φ hφ hφc hφ0 k => by
    refine le_trans ?_ (hK φ hφ hφc hφ0 k)
    have : 0 ≤ ∫ x, φ x := integral_nonneg hφ0
    nlinarith [le_max_left K 0]
  set L : ℝ≥0 := Real.toNNReal (K' * Fintype.card ι / 2)
  have hLip : ∀ n, LipschitzWith L (mollL n (u ∘ liftT)) :=
    lipschitz_mollL' hloc (le_max_right K 0) hK'
  -- A convergence point.
  have hae := ae_tendsto_mollL hloc
  obtain ⟨x₀, hx₀⟩ := hae.exists
  obtain ⟨B₀, hB₀⟩ : ∃ B₀, ∀ n, |mollL n (u ∘ liftT) x₀| ≤ B₀ := by
    obtain ⟨B₀, hB⟩ := (Metric.isBounded_range_of_tendsto _ hx₀).subset_closedBall 0
    exact ⟨B₀, fun n => by
      have := hB ⟨n, rfl⟩
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this⟩
  -- Uniform bound.
  have hbd : ∀ n x, |mollL n (u ∘ liftT) x| ≤ B₀ + L := by
    intro n x
    let m : ι → ℤ := fun i => ⌊x₀ i - x i⌋
    have hd : dist (x + intVec m) x₀ ≤ 1 := by
      refine (dist_pi_le_iff zero_le_one).2 fun i => ?_
      simp only [Pi.add_apply, intVec, Real.dist_eq, m]
      have h1 := Int.floor_le (x₀ i - x i)
      have h2 := Int.lt_floor_add_one (x₀ i - x i)
      rw [abs_le]; constructor <;> linarith
    rw [← mollL_comp_liftT_add n u x m]
    have := (hLip n).dist_le_mul (x + intVec m) x₀
    rw [Real.dist_eq] at this
    have h3 : (L : ℝ) * dist (x + intVec m) x₀ ≤ L := by
      nlinarith [L.2]
    have := abs_sub_abs_le_abs_sub (mollL n (u ∘ liftT) (x + intVec m)) (mollL n (u ∘ liftT) x₀)
    linarith [hB₀ n]
  -- Torus functions.
  have hcomp : ∀ n, moll n u ∘ liftT = mollL n (u ∘ liftT) := fun n => moll_comp_liftT n u
  have hLipT : ∀ n, LipschitzWith L (moll n u) := fun n =>
    lipschitzWith_of_liftT (by rw [hcomp]; exact hLip n)
  have hbdT : ∀ n z, |moll n u z| ≤ B₀ + L := fun n z => by
    rw [← liftT_secT z, ← Function.comp_apply (f := moll n u), hcomp]
    exact hbd n _
  obtain ⟨φ, hφ, v, hv, hunif⟩ := exists_subseq_unif (moll · u) hbdT hLipT
  have hpt : ∀ z, Tendsto (fun n => moll (φ n) u z) atTop (𝓝 (v z)) := by
    intro z
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif (ε / 2) (half_pos hε))
    exact ⟨N, fun n hn => by
      rw [Real.dist_eq]; linarith [hN n hn z]⟩
  refine ⟨v, ⟨L, ?_⟩, ⟨B₀ + L, fun z => ?_⟩, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun a b => ?_
    exact le_of_tendsto' ((hpt a).dist (hpt b)) fun n => (hLipT (φ n)).dist_le_mul a b
  · exact le_of_tendsto' ((continuous_abs.tendsto _).comp (hpt z)) fun n => hbdT (φ n) z
  · have hvu : ∀ᵐ x ∂(volume : Measure (ι → ℝ)), v (liftT x) = u (liftT x) := by
      filter_upwards [hae] with x hx
      have h1 := hpt (liftT x)
      have h2 : Tendsto (fun n => moll (φ n) u (liftT x)) atTop (𝓝 (u (liftT x))) := by
        have := hx.comp hφ.tendsto_atTop
        refine this.congr fun n => ?_
        simp only [Function.comp_apply]
        rw [← Function.comp_apply (f := moll (φ n) u), hcomp]
      exact tendsto_nhds_unique h1 h2
    exact ae_of_ae_liftT (p := fun z => v z = u z) hvu
  · intro w hw hwu
    have hvu : v =ᵐ[volume] u := by
      have hvu' : ∀ᵐ x ∂(volume : Measure (ι → ℝ)), v (liftT x) = u (liftT x) := by
        filter_upwards [hae] with x hx
        have h1 := hpt (liftT x)
        have h2 : Tendsto (fun n => moll (φ n) u (liftT x)) atTop (𝓝 (u (liftT x))) := by
          have := hx.comp hφ.tendsto_atTop
          refine this.congr fun n => ?_
          simp only [Function.comp_apply]
          rw [← Function.comp_apply (f := moll (φ n) u), hcomp]
        exact tendsto_nhds_unique h1 h2
      exact ae_of_ae_liftT (p := fun z => v z = u z) hvu'
    exact (hw.ae_eq_iff_eq volume hv).1 (hwu.trans hvu.symm)

end SharpLSI
