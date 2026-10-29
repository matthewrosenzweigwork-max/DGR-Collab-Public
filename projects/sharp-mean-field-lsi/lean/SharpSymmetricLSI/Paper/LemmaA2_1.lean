import SharpSymmetricLSI.Paper.ELEquation
import SharpSymmetricLSI.Paper.SemiconvexLip2
import SharpSymmetricLSI.Infra.ChainRule
import SharpSymmetricLSI.Infra.TorusLift

/-!
# R25 (A.9), part 1: semiconvexity of `Q = -log μ`

For the minimizer `μ = ρ m`, `ρ = e^{-V-W*μ}/Z`, so `-log ρ = V + W*μ + log Z`.
* `slice_semiconvex`: for fixed `y`, `x ↦ W(x,y)` satisfies `D²W(·,y) ≥ -K_W` distributionally
  (test the joint hypothesis with `φ(x) φₙ(y - z)` and let `n → ∞`);
* `convMeas_semiconvex`: hence `W*ν` does, for every probability measure `ν` (Fubini);
* `ae_eq_of_withDensity_eq`: if `μ = p m = ρ m` with `p > 0` arbitrary (not assumed measurable),
  `ρ` continuous and positive, and `(-log p ∘ liftT) s` is integrable, then it equals
  `(-log ρ ∘ liftT) s` a.e.;
* `semiconvex_negLog`: the semiconvexity clause of (A.9) with `K_Q = K_V + K_W`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

section prodDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_mul_fst_apply {f g : E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (p : E × E) (v : E) :
    fderiv ℝ (fun q : E × E => f q.1 * g q.2) p (v, 0) = fderiv ℝ f p.1 v * g p.2 := by
  have h := ((hf p.1).hasFDerivAt.comp p hasFDerivAt_fst).mul
    ((hg p.2).hasFDerivAt.comp p hasFDerivAt_snd)
  have h' : HasFDerivAt (fun q : E × E => f q.1 * g q.2) _ p := h
  rw [h'.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    map_zero, smul_eq_mul, mul_zero, zero_add, Function.comp_apply]
  ring

theorem secondDirDeriv_mul_fst {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (p : E × E) (v : E) :
    secondDirDeriv (fun q : E × E => f q.1 * g q.2) (v, 0) p = secondDirDeriv f v p.1 * g p.2 := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by simp)
  have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
  have hf' : Differentiable ℝ (fun y => fderiv ℝ f y v) :=
    ((hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).differentiable (by simp)
  unfold secondDirDeriv
  have e : (fun q : E × E => fderiv ℝ (fun q : E × E => f q.1 * g q.2) q (v, 0)) =
      fun q => (fun y => fderiv ℝ f y v) q.1 * g q.2 := by
    funext q; exact fderiv_mul_fst_apply hf1 hg1 q v
  rw [e, fderiv_mul_fst_apply hf' hg1]

theorem hasCompactSupport_mul_prod {f g : E → ℝ} (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (fun q : E × E => f q.1 * g q.2) := by
  refine HasCompactSupport.intro (hf.isCompact.prod hg.isCompact) fun q hq => ?_
  rcases not_and_or.mp (mt (fun h => Set.mk_mem_prod h.1 h.2) hq) with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

end prodDeriv

theorem contDiff_secondDirDeriv_aux {ι : Type*} [Fintype ι] {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (ξ : ι → ℝ) : Continuous (secondDirDeriv φ ξ) := by
  have h1 : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y ξ) :=
    (hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  exact (h1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem hasCompactSupport_secondDirDeriv {ι : Type*} [Fintype ι] {φ : (ι → ℝ) → ℝ}
    (hφc : HasCompactSupport φ) (ξ : ι → ℝ) : HasCompactSupport (secondDirDeriv φ ξ) :=
  (hφc.fderiv_apply (𝕜 := ℝ) ξ).fderiv_apply (𝕜 := ℝ) ξ

theorem integral_secondDirDeriv {ι : Type*} [Fintype ι] [DecidableEq ι] {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (ξ : ι → ℝ) : ∫ x, secondDirDeriv φ ξ x = 0 :=
  integral_fderiv_eq_zero ((hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const)
    (hφc.fderiv_apply (𝕜 := ℝ) ξ) ξ

theorem integrable_comp_liftT_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {u : UnitAddTorus ι → ℝ}
    (hu : Continuous u) {φ : (ι → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (ξ : ι → ℝ) : Integrable (fun x => u (liftT x) * secondDirDeriv φ ξ x) :=
  ((hu.comp continuous_liftT).mul (contDiff_secondDirDeriv_aux hφ ξ)).integrable_of_hasCompactSupport
    (hasCompactSupport_secondDirDeriv hφc ξ).mul_left

section semiconvex

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem exists_bound_W (hyp : Hyp V W KV KW) : ∃ B : ℝ, ∀ x y, |W x y| ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_univ.image (hyp.continuous_W)).isBounded.exists_norm_le
  exact ⟨B, fun x y => hB _ ⟨(x, y), trivial, rfl⟩⟩

/-- `x ↦ ∫ W(lift x, z) s(x) dx` is continuous in `z`. -/
theorem continuous_slice_integral (hyp : Hyp V W KV KW) {s : (Fin d → ℝ) → ℝ}
    (hs : Integrable s) (hsc : Continuous s) :
    Continuous fun z : Torus d => ∫ x, W (liftT x) z * s x := by
  obtain ⟨B, hB⟩ := exists_bound_W hyp
  refine continuous_of_dominated (bound := fun x => B * |s x|) (fun z => ?_) (fun z => ?_)
    (hs.abs.const_mul B) (Eventually.of_forall fun x => ?_)
  · exact ((hyp.continuous_W.comp ((continuous_liftT).prodMk continuous_const)).mul
      hsc).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hB _ _) (abs_nonneg _)
  · exact (hyp.continuous_W.comp (continuous_const.prodMk continuous_id)).mul continuous_const

/-- **Slices of `W` are semiconvex.** -/
theorem slice_semiconvex (hyp : Hyp V W KV KW) (y : Torus d) {φ : (Fin d → ℝ) → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) (ξ : Fin d → ℝ) :
    -KW * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤ ∫ x, W (liftT x) y * secondDirDeriv φ ξ x := by
  set s := secondDirDeriv φ ξ
  have hsc : Continuous s := contDiff_secondDirDeriv_aux hφ ξ
  have hs : Integrable s := hsc.integrable_of_hasCompactSupport (hasCompactSupport_secondDirDeriv hφc ξ)
  set g : Torus d → ℝ := fun z => ∫ x, W (liftT x) z * s x
  have hg : Continuous g := continuous_slice_integral hyp hs hsc
  obtain ⟨B, hB⟩ := exists_bound_W hyp
  have hlim := tendsto_mollL_apply hg (secT y)
  rw [liftT_secT] at hlim
  refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  set ψ : (Fin d → ℝ) → ℝ := fun z => phiSeq n (secT y - z)
  have hψ : ContDiff ℝ ∞ ψ := (contDiff_phiSeq n).comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := (hasCompactSupport_phiSeq n).comp_homeomorph
    (Homeomorph.subLeft (secT y))
  have hψi : ∫ z, ψ z = 1 := by
    rw [integral_sub_left_eq_self (fun t => phiSeq n t) volume (secT y)]; exact integral_phiSeq n
  have hψint : Integrable ψ := hψ.continuous.integrable_of_hasCompactSupport hψc
  have h := hyp.semiconvex_W (fun q => φ q.1 * ψ q.2) (hφ.comp contDiff_fst |>.mul
    (hψ.comp contDiff_snd)) (hasCompactSupport_mul_prod hφc hψc)
    (fun q => mul_nonneg (hφ0 _) (phiSeq_nonneg n _)) (ξ, 0)
  simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, add_zero] at h
  have e1 : ∫ q : (Fin d → ℝ) × (Fin d → ℝ), φ q.1 * ψ q.2 = ∫ x, φ x :=
    by rw [show (volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))) = volume.prod volume from rfl,
      integral_prod_mul, hψi, mul_one]
  rw [e1] at h
  simp_rw [secondDirDeriv_mul_fst hφ hψ] at h
  refine h.trans (le_of_eq ?_)
  have hint : Integrable (fun q : (Fin d → ℝ) × (Fin d → ℝ) =>
      W (liftT q.1) (liftT q.2) * (s q.1 * ψ q.2)) (volume.prod volume) := by
    refine (hs.mul_prod hψint).bdd_mul (c := B) ?_ (Eventually.of_forall fun q => ?_)
    · exact (hyp.continuous_W.comp ((continuous_liftT.comp continuous_fst).prodMk
        (continuous_liftT.comp continuous_snd))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hB _ _
  rw [show (volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))) = volume.prod volume from rfl,
    integral_prod_symm _ hint, mollL_apply]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [g, Function.comp]
  rw [← integral_mul_const]
  congr 1; funext x; ring

/-- **`W*ν` is semiconvex** for every probability measure `ν`. -/
theorem convMeas_semiconvex (hyp : Hyp V W KV KW) (ν : Measure (Torus d)) [IsProbabilityMeasure ν]
    {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (ξ : Fin d → ℝ) :
    -KW * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤ ∫ x, convMeas W ν (liftT x) * secondDirDeriv φ ξ x := by
  set s := secondDirDeriv φ ξ
  have hsc : Continuous s := contDiff_secondDirDeriv_aux hφ ξ
  have hs : Integrable s := hsc.integrable_of_hasCompactSupport (hasCompactSupport_secondDirDeriv hφc ξ)
  obtain ⟨B, hB⟩ := exists_bound_W hyp
  have hint : Integrable (Function.uncurry fun x y => W (liftT x) y * s x) (volume.prod ν) := by
    have h1 : Integrable (fun q : (Fin d → ℝ) × Torus d => s q.1 * (fun _ : Torus d => (1 : ℝ)) q.2)
        (volume.prod ν) := hs.mul_prod (integrable_const _)
    have h2 := h1.bdd_mul (c := B) (f := fun q : (Fin d → ℝ) × Torus d => W (liftT q.1) q.2)
      (hyp.continuous_W.comp ((continuous_liftT.comp continuous_fst).prodMk
        continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hB _ _)
    refine h2.congr (Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, mul_one]
  have e : ∫ x, convMeas W ν (liftT x) * s x = ∫ y, (∫ x, W (liftT x) y * s x) ∂ν := by
    rw [← integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [convMeas]
    rw [integral_mul_const]
  rw [e]
  calc -KW * (∑ k, ξ k ^ 2) * ∫ x, φ x = ∫ _y, (-KW * (∑ k, ξ k ^ 2) * ∫ x, φ x) ∂ν := by simp
    _ ≤ ∫ y, (∫ x, W (liftT x) y * s x) ∂ν :=
        integral_mono (integrable_const _) hint.integral_prod_right
          fun y => slice_semiconvex hyp y hφ hφc hφ0 ξ

end semiconvex

end SharpLSI
