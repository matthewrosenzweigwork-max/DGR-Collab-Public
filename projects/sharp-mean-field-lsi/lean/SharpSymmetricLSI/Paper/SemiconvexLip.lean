import SharpSymmetricLSI.Infra.Mollify
import SharpSymmetricLSI.Infra.Calculus
import SharpSymmetricLSI.Infra.Periodic
import SharpSymmetricLSI.Defs.D02_Hypotheses

/-!
# Semiconvex periodic functions are Lipschitz (Phase 3, lane D; R6 infrastructure)

If `u` is continuous on `𝕋^ι` and `∂ₖ²u ≥ -K` in the sense of distributions for every coordinate
direction, then every mollification satisfies `|∂ₖ(u ⋆ φₙ)| ≤ K/2` (periodicity + Taylor), so
`u ∘ liftT` is Lipschitz with constant `K |ι| / 2`.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal NNReal Convolution

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Distributional coordinate semiconvexity `∂ₖ²u ≥ -K`. -/
def CoordSemiconvex (u : UnitAddTorus ι → ℝ) (K : ℝ) : Prop :=
  ∀ φ : (ι → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) → ∀ k : ι,
    -K * ∫ x, φ x ≤ ∫ x, u (liftT x) * secondDirDeriv φ (Pi.single k 1) x

/-- Convolution with a smooth compactly supported kernel. -/
noncomputable def convR (F ψ : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ψ : (ι → ℝ) → ℝ)

theorem convR_apply (F ψ : (ι → ℝ) → ℝ) (x : ι → ℝ) : convR F ψ x = ∫ t, F t * ψ (x - t) := rfl

theorem mollL_eq_convR (n : ℕ) (F : (ι → ℝ) → ℝ) : mollL n F = convR F (phiSeq n) := rfl

theorem hasFDerivAt_convR_dir {F ψ : (ι → ℝ) → ℝ} (hF : LocallyIntegrable F volume)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (y v : ι → ℝ) :
    HasFDerivAt (convR F ψ) (fderiv ℝ (convR F ψ) y) y ∧
      fderiv ℝ (convR F ψ) y v = convR F (fun z => fderiv ℝ ψ z v) y := by
  have h := hψc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ) hF
    (hψ.of_le (by simp)) y
  refine ⟨h.differentiableAt.hasFDerivAt, ?_⟩
  change fderiv ℝ (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ψ) y v = _
  rw [h.fderiv, convolution_precompR_apply _ hF (hψc.fderiv (𝕜 := ℝ))
    (hψ.continuous_fderiv (by simp))]
  rfl

theorem hasDerivAt_convR_line {F ψ : (ι → ℝ) → ℝ} (hF : LocallyIntegrable F volume)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (x v : ι → ℝ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => convR F ψ (x + s • v)) (convR F (fun z => fderiv ℝ ψ z v) (x + s • v))
      s := by
  obtain ⟨h1, h2⟩ := hasFDerivAt_convR_dir hF hψ hψc (x + s • v) v
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have := h1.comp_hasDerivAt s hl
  rw [h2] at this
  exact this

theorem fderiv_comp_sub_apply {f : (ι → ℝ) → ℝ} (hf : Differentiable ℝ f) (y t v : ι → ℝ) :
    fderiv ℝ (fun t => f (y - t)) t v = -fderiv ℝ f (y - t) v := by
  have h : HasFDerivAt (fun t => f (y - t))
      ((fderiv ℝ f (y - t)).comp (-ContinuousLinearMap.id ℝ (ι → ℝ))) t :=
    (hf (y - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub y)
  rw [h.fderiv]
  simp

theorem fderiv_neg_comp_sub_apply {g : (ι → ℝ) → ℝ} (hg : Differentiable ℝ g) (y t v : ι → ℝ) :
    fderiv ℝ (fun t => -g (y - t)) t v = fderiv ℝ g (y - t) v := by
  have h : HasFDerivAt (fun t => -g (y - t))
      (-((fderiv ℝ g (y - t)).comp (-ContinuousLinearMap.id ℝ (ι → ℝ)))) t :=
    ((hg (y - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub y)).neg
  rw [h.fderiv]
  simp

theorem secondDirDeriv_comp_sub {f : (ι → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (y t v : ι → ℝ) :
    secondDirDeriv (fun t => f (y - t)) v t = secondDirDeriv f v (y - t) := by
  have hd : Differentiable ℝ f := hf.differentiable (by simp)
  have hd' : Differentiable ℝ (fun z => fderiv ℝ f z v) :=
    ((hf.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  unfold secondDirDeriv
  have e : (fun t => fderiv ℝ (fun t => f (y - t)) t v) = fun t => -fderiv ℝ f (y - t) v := by
    funext t; exact fderiv_comp_sub_apply hd y t v
  rw [e]
  exact fderiv_neg_comp_sub_apply hd' y t v

/-- The mollifier kernel reflected at `y`, as a test function. -/
theorem secondDeriv_moll_ge {u : UnitAddTorus ι → ℝ} (hu : Continuous u) {K : ℝ}
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

theorem fderiv_phiSeq_dir_contDiff (n : ℕ) (v : ι → ℝ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ (phiSeq (ι := ι) n) z v) :=
  ((contDiff_phiSeq n).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- `|∂ₖ (u ⋆ φₙ)| ≤ K/2`. -/
theorem abs_fderiv_mollL_le {u : UnitAddTorus ι → ℝ} (hu : Continuous u) {K : ℝ}
    (hK : CoordSemiconvex u K) (n : ℕ) (k : ι) (x : ι → ℝ) :
    |fderiv ℝ (mollL n (u ∘ liftT)) x (Pi.single k 1)| ≤ K / 2 := by
  set F := u ∘ liftT with hFdef
  have hF : LocallyIntegrable F volume := (hu.comp continuous_liftT).locallyIntegrable
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
  have hG'' : ∀ s, -K ≤ G'' s := fun s => secondDeriv_moll_ge hu hK n k (x + s • v)
  -- periodicity
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

end SharpLSI
