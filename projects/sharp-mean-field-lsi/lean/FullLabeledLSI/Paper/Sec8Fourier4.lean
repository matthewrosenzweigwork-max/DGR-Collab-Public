import FullLabeledLSI.Paper.Sec8Fourier3
import SharpSymmetricLSI.Defs.D02_Hypotheses
import SharpSymmetricLSI.Paper.CosineHyp

/-!
# Section 8.5 (Corollary 8.4), part 4: hypotheses (1.2) for `W(x,y) = G(x-y) - G(0)`

For smooth even `G` on `𝕋^d` the interaction `W` satisfies (1.2) with `K_V = 0` and some `K_W`:
the distributional Hessian of `p ↦ g(p₁ - p₂)` is the pointwise Hessian (two integrations by
parts), bounded below by the (periodic, hence bounded) second derivative of `g`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {d : ℕ}

/-- The interaction `W(x,y) = G(x - y) - G(0)`. -/
noncomputable def WG (G : Torus d → ℝ) (x y : Torus d) : ℝ := G (x - y) - G 0

/-- The linear map `p ↦ p₁ - p₂`. -/
noncomputable def subL (d : ℕ) : ((Fin d → ℝ) × (Fin d → ℝ)) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin d → ℝ) - ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ)

theorem subL_apply (p : (Fin d → ℝ) × (Fin d → ℝ)) : subL d p = p.1 - p.2 := rfl

theorem secondDirDeriv_comp_subL {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (ξ p : (Fin d → ℝ) × (Fin d → ℝ)) :
    secondDirDeriv (fun q => g (subL d q)) ξ p = secondDirDeriv g (subL d ξ) (subL d p) := by
  have hd : Differentiable ℝ g := hg.differentiable (by simp)
  have hd' : Differentiable ℝ (fun z => fderiv ℝ g z (subL d ξ)) :=
    ((hg.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const).differentiable (by simp)
  have e1 : ∀ y, fderiv ℝ (fun q => g (subL d q)) y ξ = fderiv ℝ g (subL d y) (subL d ξ) := by
    intro y
    have h : HasFDerivAt (fun q => g (subL d q))
        ((fderiv ℝ g (subL d y)).comp (subL d : _ →L[ℝ] _)) y :=
      (hd (subL d y)).hasFDerivAt.comp y (subL d).hasFDerivAt
    rw [h.fderiv]; rfl
  unfold secondDirDeriv
  simp_rw [e1]
  have h2 : HasFDerivAt (fun y => fderiv ℝ g (subL d y) (subL d ξ))
      ((fderiv ℝ (fun z => fderiv ℝ g z (subL d ξ)) (subL d p)).comp (subL d : _ →L[ℝ] _)) p :=
    (hd' (subL d p)).hasFDerivAt.comp p (subL d).hasFDerivAt
  rw [h2.fderiv]
  rfl

/-- Two integrations by parts. -/
theorem ibp_sec {w φ : (Fin d → ℝ) × (Fin d → ℝ) → ℝ} (hw : ContDiff ℝ ∞ w)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (ξ : (Fin d → ℝ) × (Fin d → ℝ)) :
    ∫ p, w p * secondDirDeriv φ ξ p = ∫ p, secondDirDeriv w ξ p * φ p := by
  have : (volume : Measure ((Fin d → ℝ) × (Fin d → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure volume volume
  set Dφ := fun p => fderiv ℝ φ p ξ with hDφ
  set Dw := fun p => fderiv ℝ w p ξ with hDw
  have hwd : Differentiable ℝ w := hw.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hDφs : ContDiff ℝ ∞ Dφ := (hφ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hDws : ContDiff ℝ ∞ Dw := (hw.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hDφd : Differentiable ℝ Dφ := hDφs.differentiable (by simp)
  have hDwd : Differentiable ℝ Dw := hDws.differentiable (by simp)
  have hDφc : HasCompactSupport Dφ := hφc.fderiv_apply (𝕜 := ℝ) ξ
  have hD2c : HasCompactSupport fun p => fderiv ℝ Dφ p ξ := hDφc.fderiv_apply (𝕜 := ℝ) ξ
  have hD2cont : Continuous fun p => fderiv ℝ Dφ p ξ :=
    (hDφs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDw2cont : Continuous fun p => fderiv ℝ Dw p ξ :=
    (hDws.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun p => fderiv ℝ w p ξ * Dφ p) volume :=
    (hDws.continuous.mul hDφs.continuous).integrable_of_hasCompactSupport hDφc.mul_left
  have i2 : Integrable (fun p => w p * fderiv ℝ Dφ p ξ) volume :=
    (hw.continuous.mul hD2cont).integrable_of_hasCompactSupport hD2c.mul_left
  have i3 : Integrable (fun p => w p * Dφ p) volume :=
    (hw.continuous.mul hDφs.continuous).integrable_of_hasCompactSupport hDφc.mul_left
  have ibp1 : ∫ p, w p * fderiv ℝ Dφ p ξ = -∫ p, fderiv ℝ w p ξ * Dφ p :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3 (fun p _ => hwd p)
      (fun p _ => hDφd p)
  have j1 : Integrable (fun p => fderiv ℝ Dw p ξ * φ p) volume :=
    (hDw2cont.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have j2 : Integrable (fun p => Dw p * fderiv ℝ φ p ξ) volume :=
    (hDws.continuous.mul hDφs.continuous).integrable_of_hasCompactSupport hDφc.mul_left
  have j3 : Integrable (fun p => Dw p * φ p) volume :=
    (hDws.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have ibp2 : ∫ p, Dw p * fderiv ℝ φ p ξ = -∫ p, fderiv ℝ Dw p ξ * φ p :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable j1 j2 j3 (fun p _ => hDwd p)
      (fun p _ => hφd p)
  have hsecφ : ∀ p, secondDirDeriv φ ξ p = fderiv ℝ Dφ p ξ := fun p => rfl
  have hsecw : ∀ p, secondDirDeriv w ξ p = fderiv ℝ Dw p ξ := fun p => rfl
  simp_rw [hsecφ, hsecw]
  rw [ibp1]
  have : ∫ p, Dw p * fderiv ℝ φ p ξ = ∫ p, fderiv ℝ w p ξ * Dφ p := by
    congr 1
  rw [← this, ibp2, neg_neg]

/-- The second derivative of a periodic smooth `g` is quadratically bounded. -/
theorem exists_hess_bound {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g)
    (hp : ∀ (m : Fin d → ℤ) x, g (x + intVec m) = g x) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z η : Fin d → ℝ, |secondDirDeriv g η z| ≤ M * ∑ i, η i ^ 2 := by
  have hperiod : IsPer g := hp
  have hc : Continuous (fderiv ℝ (fderiv ℝ g)) :=
    (hg.fderiv_right (m := ∞) le_rfl).continuous_fderiv (by simp)
  have hpp : ∀ (m : Fin d → ℤ) x, fderiv ℝ (fderiv ℝ g) (x + intVec m) = fderiv ℝ (fderiv ℝ g) x :=
    fun m x => (hperiod.fderiv.fderiv) m x
  obtain ⟨C, hC⟩ := periodic_bounded hc hpp
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ (fderiv ℝ g) 0)).trans (hC 0)
  refine ⟨C, hC0, fun z η => ?_⟩
  have hd : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  have e : secondDirDeriv g η z = fderiv ℝ (fderiv ℝ g) z η η := by
    unfold secondDirDeriv
    have : (fun y => fderiv ℝ g y η) = fun y => (ContinuousLinearMap.apply ℝ ℝ η) (fderiv ℝ g y) :=
      rfl
    rw [this]
    have h2 : HasFDerivAt (fun y => (ContinuousLinearMap.apply ℝ ℝ η) (fderiv ℝ g y))
        ((ContinuousLinearMap.apply ℝ ℝ η).comp (fderiv ℝ (fderiv ℝ g) z)) z :=
      ((ContinuousLinearMap.apply ℝ ℝ η).hasFDerivAt).comp z (hd z).hasFDerivAt
    rw [h2.fderiv]
    rfl
  rw [e]
  have hnorm : ‖η‖ ^ 2 ≤ ∑ i, η i ^ 2 := by
    have : ‖η‖ ≤ Real.sqrt (∑ i, η i ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => η j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i))
    calc ‖η‖ ^ 2 ≤ Real.sqrt (∑ i, η i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = ∑ i, η i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  calc |fderiv ℝ (fderiv ℝ g) z η η| ≤ ‖fderiv ℝ (fderiv ℝ g) z η η‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖fderiv ℝ (fderiv ℝ g) z η‖ * ‖η‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ g) z‖ * ‖η‖ * ‖η‖ := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖η‖ * ‖η‖ := by gcongr; exact hC z
    _ = C * ‖η‖ ^ 2 := by ring
    _ ≤ C * ∑ i, η i ^ 2 := by gcongr

theorem hyp_WG {G : Torus d → ℝ} (hG : IsSmoothT G) (hGe : ∀ x, G (-x) = G x) :
    ∃ KW : ℝ, Hyp (fun _ : Torus d => (0 : ℝ)) (WG G) 0 KW := by
  set g : (Fin d → ℝ) → ℝ := (G ∘ liftT) - fun _ => G 0 with hgdef
  have hgs : ContDiff ℝ ∞ g := hG.sub contDiff_const
  have hgp : ∀ (m : Fin d → ℤ) x, g (x + intVec m) = g x := fun m x => by
    simp [hgdef, liftT_add_intVec]
  obtain ⟨M, hM0, hM⟩ := exists_hess_bound hgs hgp
  have hGc : Continuous G := continuous_of_isSmoothT hG
  refine ⟨2 * M, le_rfl, by positivity, continuous_const, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Function.uncurry_def, WG]
    exact (hGc.comp (continuous_fst.sub continuous_snd)).sub continuous_const
  · intro φ _ _ _ ξ; simp
  · intro φ hφ hφc hφ0 ξ
    have hw : ContDiff ℝ ∞ (fun q : (Fin d → ℝ) × (Fin d → ℝ) => g (subL d q)) :=
      hgs.comp (subL d).contDiff
    have h1 := ibp_sec hw hφ hφc ξ
    have e : ∀ p : (Fin d → ℝ) × (Fin d → ℝ),
        WG G (liftT p.1) (liftT p.2) = g (subL d p) := fun p => by
      simp only [hgdef, WG, Pi.sub_apply, Function.comp_apply, subL_apply, liftT_sub]
    simp_rw [e]
    rw [h1]
    have hpt : ∀ p, -(2 * M * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2)) * φ p ≤
        secondDirDeriv (fun q => g (subL d q)) ξ p * φ p := by
      intro p
      refine mul_le_mul_of_nonneg_right ?_ (hφ0 p)
      rw [secondDirDeriv_comp_subL hgs]
      have h2 := hM (subL d p) (subL d ξ)
      have h3 : ∑ i, (subL d ξ) i ^ 2 ≤ 2 * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2) := by
        rw [two_mul]
        have : ∑ i, (subL d ξ) i ^ 2 = ∑ i, (ξ.1 i - ξ.2 i) ^ 2 := rfl
        rw [this]
        calc ∑ i, (ξ.1 i - ξ.2 i) ^ 2 ≤ ∑ i, (2 * ξ.1 i ^ 2 + 2 * ξ.2 i ^ 2) :=
              Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (ξ.1 i + ξ.2 i)]
          _ = 2 * ∑ i, ξ.1 i ^ 2 + 2 * ∑ i, ξ.2 i ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          _ = _ := by ring
      have h4 := mul_le_mul_of_nonneg_left h3 hM0
      have := (abs_le.mp h2).1
      nlinarith
    have hi1 : Integrable (fun p => -(2 * M * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2)) * φ p) volume :=
      (continuous_const.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have hDw : ContDiff ℝ ∞ (fun p => secondDirDeriv (fun q => g (subL d q)) ξ p) := by
      have : (fun p => secondDirDeriv (fun q => g (subL d q)) ξ p) =
          fun p => fderiv ℝ (fun y => fderiv ℝ (fun q => g (subL d q)) y ξ) p ξ := rfl
      rw [this]
      have h' : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun q => g (subL d q)) y ξ) :=
        (hw.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
      exact (h'.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have hi2 : Integrable (fun p => secondDirDeriv (fun q => g (subL d q)) ξ p * φ p) volume :=
      (hDw.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have := integral_mono hi1 hi2 hpt
    rw [integral_const_mul] at this
    calc -(2 * M) * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2) * ∫ p, φ p
        = -(2 * M * (∑ k, ξ.1 k ^ 2 + ∑ k, ξ.2 k ^ 2)) * ∫ p, φ p := by ring
      _ ≤ _ := this
  · intro x y
    simp only [WG]
    have : y - x = -(x - y) := by abel
    rw [this, hGe]
  · intro x; simp [WG]

end Sec8
end SharpLSI.FL
