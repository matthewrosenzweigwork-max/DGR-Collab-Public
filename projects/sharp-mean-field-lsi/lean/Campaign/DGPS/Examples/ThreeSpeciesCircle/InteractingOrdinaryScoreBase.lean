import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarSmooth

/-! Actual ordinary-root score systems for comparison with interacting
minimizers. The ordinary variational equation supplies the baseline system;
no ordinary optimizer is treated as an interacting optimizer. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A smooth AE representative satisfying the first physical score equation
identifies its score with the original stored weak gradient only almost
everywhere. No pointwise claim about the stored weak gradient is made. -/
theorem classicalScore_eq_native_ae (h : ℝ) (ρ : AbsoluteDensity 1)
    {v S : Torus 1 → ℝ} (hv : IsSmoothPeriodic v) (hρv : ρ.sqrt =ᵐ[haar 1] v)
    (hvd : ∀ t : ℝ, HasDerivAt (fun s => v (pt s))
      ((S (pt t) + v (pt t) * sigT h (pt t))/2) t) :
    S =ᵐ[haar 1] (fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * sigT h x) := by
  have hg := ((isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hρv
    (ae_eq_refl _)).ae_eq hv.isWeakGradient
  filter_upwards [hg] with x hx
  obtain ⟨t, rfl⟩ := bs_exists_pt x
  have hd := (hasDerivAt_smooth_one hv t).unique (hvd t)
  have hx0 := congrArg (fun z : Tangent 1 => z 0) hx
  rw [smoothGrad_apply] at hx0
  change coordPartial 0 v (pt t) = (S (pt t)+v (pt t)*sigT h (pt t))/2 at hd
  linarith

/-- Any actual ordinary minimizer and positive continuous AE root have the
classical baseline score system and genuinely smooth representatives. The
ordinary first variation is derived from global ordinary minimality. -/
theorem ordinaryOptimizer_classicalScore (h : ℝ) (σ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h σ)
    (hmin : ∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ →
      str025_quot h σ ≤ str025_quot h τ)
    {u : Torus 1 → ℝ} (hu : Continuous u) (hσu : σ.sqrt =ᵐ[haar 1] u)
    (hup : ∀ x, 0 < u x) :
    ∃ S : Torus 1 → ℝ, IsSmoothPeriodic u ∧ IsSmoothPeriodic S ∧
      S =ᵐ[haar 1] (fun x => 2 * weakGradient σ.sqrt σ.sqrt_mem x 0 - u x * sigT h x) ∧
      (∀ t : ℝ, HasDerivAt (fun s => u (pt s))
        ((S (pt t)+u (pt t)*sigT h (pt t))/2) t) ∧
      (∀ t : ℝ, HasDerivAt (fun s => S (pt s))
        (-(S (pt t)*sigT h (pt t))/2 - (str025_quot h σ).toReal *
          (u (pt t)*(Real.log (u (pt t)^2)-ellT h (pt t)))) t) := by
  let a := (str025_quot h σ).toReal
  let AT := fun x => 2 * weakGradient σ.sqrt σ.sqrt_mem x 0 - u x * sigT h x
  let Ru := fun x => u x*(Real.log (u x^2)-ellT h x)
  let g := fun x => -(AT x*sigT h x)/2 - a*Ru x
  have hAT : IsWeakGradient AT (vec1 g) := bs_weak_A h σ hpos hmin hu hσu.symm hup
  obtain ⟨S, hS, hSae, _, _⟩ := circle_H1_holder_half hAT
  have hRu : Continuous Ru := hu.mul
    (((hu.pow 2).log (fun x => pow_ne_zero 2 (hup x).ne')).sub
      (isSmoothPeriodic_ellT h).continuous_torus)
  let gc := fun x => -(S x*sigT h x)/2-a*Ru x
  have hgc : Continuous gc := ((hS.mul (continuous_sigT h)).neg.div_const 2).sub
    (continuous_const.mul hRu)
  have hgae : g =ᵐ[haar 1] gc := by
    filter_upwards [hSae] with x hx
    dsimp only [g, gc]
    rw [hx]
  have hSw : IsWeakGradient S (vec1 g) := hAT.congr_ae hSae.symm (ae_eq_refl _)
  obtain ⟨hSd, _⟩ := circle_duBoisReymond hS hSw (continuous_vec1 hgc) (vec1_ae hgae)
  let ug := fun x => (S x+u x*sigT h x)/2
  have hug : Continuous ug := (hS.add (hu.mul (continuous_sigT h))).div_const 2
  have huw : IsWeakGradient u (weakGradient σ.sqrt σ.sqrt_mem) :=
    (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hσu (ae_eq_refl _)
  have hgrad : weakGradient σ.sqrt σ.sqrt_mem =ᵐ[haar 1] vec1 ug := by
    filter_upwards [hSae] with x hx
    have h0 : weakGradient σ.sqrt σ.sqrt_mem x 0 = ug x := by
      dsimp only [ug]
      have hx' : S x = 2 * weakGradient σ.sqrt σ.sqrt_mem x 0-u x*sigT h x := hx
      linarith
    ext i
    fin_cases i
    simpa [vec1] using h0
  obtain ⟨hud, _⟩ := circle_duBoisReymond hu huw (continuous_vec1 hug) hgrad
  have hud' (t : ℝ) : HasDerivAt (fun s => u (pt s))
      ((S (pt t)+u (pt t)*sigT h (pt t))/2) t := by
    simpa only [vec1_apply] using hud t
  have hSd' (t : ℝ) : HasDerivAt (fun s => S (pt s))
      (-(S (pt t)*sigT h (pt t))/2-a*(u (pt t)*(Real.log (u (pt t)^2)-ellT h (pt t)))) t := by
    simpa only [vec1_apply] using hSd t
  have hsmooth := elementary_classicalScore_smooth h 0 a σ hu hS hup hud' (fun t => by
    simpa [elementaryEulerCorrection, elementaryEulerMultiplier] using hSd' t)
  exact ⟨S, hsmooth.1, hsmooth.2.1, hSae, hud', hSd'⟩

end DGPS.Examples.ThreeSpeciesCircle
