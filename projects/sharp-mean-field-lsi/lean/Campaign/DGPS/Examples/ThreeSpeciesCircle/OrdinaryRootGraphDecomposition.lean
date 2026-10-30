import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootWeakPairing
import DGPS.Frontier.STR029.T24

/-! Exact decomposition of the original full weak-H1 domain along the retained graph.
The finite-dimensional direction is selected by the original Haar Fourier coefficients;
the remaining test is proved to lie in the genuine weak-H1 complement. -/

noncomputable section
open MeasureTheory Filter Set Real
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The derivative of the actual graph has precisely the input harmonic component.
The remaining derivative still takes values in the original closed complement. -/
theorem ordinaryRangeGraph_tangent_harmonic_complement
    {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (θ x v : ℝ × ℝ) (hx : iota_STR02956 θ x ∈ U) :
    ∃ q : E_STR02969,
      fderiv ℝ (Lamp_STR02956 ψ θ) x v =
        v.1 • cosC2_STR02915 + v.2 • sinC2_STR02915 +
          (q : PeriodicC2_STR02969) := by
  let g : ℝ × ℝ → E_STR02969 := fun y => ψ (iota_STR02956 θ y)
  have hg : DifferentiableAt ℝ g x :=
    ((hψC.comp (iota_contDiff_STR02956 θ).contDiffOn (fun y hy => hy)).contDiffAt
      ((isOpen_iota_preimage_STR02956 hU θ).mem_nhds hx)).differentiableAt (by simp)
  have hLf : HasFDerivAt (Lamp_STR02956 ψ θ)
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight cosC2_STR02915 +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight sinC2_STR02915) +
        E_STR02969.subtypeL.comp (fderiv ℝ g x)) x := by
    have h1 : HasFDerivAt (fun y : ℝ × ℝ =>
        y.1 • cosC2_STR02915 + y.2 • sinC2_STR02915)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight cosC2_STR02915 +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight sinC2_STR02915) x :=
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.smul_const cosC2_STR02915).add
        ((ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.smul_const sinC2_STR02915)
    exact h1.add (E_STR02969.subtypeL.hasFDerivAt.comp x hg.hasFDerivAt)
  refine ⟨fderiv ℝ g x v, ?_⟩
  rw [hLf.fderiv]
  rfl

/-- Every actual graph tangent has zero Haar mean and the prescribed first modes. -/
theorem ordinaryRangeGraph_tangent_moments
    {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (θ x v : ℝ × ℝ) (hx : iota_STR02956 θ x ∈ U) :
    let T := fderiv ℝ (Lamp_STR02956 ψ θ) x v
    normInt_STR02933 T.val = 0 ∧
      normInt_STR02933 (fun t => T.val t * Real.cos t) = v.1 / 2 ∧
      normInt_STR02933 (fun t => T.val t * Real.sin t) = v.2 / 2 := by
  obtain ⟨q, hq⟩ := ordinaryRangeGraph_tangent_harmonic_complement hU hψC θ x v hx
  dsimp only
  rw [hq]
  have he : (v.1 • cosC2_STR02915 + v.2 • sinC2_STR02915 +
      (q : PeriodicC2_STR02969)).val =
      uT_STR02901 v.1 v.2 (q : PeriodicC2_STR02969).val :=
    paramMap_val_STR02915 v.1 v.2 q
  rw [he]
  simp only [normInt_eq_meanT_STR02962]
  exact meanT_uT_STR02924 v.1 v.2 (continuous_val_STR02924 _) (inE_of_mem_STR02924 q)

/-- Subtracting the actual graph tangent selected by the original first Fourier
coefficients leaves a full weak-H1 complement test, with no regularity restriction
on the original test beyond its genuine weak derivative. -/
theorem ordinaryRangeGraph_fullWeak_decomposition
    {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (hψC : ContDiffOn ℝ ∞ ψ U)
    (θ x : ℝ × ℝ) (hx : iota_STR02956 θ x ∈ U)
    (f g : ℝ → ℝ) (hf : IsPeriodicWeakDerivative_STR02933 f g)
    (hmean : normInt_STR02933 f = 0) :
    let v : ℝ × ℝ := (cosCoeff_STR02933 f 1, sinCoeff_STR02933 f 1)
    let T := fderiv ℝ (Lamp_STR02956 ψ θ) x v
    let w := fun t => f t - T.val t
    let k := fun t => g t - deriv T.val t
    IsPeriodicWeakDerivative_STR02933 w k ∧
      normInt_STR02933 w = 0 ∧
      normInt_STR02933 (fun t => w t * Real.cos t) = 0 ∧
      normInt_STR02933 (fun t => w t * Real.sin t) = 0 ∧
      (∀ t, f t = T.val t + w t) ∧ (∀ t, g t = deriv T.val t + k t) := by
  let v : ℝ × ℝ := (cosCoeff_STR02933 f 1, sinCoeff_STR02933 f 1)
  let T := fderiv ℝ (Lamp_STR02956 ψ θ) x v
  have hTc : Continuous T.val := continuous_val_STR02924 T
  have hTweak : IsPeriodicWeakDerivative_STR02933 T.val (deriv T.val) :=
    ordinaryRoot_periodicWeak_of_c1 T.val T.isC2.1
      (contDiff_one_iff_deriv.mpr ⟨T.isC2.2.1, T.isC2.2.2.1.continuous⟩)
  have hm := ordinaryRangeGraph_tangent_moments hU hψC θ x v hx
  change normInt_STR02933 T.val = 0 ∧
    normInt_STR02933 (fun t => T.val t * Real.cos t) = v.1 / 2 ∧
    normInt_STR02933 (fun t => T.val t * Real.sin t) = v.2 / 2 at hm
  have hfi := integrable_of_memLp_STR02934 hf.1.2
  have hTi := integrable_continuous_STR02934 hTc
  have hfc : Integrable (fun t => f t * Real.cos t)
      (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [one_mul] using integrable_mul_cos_STR02934 hfi 1
  have hfs : Integrable (fun t => f t * Real.sin t)
      (volume.restrict (Ioc 0 (2 * π))) := by
    simpa only [one_mul] using integrable_mul_sin_STR02934 hfi 1
  have hA : v.1 / 2 = normInt_STR02933 (fun t => f t * Real.cos t) := by
    simp [v, cosCoeff_STR02933]
  have hB : v.2 / 2 = normInt_STR02933 (fun t => f t * Real.sin t) := by
    simp [v, sinCoeff_STR02933]
  change IsPeriodicWeakDerivative_STR02933 (fun t => f t - T.val t)
      (fun t => g t - deriv T.val t) ∧ _
  refine ⟨weakDeriv_sub_STR02935 hf hTweak, ?_, ?_, ?_, ?_, ?_⟩
  · rw [normInt_sub_STR02902 hfi hTi, hmean, hm.1]
    ring
  · have he : (fun t => (f t - T.val t) * Real.cos t) =
        fun t => f t * Real.cos t - T.val t * Real.cos t := by funext t; ring
    rw [he, normInt_sub_STR02902 (f := fun t => f t * Real.cos t)
      (h := fun t => T.val t * Real.cos t) hfc
      (integrable_continuous_STR02934 (hTc.mul Real.continuous_cos)), hm.2.1, hA]
    ring
  · have he : (fun t => (f t - T.val t) * Real.sin t) =
        fun t => f t * Real.sin t - T.val t * Real.sin t := by funext t; ring
    rw [he, normInt_sub_STR02902 (f := fun t => f t * Real.sin t)
      (h := fun t => T.val t * Real.sin t) hfs
      (integrable_continuous_STR02934 (hTc.mul Real.continuous_sin)), hm.2.2, hB]
    ring
  · intro t; ring
  · intro t; ring

end DGPS.Examples.ThreeSpeciesCircle
