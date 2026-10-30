import DGPS.Examples.ThreeSpeciesCircle.InteractingFixedFieldWeakEuler
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarSmooth

/-! Classical score and smoothness for a fixed actual common field. The root
being regularized belongs to an independent original H1 density; its global
one-body minimum and native common value are the only variational premises. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual fixed-field global minimum gives its genuine physical weak score. -/
theorem elementaryFixedField_globalMin_score_weakGradient
    (h ε r : ℝ) (τ ρ : AbsoluteDensity 1)
    (hmin : ∀ σ : AbsoluteDensity 1,
      (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
          (∫ x, elementaryEulerCorrection h ε r τ x ∂(densityMeasure ρ : Measure (Torus 1))) ≤
        (ordinaryFisher h σ).toReal - 2 * r * (ordinaryEntropy h σ).toReal +
          (∫ x, elementaryEulerCorrection h ε r τ x ∂(densityMeasure σ : Measure (Torus 1))))
    (hvalue : (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
      (∫ x, elementaryEulerCorrection h ε r τ x ∂(densityMeasure ρ : Measure (Torus 1))) =
        elementaryEulerMultiplier h ε r τ)
    (v : Torus 1 → ℝ) (hv : Continuous v) (hae : ρ.sqrt =ᵐ[haar 1] v)
    (hvpos : ∀ x, 0 < v x) :
    let S : Torus 1 → ℝ := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * sigT h x
    IsWeakGradient S (vec1 fun x =>
      -(S x * sigT h x) / 2 + v x * elementaryEulerCorrection h ε r τ x / 2 -
        r * (v x * (Real.log (v x ^ 2) - ellT h x)) -
          elementaryEulerMultiplier h ε r τ * v x / 2) := by
  let lam := elementaryEulerMultiplier h ε r τ
  let Ξ := elementaryEulerCorrection h ε r τ
  let S : Torus 1 → ℝ := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * sigT h x
  let R := fun x => v x * (Real.log (v x ^ 2) - ellT h x)
  have hσ := continuous_sigT h
  have hΞ := (isSmooth_elementaryEulerCorrection h ε r τ).continuous_torus
  have hR : Continuous R :=
    hv.mul (((hv.pow 2).log (fun x => (pow_pos (hvpos x) 2).ne')).sub
      (isSmoothPeriodic_ellT h).continuous_torus)
  have hSmem : MemLp S 2 (haar 1) :=
    ((memLp_coord (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad 0).const_mul 2).sub
      (memLp_two_of_continuous (hv.mul hσ))
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x, |sigT h x| ≤ K := ⟨_, abs_sigT_le h⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hSσ : MemLp (fun x => S x * sigT h x) 2 (haar 1) := by
    refine (hSmem.const_mul K).mono
      (hSmem.aestronglyMeasurable.mul hσ.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK0]
    nlinarith [hK x, abs_nonneg (S x)]
  have hg : MemLp (fun x => -(S x * sigT h x) / 2 + v x * Ξ x / 2 -
      r * R x - lam * v x / 2) 2 (haar 1) := by
    have hmem := (((hSσ.const_mul (-(1 / 2 : ℝ))).add
      ((memLp_two_of_continuous (hv.mul hΞ)).const_mul (1 / 2 : ℝ))).sub
        ((memLp_two_of_continuous hR).const_mul r)).sub
          ((memLp_two_of_continuous hv).const_mul (lam / 2))
    exact hmem.ae_eq (Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Ξ]
      ring)
  refine ⟨hSmem, memLp_vec1 hg, ?_⟩
  intro φ hφ j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have E := elementaryFixedField_globalMin_weakEuler h ε r τ ρ hmin hvalue φ
    (smoothGrad φ) hφ.isWeakGradient
  have hφc := hφ.continuous_torus
  have hφd := hφ.continuous_coordPartial 0
  have i1 : Integrable (fun x => S x * coordPartial 0 φ x) (haar 1) :=
    integrable_mul_of_memLp_two hSmem (bs_memLp_top hφd)
  have i2 : Integrable (fun x => S x * (sigT h x * φ x)) (haar 1) :=
    integrable_mul_of_memLp_two hSmem (bs_memLp_top (hσ.mul hφc))
  have i3 : Integrable (fun x => R x * φ x) (haar 1) :=
    integrable_mul_of_memLp_two (memLp_two_of_continuous hR) (bs_memLp_top hφc)
  have i4 : Integrable (fun x => (v x * Ξ x) * φ x) (haar 1) :=
    integrable_mul_of_memLp_two (memLp_two_of_continuous (hv.mul hΞ)) (bs_memLp_top hφc)
  have i5 : Integrable (fun x => v x * φ x) (haar 1) :=
    integrable_mul_of_memLp_two (memLp_two_of_continuous hv) (bs_memLp_top hφc)
  have hL : (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) *
      (2 * smoothGrad φ x 0 - φ x * logScore h x) ∂haar 1) =
      ∫ x, 2 * (S x * coordPartial 0 φ x) - S x * (sigT h x * φ x) ∂haar 1 := by
    apply integral_congr_ae
    filter_upwards [hae, logScore_ae_eq h] with x hx hσx
    dsimp only [S]
    rw [hx, hσx, smoothGrad_apply]
    ring
  have hX : (∫ x, ρ.sqrt x * φ x * elementaryEulerCorrection h ε r τ x ∂haar 1) =
      ∫ x, (v x * Ξ x) * φ x ∂haar 1 := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
    ring
  have hlog : (∫ x, ρ.sqrt x * φ x *
      (Real.log (ρ.sqrt x ^ 2) - Real.log (referenceDensity h x)) ∂haar 1) =
      ∫ x, R x * φ x ∂haar 1 := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
    change v x * φ x * (Real.log (v x ^ 2) - ellT h x) = _
    dsimp only [R]
    ring
  have hM : (∫ x, ρ.sqrt x * φ x ∂haar 1) = ∫ x, v x * φ x ∂haar 1 := by
    apply integral_congr_ae
    exact hae.mono fun x hx => by
      change ρ.sqrt x * φ x = v x * φ x
      rw [hx]
  change _ + (∫ x, ρ.sqrt x * φ x * elementaryEulerCorrection h ε r τ x ∂haar 1) =
    2 * r * _ + lam * _ at E
  rw [hL, hX, hlog, hM, integral_sub (i1.const_mul 2) i2, integral_const_mul] at E
  have hInt : (∫ x, vec1 (fun x => -(S x * sigT h x) / 2 + v x * Ξ x / 2 -
      r * R x - lam * v x / 2) x 0 * φ x ∂haar 1) =
      -(1 / 2 : ℝ) * (∫ x, S x * (sigT h x * φ x) ∂haar 1) +
        (1 / 2 : ℝ) * (∫ x, (v x * Ξ x) * φ x ∂haar 1) -
          r * (∫ x, R x * φ x ∂haar 1) -
            (lam / 2) * (∫ x, v x * φ x ∂haar 1) := by
    have heq : (fun x => vec1 (fun x => -(S x * sigT h x) / 2 + v x * Ξ x / 2 -
        r * R x - lam * v x / 2) x 0 * φ x) = fun x =>
        (-(1 / 2 : ℝ)) * (S x * (sigT h x * φ x)) +
          (1 / 2 : ℝ) * ((v x * Ξ x) * φ x) - r * (R x * φ x) -
            (lam / 2) * (v x * φ x) := by
      funext x
      simp only [vec1_apply]
      ring
    have i24 : Integrable (fun x => (-(1 / 2 : ℝ)) * (S x * (sigT h x * φ x)) +
        (1 / 2 : ℝ) * ((v x * Ξ x) * φ x)) (haar 1) := by
      exact ((i2.const_mul (-(1 / 2 : ℝ))).add
        (i4.const_mul (1 / 2 : ℝ))).congr (Eventually.of_forall fun x => rfl)
    have i243 : Integrable (fun x => (-(1 / 2 : ℝ)) * (S x * (sigT h x * φ x)) +
        (1 / 2 : ℝ) * ((v x * Ξ x) * φ x) - r * (R x * φ x)) (haar 1) := by
      exact (i24.sub (i3.const_mul r)).congr (Eventually.of_forall fun x => rfl)
    rw [heq, integral_sub i243 (i5.const_mul (lam / 2)),
      integral_sub i24 (i3.const_mul r),
      integral_add (i2.const_mul (-(1 / 2 : ℝ))) (i4.const_mul (1 / 2 : ℝ))]
    simp only [integral_const_mul]
  rw [hInt]
  linarith


/-- A factual positive continuous AE representative of any actual fixed-field
minimum is smooth. The feedback density stays independent of that root. -/
theorem elementaryFixedField_globalMin_smooth
    (h ε r : ℝ) (τ ρ : AbsoluteDensity 1)
    (hmin : ∀ σ : AbsoluteDensity 1,
      (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
          (∫ x, elementaryEulerCorrection h ε r τ x ∂(densityMeasure ρ : Measure (Torus 1))) ≤
        (ordinaryFisher h σ).toReal - 2 * r * (ordinaryEntropy h σ).toReal +
          (∫ x, elementaryEulerCorrection h ε r τ x ∂(densityMeasure σ : Measure (Torus 1))))
    (hvalue : (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
      (∫ x, elementaryEulerCorrection h ε r τ x ∂(densityMeasure ρ : Measure (Torus 1))) =
        elementaryEulerMultiplier h ε r τ)
    (v : Torus 1 → ℝ) (hv : Continuous v) (hae : ρ.sqrt =ᵐ[haar 1] v)
    (hvpos : ∀ x, 0 < v x) :
    ∃ S : Torus 1 → ℝ, Continuous S ∧
      (∀ t : ℝ, HasDerivAt (fun s => v (pt s))
        ((S (pt t) + v (pt t) * sigT h (pt t)) / 2) t) ∧
      (∀ t : ℝ, HasDerivAt (fun s => S (pt s))
        (-(S (pt t) * sigT h (pt t)) / 2 +
          v (pt t) * elementaryEulerCorrection h ε r τ (pt t) / 2 -
            r * (v (pt t) * (Real.log (v (pt t) ^ 2) - ellT h (pt t))) -
              elementaryEulerMultiplier h ε r τ * v (pt t) / 2) t) ∧
      IsSmoothPeriodic v ∧ IsSmoothPeriodic S ∧ IsSmoothPeriodic (fun x => Real.log (v x ^ 2)) := by
  let lam := elementaryEulerMultiplier h ε r τ
  let Ξ := elementaryEulerCorrection h ε r τ
  let AT : Torus 1 → ℝ := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * sigT h x
  let RT := fun x => v x * (Real.log (v x ^ 2) - ellT h x)
  let g := fun x => -(AT x * sigT h x) / 2 + v x * Ξ x / 2 - r * RT x - lam * v x / 2
  have hAT : IsWeakGradient AT (vec1 g) :=
    elementaryFixedField_globalMin_score_weakGradient h ε r τ ρ hmin hvalue v hv hae hvpos
  obtain ⟨Ac, hAc, hAae, _, _⟩ := circle_H1_holder_half hAT
  have hσ := continuous_sigT h
  have hΞ := (isSmooth_elementaryEulerCorrection h ε r τ).continuous_torus
  have hRT : Continuous RT :=
    hv.mul (((hv.pow 2).log (fun x => (pow_pos (hvpos x) 2).ne')).sub
      (isSmoothPeriodic_ellT h).continuous_torus)
  let gc := fun x => -(Ac x * sigT h x) / 2 + v x * Ξ x / 2 - r * RT x - lam * v x / 2
  have hgc : Continuous gc :=
    ((((hAc.mul hσ).neg.div_const 2).add ((hv.mul hΞ).div_const 2)).sub
      (hRT.const_mul r)).sub ((hv.const_mul lam).div_const 2)
  have hgae : g =ᵐ[haar 1] gc := by
    filter_upwards [hAae] with x hx
    dsimp only [g, gc]
    rw [hx]
  have hAw : IsWeakGradient Ac (vec1 g) := hAT.congr_ae hAae.symm (ae_eq_refl _)
  obtain ⟨hAd, _⟩ := circle_duBoisReymond hAc hAw (continuous_vec1 hgc) (vec1_ae hgae)
  have hvw : IsWeakGradient v (weakGradient ρ.sqrt ρ.sqrt_mem) :=
    (isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hae (ae_eq_refl _)
  let vg := fun x => (Ac x + v x * sigT h x) / 2
  have hvg : Continuous vg := (hAc.add (hv.mul hσ)).div_const 2
  have hgrad : weakGradient ρ.sqrt ρ.sqrt_mem =ᵐ[haar 1] vec1 vg := by
    filter_upwards [hAae] with x hx
    have h0 : weakGradient ρ.sqrt ρ.sqrt_mem x 0 = vg x := by
      dsimp only [vg]
      have hx' : Ac x = 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * sigT h x := hx
      linarith
    ext i
    fin_cases i
    simpa [vec1] using h0
  obtain ⟨hvd, _⟩ := circle_duBoisReymond hv hvw (continuous_vec1 hvg) hgrad
  have hvd' : ∀ t : ℝ, HasDerivAt (fun s => v (pt s))
      ((Ac (pt t) + v (pt t) * sigT h (pt t)) / 2) t := by
    intro t
    simpa only [vec1_apply] using hvd t
  have hAd' : ∀ t : ℝ, HasDerivAt (fun s => Ac (pt s))
      (-(Ac (pt t) * sigT h (pt t)) / 2 +
        v (pt t) * elementaryEulerCorrection h ε r τ (pt t) / 2 -
          r * (v (pt t) * (Real.log (v (pt t) ^ 2) - ellT h (pt t))) -
            elementaryEulerMultiplier h ε r τ * v (pt t) / 2) t := by
    intro t
    simpa only [vec1_apply] using hAd t
  obtain ⟨hvsm, hSsm, hlogsm⟩ :=
    elementary_classicalScore_smooth h ε r τ hv hAc hvpos hvd' hAd'
  exact ⟨Ac, hAc, hvd', hAd', hvsm, hSsm, hlogsm⟩

end DGPS.Examples.ThreeSpeciesCircle
