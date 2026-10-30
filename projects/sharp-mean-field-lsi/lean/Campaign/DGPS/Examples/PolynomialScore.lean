import DGPS.Examples.PolynomialWeakEuler
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryBootstrap

/-! Actual original-domain polynomial score equation. The continuous entropy
force extends through root zeros, so the weak-score and classical first-order
system do not require a positive-root premise. Logarithmic chart entry and
smooth bootstrapping are separate conclusions. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.PolynomialSpecies

theorem continuous_polynomialEulerCorrection (h r : ℝ) (ρ : AbsoluteDensity 1) :
    Continuous (polynomialEulerCorrection h r ρ) := by
  exact ((((polynomialRankOne h).φ_cont.const_mul _).add
    ((polynomialRankOne h).Aq_cont.const_mul _)).add
      (((polynomialRankOne h).dφ_cont.pow 2).const_mul _))

/-- The actual physical score has its genuine weak derivative for any
continuous representative of an original-domain minimizer, including zeros. -/
theorem polynomial_scalarMinimizer_score_weakGradient (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hmin : scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b)
    (v : Torus 1 → ℝ) (hv : Continuous v) (hae : ρ.sqrt =ᵐ[haar 1] v) :
    let M := polynomialRankOne h
    let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
    let S : Torus 1 → ℝ := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * M.dlogq x
    IsWeakGradient S (vec1 fun x =>
      -(S x * M.dlogq x) / 2 + v x * polynomialEulerCorrection h r ρ x / 2 -
        r * (v x * (Real.log (v x ^ 2) - Real.log (M.q x))) -
          polynomialEulerMultiplier h r ρ * v x / 2) := by
  let M := polynomialRankOne h
  let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
  let lam := polynomialEulerMultiplier h r ρ
  let Ξ := polynomialEulerCorrection h r ρ
  let S : Torus 1 → ℝ := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * M.dlogq x
  let R := fun x => v x * (Real.log (v x ^ 2) - Real.log (M.q x))
  have hσ := M.dlogq_cont
  have hΞ := continuous_polynomialEulerCorrection h r ρ
  have hR : Continuous R := by
    change Continuous (fun x => v x * (Real.log (v x ^ 2) - Real.log (M.q x)))
    have he : (fun x => v x * (Real.log (v x ^ 2) - Real.log (M.q x))) =
        fun x => 2 * (v x * Real.log (v x)) - v x * Real.log (M.q x) := by
      funext x
      rw [Real.log_pow]
      push_cast
      ring
    rw [he]
    exact ((Real.continuous_mul_log.comp hv).const_mul 2).sub
      (hv.mul M.log_smooth.continuous_torus)
  have hSmem : MemLp S 2 (haar 1) :=
    ((memLp_coord (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad 0).const_mul 2).sub
      (memLp_two_of_continuous (hv.mul hσ))
  obtain ⟨K, hKb⟩ := isCompact_univ.exists_bound_of_continuousOn hσ.continuousOn
  have hK : ∀ x, |M.dlogq x| ≤ K := fun x => by
    simpa only [Real.norm_eq_abs] using hKb x (Set.mem_univ x)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hSσ : MemLp (fun x => S x * M.dlogq x) 2 (haar 1) := by
    refine (hSmem.const_mul K).mono
      (hSmem.aestronglyMeasurable.mul hσ.aestronglyMeasurable) ?_
    refine Eventually.of_forall fun x => ?_
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK0]
    nlinarith [hK x, abs_nonneg (S x)]
  have hg : MemLp (fun x => -(S x * M.dlogq x) / 2 + v x * Ξ x / 2 -
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
  have E := polynomial_scalarMinimizer_weakEuler h b ρ hG hmin hφ.isWeakGradient
  have hφc := hφ.continuous_torus
  have hφd := hφ.continuous_coordPartial 0
  have i1 : Integrable (fun x => S x * coordPartial 0 φ x) (haar 1) :=
    integrable_mul_of_memLp_two hSmem (bs_memLp_top hφd)
  have i2 : Integrable (fun x => S x * (M.dlogq x * φ x)) (haar 1) :=
    integrable_mul_of_memLp_two hSmem (bs_memLp_top (hσ.mul hφc))
  have i3 : Integrable (fun x => R x * φ x) (haar 1) :=
    integrable_mul_of_memLp_two (memLp_two_of_continuous hR) (bs_memLp_top hφc)
  have i4 : Integrable (fun x => (v x * Ξ x) * φ x) (haar 1) :=
    integrable_mul_of_memLp_two (memLp_two_of_continuous (hv.mul hΞ)) (bs_memLp_top hφc)
  have i5 : Integrable (fun x => v x * φ x) (haar 1) :=
    integrable_mul_of_memLp_two (memLp_two_of_continuous hv) (bs_memLp_top hφc)
  have hL : (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x) *
      (2 * smoothGrad φ x 0 - φ x * M.dlogq x) ∂haar 1) =
      ∫ x, 2 * (S x * coordPartial 0 φ x) - S x * (M.dlogq x * φ x) ∂haar 1 := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    dsimp only [S]
    rw [hx, smoothGrad_apply]
    ring
  have hX : (∫ x, ρ.sqrt x * φ x * polynomialEulerCorrection h r ρ x ∂haar 1) =
      ∫ x, (v x * Ξ x) * φ x ∂haar 1 := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
    ring
  have hlog : (∫ x, ρ.sqrt x * φ x *
      (Real.log (ρ.sqrt x ^ 2) - Real.log (M.q x)) ∂haar 1) =
      ∫ x, R x * φ x ∂haar 1 := by
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    rw [hx]
    change v x * φ x * (Real.log (v x ^ 2) - Real.log (M.q x)) = _
    dsimp only [R]
    ring
  have hM : (∫ x, ρ.sqrt x * φ x ∂haar 1) = ∫ x, v x * φ x ∂haar 1 := by
    apply integral_congr_ae
    exact hae.mono fun x hx => by
      change ρ.sqrt x * φ x = v x * φ x
      rw [hx]
  change _ + (∫ x, ρ.sqrt x * φ x * polynomialEulerCorrection h r ρ x ∂haar 1) =
    2 * r * _ + lam * _ at E
  rw [hL, hX, hlog, hM, integral_sub (i1.const_mul 2) i2, integral_const_mul] at E
  have hInt : (∫ x, vec1 (fun x => -(S x * M.dlogq x) / 2 + v x * Ξ x / 2 -
      r * R x - lam * v x / 2) x 0 * φ x ∂haar 1) =
      -(1 / 2 : ℝ) * (∫ x, S x * (M.dlogq x * φ x) ∂haar 1) +
        (1 / 2 : ℝ) * (∫ x, (v x * Ξ x) * φ x ∂haar 1) -
          r * (∫ x, R x * φ x ∂haar 1) -
            (lam / 2) * (∫ x, v x * φ x ∂haar 1) := by
    have heq : (fun x => vec1 (fun x => -(S x * M.dlogq x) / 2 + v x * Ξ x / 2 -
        r * R x - lam * v x / 2) x 0 * φ x) = fun x =>
        (-(1 / 2 : ℝ)) * (S x * (M.dlogq x * φ x)) +
          (1 / 2 : ℝ) * ((v x * Ξ x) * φ x) - r * (R x * φ x) -
            (lam / 2) * (v x * φ x) := by
      funext x
      simp only [vec1_apply]
      ring
    have i24 : Integrable (fun x => (-(1 / 2 : ℝ)) * (S x * (M.dlogq x * φ x)) +
        (1 / 2 : ℝ) * ((v x * Ξ x) * φ x)) (haar 1) := by
      exact ((i2.const_mul (-(1 / 2 : ℝ))).add
        (i4.const_mul (1 / 2 : ℝ))).congr (Eventually.of_forall fun x => rfl)
    have i243 : Integrable (fun x => (-(1 / 2 : ℝ)) * (S x * (M.dlogq x * φ x)) +
        (1 / 2 : ℝ) * ((v x * Ξ x) * φ x) - r * (R x * φ x)) (haar 1) := by
      exact (i24.sub (i3.const_mul r)).congr (Eventually.of_forall fun x => rfl)
    rw [heq, integral_sub i243 (i5.const_mul (lam / 2)),
      integral_sub i24 (i3.const_mul r),
      integral_add (i2.const_mul (-(1 / 2 : ℝ))) (i4.const_mul (1 / 2 : ℝ))]
    simp only [integral_const_mul]
  rw [hInt]
  linarith

/-- Every actual original-domain minimizer has a continuous nonnegative root
representative and a genuine classical physical root/score system. Positivity
and quantitative chart entry are not asserted by this theorem. -/
theorem polynomial_scalarMinimizer_classicalScore (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h) ρ)
    (hmin : scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
      scalarRate (canonical_elementary_polynomial_model h) b) :
    let M := polynomialRankOne h
    let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
    ∃ v S : Torus 1 → ℝ, Continuous v ∧ Continuous S ∧ ρ.sqrt =ᵐ[haar 1] v ∧
      (∀ x, 0 ≤ v x) ∧
      (weakGradient ρ.sqrt ρ.sqrt_mem =ᵐ[haar 1]
        vec1 fun x => (S x + v x * M.dlogq x) / 2) ∧
      (∀ t : ℝ, HasDerivAt (fun s => v (pt s))
        ((S (pt t) + v (pt t) * M.dlogq (pt t)) / 2) t) ∧
      (∀ t : ℝ, HasDerivAt (fun s => S (pt s))
        (-(S (pt t) * M.dlogq (pt t)) / 2 +
          v (pt t) * polynomialEulerCorrection h r ρ (pt t) / 2 -
            r * (v (pt t) * (Real.log (v (pt t) ^ 2) - Real.log (M.q (pt t)))) -
              polynomialEulerMultiplier h r ρ * v (pt t) / 2) t) := by
  let M := polynomialRankOne h
  let r := (scalarRate (canonical_elementary_polynomial_model h) b).toReal
  obtain ⟨v, hv, hvae, _, _⟩ := circle_H1_holder_half (isWeakGradient_weakGradient ρ.sqrt_mem)
  have hae : ρ.sqrt =ᵐ[haar 1] v := hvae.symm
  have hvnonneg : ∀ x, 0 ≤ v x := by
    have habs : v =ᵐ[haar 1] fun x => |v x| := by
      filter_upwards [hvae, ρ.sqrt_nonneg] with x hx hp
      rw [hx, abs_of_nonneg hp]
    have he := Measure.eq_of_ae_eq habs hv hv.abs
    intro x
    calc 0 ≤ |v x| := abs_nonneg _
      _ = v x := (congrFun he x).symm
  let lam := polynomialEulerMultiplier h r ρ
  let Ξ := polynomialEulerCorrection h r ρ
  let AT : Torus 1 → ℝ := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * M.dlogq x
  let RT := fun x => v x * (Real.log (v x ^ 2) - Real.log (M.q x))
  let g := fun x => -(AT x * M.dlogq x) / 2 + v x * Ξ x / 2 - r * RT x - lam * v x / 2
  have hAT : IsWeakGradient AT (vec1 g) :=
    polynomial_scalarMinimizer_score_weakGradient h b ρ hG hmin v hv hae
  obtain ⟨Ac, hAc, hAae, _, _⟩ := circle_H1_holder_half hAT
  have hσ := M.dlogq_cont
  have hΞ := continuous_polynomialEulerCorrection h r ρ
  have hRT : Continuous RT := by
    have he : RT = fun x => 2 * (v x * Real.log (v x)) - v x * Real.log (M.q x) := by
      funext x
      dsimp only [RT]
      rw [Real.log_pow]
      push_cast
      ring
    rw [he]
    exact ((Real.continuous_mul_log.comp hv).const_mul 2).sub
      (hv.mul M.log_smooth.continuous_torus)
  let gc := fun x => -(Ac x * M.dlogq x) / 2 + v x * Ξ x / 2 - r * RT x - lam * v x / 2
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
  let vg := fun x => (Ac x + v x * M.dlogq x) / 2
  have hvg : Continuous vg := (hAc.add (hv.mul hσ)).div_const 2
  have hgrad : weakGradient ρ.sqrt ρ.sqrt_mem =ᵐ[haar 1] vec1 vg := by
    filter_upwards [hAae] with x hx
    have h0 : weakGradient ρ.sqrt ρ.sqrt_mem x 0 = vg x := by
      dsimp only [vg]
      have hx' : Ac x = 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - v x * M.dlogq x := hx
      linarith
    ext i
    fin_cases i
    simpa [vec1] using h0
  obtain ⟨hvd, _⟩ := circle_duBoisReymond hv hvw (continuous_vec1 hvg) hgrad
  refine ⟨v, Ac, hv, hAc, hae, hvnonneg, hgrad, ?_, ?_⟩
  · intro t
    simpa only [vec1_apply] using hvd t
  · intro t
    simpa only [vec1_apply] using hAd t

end DGPS.Examples.PolynomialSpecies
