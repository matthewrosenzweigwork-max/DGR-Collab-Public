import DGPS.Examples.PolynomialSpeciesActualPoincareMargin
import DGPS.Examples.PolynomialNativeH1SplitDescent
import DGPS.Variational.SpeciesInclusion
import DGPS.Examples.ThreeSpeciesCircle.ThreeSpeciesCanonicalAssembly

noncomputable section
open MeasureTheory Filter Topology NormedSpace
open scoped ContDiff ENNReal
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies


/-- Density-H1, not merely square-root-H1: compactness supplies a positive
uniform root lower bound before the one-dimensional H1 algebra is applied. -/
theorem nativeH1BinarySplit_positiveH1Density
    (ρ : AbsoluteDensity 1) (v : Torus 1 → ℝ) (hv : Continuous v) (hvp : ∀ x, 0 < v x)
    (hrep : ρ.sqrt =ᵐ[haar 1] v) (g : Torus 1 → ℝ)
    (G : Torus 1 → Tangent 1) (hg : IsWeakGradient g G) (hc : Continuous g)
    (hm : ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)) = 0)
    (t : ℝ) (hp : ∀ (s : Fin 2) x, 0 < 1 + t * (![g, fun x => -g x] s) x) :
    let F := nativeH1BinarySplit ρ g G hg hc hm t hp
    ∀ s : Fin F.count, PositiveH1Density (F.density s) := by
  dsimp only
  intro s
  obtain ⟨w, hwc, hwp, hwrep, hwH⟩ :=
    nativeH1BinarySplit_positive_representatives ρ v hv hvp hrep g G hg hc hm t hp s
  obtain ⟨x, _hx, hxmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hwc.continuousOn
  exact positiveH1Density_of_bounded_root _ w hwc hwrep hwH (w x) (hwp x)
    (fun y => hxmin (Set.mem_univ y))

/-- Actual every-optimizer, every normalized native first eigenfunction,
both-sign descent. The margin and smooth positive original representative are
produced here rather than assumed. -/
theorem polynomial_scalarMinimizer_every_native_eigenfunction_descent
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hN : IsOpen N) (h0N : (0 : E_STR02969) ∈ N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψN : ∀ p ∈ U, ψ p ∈ N)
    (hgraph : ∀ p ∈ U, ∀ w ∈ N, polynomialRangeMap (p, w) = 0 ↔ ψ p = w)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (henv : ∀ a b h γ : ℝ,
      ((a, b, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
      HasDerivAt (fun τ : ℝ => polynomialChartDeficit h (a0 * (1 + τ))
        (a • cosC2_STR02915 + b • sinC2_STR02915 +
          (ψ (a, b, (h, root_EX054 h), τ) : PeriodicC2_STR02969)))
        (-2 * a0 * polynomialChartGap h
          (a • cosC2_STR02915 + b • sinC2_STR02915 +
            (ψ (a, b, (h, root_EX054 h), γ) : PeriodicC2_STR02969))) γ)  :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
      ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (canonical_elementary_polynomial_model h) ρ →
      scalarQuotient (canonical_elementary_polynomial_model h) b ρ =
        scalarRate (canonical_elementary_polynomial_model h) b →
      ∀ f : WeakH1Test (densityMeasure ρ),
      (∫ x, f.fn x ∂(densityMeasure ρ : Measure (Torus 1))) = 0 →
      (∫ x, f.fn x ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) = 1 →
      (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure ρ : Measure (Torus 1))) =
        (poincareRate (densityMeasure ρ)).toReal →
    ∃ (g : Torus 1 → ℝ) (hc : Continuous g) (hg : IsWeakGradient g f.grad)
        (hm : ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1)) = 0),
      g =ᵐ[haar 1] f.fn ∧ g =ᵐ[(densityMeasure ρ : Measure (Torus 1))] f.fn ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| < δ →
        ∃ hp : ∀ (s : Fin 2) x, 0 < 1 + t * (![g, fun x => -g x] s) x,
          let F := nativeH1BinarySplit ρ g f.grad hg hc hm t hp
          (∀ s : Fin F.count, PositiveH1Density (F.density s)) ∧
          densityMeasure (barycenter F) = densityMeasure ρ ∧
          (speciesGap (canonical_elementary_polynomial_model h) F : ℝ) = (scalarGap (canonical_elementary_polynomial_model h) ρ : ℝ) +
            (1 / 2 : ℝ) * ((∫ x, InformationTheory.klFun (1 + t * g x)
              ∂(densityMeasure ρ : Measure (Torus 1))) +
              ∫ x, InformationTheory.klFun (1 + t * (-g x))
                ∂(densityMeasure ρ : Measure (Torus 1))) ∧
          0 < speciesGap (canonical_elementary_polynomial_model h) F ∧ speciesDissipation (canonical_elementary_polynomial_model h) b F ≠ ⊤ ∧
            speciesQuotient (canonical_elementary_polynomial_model h) b F < scalarRate (canonical_elementary_polynomial_model h) b := by
  obtain ⟨δP, c, hδP, _hc, hPC⟩ := polynomial_scalarMinimizer_actual_poincare_margin
    hU h0U hN h0N hψ hψN hgraph hzero hamp henv
  obtain ⟨δS, hδS, hsmooth⟩ := polynomial_scalarMinimizer_smooth_representative
  refine ⟨min δP δS, lt_min hδP hδS, ?_⟩
  intro h hh hsmall b ρ hG hmin f hmean hmass henergy
  have hpc := (hPC h hh (hsmall.trans_le (min_le_left _ _)) b ρ hG hmin).2
  obtain ⟨v, hv, hvrep, hvlo, _hvlog⟩ :=
    hsmooth h hh (hsmall.trans_le (min_le_right _ _)) b ρ hG hmin
  have hvpos : ∀ x, 0 < v x := fun x => lt_of_lt_of_le (by norm_num) (hvlo x)
  have hD : scalarDissipation (canonical_elementary_polynomial_model h) b ρ ≠ ⊤ := by
    have hi := (polynomial_family_gap_and_dissipation h b (SpeciesFamily.single ρ)).2.2.1
    simpa only [speciesDissipation_single] using hi
  rw [← hmin] at hpc
  have hd := nativeH1BinarySplit_poincare_attainer_descent
    (canonical_elementary_polynomial_model h) b ρ v hv.continuous_torus hvpos hvrep
    hG hD f hmean hmass henergy hpc
  obtain ⟨g, hc, hg, hm, hgae, hgμ, ε, hε, hsplit⟩ := hd
  refine ⟨g, hc, hg, hm, hgae, hgμ, ε, hε, ?_⟩
  intro t ht0 htε
  obtain ⟨hp, hbary, hgap, hGsplit, hDsplit, hQsplit⟩ := hsplit t ht0 htε
  refine ⟨hp, nativeH1BinarySplit_positiveH1Density ρ v hv.continuous_torus hvpos hvrep
    g f.grad hg hc hm t hp, hbary, hgap, hGsplit, hDsplit, ?_⟩
  simpa only [hmin] using hQsplit

end DGPS.Examples.PolynomialSpecies
