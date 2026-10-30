import DGPS.Examples.ThreeSpeciesCircle.H1SplitActualQuotient

/-! Actual full-H1 uphill splitting at EVERY scalar minimizer. Native weighted
tests and a.e. cancellation are admitted before selecting continuous H1
representatives. No optimizer classification, Euler equation or Poincare-gap
conclusion is a premise of the public factory. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Every nontrivial finite centered fixed-barycenter H1 split of EVERY actual
scalar optimizer has the exact positive second-order quotient coefficient and
strictly increases the quotient for BOTH signs of sufficiently small parameters.
The preparation's weighted-H1 pseudotype is represented by the full native
`WeakH1Test`; barycenter equality is equality of the actual probability laws. -/
theorem scalarOptimizer_everyInfinitesimalFixedBarycenterSplit_uphill :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ σ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) σ →
            scalarQuotient (modelData h ε) b σ = scalarRate (modelData h ε) b →
            ∀ (q : ℕ+) (θ : Fin q → ℝ) (hθ : ∀ s, 0 < θ s) (hθsum : ∑ s, θ s = 1),
              ∀ f : Fin q → WeakH1Test (densityMeasure σ),
                (∀ s, ∫ x, (f s).fn x ∂(densityMeasure σ : Measure (Torus 1)) = 0) →
                (∀ᵐ x ∂(densityMeasure σ : Measure (Torus 1)), ∑ s, θ s * (f s).fn x = 0) →
                let B := ∑ s, θ s * ∫ x, (f s).fn x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))
                let r := (scalarRate (modelData h ε) b).toReal
                let c := ((∑ s, θ s * ∫ x, ((f s).grad x 0) ^ 2
                    ∂(densityMeasure σ : Measure (Torus 1))) - r * B) /
                  (2 * (scalarGap (modelData h ε) σ : ℝ))
                0 < B → 0 < c ∧
                ∃ (g : Fin q → Torus 1 → ℝ)
                  (hg : ∀ s, IsWeakGradient (g s) (f s).grad)
                  (hgc : ∀ s, Continuous (g s))
                  (hm : ∀ s, ∫ x, g s x ∂(densityMeasure σ : Measure (Torus 1)) = 0)
                  (hcancel : ∀ x, ∑ s, θ s * g s x = 0),
                  (∀ s, g s =ᵐ[haar 1] (f s).fn) ∧
                  ∃ t0 : ℝ, 0 < t0 ∧ ∃ rem : ℝ → ℝ,
                    Tendsto (fun t => rem t / t ^ 2) (𝓝[{t : ℝ | t ≠ 0}] 0) (𝓝 0) ∧
                    ∀ t : ℝ, 0 < |t| → |t| < t0 →
                      ∃ hp : ∀ s x, 0 < 1 + t * g s x,
                        let F := finiteH1Split σ q θ hθ hθsum g (fun s => (f s).grad) hg hgc hm t hp
                        (∀ s, (densityMeasure (F.density s) : Measure (Torus 1)) =
                          (densityMeasure σ : Measure (Torus 1)).withDensity
                            (fun x => ENNReal.ofReal (1 + t * (f s).fn x))) ∧
                        (∀ s, ∃ v : Torus 1 → ℝ, Continuous v ∧
                          (F.density s).sqrt =ᵐ[haar 1] v ∧ MemH1 v ∧
                            ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ v x) ∧
                        densityMeasure (barycenter F) = densityMeasure σ ∧
                        0 < speciesGap (modelData h ε) F ∧
                        speciesQuotient (modelData h ε) b F ≠ ⊤ ∧
                        speciesQuotient (modelData h ε) b F = ENNReal.ofReal (r + c * t ^ 2 + rem t) ∧
                        scalarRate (modelData h ε) b < speciesQuotient (modelData h ε) b F := by
  classical
  obtain ⟨D⟩ := exists_ordinaryRootGraphData
  obtain ⟨δP, hδP, _, hpositive⟩ := elementaryModel_minimizer_positive_representative D
  obtain ⟨δC, hδC, hcoefficient⟩ := elementaryModel_minimizer_split_quadratic_positive
  refine ⟨min δP δC, lt_min hδP hδC, fun h hh hhd => ?_⟩
  obtain ⟨εP, m, hεP, hεPmax, hm, hPos⟩ := hpositive h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨εC, hεC, _, hCoef⟩ := hcoefficient h hh (hhd.trans_le (min_le_right _ _))
  refine ⟨min εP εC, lt_min hεP hεC, (min_le_left _ _).trans hεPmax,
    fun ε hε hεsmall b σ hbase hmin q θ hθ hθsum f hmean hcancel => ?_⟩
  dsimp only
  intro hB
  have heP : ε < εP := hεsmall.trans_le (min_le_left _ _)
  have heC : ε < εC := hεsmall.trans_le (min_le_right _ _)
  obtain ⟨u, hu, hurep, hul⟩ := hPos ε hε heP b σ hbase hmin
  have hup : ∀ x, 0 < u x := fun x => hm.trans_le (hul x)
  obtain ⟨g, hgc, hgae, hgμ, hg, hgm, hcancelg⟩ :=
    nativeTangentFamily_continuous_reps σ u hu hup hurep q θ f hmean hcancel
  have hc := hCoef ε hε heC b σ hbase hmin q θ hθ f hmean hB
  have hBrep : (∑ s, θ s * ∫ x, g s x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) =
      ∑ s, θ s * ∫ x, (f s).fn x ^ 2 ∂(densityMeasure σ : Measure (Torus 1)) := by
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    apply integral_congr_ae
    filter_upwards [hgμ s] with x hx
    rw [hx]
  have hErep : (∑ s, θ s * ∫ x, ‖(f s).grad x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) =
      ∑ s, θ s * ∫ x, ((f s).grad x 0) ^ 2 ∂(densityMeasure σ : Measure (Torus 1)) := by
    apply Finset.sum_congr rfl
    intro s _
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by simp [EuclideanSpace.norm_sq_eq]
  have hnum : 0 < (∑ s, θ s * ∫ x, ((f s).grad x 0) ^ 2
      ∂(densityMeasure σ : Measure (Torus 1))) -
        (scalarRate (modelData h ε) b).toReal *
          (∑ s, θ s * ∫ x, (f s).fn x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) := by
    have ht := mul_pos hc (show 0 < 2 * (scalarGap (modelData h ε) σ : ℝ) by positivity)
    rwa [div_mul_cancel₀ _ (by positivity : 2 * (scalarGap (modelData h ε) σ : ℝ) ≠ 0)] at ht
  have hnumg : 0 < (∑ s, θ s * ∫ x, ‖(f s).grad x‖ ^ 2
      ∂(densityMeasure σ : Measure (Torus 1))) -
        (scalarRate (modelData h ε) b).toReal *
          (∑ s, θ s * ∫ x, g s x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) := by
    rw [hErep, hBrep]
    exact hnum
  have hexp := finiteH1Split_actual_quotient_expansion σ q θ hθ hθsum g
    (fun s => (f s).grad) hg hgc hgm hcancelg (fun s => (f s).isWeak.memLp_grad)
    h ε b hbase hmin hnumg
  dsimp only at hexp
  rw [hErep, hBrep] at hexp
  obtain ⟨_, t0, ht0, rem, hrem, hsplit⟩ := hexp
  refine ⟨hc, g, hg, hgc, hgm, hcancelg, hgae, t0, ht0, rem, hrem,
    fun t ht hsmall => ?_⟩
  obtain ⟨hp, hbary, hGap, hfin, hQ, hstrict⟩ := hsplit t ht hsmall
  refine ⟨hp, ?_, ?_, hbary, hGap, hfin, hQ, hstrict⟩
  · intro s
    change (densityMeasure (relativeH1SplitDensity σ (g s) (f s).grad (hg s)
      (hgc s) (hgm s) t (hp s)) : Measure (Torus 1)) = _
    rw [relativeH1SplitDensity_measure]
    apply withDensity_congr_ae
    filter_upwards [hgμ s] with x hx
    rw [hx]
  · intro s
    exact relativeH1SplitDensity_positive_rep σ u hu hup hurep (g s) (f s).grad
      (hg s) (hgc s) (hgm s) t (hp s)

end DGPS.Examples.ThreeSpeciesCircle
