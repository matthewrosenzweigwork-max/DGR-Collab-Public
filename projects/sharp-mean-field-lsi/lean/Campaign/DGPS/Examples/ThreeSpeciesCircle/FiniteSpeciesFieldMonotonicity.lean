import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesAddition

/-! Global active minimality compares TWO actual full-family optimizers at the
same full rate. The result is the nonpositive feedback pairing; a positive
charged-weight lower bound remains a separate quantitative step. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem averaged_common_value {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (hG : 0 < speciesGap (modelData h ε) F)
    (hmin : speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b) :
    let r := (speciesRate (modelData h ε) b).toReal
    elementaryEulerMultiplier h ε r (barycenter F) =
      (∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
        2 * r * (ordinaryEntropy h (F.density s)).toReal)) +
      ∫ x, elementaryEulerCorrection h ε r (barycenter F) x
        ∂(densityMeasure (barycenter F) : Measure (Torus 1)) := by
  dsimp only
  let r := (speciesRate (modelData h ε) b).toReal
  let V := elementaryEulerCorrection h ε r (barycenter F)
  have hs : (∑ s, F.weight s * elementaryEulerMultiplier h ε r (barycenter F)) =
      elementaryEulerMultiplier h ε r (barycenter F) := by
    rw [← Finset.sum_mul, F.weight_sum, one_mul]
  calc
    elementaryEulerMultiplier h ε r (barycenter F) =
        ∑ s, F.weight s * elementaryEulerMultiplier h ε r (barycenter F) := hs.symm
    _ = ∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
        2 * r * (ordinaryEntropy h (F.density s)).toReal +
        ∫ x, V x ∂(densityMeasure (F.density s) : Measure (Torus 1))) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [elementaryModel_speciesRate_common_value hh hε hεmax b F hG hmin s]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      exact (Structural.budget_integral_barycenter F
        (isSmooth_elementaryEulerCorrection h ε r (barycenter F)).continuous_torus).symm

private theorem cross_family_comparison {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F G : SpeciesFamily 1)
    (hF : 0 < speciesGap (modelData h ε) F)
    (hminF : speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b) :
    let r := (speciesRate (modelData h ε) b).toReal
    elementaryEulerMultiplier h ε r (barycenter F) ≤
      (∑ t, G.weight t * ((ordinaryFisher h (G.density t)).toReal -
        2 * r * (ordinaryEntropy h (G.density t)).toReal)) +
      ∫ x, elementaryEulerCorrection h ε r (barycenter F) x
        ∂(densityMeasure (barycenter G) : Measure (Torus 1)) := by
  dsimp only
  let r := (speciesRate (modelData h ε) b).toReal
  let s : Fin F.count := ⟨0, F.count.pos⟩
  have ht (t : Fin G.count) : elementaryEulerMultiplier h ε r (barycenter F) ≤
      (ordinaryFisher h (G.density t)).toReal - 2 * r * (ordinaryEntropy h (G.density t)).toReal +
        ∫ x, elementaryEulerCorrection h ε r (barycenter F) x
          ∂(densityMeasure (G.density t) : Measure (Torus 1)) := by
    rw [← elementaryModel_speciesRate_common_value hh hε hεmax b F hF hminF s]
    exact elementaryModel_speciesRate_active_global_minimum hh hε hεmax b F hF hminF s (G.density t)
  have hs := Finset.sum_le_sum fun t (_ : t ∈ (Finset.univ : Finset (Fin G.count))) =>
    mul_le_mul_of_nonneg_left (ht t) (G.weight_nonneg t)
  rw [← Finset.sum_mul, G.weight_sum, one_mul] at hs
  simp_rw [mul_add] at hs
  rw [Finset.sum_add_distrib] at hs
  rw [← Structural.budget_integral_barycenter G
    (isSmooth_elementaryEulerCorrection h ε r (barycenter F)).continuous_torus] at hs
  exact hs

/-- The true common feedback pairs NONPOSITIVELY with the barycenter difference
of any two actual full-family minimizers. Rates coincide because both attain the
SAME full speciesRate; no branch or weight premise is used. -/
theorem elementaryModel_minimizers_feedback_pairing_nonpos {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F G : SpeciesFamily 1)
    (hF : 0 < speciesGap (modelData h ε) F)
    (hG : 0 < speciesGap (modelData h ε) G)
    (hminF : speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b)
    (hminG : speciesQuotient (modelData h ε) b G = speciesRate (modelData h ε) b) :
    let r := (speciesRate (modelData h ε) b).toReal
    (∫ x, (elementaryEulerCorrection h ε r (barycenter F) x -
        elementaryEulerCorrection h ε r (barycenter G) x) *
      ((barycenter F).density x - (barycenter G).density x) ∂haar 1) ≤ 0 := by
  dsimp only
  let r := (speciesRate (modelData h ε) b).toReal
  let V := elementaryEulerCorrection h ε r (barycenter F)
  let W := elementaryEulerCorrection h ε r (barycenter G)
  have hFF := averaged_common_value hh hε hεmax b F hF hminF
  have hGG := averaged_common_value hh hε hεmax b G hG hminG
  have hFG := cross_family_comparison hh hε hεmax b F G hF hminF
  have hGF := cross_family_comparison hh hε hεmax b G F hG hminG
  have hpair : (∫ x, V x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) -
      (∫ x, V x ∂(densityMeasure (barycenter G) : Measure (Torus 1))) +
      (∫ x, W x ∂(densityMeasure (barycenter G) : Measure (Torus 1))) -
      (∫ x, W x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) ≤ 0 := by
    linarith only [hFF, hGG, hFG, hGF]
  have hV := (isSmooth_elementaryEulerCorrection h ε r (barycenter F)).continuous_torus
  have hW := (isSmooth_elementaryEulerCorrection h ε r (barycenter G)).continuous_torus
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hV.sub hW).continuousOn
  have hi (ρ : AbsoluteDensity 1) : Integrable (fun x => ρ.density x * (V x - W x)) (haar 1) :=
    ρ.integrable_density.mul_bdd (hV.sub hW).aestronglyMeasurable (c := C)
      (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))
  have he : (∫ x, (V x - W x) * ((barycenter F).density x - (barycenter G).density x) ∂haar 1) =
      (∫ x, V x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) -
      (∫ x, W x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) -
      ((∫ x, V x ∂(densityMeasure (barycenter G) : Measure (Torus 1))) -
      (∫ x, W x ∂(densityMeasure (barycenter G) : Measure (Torus 1)))) := by
    have hp : (fun x => (V x - W x) * ((barycenter F).density x - (barycenter G).density x)) =
        fun x => (barycenter F).density x * (V x - W x) -
          (barycenter G).density x * (V x - W x) := by funext x; ring
    rw [hp, integral_sub (hi _) (hi _), ← Structural.budget_integral_densityMeasure,
      ← Structural.budget_integral_densityMeasure]
    rw [integral_sub (hV.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_sub (hV.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (hW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  change (∫ x, (V x - W x) * ((barycenter F).density x - (barycenter G).density x) ∂haar 1) ≤ 0
  rw [he]
  linarith only [hpair]

end DGPS.Examples.ThreeSpeciesCircle
