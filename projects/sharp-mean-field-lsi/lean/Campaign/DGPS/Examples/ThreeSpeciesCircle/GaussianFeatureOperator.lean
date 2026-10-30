import DGPS.Examples.ThreeSpeciesCircle.GaussianReferenceGram

/-! The actual centered finite-rank Hessian in its elementary features. This is
an operator identity on the original centered L2 space, not a generator
spectral assertion. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The original elementary feature classes in the actual centered Hilbert space. -/
noncomputable def gaussianReferenceFeature {h : ℝ} (hh : 0 < h) (i : Fin 3) :
    centeredL2 (refProb hh) :=
  ⟨lpOf (refProb hh) (featVec h i) (continuous_featVec h i), by
    change (∫ x, lpOf (refProb hh) (featVec h i) (continuous_featVec h i) x
      ∂(refProb hh : Measure (Torus 1))) = 0
    rw [integral_congr_ae (lpOf_ae (refProb hh) _ _)]
    obtain ⟨hc, hs, hb, _⟩ := elementaryFeatures_centered_independent hh
    fin_cases i
    · exact hc
    · exact hs
    · exact hb⟩

/-- Hilbert feature coordinates are the original actual reference integrals. -/
theorem gaussianReferenceFeature_inner {h : ℝ} (hh : 0 < h) (i : Fin 3)
    (f : centeredL2 (refProb hh)) :
    inner ℝ (gaussianReferenceFeature hh i) f =
      ∫ x, featVec h i x * (f : Lp ℝ 2 (refProb hh : Measure (Torus 1))) x
        ∂(refProb hh : Measure (Torus 1)) :=
  inner_lpOf (refProb hh) (continuous_featVec h i) _

/-- Exact finite-rank action of the actual centered interaction for every coupling. -/
theorem elementaryModel_centeredInteraction_features {h : ℝ} (hh : 0 < h) (ε : ℝ)
    (f : centeredL2 (refProb hh)) :
    centeredInteraction (modelData h ε) (refProb hh) f =
      ∑ i : Fin 3, (ε * ![kAlpha, kAlpha, -kBeta] i *
        inner ℝ (gaussianReferenceFeature hh i) f) • gaussianReferenceFeature hh i := by
  let μ := refProb hh
  let F : Lp ℝ 2 (μ : Measure (Torus 1)) := f
  let e := gaussianReferenceFeature hh
  let u : Fin 3 → Lp ℝ 2 (μ : Measure (Torus 1)) := fun i =>
    lpOf μ (featVec h i) (continuous_featVec h i)
  let a : Fin 3 → ℝ := fun i => ε * ![kAlpha, kAlpha, -kBeta] i
  have hLHS : ((centeredInteraction (modelData h ε) μ f : centeredL2 μ) :
      Lp ℝ 2 (μ : Measure (Torus 1))) =ᵐ[(μ : Measure (Torus 1))]
      kernelTransform (modelData h ε) μ F := kernelOp_ae _ μ F
  have hpt : ∀ x, kernelTransform (modelData h ε) μ F x =
      ∑ i : Fin 3, (a i * ∫ y, featVec h i y * F y ∂(μ : Measure (Torus 1))) * featVec h i x := by
    intro x
    unfold kernelTransform
    have he : ∀ y, centeredKernel (modelData h ε) μ x y * F y =
        ∑ i : Fin 3, (a i * featVec h i x) * (featVec h i y * F y) := by
      intro y
      simp only [show ∀ x y, centeredKernel (modelData h ε) μ x y = ε * kernelK h x y
        from centeredKernel_model hh ε, kernelK_eq_sum, a, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ =>
      (integrable_cont_mul_lp μ (continuous_featVec h i) F).const_mul _)]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; ring
  have hi : ∀ i, inner ℝ (e i) f = ∫ y, featVec h i y * F y ∂(μ : Measure (Torus 1)) :=
    fun i => gaussianReferenceFeature_inner hh i f
  apply Subtype.ext
  apply Lp.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [Fin.sum_univ_three]
  filter_upwards [hLHS,
    Lp.coeFn_add ((a 0 * inner ℝ (e 0) f) • u 0 + (a 1 * inner ℝ (e 1) f) • u 1)
      ((a 2 * inner ℝ (e 2) f) • u 2),
    Lp.coeFn_add ((a 0 * inner ℝ (e 0) f) • u 0) ((a 1 * inner ℝ (e 1) f) • u 1),
    Lp.coeFn_smul (a 0 * inner ℝ (e 0) f) (u 0),
    Lp.coeFn_smul (a 1 * inner ℝ (e 1) f) (u 1),
    Lp.coeFn_smul (a 2 * inner ℝ (e 2) f) (u 2),
    lpOf_ae μ _ (continuous_featVec h 0), lpOf_ae μ _ (continuous_featVec h 1),
    lpOf_ae μ _ (continuous_featVec h 2)] with x hx h1 h2 h3 h4 h5 f0 f1 f2
  change _ = (((a 0 * inner ℝ (e 0) f) • u 0 +
    (a 1 * inner ℝ (e 1) f) • u 1 + (a 2 * inner ℝ (e 2) f) • u 2) :
      Lp ℝ 2 (μ : Measure (Torus 1))) x
  rw [hx, hpt, h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [f0, f1, f2, Fin.sum_univ_three, hi 0, hi 1, hi 2]

/-- The actual density Hessian is identity plus the proved elementary feature action. -/
theorem elementaryModel_densityHessian_features {h : ℝ} (hh : 0 < h) (ε : ℝ)
    (f : centeredL2 (refProb hh)) :
    densityHessian (modelData h ε) (refProb hh) f =
      f + ∑ i : Fin 3, (ε * ![kAlpha, kAlpha, -kBeta] i *
        inner ℝ (gaussianReferenceFeature hh i) f) • gaussianReferenceFeature hh i := by
  change f + centeredInteraction (modelData h ε) (refProb hh) f = _
  rw [elementaryModel_centeredInteraction_features hh ε f]

end DGPS.Examples.ThreeSpeciesCircle
