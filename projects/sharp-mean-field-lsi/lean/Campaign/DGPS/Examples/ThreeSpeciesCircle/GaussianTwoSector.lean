import DGPS.Examples.ThreeSpeciesCircle.GaussianStrictLift

/-! Native two-sector identification from the actual strict Gaussian lift. -/

noncomputable section

namespace DGPS.Examples.ThreeSpeciesCircle

/-- One fixed-field coupling interval supplies both required native spectral
conclusions for every proof of the same actual coercive Hessian. -/
theorem elementaryModel_twoSector_and_strictGaussian {h : ℝ} (hh : 0 < h)
    (hhsmall : |h| ≤ 1 / 1000) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh),
        twoSectorRate (modelData h ε) (ordinaryReference h) hH = poincareRate (refProb hh) ∧
          poincareRate (refProb hh) < gaussianRate (modelData h ε) (refProb hh) hH := by
  obtain ⟨ε0, hε0, hεmax, hstrict⟩ := elementaryModel_gaussianRate_gt_referencePoincare hh hhsmall
  refine ⟨ε0, hε0, hεmax, ?_⟩
  intro ε hε hεsmall hH
  have ht := hstrict ε hε hεsmall hH
  exact ⟨min_eq_right ht.le, ht⟩

end DGPS.Examples.ThreeSpeciesCircle
