import DGPS.Examples.ThreeSpeciesCircle.CompensatingH1Binary
import DGPS.Examples.ThreeSpeciesCircle.InteractingDeficitExpansion

/-! Exact ordinary entropy and information identities at the actual reference
barycenter. These retain the original interaction and its genuine weak force. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

theorem elementaryReference_kernelMean_zero {h : ℝ} (hh : 0 < h) :
    elementaryKernelMean h (threefoldReference h) = 0 := by
  obtain ⟨hc, hs, hb, _⟩ := elementaryFeatures_centered_independent hh
  funext x
  change kAlpha * (momC h (threefoldReference h) * featureC h x +
    momS h (threefoldReference h) * featureS h x) -
      kBeta * (momB h (threefoldReference h) * featureB h x) = 0
  change momC h (threefoldReference h) = 0 at hc
  change momS h (threefoldReference h) = 0 at hs
  change momB h (threefoldReference h) = 0 at hb
  simp only [hc, hs, hb, zero_mul, add_zero, mul_zero, sub_zero]

theorem elementaryReference_kprime_zero {h : ℝ} (hh : 0 < h) :
    elementaryKprime h (threefoldReference h) = 0 := by
  unfold elementaryKprime
  rw [elementaryReference_kernelMean_zero hh]
  funext x
  simp [coordPartial]

theorem elementaryReference_AK_zero {h : ℝ} (hh : 0 < h) :
    elementaryAK h (threefoldReference h) = 0 := by
  unfold elementaryAK
  rw [elementaryReference_kprime_zero hh]
  funext x
  simp [coordPartial]

/-- At the TRUE reference barycenter, all interaction contributions to the
finite-family dissipation vanish exactly. No smoothness of the species is used. -/
theorem elementaryModel_reference_barycenter_dissipation {h : ℝ} (hh : 0 < h)
    (ε : ℝ) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (hbar : (densityMeasure (barycenter F) : Measure (Torus 1)) = threefoldReference h) :
    speciesDissipation (modelData h ε) b F ≠ ⊤ ∧
      (speciesDissipation (modelData h ε) b F).toReal =
        ∑ s, F.weight s * (ordinaryFisher h (F.density s)).toReal := by
  obtain ⟨hfin, he⟩ := elementaryModel_speciesDissipation_expansion h ε b F
  rw [hbar, elementaryReference_AK_zero hh] at he
  have hJ : elementaryJ h (barycenter F) = 0 := by
    unfold elementaryJ
    rw [hbar, elementaryReference_kprime_zero hh]
    simp
  refine ⟨hfin, ?_⟩
  simpa only [Pi.zero_apply, mul_zero, integral_zero, hJ, zero_add, add_zero] using he

/-- At the TRUE reference barycenter, the actual finite-family gap is exactly
the weighted ordinary reference entropy. -/
theorem elementaryModel_reference_barycenter_gap {h ε : ℝ}
    (hh : 0 < h) (hε : 0 < ε) (hεmax : ε < epsMax h)
    (F : SpeciesFamily 1)
    (hbar : (densityMeasure (barycenter F) : Measure (Torus 1)) = threefoldReference h) :
    (speciesGap (modelData h ε) F : ℝ) =
      ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal := by
  have he := elementaryModel_speciesGap_expansion hh hε hεmax F
  have hQ : elementaryQ h (threefoldReference h) = 0 := by
    unfold elementaryQ
    rw [elementaryReference_kernelMean_zero hh]
    simp
  rw [hbar, hQ, mul_zero, add_zero] at he
  exact he

end DGPS.Examples.ThreeSpeciesCircle
