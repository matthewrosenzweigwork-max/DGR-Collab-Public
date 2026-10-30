import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMomentRotations
import DGPS.Examples.ThreeSpeciesCircle.NearestRootMomentError
import DGPS.Examples.ThreeSpeciesCircle.ThreefoldMomentQuadratic
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferenceLocalStability

/-! Exact interacting correction at actual assigned ordinary roots. Arbitrary
original species weights are grouped into the three nonreference orbit weights;
the actual reference contribution vanishes by genuine generator centering. -/

noncomputable section
open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Total original weight assigned to each nonreference ordinary root. -/
def assignedOrbitWeights (F : SpeciesFamily 1) (label : Fin F.count → Fin 4) (j : Fin 3) : ℝ :=
  ∑ s, if label s = j.succ then F.weight s else 0

theorem assignedOrbitWeights_nonneg (F : SpeciesFamily 1)
    (label : Fin F.count → Fin 4) (j : Fin 3) : 0 ≤ assignedOrbitWeights F label j := by
  apply Finset.sum_nonneg
  intro s hs
  split_ifs
  · exact F.weight_nonneg s
  · exact le_rfl

private theorem grouping (F : SpeciesFamily 1) (label : Fin F.count → Fin 4)
    (g : Fin 4 → ℝ) (hg : g 0 = 0) :
    (∑ s, F.weight s * g (label s)) = ∑ j : Fin 3, assignedOrbitWeights F label j * g j.succ := by
  classical
  have hleft : (∑ s, F.weight s * g (label s)) =
      ∑ s, ∑ j : Fin 3, (if label s = j.succ then F.weight s * g j.succ else 0) := by
    apply Finset.sum_congr rfl
    intro s hs
    generalize he : label s = i
    fin_cases i <;> simp [Fin.sum_univ_three, hg]
  have hright : (∑ j : Fin 3, ∑ s, (if label s = j.succ then F.weight s * g j.succ else 0)) =
      ∑ j : Fin 3, assignedOrbitWeights F label j * g j.succ := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [assignedOrbitWeights, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs <;> simp_all
  exact hleft.trans (Finset.sum_comm.trans hright)

/-- Nonreference mass is the sum of the actual grouped orbit weights. -/
theorem assignedOrbitWeights_mass (F : SpeciesFamily 1) (label : Fin F.count → Fin 4) :
    threefoldMass (assignedOrbitWeights F label) = nonreferenceRootWeight F label := by
  have he := grouping F label (fun i => if i = 0 then 0 else 1) (by simp)
  simpa only [Fin.succ_ne_zero, if_false, mul_one, mul_ite, mul_zero,
    threefoldMass, nonreferenceRootWeight] using he.symm

private theorem assigned_integral_grouping (F : SpeciesFamily 1)
    (σ : Fin 3 → AbsoluteDensity 1) (h : ℝ) (label : Fin F.count → Fin 4)
    (f : Torus 1 → ℝ) (hf : Continuous f)
    (hzero : (∫ x, f x ∂threefoldReference h) = 0) :
    (∫ x, f x ∂(densityMeasure (barycenter
      (assignedRootFamily F (Fin.cases (ordinaryReferenceAbsolute h) σ) label)) : Measure (Torus 1))) =
        ∑ j : Fin 3, assignedOrbitWeights F label j *
          ∫ x, f x ∂(densityMeasure (σ j) : Measure (Torus 1)) := by
  rw [Structural.budget_integral_barycenter _ hf]
  change (∑ s, F.weight s * (∫ x, f x ∂(densityMeasure
    (Fin.cases (ordinaryReferenceAbsolute h) σ (label s)) : Measure (Torus 1)))) = _
  apply grouping F label (fun i : Fin 4 =>
    ∫ x, f x ∂(densityMeasure (Fin.cases (ordinaryReferenceAbsolute h) σ i) : Measure (Torus 1)))
  change (∫ x, f x ∂(densityMeasure (ordinaryReferenceAbsolute h) : Measure (Torus 1))) = 0
  rw [ordinaryReferenceAbsolute_measure h]
  exact hzero

private theorem phase_coordinates (j : Fin 3) :
    (threefoldPhase j).re = Real.cos (2 * Real.pi * ((j : ℕ) / 3)) ∧
      (threefoldPhase j).im = Real.sin (2 * Real.pi * ((j : ℕ) / 3)) := by
  fin_cases j
  · norm_num [threefoldPhase]
  · have he : (-1 / 2 : ℝ) = Real.cos (2 * Real.pi * (1 / 3)) ∧
        Real.sqrt 3 / 2 = Real.sin (2 * Real.pi * (1 / 3)) := by
      rw [show 2 * Real.pi * (1 / 3) = 2 * Real.pi / 3 by ring,
        cos_theta_STR02923, sin_theta_STR02923]
      exact ⟨rfl, rfl⟩
    simpa [threefoldPhase] using he
  · have he : (-1 / 2 : ℝ) = Real.cos (2 * Real.pi * (2 / 3)) ∧
        -(Real.sqrt 3 / 2) = Real.sin (2 * Real.pi * (2 / 3)) := by
      rw [show 2 * Real.pi * (2 / 3) = 2 * (2 * Real.pi / 3) by ring,
        Real.cos_two_mul, Real.sin_two_mul, cos_theta_STR02923, sin_theta_STR02923]
      constructor <;> ring
    simpa [threefoldPhase] using he

private theorem orbit_re (p : Fin 3 → ℝ) (v : ℂ) :
    (threefoldOrbitSum p v).re =
      ∑ j, p j * ((threefoldPhase j).re * v.re - (threefoldPhase j).im * v.im) := by
  simp only [threefoldOrbitSum, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem orbit_im (p : Fin 3 → ℝ) (v : ℂ) :
    (threefoldOrbitSum p v).im =
      ∑ j, p j * ((threefoldPhase j).im * v.re + (threefoldPhase j).re * v.im) := by
  simp only [threefoldOrbitSum, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The actual assigned-root C is the finite C3 quadratic. Its coefficients
are actual native moments at the SAME root zero, not assumed asymptotic values. -/
theorem elementaryC_assigned_ordinary_roots (D : OrdinaryRootGraphData) {h : ℝ} (hh : 0 < h)
    (hhr : h ∈ Set.Ioo (-D.radius) D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ))
    (a : ℝ) (F : SpeciesFamily 1) (label : Fin F.count → Fin 4) :
    let v : ℂ := ⟨momC h (densityMeasure (σ 0)), momS h (densityMeasure (σ 0))⟩
    let w : ℂ := ⟨∫ x, elementaryFeatureGenerator h (featureC h) x
      ∂(densityMeasure (σ 0) : Measure (Torus 1)),
      ∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure (σ 0) : Measure (Torus 1))⟩
    let B := momB h (densityMeasure (σ 0))
    let E := ∫ x, elementaryFeatureGenerator h (featureB h) x
      ∂(densityMeasure (σ 0) : Measure (Torus 1))
    elementaryC h a (barycenter (assignedRootFamily F (Fin.cases (ordinaryReferenceAbsolute h) σ) label)) =
      threefoldQuadratic (threefoldAlpha a B E) (threefoldBeta a v w) (assignedOrbitWeights F label) := by
  dsimp only
  let τ := barycenter (assignedRootFamily F (Fin.cases (ordinaryReferenceAbsolute h) σ) label)
  let p := assignedOrbitWeights F label
  have hg (i : Fin 6) : (∫ x, elementarySixObservable h i x ∂(densityMeasure τ : Measure (Torus 1))) =
      ∑ j : Fin 3, p j * ∫ x, elementarySixObservable h i x ∂(densityMeasure (σ j) : Measure (Torus 1)) :=
    assigned_integral_grouping F σ h label _ (continuous_elementarySixObservable h i)
      (elementarySixObservable_reference_zero hh i)
  have hr := ordinaryRoot_six_moment_rotations D h hhr σ hσ
  apply elementaryC_of_threefold_moments
  · change momC h (densityMeasure τ) = _
    rw [show momC h (densityMeasure τ) = ∑ j : Fin 3, p j * momC h (densityMeasure (σ j)) from hg 0,
      orbit_re]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(phase_coordinates j).1, (phase_coordinates j).2]
    exact congrArg (fun z => p j * z) (hr j).1
  · change momS h (densityMeasure τ) = _
    rw [show momS h (densityMeasure τ) = ∑ j : Fin 3, p j * momS h (densityMeasure (σ j)) from hg 1,
      orbit_im]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(phase_coordinates j).1, (phase_coordinates j).2]
    exact congrArg (fun z => p j * z) (hr j).2.1
  · change (∫ x, elementarySixObservable h 3 x ∂(densityMeasure τ : Measure (Torus 1))) = _
    rw [hg 3, orbit_re]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(phase_coordinates j).1, (phase_coordinates j).2]
    exact congrArg (fun z => p j * z) (hr j).2.2.2.1
  · change (∫ x, elementarySixObservable h 4 x ∂(densityMeasure τ : Measure (Torus 1))) = _
    rw [hg 4, orbit_im]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(phase_coordinates j).1, (phase_coordinates j).2]
    exact congrArg (fun z => p j * z) (hr j).2.2.2.2.1
  · change momB h (densityMeasure τ) = _
    rw [show momB h (densityMeasure τ) = ∑ j : Fin 3, p j * momB h (densityMeasure (σ j)) from hg 2]
    unfold threefoldMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(hr j).2.2.1]
    ring
  · change (∫ x, elementarySixObservable h 5 x ∂(densityMeasure τ : Measure (Torus 1))) = _
    rw [hg 5]
    unfold threefoldMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hAB : (∫ x, elementaryFeatureGenerator h (featureB h) x
        ∂(densityMeasure (σ j) : Measure (Torus 1))) =
        ∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure (σ 0) : Measure (Torus 1)) :=
      (hr j).2.2.2.2.2
    change p j * (∫ x, elementaryFeatureGenerator h (featureB h) x
      ∂(densityMeasure (σ j) : Measure (Torus 1))) =
      (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure (σ 0) : Measure (Torus 1))) * p j
    rw [hAB]
    ring

end DGPS.Examples.ThreeSpeciesCircle
