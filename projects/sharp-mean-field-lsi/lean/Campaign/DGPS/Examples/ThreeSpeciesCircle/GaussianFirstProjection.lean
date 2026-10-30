import DGPS.Examples.ThreeSpeciesCircle.GaussianFirstFeatureForm

/-! The genuine weighted first-feature projection on the original native
weak form domain. The complementary function is not required to be smooth. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

def gaussianReferenceFirstProjection {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) : WeakH1Test (refProb hh) :=
  gaussianReferenceFirstCombination hh
    (2 * h ^ 2 * ∫ x, featureC h x * f.fn x ∂(refProb hh : Measure (Torus 1)))
    (2 * h ^ 2 * ∫ x, featureS h x * f.fn x ∂(refProb hh : Measure (Torus 1)))

/-- The actual first-feature projection is centered, and its residual has
both true weighted first-feature moments zero. -/
theorem gaussianReferenceFirstProjection_constraints {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) :
    (∫ x, (gaussianReferenceFirstProjection hh f).fn x ∂(refProb hh : Measure (Torus 1))) = 0 ∧
    (∫ x, featureC h x * (gaussianReferenceTestSubtract hh f
      (gaussianReferenceFirstProjection hh f)).fn x ∂(refProb hh : Measure (Torus 1))) = 0 ∧
    (∫ x, featureS h x * (gaussianReferenceTestSubtract hh f
      (gaussianReferenceFirstProjection hh f)).fn x ∂(refProb hh : Measure (Torus 1))) = 0 := by
  let μ := refProb hh
  let X := ∫ x, featureC h x * f.fn x ∂(μ : Measure (Torus 1))
  let Y := ∫ x, featureS h x * f.fn x ∂(μ : Measure (Torus 1))
  let p := gaussianReferenceFirstProjection hh f
  have hp := gaussianReferenceFirstCombination_moments hh (2 * h ^ 2 * X) (2 * h ^ 2 * Y)
  change (∫ x, p.fn x ∂(μ : Measure (Torus 1))) = 0 ∧
    (∫ x, featureC h x * p.fn x ∂(μ : Measure (Torus 1))) = (2 * h ^ 2 * X) / (2 * h ^ 2) ∧
    (∫ x, featureS h x * p.fn x ∂(μ : Measure (Torus 1))) = (2 * h ^ 2 * Y) / (2 * h ^ 2) at hp
  have hcL : MemLp (featureC h) 2 (μ : Measure (Torus 1)) :=
    (featureC_continuous h).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsL : MemLp (featureS h) 2 (μ : Measure (Torus 1)) :=
    (featureS_continuous h).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨hp.1, ?_, ?_⟩
  · change (∫ x, featureC h x * (f.fn x - p.fn x) ∂(μ : Measure (Torus 1))) = 0
    simp_rw [mul_sub]
    have iF : Integrable (fun x => featureC h x * f.fn x) (μ : Measure (Torus 1)) :=
      hcL.integrable_mul f.isWeak.memLp
    have iP : Integrable (fun x => featureC h x * p.fn x) (μ : Measure (Torus 1)) :=
      hcL.integrable_mul p.isWeak.memLp
    rw [integral_sub iF iP, hp.2.1]
    change X - (2 * h ^ 2 * X) / (2 * h ^ 2) = 0
    field_simp [hh.ne'] <;> ring
  · change (∫ x, featureS h x * (f.fn x - p.fn x) ∂(μ : Measure (Torus 1))) = 0
    simp_rw [mul_sub]
    have iF : Integrable (fun x => featureS h x * f.fn x) (μ : Measure (Torus 1)) :=
      hsL.integrable_mul f.isWeak.memLp
    have iP : Integrable (fun x => featureS h x * p.fn x) (μ : Measure (Torus 1)) :=
      hsL.integrable_mul p.isWeak.memLp
    rw [integral_sub iF iP, hp.2.2]
    change Y - (2 * h ^ 2 * Y) / (2 * h ^ 2) = 0
    field_simp [hh.ne'] <;> ring

/-- Actual native projection mass, energy and weighted mass orthogonality.
Every identity retains the original chosen weak gradient. -/
theorem gaussianReferenceFirstProjection_forms {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) :
    gaussianReferenceMass hh (gaussianReferenceFirstProjection hh f) =
      2 * h ^ 2 * ((∫ x, featureC h x * f.fn x ∂(refProb hh : Measure (Torus 1))) ^ 2 +
        (∫ x, featureS h x * f.fn x ∂(refProb hh : Measure (Torus 1))) ^ 2) ∧
    gaussianReferenceRealEnergy hh (gaussianReferenceFirstProjection hh f) =
      a0 * gaussianReferenceMass hh (gaussianReferenceFirstProjection hh f) ∧
    gaussianReferenceMass hh f =
      gaussianReferenceMass hh (gaussianReferenceFirstProjection hh f) +
        gaussianReferenceMass hh (gaussianReferenceTestSubtract hh f (gaussianReferenceFirstProjection hh f)) := by
  let μ := refProb hh
  let X := ∫ x, featureC h x * f.fn x ∂(μ : Measure (Torus 1))
  let Y := ∫ x, featureS h x * f.fn x ∂(μ : Measure (Torus 1))
  let c := 2 * h ^ 2 * X
  let s := 2 * h ^ 2 * Y
  let p := gaussianReferenceFirstProjection hh f
  let w := gaussianReferenceTestSubtract hh f p
  have hp := gaussianReferenceFirstCombination_forms hh c s
  change gaussianReferenceMass hh p = (c ^ 2 + s ^ 2) / (2 * h ^ 2) ∧
    gaussianReferenceRealEnergy hh p = a0 * gaussianReferenceMass hh p at hp
  have hmass : gaussianReferenceMass hh p = 2 * h ^ 2 * (X ^ 2 + Y ^ 2) := by
    rw [hp.1]
    dsimp only [c, s]
    field_simp [hh.ne']
    <;> ring
  refine ⟨hmass, hp.2, ?_⟩
  have hcL : MemLp (featureC h) 2 (μ : Measure (Torus 1)) :=
    (featureC_continuous h).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsL : MemLp (featureS h) 2 (μ : Measure (Torus 1)) :=
    (featureS_continuous h).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpair : (∫ x, f.fn x * p.fn x ∂(μ : Measure (Torus 1))) = gaussianReferenceMass hh p := by
    have he : (fun x => f.fn x * p.fn x) = fun x =>
        c * (featureC h x * f.fn x) + s * (featureS h x * f.fn x) := by
      funext x
      change f.fn x * (c * featureC h x + s * featureS h x) = _
      ring
    have iC : Integrable (fun x => c * (featureC h x * f.fn x))
        (μ : Measure (Torus 1)) := (hcL.integrable_mul f.isWeak.memLp).const_mul c
    have iS : Integrable (fun x => s * (featureS h x * f.fn x))
        (μ : Measure (Torus 1)) := (hsL.integrable_mul f.isWeak.memLp).const_mul s
    rw [he, integral_add iC iS, integral_const_mul, integral_const_mul, hmass]
    change c * X + s * Y = 2 * h ^ 2 * (X ^ 2 + Y ^ 2)
    dsimp [c, s]
    ring
  have he : (fun x => w.fn x ^ 2) = fun x =>
      (f.fn x ^ 2 - 2 * (f.fn x * p.fn x)) + p.fn x ^ 2 := by
    funext x
    change (f.fn x - p.fn x) ^ 2 = _
    ring
  have hi : Integrable (fun x => f.fn x * p.fn x) (refProb hh : Measure (Torus 1)) :=
    f.isWeak.memLp.integrable_mul p.isWeak.memLp
  have iTwice : Integrable (fun x => 2 * (f.fn x * p.fn x))
      (refProb hh : Measure (Torus 1)) := hi.const_mul 2
  have iSub : Integrable (fun x => f.fn x ^ 2 - 2 * (f.fn x * p.fn x))
      (refProb hh : Measure (Torus 1)) := f.isWeak.memLp.integrable_sq.sub iTwice
  have hw : gaussianReferenceMass hh w = gaussianReferenceMass hh f -
      2 * gaussianReferenceMass hh p + gaussianReferenceMass hh p := by
    unfold gaussianReferenceMass
    rw [he, integral_add iSub p.isWeak.memLp.integrable_sq,
      integral_sub f.isWeak.memLp.integrable_sq iTwice, integral_const_mul, hpair]
    rfl
  change gaussianReferenceMass hh f = gaussianReferenceMass hh p + gaussianReferenceMass hh w
  linarith only [hw]

end DGPS.Examples.ThreeSpeciesCircle
