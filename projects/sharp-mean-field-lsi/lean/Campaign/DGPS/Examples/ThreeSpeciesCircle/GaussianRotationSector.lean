import DGPS.Examples.ThreeSpeciesCircle.GaussianReferenceGram
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryOptimizers
import DGPS.Circle.VonMisesParity

/-! The genuine C3 reference action on the full native weak form domain.
Only spatial rotations are used. No generator-feature projection commutation
or exact trigonometric generator eigenrelation is introduced. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Circle.VonMisesParity

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual order-three spatial translation in unit-circle coordinates. -/
def gaussianThirdTurn : Torus 1 := pt (1 / 3)

private theorem pt_add (s t : ℝ) : pt s + pt t = pt (s + t) :=
  (SharpLSI.liftT_add (fun _ : Fin 1 => s) (fun _ : Fin 1 => t)).symm

/-- Three actual turns give the identity on the original torus. -/
theorem gaussianThirdTurn_three : gaussianThirdTurn + gaussianThirdTurn + gaussianThirdTurn = 0 := by
  rw [gaussianThirdTurn, pt_add, pt_add]
  norm_num only [show (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1 by norm_num]
  ext i
  exact AddCircle.coe_period 1

/-- The canonical reference density is invariant under the actual third turn. -/
theorem referenceDensity_gaussianThirdTurn (h : ℝ) (x : Torus 1) :
    referenceDensity h (x + gaussianThirdTurn) = referenceDensity h x := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  rw [gaussianThirdTurn, pt_add, referenceDensity_pt, referenceDensity_pt,
    show 2 * Real.pi * 3 * (t + 1 / 3) = 2 * Real.pi * 3 * t + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

/-- Every original reference integral is rotation invariant. This is a measure
identity and does not require a continuous observable. -/
theorem threefoldReference_integral_thirdTurn (h : ℝ) (f : Torus 1 → ℝ) :
    (∫ x, f (x + gaussianThirdTurn) ∂threefoldReference h) =
      ∫ x, f x ∂threefoldReference h := by
  rw [integral_threefoldReference, integral_threefoldReference]
  have he := integral_add_right_eq_self (μ := haar 1)
    (fun x : Torus 1 => referenceDensity h x * f x) gaussianThirdTurn
  simpa only [referenceDensity_gaussianThirdTurn] using he

private theorem native_to_haar {h : ℝ} (hh : 0 < h) (f : WeakH1Test (refProb hh)) :
    IsWeakGradient f.fn f.grad :=
  (isWeightedWeakGradient_iff (ordinaryReference h)).mp
    ((isMeasureWeakGradient_iff (ordinaryReference h)).mp f.isWeak)

private theorem haar_to_native {h : ℝ} (hh : 0 < h) {f : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (hf : IsWeakGradient f g) : IsMeasureWeakGradient (refProb hh) f g :=
  (isMeasureWeakGradient_iff (ordinaryReference h)).mpr
    ((isWeightedWeakGradient_iff (ordinaryReference h)).mpr hf)

/-- Spatial rotation preserves the original full native weighted weak domain
and transports its actual chosen gradient, with no smooth-test premise. -/
noncomputable def gaussianReferenceTestTurn {h : ℝ} (hh : 0 < h) (f : WeakH1Test (refProb hh)) :
    WeakH1Test (refProb hh) where
  fn x := f.fn (x + gaussianThirdTurn)
  grad x := f.grad (x + gaussianThirdTurn)
  isWeak := by
    apply haar_to_native hh
    simpa only [sub_neg_eq_add] using
      isWeakGradient_translate (native_to_haar hh f) (-gaussianThirdTurn)

/-- The true C3 averaging projection on original scalar functions. -/
def gaussianReferenceAverage (f : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  (1 / 3 : ℝ) * (f x + f (x + gaussianThirdTurn) + f (x + gaussianThirdTurn + gaussianThirdTurn))

/-- The averaged native test remains in the full original weak domain, with
the averaged original weak gradient. -/
noncomputable def gaussianReferenceTestAverage {h : ℝ} (hh : 0 < h) (f : WeakH1Test (refProb hh)) :
    WeakH1Test (refProb hh) where
  fn := gaussianReferenceAverage f.fn
  grad x := (1 / 3 : ℝ) • (f.grad x + f.grad (x + gaussianThirdTurn) +
    f.grad (x + gaussianThirdTurn + gaussianThirdTurn))
  isWeak := by
    apply haar_to_native hh
    have h0 := native_to_haar hh f
    have h1 := native_to_haar hh (gaussianReferenceTestTurn hh f)
    have h2 := native_to_haar hh (gaussianReferenceTestTurn hh (gaussianReferenceTestTurn hh f))
    exact ((h0.add h1).add h2).smul (1 / 3)

/-- Actual averaging is invariant under the true spatial C3 action. -/
theorem gaussianReferenceAverage_invariant (f : Torus 1 → ℝ) (x : Torus 1) :
    gaussianReferenceAverage f (x + gaussianThirdTurn) = gaussianReferenceAverage f x := by
  have h3 : x + gaussianThirdTurn + gaussianThirdTurn + gaussianThirdTurn = x := by
    rw [add_assoc x gaussianThirdTurn gaussianThirdTurn,
      add_assoc x (gaussianThirdTurn + gaussianThirdTurn) gaussianThirdTurn,
      gaussianThirdTurn_three, add_zero]
  unfold gaussianReferenceAverage
  rw [h3]
  ring

/-- The C3 averaging operator is genuinely idempotent on original functions. -/
theorem gaussianReferenceAverage_idempotent (f : Torus 1 → ℝ) :
    gaussianReferenceAverage (gaussianReferenceAverage f) = gaussianReferenceAverage f := by
  funext x
  change (1 / 3 : ℝ) * (gaussianReferenceAverage f x +
    gaussianReferenceAverage f (x + gaussianThirdTurn) +
    gaussianReferenceAverage f (x + gaussianThirdTurn + gaussianThirdTurn)) = gaussianReferenceAverage f x
  have h1 := gaussianReferenceAverage_invariant f x
  have h2 : gaussianReferenceAverage f (x + gaussianThirdTurn + gaussianThirdTurn) =
      gaussianReferenceAverage f x := (gaussianReferenceAverage_invariant f (x + gaussianThirdTurn)).trans h1
  rw [h1, h2]
  ring

end DGPS.Examples.ThreeSpeciesCircle
