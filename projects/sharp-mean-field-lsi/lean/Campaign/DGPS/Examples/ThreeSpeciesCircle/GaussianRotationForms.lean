import DGPS.Examples.ThreeSpeciesCircle.GaussianRotationSector

/-! Exact weighted mass and physical-energy orthogonality of the genuine C3
average on the original weak form domain. No spectral or deficit estimate is
assumed. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem invariant_pair_average (h : ℝ) (f v : Torus 1 → ℝ)
    (hv : ∀ x, v (x + gaussianThirdTurn) = v x)
    (i0 : Integrable (fun x => v x * f x) (threefoldReference h))
    (i1 : Integrable (fun x => v x * f (x + gaussianThirdTurn)) (threefoldReference h))
    (i2 : Integrable (fun x => v x * f (x + gaussianThirdTurn + gaussianThirdTurn)) (threefoldReference h)) :
    (∫ x, v x * gaussianReferenceAverage f x ∂threefoldReference h) =
      ∫ x, v x * f x ∂threefoldReference h := by
  have h1 : (∫ x, v x * f (x + gaussianThirdTurn) ∂threefoldReference h) =
      ∫ x, v x * f x ∂threefoldReference h := by
    have ht := threefoldReference_integral_thirdTurn h (fun x => v x * f x)
    simpa only [hv] using ht
  have h2 : (∫ x, v x * f (x + gaussianThirdTurn + gaussianThirdTurn) ∂threefoldReference h) =
      ∫ x, v x * f x ∂threefoldReference h := by
    have ht := threefoldReference_integral_thirdTurn h (fun x => v x * f (x + gaussianThirdTurn))
    simp only [hv] at ht
    exact ht.trans h1
  have he : (fun x => v x * gaussianReferenceAverage f x) = fun x =>
      (1 / 3 : ℝ) * ((v x * f x + v x * f (x + gaussianThirdTurn)) +
        v x * f (x + gaussianThirdTurn + gaussianThirdTurn)) := by
    funext x
    unfold gaussianReferenceAverage
    ring
  have i01 : Integrable (fun x => v x * f x + v x * f (x + gaussianThirdTurn))
      (threefoldReference h) := i0.add i1
  rw [he, integral_const_mul, integral_add i01 i2, integral_add i0 i1, h1, h2]
  ring

private theorem square_split {μ : Measure (Torus 1)} (a b : Torus 1 → ℝ)
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hpair : (∫ x, a x * b x ∂μ) = ∫ x, b x ^ 2 ∂μ) :
    (∫ x, a x ^ 2 ∂μ) = (∫ x, b x ^ 2 ∂μ) + ∫ x, (a x - b x) ^ 2 ∂μ := by
  have iab : Integrable (fun x => a x * b x) μ := ha.integrable_mul hb
  have ia := ha.integrable_sq
  have ib := hb.integrable_sq
  have i2ab : Integrable (fun x => 2 * (a x * b x)) μ := iab.const_mul 2
  have he : (fun x => (a x - b x) ^ 2) = fun x =>
      (a x ^ 2 - 2 * (a x * b x)) + b x ^ 2 := by funext x; ring
  have idiff : Integrable (fun x => a x ^ 2 - 2 * (a x * b x)) μ := ia.sub i2ab
  rw [he, integral_add idiff ib,
    integral_sub ia i2ab, integral_const_mul, hpair]
  ring

/-- Full original native weak tests admit the actual averaged/residual mass
orthogonality, with no smoothness or boundedness hypothesis. -/
theorem gaussianReferenceAverage_mass_split {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) :
    (∫ x, f.fn x ^ 2 ∂(refProb hh : Measure (Torus 1))) =
      (∫ x, (gaussianReferenceTestAverage hh f).fn x ^ 2 ∂(refProb hh : Measure (Torus 1))) +
        ∫ x, (f.fn x - (gaussianReferenceTestAverage hh f).fn x) ^ 2
          ∂(refProb hh : Measure (Torus 1)) := by
  let P := gaussianReferenceTestAverage hh f
  let R := gaussianReferenceTestTurn hh f
  let R2 := gaussianReferenceTestTurn hh R
  have he := invariant_pair_average h f.fn P.fn (gaussianReferenceAverage_invariant f.fn)
    (P.isWeak.memLp.integrable_mul f.isWeak.memLp)
    (P.isWeak.memLp.integrable_mul R.isWeak.memLp)
    (P.isWeak.memLp.integrable_mul R2.isWeak.memLp)
  have hp : (∫ x, f.fn x * P.fn x ∂(refProb hh : Measure (Torus 1))) =
      ∫ x, P.fn x ^ 2 ∂(refProb hh : Measure (Torus 1)) := by
    change (∫ x, P.fn x * P.fn x ∂(refProb hh : Measure (Torus 1))) =
      ∫ x, P.fn x * f.fn x ∂(refProb hh : Measure (Torus 1)) at he
    calc
      _ = ∫ x, P.fn x * f.fn x ∂(refProb hh : Measure (Torus 1)) :=
        integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ = ∫ x, P.fn x * P.fn x ∂(refProb hh : Measure (Torus 1)) := he.symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun x => by ring)
  exact square_split f.fn P.fn f.isWeak.memLp P.isWeak.memLp hp

/-- The same actual projection is orthogonal for the physical Dirichlet form;
the averaged weak gradient is the original chosen gradient averaged spatially. -/
theorem gaussianReferenceAverage_energy_split {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) :
    (∫ x, ‖f.grad x‖ ^ 2 ∂(refProb hh : Measure (Torus 1))) =
      (∫ x, ‖(gaussianReferenceTestAverage hh f).grad x‖ ^ 2 ∂(refProb hh : Measure (Torus 1))) +
        ∫ x, ‖f.grad x - (gaussianReferenceTestAverage hh f).grad x‖ ^ 2
          ∂(refProb hh : Measure (Torus 1)) := by
  let P := gaussianReferenceTestAverage hh f
  let R := gaussianReferenceTestTurn hh f
  let R2 := gaussianReferenceTestTurn hh R
  let a : Torus 1 → ℝ := fun x => f.grad x 0
  let b : Torus 1 → ℝ := fun x => P.grad x 0
  have ha : MemLp a 2 (refProb hh : Measure (Torus 1)) :=
    (EuclideanSpace.proj 0 : Tangent 1 →L[ℝ] ℝ).comp_memLp' f.isWeak.memLp_grad
  have hb : MemLp b 2 (refProb hh : Measure (Torus 1)) :=
    (EuclideanSpace.proj 0 : Tangent 1 →L[ℝ] ℝ).comp_memLp' P.isWeak.memLp_grad
  have ha1 : MemLp (fun x => a (x + gaussianThirdTurn)) 2 (refProb hh : Measure (Torus 1)) :=
    (EuclideanSpace.proj 0 : Tangent 1 →L[ℝ] ℝ).comp_memLp' R.isWeak.memLp_grad
  have ha2 : MemLp (fun x => a (x + gaussianThirdTurn + gaussianThirdTurn)) 2
      (refProb hh : Measure (Torus 1)) :=
    (EuclideanSpace.proj 0 : Tangent 1 →L[ℝ] ℝ).comp_memLp' R2.isWeak.memLp_grad
  have hbval (x : Torus 1) : b x = gaussianReferenceAverage a x := by
    simp only [b, P, gaussianReferenceTestAverage, gaussianReferenceAverage, a,
      PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  have hbper (x : Torus 1) : b (x + gaussianThirdTurn) = b x := by
    rw [hbval, hbval]
    exact gaussianReferenceAverage_invariant a x
  have he := invariant_pair_average h a b hbper (hb.integrable_mul ha)
    (hb.integrable_mul ha1) (hb.integrable_mul ha2)
  simp_rw [← hbval] at he
  have hp : (∫ x, a x * b x ∂(refProb hh : Measure (Torus 1))) =
      ∫ x, b x ^ 2 ∂(refProb hh : Measure (Torus 1)) := by
    calc
      _ = ∫ x, b x * a x ∂(refProb hh : Measure (Torus 1)) :=
        integral_congr_ae (Eventually.of_forall fun x => by ring)
      _ = ∫ x, b x * b x ∂(refProb hh : Measure (Torus 1)) := he.symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hs := square_split a b ha hb hp
  have hn (z : Tangent 1) : ‖z‖ ^ 2 = (z 0) ^ 2 := by simp [EuclideanSpace.norm_sq_eq]
  simpa only [hn, PiLp.sub_apply, a, b, P] using hs

end DGPS.Examples.ThreeSpeciesCircle
