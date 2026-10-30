import DGPS.Examples.ThreeSpeciesCircle.GaussianNativeComplement
import DGPS.Examples.ThreeSpeciesCircle.GaussianRotationMoments

/-! The negative invariant feature is controlled by the genuine reference
Poincare defect. All tests remain in their original native weak form domain;
the finite reference rate is established before taking its real value. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

def gaussianReferenceMass {h : ℝ} (hh : 0 < h) (f : WeakH1Test (refProb hh)) : ℝ :=
  ∫ x, f.fn x ^ 2 ∂(refProb hh : Measure (Torus 1))

def gaussianReferenceRealEnergy {h : ℝ} (hh : 0 < h) (f : WeakH1Test (refProb hh)) : ℝ :=
  ∫ x, ‖f.grad x‖ ^ 2 ∂(refProb hh : Measure (Torus 1))

/-- The original native energy is finite and equals the real form integral. -/
theorem gaussianReference_energy_eq_ofReal {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) :
    dirichletEnergy (refProb hh) f = ENNReal.ofReal (gaussianReferenceRealEnergy hh f) := by
  unfold dirichletEnergy gaussianReferenceRealEnergy
  rw [ofReal_integral_eq_lintegral_ofReal f.isWeak.memLp_grad.norm.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg _)]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- The finite actual reference Poincare rate controls every full-domain test. -/
theorem gaussianReference_poincare_real {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh)) :
    (poincareRate (refProb hh)).toReal * weightedVariance (refProb hh) f.fn ≤
      gaussianReferenceRealEnergy hh f := by
  have hE0 : 0 ≤ gaussianReferenceRealEnergy hh f := integral_nonneg fun _ => sq_nonneg _
  by_cases hv : 0 < weightedVariance (refProb hh) f.fn
  · have he := (le_poincareRate_iff_forall (refProb hh) _).1 le_rfl f hv
    rw [gaussianReference_energy_eq_ofReal] at he
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hv.le,
      ENNReal.toReal_ofReal hE0] using hr
  · have hv0 := weightedVariance_nonneg (refProb hh) f.fn
    have hz : weightedVariance (refProb hh) f.fn = 0 := le_antisymm (le_of_not_gt hv) hv0
    rw [hz, mul_zero]
    exact hE0

/-- Subtraction preserves the full native domain and the actual difference gradient. -/
def gaussianReferenceTestSubtract {h : ℝ} (hh : 0 < h)
    (f g : WeakH1Test (refProb hh)) : WeakH1Test (refProb hh) where
  fn x := f.fn x - g.fn x
  grad x := f.grad x - g.grad x
  isWeak := by
    have hf := (isWeightedWeakGradient_iff (ordinaryReference h)).mp
      ((isMeasureWeakGradient_iff (ordinaryReference h)).mp f.isWeak)
    have hg := (isWeightedWeakGradient_iff (ordinaryReference h)).mp
      ((isMeasureWeakGradient_iff (ordinaryReference h)).mp g.isWeak)
    apply (isMeasureWeakGradient_iff (ordinaryReference h)).mpr
    apply (isWeightedWeakGradient_iff (ordinaryReference h)).mpr
    convert hf.add (hg.smul (-1)) using 1 <;> funext x <;> simp [sub_eq_add_neg]

private theorem variance_mass {h : ℝ} (hh : 0 < h) (f : WeakH1Test (refProb hh))
    (hf : (∫ x, f.fn x ∂(refProb hh : Measure (Torus 1))) = 0) :
    weightedVariance (refProb hh) f.fn = gaussianReferenceMass hh f := by
  unfold weightedVariance gaussianReferenceMass
  rw [hf]
  simp only [sub_zero]

/-- The actual C3 projection cannot increase the nonnegative reference defect. -/
theorem gaussianReferenceAverage_defect_le {h : ℝ} (hh : 0 < h)
    (f : WeakH1Test (refProb hh))
    (hf : (∫ x, f.fn x ∂(refProb hh : Measure (Torus 1))) = 0) :
    gaussianReferenceRealEnergy hh (gaussianReferenceTestAverage hh f) -
        (poincareRate (refProb hh)).toReal * gaussianReferenceMass hh (gaussianReferenceTestAverage hh f) ≤
      gaussianReferenceRealEnergy hh f -
        (poincareRate (refProb hh)).toReal * gaussianReferenceMass hh f := by
  let P := gaussianReferenceTestAverage hh f
  let w := gaussianReferenceTestSubtract hh f P
  have hPm : (∫ x, P.fn x ∂(refProb hh : Measure (Torus 1))) = 0 :=
    (gaussianReferenceAverage_mean hh f).trans hf
  have hwm : (∫ x, w.fn x ∂(refProb hh : Measure (Torus 1))) = 0 := by
    change (∫ x, f.fn x - P.fn x ∂(refProb hh : Measure (Torus 1))) = 0
    rw [integral_sub (f.isWeak.memLp.integrable (by norm_num))
      (P.isWeak.memLp.integrable (by norm_num)), hf, hPm, sub_self]
  have hd := gaussianReference_poincare_real hh w
  rw [variance_mass hh w hwm] at hd
  have hL := gaussianReferenceAverage_mass_split hh f
  have hE := gaussianReferenceAverage_energy_split hh f
  change gaussianReferenceMass hh f = gaussianReferenceMass hh P + gaussianReferenceMass hh w at hL
  change gaussianReferenceRealEnergy hh f =
    gaussianReferenceRealEnergy hh P + gaussianReferenceRealEnergy hh w at hE
  change gaussianReferenceRealEnergy hh P -
      (poincareRate (refProb hh)).toReal * gaussianReferenceMass hh P ≤
    gaussianReferenceRealEnergy hh f -
      (poincareRate (refProb hh)).toReal * gaussianReferenceMass hh f
  rw [hL, hE]
  nlinarith only [hd]

private theorem integral_product_sq {μ : ProbabilityMeasure (Torus 1)}
    {f g : Torus 1 → ℝ} (hf : MemLp f 2 (μ : Measure (Torus 1)))
    (hg : MemLp g 2 (μ : Measure (Torus 1))) :
    (∫ x, f x * g x ∂(μ : Measure (Torus 1))) ^ 2 ≤
      (∫ x, f x ^ 2 ∂(μ : Measure (Torus 1))) * ∫ x, g x ^ 2 ∂(μ : Measure (Torus 1)) := by
  have he : inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂(μ : Measure (Torus 1)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp [sq, mul_comm]
  have hs := pow_le_pow_left₀ (abs_nonneg (inner ℝ (hf.toLp f) (hg.toLp g)))
    (abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)) 2
  have hn (k : Torus 1 → ℝ) (hk : MemLp k 2 (μ : Measure (Torus 1))) :
      ‖hk.toLp k‖ ^ 2 = ∫ x, k x ^ 2 ∂(μ : Measure (Torus 1)) := by
    rw [Structural.norm_sq_eq_integral_sq μ]
    apply integral_congr_ae
    filter_upwards [hk.coeFn_toLp] with x hx
    rw [hx]
  rw [sq_abs, he, mul_pow, hn f hf, hn g hg] at hs
  exact hs

/-- The invariant negative feature is controlled by the original reference
Poincare defect, uniformly over every centered native weak test. -/
theorem gaussianReference_third_moment_defect {h : ℝ} (hh : 0 < h)
    (hhsmall : |h| ≤ 1 / 1000) (f : WeakH1Test (refProb hh))
    (hf : (∫ x, f.fn x ∂(refProb hh : Measure (Torus 1))) = 0) :
    (∫ x, featureB h x * f.fn x ∂(refProb hh : Measure (Torus 1))) ^ 2 ≤
      ((∫ x, featureB h x ^ 2 ∂(refProb hh : Measure (Torus 1))) / a0) *
        (gaussianReferenceRealEnergy hh f -
          (poincareRate (refProb hh)).toReal * gaussianReferenceMass hh f) := by
  let P := gaussianReferenceTestAverage hh f
  have hPm : (∫ x, P.fn x ∂(refProb hh : Measure (Torus 1))) = 0 :=
    (gaussianReferenceAverage_mean hh f).trans hf
  obtain ⟨hc, hs⟩ := gaussianReferenceAverage_first_moments hh f
  have hc' : (∫ x, P.fn x * cosHarm 1 x ∂(refProb hh : Measure (Torus 1))) = 0 := by
    have he : (fun x => P.fn x * cosHarm 1 x) = fun x => h * (featureC h x * P.fn x) := by
      funext x; unfold featureC; field_simp [hh.ne'] <;> ring
    rw [he, integral_const_mul, hc, mul_zero]
  have hs' : (∫ x, P.fn x * sinHarm 1 x ∂(refProb hh : Measure (Torus 1))) = 0 := by
    have he : (fun x => P.fn x * sinHarm 1 x) = fun x => h * (featureS h x * P.fn x) := by
      funext x; unfold featureS; field_simp [hh.ne'] <;> ring
    rw [he, integral_const_mul, hs, mul_zero]
  have hg := threefold_reference_constrained_gap_native hh hhsmall P hc' hs'
  rw [gaussianReference_energy_eq_ofReal, variance_mass hh P hPm] at hg
  have hg' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
  have hL : 0 ≤ gaussianReferenceMass hh P := integral_nonneg fun _ => sq_nonneg _
  have hE : 0 ≤ gaussianReferenceRealEnergy hh P := integral_nonneg fun _ => sq_nonneg _
  have hnonneg : 0 ≤ 2 * a0 * gaussianReferenceMass hh P :=
    mul_nonneg (mul_nonneg (by norm_num) a0_pos.le) hL
  rw [ENNReal.toReal_ofReal hnonneg,
    ENNReal.toReal_ofReal hE] at hg'
  have hp := ENNReal.toReal_mono ENNReal.ofReal_ne_top (threefold_reference_poincare_upper hh)
  rw [ENNReal.toReal_ofReal a0_pos.le] at hp
  have hd := gaussianReferenceAverage_defect_le hh f hf
  change gaussianReferenceRealEnergy hh P -
      (poincareRate (refProb hh)).toReal * gaussianReferenceMass hh P ≤
    gaussianReferenceRealEnergy hh f -
      (poincareRate (refProb hh)).toReal * gaussianReferenceMass hh f at hd
  have hmass : a0 * gaussianReferenceMass hh P ≤ gaussianReferenceRealEnergy hh f -
      (poincareRate (refProb hh)).toReal * gaussianReferenceMass hh f := by
    nlinarith only [hg', hd, mul_le_mul_of_nonneg_right hp hL]
  have hbL : MemLp (featureB h) 2 (refProb hh : Measure (Torus 1)) :=
    (featureB_continuous h).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcs := integral_product_sq hbL P.isWeak.memLp
  rw [gaussianReferenceAverage_third_moment hh f] at hcs
  have hB : 0 ≤ ∫ x, featureB h x ^ 2 ∂(refProb hh : Measure (Torus 1)) :=
    integral_nonneg fun _ => sq_nonneg _
  calc
    _ ≤ (∫ x, featureB h x ^ 2 ∂(refProb hh : Measure (Torus 1))) * gaussianReferenceMass hh P := hcs
    _ ≤ _ := by
      have hm : gaussianReferenceMass hh P ≤
          (gaussianReferenceRealEnergy hh f -
            (poincareRate (refProb hh)).toReal * gaussianReferenceMass hh f) / a0 :=
        (le_div_iff₀ a0_pos).2 (by simpa only [mul_comm] using hmass)
      have hm' := mul_le_mul_of_nonneg_left hm hB
      simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hm'

end DGPS.Examples.ThreeSpeciesCircle
