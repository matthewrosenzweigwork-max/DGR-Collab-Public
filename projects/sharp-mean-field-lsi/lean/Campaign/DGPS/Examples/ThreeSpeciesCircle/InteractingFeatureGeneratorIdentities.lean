import DGPS.Examples.ThreeSpeciesCircle.InteractingGeneratorCentering

/-! Exact physical generator images of the SAME centered model features.
The extra second/fourth/sixth harmonics are retained. No eigenfeature or
kernel-generator commutation identity is asserted. -/

noncomputable section
open MeasureTheory

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem generator_from_lift (h : ℝ) (φ : Torus 1 → ℝ) (hφ : IsSmoothPeriodic φ)
    (F F1 F2 : ℝ → ℝ) (hF : ∀ t, φ (pt t) = F t)
    (hd : ∀ t, HasDerivAt F (F1 t) t) (hd2 : ∀ t, HasDerivAt F1 (F2 t) t) (t : ℝ) :
    elementaryFeatureGenerator h φ (pt t) = -F2 t - sg0 h t * F1 t := by
  have hfun : (fun s => φ (pt s)) = F := funext hF
  have h1 (s : ℝ) : coordPartial 0 φ (pt s) = F1 s := by
    have hh := circ_coordPartial_pt hφ s
    rw [hfun] at hh
    exact hh.unique (hd s)
  have hfun1 : (fun s => coordPartial 0 φ (pt s)) = F1 := funext h1
  have h2 : coordPartial 0 (coordPartial 0 φ) (pt t) = F2 t := by
    have hh := circ_coordPartial_pt (hφ.isSmoothPeriodic_coordPartial 0) t
    rw [hfun1] at hh
    exact hh.unique (hd2 t)
  unfold elementaryFeatureGenerator
  rw [h1, h2, sigT_lift]

/-- The true generator of c_h includes its second/fourth harmonic correction. -/
theorem elementaryFeatureGenerator_C {h : ℝ} (hh : 0 < h) (x : Torus 1) :
    elementaryFeatureGenerator h (featureC h) x =
      a0 * featureC h x + 3 * a0 / 2 * (cosHarm 4 x - cosHarm 2 x) := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  have hF (s : ℝ) : featureC h (pt s) = Real.cos (2 * Real.pi * s) / h := by
    simp only [featureC, cosHarm_pt, Nat.cast_one, mul_one]
  have hd (s : ℝ) : HasDerivAt (fun s => Real.cos (2 * Real.pi * s) / h)
      (-(2 * Real.pi) * Real.sin (2 * Real.pi * s) / h) s := by
    convert (((hasDerivAt_id s).const_mul (2 * Real.pi)).cos.div_const h) using 1 <;> simp only [id_eq] <;> first | (funext y; ring) | ring
  have hd2 (s : ℝ) : HasDerivAt
      (fun s => -(2 * Real.pi) * Real.sin (2 * Real.pi * s) / h)
      (-(2 * Real.pi) ^ 2 * Real.cos (2 * Real.pi * s) / h) s := by
    convert ((((hasDerivAt_id s).const_mul (2 * Real.pi)).sin.const_mul (-(2 * Real.pi))).div_const h)
      using 1 <;> simp only [id_eq] <;> first | (funext y; ring) | ring
  have hg := generator_from_lift h (featureC h) (smooth_featureC h) _ _ _ hF hd hd2 t
  rw [hg]
  simp only [featureC, cosHarm_pt, Nat.cast_ofNat, Nat.cast_one, mul_one]
  have hc4 : Real.cos (2 * Real.pi * 4 * t) =
      Real.cos (6 * Real.pi * t) * Real.cos (2 * Real.pi * t) -
        Real.sin (6 * Real.pi * t) * Real.sin (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * 4 * t = 6 * Real.pi * t + 2 * Real.pi * t by ring, Real.cos_add]
  have hc2 : Real.cos (2 * Real.pi * 2 * t) =
      Real.cos (6 * Real.pi * t) * Real.cos (2 * Real.pi * t) +
        Real.sin (6 * Real.pi * t) * Real.sin (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * 2 * t = 6 * Real.pi * t - 2 * Real.pi * t by ring, Real.cos_sub]
  rw [hc4, hc2]
  unfold a0 sg0
  field_simp [hh.ne']
  <;> ring

/-- The sine feature has the same C3 charge but a distinct genuine generator image. -/
theorem elementaryFeatureGenerator_S {h : ℝ} (hh : 0 < h) (x : Torus 1) :
    elementaryFeatureGenerator h (featureS h) x =
      a0 * featureS h x + 3 * a0 / 2 * (sinHarm 4 x + sinHarm 2 x) := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  have hF (s : ℝ) : featureS h (pt s) = Real.sin (2 * Real.pi * s) / h := by
    simp only [featureS, sinHarm_pt, Nat.cast_one, mul_one]
  have hd (s : ℝ) : HasDerivAt (fun s => Real.sin (2 * Real.pi * s) / h)
      ((2 * Real.pi) * Real.cos (2 * Real.pi * s) / h) s := by
    convert (((hasDerivAt_id s).const_mul (2 * Real.pi)).sin.div_const h) using 1 <;> simp only [id_eq] <;> first | (funext y; ring) | ring
  have hd2 (s : ℝ) : HasDerivAt
      (fun s => (2 * Real.pi) * Real.cos (2 * Real.pi * s) / h)
      (-(2 * Real.pi) ^ 2 * Real.sin (2 * Real.pi * s) / h) s := by
    convert ((((hasDerivAt_id s).const_mul (2 * Real.pi)).cos.const_mul (2 * Real.pi)).div_const h)
      using 1 <;> simp only [id_eq] <;> first | (funext y; ring) | ring
  have hg := generator_from_lift h (featureS h) (smooth_featureS h) _ _ _ hF hd hd2 t
  rw [hg]
  simp only [featureS, sinHarm_pt, Nat.cast_ofNat, Nat.cast_one, mul_one]
  have hs4 : Real.sin (2 * Real.pi * 4 * t) =
      Real.sin (6 * Real.pi * t) * Real.cos (2 * Real.pi * t) +
        Real.cos (6 * Real.pi * t) * Real.sin (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * 4 * t = 6 * Real.pi * t + 2 * Real.pi * t by ring, Real.sin_add]
  have hs2 : Real.sin (2 * Real.pi * 2 * t) =
      Real.sin (6 * Real.pi * t) * Real.cos (2 * Real.pi * t) -
        Real.cos (6 * Real.pi * t) * Real.sin (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * 2 * t = 6 * Real.pi * t - 2 * Real.pi * t by ring, Real.sin_sub]
  rw [hs4, hs2]
  unfold a0 sg0
  field_simp [hh.ne']
  <;> ring

/-- The centered third feature retains its exact centered sixth-harmonic correction. -/
theorem elementaryFeatureGenerator_B {h : ℝ} (hh : 0 < h) (x : Torus 1) :
    elementaryFeatureGenerator h (featureB h) x =
      9 * a0 * featureB h x + 135 * a0 / (8 * h ^ 2) *
        (cosHarm 6 x - besselI 2 h / besselI 0 h) := by
  obtain ⟨t, rfl⟩ := circ_exists_pt x
  have hF (s : ℝ) : featureB h (pt s) =
      15 * (Real.cos (6 * Real.pi * s) - referenceMean h) / (4 * h ^ 3) := by
    simp only [featureB, cosHarm_pt, Nat.cast_ofNat]
    congr 3 <;> ring
  have hd (s : ℝ) : HasDerivAt
      (fun s => 15 * (Real.cos (6 * Real.pi * s) - referenceMean h) / (4 * h ^ 3))
      (-(90 * Real.pi) * Real.sin (6 * Real.pi * s) / (4 * h ^ 3)) s := by
    convert (((((hasDerivAt_id s).const_mul (6 * Real.pi)).cos.sub_const
      (referenceMean h)).const_mul 15).div_const (4 * h ^ 3)) using 1 <;> simp only [id_eq] <;> first | (funext y; ring) | ring
  have hd2 (s : ℝ) : HasDerivAt
      (fun s => -(90 * Real.pi) * Real.sin (6 * Real.pi * s) / (4 * h ^ 3))
      (-(540 * Real.pi ^ 2) * Real.cos (6 * Real.pi * s) / (4 * h ^ 3)) s := by
    convert (((((hasDerivAt_id s).const_mul (6 * Real.pi)).sin.const_mul
      (-(90 * Real.pi))).div_const (4 * h ^ 3))) using 1 <;> simp only [id_eq] <;> first | (funext y; ring) | ring
  have hg := generator_from_lift h (featureB h) (smooth_featureB h) _ _ _ hF hd hd2 t
  rw [hg]
  have hc6 : Real.cos (2 * Real.pi * 6 * t) = 1 - 2 * Real.sin (6 * Real.pi * t) ^ 2 := by
    rw [show 2 * Real.pi * 6 * t = 6 * Real.pi * t + 6 * Real.pi * t by ring, Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq (6 * Real.pi * t)]
  simp only [featureB, cosHarm_pt, Nat.cast_ofNat]
  rw [hc6]
  have hc3 : Real.cos (2 * Real.pi * 3 * t) = Real.cos (6 * Real.pi * t) := by congr 1 <;> ring
  rw [hc3]
  obtain ⟨_, _, _, _, _, _, hrec⟩ := threefoldReference_integral_properties hh
  rw [hrec]
  unfold a0 sg0
  field_simp [hh.ne', besselI_zero_pos.ne']
  <;> ring

end DGPS.Examples.ThreeSpeciesCircle
