import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentCalculus

/-! A genuine positive extension of the full density segment, with common
compact coefficient bounds for parameter differentiation. No uniform positivity
or coefficient estimate is an input. -/

noncomputable section
open MeasureTheory Filter Topology Set

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Compact positive endpoint roots give a common positive neighborhood of the
ENTIRE closed segment, including both endpoints. All constants precede t and x. -/
theorem h1DensitySegment_uniform_positive_extension (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x) :
    ∃ η m K : ℝ, 0 < η ∧ 0 < m ∧ 0 ≤ K ∧
      ∀ t ∈ Icc (-η) (1 + η), ∀ x,
        m ≤ h1DensitySegmentValue u v t x ∧
        |h1DensitySegmentValue u v t x| ≤ K ∧
        |v x ^ 2 - u x ^ 2| ≤ K ∧
        |Real.log (h1DensitySegmentValue u v t x)| ≤ K ∧
        |(h1DensitySegmentValue u v t x)⁻¹| ≤ K := by
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty (hu.pow 2).continuousOn
  obtain ⟨x1, _, hx1⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty (hv.pow 2).continuousOn
  let m0 := min (u x0 ^ 2) (v x1 ^ 2)
  have hm0 : 0 < m0 := lt_min (sq_pos_of_pos (hup x0)) (sq_pos_of_pos (hvp x1))
  have hmu (x : Torus 1) : m0 ≤ u x ^ 2 := (min_le_left _ _).trans (hx0 (mem_univ x))
  have hmv (x : Torus 1) : m0 ≤ v x ^ 2 := (min_le_right _ _).trans (hx1 (mem_univ x))
  have hdc : Continuous (fun x => v x ^ 2 - u x ^ 2) := (hv.pow 2).sub (hu.pow 2)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hdc.continuousOn
  let B := |C| + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hdB (x : Torus 1) : |v x ^ 2 - u x ^ 2| ≤ B := by
    have hx : |v x ^ 2 - u x ^ 2| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC x (mem_univ x)
    dsimp only [B]
    linarith [le_abs_self C]
  let η := m0 / (2 * B)
  let m := m0 / 2
  have hη : 0 < η := div_pos hm0 (by positivity)
  have hm : 0 < m := half_pos hm0
  have hηB : η * B = m0 / 2 := by
    dsimp only [η]
    field_simp [hB.ne']
  have hpositive (t : ℝ) (ht : t ∈ Icc (-η) (1 + η)) (x : Torus 1) :
      m ≤ h1DensitySegmentValue u v t x := by
    by_cases ht0 : t < 0
    · have hmul : -(η * B) ≤ t * (v x ^ 2 - u x ^ 2) := by
        calc _ = (-η) * B := by ring
          _ ≤ t * B := mul_le_mul_of_nonneg_right ht.1 hB.le
          _ ≤ t * (v x ^ 2 - u x ^ 2) :=
            mul_le_mul_of_nonpos_left (abs_le.mp (hdB x)).2 ht0.le
      have he : h1DensitySegmentValue u v t x = u x ^ 2 + t * (v x ^ 2 - u x ^ 2) := by
        unfold h1DensitySegmentValue
        ring
      rw [he]
      dsimp only [m]
      nlinarith [hmu x]
    · have ht0' : 0 ≤ t := not_lt.mp ht0
      by_cases ht1 : t ≤ 1
      · have hl := mul_le_mul_of_nonneg_left (hmu x) (sub_nonneg.mpr ht1)
        have hr := mul_le_mul_of_nonneg_left (hmv x) ht0'
        unfold h1DensitySegmentValue
        dsimp only [m]
        nlinarith
      · have ht1' : 0 ≤ t - 1 := by linarith
        have hmul := mul_le_mul_of_nonneg_left (abs_le.mp (hdB x)).1 ht1'
        have htb := mul_le_mul_of_nonneg_right (show t - 1 ≤ η by linarith [ht.2]) hB.le
        have he : h1DensitySegmentValue u v t x = v x ^ 2 + (t - 1) * (v x ^ 2 - u x ^ 2) := by
          unfold h1DensitySegmentValue
          ring
        rw [he]
        dsimp only [m]
        nlinarith [hmv x]
  let S : Set (ℝ × Torus 1) := Icc (-η) (1 + η) ×ˢ univ
  have hS : IsCompact S := isCompact_Icc.prod isCompact_univ
  have hT : Continuous (fun p : ℝ × Torus 1 => h1DensitySegmentValue u v p.1 p.2) :=
    ((continuous_const.sub continuous_fst).mul ((hu.comp continuous_snd).pow 2)).add
      (continuous_fst.mul ((hv.comp continuous_snd).pow 2))
  have hD : Continuous (fun p : ℝ × Torus 1 => v p.2 ^ 2 - u p.2 ^ 2) :=
    hdc.comp continuous_snd
  have hn (p : ℝ × Torus 1) (hp : p ∈ S) : h1DensitySegmentValue u v p.1 p.2 ≠ 0 :=
    (hm.trans_le (hpositive p.1 hp.1 p.2)).ne'
  obtain ⟨KT, hKT⟩ := hS.exists_bound_of_continuousOn hT.continuousOn
  obtain ⟨KD, hKD⟩ := hS.exists_bound_of_continuousOn hD.continuousOn
  obtain ⟨KL, hKL⟩ := hS.exists_bound_of_continuousOn (hT.continuousOn.log hn)
  obtain ⟨KI, hKI⟩ := hS.exists_bound_of_continuousOn (hT.continuousOn.inv₀ hn)
  let K := |KT| + |KD| + |KL| + |KI|
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hKTK : KT ≤ K := by dsimp only [K]; linarith [le_abs_self KT, abs_nonneg KD, abs_nonneg KL, abs_nonneg KI]
  have hKDK : KD ≤ K := by dsimp only [K]; linarith [le_abs_self KD, abs_nonneg KT, abs_nonneg KL, abs_nonneg KI]
  have hKLK : KL ≤ K := by dsimp only [K]; linarith [le_abs_self KL, abs_nonneg KT, abs_nonneg KD, abs_nonneg KI]
  have hKIK : KI ≤ K := by dsimp only [K]; linarith [le_abs_self KI, abs_nonneg KT, abs_nonneg KD, abs_nonneg KL]
  refine ⟨η, m, K, hη, hm, hK, fun t ht x => ?_⟩
  have hp : (t, x) ∈ S := ⟨ht, mem_univ x⟩
  refine ⟨hpositive t ht x, ?_, ?_, ?_, ?_⟩
  · exact (show |h1DensitySegmentValue u v t x| ≤ KT by
      simpa only [Real.norm_eq_abs] using hKT (t, x) hp).trans hKTK
  · exact (show |v x ^ 2 - u x ^ 2| ≤ KD by
      simpa only [Real.norm_eq_abs] using hKD (t, x) hp).trans hKDK
  · exact (show |Real.log (h1DensitySegmentValue u v t x)| ≤ KL by
      simpa only [Real.norm_eq_abs] using hKL (t, x) hp).trans hKLK
  · exact (show |(h1DensitySegmentValue u v t x)⁻¹| ≤ KI by
      have hb := hKI (t, x) hp
      have heq : ((fun p : ℝ × Torus 1 => h1DensitySegmentValue u v p.1 p.2)⁻¹) =
          (fun p => (h1DensitySegmentValue u v p.1 p.2)⁻¹) := by
        funext p
        rfl
      rw [heq] at hb
      simpa only [Real.norm_eq_abs, Pi.inv_apply] using hb).trans hKIK

end DGPS.Examples.ThreeSpeciesCircle
