import FullLabeledLSI.Paper.Sec3Equi

/-!
# Proposition 3.3 (≤), part A: densities `ρ = q u²` relative to a reference density `q`

For a reference density `q` bounded above and below with `√q ∈ H¹` and a bounded nonnegative
`u` with `L²` weak gradient `gu`, the density `ρ = q u²` has `√ρ = √q · u ∈ H¹` and
`I(ρ|q) = ∫ 4 q |gu|² dm`.
-/

noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ}

theorem haar_ac_densMeasure {q : Torus d → ℝ} (hq0 : ∀ x, 0 < q x) (hq1 : ∫ x, q x ∂haar d = 1) :
    haar d ≪ densMeasure q :=
  withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp_aemeasurable
      (integrable_of_integral_eq_one' hq1).aestronglyMeasurable.aemeasurable)
    (Filter.Eventually.of_forall fun x => by simpa using hq0 x)

section SqrtMul

variable {q : Torus d → ℝ} {c C B : ℝ} {u : Torus d → ℝ} {gu : Torus d → Fin d → ℝ}

theorem isWeakGrad_sqrt_mul (hqH : MemH1 (haar d) (fun x => Real.sqrt (q x)))
    (hq0 : ∀ x, 0 ≤ q x) (hu : IsWeakGrad u gu) (hu0 : ∀ x, 0 ≤ u x) (huB : ∀ x, u x ≤ B)
    (hgu : ∀ k, MemLp (fun y => gu y k) 2 (haar d)) :
    IsWeakGrad (fun y => Real.sqrt (q y * u y ^ 2))
      (fun y k => u y * weakGrad (fun x => Real.sqrt (q x)) y k + Real.sqrt (q y) * gu y k) := by
  have hu2 : MemLp u 2 (haar d) :=
    MemLp.of_bound hu.aestronglyMeasurable_fun B (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hu0 x)]; exact huB x)
  have h := isWeakGrad_mul_L2 (isWeakGrad_weakGrad hqH.1) hu hqH.2.1 hu2
    (memLp_comp_weakGrad hqH) hgu
  have e : (fun y => Real.sqrt (q y * u y ^ 2)) = fun y => Real.sqrt (q y) * u y := by
    funext y
    rw [Real.sqrt_mul (hq0 y), Real.sqrt_sq (hu0 y)]
  rw [e]
  convert h using 1

theorem memLp_sqrt_mul_grad (hqH : MemH1 (haar d) (fun x => Real.sqrt (q x)))
    (hqC : ∀ x, q x ≤ C) (hq0 : ∀ x, 0 ≤ q x) (hu : IsWeakGrad u gu) (hu0 : ∀ x, 0 ≤ u x)
    (huB : ∀ x, u x ≤ B) (hgu : ∀ k, MemLp (fun y => gu y k) 2 (haar d)) (k : Fin d) :
    MemLp (fun y => u y * weakGrad (fun x => Real.sqrt (q x)) y k +
      Real.sqrt (q y) * gu y k) 2 (haar d) := by
  have hgq := memLp_comp_weakGrad hqH k
  have hm1 : AEStronglyMeasurable (fun y => u y * weakGrad (fun x => Real.sqrt (q x)) y k)
      (haar d) := hu.aestronglyMeasurable_fun.mul
    ((isWeakGrad_weakGrad hqH.1).aestronglyMeasurable_grad k)
  have hm2 : AEStronglyMeasurable (fun y => Real.sqrt (q y) * gu y k) (haar d) :=
    hqH.2.1.aestronglyMeasurable.mul (hu.aestronglyMeasurable_grad k)
  refine MemLp.add ?_ ?_
  · refine hgq.of_le_mul (c := |B|) hm1 (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hu0 y)]
    exact mul_le_mul_of_nonneg_right ((huB y).trans (le_abs_self B)) (abs_nonneg _)
  · refine (hgu k).of_le_mul (c := Real.sqrt C) hm2 (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hqC y)) (abs_nonneg _)

theorem memH1_sqrt_mul (hqH : MemH1 (haar d) (fun x => Real.sqrt (q x)))
    (hqC : ∀ x, q x ≤ C) (hq0 : ∀ x, 0 ≤ q x) (hu : IsWeakGrad u gu) (hu0 : ∀ x, 0 ≤ u x)
    (huB : ∀ x, u x ≤ B) (hgu : ∀ k, MemLp (fun y => gu y k) 2 (haar d)) :
    MemH1 (haar d) (fun y => Real.sqrt (q y * u y ^ 2)) := by
  have hw := isWeakGrad_sqrt_mul hqH hq0 hu hu0 huB hgu
  refine ⟨⟨_, hw⟩, ?_, ?_⟩
  · refine MemLp.of_bound hw.aestronglyMeasurable_fun (Real.sqrt C * |B|)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_mul (hq0 y),
      Real.sqrt_sq (hu0 y)]
    exact mul_le_mul (Real.sqrt_le_sqrt (hqC y)) ((huB y).trans (le_abs_self B)) (hu0 y)
      (Real.sqrt_nonneg _)
  · have hL : MemLp (fun y => ∑ k, ‖u y * weakGrad (fun x => Real.sqrt (q x)) y k +
        Real.sqrt (q y) * gu y k‖) 2 (haar d) :=
      memLp_finsetSum _ fun k _ => (memLp_sqrt_mul_grad hqH hqC hq0 hu hu0 huB hgu k).norm
    refine hL.of_le (Real.continuous_sqrt.comp_aestronglyMeasurable
      (isWeakGrad_weakGrad ⟨_, hw⟩).aestronglyMeasurable_sqNorm) ?_
    filter_upwards [weakGrad_ae_eq hw] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
    have := sqrt_sqNorm_le_sum_abs (fun k => u y * weakGrad (fun x => Real.sqrt (q x)) y k +
      Real.sqrt (q y) * gu y k)
    rw [hy]
    simpa only [Real.norm_eq_abs] using this

theorem relFisher_sqrt_mul (hc : 0 < c) (hbd : ∀ x, c ≤ q x ∧ q x ≤ C)
    (hq1 : ∫ x, q x ∂haar d = 1) (hqH : MemH1 (haar d) (fun x => Real.sqrt (q x)))
    (hu : IsWeakGrad u gu) (hu0 : ∀ x, 0 ≤ u x) (huB : ∀ x, u x ≤ B)
    (hgu : ∀ k, MemLp (fun y => gu y k) 2 (haar d)) :
    relFisher (fun y => q y * u y ^ 2) q =
      ∫⁻ x, ENNReal.ofReal (4 * (q x * sqNorm (gu x))) ∂haar d := by
  have hq0 : ∀ x, 0 < q x := fun x => hc.trans_le (hbd x).1
  have hqC : ∀ x, q x ≤ C := fun x => (hbd x).2
  have hw := isWeakGrad_sqrt_mul hqH (fun x => (hq0 x).le) hu hu0 huB hgu
  have hmem := memH1_sqrt_mul hqH hqC (fun x => (hq0 x).le) hu hu0 huB hgu
  have hac : densMeasure (fun y => q y * u y ^ 2) ≪ densMeasure q :=
    (withDensity_absolutelyContinuous _ _).trans (haar_ac_densMeasure hq0 hq1)
  unfold relFisher
  rw [if_pos ⟨hac, hmem, hqH⟩]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq hw] with y hy
  congr 1
  rw [hy]
  have hs : 0 < Real.sqrt (q y) := Real.sqrt_pos.2 (hq0 y)
  have hs2 : Real.sqrt (q y) ^ 2 = q y := Real.sq_sqrt (hq0 y).le
  have hk : ∀ k, (2 * (u y * weakGrad (fun x => Real.sqrt (q x)) y k + Real.sqrt (q y) * gu y k) -
      Real.sqrt (q y * u y ^ 2) * score q y k) ^ 2 = 4 * (q y * gu y k ^ 2) := by
    intro k
    simp only [score, if_pos (hq0 y)]
    rw [Real.sqrt_mul (hq0 y).le, Real.sqrt_sq (hu0 y)]
    field_simp
    nlinarith [hs2]
  simp only [sqNorm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => hk k

end SqrtMul

end SharpLSI.FL
