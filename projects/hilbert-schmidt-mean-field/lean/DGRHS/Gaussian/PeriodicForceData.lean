import DGRHS.Gaussian.PeriodicDynamicDrift
import DGRHS.Gaussian.PeriodicRieszTransportBounds
import DGRHS.Gaussian.PeriodicRieszNorms
import DGRHS.Gaussian.PeriodicLogTransportBound
import DGRHS.Gaussian.PeriodicLogKernelSections

/-!
Packet P11c, unit 3 (part 3): the torus Riesz and LOG interaction forces as `PeriodicForceData`.

The force is the gradient of the smooth lift of the periodic kernel (`periodicForceOfSmooth`).  The `n = 1`
transport kernel of Theorem 2.8 is exactly `⟪F(x-y), v x - v y⟫` (`periodicRieszTransportKernel_one`,
`periodicLogTransportKernel_one`), so the uniform section bounds follow from the pointwise bounds of the
P9h chain: the bounded LOG kernel, and the integrable positive majorant for Riesz.
-/

noncomputable section
open MeasureTheory Set
open scoped NNReal RealInnerProductSpace ENNReal BigOperators Classical
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma measurable_periodicForcePair_of_force {F : PeriodicTorus ι → E} (hF : Measurable F)
    {v : PeriodicTorus ι → E} (hv : Measurable v) : Measurable (periodicForcePair F v) := by
  unfold periodicForcePair
  have hF' : Measurable (fun p : PeriodicTorus ι × PeriodicTorus ι => F (p.1 - p.2)) :=
    hF.comp (measurable_fst.sub measurable_snd)
  exact hF'.inner ((hv.comp measurable_fst).sub (hv.comp measurable_snd))

/-! ### LOG -/

lemma periodicLogSmooth_contDiffOn (n : ℕ) :
    ContDiffOn ℝ n (periodicLogSmooth (ι := ι)) (periodicOffLattice : Set E) :=
  fun _ hz => (periodicLogSmooth_contDiffAt n hz).contDiffWithinAt

lemma measurable_periodicLogForce :
    Measurable (periodicForceOfSmooth (periodicLogSmooth (ι := ι)) : PeriodicTorus ι → E) :=
  measurable_periodicForceOfSmooth (periodicLogSmooth_contDiffOn 1)

lemma periodicLog_section_bound (K : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : PeriodicTorus ι → E}, LipschitzWith K v → ∀ x : PeriodicTorus ι,
      Integrable (fun y => periodicForcePair (periodicForceOfSmooth (periodicLogSmooth (ι := ι))) v (x, y))
        (periodicHaar ι) ∧
      ∫ y, |periodicForcePair (periodicForceOfSmooth (periodicLogSmooth (ι := ι))) v (x, y)|
        ∂periodicHaar ι ≤ C := by
  obtain ⟨C0, hC0, hb⟩ := periodicLogTransportKernel_bound (ι := ι) 1 le_rfl
  refine ⟨C0 * (K : ℝ), by positivity, ?_⟩
  intro v hv x
  have hbound : ∀ y, |periodicForcePair (periodicForceOfSmooth (periodicLogSmooth (ι := ι))) v (x, y)| ≤
      C0 * (K : ℝ) := by
    intro y
    have := hb hv (x, y)
    rw [periodicLogTransportKernel_one] at this
    simpa using this
  have hm : Measurable (fun y => periodicForcePair
      (periodicForceOfSmooth (periodicLogSmooth (ι := ι))) v (x, y)) :=
    (measurable_periodicForcePair_of_force measurable_periodicLogForce hv.continuous.measurable).comp
      (measurable_const.prodMk measurable_id)
  refine ⟨(integrable_const (C0 * (K : ℝ))).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hbound y), ?_⟩
  calc ∫ y, |periodicForcePair (periodicForceOfSmooth (periodicLogSmooth (ι := ι))) v (x, y)|
        ∂periodicHaar ι ≤ ∫ _y, C0 * (K : ℝ) ∂periodicHaar ι :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall hbound)
    _ = C0 * (K : ℝ) := by simp

/-- The torus LOG interaction force. -/
def periodicLogForceData : PeriodicForceData ι where
  F := periodicForceOfSmooth (periodicLogSmooth (ι := ι))
  measurable := measurable_periodicLogForce
  odd := periodicForceOfSmooth_odd periodicLogSmooth_neg periodicLogSmooth_add_lattice
  section_bound := periodicLog_section_bound

/-! ### Riesz -/

lemma periodicRieszSmooth_contDiffAt (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (n : ℕ)
    {z : E} (hz : z ∈ (periodicOffLattice : Set E)) :
    ContDiffAt ℝ n (periodicRieszSmooth (ι := ι) s) z := by
  have hc0 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have hP := periodicProfileSum_contDiffAt (ι := ι) (periodicRieszSmoothCoeff ι s) s periodicRieszTau
    hc0 hs periodicRieszTau_pos (Ioc 0 periodicRieszTau) measurableSet_Ioc (subset_refl _) n hz
  have hL : ContDiffAt ℝ n (periodicRieszLongKernel (ι := ι) s (periodicHeatCut periodicRieszTau)) z :=
    (contDiff_periodicRieszLongKernel s (periodicHeatCut periodicRieszTau) hs hs2
      (periodicHeatCut_pos periodicRieszTau_pos) n).contDiffAt
  have h := (hP.add hL).sub (contDiffAt_const (c := periodicRieszMellinFactor ι s *
    (periodicHeatCut periodicRieszTau) ^ (((Fintype.card ι : ℝ) - s) / 2) /
      (((Fintype.card ι : ℝ) - s) / 2)))
  exact h

lemma periodicRieszSmooth_contDiffOn (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (n : ℕ) :
    ContDiffOn ℝ n (periodicRieszSmooth (ι := ι) s) (periodicOffLattice : Set E) :=
  fun _ hz => (periodicRieszSmooth_contDiffAt s hs hs2 n hz).contDiffWithinAt

lemma measurable_periodicRieszForce (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    Measurable (periodicForceOfSmooth (periodicRieszSmooth (ι := ι) s) : PeriodicTorus ι → E) :=
  measurable_periodicForceOfSmooth (periodicRieszSmooth_contDiffOn s hs hs2 1)

lemma periodicRiesz_section_bound (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (K : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : PeriodicTorus ι → E}, LipschitzWith K v → ∀ x : PeriodicTorus ι,
      Integrable (fun y => periodicForcePair (periodicForceOfSmooth (periodicRieszSmooth (ι := ι) s)) v
        (x, y)) (periodicHaar ι) ∧
      ∫ y, |periodicForcePair (periodicForceOfSmooth (periodicRieszSmooth (ι := ι) s)) v (x, y)|
        ∂periodicHaar ι ≤ C := by
  set a := sourceRieszGaussianDerivativeConstant 1 * (2 : ℝ) ^ s with ha
  set b := periodicRieszLongBound (ι := ι) s 1 * (Fintype.card ι : ℝ) ^ 1 with hbdef
  have ha0 : 0 ≤ a := by
    have := (sourceRieszGaussianDerivativeConstant_pos 1).le
    positivity
  have hb0 : 0 ≤ b := mul_nonneg (periodicRieszLongBound_nonneg s hs 1) (by positivity)
  have hMaj : Integrable (periodicRieszMajorantFun (ι := ι) s) (periodicHaar ι) :=
    (periodicRieszMajorantFun_memLp s hs hs2).integrable one_le_two
  refine ⟨(K : ℝ) * (a * ∫ y, periodicRieszMajorantFun (ι := ι) s y ∂periodicHaar ι + b),
    mul_nonneg K.coe_nonneg (add_nonneg (mul_nonneg ha0
      (integral_nonneg fun y => periodicRieszShortFun_nonneg s 1 hs y)) hb0), ?_⟩
  intro v hv x
  let B := fun y : PeriodicTorus ι => (K : ℝ) * (a * periodicRieszMajorantFun (ι := ι) s (x - y) + b)
  have hMx : Integrable (fun y => periodicRieszMajorantFun (ι := ι) s (x - y)) (periodicHaar ι) :=
    (periodicHaar_preserving_sub_left x).integrable_comp_of_integrable hMaj
  have hBi : Integrable B (periodicHaar ι) :=
    (((hMx.const_mul a).add (integrable_const b)).const_mul (K : ℝ))
  have hbound : ∀ y, |periodicForcePair (periodicForceOfSmooth (periodicRieszSmooth (ι := ι) s)) v
      (x, y)| ≤ B y := by
    intro y
    have hnn : 0 ≤ B y := mul_nonneg K.coe_nonneg (add_nonneg (mul_nonneg ha0
      (periodicRieszShortFun_nonneg s 1 hs _)) hb0)
    by_cases hxy : x = y
    · have : periodicForcePair (periodicForceOfSmooth (periodicRieszSmooth (ι := ι) s)) v (x, y) = 0 := by
        subst hxy
        simp [periodicForcePair, periodicForceOfSmooth_zero]
      rw [this, abs_zero]
      exact hnn
    · have h := periodicRieszTransportKernel_bound 1 le_rfl s hs hs2 hv (x, y)
      rw [periodicRieszTransportKernel_one] at h
      have hx0 : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have hMeq : periodicRieszMajorant (ι := ι) s (periodicCenteredLift (x - y)) =
          periodicRieszMajorantFun (ι := ι) s (x - y) := by
        simp only [periodicRieszMajorantFun, periodicRieszShortFun, ite_eq_right hx0]
        rfl
      simp only [hMeq, pow_one] at h
      simp only [B, ha, hbdef, pow_one]
      calc _ ≤ _ := h
        _ = _ := by ring
  have hm : Measurable (fun y => periodicForcePair
      (periodicForceOfSmooth (periodicRieszSmooth (ι := ι) s)) v (x, y)) :=
    (measurable_periodicForcePair_of_force (measurable_periodicRieszForce s hs hs2)
      hv.continuous.measurable).comp (measurable_const.prodMk measurable_id)
  refine ⟨hBi.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hbound y), ?_⟩
  calc ∫ y, |periodicForcePair (periodicForceOfSmooth (periodicRieszSmooth (ι := ι) s)) v (x, y)|
        ∂periodicHaar ι ≤ ∫ y, B y ∂periodicHaar ι :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hBi
          (Filter.Eventually.of_forall hbound)
    _ = (K : ℝ) * (a * ∫ y, periodicRieszMajorantFun (ι := ι) s y ∂periodicHaar ι + b) := by
        simp only [B]
        rw [integral_const_mul, integral_add (hMx.const_mul a) (integrable_const b),
          integral_const_mul]
        have hinv : (∫ y, periodicRieszMajorantFun (ι := ι) s (x - y) ∂periodicHaar ι) =
            ∫ y, periodicRieszMajorantFun (ι := ι) s y ∂periodicHaar ι :=
          (periodicHaar_preserving_sub_left x).integral_comp
            (MeasurableEquiv.subLeft x).measurableEmbedding _
        rw [hinv]
        simp

/-- The torus Riesz interaction force, `0 < s < d/2`. -/
def periodicRieszForceData (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    PeriodicForceData ι where
  F := periodicForceOfSmooth (periodicRieszSmooth (ι := ι) s)
  measurable := measurable_periodicRieszForce s hs hs2
  odd := periodicForceOfSmooth_odd (periodicRieszSmooth_neg s) (periodicRieszSmooth_add_lattice s)
  section_bound := periodicRiesz_section_bound s hs hs2

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogForceData
#print axioms DGRHS.Periodic.periodicRieszForceData
