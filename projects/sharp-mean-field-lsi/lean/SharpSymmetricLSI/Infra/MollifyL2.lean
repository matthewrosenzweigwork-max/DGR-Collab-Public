import SharpSymmetricLSI.Infra.Mollify

/-!
# Mollification is an `L²(m)` contraction (Phase 2, I1)

`sq_lintegral_le`: Jensen/Cauchy–Schwarz `(∫ w g)² ≤ ∫ w g²` for a probability weight `w`.
`lintegral_moll_sq_le`: `∫ |moll n u|² dm ≤ ∫ |u|² dm`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

theorem sq_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {w g : α → ℝ≥0∞}
    (hw : AEMeasurable w μ) (hg : AEMeasurable g μ) (hw1 : ∫⁻ x, w x ∂μ = 1) :
    (∫⁻ x, w x * g x ∂μ) ^ 2 ≤ ∫⁻ x, w x * g x ^ 2 ∂μ := by
  have hpq := Real.HolderConjugate.two_two
  set s : α → ℝ≥0∞ := fun x => w x ^ (1 / 2 : ℝ) with hs
  have hs2 : ∀ x, s x ^ (2 : ℝ) = w x := fun x => by
    rw [hs]; simp only; rw [← ENNReal.rpow_mul]; norm_num
  have hsg : ∀ x, (s x * g x) ^ (2 : ℝ) = w x * g x ^ 2 := fun x => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hs2, ENNReal.rpow_two]
  have hss : ∀ x, s x * (s x * g x) = w x * g x := fun x => by
    rw [← mul_assoc, ← sq, ← ENNReal.rpow_two, hs2]
  have hsm : AEMeasurable s μ := hw.pow_const _
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hsm (hsm.mul hg)
  simp only [Pi.mul_apply, hss, hs2, hsg, hw1, ENNReal.one_rpow, one_mul] at h
  calc (∫⁻ x, w x * g x ∂μ) ^ 2 ≤ ((∫⁻ x, w x * g x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = ∫⁻ x, w x * g x ^ 2 ∂μ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

variable {ι : Type*} [Fintype ι]

/-- Mollification is an `L²(m)` contraction (measurable case). -/
theorem lintegral_moll_sq_le_of_measurable (n : ℕ) {u : UnitAddTorus ι → ℝ} (hu : Measurable u)
    (hi : Integrable u volume) : ∫⁻ y, ‖moll n u y‖ₑ ^ 2 ≤ ∫⁻ y, ‖u y‖ₑ ^ 2 := by
  have hU : Measurable (u ∘ liftT) := hu.comp measurable_liftT
  rw [← (measurePreserving_liftT (ι := ι)).lintegral_comp
    ((measurable_moll n hi).enorm.pow_const 2)]
  simp_rw [show ∀ x, moll n u (liftT x) = mollL n (u ∘ liftT) x from
    fun x => congrFun (moll_comp_liftT n u) x]
  have hφm : Measurable fun s : ι → ℝ => ENNReal.ofReal (phiSeq n s) :=
    ENNReal.measurable_ofReal.comp (contDiff_phiSeq n).continuous.measurable
  have hmeas : Measurable (Function.uncurry fun (x s : ι → ℝ) =>
      ENNReal.ofReal (phiSeq n s) * ‖(u ∘ liftT) (x - s)‖ₑ ^ 2) :=
    (hφm.comp measurable_snd).mul ((hU.comp (measurable_fst.sub measurable_snd)).enorm.pow_const 2)
  calc ∫⁻ x in unitBox ι, ‖mollL n (u ∘ liftT) x‖ₑ ^ 2
      ≤ ∫⁻ x in unitBox ι, ∫⁻ s, ENNReal.ofReal (phiSeq n s) * ‖(u ∘ liftT) (x - s)‖ₑ ^ 2 := by
        refine lintegral_mono fun x => ?_
        calc ‖mollL n (u ∘ liftT) x‖ₑ ^ 2
            ≤ (∫⁻ s, ENNReal.ofReal (phiSeq n s) * ‖(u ∘ liftT) (x - s)‖ₑ) ^ 2 :=
              pow_le_pow_left₀ zero_le (enorm_mollL_le n _ x) 2
          _ ≤ _ := sq_lintegral_le hφm.aemeasurable
              ((hU.comp (measurable_const.sub measurable_id)).enorm.aemeasurable)
              (lintegral_ofReal_phiSeq n)
    _ = ∫⁻ s, ∫⁻ x in unitBox ι, ENNReal.ofReal (phiSeq n s) * ‖(u ∘ liftT) (x - s)‖ₑ ^ 2 :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ s, ENNReal.ofReal (phiSeq n s) * ∫⁻ y, ‖u y‖ₑ ^ 2 := by
        refine lintegral_congr fun s => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_unitBox_sub (hu.enorm.pow_const 2) s
    _ = ∫⁻ y, ‖u y‖ₑ ^ 2 := by
        rw [lintegral_mul_const _ hφm, lintegral_ofReal_phiSeq, one_mul]

/-- Mollification is an `L²(m)` contraction. -/
theorem lintegral_moll_sq_le (n : ℕ) {u : UnitAddTorus ι → ℝ} (hi : Integrable u volume) :
    ∫⁻ y, ‖moll n u y‖ₑ ^ 2 ≤ ∫⁻ y, ‖u y‖ₑ ^ 2 := by
  set v := hi.aestronglyMeasurable.mk u with hv
  have huv : u =ᵐ[volume] v := hi.aestronglyMeasurable.ae_eq_mk
  rw [moll_congr_ae n huv]
  calc ∫⁻ y, ‖moll n v y‖ₑ ^ 2 ≤ ∫⁻ y, ‖v y‖ₑ ^ 2 :=
        lintegral_moll_sq_le_of_measurable n
          hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable (hi.congr huv)
    _ = ∫⁻ y, ‖u y‖ₑ ^ 2 := (lintegral_congr_ae (huv.mono fun y hy => by simp [hy])).symm

end SharpLSI
