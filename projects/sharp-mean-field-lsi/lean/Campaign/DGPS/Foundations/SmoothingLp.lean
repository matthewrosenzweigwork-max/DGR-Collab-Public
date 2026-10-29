import DGPS.Foundations.Torus
import SharpSymmetricLSI.Infra.MollifyL2

/-!
# Periodic mollification in `Lᵖ(m)`, `1 ≤ p < ∞` (FOU002, part 1)

The periodic smoothing operators are the legacy torus mollifiers `SharpLSI.moll n`:
`moll n f (y) = ∫ φₙ(s) f(y - s) ds`, with `φₙ = SharpLSI.phiSeq n` a nonnegative `C^∞` bump of
integral one supported in the ball of radius `2/(n+2)` of `ℝ^d` (convolution through the periodic
lift; equivalently, convolution on `𝕋^d` with the periodization of `φₙ`).

* `rpow_lintegral_le`: Jensen `(∫ w g)^p ≤ ∫ w g^p` for a probability weight `w`, `p ≥ 1`;
* `lintegral_moll_rpow_le`, `eLpNorm_moll_le`: `moll n` is an `Lᵖ(m)` contraction;
* `tendsto_eLpNorm_moll_sub`: `moll n f → f` in `Lᵖ(m)` for `f ∈ Lᵖ(m)`, `1 ≤ p < ∞`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS

/-- Jensen's inequality `(∫ w g)^p ≤ ∫ w g^p` for a probability weight `w` and `p ≥ 1`. -/
theorem rpow_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {w g : α → ℝ≥0∞}
    {p : ℝ} (hp : 1 ≤ p) (hw : AEMeasurable w μ) (hg : AEMeasurable g μ)
    (hw1 : ∫⁻ x, w x ∂μ = 1) :
    (∫⁻ x, w x * g x ∂μ) ^ p ≤ ∫⁻ x, w x * g x ^ p ∂μ := by
  rcases hp.eq_or_lt with rfl | hp1
  · simp
  set q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  set s : α → ℝ≥0∞ := fun x => w x ^ (1 / q) with hs
  set t : α → ℝ≥0∞ := fun x => w x ^ (1 / p) * g x with ht
  have hts : ∀ x, t x * s x = w x * g x := fun x => by
    simp only [ht, hs]
    rw [mul_comm (w x ^ (1 / p)), mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _
      (by positivity) (by positivity), hpq.one_div_add_one_div, div_one, ENNReal.rpow_one,
      mul_comm]
  have hsq : ∀ x, s x ^ q = w x := fun x => by
    simp only [hs]
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  have htp : ∀ x, t x ^ p = w x * g x ^ p := fun x => by
    simp only [ht]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
      one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
  have hsm : AEMeasurable s μ := hw.pow_const _
  have htm : AEMeasurable t μ := (hw.pow_const _).mul hg
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq htm hsm
  simp only [Pi.mul_apply, hts, hsq, htp, hw1, ENNReal.one_rpow, mul_one] at h
  calc (∫⁻ x, w x * g x ∂μ) ^ p ≤ ((∫⁻ x, w x * g x ^ p ∂μ) ^ (1 / p)) ^ p :=
        ENNReal.rpow_le_rpow h hp0.le
    _ = ∫⁻ x, w x * g x ^ p ∂μ := by
        rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]

variable {d : ℕ}

open SharpLSI in
/-- Mollification is an `Lᵖ(m)` contraction (measurable case). -/
theorem lintegral_moll_rpow_le_of_measurable (n : ℕ) {p : ℝ} (hp : 1 ≤ p) {u : Torus d → ℝ}
    (hu : Measurable u) (hi : Integrable u (haar d)) :
    ∫⁻ y, ‖moll n u y‖ₑ ^ p ∂haar d ≤ ∫⁻ y, ‖u y‖ₑ ^ p ∂haar d := by
  have hU : Measurable (u ∘ liftT) := hu.comp measurable_liftT
  show ∫⁻ y, ‖moll n u y‖ₑ ^ p ≤ ∫⁻ y, ‖u y‖ₑ ^ p
  rw [← (measurePreserving_liftT (ι := Fin d)).lintegral_comp
    ((measurable_moll n hi).enorm.pow_const p)]
  simp_rw [show ∀ x, moll n u (liftT x) = mollL n (u ∘ liftT) x from
    fun x => congrFun (moll_comp_liftT n u) x]
  have hφm : Measurable fun s : Fin d → ℝ => ENNReal.ofReal (phiSeq n s) :=
    ENNReal.measurable_ofReal.comp (contDiff_phiSeq n).continuous.measurable
  have hmeas : Measurable (Function.uncurry fun (x s : Fin d → ℝ) =>
      ENNReal.ofReal (phiSeq n s) * ‖(u ∘ liftT) (x - s)‖ₑ ^ p) :=
    (hφm.comp measurable_snd).mul ((hU.comp (measurable_fst.sub measurable_snd)).enorm.pow_const p)
  calc ∫⁻ x in unitBox (Fin d), ‖mollL n (u ∘ liftT) x‖ₑ ^ p
      ≤ ∫⁻ x in unitBox (Fin d), ∫⁻ s, ENNReal.ofReal (phiSeq n s) *
          ‖(u ∘ liftT) (x - s)‖ₑ ^ p := by
        refine lintegral_mono fun x => ?_
        calc ‖mollL n (u ∘ liftT) x‖ₑ ^ p
            ≤ (∫⁻ s, ENNReal.ofReal (phiSeq n s) * ‖(u ∘ liftT) (x - s)‖ₑ) ^ p :=
              ENNReal.rpow_le_rpow (enorm_mollL_le n _ x) (by linarith)
          _ ≤ _ := rpow_lintegral_le hp hφm.aemeasurable
              ((hU.comp (measurable_const.sub measurable_id)).enorm.aemeasurable)
              (lintegral_ofReal_phiSeq n)
    _ = ∫⁻ s, ∫⁻ x in unitBox (Fin d), ENNReal.ofReal (phiSeq n s) *
          ‖(u ∘ liftT) (x - s)‖ₑ ^ p :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ s, ENNReal.ofReal (phiSeq n s) * ∫⁻ y, ‖u y‖ₑ ^ p := by
        refine lintegral_congr fun s => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_unitBox_sub (hu.enorm.pow_const p) s
    _ = ∫⁻ y, ‖u y‖ₑ ^ p := by
        rw [lintegral_mul_const _ hφm, lintegral_ofReal_phiSeq, one_mul]

/-- Mollification is an `Lᵖ(m)` contraction, `p ≥ 1` (lintegral form). -/
theorem lintegral_moll_rpow_le (n : ℕ) {p : ℝ} (hp : 1 ≤ p) {u : Torus d → ℝ}
    (hi : Integrable u (haar d)) :
    ∫⁻ y, ‖SharpLSI.moll n u y‖ₑ ^ p ∂haar d ≤ ∫⁻ y, ‖u y‖ₑ ^ p ∂haar d := by
  set v := hi.aestronglyMeasurable.mk u with hv
  have huv : u =ᵐ[haar d] v := hi.aestronglyMeasurable.ae_eq_mk
  rw [SharpLSI.moll_congr_ae n huv]
  calc ∫⁻ y, ‖SharpLSI.moll n v y‖ₑ ^ p ∂haar d ≤ ∫⁻ y, ‖v y‖ₑ ^ p ∂haar d :=
        lintegral_moll_rpow_le_of_measurable n hp
          hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable (hi.congr huv)
    _ = ∫⁻ y, ‖u y‖ₑ ^ p ∂haar d :=
        (lintegral_congr_ae (huv.mono fun y hy => by simp [hy])).symm

theorem integrable_of_memLp {p : ℝ≥0∞} (hp : 1 ≤ p) {u : Torus d → ℝ}
    (hu : MemLp u p (haar d)) : Integrable u (haar d) :=
  (hu.mono_exponent hp).integrable le_rfl

theorem aestronglyMeasurable_moll (n : ℕ) {u : Torus d → ℝ} (hi : Integrable u (haar d)) :
    AEStronglyMeasurable (SharpLSI.moll n u) (haar d) :=
  (SharpLSI.measurable_moll n hi).aestronglyMeasurable

/-- Mollification is an `Lᵖ(m)` contraction, `1 ≤ p < ∞`. -/
theorem eLpNorm_moll_le (n : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {u : Torus d → ℝ}
    (hu : MemLp u p (haar d)) :
    eLpNorm (SharpLSI.moll n u) p (haar d) ≤ eLpNorm u p (haar d) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hp' hp
  have hi := integrable_of_memLp hp hu
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' (aestronglyMeasurable_moll n hi),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hi.aestronglyMeasurable]
  exact ENNReal.rpow_le_rpow (lintegral_moll_rpow_le n hpr hi)
    (by positivity)

theorem memLp_moll (n : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {u : Torus d → ℝ}
    (hu : MemLp u p (haar d)) : MemLp (SharpLSI.moll n u) p (haar d) :=
  (eLpNorm_moll_le n hp hp' hu).trans_lt hu

/-- `moll n f → f` in `Lᵖ(m)` for `f ∈ Lᵖ(m)`, `1 ≤ p < ∞` (approximate identity). -/
theorem tendsto_eLpNorm_moll_sub {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : Torus d → ℝ}
    (hf : MemLp f p (haar d)) :
    Tendsto (fun n => eLpNorm (fun y => SharpLSI.moll n f y - f y) p (haar d)) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  -- `ε = δ + δ + δ` with `δ = ε / 3`
  obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ δ + δ + δ ≤ ε := by
    rcases eq_or_ne ε ∞ with rfl | hε'
    · exact ⟨1, one_ne_zero, by simp⟩
    refine ⟨ε / 3, (ENNReal.div_pos hε.ne' (by simp)).ne', le_of_eq ?_⟩
    rw [← two_mul, ← add_one_mul]
    norm_num
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  obtain ⟨h, hfh, hhp⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le hp' hδ0
  have hfi := integrable_of_memLp hp hf
  have hhi := integrable_of_memLp hp hhp
  -- uniform convergence for the continuous approximant
  obtain ⟨η, hη0, hηδ⟩ : ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal η ≤ δ := by
    rcases eq_or_ne δ ∞ with rfl | hδ'
    · exact ⟨1, one_pos, le_top⟩
    refine ⟨δ.toReal, ENNReal.toReal_pos hδ0 hδ', ?_⟩
    rw [ENNReal.ofReal_toReal hδ']
  have hunif := SharpLSI.moll_uniform_of_continuous h.continuous hη0
  filter_upwards [hunif] with n hn
  have hsplit : (fun y => SharpLSI.moll n f y - f y) =
      (fun y => SharpLSI.moll n (fun z => f z - h z) y) +
        ((fun y => SharpLSI.moll n h y - h y) + (fun y => h y - f y)) := by
    funext y
    simp only [Pi.add_apply, SharpLSI.moll_sub n hfi hhi]
    ring
  have hm1 : AEStronglyMeasurable (fun y => SharpLSI.moll n (fun z => f z - h z) y) (haar d) :=
    aestronglyMeasurable_moll n (hfi.sub hhi)
  have hm2 : AEStronglyMeasurable (fun y => SharpLSI.moll n h y - h y) (haar d) :=
    (aestronglyMeasurable_moll n hhi).sub hhi.aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun y => h y - f y) (haar d) :=
    hhi.aestronglyMeasurable.sub hfi.aestronglyMeasurable
  rw [hsplit]
  refine (eLpNorm_add_le hp).trans ?_
  refine le_trans ?_ hδε
  rw [add_assoc]
  gcongr
  · calc eLpNorm (fun y => SharpLSI.moll n (fun z => f z - h z) y) p (haar d)
        ≤ eLpNorm (fun z => f z - h z) p (haar d) := eLpNorm_moll_le n hp hp' (hf.sub hhp)
      _ ≤ δ := hfh
  · refine (eLpNorm_add_le hp).trans (add_le_add ?_ ?_)
    · refine (eLpNorm_le_of_ae_bound (C := η) hm2 (Eventually.of_forall fun y => ?_)).trans ?_
      · rw [Real.norm_eq_abs, ← Real.dist_eq]; exact hn y
      · simpa using hηδ
    · rw [← eLpNorm_neg]
      convert hfh using 2
      funext y
      simp
