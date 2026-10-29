import SharpSymmetricLSI.Paper.FourierPoincare
import SharpSymmetricLSI.Defs.D12_Cosine

/-!
# (3.28): bounded perturbation of the Poincaré inequality on `𝕋^n` (Phase 3, lane C)

Companion TeX L111–116: with `ρ = e^{-ψ}/Z`, `c = ∫ u dm`,
`Var_ν(u) ≤ ∫ (u-c)² dν ≤ (sup ρ) Var_m(u) ≤ (sup ρ)/(4π²) ∫|∇u|² dm
≤ (sup ρ/inf ρ)/(4π²) ∫|∇u|² dν`, with essential bounds of `ψ`. The Haar Poincaré inequality is
`poincare_haar` (Fourier series).
-/

open MeasureTheory Set Filter
open scoped ENNReal Real

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

/-- `Var_ν(u) ≤ ∫ |u - c|² dν`. -/
theorem var_le_lintegral_sub_sq {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {u : α → ℝ} (hu : MemLp u 2 ν) (c : ℝ) :
    var ν u ≤ ∫⁻ x, ‖u x - c‖ₑ ^ 2 ∂ν := by
  have hc : MemLp (fun x => u x - c) 2 ν := hu.sub (memLp_const c)
  rw [var, ← ProbabilityTheory.ofReal_variance hu,
    ← ProbabilityTheory.variance_sub_const hu.aestronglyMeasurable c]
  refine (ENNReal.ofReal_le_ofReal (ProbabilityTheory.variance_le_expectation_sq
    hc.aestronglyMeasurable)).trans_eq ?_
  simp only [Pi.pow_apply]
  rw [ofReal_integral_eq_lintegral_ofReal hc.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg _)]
  simp only [ofReal_sq_eq_enorm_sq]

/-- (3.28) on `𝕋^ι`, with the essential oscillation of `ψ`. -/
theorem bounded_perturbation_aux [DecidableEq ι] {ψ : UnitAddTorus ι → ℝ}
    (hψ : AEMeasurable ψ volume)
    (hb : ∃ B, ∀ᵐ x ∂(volume : Measure (UnitAddTorus ι)), |ψ x| ≤ B)
    {u : UnitAddTorus ι → ℝ} (hu : MemH1 volume u) :
    var (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-ψ x) / ∫ y, Real.exp (-ψ y))) u ≤
      ENNReal.ofReal (Real.exp (essSup ψ volume - essInf ψ volume) / (4 * π ^ 2)) *
        dirichlet (volume.withDensity
          fun x => ENNReal.ofReal (Real.exp (-ψ x) / ∫ y, Real.exp (-ψ y))) u := by
  obtain ⟨B, hB⟩ := hb
  set M := essSup ψ volume with hMdef
  set m := essInf ψ volume with hmdef
  have hM : ∀ᵐ x ∂(volume : Measure (UnitAddTorus ι)), ψ x ≤ M :=
    ae_le_essSup (isBoundedUnder_of_eventually_le (hB.mono fun x hx => (le_abs_self _).trans hx))
  have hm : ∀ᵐ x ∂(volume : Measure (UnitAddTorus ι)), m ≤ ψ x :=
    ae_essInf_le (isBoundedUnder_of_eventually_ge (a := -B) (hB.mono fun x hx => by
      linarith [neg_abs_le (ψ x)]))
  set Z := ∫ y, Real.exp (-ψ y) with hZdef
  have hexpm : AEStronglyMeasurable (fun y => Real.exp (-ψ y)) volume :=
    (Real.measurable_exp.comp_aemeasurable hψ.neg).aestronglyMeasurable
  have hZi : Integrable (fun y => Real.exp (-ψ y)) volume :=
    Integrable.of_bound hexpm (Real.exp B) (hB.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith [neg_abs_le (ψ x)]))
  have hZ : 0 < Z := integral_exp_pos hZi
  set ρ : UnitAddTorus ι → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-ψ x) / Z) with hρdef
  set ν := (volume : Measure (UnitAddTorus ι)).withDensity ρ with hνdef
  have hρm : AEMeasurable ρ volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hexpm.aemeasurable.div_const Z)
  set Lp := ENNReal.ofReal (Real.exp (-m) / Z) with hLp
  set Lm := ENNReal.ofReal (Real.exp (-M) / Z) with hLm
  have hup : ∀ᵐ x ∂(volume : Measure (UnitAddTorus ι)), ρ x ≤ Lp := hm.mono fun x hx =>
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hZ.le)
  have hlo : ∀ᵐ x ∂(volume : Measure (UnitAddTorus ι)), Lm ≤ ρ x := hM.mono fun x hx =>
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hZ.le)
  have hprob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hνdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hρdef,
      ← ofReal_integral_eq_lintegral_ofReal (hZi.div_const Z)
        (Eventually.of_forall fun x => div_nonneg (Real.exp_pos _).le hZ.le), integral_div,
      div_self hZ.ne', ENNReal.ofReal_one]
  have hle : ν ≤ Lp • volume := by
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [hνdef, withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
    exact lintegral_mono_ae (ae_restrict_of_ae hup)
  have huν : MemLp u 2 ν := hu.2.1.of_measure_le_smul ENNReal.ofReal_ne_top hle
  have hum : AEStronglyMeasurable u volume := hu.2.1.aestronglyMeasurable
  set c := ∫ x, u x with hc
  -- Step 1: `Var_ν(u) ≤ ∫ |u - c|² dν`
  have h1 := var_le_lintegral_sub_sq huν c
  -- Step 2: `∫ |u - c|² dν ≤ (sup ρ) Var_m(u)`
  have h2 : ∫⁻ x, ‖u x - c‖ₑ ^ 2 ∂ν ≤ Lp * var volume u := by
    rw [hνdef, lintegral_withDensity_eq_lintegral_mul₀ hρm
      (g := fun x => ‖u x - c‖ₑ ^ 2)
      (((hum.sub aestronglyMeasurable_const).enorm.pow_const 2))]
    show _ ≤ Lp * ∫⁻ x, ‖u x - c‖ₑ ^ 2
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono_ae (hup.mono fun x hx => mul_le_mul_left hx _)
  -- Step 3: Poincaré for Haar measure
  have h3 := poincare_haar hu
  set A := ENNReal.ofReal (4 * π ^ 2) with hA
  have hA0 : A ≠ 0 := by simp [hA]
  have h3' : var volume u ≤ A⁻¹ * dirichlet volume u := by
    calc var volume u = A⁻¹ * (A * var volume u) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hA0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ A⁻¹ * dirichlet volume u := by gcongr
  -- Step 4: `∫ |∇u|² dm ≤ (inf ρ)⁻¹ ∫ |∇u|² dν`
  have hLm0 : Lm ≠ 0 := by simp [hLm]; exact div_pos (Real.exp_pos _) hZ
  have h4 : dirichlet volume u ≤ Lm⁻¹ * dirichlet ν u := by
    have hw := isWeakGrad_weakGrad hu.1
    unfold dirichlet
    rw [hνdef, lintegral_withDensity_eq_lintegral_mul₀ hρm
      (g := fun x => ENNReal.ofReal (sqNorm (weakGrad u x)))
      ((ENNReal.measurable_ofReal.comp_aemeasurable
        hw.aestronglyMeasurable_sqNorm.aemeasurable)),
      ← lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hLm0)]
    refine lintegral_mono_ae (hlo.mono fun x hx => ?_)
    calc ENNReal.ofReal (sqNorm (weakGrad u x))
        = Lm⁻¹ * (Lm * ENNReal.ofReal (sqNorm (weakGrad u x))) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hLm0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ Lm⁻¹ * (ρ x * ENNReal.ofReal (sqNorm (weakGrad u x))) := by gcongr
  -- the constant
  have hconst : Lp * A⁻¹ * Lm⁻¹ = ENNReal.ofReal (Real.exp (M - m) / (4 * π ^ 2)) := by
    rw [hA, hLm, hLp, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_inv_of_pos (div_pos (Real.exp_pos _) hZ),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.exp_sub, Real.exp_neg, Real.exp_neg]
    field_simp
  calc var ν u ≤ Lp * var volume u := h1.trans h2
    _ ≤ Lp * (A⁻¹ * (Lm⁻¹ * dirichlet ν u)) := by gcongr; exact h3'.trans (by gcongr)
    _ = ENNReal.ofReal (Real.exp (M - m) / (4 * π ^ 2)) * dirichlet ν u := by
        rw [← hconst]; ring

/-- (3.28) as printed (pointwise `sup`, `inf`). -/
theorem bounded_perturbation_sup_aux [DecidableEq ι] {ψ : UnitAddTorus ι → ℝ}
    (hψ : Measurable ψ) (hb : ∃ B, ∀ x, |ψ x| ≤ B) {u : UnitAddTorus ι → ℝ}
    (hu : MemH1 volume u) :
    var (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-ψ x) / ∫ y, Real.exp (-ψ y))) u ≤
      ENNReal.ofReal (Real.exp ((⨆ x, ψ x) - ⨅ x, ψ x) / (4 * π ^ 2)) *
        dirichlet (volume.withDensity
          fun x => ENNReal.ofReal (Real.exp (-ψ x) / ∫ y, Real.exp (-ψ y))) u := by
  obtain ⟨B, hB⟩ := hb
  refine (bounded_perturbation_aux hψ.aemeasurable ⟨B, Eventually.of_forall hB⟩ hu).trans ?_
  have hup : BddAbove (range ψ) := ⟨B, by rintro _ ⟨x, rfl⟩; exact (le_abs_self _).trans (hB x)⟩
  have hlo : BddBelow (range ψ) := ⟨-B, by
    rintro _ ⟨x, rfl⟩; linarith [neg_abs_le (ψ x), hB x]⟩
  have h1 : essSup ψ volume ≤ ⨆ x, ψ x :=
    essSup_le_of_ae_le _ (Eventually.of_forall fun x => le_ciSup hup x)
      (isCoboundedUnder_le_of_eventually_le _ (x := -B) (Eventually.of_forall fun x => by
        linarith [neg_abs_le (ψ x), hB x]))
  have h2 : ⨅ x, ψ x ≤ essInf ψ volume :=
    le_essInf_of_ae_le _ (Eventually.of_forall fun x => ciInf_le hlo x)
      (isCoboundedUnder_ge_of_eventually_le _ (x := B) (Eventually.of_forall fun x =>
        (le_abs_self _).trans (hB x)))
  gcongr

end SharpLSI
