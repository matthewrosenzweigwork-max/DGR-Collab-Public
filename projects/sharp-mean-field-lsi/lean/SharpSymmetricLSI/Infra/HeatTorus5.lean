import SharpSymmetricLSI.Infra.HeatTorus4
import SharpSymmetricLSI.Infra.ChainRule

/-!
# The periodic heat kernel on `𝕋^ι` (I4, part 5): gradients commute with `e^{tΔ}`

If `g` is a weak gradient of `f ∈ L¹(𝕋^ι)` with `g ∈ L¹`, then `e^{tΔ} g` is a weak gradient of
`e^{tΔ} f` (`isWeakGrad_heatT`). Proof: Fubini on `ℝ^ι × ℝ^ι` against the Gaussian, and the
weak-gradient identity tested against translates of the test function.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι]

theorem heatT_liftT (t : ℝ) (f : UnitAddTorus ι → ℝ) (x : ι → ℝ) :
    heatT t f (liftT x) = ∫ y, f (liftT (x - y)) * heatKernel t y := by
  rw [heatT]; simp_rw [liftT_sub]

/-- Fubini integrability for the heat flow tested against a compactly supported function. -/
theorem integrable_heat_test {t : ℝ} (ht : 0 < t) {h : UnitAddTorus ι → ℝ} (hh : Integrable h)
    {ψ : (ι → ℝ) → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun p : (ι → ℝ) × (ι → ℝ) => h (liftT (p.1 - p.2)) * heatKernel t p.2 * ψ p.1)
      (volume.prod volume) := by
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hψc
  obtain ⟨R, hR⟩ := exists_cube_of_hasCompactSupport hψc
  have hmeas : AEStronglyMeasurable
      (fun p : (ι → ℝ) × (ι → ℝ) => h (liftT (p.1 - p.2)) * heatKernel t p.2 * ψ p.1)
      (volume.prod volume) := by
    refine (AEStronglyMeasurable.mul ?_ ?_).mul ?_
    · exact hh.aestronglyMeasurable.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_liftT.comp
          (quasiMeasurePreserving_sub_of_right_invariant volume volume))
    · exact ((measurable_heatKernel t).comp measurable_snd).aestronglyMeasurable
    · exact (hψ.comp continuous_fst).aestronglyMeasurable
  refine ⟨hmeas, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hmeas.enorm]
  -- inner integral in `x`, for fixed `y`
  have hinner : ∀ y : ι → ℝ, ∫⁻ x, ‖h (liftT (x - y)) * heatKernel t y * ψ x‖ₑ ≤
      ENNReal.ofReal C * ((2 * R + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * ∫⁻ z, ‖h z‖ₑ *
        ENNReal.ofReal (heatKernel t y) := by
    intro y
    calc ∫⁻ x, ‖h (liftT (x - y)) * heatKernel t y * ψ x‖ₑ
        ≤ ∫⁻ x, (cube ι R).indicator (fun x => ‖h (liftT x - liftT y)‖ₑ *
            ENNReal.ofReal (heatKernel t y) * ENNReal.ofReal C) x := by
          refine lintegral_mono fun x => ?_
          rw [enorm_mul, enorm_mul, liftT_sub,
            Real.enorm_eq_ofReal (heatKernel_pos ht y).le]
          by_cases hx : x ∈ cube ι R
          · rw [indicator_of_mem hx]
            gcongr
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hC x)
          · have : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hR h))
            simp [this]
      _ = (∫⁻ x in cube ι R, ‖h (liftT x - liftT y)‖ₑ) * ENNReal.ofReal (heatKernel t y) *
            ENNReal.ofReal C := by
          rw [lintegral_indicator (show MeasurableSet (cube ι R) from
              MeasurableSet.univ_pi fun _ => measurableSet_Icc),
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
            lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
      _ ≤ (((2 * R + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * ∫⁻ z, ‖h z‖ₑ) *
            ENNReal.ofReal (heatKernel t y) * ENNReal.ofReal C := by
          gcongr
          have := lintegral_cube_le (H := fun z => ‖h (z - liftT y)‖ₑ) R
            (hh.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
              (measurePreserving_sub_right volume (liftT y)).quasiMeasurePreserving)
          refine this.trans (le_of_eq ?_)
          congr 1
          exact lintegral_sub_right_eq_self (fun z => ‖h z‖ₑ) (liftT y)
      _ = _ := by rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]; ring
  calc ∫⁻ y, ∫⁻ x, ‖h (liftT (x - y)) * heatKernel t y * ψ x‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal C * ((2 * R + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι *
          ∫⁻ z, ‖h z‖ₑ * ENNReal.ofReal (heatKernel t y) := lintegral_mono hinner
    _ = ENNReal.ofReal C * ((2 * R + 2 : ℕ) : ℝ≥0∞) ^ Fintype.card ι * (∫⁻ z, ‖h z‖ₑ) *
          ∫⁻ y, ENNReal.ofReal (heatKernel t y) := by
        rw [lintegral_const_mul' _ _ (by
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))]
        simp_rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
        rw [lintegral_const_mul' _ _ (hh.2.ne)]
        ring
    _ < ⊤ := by
        refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.pow_lt_top (ENNReal.natCast_lt_top _))) hh.2) ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel ht)
          (Eventually.of_forall fun y => (heatKernel_pos ht y).le)]
        exact ENNReal.ofReal_lt_top

/-- `∫ (e^{tΔ}h)(x) ψ(x) dx = ∫ G_t(y) ∫ h(x) ψ(x + y) dx dy`. -/
theorem integral_heatT_mul {t : ℝ} (ht : 0 < t) {h : UnitAddTorus ι → ℝ} (hh : Integrable h)
    {ψ : (ι → ℝ) → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, heatT t h (liftT x) * ψ x =
      ∫ y, heatKernel t y * ∫ x, h (liftT x) * ψ (x + y) := by
  have hint := integrable_heat_test ht hh hψ hψc
  calc ∫ x, heatT t h (liftT x) * ψ x
      = ∫ x, ∫ y, h (liftT (x - y)) * heatKernel t y * ψ x := by
        congr 1; funext x
        rw [heatT_liftT, ← integral_mul_const]
    _ = ∫ y, ∫ x, h (liftT (x - y)) * heatKernel t y * ψ x := integral_integral_swap hint
    _ = ∫ y, heatKernel t y * ∫ x, h (liftT x) * ψ (x + y) := by
        congr 1; funext y
        rw [← integral_const_mul]
        have := integral_add_right_eq_self
          (fun x => h (liftT (x - y)) * heatKernel t y * ψ x) (μ := volume) y
        simp only [add_sub_cancel_right] at this
        rw [← this]
        congr 1; funext x; ring

variable [DecidableEq ι]

/-- **Gradients commute with the heat flow.** -/
theorem isWeakGrad_heatT {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ}
    {g : UnitAddTorus ι → ι → ℝ} (hfg : IsWeakGrad f g) (hf : Integrable f)
    (hg : ∀ k, Integrable (fun y => g y k)) :
    IsWeakGrad (heatT t f) (fun z k => heatT t (fun y => g y k) z) := by
  refine ⟨?_, fun k => ?_, fun φ hφ hφc k => ?_⟩
  · exact (isSmoothT_heatT ht hf).continuous.locallyIntegrable
  · exact (isSmoothT_heatT ht (hg k)).continuous.locallyIntegrable
  · have hφ' : Continuous fun x => fderiv ℝ φ x (Pi.single k 1) :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hφ'c : HasCompactSupport fun x => fderiv ℝ φ x (Pi.single k 1) :=
      hφc.fderiv_apply (𝕜 := ℝ) _
    rw [integral_heatT_mul ht hf hφ' hφ'c, integral_heatT_mul ht (hg k) hφ.continuous hφc,
      ← integral_neg]
    congr 1; funext y
    rw [← mul_neg]
    congr 1
    -- the weak gradient identity, tested against `φ(· + y)`
    have hφy : ContDiff ℝ ∞ (fun x => φ (x + y)) := hφ.comp (contDiff_id.add contDiff_const)
    have hφyc : HasCompactSupport (fun x => φ (x + y)) := by
      have := hφc.comp_homeomorph (Homeomorph.addRight y)
      exact this
    have h := hfg.ibp (fun x => φ (x + y)) hφy hφyc k
    have hd : ∀ x, fderiv ℝ (fun x => φ (x + y)) x (Pi.single k 1) =
        fderiv ℝ φ (x + y) (Pi.single k 1) := fun x => by
      rw [fderiv_comp_add_right]
    simp_rw [hd] at h
    exact h

end SharpLSI
