import SharpSymmetricLSI.Paper.WeightedHS2

/-!
# (6.3): assembly (Phase 3, lane D; R24)
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section whs
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

/-- **(6.3).** -/
theorem weighted_hs_aux :
    Integrable (fun p : Torus d × Torus d => sqNorm (bForce W μ p.1 p.2))
      ((μ : Measure (Torus d)).prod (μ : Measure (Torus d))) ∧
    HasSum (fun ij : ℕ × ℕ => lam (ij.1 + 1) * Tmat W μ e ij.1 ij.2 ^ 2)
      (∫ x, ∫ y, sqNorm (bForce W μ x y) ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d))) := by
  set μm := (μ : Measure (Torus d))
  have hac := minimizer_ac hyp hμ
  obtain ⟨hbm, M, hM0, hM, -, -⟩ := bfixF_props hyp hac
  set k : ℕ → Torus d → ℝ := fun i y => ∫ x, centeredKernel W μ x y * e i x ∂μm with hk
  set E : Torus d → ℝ := fun y => ∫ x, ∑ j, bfixF W μ x y j * bfixF W μ x y j ∂μm with hE
  -- the bounded field squared
  set G : Torus d × Torus d → ℝ := fun p => ∑ j, bfixF W μ p.1 p.2 j * bfixF W μ p.1 p.2 j
  have hGm : Measurable G := Finset.measurable_sum _ fun j _ => (hbm j).mul (hbm j)
  have hGb : ∀ p, |G p| ≤ d * M ^ 2 := fun p => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |bfixF W μ p.1 p.2 j * bfixF W μ p.1 p.2 j| ≤ ∑ _j : Fin d, M ^ 2 :=
          Finset.sum_le_sum fun j _ => by
            rw [abs_mul, sq]; exact mul_le_mul (hM _ _ j) (hM _ _ j) (abs_nonneg _) hM0
      _ = d * M ^ 2 := by simp
  have hG0 : ∀ p, 0 ≤ G p := fun p => Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hGi : Integrable G (μm.prod μm) := integrable_of_bdd hGm hGb
  -- `bForce = bfix` a.e. on `μ ⊗ μ`
  have hacp : μm.prod μm ≪ (haar d).prod (haar d) := hac.prod hac
  have hbae := hacp.ae_le (bForce_ae_prod hyp hac)
  have hsq : (fun p : Torus d × Torus d => sqNorm (bForce W μ p.1 p.2)) =ᵐ[μm.prod μm] G := by
    filter_upwards [hbae] with p hp
    simp only [sqNorm, G, bfixF, hp, sq]
  refine ⟨hGi.congr hsq.symm, ?_⟩
  -- the right-hand side is `∫ E`
  have hRHS : ∫ x, ∫ y, sqNorm (bForce W μ x y) ∂μm ∂μm = ∫ y, E y ∂μm := by
    rw [← integral_prod (fun p : Torus d × Torus d => sqNorm (bForce W μ p.1 p.2))
      (hGi.congr hsq.symm), integral_congr_ae hsq, integral_prod_symm G hGi]
  rw [hRHS]
  -- Parseval in `y` for the coefficients
  have hkL := coeff_props hyp hμ he
  have hk0 : ∀ y, k 0 y = 0 := coeff_zero_left hyp hμ he
  have hrow : ∀ i, HasSum (fun j => Tmat W μ e i j ^ 2) (∫ y, k (i + 1) y ^ 2 ∂μm) := by
    intro i
    have h := hasSum_sq_coeff he (hkL (i + 1))
    rw [← hasSum_nat_add_iff' 1] at h
    simp only [Finset.range_one, Finset.sum_singleton] at h
    rw [coeff_zero_right hyp hμ he, sq, mul_zero, sub_zero] at h
    convert h using 2 with j
    unfold Tmat
    rw [coeff_fubini hyp hμ he]
  -- the slices, integrated
  have hslice : ∀ y, HasSum (fun i => lam i * k i y ^ 2) (E y) := fun y => slice_energy hyp hμ he y
  have hlam0 : ∀ i, 0 ≤ lam i := lam_nonneg hac he
  have hkm : ∀ i, AEStronglyMeasurable (k i) μm := fun i => (hkL i).aestronglyMeasurable
  have hcol : HasSum (fun i => lam i * ∫ y, k i y ^ 2 ∂μm) (∫ y, E y ∂μm) := by
    have hEm : Measurable E := (hGm.comp measurable_swap).stronglyMeasurable.integral_prod_right'
      |>.measurable
    have hEb : ∀ y, |E y| ≤ d * M ^ 2 := fun y => abs_integral_le_of_bdd fun x => hGb (x, y)
    have hE0 : ∀ y, 0 ≤ E y := fun y => integral_nonneg fun x => hG0 (x, y)
    have hEi : Integrable E μm := integrable_of_bdd hEm hEb
    have hai : ∀ i, Integrable (fun y => lam i * k i y ^ 2) μm := fun i =>
      ((hkL i).integrable_sq).const_mul _
    have ha0 : ∀ i y, 0 ≤ lam i * k i y ^ 2 := fun i y => mul_nonneg (hlam0 i) (sq_nonneg _)
    -- in `ℝ≥0∞`
    have hlin : ∫⁻ y, ENNReal.ofReal (E y) ∂μm =
        ∑' i, ENNReal.ofReal (lam i * ∫ y, k i y ^ 2 ∂μm) := by
      have h1 : ∀ y, ENNReal.ofReal (E y) = ∑' i, ENNReal.ofReal (lam i * k i y ^ 2) := fun y => by
        rw [← (hslice y).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (ha0 · y) (hslice y).summable]
      simp_rw [h1]
      rw [lintegral_tsum (f := fun i y => ENNReal.ofReal (lam i * k i y ^ 2)) fun i =>
        (ENNReal.measurable_ofReal.comp_aemeasurable (hai i).aestronglyMeasurable.aemeasurable)]
      refine tsum_congr fun i => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hai i) (Eventually.of_forall (ha0 i)),
        integral_const_mul]
    have hne : ∑' i, ENNReal.ofReal (lam i * ∫ y, k i y ^ 2 ∂μm) ≠ ⊤ := by
      rw [← hlin, ← ofReal_integral_eq_lintegral_ofReal hEi (Eventually.of_forall hE0)]
      exact ENNReal.ofReal_ne_top
    have hnn : ∀ i, 0 ≤ lam i * ∫ y, k i y ^ 2 ∂μm := fun i =>
      mul_nonneg (hlam0 i) (integral_nonneg fun y => sq_nonneg _)
    have hsum : Summable fun i => lam i * ∫ y, k i y ^ 2 ∂μm := by
      have := ENNReal.summable_toReal hne
      simpa [ENNReal.toReal_ofReal (hnn _)] using this
    refine hsum.hasSum_iff.mpr ?_
    have h2 := ENNReal.ofReal_tsum_of_nonneg hnn hsum
    rw [← hlin, ← ofReal_integral_eq_lintegral_ofReal hEi (Eventually.of_forall hE0)] at h2
    exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hnn) (integral_nonneg hE0)).mp h2
  -- shift the column sum (the `i = 0` term vanishes) and assemble the double sum
  have hcol' : HasSum (fun i => lam (i + 1) * ∫ y, k (i + 1) y ^ 2 ∂μm) (∫ y, E y ∂μm) := by
    have h := (hasSum_nat_add_iff' 1).mpr hcol
    simp only [Finset.range_one, Finset.sum_singleton, hk0, sq, mul_zero, integral_zero,
      sub_zero] at h
    simpa [sq] using h
  have hterm : ∀ i, HasSum (fun j => lam (i + 1) * Tmat W μ e i j ^ 2)
      (lam (i + 1) * ∫ y, k (i + 1) y ^ 2 ∂μm) := fun i => (hrow i).mul_left _
  have hnn2 : 0 ≤ fun ij : ℕ × ℕ => lam (ij.1 + 1) * Tmat W μ e ij.1 ij.2 ^ 2 := fun ij =>
    mul_nonneg (hlam0 _) (sq_nonneg _)
  have hsumm : Summable fun ij : ℕ × ℕ => lam (ij.1 + 1) * Tmat W μ e ij.1 ij.2 ^ 2 := by
    refine (summable_prod_of_nonneg hnn2).mpr ⟨fun i => (hterm i).summable, ?_⟩
    simp_rw [fun i => (hterm i).tsum_eq]
    exact hcol'.summable
  refine hsumm.hasSum_iff.mpr ?_
  rw [hsumm.tsum_prod]
  simp_rw [fun i => (hterm i).tsum_eq]
  exact hcol'.tsum_eq

end whs

end SharpLSI
