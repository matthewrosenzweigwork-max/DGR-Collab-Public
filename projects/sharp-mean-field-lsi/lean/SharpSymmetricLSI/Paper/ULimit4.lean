import SharpSymmetricLSI.Paper.ULimit3

/-!
# `T` is Hilbert–Schmidt: `∑_{i,j ≥ 1} T_{ij}² = ‖K‖²_{L²(μ⊗μ)}` (Phase 3, lane D; R26)
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section hs
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

theorem hasSum_Tmat_sq :
    HasSum (fun ij : ℕ × ℕ => Tmat W μ e ij.1 ij.2 ^ 2)
      (∫ x, ∫ y, centeredKernel W μ x y ^ 2 ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d))) := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μm
  have hKm := measurable_centeredKernel hyp μm
  set k : ℕ → Torus d → ℝ := fun i y => ∫ x, centeredKernel W μ x y * e i x ∂μm with hk
  set E : Torus d → ℝ := fun y => ∫ x, centeredKernel W μ x y ^ 2 ∂μm with hE
  have hK2m : Measurable fun p : Torus d × Torus d => centeredKernel W μ p.1 p.2 ^ 2 :=
    hKm.pow_const 2
  have hK2b : ∀ p : Torus d × Torus d, |centeredKernel W μ p.1 p.2 ^ 2| ≤ B ^ 2 := fun p => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _ _) 2
  have hK2i : Integrable (fun p : Torus d × Torus d => centeredKernel W μ p.1 p.2 ^ 2)
      (μm.prod μm) := integrable_of_bdd hK2m hK2b
  have hRHS : ∫ x, ∫ y, centeredKernel W μ x y ^ 2 ∂μm ∂μm = ∫ y, E y ∂μm :=
    integral_integral_swap hK2i
  rw [hRHS]
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
  -- Parseval in `x` for each slice
  have hslice : ∀ y, HasSum (fun i => k i y ^ 2) (E y) := fun y => by
    have hm : Measurable fun x => centeredKernel W μ x y := hKm.comp (measurable_prodMk_right)
    have hL : MemLp (fun x => centeredKernel W μ x y) 2 μm :=
      MemLp.of_bound hm.aestronglyMeasurable B (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hB x y)
    exact hasSum_sq_coeff he hL
  have hcol : HasSum (fun i => ∫ y, k i y ^ 2 ∂μm) (∫ y, E y ∂μm) := by
    have hEm : Measurable E := (hK2m.comp measurable_swap).stronglyMeasurable.integral_prod_right'
      |>.measurable
    have hEb : ∀ y, |E y| ≤ B ^ 2 := fun y => abs_integral_le_of_bdd fun x => hK2b (x, y)
    have hE0 : ∀ y, 0 ≤ E y := fun y => integral_nonneg fun x => sq_nonneg _
    have hEi : Integrable E μm := integrable_of_bdd hEm hEb
    have hai : ∀ i, Integrable (fun y => k i y ^ 2) μm := fun i => (hkL i).integrable_sq
    have ha0 : ∀ i y, 0 ≤ k i y ^ 2 := fun i y => sq_nonneg _
    have hlin : ∫⁻ y, ENNReal.ofReal (E y) ∂μm = ∑' i, ENNReal.ofReal (∫ y, k i y ^ 2 ∂μm) := by
      have h1 : ∀ y, ENNReal.ofReal (E y) = ∑' i, ENNReal.ofReal (k i y ^ 2) := fun y => by
        rw [← (hslice y).tsum_eq, ENNReal.ofReal_tsum_of_nonneg (ha0 · y) (hslice y).summable]
      simp_rw [h1]
      rw [lintegral_tsum (f := fun i y => ENNReal.ofReal (k i y ^ 2)) fun i =>
        (ENNReal.measurable_ofReal.comp_aemeasurable (hai i).aestronglyMeasurable.aemeasurable)]
      refine tsum_congr fun i => ?_
      rw [← ofReal_integral_eq_lintegral_ofReal (hai i) (Eventually.of_forall (ha0 i))]
    have hne : ∑' i, ENNReal.ofReal (∫ y, k i y ^ 2 ∂μm) ≠ ⊤ := by
      rw [← hlin, ← ofReal_integral_eq_lintegral_ofReal hEi (Eventually.of_forall hE0)]
      exact ENNReal.ofReal_ne_top
    have hnn : ∀ i, 0 ≤ ∫ y, k i y ^ 2 ∂μm := fun i => integral_nonneg fun y => sq_nonneg _
    have hsum : Summable fun i => ∫ y, k i y ^ 2 ∂μm := by
      have := ENNReal.summable_toReal hne
      simpa [ENNReal.toReal_ofReal (hnn _)] using this
    refine hsum.hasSum_iff.mpr ?_
    have h2 := ENNReal.ofReal_tsum_of_nonneg hnn hsum
    rw [← hlin, ← ofReal_integral_eq_lintegral_ofReal hEi (Eventually.of_forall hE0)] at h2
    exact (ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg hnn) (integral_nonneg hE0)).mp h2
  have hcol' : HasSum (fun i => ∫ y, k (i + 1) y ^ 2 ∂μm) (∫ y, E y ∂μm) := by
    have h := (hasSum_nat_add_iff' 1).mpr hcol
    simp only [Finset.range_one, Finset.sum_singleton, hk0, sq, mul_zero, integral_zero,
      sub_zero] at h
    simpa [sq] using h
  have hnn2 : 0 ≤ fun ij : ℕ × ℕ => Tmat W μ e ij.1 ij.2 ^ 2 := fun ij => sq_nonneg _
  have hsumm : Summable fun ij : ℕ × ℕ => Tmat W μ e ij.1 ij.2 ^ 2 := by
    refine (summable_prod_of_nonneg hnn2).mpr ⟨fun i => (hrow i).summable, ?_⟩
    simp_rw [fun i => (hrow i).tsum_eq]
    exact hcol'.summable
  refine hsumm.hasSum_iff.mpr ?_
  rw [hsumm.tsum_prod]
  simp_rw [fun i => (hrow i).tsum_eq]
  exact hcol'.tsum_eq

theorem Tmat_symm (i j : ℕ) : Tmat W μ e i j = Tmat W μ e j i := by
  set μm := (μ : Measure (Torus d))
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp μm
  have hKm := measurable_centeredKernel hyp μm
  have hint : Integrable (fun p : Torus d × Torus d =>
      centeredKernel W μ p.1 p.2 * e (i + 1) p.1 * e (j + 1) p.2) (μm.prod μm) := by
    have h1 : MemLp (fun p : Torus d × Torus d => e (i + 1) p.1) 2 (μm.prod μm) :=
      (he.memLp (i + 1)).comp_measurePreserving measurePreserving_fst
    have h2 : MemLp (fun p : Torus d × Torus d => e (j + 1) p.2) 2 (μm.prod μm) :=
      (he.memLp (j + 1)).comp_measurePreserving measurePreserving_snd
    have h3 := (h1.integrable_mul h2).bdd_mul (c := B) hKm.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hB _ _)
    refine h3.congr (Eventually.of_forall fun p => ?_)
    obtain ⟨x, y⟩ := p; simp only [Pi.mul_apply, Function.uncurry_apply_pair]; ring
  unfold Tmat
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun y => integral_congr_ae
    (Eventually.of_forall fun x => ?_))
  simp only
  rw [centeredKernel_symm hyp hμ he]; ring

theorem exists_secondChaos_Tmat : ∃ Q, IsSecondChaos (Tmat W μ e) Q :=
  exists_secondChaos (Tmat_symm hyp hμ he) (hasSum_Tmat_sq hyp hμ he).summable

end hs

end SharpLSI
