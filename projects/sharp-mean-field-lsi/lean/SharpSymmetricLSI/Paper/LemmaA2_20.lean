import SharpSymmetricLSI.Paper.LemmaA2_19
import SharpSymmetricLSI.Paper.EnergyParseval3

/-!
# R25 Lemma A.2, part 20: the weighted Hilbert–Schmidt identity for Lipschitz kernels

For a continuous kernel `F` whose `x`-slices are uniformly Lipschitz,
`∑_{i,j} λ_i F_{ij}² = ∬ |∇_x F|² dμ dμ` with `F_{ij} = ∫∫ F e_i e_j` (`weighted_hs_gen`):
the energy Parseval identity in `x` for each slice, monotone convergence in `y`, and Parseval in `y`
for the coefficient functions.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

section whs

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (hb : IsRefEigenbasis (densMeasure ρ) e lam)
include hρ hρc hb

theorem continuous_slice_coeff {F : Torus d → Torus d → ℝ} (hFc : Continuous (Function.uncurry F))
    (i : ℕ) : Continuous fun y => ∫ x, F x y * e i x ∂densMeasure ρ := by
  haveI := hρ.isProb
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hFc.continuousOn
  have hei : Integrable (e i) (densMeasure ρ) := ((hb.memH1 i).2.1).integrable one_le_two
  refine continuous_of_dominated (bound := fun x => B * |e i x|) (fun y => ?_) (fun y => ?_)
    (hei.abs.const_mul B) (Eventually.of_forall fun x => ?_)
  · exact ((hFc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable).mul
      hei.aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hB (x, y) (mem_univ _))
      (abs_nonneg _)
  · exact (hFc.comp (continuous_const.prodMk continuous_id)).mul continuous_const

/-- **Weighted Hilbert–Schmidt identity.** -/
theorem weighted_hs_gen {F : Torus d → Torus d → ℝ} (hFc : Continuous (Function.uncurry F))
    {L : ℝ≥0} (hFL : ∀ y, LipschitzWith L ((fun x => F x y) ∘ liftT)) :
    HasSum (fun ij : ℕ × ℕ =>
        lam ij.1 * (∫ y, (∫ x, F x y * e ij.1 x ∂densMeasure ρ) * e ij.2 y ∂densMeasure ρ) ^ 2)
      (∫ y, (∫ x, sqNorm (lipGrad (fun x => F x y) x) ∂densMeasure ρ) ∂densMeasure ρ) := by
  haveI := hρ.isProb
  set P := densMeasure ρ
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => refLam_nonneg hρ hb i
  set cf : ℕ → Torus d → ℝ := fun i y => ∫ x, F x y * e i x ∂P
  have hcfc : ∀ i, Continuous (cf i) := fun i => continuous_slice_coeff hρ hρc hb hFc i
  set G : Torus d → ℝ := fun y => ∫ x, sqNorm (lipGrad (fun x => F x y) x) ∂P
  have hsl : ∀ y, Continuous fun x => F x y := fun y =>
    hFc.comp (continuous_id.prodMk continuous_const)
  -- energy Parseval for each slice
  have hE : ∀ y, HasSum (fun i => lam i * cf i y ^ 2) (G y) := by
    intro y
    have hH := memH1_of_lipschitz hρ hρc (hsl y) (hFL y)
    have h := energy_parseval hρ.ac hρ.haar_le_smul hb hH
    have hw := isWeakGrad_lipGrad (hsl y) (hFL y)
    have hae : weakGrad (fun x => F x y) =ᵐ[volume] lipGrad (fun x => F x y) :=
      weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw⟩) hw
    have hP : weakGrad (fun x => F x y) =ᵐ[P] lipGrad (fun x => F x y) := hρ.ac.ae_le hae
    convert h using 1
    unfold dirPair
    refine integral_congr_ae ?_
    filter_upwards [hP] with x hx
    simp only [hx, sqNorm, sq]
  have hG0 : ∀ y, 0 ≤ G y := fun y => integral_nonneg fun x =>
    Finset.sum_nonneg fun k _ => sq_nonneg _
  -- measurability and integrability of `G`
  have hSm : ∀ N, Continuous fun y => ∑ i ∈ Finset.range N, lam i * cf i y ^ 2 := fun N =>
    continuous_finset_sum _ fun i _ => continuous_const.mul ((hcfc i).pow 2)
  have hGm : Measurable G := by
    refine measurable_of_tendsto_metrizable (f := fun N y => ∑ i ∈ Finset.range N, lam i * cf i y ^ 2)
      (fun N => (hSm N).measurable) ?_
    rw [tendsto_pi_nhds]
    exact fun y => (hE y).tendsto_sum_nat
  have hGb : ∀ y, G y ≤ d * L ^ 2 := by
    intro y
    calc G y ≤ ∫ _x, (d * L ^ 2 : ℝ) ∂P := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_) (integrable_const _)
            (Eventually.of_forall fun x => ?_)
          · exact Finset.sum_nonneg fun k _ => sq_nonneg _
          · calc sqNorm (lipGrad (fun x => F x y) x) ≤ ∑ _k : Fin d, (L : ℝ) ^ 2 :=
                  Finset.sum_le_sum fun k _ => by
                    rw [← sq_abs]
                    exact pow_le_pow_left₀ (abs_nonneg _) (abs_lipGrad_le (hFL y) x k) 2
              _ = d * L ^ 2 := by simp
      _ = d * L ^ 2 := by simp
  have hGi : Integrable G P := (integrable_const ((d : ℝ) * L ^ 2)).mono' hGm.aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (hG0 y)]; exact hGb y)
  -- monotone convergence in `y`
  have hcfb : ∀ i, ∃ B, ∀ y, |cf i y| ≤ B := fun i => by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (hcfc i).continuousOn
    exact ⟨B, fun y => by simpa [Real.norm_eq_abs] using hB y (mem_univ _)⟩
  have hcfi : ∀ i, Integrable (fun y => cf i y ^ 2) P := fun i =>
    let ⟨B, hB⟩ := hcfb i
    (integrable_const (B ^ 2)).mono' ((hcfc i).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB y) 2)
  have hsumi : HasSum (fun i => lam i * ∫ y, cf i y ^ 2 ∂P) (∫ y, G y ∂P) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => mul_nonneg (hlam0 i)
      (integral_nonneg fun y => sq_nonneg _))]
    have hlim := integral_tendsto_of_tendsto_of_monotone
      (f := fun N y => ∑ i ∈ Finset.range N, lam i * cf i y ^ 2) (F := G)
      (fun N => integrable_finset_sum _ fun i _ => (hcfi i).const_mul _) hGi
      (Eventually.of_forall fun y => fun N M hNM =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
          fun i _ _ => mul_nonneg (hlam0 i) (sq_nonneg _))
      (Eventually.of_forall fun y => (hE y).tendsto_sum_nat)
    refine hlim.congr fun N => ?_
    rw [integral_finset_sum _ fun i _ => (hcfi i).const_mul _]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  -- Parseval in `y`
  have hPy : ∀ i, HasSum (fun j => (∫ y, cf i y * e j y ∂P) ^ 2) (∫ y, cf i y ^ 2 ∂P) := fun i =>
    let ⟨B, hB⟩ := hcfb i
    hasSum_sq_coeff hb (MemLp.of_bound (hcfc i).aestronglyMeasurable B
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y))
  -- assemble over `ℕ × ℕ`
  set a : ℕ × ℕ → ℝ := fun ij => lam ij.1 * (∫ y, cf ij.1 y * e ij.2 y ∂P) ^ 2
  have ha0 : ∀ ij, 0 ≤ a ij := fun ij => mul_nonneg (hlam0 _) (sq_nonneg _)
  have hfib : ∀ i, HasSum (fun j => a (i, j)) (lam i * ∫ y, cf i y ^ 2 ∂P) := fun i =>
    (hPy i).mul_left (lam i)
  have hsum : Summable a := by
    refine (summable_prod_of_nonneg ha0).mpr ⟨fun i => (hfib i).summable, ?_⟩
    exact hsumi.summable.congr fun i => ((hfib i).tsum_eq).symm
  have := hsum.hasSum
  rwa [hsum.tsum_prod' (fun i => (hfib i).summable), tsum_congr fun i => (hfib i).tsum_eq,
    hsumi.tsum_eq] at this

/-- **Parseval on `μ ⊗ μ`** for continuous kernels. -/
theorem parseval_gen {F : Torus d → Torus d → ℝ} (hFc : Continuous (Function.uncurry F)) :
    HasSum (fun ij : ℕ × ℕ =>
        (∫ y, (∫ x, F x y * e ij.1 x ∂densMeasure ρ) * e ij.2 y ∂densMeasure ρ) ^ 2)
      (∫ y, (∫ x, F x y ^ 2 ∂densMeasure ρ) ∂densMeasure ρ) := by
  haveI := hρ.isProb
  set P := densMeasure ρ
  set cf : ℕ → Torus d → ℝ := fun i y => ∫ x, F x y * e i x ∂P
  have hcfc : ∀ i, Continuous (cf i) := fun i => continuous_slice_coeff hρ hρc hb hFc i
  set G : Torus d → ℝ := fun y => ∫ x, F x y ^ 2 ∂P
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hFc.continuousOn
  have hB' : ∀ x y, |F x y| ≤ B := fun x y => by
    simpa [Real.norm_eq_abs] using hB (x, y) (mem_univ _)
  have hsl : ∀ y, Continuous fun x => F x y := fun y =>
    hFc.comp (continuous_id.prodMk continuous_const)
  have hE : ∀ y, HasSum (fun i => cf i y ^ 2) (G y) := fun y =>
    hasSum_sq_coeff hb (MemLp.of_bound (hsl y).aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB' x y))
  have hGc : Continuous G := by
    refine continuous_of_dominated (bound := fun _ => B ^ 2) (fun y => ?_) (fun y => ?_)
      (integrable_const _) (Eventually.of_forall fun x => ?_)
    · exact ((hsl y).pow 2).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hB' x y) 2
    · exact (hFc.comp (continuous_const.prodMk continuous_id)).pow 2
  have hGi : Integrable G P := (integrable_const (B ^ 2)).mono' hGc.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      calc G y ≤ ∫ _x, B ^ 2 ∂P := integral_mono_of_nonneg
            (Eventually.of_forall fun _ => sq_nonneg _) (integrable_const _)
            (Eventually.of_forall fun x => by
              show F x y ^ 2 ≤ B ^ 2
              rw [← sq_abs (F x y)]; exact pow_le_pow_left₀ (abs_nonneg _) (hB' x y) 2)
        _ = B ^ 2 := by simp)
  have hcfb : ∀ i, ∃ B, ∀ y, |cf i y| ≤ B := fun i => by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (hcfc i).continuousOn
    exact ⟨B, fun y => by simpa [Real.norm_eq_abs] using hB y (mem_univ _)⟩
  have hcfi : ∀ i, Integrable (fun y => cf i y ^ 2) P := fun i =>
    let ⟨B, hB⟩ := hcfb i
    (integrable_const (B ^ 2)).mono' ((hcfc i).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB y) 2)
  have hsumi : HasSum (fun i => ∫ y, cf i y ^ 2 ∂P) (∫ y, G y ∂P) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => integral_nonneg fun y => sq_nonneg _)]
    have hlim := integral_tendsto_of_tendsto_of_monotone
      (f := fun N y => ∑ i ∈ Finset.range N, cf i y ^ 2) (F := G)
      (fun N => integrable_finset_sum _ fun i _ => hcfi i) hGi
      (Eventually.of_forall fun y => fun N M hNM =>
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
          fun i _ _ => sq_nonneg _)
      (Eventually.of_forall fun y => (hE y).tendsto_sum_nat)
    refine hlim.congr fun N => ?_
    rw [integral_finset_sum _ fun i _ => hcfi i]
  have hPy : ∀ i, HasSum (fun j => (∫ y, cf i y * e j y ∂P) ^ 2) (∫ y, cf i y ^ 2 ∂P) := fun i =>
    let ⟨B, hB⟩ := hcfb i
    hasSum_sq_coeff hb (MemLp.of_bound (hcfc i).aestronglyMeasurable B
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y))
  set a : ℕ × ℕ → ℝ := fun ij => (∫ y, cf ij.1 y * e ij.2 y ∂P) ^ 2
  have ha0 : ∀ ij, 0 ≤ a ij := fun ij => sq_nonneg _
  have hsum : Summable a := by
    refine (summable_prod_of_nonneg ha0).mpr ⟨fun i => (hPy i).summable, ?_⟩
    exact hsumi.summable.congr fun i => ((hPy i).tsum_eq).symm
  have := hsum.hasSum
  rwa [hsum.tsum_prod' (fun i => (hPy i).summable), tsum_congr fun i => (hPy i).tsum_eq,
    hsumi.tsum_eq] at this

end whs

end SharpLSI
