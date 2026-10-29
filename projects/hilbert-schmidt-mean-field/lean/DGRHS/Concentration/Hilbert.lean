import DGRHS.Concentration.HilbertProjection

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped InnerProductSpace Topology
namespace DGRHS.Concentration

lemma bounded_empirical_norm_product_aes {E Ω : Type*} [NormedAddCommGroup E]
    [MeasurableSpace Ω] {n : ℕ} (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → E) (B : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B) :
    AEStronglyMeasurable (empiricalNormOnProduct Z) (Measure.pi μ) := by
  have hi : ∀ i, Integrable (fun ω : Fin n → Ω ↦ Z i (ω i)) (Measure.pi μ) := fun i ↦
    bounded_hilbert_integrable
      ((hZ i).comp_quasiMeasurePreserving (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving)
      ((measurePreserving_pi_coordinate μ i).quasiMeasurePreserving.ae (hB i))
  change AEStronglyMeasurable (fun ω ↦ ‖∑ i, Z i (ω i)‖) (Measure.pi μ)
  simpa only [Finset.sum_apply] using
    (integrable_finsetSum Finset.univ (fun i _ ↦ hi i)).aestronglyMeasurable.norm

/-- Full arbitrary complete real Hilbert bound from actual nested finite-rank projections.
No ambient separability or finite-dimensional premise is imposed. All moment integrability
and all almost-everywhere convergence facts are proved before dominated convergence. -/
theorem hilbert_integer_moment {H Ω : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [MeasurableSpace Ω] {n : ℕ}
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B C D : ℝ) (hBpos : 0 ≤ B) (hCpos : 0 ≤ C) (hDpos : 0 ≤ D)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hMean : ∀ i, ∫ x, Z i x ∂μ i = 0)
    (hTrace : (∑ i, ∫ x, ‖Z i x‖^2 ∂μ i) ≤ C^2)
    (hWeak : ∀ u : H, ‖u‖ ≤ 1 → (∑ i, ∫ x, (inner ℝ u (Z i x))^2 ∂μ i) ≤ D^2)
    (m : ℕ) (hm : 1 ≤ m) :
    (∫ ω, (empiricalNormOnProduct Z ω)^m ∂Measure.pi μ)^(1/(m : ℝ)) ≤
      12*(C+Real.sqrt (m : ℝ)*D+(m : ℝ)*B) := by
  let U := fun r ↦ hilbertApproximationSubspace μ Z hZ r
  let Y := fun (r : ℕ) (i : Fin n) (x : Ω) ↦ (U r).orthogonalProjectionOnto (Z i x)
  let W := fun r ↦ empiricalNormOnProduct (Y r)
  have hY : ∀ r i, AEStronglyMeasurable (Y r i) (μ i) := fun r i ↦
    (U r).orthogonalProjectionOnto.continuous.comp_aestronglyMeasurable (hZ i)
  have hYb : ∀ r i, ∀ᵐ x ∂μ i, ‖Y r i x‖ ≤ B := fun r i ↦ (hB i).mono fun x hx ↦
    ((U r).norm_orthogonalProjectionOnto_apply_le _).trans hx
  have hW : ∀ r, AEStronglyMeasurable (W r) (Measure.pi μ) := fun r ↦
    bounded_empirical_norm_product_aes μ (Y r) B (hY r) (hYb r)
  have hWb : ∀ r, ∀ᵐ ω ∂Measure.pi μ, |W r ω| ≤ (n : ℝ)*B := fun r ↦
    empirical_norm_product_bounded μ (Y r) B (hYb r)
  have hPowb : ∀ r, ∀ᵐ ω ∂Measure.pi μ, |(W r ω)^m| ≤ ((n : ℝ)*B)^m := by
    intro r
    filter_upwards [hWb r] with ω hω
    rw [abs_pow]
    gcongr
  have hPowI : ∀ r, Integrable (fun ω ↦ (W r ω)^m) (Measure.pi μ) := fun r ↦
    integrable_of_ae_abs_le ((hW r).fun_pow m) (hPowb r)
  have hRaw := bounded_empirical_norm_product_aes μ Z B hZ hB
  have hRawb := empirical_norm_product_bounded μ Z B hB
  have hRawPowb : ∀ᵐ ω ∂Measure.pi μ, |(empiricalNormOnProduct Z ω)^m| ≤ ((n : ℝ)*B)^m := by
    filter_upwards [hRawb] with ω hω
    rw [abs_pow]
    gcongr
  have hRawPowI := integrable_of_ae_abs_le (hRaw.fun_pow m) hRawPowb
  have hEq : ∀ r ω, W r ω = ‖∑ i, (U r).starProjection (Z i (ω i))‖ := by
    intro r ω
    change ‖((∑ i, (U r).orthogonalProjectionOnto (Z i (ω i)) : U r) : H)‖ = _
    simp
  have hLim : ∀ᵐ ω ∂Measure.pi μ, Tendsto (fun r ↦ (W r ω)^m) atTop
      (𝓝 ((empiricalNormOnProduct Z ω)^m)) := by
    have hj : ∀ᵐ ω ∂Measure.pi μ, ∀ i,
        Tendsto (fun r ↦ (U r).starProjection (Z i (ω i))) atTop (𝓝 (Z i (ω i))) :=
      ae_all_iff.mpr fun i ↦ (measurePreserving_pi_coordinate μ i).quasiMeasurePreserving.ae
        (hilbert_projection_tendsto_ae μ Z hZ i)
    filter_upwards [hj] with ω hω
    have hs := tendsto_finsetSum Finset.univ (fun i _ ↦ hω i)
    have hn : Tendsto (fun r ↦ W r ω) atTop (𝓝 (empiricalNormOnProduct Z ω)) := by
      simpa only [hEq,empiricalNormOnProduct,empiricalNorm] using hs.norm
    exact hn.pow m
  have hIntegral := tendsto_integral_of_dominated_convergence
    (fun _ : Fin n → Ω ↦ ((n : ℝ)*B)^m)
    (fun r ↦ (hW r).fun_pow m) (integrable_const _)
    (fun r ↦ (hPowb r).mono fun ω hω ↦ by simpa only [Real.norm_eq_abs] using hω) hLim
  let K := 12*(C+Real.sqrt (m : ℝ)*D+(m : ℝ)*B)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hb : ∀ r, (∫ ω, (W r ω)^m ∂Measure.pi μ) ≤ K^m := by
    intro r
    have ht := projected_hilbert_integer_moment (U r) μ Z B C D hBpos hCpos hDpos hZ hB hMean hTrace hWeak m hm
    have hq : 0 ≤ ∫ ω, (W r ω)^m ∂Measure.pi μ := integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) m
    have hh := (Real.rpow_inv_le_iff_of_pos hq hK hmpos).mp (by simpa only [one_div] using ht)
    simpa only [Real.rpow_natCast] using hh
  have hq := le_of_tendsto hIntegral (Filter.Eventually.of_forall hb)
  have hnonneg : 0 ≤ ∫ ω, (empiricalNormOnProduct Z ω)^m ∂Measure.pi μ :=
    integral_nonneg fun ω ↦ pow_nonneg (norm_nonneg _) m
  have hh := (Real.rpow_inv_le_iff_of_pos hnonneg hK hmpos).mpr
    (by simpa only [Real.rpow_natCast] using hq)
  simpa only [one_div] using hh

#print axioms DGRHS.Concentration.hilbert_integer_moment
#check @DGRHS.Concentration.hilbert_integer_moment
end DGRHS.Concentration
