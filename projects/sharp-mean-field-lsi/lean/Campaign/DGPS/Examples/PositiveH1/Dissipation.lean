import DGPS.Examples.PositiveH1.CrossTerm
import DGPS.Model.ScalarRate
import DGPS.Model.SpeciesRate
/-!
# H1011: exact scalar and species dissipation expansion

The theorem lives in namespace `DGPS.Examples.PositiveH1.Nonlinear` but in this separate module
because `weak_fourier_cross_term` (H1010) lives in `CrossTerm`, which imports `Nonlinear`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DGPS.Examples.PositiveH1.Nonlinear
open DGPS DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model
  DGPS.Examples.PositiveH1.CrossTerm

theorem h1011_measureFourier (σ : AbsoluteDensity 1) (n : ℕ) :
    measureFourier (densityMeasure σ : Measure (Torus 1)) n = fourierCoeff σ.density (freq n) := by
  unfold measureFourier
  rw [fourierCoeff_eq_integral, densityMeasure_coe]
  have hm : AEMeasurable (fun x => ENNReal.ofReal (σ.sqrt x ^ 2)) (haar 1) :=
    (σ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), AbsoluteDensity.density, Complex.real_smul]
  rw [mul_comm]

theorem h1011_fourierEnergy (σ : AbsoluteDensity 1) :
    fourierEnergy (densityMeasure σ) = P σ := by
  unfold fourierEnergy P
  exact tsum_congr fun n => by rw [h1011_measureFourier]

theorem h1011_freeEnergy_form (σ : ProbabilityMeasure (Torus 1)) :
    potentialEnergy positiveH1 σ + (1/2 : ℝ) * interactionEnergy positiveH1 σ
      - freeEnergyMinimumReal positiveH1 = kappa / 2 * fourierEnergy σ := by
  have hV : potentialEnergy positiveH1 σ = 0 := by
    unfold potentialEnergy
    show ∫ x, (0:ℝ) ∂(σ : Measure (Torus 1)) = 0
    simp
  have hF : freeEnergyMinimumReal positiveH1 = -(kappa * A / 2) := by
    have h := coe_freeEnergyMinimumReal positiveH1
    rw [freeEnergyMinimum_positiveH1] at h
    exact EReal.coe_injective h
  rw [hV, hF, interactionEnergy_positiveH1]; ring


theorem h1011_gap_species (F : SpeciesFamily 1) :
    (speciesGap positiveH1 F : ℝ) =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal
        + kappa / 2 * P (barycenter F) := by
  rw [coe_speciesGap, speciesRawGap, ← h1011_fourierEnergy, ← h1011_freeEnergy_form
    (densityMeasure (barycenter F))]
  simp only [densityMeasure]
  ring

theorem h1011_gap_scalar (ρ : AbsoluteDensity 1) :
    (scalarGap positiveH1 ρ : ℝ) =
      (relativeEntropy (densityMeasure ρ) (haar 1)).toReal + kappa / 2 * P ρ := by
  have h1 := coe_densityFreeEnergy positiveH1 ρ
  rw [freeEnergy_eq_real positiveH1 (densityMeasure ρ)
    (absoluteDensity_entropy_finite ρ).2.2.1] at h1
  have h2 := EReal.coe_injective h1
  rw [coe_scalarGap, h2, ← h1011_fourierEnergy, ← h1011_freeEnergy_form (densityMeasure ρ)]
  ring


theorem h1011_norm_sq (v : Tangent 1) : ‖v‖ ^ 2 = (v 0) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]

theorem h1011_core (ρ τ : AbsoluteDensity 1) (b : AbsoluteDrift positiveH1) :
    ∃ J : ℝ, 0 ≤ J ∧
      J = 4 * ∫ x, (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1
        + 2 * kappa * ∫ x, densityDeriv ρ x * conv dR τ.density x ∂haar 1
        + kappa ^ 2 * ∫ x, ρ.density x * (conv dR τ.density x) ^ 2 ∂haar 1 ∧
      ∫⁻ x, ENNReal.ofReal
        (‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2) ∂haar 1
        = ENNReal.ofReal J := by
  set g0 : Torus 1 → ℝ := fun x => weakGradient ρ.sqrt ρ.sqrt_mem x 0 with hg0
  set c : Torus 1 → ℝ := conv dR τ.density with hcdef
  have hg : MemLp g0 2 (haar 1) :=
    memLp_coord_of_memLp (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad 0
  have hc : Continuous c := continuous_driftField τ
  have hcb : MemLp c ⊤ (haar 1) := memLp_of_cont hc _
  have hw : MemLp (fun x => ρ.sqrt x * c x) 2 (haar 1) := by
    have h : MemLp (ρ.sqrt * c) 2 (haar 1) := ρ.memLp_sqrt.smul hcb
    exact h
  obtain ⟨-, -, -, -, -, -, -, hforce, -⟩ := admissibleRegularity τ
  have hae : b.force τ =ᵐ[haar 1] positiveH1Drift.force τ := absoluteDrift_unique b positiveH1Drift τ
  have hpt : ∀ᵐ x ∂haar 1,
      ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2
        = 4 * g0 x ^ 2 + 4 * kappa * (g0 x * (ρ.sqrt x * c x))
          + kappa ^ 2 * (ρ.sqrt x * c x) ^ 2 := by
    filter_upwards [hae] with x hx
    rw [hx, h1011_norm_sq, hforce x]
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
      smul_eq_mul, hg0, hcdef, conv]
    ring
  have i1 : Integrable (fun x => g0 x ^ 2) (haar 1) := hg.integrable_sq
  have i2 : Integrable (fun x => g0 x * (ρ.sqrt x * c x)) (haar 1) := hg.integrable_mul hw
  have i3 : Integrable (fun x => (ρ.sqrt x * c x) ^ 2) (haar 1) := hw.integrable_sq
  have hint : ∫ x, ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2
        ∂haar 1 = 4 * ∫ x, g0 x ^ 2 ∂haar 1
        + 4 * kappa * ∫ x, g0 x * (ρ.sqrt x * c x) ∂haar 1
        + kappa ^ 2 * ∫ x, (ρ.sqrt x * c x) ^ 2 ∂haar 1 := by
    have j1 := i1.const_mul 4
    have j2 := i2.const_mul (4 * kappa)
    have j3 := i3.const_mul (kappa ^ 2)
    have h12 := integral_add j1 j2
    have h123 := integral_add (j1.add j2) j3
    simp only [Pi.add_apply] at h123
    rw [integral_congr_ae hpt, h123, h12, integral_const_mul, integral_const_mul,
      integral_const_mul]
  have hJ : 4 * ∫ x, g0 x ^ 2 ∂haar 1 + 2 * kappa * ∫ x, densityDeriv ρ x * c x ∂haar 1
        + kappa ^ 2 * ∫ x, ρ.density x * (c x) ^ 2 ∂haar 1
      = ∫ x, ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2
        ∂haar 1 := by
    rw [hint]
    have e1 : ∫ x, densityDeriv ρ x * c x ∂haar 1
        = 2 * ∫ x, g0 x * (ρ.sqrt x * c x) ∂haar 1 := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [densityDeriv, hg0]; ring
    have e2 : ∫ x, ρ.density x * (c x) ^ 2 ∂haar 1 = ∫ x, (ρ.sqrt x * c x) ^ 2 ∂haar 1 := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [AbsoluteDensity.density]; ring
    rw [e1, e2]; ring
  have hnn : 0 ≤ ∫ x, ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2
        ∂haar 1 := integral_nonneg fun x => sq_nonneg _
  have hI : Integrable (fun x => ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x
      + ρ.sqrt x • b.force τ x‖ ^ 2) (haar 1) := by
    have := ((i1.const_mul 4).add (i2.const_mul (4 * kappa))).add (i3.const_mul (kappa ^ 2))
    refine this.congr ?_
    filter_upwards [hpt] with x hx
    rw [hx]; rfl
  refine ⟨_, hJ ▸ hnn, rfl, ?_⟩
  rw [hJ, ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun x => sq_nonneg _)]


theorem h1011_bary_deriv (F : SpeciesFamily 1) :
    ∀ᵐ x ∂haar 1, densityDeriv (barycenter F) x
      = ∑ s, F.weight s * densityDeriv (F.density s) x := by
  have hs : ∀ s : Fin F.count, IsWeakGradient (F.density s).density
      (fun x => (2 * (F.density s).sqrt x) • F.sqrtGradient s x) := fun s => by
    obtain ⟨-, -, -, h, -⟩ := admissibleRegularity (F.density s)
    exact h
  have key : ∀ S : Finset (Fin F.count), IsWeakGradient
      (fun x => ∑ s ∈ S, F.weight s * (F.density s).density x)
      (fun x => ∑ s ∈ S, F.weight s • ((2 * (F.density s).sqrt x) • F.sqrtGradient s x)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using (isWeakGradient_zero (d := 1))
    | insert a S ha ih =>
      have := ((hs a).smul (F.weight a)).add ih
      simpa [Finset.sum_insert ha] using this
  have hb : IsWeakGradient (barycenter F).density
      (fun x => ∑ s, F.weight s • ((2 * (F.density s).sqrt x) • F.sqrtGradient s x)) := by
    have := key Finset.univ
    have e : (barycenter F).density = fun x => ∑ s, F.weight s * (F.density s).density x :=
      funext fun x => F.barycenter_density_apply x
    rw [e]; exact this
  obtain ⟨-, -, -, hbar, hb5, -⟩ := admissibleRegularity (barycenter F)
  filter_upwards [hbar.ae_eq hb] with x hx
  have h0 := congrArg (fun v : Tangent 1 => v 0) hx
  simp only at h0
  have h1 : densityDeriv (barycenter F) x = ((2 * (barycenter F).sqrt x) •
      weakGradient (barycenter F).sqrt (barycenter F).sqrt_mem x) 0 := (hb5 x).symm
  rw [h1, h0]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨-, -, -, -, h5, -⟩ := admissibleRegularity (F.density s)
  rw [← h5 x]; rfl


theorem h1011_int_mul_cont {f k : Torus 1 → ℝ} (hf : Integrable f (haar 1)) (hk : Continuous k) :
    Integrable (fun x => f x * k x) (haar 1) :=
  hf.mul_of_top_left (memLp_of_cont hk _)

/-- **H1011.** Exact scalar and species dissipation expansion for the positive `H¹` example:
`G = ∑ θ_s H(ρ_s) + (κ/2) P(ρ̄)` and
`D = ∑ θ_s I(ρ_s) + 2κ Q(ρ̄) + κ² ∫ ρ̄ |R′ * ρ̄|² dm`, where
`I(ρ) = 4 ∫ |(√ρ)′|²`; the scalar formulas are the case of one species. -/
theorem exact_scalar_and_species_dissipation_expansion :
    (∀ (b : AbsoluteDrift positiveH1) (ρ : AbsoluteDensity 1),
      (scalarGap positiveH1 ρ : ℝ) =
        (relativeEntropy (densityMeasure ρ) (haar 1)).toReal + kappa / 2 * P ρ ∧
      0 ≤ 4 * ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1 + 2 * kappa * Q ρ
        + kappa ^ 2 * ∫ x, ρ.density x * (conv dR ρ.density x) ^ 2 ∂haar 1 ∧
      scalarDissipation positiveH1 b ρ = ENNReal.ofReal
        (4 * ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1 + 2 * kappa * Q ρ
          + kappa ^ 2 * ∫ x, ρ.density x * (conv dR ρ.density x) ^ 2 ∂haar 1)) ∧
    (∀ (b : AbsoluteDrift positiveH1) (F : SpeciesFamily 1),
      (speciesGap positiveH1 F : ℝ) =
        ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal
          + kappa / 2 * P (barycenter F) ∧
      0 ≤ ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)
        + 2 * kappa * Q (barycenter F)
        + kappa ^ 2 * ∫ x, (barycenter F).density x * (conv dR (barycenter F).density x) ^ 2
          ∂haar 1 ∧
      speciesDissipation positiveH1 b F = ENNReal.ofReal
        (∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)
          + 2 * kappa * Q (barycenter F)
          + kappa ^ 2 * ∫ x, (barycenter F).density x * (conv dR (barycenter F).density x) ^ 2
            ∂haar 1)) := by
  have hnorm : ∀ (ρ : AbsoluteDensity 1),
      ∫ x, (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1
        = ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1 := fun ρ =>
    integral_congr_ae (Eventually.of_forall fun x => (h1011_norm_sq _).symm)
  refine ⟨fun b ρ => ?_, fun b F => ?_⟩
  · obtain ⟨J, hJ0, hJ, hl⟩ := h1011_core ρ ρ b
    have hQ := (weak_fourier_cross_term ρ).2.2
    rw [hQ, hnorm ρ] at hJ
    refine ⟨h1011_gap_scalar ρ, hJ ▸ hJ0, ?_⟩
    rw [← hJ]
    exact hl
  · choose J hJ0 hJ hl using fun s => h1011_core (F.density s) (barycenter F) b
    set c : Torus 1 → ℝ := conv dR (barycenter F).density with hc
    have hcc : Continuous c := continuous_driftField (barycenter F)
    have hB : ∀ s, Integrable (fun x => densityDeriv (F.density s) x * c x) (haar 1) := fun s =>
      h1011_int_mul_cont ((memLp_densityDeriv (F.density s)).integrable one_le_two) hcc
    have hC : ∀ s, Integrable (fun x => (F.density s).density x * (c x) ^ 2) (haar 1) := fun s =>
      h1011_int_mul_cont (F.density s).integrable_density (hcc.pow 2)
    have hBsum : ∑ s, F.weight s * ∫ x, densityDeriv (F.density s) x * c x ∂haar 1
        = Q (barycenter F) := by
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ fun s _ => (hB s).const_mul (F.weight s)]
      rw [← (weak_fourier_cross_term (barycenter F)).2.2]
      refine integral_congr_ae ?_
      filter_upwards [h1011_bary_deriv F] with x hx
      rw [hx, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    have hCsum : ∑ s, F.weight s * ∫ x, (F.density s).density x * (c x) ^ 2 ∂haar 1
        = ∫ x, (barycenter F).density x * (c x) ^ 2 ∂haar 1 := by
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ fun s _ => (hC s).const_mul (F.weight s)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [F.barycenter_density_apply x, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [AbsoluteDensity.density]; ring
    have hX : ∑ s, F.weight s * J s =
        ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)
          + 2 * kappa * Q (barycenter F)
          + kappa ^ 2 * ∫ x, (barycenter F).density x * (conv dR (barycenter F).density x) ^ 2
            ∂haar 1 := by
      rw [← hBsum, ← hCsum]
      have : ∀ s, F.weight s * J s = F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)
          + 2 * kappa * (F.weight s * ∫ x, densityDeriv (F.density s) x * c x ∂haar 1)
          + kappa ^ 2 * (F.weight s * ∫ x, (F.density s).density x * (c x) ^ 2 ∂haar 1) := by
        intro s
        rw [hJ s]
        simp only [SpeciesFamily.sqrtGradient]
        rw [hnorm (F.density s)]
        ring
      simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    refine ⟨h1011_gap_species F, ?_, ?_⟩
    · rw [← hX]
      exact Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) (hJ0 s)
    · rw [← hX]
      unfold speciesDissipation
      rw [ENNReal.ofReal_sum_of_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) (hJ0 s)]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [ENNReal.ofReal_mul (F.weight_nonneg s)]
      congr 1
      exact hl s

end DGPS.Examples.PositiveH1.Nonlinear
