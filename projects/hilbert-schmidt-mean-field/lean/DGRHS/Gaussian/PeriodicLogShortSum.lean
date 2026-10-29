import DGRHS.Gaussian.PeriodicLogProfile
import DGRHS.Gaussian.PeriodicRieszShortSum

/-!
Packet P9h, unit 3 (LOG, part 2): the short heat-time integral of the periodic heat series off the
lattice equals `2 π^{d/2}` times the lattice sum of the LOG short-range profile (the `s = 0` case of
`periodic_short_heat_integral`, which needs `s > 0`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma periodicLogProfile_eq (c τ : ℝ) (y : E) :
    periodicProfile c 0 (Ioc 0 τ) y = c * gaussianLogShortRange τ y := by
  unfold periodicProfile gaussianLogShortRange
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  simp only [neg_zero, zero_sub, Real.rpow_neg_one]
  rfl

/-- The change of variables `u = 2π²t²` for the LOG profile (`s = 0`). -/
lemma periodicHeatImage_substitution_log (τ : ℝ) (hτ : 0 < τ) (y : E) :
    ∫ u in Ioc 0 (2 * Real.pi ^ 2 * τ ^ 2), periodicHeatImageIntegrand 0 y u =
      periodicRieszProfileConst ι 0 * gaussianLogShortRange τ y ∧
    (y ≠ 0 → IntegrableOn (periodicHeatImageIntegrand 0 y) (Ioc 0 (2 * Real.pi ^ 2 * τ ^ 2))) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  let f : ℝ → ℝ := fun t => 2 * Real.pi ^ 2 * t ^ 2
  let f' : ℝ → ℝ := fun t => 4 * Real.pi ^ 2 * t
  have hS : MeasurableSet (Ioc (0 : ℝ) τ) := measurableSet_Ioc
  have hf' : ∀ t ∈ Ioc (0 : ℝ) τ, HasDerivWithinAt f (f' t) (Ioc 0 τ) t := by
    intro t _
    have h := (hasDerivAt_pow 2 t).const_mul (2 * Real.pi ^ 2)
    refine (h.hasDerivWithinAt).congr_deriv ?_
    simp only [f']
    push_cast
    ring
  have hinj : InjOn f (Ioc 0 τ) := by
    intro a ha b hb hab
    have h : a ^ 2 = b ^ 2 := by
      have hc : (2 * Real.pi ^ 2) ≠ 0 := by positivity
      exact mul_left_cancel₀ hc hab
    exact (pow_left_inj₀ ha.1.le hb.1.le (by norm_num)).1 h
  have himage : f '' Ioc 0 τ = Ioc 0 (2 * Real.pi ^ 2 * τ ^ 2) := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨by have := ht.1; positivity, ?_⟩
      have := ht.2
      have h0 := ht.1
      show 2 * Real.pi ^ 2 * t ^ 2 ≤ 2 * Real.pi ^ 2 * τ ^ 2
      have : t ^ 2 ≤ τ ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    · intro hu
      refine ⟨Real.sqrt (u / (2 * Real.pi ^ 2)), ⟨Real.sqrt_pos.2 (div_pos hu.1 (by positivity)), ?_⟩, ?_⟩
      · rw [Real.sqrt_le_left hτ.le]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hu.2]
      · show 2 * Real.pi ^ 2 * Real.sqrt (u / (2 * Real.pi ^ 2)) ^ 2 = u
        rw [Real.sq_sqrt (div_pos hu.1 (by positivity)).le]
        field_simp
  have hint : IntegrableOn (fun t => |f' t| • periodicHeatImageIntegrand 0 y (f t)) (Ioc 0 τ) ∨ y = 0 := by
    by_cases hy : y = 0
    · exact Or.inr hy
    · left
      have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have h := DGRHS.Gaussian.integrableOn_gaussianLog_profile_short τ ‖y‖ hτ hy'
      have h2 : IntegrableOn (fun t : ℝ => t ^ (-(0 : ℝ) - 1) * sourceRieszGaussianScale t y) (Ioc 0 τ) := by
        refine h.congr_fun (fun t ht => ?_) hS
        simp only [neg_zero, zero_sub, Real.rpow_neg_one]
        rfl
      exact IntegrableOn.congr_fun (h2.const_mul (periodicRieszProfileConst ι 0))
        (fun t ht => (periodicHeatImageIntegrand_sub 0 τ y ht.1).symm) hS
  constructor
  · rw [← himage, integral_image_eq_integral_abs_deriv_smul hS hf' hinj]
    rw [setIntegral_congr_fun hS (fun t ht => periodicHeatImageIntegrand_sub 0 τ y ht.1)]
    rw [integral_const_mul]
    congr 1
    unfold gaussianLogShortRange
    refine setIntegral_congr_fun hS (fun t ht => ?_)
    simp only [neg_zero, zero_sub, Real.rpow_neg_one]
    rfl
  · intro hy
    rw [← himage]
    refine (integrableOn_image_iff_integrableOn_abs_deriv_smul hS hf' hinj _).2 ?_
    rcases hint with h | h
    · exact h
    · exact absurd h hy

theorem periodic_short_heat_integral_log (τ : ℝ) (hτ : 0 < τ) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    IntegrableOn (fun u : ℝ => u ^ (((Fintype.card ι : ℝ) - 0) / 2 - 1) *
      (periodicGaussianHeat u (periodicLift z)).re) (Ioc 0 (2 * Real.pi ^ 2 * τ ^ 2)) ∧
    ∫ u in Ioc 0 (2 * Real.pi ^ 2 * τ ^ 2), u ^ (((Fintype.card ι : ℝ) - 0) / 2 - 1) *
        (periodicGaussianHeat u (periodicLift z)).re =
      periodicRieszProfileConst ι 0 * periodicLogProfileSum τ z := by
  set ε : ℝ := 2 * Real.pi ^ 2 * τ ^ 2 with hε
  set μ : Measure ℝ := volume.restrict (Ioc 0 ε) with hμ
  let F : PeriodicFrequency ι → ℝ → ℝ := fun m u =>
    periodicHeatImageIntegrand 0 (z + periodicFrequencyVector m) u
  have hc0 : 0 ≤ periodicRieszProfileConst ι 0 := (periodicRieszProfileConst_pos 0).le
  have hFint : ∀ m, Integrable (F m) μ := fun m =>
    (periodicHeatImage_substitution_log τ hτ (z + periodicFrequencyVector m)).2 (hz m)
  have hFnn : ∀ m, 0 ≤ᵐ[μ] F m := by
    intro m
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact periodicHeatImageIntegrand_nonneg 0 _ hu.1
  have hpt : ∀ᵐ u ∂μ, Summable fun m => F m u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := hu.1
    have h := (summable_exp_neg_lattice (ι := ι) (Real.pi ^ 2 / u) (by positivity) z).mul_left
      (Real.pi ^ ((Fintype.card ι : ℝ) / 2) * u ^ (-(0 : ℝ) / 2 - 1))
    refine h.congr (fun m => ?_)
    simp only [F, periodicHeatImageIntegrand]
    congr 2
    ring
  have hFint0 : ∀ m, ∫ u, F m u ∂μ = periodicRieszProfileConst ι 0 *
      gaussianLogShortRange τ (z + periodicFrequencyVector m) := fun m =>
    (periodicHeatImage_substitution_log τ hτ (z + periodicFrequencyVector m)).1
  have hsumI : Summable fun m => ∫ u, F m u ∂μ := by
    simp_rw [hFint0]
    exact (summable_gaussianLogShortRange_translate τ hτ hz).mul_left _
  have hnormeq : ∀ m, ∫ u, ‖F m u‖ ∂μ = ∫ u, F m u ∂μ := by
    intro m
    refine integral_congr_ae ?_
    filter_upwards [hFnn m] with u hu
    rw [Real.norm_of_nonneg hu]
  have hsumN : Summable fun m => ∫ u, ‖F m u‖ ∂μ := by
    simp_rw [hnormeq]; exact hsumI
  have hInt : Integrable (fun u => ∑' m, F m u) μ :=
    integrable_tsum_of_nonneg_summable_integral hFint hFnn hpt hsumI
  have hEq : (fun u : ℝ => u ^ (((Fintype.card ι : ℝ) - 0) / 2 - 1) *
      (periodicGaussianHeat u (periodicLift z)).re) =ᵐ[μ] fun u => ∑' m, F m u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact periodic_heat_weighted_eq_tsum 0 z hu.1
  refine ⟨hInt.congr hEq.symm, ?_⟩
  rw [integral_congr_ae hEq, ← integral_tsum_of_summable_integral_norm hFint hsumN]
  unfold periodicLogProfileSum
  rw [tsum_congr hFint0, tsum_mul_left]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_short_heat_integral_log
