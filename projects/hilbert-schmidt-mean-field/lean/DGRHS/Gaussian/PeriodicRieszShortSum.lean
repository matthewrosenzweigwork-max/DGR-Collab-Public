import DGRHS.Gaussian.PeriodicRieszShortDecomp

/-!
Packet P9h, unit 2 (part 7): the short heat-time integral of the periodic heat series at a point off
the lattice equals the lattice sum of Gaussian-scale profiles (Tonelli for the image sum).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

lemma integrable_tsum_of_nonneg_summable_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {κ : Type*} [Countable κ] {F : κ → α → ℝ} (hF : ∀ i, Integrable (F i) μ)
    (hnn : ∀ i, 0 ≤ᵐ[μ] F i) (hpt : ∀ᵐ x ∂μ, Summable fun i => F i x)
    (hsum : Summable fun i => ∫ x, F i x ∂μ) : Integrable (fun x => ∑' i, F i x) μ := by
  refine ⟨AEStronglyMeasurable.tsum fun i => (hF i).1, ?_⟩
  have h1 : ∀ᵐ x ∂μ, ‖∑' i, F i x‖ₑ = ∑' i, ENNReal.ofReal (F i x) := by
    filter_upwards [hpt, ae_all_iff.2 hnn] with x hx hn
    rw [Real.enorm_eq_ofReal (tsum_nonneg hn)]
    exact ENNReal.ofReal_tsum_of_nonneg hn hx
  rw [HasFiniteIntegral, lintegral_congr_ae h1,
    lintegral_tsum (fun i => (hF i).1.aemeasurable.ennreal_ofReal)]
  have h2 : ∀ i, ∫⁻ x, ENNReal.ofReal (F i x) ∂μ = ENNReal.ofReal (∫ x, F i x ∂μ) :=
    fun i => (ofReal_integral_eq_lintegral_ofReal (hF i) (hnn i)).symm
  simp_rw [h2]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg_of_ae (hnn i)) hsum]
  exact ENNReal.ofReal_lt_top

lemma summable_periodicProfile_translate (c s η : ℝ) (hc : 0 ≤ c) (hs : 0 < s) (hη : 0 < η)
    (S : Set ℝ) (hSm : MeasurableSet S) (hS : S ⊆ Ioc 0 η) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    Summable fun m : PeriodicFrequency ι => periodicProfile c s S (z + periodicFrequencyVector m) := by
  obtain ⟨r, hr, -, hk⟩ := periodicProfile_translate_local_bounds c s η hc hs hη S hSm hS z hz
  obtain ⟨u, hu, hub⟩ := hk 0
  refine Summable.of_norm_bounded hu (fun m => ?_)
  have := hub m z (mem_ball_self hr)
  simpa only [norm_iteratedFDeriv_zero] using this

lemma periodicHeatImageIntegrand_nonneg (s : ℝ) (y : E) {u : ℝ} (hu : 0 < u) :
    0 ≤ periodicHeatImageIntegrand s y u := by
  unfold periodicHeatImageIntegrand
  positivity

theorem periodic_short_heat_integral (s τ : ℝ) (hs : 0 < s) (hτ : 0 < τ) {z : E}
    (hz : z ∈ (periodicOffLattice : Set E)) :
    IntegrableOn (fun u : ℝ => u ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
      (periodicGaussianHeat u (periodicLift z)).re) (Ioc 0 (2 * Real.pi ^ 2 * τ ^ 2)) ∧
    ∫ u in Ioc 0 (2 * Real.pi ^ 2 * τ ^ 2), u ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
        (periodicGaussianHeat u (periodicLift z)).re =
      periodicProfileSum (periodicRieszProfileConst ι s) s (Ioc 0 τ) z := by
  set ε : ℝ := 2 * Real.pi ^ 2 * τ ^ 2 with hε
  set μ : Measure ℝ := volume.restrict (Ioc 0 ε) with hμ
  let F : PeriodicFrequency ι → ℝ → ℝ := fun m u =>
    periodicHeatImageIntegrand s (z + periodicFrequencyVector m) u
  have hc0 : 0 ≤ periodicRieszProfileConst ι s := (periodicRieszProfileConst_pos s).le
  have hFint : ∀ m, Integrable (F m) μ := fun m =>
    (periodicHeatImage_substitution s τ hs hτ (z + periodicFrequencyVector m)).2 (hz m)
  have hFnn : ∀ m, 0 ≤ᵐ[μ] F m := by
    intro m
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact periodicHeatImageIntegrand_nonneg s _ hu.1
  have hpt : ∀ᵐ u ∂μ, Summable fun m => F m u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := hu.1
    have h := (summable_exp_neg_lattice (ι := ι) (Real.pi ^ 2 / u) (by positivity) z).mul_left
      (Real.pi ^ ((Fintype.card ι : ℝ) / 2) * u ^ (-s / 2 - 1))
    refine h.congr (fun m => ?_)
    simp only [F, periodicHeatImageIntegrand]
    congr 2
    ring
  have hFint0 : ∀ m, ∫ u, F m u ∂μ = periodicProfile (periodicRieszProfileConst ι s) s (Ioc 0 τ)
      (z + periodicFrequencyVector m) := fun m =>
    (periodicHeatImage_substitution s τ hs hτ (z + periodicFrequencyVector m)).1
  have hsumI : Summable fun m => ∫ u, F m u ∂μ := by
    simp_rw [hFint0]
    exact summable_periodicProfile_translate _ s τ hc0 hs hτ (Ioc 0 τ) measurableSet_Ioc
      (fun t ht => ht) hz
  have hnormeq : ∀ m, ∫ u, ‖F m u‖ ∂μ = ∫ u, F m u ∂μ := by
    intro m
    refine integral_congr_ae ?_
    filter_upwards [hFnn m] with u hu
    rw [Real.norm_of_nonneg hu]
  have hsumN : Summable fun m => ∫ u, ‖F m u‖ ∂μ := by
    simp_rw [hnormeq]; exact hsumI
  have hInt : Integrable (fun u => ∑' m, F m u) μ :=
    integrable_tsum_of_nonneg_summable_integral hFint hFnn hpt hsumI
  have hEq : (fun u : ℝ => u ^ (((Fintype.card ι : ℝ) - s) / 2 - 1) *
      (periodicGaussianHeat u (periodicLift z)).re) =ᵐ[μ] fun u => ∑' m, F m u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact periodic_heat_weighted_eq_tsum s z hu.1
  refine ⟨hInt.congr hEq.symm, ?_⟩
  rw [integral_congr_ae hEq, ← integral_tsum_of_summable_integral_norm hFint hsumN]
  unfold periodicProfileSum
  exact tsum_congr hFint0

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_short_heat_integral
