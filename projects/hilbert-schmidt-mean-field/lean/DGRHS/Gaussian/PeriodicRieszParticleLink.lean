import DGRHS.Gaussian.PeriodicRieszLocalMaster
import DGRHS.Gaussian.PeriodicRieszTheorem211
import DGRHS.Gaussian.PeriodicRieszLowerCutTheorem22ii
import DGRHS.Gaussian.PeriodicRieszDensityPositive

/-!
Packet P9h, unit 2 (part 26): the torus particle exponent written with the pointwise smooth
representative `periodicRieszPair` and its identification with the P9 objects (the singular
partition and Gibbs law built from the spectral representative `periodicRieszKernel`):
`I_μ ≥ 0`, almost-sure equality of the exponents, `K_{N,β} = ∫ e^{exponent}`, `Q_{N,β} = tilted law`,
and uniform particle weights `1 ≤ ∫ e^{exponent} ≤ C` (torus form of `SourceRieszLocalPartition`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- A bounded capped density law has a measurable nonnegative density, bounded a.e. by the same
constant. -/
lemma exists_measurable_density (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    ∃ ρ' : PeriodicTorus ι → ℝ, Measurable ρ' ∧ (∀ x, 0 ≤ ρ' x) ∧
      (∀ᵐ x ∂periodicHaar ι, ρ' x ≤ M) ∧
      periodicCappedDensityMeasure ρ' = periodicCappedDensityMeasure ρ := by
  let μ := periodicCappedDensityMeasure ρ
  have hle := periodicCappedDensityMeasure_le ρ M hρ
  have hac : μ ≪ periodicHaar ι := Measure.absolutelyContinuous_of_le_smul hle
  let f := μ.rnDeriv (periodicHaar ι)
  have hfm : Measurable f := Measure.measurable_rnDeriv _ _
  have hfin : ∀ᵐ x ∂periodicHaar ι, f x < ∞ := Measure.rnDeriv_lt_top μ (periodicHaar ι)
  have hfM : f ≤ᵐ[periodicHaar ι] fun _ => ENNReal.ofReal M := by
    refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite hfm ?_
    intro t ht _
    calc (∫⁻ x in t, f x ∂periodicHaar ι) ≤ μ t := Measure.setLIntegral_rnDeriv_le t
      _ ≤ (ENNReal.ofReal M • periodicHaar ι) t := hle t
      _ = ∫⁻ _ in t, ENNReal.ofReal M ∂periodicHaar ι := by
        rw [setLIntegral_const]
        simp
  refine ⟨fun x => (f x).toReal, hfm.ennreal_toReal, fun x => ENNReal.toReal_nonneg, ?_, ?_⟩
  · filter_upwards [hfM] with x hx
    exact ENNReal.toReal_le_of_le_ofReal hM hx
  · have h1 : periodicCappedDensityMeasure (fun x => (f x).toReal) = (periodicHaar ι).withDensity f := by
      unfold periodicCappedDensityMeasure
      apply withDensity_congr_ae
      filter_upwards [hfin] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    rw [h1]
    exact Measure.withDensity_rnDeriv_eq μ (periodicHaar ι) hac


/-! ### Identification of the kernel representatives -/

lemma periodicRieszPotential_eq (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (x : PeriodicTorus ι) :
    DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)) x =
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) x := by
  have hG := periodicRieszPairFun_ae (ι := ι) s hs hs2
  have h1 : (fun y => periodicRieszPairFun s (x - y)) =ᵐ[periodicHaar ι]
      (fun y => periodicRieszKernel s hs2 (x - y)) :=
    (periodicHaar_preserving_sub_left x).quasiMeasurePreserving.ae_eq_comp hG
  have hμ : periodicCappedDensityMeasure ρ ≪ periodicHaar ι :=
    Measure.absolutelyContinuous_of_le_smul (periodicCappedDensityMeasure_le ρ M hρ)
  unfold DGRHS.potential
  refine integral_congr_ae ?_
  filter_upwards [hμ.ae_eq h1] with y hy
  simp only [periodicRieszPair_eq_fun]
  exact hy.symm

lemma periodicRieszInteraction_eq (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)) =
      DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) := by
  unfold DGRHS.interactionEnergy
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [periodicRieszKernel_pair_ae s hs hs2 ρ M hρ] with q hq
  exact hq

lemma periodicRieszInteraction_nonneg (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    0 ≤ DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) := by
  obtain ⟨ρ', hm, h0, hM', hcap⟩ := exists_measurable_density ρ M hM hρ
  have hform := periodicRiesz_density_bounded_form_nonneg s hs2 hs ρ' hm
    (Filter.Eventually.of_forall h0) M hM hM' (fun _ => 1) stronglyMeasurable_const 1 (by simp)
  rw [hcap] at hform
  rw [← periodicRieszInteraction_eq s hs hs2 ρ M hρ]
  unfold DGRHS.interactionEnergy
  refine mul_nonneg (by norm_num) ?_
  simpa only [mul_one] using hform

/-! ### The particle exponent -/

/-- The torus particle exponent `-β N F_N` (smooth representative). -/
def periodicRieszParticleExponent (s : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (β : ℝ) (N : ℕ)
    (ω : Fin N → PeriodicTorus ι) : ℝ :=
  -β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszPair s))
    (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)))
    (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) N ω

lemma periodicRieszParticleExponent_eq (s : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (β : ℝ) (N : ℕ) (hN : 0 < N)
    (ω : Fin N → PeriodicTorus ι) :
    periodicRieszParticleExponent s ρ β N ω =
      DGRHS.CLT.sourceParticleExponent
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszPair s))
        (DGRHS.potential (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) β N ω :=
  DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ β hN ω

lemma periodicRieszSourceExponent_ae (s β : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    (fun ω => DGRHS.CLT.sourceParticleExponent
        (periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ))
        (DGRHS.potential (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b))) β N ω) =ᵐ[
      Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)]
    (fun ω => DGRHS.CLT.sourceParticleExponent
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszPair s))
        (DGRHS.potential (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) β N ω) := by
  have hst := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) N _ _
    (ae_hoeffdingCentered_congr (periodicCappedDensityMeasure ρ) _ _
      (periodicRieszKernel_pair_ae s hs hs2 ρ M hρ))
  have hF : DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)) =
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) :=
    funext (periodicRieszPotential_eq s hs hs2 ρ M hρ)
  have hI := periodicRieszInteraction_eq s hs hs2 ρ M hρ
  filter_upwards [hst] with ω hω
  rw [periodic_sourceParticleExponent_eq, periodic_sourceParticleExponent_eq, hF, hI]
  have hω' : iidNegativeStatistic N (periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ)) ω =
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszPair s)) ω := hω
  rw [hω']

lemma periodicRieszSingularGibbs_eq_particle (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    periodicRieszSingularGibbs s β hs2 ρ N =
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)).tilted
        (periodicRieszParticleExponent s ρ β N) := by
  have h := periodicRieszSingularGibbs_eq s β hs hβ hs2 ρ M hM hρ N
  dsimp only at h
  rw [h]
  apply tilted_congr
  filter_upwards [periodicRieszSourceExponent_ae s β hs hs2 ρ M hρ N] with ω hω
  rw [periodicRieszParticleExponent_eq s ρ β N (by omega)]
  exact hω

lemma periodicRieszSourcePartition_eq_particle (s β : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    periodicRieszSourcePartition s β hs2 ρ N =
      ∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) := by
  unfold periodicRieszSourcePartition
  refine integral_congr_ae ?_
  filter_upwards [periodicRieszSourceExponent_ae s β hs hs2 ρ M hρ N] with ω hω
  rw [periodicRieszParticleExponent_eq s ρ β N (by omega)]
  refine congrArg Real.exp ?_
  exact (DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ β (by omega : 0 < N) ω).trans hω

lemma measurable_periodicRieszParticleExponent (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (β : ℝ) (N : ℕ) (hN : 0 < N) :
    Measurable (periodicRieszParticleExponent s ρ β N) := by
  let μ := periodicCappedDensityMeasure ρ
  have hWm : StronglyMeasurable (periodicRieszPair (ι := ι) s) :=
    (measurable_periodicRieszPair s hs hs2).stronglyMeasurable
  have hE := measurable_physical_iidNegativeStatistic N _
    (stronglyMeasurable_hoeffdingCentered μ _ hWm).measurable
  have hF : Measurable (DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) :=
    hWm.integral_prod_right'.measurable
  have hSum : Measurable (fun ω : Fin N → PeriodicTorus ι => ∑ i : Fin N,
      DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) (ω i)) :=
    Finset.measurable_sum _ (fun i _ => hF.comp (measurable_pi_apply i))
  have hm : Measurable (fun ω : Fin N → PeriodicTorus ι =>
      β * iidNegativeStatistic N (hoeffdingCentered μ (periodicRieszPair s)) ω +
        β * ((N : ℝ)⁻¹ * ∑ i : Fin N, DGRHS.potential μ
          (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) (ω i)) -
        β * DGRHS.interactionEnergy μ (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) :=
    ((hE.const_mul β).add ((hSum.const_mul (N : ℝ)⁻¹).const_mul β)).sub measurable_const
  convert hm using 1
  funext ω
  rw [periodicRieszParticleExponent_eq s ρ β N hN, periodic_sourceParticleExponent_eq]

/-- Uniform particle weights with the Jensen lower bound (torus form of
`sourceRieszLocalParticleWeight_uniform`). -/
theorem periodicRieszParticleWeight_uniform (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (periodicRieszParticleExponent s ρ β N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      1 ≤ (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨-, C, hC⟩ := periodicRieszWeight_uniform s β hs hβ hs2 ρ M hM hρ
  have hrate := periodicRieszSingularPartition_original_rate_full s β hs hβ hs2 ρ M hM hρ
  obtain ⟨-, -, -, κ, eig, e, -, -, -, -, -, -, C', -, hr⟩ := hrate
  have hI0 := periodicRieszInteraction_nonneg s hs hs2 ρ M hM hρ
  have hIeq := periodicRieszInteraction_eq s hs hs2 ρ M hρ
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun N hN => ?_⟩
  have hn : 0 < N := by omega
  have hexp : (fun ω => Real.exp (periodicRieszParticleExponent s ρ β N ω)) =ᵐ[
      Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (DGRHS.CLT.sourceParticleExponent
        (periodicRieszCentered s hs2 (periodicCappedDensityMeasure ρ))
        (DGRHS.potential (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b))) β N ω)) := by
    filter_upwards [periodicRieszSourceExponent_ae s β hs hs2 ρ M hρ N] with ω hω
    rw [periodicRieszParticleExponent_eq s ρ β N hn, ← hω]
  have hi := (hC N).1.congr hexp.symm
  have hb : (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C := by
    rw [integral_congr_ae hexp]
    exact (hC N).2
  refine ⟨hi, ?_, hb.trans (le_max_left _ _)⟩
  have hJ := (hr N hN).2.1
  have hK : (periodicRieszSingularPartition s β hs2 ρ N).toReal =
      periodicRieszSourcePartition s β hs2 ρ N := by
    rw [periodicRieszSingularPartition_eq_integral s β hs hβ hs2 ρ M hM hρ N]
    exact ENNReal.toReal_ofReal (by
      unfold periodicRieszSourcePartition
      exact integral_nonneg fun x => (Real.exp_pos _).le)
  rw [hK, periodicRieszSourcePartition_eq_particle s β hs hs2 ρ M hρ N hN] at hJ
  rw [hIeq] at hJ
  have h1 : 1 ≤ Real.exp (β * DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (mul_nonneg hβ hI0)
  exact h1.trans hJ

end DGRHS.Periodic
#print axioms DGRHS.Periodic.exists_measurable_density
#print axioms DGRHS.Periodic.periodicRieszInteraction_nonneg
#print axioms DGRHS.Periodic.periodicRieszSingularGibbs_eq_particle
#print axioms DGRHS.Periodic.periodicRieszParticleWeight_uniform
