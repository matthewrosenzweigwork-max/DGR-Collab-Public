import DGRHS.Gaussian.PeriodicLogTransportBound
import DGRHS.Gaussian.PeriodicRieszLocalM1
import DGRHS.Gaussian.PeriodicLogTheorem22ii

/-!
Packet P9h, unit 3 (LOG, part 9): the pointwise smooth representative `periodicLogPair` of the periodic
LOG kernel, its everywhere lower bound, and the identification of the P9 torus LOG singular partition
and Gibbs law with the exponential `-β N F_N` written with it (torus version of
`SourceLogEnergyLowerBound` and of the singular identification).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The pointwise smooth representative of the periodic LOG kernel as a function on the torus. -/
def periodicLogPairFun (z : PeriodicTorus ι) : ℝ :=
  if z = 0 then 0 else periodicLogSmooth (periodicCenteredLift z)

/-- The pair kernel. -/
def periodicLogPair (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ := periodicLogPairFun (p.1 - p.2)

lemma periodicLogPairFun_ae : periodicLogPairFun (ι := ι) =ᵐ[periodicHaar ι] periodicLogKernel := by
  have h := periodicLogSmoothLift_ae (ι := ι) periodicRieszTau periodicRieszTau_pos
  haveI := periodicHaar_nullSingletonClass (ι := ι)
  filter_upwards [h, (periodicHaar ι).ae_ne 0] with x hx hx0
  unfold periodicLogPairFun
  rw [ite_eq_right hx0]
  exact hx

lemma integrable_periodicLogPairFun : Integrable (periodicLogPairFun (ι := ι)) (periodicHaar ι) :=
  (periodicLogKernel_integrable (ι := ι)).congr periodicLogPairFun_ae.symm

lemma integral_abs_periodicLogPairFun :
    ∫ z, |periodicLogPairFun (ι := ι) z| ∂periodicHaar ι = ∫ z, |periodicLogKernel (ι := ι) z| ∂periodicHaar ι := by
  refine integral_congr_ae ?_
  filter_upwards [periodicLogPairFun_ae (ι := ι)] with x hx
  rw [hx]

lemma periodicLogPairFun_neg (z : PeriodicTorus ι) : periodicLogPairFun (-z) = periodicLogPairFun z := by
  by_cases hz : z = 0
  · subst hz; simp
  have hz' : -z ≠ 0 := neg_ne_zero.mpr hz
  simp only [periodicLogPairFun, ite_eq_right hz, ite_eq_right hz']
  obtain ⟨m, hm⟩ := exists_centeredLift_neg z
  rw [hm, periodicLogSmooth_add_lattice, periodicLogSmooth_neg]

lemma periodicLogPair_symm (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicLogPair p.swap = periodicLogPair p := by
  unfold periodicLogPair
  have : (p.swap.1 - p.swap.2) = -(p.1 - p.2) := by simp
  rw [this, periodicLogPairFun_neg]

lemma measurable_periodicLogSmooth : Measurable (periodicLogSmooth (ι := ι)) := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hP : Measurable (periodicLogProfileSum (ι := ι) periodicRieszTau) := by
    unfold periodicLogProfileSum
    exact Measurable.tsum fun m =>
      (stronglyMeasurable_gaussianLogShortRange periodicRieszTau periodicRieszTau_pos hd).measurable.comp
        (measurable_id.add_const _)
  have hL : Measurable (periodicLogLongKernel (ι := ι) (periodicHeatCut periodicRieszTau)) :=
    (contDiff_periodicLogLongKernel (periodicHeatCut periodicRieszTau)
      (periodicHeatCut_pos periodicRieszTau_pos) 0).continuous.measurable
  unfold periodicLogSmooth periodicLogSmoothLift
  exact ((measurable_const.mul hP).add hL).sub measurable_const

lemma measurable_periodicLogPairFun : Measurable (periodicLogPairFun (ι := ι)) := by
  unfold periodicLogPairFun
  exact Measurable.ite (measurableSet_singleton (0 : PeriodicTorus ι)) measurable_const
    (measurable_periodicLogSmooth.comp measurable_periodicCenteredLift)

lemma measurable_periodicLogPair : Measurable (periodicLogPair (ι := ι)) :=
  measurable_periodicLogPairFun.comp (measurable_fst.sub measurable_snd)

/-- Pointwise lower bound constant of the smooth representative. -/
def periodicLogPairLower (ι : Type u) [Fintype ι] [Nonempty ι] : ℝ :=
  (∑' k : PeriodicFrequency ι, periodicLogLCCoeff (periodicHeatCut periodicRieszTau) k) +
    periodicLogMellinFactor ι * (periodicHeatCut periodicRieszTau) ^ ((Fintype.card ι : ℝ) / 2) /
      ((Fintype.card ι : ℝ) / 2)

lemma periodicLogPairLower_nonneg : 0 ≤ periodicLogPairLower ι := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have h1 : 0 ≤ ∑' k : PeriodicFrequency ι, periodicLogLCCoeff (periodicHeatCut periodicRieszTau) k :=
    tsum_nonneg fun k => periodicLogLCCoeff_nonneg _ (periodicHeatCut_pos periodicRieszTau_pos).le k
  have h2 := periodicLogMellinFactor_pos (ι := ι)
  have h3 := periodicHeatCut_pos periodicRieszTau_pos
  unfold periodicLogPairLower
  positivity

lemma periodicLogPairFun_lower (z : PeriodicTorus ι) : -periodicLogPairLower ι ≤ periodicLogPairFun z := by
  have hw := periodicLogPairLower_nonneg (ι := ι)
  by_cases hz : z = 0
  · subst hz; simp [periodicLogPairFun]; exact hw
  simp only [periodicLogPairFun, ite_eq_right hz]
  set y := periodicCenteredLift z with hy
  have hP : 0 ≤ periodicLogProfileSum (ι := ι) periodicRieszTau y :=
    tsum_nonneg fun m => gaussianLogShortRange_nonneg _ _
  have hL := norm_iteratedFDeriv_periodicLogLongKernel_le (ι := ι) (periodicHeatCut periodicRieszTau)
    (periodicHeatCut_pos periodicRieszTau_pos) 0 y
  simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one, Real.norm_eq_abs] at hL
  have hL' := (abs_le.mp hL).1
  have hc0 := periodicLogSmoothCoeff_pos (ι := ι)
  change -periodicLogPairLower ι ≤ periodicLogSmoothCoeff ι * periodicLogProfileSum periodicRieszTau y +
    periodicLogLongKernel (periodicHeatCut periodicRieszTau) y - _
  unfold periodicLogPairLower
  nlinarith [mul_nonneg hc0.le hP]

lemma periodicLogPair_lower (p : PeriodicTorus ι × PeriodicTorus ι) :
    -periodicLogPairLower ι ≤ periodicLogPair p := periodicLogPairFun_lower _

lemma periodicLogPair_potential_abs_le (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (x : PeriodicTorus ι) :
    |DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogPair (a, b)) x| ≤
      M * ∫ z, |periodicLogKernel (ι := ι) z| ∂periodicHaar ι := by
  have hg := integrable_periodicLogPairFun (ι := ι)
  have hnn := periodicDensityRow_nonnegative_bound ρ M hM hρ (fun z => |periodicLogPairFun z|)
    hg.abs (fun z => abs_nonneg _) x
  rw [integral_abs_periodicLogPairFun] at hnn
  unfold DGRHS.potential
  simp only [periodicLogPair]
  calc |∫ y, periodicLogPairFun (x - y) ∂periodicCappedDensityMeasure ρ|
      ≤ ∫ y, |periodicLogPairFun (x - y)| ∂periodicCappedDensityMeasure ρ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := periodicCappedDensityMeasure ρ)
            (fun y => periodicLogPairFun (x - y))
    _ ≤ _ := hnn

lemma periodicLogKernel_pair_ae (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)) =ᵐ[
      (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)] periodicLogPair :=
  (periodic_pair_ae_of_haar_ae ρ M hρ (periodicLogPairFun_ae (ι := ι))).symm

lemma periodicLogPotential_eq (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (x : PeriodicTorus ι) :
    DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) x =
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogPair (a, b)) x := by
  have hG := periodicLogPairFun_ae (ι := ι)
  have h1 : (fun y => periodicLogPairFun (x - y)) =ᵐ[periodicHaar ι]
      (fun y => periodicLogKernel (x - y)) :=
    (periodicHaar_preserving_sub_left x).quasiMeasurePreserving.ae_eq_comp hG
  have hμ : periodicCappedDensityMeasure ρ ≪ periodicHaar ι :=
    Measure.absolutelyContinuous_of_le_smul (periodicCappedDensityMeasure_le ρ M hρ)
  unfold DGRHS.potential
  refine integral_congr_ae ?_
  filter_upwards [hμ.ae_eq h1] with y hy
  exact hy.symm

lemma periodicLogInteraction_eq (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) =
      DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogPair (a, b)) := by
  unfold DGRHS.interactionEnergy
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [periodicLogKernel_pair_ae ρ M hρ] with q hq
  exact hq

/-! ### The particle exponent -/

/-- The torus LOG particle exponent `-β N F_N` (smooth representative). -/
def periodicLogParticleExponent (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (β : ℝ) (N : ℕ)
    (ω : Fin N → PeriodicTorus ι) : ℝ :=
  -β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered (periodicCappedDensityMeasure ρ) periodicLogPair)
    (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogPair (a, b)))
    (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogPair (a, b))) N ω

lemma periodicLogParticleExponent_eq (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (β : ℝ) (N : ℕ) (hN : 0 < N)
    (ω : Fin N → PeriodicTorus ι) :
    periodicLogParticleExponent ρ β N ω =
      DGRHS.CLT.sourceParticleExponent
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) periodicLogPair)
        (DGRHS.potential (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicLogPair (a, b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicLogPair (a, b))) β N ω :=
  DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ β hN ω

lemma periodicLogSourceExponent_ae (β : ℝ) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    (fun ω => DGRHS.CLT.sourceParticleExponent (periodicLogCentered (periodicCappedDensityMeasure ρ))
        (DGRHS.potential (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))) β N ω) =ᵐ[
      Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)]
    (fun ω => DGRHS.CLT.sourceParticleExponent
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) periodicLogPair)
        (DGRHS.potential (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicLogPair (a, b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicLogPair (a, b))) β N ω) := by
  have hst := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) N _ _
    (ae_hoeffdingCentered_congr (periodicCappedDensityMeasure ρ) _ _
      (periodicLogKernel_pair_ae ρ M hρ))
  have hF : DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) =
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogPair (a, b)) :=
    funext (periodicLogPotential_eq ρ M hρ)
  have hI := periodicLogInteraction_eq ρ M hρ
  filter_upwards [hst] with ω hω
  rw [periodic_sourceParticleExponent_eq, periodic_sourceParticleExponent_eq, hF, hI]
  have hω' : iidNegativeStatistic N (periodicLogCentered (periodicCappedDensityMeasure ρ)) ω =
      iidNegativeStatistic N (hoeffdingCentered (periodicCappedDensityMeasure ρ) periodicLogPair) ω := hω
  rw [hω']

lemma periodicLogSingularGibbs_eq_particle (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    periodicLogSingularGibbs β ρ N =
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)).tilted
        (periodicLogParticleExponent ρ β N) := by
  have h := periodicLogSingularGibbs_eq β hβ ρ M hM hρ N
  dsimp only at h
  rw [h]
  apply tilted_congr
  filter_upwards [periodicLogSourceExponent_ae β ρ M hρ N] with ω hω
  rw [periodicLogParticleExponent_eq ρ β N (by omega)]
  exact hω

lemma periodicLogSourcePartition_eq_particle (β : ℝ) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    periodicLogSourcePartition β ρ N =
      ∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) := by
  unfold periodicLogSourcePartition
  refine integral_congr_ae ?_
  filter_upwards [periodicLogSourceExponent_ae β ρ M hρ N] with ω hω
  rw [periodicLogParticleExponent_eq ρ β N (by omega)]
  refine congrArg Real.exp ?_
  exact (DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ β (by omega : 0 < N) ω).trans hω

lemma periodicLogSingularPartition_toReal_eq (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) :
    (periodicLogSingularPartition β ρ N).toReal =
      ∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ) := by
  rw [periodicLogSingularPartition_eq_integral β hβ ρ M hM hρ N,
    ENNReal.toReal_ofReal (by
      unfold periodicLogSourcePartition
      exact integral_nonneg fun x => (Real.exp_pos _).le)]
  exact periodicLogSourcePartition_eq_particle β ρ M hρ N hN

lemma measurable_periodicLogParticleExponent (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (β : ℝ) (N : ℕ) (hN : 0 < N) :
    Measurable (periodicLogParticleExponent ρ β N) := by
  let μ := periodicCappedDensityMeasure ρ
  have hWm : StronglyMeasurable (periodicLogPair (ι := ι)) :=
    measurable_periodicLogPair.stronglyMeasurable
  have hE := measurable_physical_iidNegativeStatistic N _
    (stronglyMeasurable_hoeffdingCentered μ _ hWm).measurable
  have hF : Measurable (DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicLogPair (a, b))) :=
    hWm.integral_prod_right'.measurable
  have hSum : Measurable (fun ω : Fin N → PeriodicTorus ι => ∑ i : Fin N,
      DGRHS.potential μ (fun a b : PeriodicTorus ι => periodicLogPair (a, b)) (ω i)) :=
    Finset.measurable_sum _ (fun i _ => hF.comp (measurable_pi_apply i))
  have hm : Measurable (fun ω : Fin N → PeriodicTorus ι =>
      β * iidNegativeStatistic N (hoeffdingCentered μ periodicLogPair) ω +
        β * ((N : ℝ)⁻¹ * ∑ i : Fin N, DGRHS.potential μ
          (fun a b : PeriodicTorus ι => periodicLogPair (a, b)) (ω i)) -
        β * DGRHS.interactionEnergy μ (fun a b : PeriodicTorus ι => periodicLogPair (a, b))) :=
    ((hE.const_mul β).add ((hSum.const_mul (N : ℝ)⁻¹).const_mul β)).sub measurable_const
  convert hm using 1
  funext ω
  rw [periodicLogParticleExponent_eq ρ β N hN, periodic_sourceParticleExponent_eq]

/-- Uniform particle weights with the Jensen lower bound. -/
theorem periodicLogParticleWeight_uniform (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (periodicLogParticleExponent ρ β N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      Real.exp (β * DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))) ≤
        (∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨C, hC, hU⟩ := periodicLogPartition_uniform β hβ ρ M hM hρ
  have hrate := periodicLogSingularPartition_original_rate β hβ ρ M hM hρ
  obtain ⟨-, -, -, κ, eig, e, -, -, -, -, -, -, c, C', -, -, -, hr⟩ := hrate
  refine ⟨C, hC, fun N hN => ?_⟩
  have hn : 0 < N := by omega
  have hexp : (fun ω => Real.exp (periodicLogParticleExponent ρ β N ω)) =ᵐ[
      Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)))
        (DGRHS.potential (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)))
        (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
          (fun a b : PeriodicTorus ι => periodicLogKernel (a - b))) N ω)) := by
    filter_upwards [periodicLogSourceExponent_ae β ρ M hρ N] with ω hω
    rw [periodicLogParticleExponent_eq ρ β N hn]
    refine congrArg Real.exp ?_
    exact ((DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ β hn ω).trans hω).symm
  have hi := (hU N hN).1.congr hexp.symm
  have hb : (∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C := by
    rw [integral_congr_ae hexp]
    exact (hU N hN).2
  refine ⟨hi, ?_, hb⟩
  have hJ := (hr N hN).2.1
  rw [periodicLogSingularPartition_toReal_eq β hβ ρ M hM hρ N hN] at hJ
  exact hJ

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogParticleWeight_uniform
#print axioms DGRHS.Periodic.periodicLogSingularGibbs_eq_particle
