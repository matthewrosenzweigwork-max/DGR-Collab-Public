import DGRHS.Gaussian.PeriodicLogMellin
import DGRHS.Gaussian.PeriodicMellinTailParticleCap
import DGRHS.Gaussian.PeriodicHeatDiagonalScale

/-!
Packet P9e, unit 2 (part 1): the long-time tail `t >= eps` of the torus LOG Mellin integral.
Torus form of the tail estimates of Lemma 4.3(ii) / Step 1 of Proposition 5.1 (TeX 1377-1405,
1664-1671): no infrared truncation is needed because `heat - 1` has no zero mode.

* `periodicLogTailEnvelope`: a spatially uniform integrable majorant of
  `t^(d/2-1) |heat(t+tau)(x) - 1|` (`~ t^(-1)` for `t <= 1`, exponentially small for `t > 1`);
* `periodicLogMellinTail`, its sup bound `periodicLogTailConst`, its identification with the proper
  cutoff representative, and the uniform-in-`N` negative-statistic cap (centering commutes with the
  tail integral; the per-time Gram cap `2 (heat(0) - 1)` is integrated).
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Majorant of the tail integrand, uniform in the spatial point and the heat shift. -/
def periodicLogTailEnvelope (ι : Type u) [Fintype ι] (t : ℝ) : ℝ :=
  if t ≤ 1 then (periodicHeatDiagonalSmallConstant ι + 1) * t⁻¹
  else periodicHeatTailMass ι * (t ^ periodicLogMellinExponent ι * Real.exp (-t / 2))

lemma periodicLogTailEnvelope_nonneg (t : ℝ) (ht : 0 < t) :
    0 ≤ periodicLogTailEnvelope ι t := by
  have hC := periodicHeatDiagonalSmallConstant_nonneg (ι := ι)
  have hD := periodicHeatTailMass_nonneg (ι := ι)
  unfold periodicLogTailEnvelope
  split_ifs
  · positivity
  · have := Real.rpow_nonneg ht.le (periodicLogMellinExponent ι)
    positivity

lemma periodicLogTail_integrand_le (τ t : ℝ) (ht : 0 < t) (hτ : 0 ≤ τ)
    (x : PeriodicTorus ι) :
    ‖t ^ periodicLogMellinExponent ι * ((periodicGaussianHeat (t + τ) x).re - 1)‖ ≤
      periodicLogTailEnvelope ι t := by
  have hp : 0 ≤ t ^ periodicLogMellinExponent ι := Real.rpow_nonneg ht.le _
  have hre : ‖(periodicGaussianHeat (t + τ) x).re - 1‖ ≤
      ‖periodicGaussianHeat (t + τ) x - 1‖ := by
    simpa only [Real.norm_eq_abs, Complex.sub_re, Complex.one_re] using
      Complex.abs_re_le_norm (periodicGaussianHeat (t + τ) x - 1)
  rw [norm_mul, Real.norm_of_nonneg hp]
  unfold periodicLogTailEnvelope
  split_ifs with h1
  · calc
      _ ≤ t ^ periodicLogMellinExponent ι *
          ((periodicHeatDiagonalSmallConstant ι + 1) * t ^ (-((Fintype.card ι : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left
          (hre.trans (periodicGaussianHeat_centered_shifted_small_bound t τ ht h1 hτ x)) hp
      _ = (periodicHeatDiagonalSmallConstant ι + 1) * t⁻¹ := by
        rw [mul_left_comm, ← Real.rpow_add ht, ← Real.rpow_neg_one]
        congr 2
        unfold periodicLogMellinExponent
        ring
  · have hl := periodicGaussianHeat_centered_shifted_large_bound t τ (le_of_lt (not_le.mp h1)) hτ x
    calc
      _ ≤ t ^ periodicLogMellinExponent ι * (Real.exp (-t / 2) * periodicHeatTailMass ι) :=
        mul_le_mul_of_nonneg_left (hre.trans hl) hp
      _ = _ := by ring

lemma periodicLogTailEnvelope_integrableOn (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (periodicLogTailEnvelope ι) (Ioi ε) := by
  have hsub : Ioi ε ⊆ Ioc ε 1 ∪ Ioi 1 := by
    intro t ht
    by_cases h : t ≤ 1
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr (lt_of_not_ge h)
  refine IntegrableOn.mono_set ?_ hsub
  refine IntegrableOn.union ?_ ?_
  · have hc : ContinuousOn (fun t : ℝ => (periodicHeatDiagonalSmallConstant ι + 1) * t⁻¹)
        (Icc ε 1) :=
      continuousOn_const.mul (ContinuousOn.inv₀ continuousOn_id
        (fun t ht => ne_of_gt (lt_of_lt_of_le hε ht.1)))
    have hi : IntegrableOn (fun t : ℝ => (periodicHeatDiagonalSmallConstant ι + 1) * t⁻¹)
        (Ioc ε 1) := (hc.integrableOn_Icc).mono_set (Ioc_subset_Icc_self (a := ε) (b := 1))
    refine IntegrableOn.congr_fun hi (fun t ht => ?_) measurableSet_Ioc
    show (periodicHeatDiagonalSmallConstant ι + 1) * t⁻¹ = periodicLogTailEnvelope ι t
    unfold periodicLogTailEnvelope
    rw [ite_eq_left ht.2]
  · have h := periodicUnshiftedMellin_majorant_integrable (periodicLogMellinExponent ι)
      periodicLogMellinExponent_gt
    have h1 : IntegrableOn (fun t : ℝ => periodicHeatTailMass ι *
        (t ^ periodicLogMellinExponent ι * Real.exp (-t / 2))) (Ioi 1) :=
      (h.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul (periodicHeatTailMass ι)
    refine IntegrableOn.congr_fun h1 (fun t ht => ?_) measurableSet_Ioi
    show periodicHeatTailMass ι * (t ^ periodicLogMellinExponent ι * Real.exp (-t / 2)) =
      periodicLogTailEnvelope ι t
    unfold periodicLogTailEnvelope
    rw [ite_eq_right (not_le.mpr ht)]

/-- The (finite) integral of the tail envelope: the uniform sup bound of the tail. -/
def periodicLogTailConst (ι : Type u) [Fintype ι] (ε : ℝ) : ℝ :=
  ∫ t in Ioi ε, periodicLogTailEnvelope ι t

lemma periodicLogTailConst_nonneg (ε : ℝ) (hε : 0 ≤ ε) : 0 ≤ periodicLogTailConst ι ε := by
  unfold periodicLogTailConst
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact periodicLogTailEnvelope_nonneg t (hε.trans_lt ht)

lemma periodicLogTailIntegrand_measurable (τ : ℝ) :
    Measurable (fun q : ℝ × PeriodicTorus ι =>
      q.1 ^ periodicLogMellinExponent ι * ((periodicGaussianHeat (q.1 + τ) q.2).re - 1)) := by
  have hm : Measurable (fun q : ℝ × PeriodicTorus ι => (q.1 + τ, q.2)) := by fun_prop
  have hh := (periodicGaussianHeat_joint_measurable (ι := ι)).comp hm
  exact (by fun_prop : Measurable (fun q : ℝ × PeriodicTorus ι =>
      q.1 ^ periodicLogMellinExponent ι)).mul
    ((Complex.continuous_re.measurable.comp hh).sub measurable_const)

/-- The long-time tail of the LOG Mellin integral. -/
def periodicLogMellinTail (τ ε : ℝ) (x : PeriodicTorus ι) : ℝ :=
  ∫ t : ℝ in Ioi ε, t ^ periodicLogMellinExponent ι *
    ((periodicGaussianHeat (t + τ) x).re - 1)

lemma periodicLogMellinTail_measurable (τ ε : ℝ) :
    Measurable (periodicLogMellinTail (ι := ι) τ ε) := by
  unfold periodicLogMellinTail
  exact ((periodicLogTailIntegrand_measurable (ι := ι) τ).stronglyMeasurable.integral_prod_left'
    (μ := (volume : Measure ℝ).restrict (Ioi ε))).measurable

lemma periodicLogTailIntegrand_integrableOn (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (x : PeriodicTorus ι) :
    IntegrableOn (fun t : ℝ => t ^ periodicLogMellinExponent ι *
      ((periodicGaussianHeat (t + τ) x).re - 1)) (Ioi ε) := by
  refine (periodicLogTailEnvelope_integrableOn (ι := ι) ε hε).mono'
    ((periodicLogTailIntegrand_measurable (ι := ι) τ).comp
      (show Measurable (fun t : ℝ => (t, x)) by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact periodicLogTail_integrand_le τ t (hε.trans ht) hτ x

lemma periodicLogMellinTail_norm_bound (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (x : PeriodicTorus ι) :
    ‖periodicLogMellinTail τ ε x‖ ≤ periodicLogTailConst ι ε := by
  have hi := periodicLogTailIntegrand_integrableOn τ ε hτ hε x
  calc
    _ ≤ ∫ t : ℝ in Ioi ε, ‖t ^ periodicLogMellinExponent ι *
        ((periodicGaussianHeat (t + τ) x).re - 1)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi ε, periodicLogTailEnvelope ι t := by
      apply integral_mono_ae hi.norm (periodicLogTailEnvelope_integrableOn (ι := ι) ε hε)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact periodicLogTail_integrand_le τ t (hε.trans ht) hτ x
    _ = _ := rfl

lemma periodicLogMellinTail_eq_cutoff_ae (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    periodicLogMellinTail (ι := ι) τ ε =ᵐ[periodicHaar ι]
      periodicMellinCutoff (periodicLogMellinExponent ι) τ ε :=
  (periodicMellinCutoff_ae_tail _ τ ε periodicLogMellinExponent_gt hτ hε).symm

lemma periodicLogMellinTail_integrable (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 ≤ ε) :
    Integrable (periodicLogMellinTail (ι := ι) τ ε) (periodicHaar ι) :=
  (periodicMellinCutoff_integrable _ τ ε periodicLogMellinExponent_gt hτ).congr
    (periodicLogMellinTail_eq_cutoff_ae τ ε hτ hε).symm

/-- Pair form of the tail integrand. -/
def periodicLogPairTailIntegrand (τ : ℝ)
    (q : ℝ × (PeriodicTorus ι × PeriodicTorus ι)) : ℝ :=
  q.1 ^ periodicLogMellinExponent ι *
    ((periodicGaussianHeat (q.1 + τ) (q.2.1 - q.2.2)).re - 1)

lemma periodicLogPairTailIntegrand_measurable (τ : ℝ) :
    Measurable (periodicLogPairTailIntegrand (ι := ι) τ) := by
  unfold periodicLogPairTailIntegrand
  have hm : Measurable (fun q : ℝ × (PeriodicTorus ι × PeriodicTorus ι) =>
      (q.1 + τ, q.2.1 - q.2.2)) := by fun_prop
  exact (show Measurable (fun q : ℝ × (PeriodicTorus ι × PeriodicTorus ι) =>
      q.1 ^ periodicLogMellinExponent ι) by fun_prop).mul
    ((Complex.continuous_re.measurable.comp
      (periodicGaussianHeat_joint_measurable.comp hm)).sub measurable_const)

lemma periodicLogPairTailIntegrand_uniform_bound (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) :
    ∀ᵐ t ∂volume.restrict (Ioi ε), ∀ p : PeriodicTorus ι × PeriodicTorus ι,
      ‖periodicLogPairTailIntegrand τ (t, p)‖ ≤ periodicLogTailEnvelope ι t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  intro p
  exact periodicLogTail_integrand_le τ t (hε.trans ht) hτ (p.1 - p.2)

/-- Proper centering commutes with the tail integral, pointwise at every spatial pair. -/
lemma periodicLogMellinTail_centering_commutes (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    Integrable (fun t => hoeffdingCentered μ
      (fun q => periodicLogPairTailIntegrand τ (t, q)) p) (volume.restrict (Ioi ε)) ∧
    hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicLogMellinTail τ ε (q.1 - q.2)) p =
      ∫ t : ℝ in Ioi ε, hoeffdingCentered μ
        (fun q => periodicLogPairTailIntegrand τ (t, q)) p := by
  have hm := (periodicLogPairTailIntegrand_measurable (ι := ι) τ).stronglyMeasurable
  have hi := periodicLogTailEnvelope_integrableOn (ι := ι) ε hε
  have hb := periodicLogPairTailIntegrand_uniform_bound (ι := ι) τ ε hτ hε
  exact ⟨integrable_parameter_hoeffdingCentered_of_envelope _ μ _ hm _ hi hb p,
    hoeffdingCentered_integral_parameter_of_envelope _ μ _ hm _ hi hb p⟩

lemma periodicLogTailIntegrand_particle_cap (τ t : ℝ) (ht : 0 < t) (hτ : 0 ≤ τ)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    iidNegativeStatistic N (hoeffdingCentered μ
      (fun p => periodicLogPairTailIntegrand τ (t, p))) x ≤
      2 * periodicLogTailEnvelope ι t := by
  let c : ℝ := t ^ periodicLogMellinExponent ι
  let W : PeriodicTorus ι × PeriodicTorus ι → ℝ :=
    fun p => (periodicGaussianHeat (t + τ) (p.1 - p.2)).re - 1
  have hc : 0 ≤ c := Real.rpow_nonneg ht.le _
  have htτ := add_pos_of_pos_of_nonneg ht hτ
  have hcap : iidNegativeStatistic N (hoeffdingCentered μ W) x ≤
      2 * ((periodicGaussianHeat (t + τ) (0 : PeriodicTorus ι)).re - 1) := by
    simpa only [iidNegativeStatistic, iidCoupledSum, DGRHS.Decoupling.offDiagonalSum,
      ite_not] using periodicCenteredHeat_centered_particle_cap (t + τ) htτ μ N hN x
  have hdiag : c * ((periodicGaussianHeat (t + τ) (0 : PeriodicTorus ι)).re - 1) ≤
      periodicLogTailEnvelope ι t := by
    have h := periodicLogTail_integrand_le τ t ht hτ (0 : PeriodicTorus ι)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have he : hoeffdingCentered μ (fun p => periodicLogPairTailIntegrand τ (t, p)) =
      c • hoeffdingCentered μ W := by
    funext p
    exact hoeffdingCentered_const_mul_pointwise μ W c p
  rw [he, physical_iidNegativeStatistic_const_smul]
  calc
    _ ≤ c * (2 * ((periodicGaussianHeat (t + τ) (0 : PeriodicTorus ι)).re - 1)) :=
      mul_le_mul_of_nonneg_left hcap hc
    _ = 2 * (c * ((periodicGaussianHeat (t + τ) (0 : PeriodicTorus ι)).re - 1)) := by ring
    _ ≤ _ := by linarith

/-- Uniform-in-`N` deterministic cap of the centered tail negative statistic. -/
lemma periodicLogMellinTail_particle_cap (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    iidNegativeStatistic N (hoeffdingCentered μ
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinTail τ ε (p.1 - p.2))) x ≤
      2 * periodicLogTailConst ι ε := by
  let ν : Measure ℝ := volume.restrict (Ioi ε)
  let H := fun (t : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) =>
    hoeffdingCentered μ (fun q => periodicLogPairTailIntegrand τ (t, q)) p
  have hi (p : PeriodicTorus ι × PeriodicTorus ι) : Integrable (fun t => H t p) ν :=
    (periodicLogMellinTail_centering_commutes τ ε hτ hε μ p).1
  have he : hoeffdingCentered μ
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinTail τ ε (p.1 - p.2)) =
      fun p => ∫ t, H t p ∂ν := by
    funext p
    exact (periodicLogMellinTail_centering_commutes τ ε hτ hε μ p).2
  rw [he, ← integral_iidNegativeStatistic_parameter ν H hi N x]
  have henv : Integrable (fun t : ℝ => 2 * periodicLogTailEnvelope ι t) ν :=
    (periodicLogTailEnvelope_integrableOn (ι := ι) ε hε).const_mul 2
  calc
    _ ≤ ∫ t, 2 * periodicLogTailEnvelope ι t ∂ν := by
      apply integral_mono_ae (integrable_iidNegativeStatistic_parameter ν H hi N x) henv
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact periodicLogTailIntegrand_particle_cap τ t (hε.trans ht) hτ μ N hN x
    _ = _ := by
      rw [integral_const_mul]
      rfl

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogTailEnvelope_nonneg
#print axioms DGRHS.Periodic.periodicLogTail_integrand_le
#print axioms DGRHS.Periodic.periodicLogTailEnvelope_integrableOn
#print axioms DGRHS.Periodic.periodicLogTailConst_nonneg
#print axioms DGRHS.Periodic.periodicLogTailIntegrand_measurable
#print axioms DGRHS.Periodic.periodicLogMellinTail_measurable
#print axioms DGRHS.Periodic.periodicLogTailIntegrand_integrableOn
#print axioms DGRHS.Periodic.periodicLogMellinTail_norm_bound
#print axioms DGRHS.Periodic.periodicLogMellinTail_eq_cutoff_ae
#print axioms DGRHS.Periodic.periodicLogMellinTail_integrable
#print axioms DGRHS.Periodic.periodicLogPairTailIntegrand_measurable
#print axioms DGRHS.Periodic.periodicLogPairTailIntegrand_uniform_bound
#print axioms DGRHS.Periodic.periodicLogMellinTail_centering_commutes
#print axioms DGRHS.Periodic.periodicLogTailIntegrand_particle_cap
#print axioms DGRHS.Periodic.periodicLogMellinTail_particle_cap
