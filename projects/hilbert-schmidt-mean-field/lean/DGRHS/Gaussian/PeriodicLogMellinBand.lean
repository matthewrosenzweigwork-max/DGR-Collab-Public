import DGRHS.Gaussian.PeriodicLogMellinTail
import DGRHS.Gaussian.PeriodicRieszMasterBand

/-!
Packet P9e, unit 2 (part 2): the finite heat-time band `[delta, a]` of the torus LOG Mellin integral
(the periodic analogue of `gaussianLogMasterBand`, Lemma 4.3(ii) / Proposition 5.1 log case,
TeX 1377-1405, 1673-1717).  At `s = 0` the band is *logarithmically* large:
`sup |band| <= K log(a/delta)` and the centered negative statistic is capped by `2 K log(a/delta)`
uniformly in the number of particles, with `K = C_small + 1`.  The `L^2(mu x mu)`-controls (row,
joint, operator) are small for small upper time `a`, exactly as in the Riesz band.

All objects are heat-time ("Mellin-level") objects without the normalization constant
`periodicLogMellinFactor`; the factor enters only through the coupling constant later.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators ENNReal Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- `K = C_small + 1`: the logarithmic band constant. -/
def periodicLogBandConst (ι : Type u) [Fintype ι] : ℝ := periodicHeatDiagonalSmallConstant ι + 1

lemma periodicLogBandConst_pos : 0 < periodicLogBandConst ι := by
  have := periodicHeatDiagonalSmallConstant_nonneg (ι := ι)
  unfold periodicLogBandConst
  linarith

lemma periodicLog_log_ratio_nonneg (δ a : ℝ) (hδ : 0 < δ) (hδa : δ ≤ a) :
    0 ≤ Real.log (a / δ) :=
  Real.log_nonneg ((one_le_div hδ).2 hδa)

lemma periodicLogBandIntegrand_small_norm_bound (τ t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hτ : 0 ≤ τ) (x : PeriodicTorus ι) :
    ‖periodicPositiveMellinIntegrand (periodicLogMellinExponent ι) τ t x‖ ≤
      periodicLogBandConst ι * t⁻¹ := by
  have hp : 0 ≤ t ^ periodicLogMellinExponent ι := Real.rpow_nonneg ht.le _
  have hC : periodicHeatDiagonalSmallConstant ι ≤ periodicLogBandConst ι := by
    unfold periodicLogBandConst; linarith
  calc
    _ = t ^ periodicLogMellinExponent ι * ‖(periodicGaussianHeat (t + τ) x).re‖ := by
      change ‖t ^ periodicLogMellinExponent ι * (periodicGaussianHeat (t + τ) x).re‖ = _
      rw [norm_mul, Real.norm_of_nonneg hp]
    _ ≤ t ^ periodicLogMellinExponent ι * ‖periodicGaussianHeat (t + τ) x‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) hp
    _ ≤ t ^ periodicLogMellinExponent ι *
        (periodicHeatDiagonalSmallConstant ι * t ^ (-((Fintype.card ι : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left (periodicGaussianHeat_shifted_small_bound t τ ht ht1 hτ x) hp
    _ ≤ t ^ periodicLogMellinExponent ι *
        (periodicLogBandConst ι * t ^ (-((Fintype.card ι : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg ht.le _)) hp
    _ = periodicLogBandConst ι * t⁻¹ := by
      rw [mul_left_comm, ← Real.rpow_add ht, ← Real.rpow_neg_one]
      congr 2
      unfold periodicLogMellinExponent
      ring

lemma periodicLog_inv_integrableOn (c δ a : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => c * t⁻¹) (Ioc δ a) := by
  have hc : ContinuousOn (fun t : ℝ => c * t⁻¹) (Icc δ a) :=
    continuousOn_const.mul (ContinuousOn.inv₀ continuousOn_id
      (fun t ht => ne_of_gt (lt_of_lt_of_le hδ ht.1)))
  exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self

lemma periodicLog_inv_integral (c δ a : ℝ) (hδ : 0 < δ) (hδa : δ ≤ a) :
    (∫ t : ℝ in Ioc δ a, c * t⁻¹) = c * Real.log (a / δ) := by
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hδa,
    integral_inv_of_pos hδ (hδ.trans_le hδa)]

lemma periodicLogBand_parameter_integrable (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (ha1 : a ≤ 1) (x : PeriodicTorus ι) :
    IntegrableOn (fun t : ℝ =>
      periodicPositiveMellinIntegrand (periodicLogMellinExponent ι) τ t x) (Ioc δ a) := by
  refine (periodicLog_inv_integrableOn (periodicLogBandConst ι) δ a hδ).mono'
    ((periodicPositiveMellinIntegrand_measurable (ι := ι) (periodicLogMellinExponent ι) τ).comp
      (show Measurable (fun t : ℝ => (t, x)) by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact periodicLogBandIntegrand_small_norm_bound τ t (hδ.trans ht.1) (ht.2.trans ha1) hτ x

lemma periodicLogBand_norm_bound (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδa : δ ≤ a)
    (ha1 : a ≤ 1) (x : PeriodicTorus ι) :
    ‖periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a x‖ ≤
      periodicLogBandConst ι * Real.log (a / δ) := by
  have hi := periodicLogBand_parameter_integrable τ δ a hτ hδ ha1 x
  have he := periodicLog_inv_integrableOn (periodicLogBandConst ι) δ a hδ
  calc
    _ ≤ ∫ t : ℝ in Ioc δ a,
        ‖periodicPositiveMellinIntegrand (periodicLogMellinExponent ι) τ t x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioc δ a, periodicLogBandConst ι * t⁻¹ := by
      apply integral_mono_ae hi.norm he
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact periodicLogBandIntegrand_small_norm_bound τ t (hδ.trans ht.1) (ht.2.trans ha1) hτ x
    _ = _ := periodicLog_inv_integral _ δ a hδ hδa

lemma periodicLogBand_pair_symmetric (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (x y : PeriodicTorus ι) :
    periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (x - y) =
      periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (y - x) := by
  unfold periodicPositiveMellinBand
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  unfold periodicPositiveMellinIntegrand
  rw [periodicGaussianHeat_real_sub_symmetric (t + τ)
    (add_pos_of_pos_of_nonneg (hδ.trans_lt ht.1) hτ) x y]

/-- Every row, every column, and the pair kernel of the band are proper for arbitrary probability
backgrounds (no density cap is needed). -/
lemma periodicLogBand_pair_proper (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδa : δ ≤ a)
    (ha1 : a ≤ 1) (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    (∀ x, Integrable (fun y => periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a
      (x - y)) μ) ∧
    (∀ y, Integrable (fun x => periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a
      (x - y)) μ) ∧
    Integrable (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2)) (μ.prod μ) := by
  have hm := periodicPositiveMellinBand_measurable (ι := ι) (periodicLogMellinExponent ι) τ δ a
  have hb := periodicLogBand_norm_bound (ι := ι) τ δ a hτ hδ hδa ha1
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact (integrable_const _).mono'
      (hm.comp (show Measurable (fun y => x - y) by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall (fun y => hb (x - y)))
  · intro y
    exact (integrable_const _).mono'
      (hm.comp (show Measurable (fun x => x - y) by fun_prop)).aestronglyMeasurable
      (Eventually.of_forall (fun x => hb (x - y)))
  · exact (integrable_const _).mono' (hm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
      (Eventually.of_forall (fun q => hb (q.1 - q.2)))

lemma periodicLogBand_centered_norm_bound (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδa : δ ≤ a)
    (ha1 : a ≤ 1) (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    ‖hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2)) p‖ ≤
      4 * (periodicLogBandConst ι * Real.log (a / δ)) :=
  norm_hoeffdingCentered_le_of_pointwise_bound μ _ _
    (fun q => periodicLogBand_norm_bound τ δ a hτ hδ hδa ha1 (q.1 - q.2)) p

lemma periodicLogBand_centered_memLp_infty (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδa : δ ≤ a) (ha1 : a ≤ 1) (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] :
    MemLp (hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2))) ∞ (μ.prod μ) := by
  have hK := periodicLogBandConst_pos (ι := ι)
  have hl := periodicLog_log_ratio_nonneg δ a hδ hδa
  have hD : 0 ≤ 4 * (periodicLogBandConst ι * Real.log (a / δ)) := by positivity
  apply (memLp_const (4 * (periodicLogBandConst ι * Real.log (a / δ)))).of_le
    (stronglyMeasurable_hoeffdingCentered μ _
      ((periodicPositiveMellinBand_measurable (ι := ι) (periodicLogMellinExponent ι) τ δ a
        ).stronglyMeasurable.comp_measurable
        (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_of_nonneg hD]
  exact periodicLogBand_centered_norm_bound τ δ a hτ hδ hδa ha1 μ p

/-- Scaled centered band: the LOG analogue of `periodicRieszMasterBand`. -/
def periodicLogMasterBand (τ δ a c : ℝ) (ρ : PeriodicTorus ι → ℝ) :
    PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  c • hoeffdingCentered (periodicCappedDensityMeasure ρ)
    (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2))

lemma measurable_periodicLogMasterBand (τ δ a c : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    Measurable (periodicLogMasterBand τ δ a c ρ) :=
  ((stronglyMeasurable_hoeffdingCentered _ _
    ((periodicPositiveMellinBand_measurable (ι := ι) (periodicLogMellinExponent ι) τ δ a
      ).stronglyMeasurable.comp_measurable
      (measurable_fst.sub measurable_snd))).const_smul c).measurable

lemma memLp_infty_periodicLogMasterBand (τ δ a c : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδa : δ ≤ a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    MemLp (periodicLogMasterBand τ δ a c ρ) ∞
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) :=
  (periodicLogBand_centered_memLp_infty τ δ a hτ hδ hδa ha1
    (periodicCappedDensityMeasure ρ)).const_smul c

lemma periodicLogMasterBand_symmetric (τ δ a c : ℝ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (x y : PeriodicTorus ι) :
    periodicLogMasterBand τ δ a c ρ (x, y) = periodicLogMasterBand τ δ a c ρ (y, x) := by
  have h := DGRHS.centeredKernel_symmetric (periodicCappedDensityMeasure ρ)
    (fun x y => periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (x - y))
    (periodicLogBand_pair_symmetric τ δ a hτ hδ) x y
  exact congrArg (fun z : ℝ => c * z) h

lemma periodicLogMasterBand_canonical (τ δ a c : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδa : δ ≤ a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    ∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      ∫ y, periodicLogMasterBand τ δ a c ρ (x, y) ∂periodicCappedDensityMeasure ρ = 0 := by
  have h := DGRHS.integral_centeredKernel_right (periodicCappedDensityMeasure ρ)
    (fun x y => periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (x - y))
    (periodicLogBand_pair_proper τ δ a hτ hδ hδa ha1 (periodicCappedDensityMeasure ρ)).2.2
  filter_upwards [h] with x hx
  unfold periodicLogMasterBand
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  change c * (∫ y, DGRHS.centeredKernel (periodicCappedDensityMeasure ρ)
    (fun x y => periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (x - y)) x y
    ∂periodicCappedDensityMeasure ρ) = 0
  rw [hx, mul_zero]

lemma norm_periodicLogMasterBand_le (τ δ a c : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδa : δ ≤ a)
    (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (q : PeriodicTorus ι × PeriodicTorus ι) :
    ‖periodicLogMasterBand τ δ a c ρ q‖ ≤
      4 * |c| * (periodicLogBandConst ι * Real.log (a / δ)) := by
  unfold periodicLogMasterBand
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [norm_mul, Real.norm_eq_abs]
  calc
    _ ≤ |c| * (4 * (periodicLogBandConst ι * Real.log (a / δ))) :=
      mul_le_mul_of_nonneg_left
        (periodicLogBand_centered_norm_bound τ δ a hτ hδ hδa ha1 _ q) (abs_nonneg c)
    _ = _ := by ring

lemma essential_periodicLogMasterBand_le (τ δ a c : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδa : δ ≤ a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    (eLpNormEssSup (periodicLogMasterBand τ δ a c ρ)
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))).toReal ≤
      4 * |c| * (periodicLogBandConst ι * Real.log (a / δ)) := by
  have hK := periodicLogBandConst_pos (ι := ι)
  have hl := periodicLog_log_ratio_nonneg δ a hδ hδa
  have hC : 0 ≤ 4 * |c| * (periodicLogBandConst ι * Real.log (a / δ)) := by positivity
  have h := eLpNormEssSup_le_of_ae_bound
    (μ := (periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))
    (Eventually.of_forall (norm_periodicLogMasterBand_le τ δ a c hτ hδ hδa ha1 ρ))
  simpa only [ENNReal.toReal_ofReal hC] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

/-! ### Particle cap of the centered band (uniform in the number of particles) -/

/-- Pair form of the band integrand. -/
def periodicLogPositivePairIntegrand (τ : ℝ)
    (q : ℝ × (PeriodicTorus ι × PeriodicTorus ι)) : ℝ :=
  periodicPositiveMellinIntegrand (periodicLogMellinExponent ι) τ q.1 (q.2.1 - q.2.2)

lemma periodicLogPositivePairIntegrand_measurable (τ : ℝ) :
    Measurable (periodicLogPositivePairIntegrand (ι := ι) τ) :=
  (periodicPositiveMellinIntegrand_measurable (ι := ι) (periodicLogMellinExponent ι) τ).comp
    (show Measurable (fun q : ℝ × (PeriodicTorus ι × PeriodicTorus ι) =>
      (q.1, q.2.1 - q.2.2)) by fun_prop)

lemma periodicLogBand_centering_commutes (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (ha1 : a ≤ 1)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    Integrable (fun t => hoeffdingCentered μ
      (fun q => periodicLogPositivePairIntegrand τ (t, q)) p) (volume.restrict (Ioc δ a)) ∧
    hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2)) p =
      ∫ t : ℝ in Ioc δ a,
        hoeffdingCentered μ (fun q => periodicLogPositivePairIntegrand τ (t, q)) p := by
  let ν : Measure ℝ := volume.restrict (Ioc δ a)
  let B : ℝ → ℝ := fun t => periodicLogBandConst ι * t⁻¹
  have hm := (periodicLogPositivePairIntegrand_measurable (ι := ι) τ).stronglyMeasurable
  have hi : Integrable B ν := periodicLog_inv_integrableOn _ δ a hδ
  have hb : ∀ᵐ t ∂ν, ∀ q : PeriodicTorus ι × PeriodicTorus ι,
      ‖periodicLogPositivePairIntegrand τ (t, q)‖ ≤ B t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro q
    exact periodicLogBandIntegrand_small_norm_bound τ t (hδ.trans ht.1) (ht.2.trans ha1) hτ
      (q.1 - q.2)
  exact ⟨integrable_parameter_hoeffdingCentered_of_envelope ν μ _ hm B hi hb p,
    hoeffdingCentered_integral_parameter_of_envelope ν μ _ hm B hi hb p⟩

/-- The constant removed from the full heat is canceled after each actual row and pair integral is
proper; pointwise at every spatial pair. -/
lemma periodicLogPositivePairIntegrand_centered_eq_tail (τ t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1)
    (hτ : 0 ≤ τ) (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (p : PeriodicTorus ι × PeriodicTorus ι) :
    hoeffdingCentered μ (fun q => periodicLogPositivePairIntegrand τ (t, q)) p =
      hoeffdingCentered μ (fun q => periodicLogPairTailIntegrand τ (t, q)) p := by
  let H : PeriodicTorus ι × PeriodicTorus ι → ℝ :=
    fun q => periodicLogPositivePairIntegrand τ (t, q)
  let c : ℝ := t ^ periodicLogMellinExponent ι
  have hm : StronglyMeasurable H :=
    (periodicLogPositivePairIntegrand_measurable τ).stronglyMeasurable.comp_measurable
      (show Measurable (fun q : PeriodicTorus ι × PeriodicTorus ι => (t, q)) by fun_prop)
  have hb (q : PeriodicTorus ι × PeriodicTorus ι) : ‖H q‖ ≤ periodicLogBandConst ι * t⁻¹ :=
    periodicLogBandIntegrand_small_norm_bound τ t ht ht1 hτ (q.1 - q.2)
  have he : (fun q => H q - c) = (fun q => periodicLogPairTailIntegrand τ (t, q)) := by
    funext q
    dsimp [H, c, periodicLogPositivePairIntegrand, periodicPositiveMellinIntegrand,
      periodicLogPairTailIntegrand]
    ring
  have hc := hoeffdingCentered_sub_const_of_pointwise_bound μ H hm _ hb c p
  rw [he] at hc
  exact hc.symm

lemma periodicLogBand_particle_cap (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ) (hδa : δ ≤ a)
    (ha1 : a ≤ 1) (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    iidNegativeStatistic N (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2))) x ≤
      2 * (periodicLogBandConst ι * Real.log (a / δ)) := by
  let ν : Measure ℝ := volume.restrict (Ioc δ a)
  let H := fun (t : ℝ) (p : PeriodicTorus ι × PeriodicTorus ι) =>
    hoeffdingCentered μ (fun q => periodicLogPositivePairIntegrand τ (t, q)) p
  have hi (p : PeriodicTorus ι × PeriodicTorus ι) : Integrable (fun t => H t p) ν :=
    (periodicLogBand_centering_commutes τ δ a hτ hδ ha1 μ p).1
  have he : hoeffdingCentered μ (fun q : PeriodicTorus ι × PeriodicTorus ι =>
      periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2)) =
      fun q => ∫ t, H t q ∂ν := by
    funext q
    exact (periodicLogBand_centering_commutes τ δ a hτ hδ ha1 μ q).2
  rw [he, ← integral_iidNegativeStatistic_parameter ν H hi N x]
  have heIoc : Integrable (fun t : ℝ => 2 * periodicLogBandConst ι * t⁻¹) ν :=
    periodicLog_inv_integrableOn _ δ a hδ
  calc
    _ ≤ ∫ t, 2 * periodicLogBandConst ι * t⁻¹ ∂ν := by
      apply integral_mono_ae (integrable_iidNegativeStatistic_parameter ν H hi N x) heIoc
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hEq : H t = hoeffdingCentered μ (fun q => periodicLogPairTailIntegrand τ (t, q)) := by
        funext q
        exact periodicLogPositivePairIntegrand_centered_eq_tail τ t
          (hδ.trans ht.1) (ht.2.trans ha1) hτ μ q
      rw [hEq]
      refine (periodicLogTailIntegrand_particle_cap τ t (hδ.trans ht.1) hτ μ N hN x).trans ?_
      unfold periodicLogTailEnvelope
      rw [ite_eq_left (ht.2.trans ha1)]
      apply le_of_eq
      unfold periodicLogBandConst
      ring
    _ = _ := by
      rw [periodicLog_inv_integral _ δ a hδ hδa]
      ring

lemma periodicLogMasterBand_particle_cap (τ δ a c : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδa : δ ≤ a) (ha1 : a ≤ 1) (hc : 0 ≤ c) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (N : ℕ) (hN : 1 ≤ N) (x : Fin N → PeriodicTorus ι) :
    iidNegativeStatistic N (periodicLogMasterBand τ δ a c ρ) x ≤
      2 * c * (periodicLogBandConst ι * Real.log (a / δ)) := by
  unfold periodicLogMasterBand
  rw [physical_iidNegativeStatistic_const_smul]
  have h := mul_le_mul_of_nonneg_left
    (periodicLogBand_particle_cap τ δ a hτ hδ hδa ha1 (periodicCappedDensityMeasure ρ) N hN x) hc
  linarith

/-! ### `L^2` controls (smallness of the band for small upper time `a`) -/

/-- Upper-scale control, independent of the lower time and of the heat shift. -/
def periodicLogBandRowControl (a M : ℝ) (ι : Type*) [Fintype ι] : ℝ :=
  M * (periodicHeatDiagonalSmallConstant ι / (((Fintype.card ι : ℝ) / 4 - 0 / 2) ^ 2)) *
    a ^ ((Fintype.card ι : ℝ) / 2 - 0)

lemma periodicLogBandRowControl_nonneg (a M : ℝ) (ha : 0 ≤ a) (hM : 0 ≤ M) :
    0 ≤ periodicLogBandRowControl a M ι := by
  unfold periodicLogBandRowControl
  have hC := periodicHeatDiagonalSmallConstant_nonneg (ι := ι)
  have := Real.rpow_nonneg ha ((Fintype.card ι : ℝ) / 2 - 0)
  positivity

lemma periodicLogBand_memLp (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (ha : 0 < a) (ha1 : a ≤ 1) :
    MemLp (periodicPositiveMellinBand (ι := ι) (periodicLogMellinExponent ι) τ δ a) 2
      (periodicHaar ι) :=
  periodicPositiveMellinBand_memLp 0 τ δ a
    (by rw [mul_zero]; exact_mod_cast Fintype.card_pos) hτ hδ ha ha1

lemma periodicLogBand_sq_mass_bound (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (ha : 0 < a)
    (ha1 : a ≤ 1) :
    (∫ x : PeriodicTorus ι,
      periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a x ^ 2 ∂periodicHaar ι) ≤
      periodicHeatDiagonalSmallConstant ι / (((Fintype.card ι : ℝ) / 4 - 0 / 2) ^ 2) *
        a ^ ((Fintype.card ι : ℝ) / 2 - 0) :=
  periodicPositiveMellinBand_sq_mass_bound 0 τ δ a
    (by rw [mul_zero]; exact_mod_cast Fintype.card_pos) hτ hδ ha ha1

lemma periodicLogBand_centered_memLp (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ) (ha : 0 < a)
    (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun p : PeriodicTorus ι × PeriodicTorus ι =>
        periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (p.1 - p.2))) 2
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) :=
  memLp_hoeffdingCentered _ _
    ((periodicPositiveMellinBand_measurable (ι := ι) (periodicLogMellinExponent ι) τ δ a
      ).stronglyMeasurable.comp_measurable (measurable_fst.sub measurable_snd))
    (periodicPair_memLp_of_density_cap ρ M hρ _
      (periodicLogBand_memLp τ δ a hτ hδ ha ha1))

lemma periodicLogBand_centered_square_controls (τ δ a : ℝ) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      (∫ y, hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun p : PeriodicTorus ι × PeriodicTorus ι =>
          periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (p.1 - p.2))
          (x, y) ^ 2 ∂periodicCappedDensityMeasure ρ) ≤
        16 * periodicLogBandRowControl a M ι) ∧
    (∫ p, hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a (q.1 - q.2)) p ^ 2
        ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ≤
      16 * periodicLogBandRowControl a M ι := by
  have h := periodicCenteredPair_row_and_joint_sq_controls ρ M hM hρ
    (periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a)
    (periodicPositiveMellinBand_measurable _ τ δ a).stronglyMeasurable
    (periodicLogBand_memLp τ δ a hτ hδ ha ha1)
  have hb : M * (∫ z, periodicPositiveMellinBand (periodicLogMellinExponent ι) τ δ a z ^ 2
      ∂periodicHaar ι) ≤ periodicLogBandRowControl a M ι := by
    simpa only [periodicLogBandRowControl, mul_assoc] using
      mul_le_mul_of_nonneg_left (periodicLogBand_sq_mass_bound τ δ a hτ hδ ha ha1) hM
  constructor
  · filter_upwards [h.1] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
  · exact h.2.trans (mul_le_mul_of_nonneg_left hb (by norm_num))

lemma exists_periodicLogBand_small_scale (c M ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      16 * c ^ 2 * periodicLogBandRowControl a M ι < ε ∧
      4 * |c| * Real.sqrt (periodicLogBandRowControl a M ι) < ε := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hp : 0 < (Fintype.card ι : ℝ) / 2 - 0 := by linarith
  have ht : Tendsto (fun a : ℝ => periodicLogBandRowControl a M ι) (𝓝[>] 0) (𝓝 0) := by
    unfold periodicLogBandRowControl
    have hr := (tendsto_id : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝[>] 0)).mono_right
      nhdsWithin_le_nhds
    simpa only [mul_zero, id_eq] using (hr.rpow_const_nhds_zero hp).const_mul
      (M * (periodicHeatDiagonalSmallConstant ι / (((Fintype.card ι : ℝ) / 4 - 0 / 2) ^ 2)))
  have htr : Tendsto (fun a => 16 * c ^ 2 * periodicLogBandRowControl a M ι)
      (𝓝[>] 0) (𝓝 0) := by simpa only [mul_zero] using ht.const_mul (16 * c ^ 2)
  have hto : Tendsto (fun a => 4 * |c| * Real.sqrt (periodicLogBandRowControl a M ι))
      (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, Function.comp_def] using
      ((Real.continuous_sqrt.tendsto 0).comp ht).const_mul (4 * |c|)
  have he := (htr.eventually (gt_mem_nhds hε)).and (hto.eventually (gt_mem_nhds hε))
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  have hrange : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a < 1 :=
    hpos.and (nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨a, hb, hpos, hlt⟩ := (he.and hrange).exists
  exact ⟨a, hpos, hlt, hb.1, hb.2⟩

lemma periodicLogMasterBand_norm_fields (τ δ a β : ℝ) (hτ : 0 ≤ τ) (hδ : 0 < δ)
    (hδa : δ ≤ a) (ha : 0 < a) (ha1 : a ≤ 1) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hrow : 16 * (2 * β) ^ 2 * periodicLogBandRowControl a M ι ≤ 1 / glzUniversalTailConstant)
    (hop : 4 * |2 * β| * Real.sqrt (periodicLogBandRowControl a M ι) ≤
      1 / glzUniversalTailConstant) :
    (∀ᵐ x ∂periodicCappedDensityMeasure ρ,
      (∫ y, (periodicLogMasterBand τ δ a (2 * β) ρ (x, y)) ^ 2
        ∂periodicCappedDensityMeasure ρ) ≤ 1 / glzUniversalTailConstant) ∧
    ((∫ q, (periodicLogMasterBand τ δ a (2 * β) ρ q) ^ 2
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) ≤
        1 / glzUniversalTailConstant) ∧
    ‖DGRHS.Kernel.integralOperator (periodicLogMasterBand τ δ a (2 * β) ρ)
      ((memLp_infty_periodicLogMasterBand τ δ a (2 * β) hτ hδ hδa ha1 ρ).mono_exponent
        (show (2 : ℝ≥0∞) ≤ ∞ from le_top))‖ ≤ 1 / glzUniversalTailConstant := by
  let μ := periodicCappedDensityMeasure ρ
  obtain ⟨hr0, hj0⟩ := periodicLogBand_centered_square_controls τ δ a hτ hδ.le ha ha1 ρ M hM hρ
  have hK : 0 ≤ periodicLogBandRowControl a M ι := periodicLogBandRowControl_nonneg a M ha.le hM
  have hr : ∀ᵐ x ∂μ, (∫ y, (periodicLogMasterBand τ δ a (2 * β) ρ (x, y)) ^ 2 ∂μ) ≤
      16 * (2 * β) ^ 2 * periodicLogBandRowControl a M ι := by
    filter_upwards [hr0] with x hx
    unfold periodicLogMasterBand
    simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg (2 * β))]
  have hj : (∫ q, (periodicLogMasterBand τ δ a (2 * β) ρ q) ^ 2 ∂μ.prod μ) ≤
      16 * (2 * β) ^ 2 * periodicLogBandRowControl a M ι := by
    unfold periodicLogMasterBand
    simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [integral_const_mul]
    nlinarith [mul_le_mul_of_nonneg_left hj0 (sq_nonneg (2 * β))]
  refine ⟨?_, hj.trans hrow, ?_⟩
  · filter_upwards [hr] with x hx
    exact hx.trans hrow
  · let W := periodicLogMasterBand τ δ a (2 * β) ρ
    have hW : MemLp W 2 (μ.prod μ) :=
      (periodicLogBand_centered_memLp τ δ a hτ hδ.le ha ha1 ρ M hρ).const_smul (2 * β)
    have hb : ‖hW.toLp W‖ ^ 2 ≤ 16 * (2 * β) ^ 2 * periodicLogBandRowControl a M ι := by
      rw [DGRHS.Kernel.norm_toLp_sq]
      exact hj
    have hright : 0 ≤ 4 * |2 * β| * Real.sqrt (periodicLogBandRowControl a M ι) := by positivity
    have hsquare : (4 * |2 * β| * Real.sqrt (periodicLogBandRowControl a M ι)) ^ 2 =
        16 * (2 * β) ^ 2 * periodicLogBandRowControl a M ι := by
      rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hK]
      norm_num
    have hn : ‖hW.toLp W‖ ≤ 4 * |2 * β| * Real.sqrt (periodicLogBandRowControl a M ι) := by
      nlinarith [norm_nonneg (hW.toLp W)]
    exact ((DGRHS.Kernel.norm_integralOperator_le W hW).trans hn).trans hop

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogBandConst_pos
#print axioms DGRHS.Periodic.periodicLogBandIntegrand_small_norm_bound
#print axioms DGRHS.Periodic.periodicLogBand_norm_bound
#print axioms DGRHS.Periodic.periodicLogBand_pair_proper
#print axioms DGRHS.Periodic.periodicLogBand_centered_memLp_infty
#print axioms DGRHS.Periodic.measurable_periodicLogMasterBand
#print axioms DGRHS.Periodic.memLp_infty_periodicLogMasterBand
#print axioms DGRHS.Periodic.periodicLogMasterBand_symmetric
#print axioms DGRHS.Periodic.periodicLogMasterBand_canonical
#print axioms DGRHS.Periodic.essential_periodicLogMasterBand_le
#print axioms DGRHS.Periodic.periodicLogBand_centering_commutes
#print axioms DGRHS.Periodic.periodicLogBand_particle_cap
#print axioms DGRHS.Periodic.periodicLogMasterBand_particle_cap
#print axioms DGRHS.Periodic.periodicLogBand_memLp
#print axioms DGRHS.Periodic.periodicLogBand_centered_square_controls
#print axioms DGRHS.Periodic.exists_periodicLogBand_small_scale
#print axioms DGRHS.Periodic.periodicLogMasterBand_norm_fields
