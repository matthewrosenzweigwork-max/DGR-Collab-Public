import DGRHS.Gaussian.PeriodicLogMellinSplit
import DGRHS.Gaussian.GaussianLogAdaptiveBounds
import DGRHS.Gaussian.GaussianRieszCutoffMoment
import DGRHS.Concentration.MasterExponential

/-!
Packet P9e, unit 2 (part 4) and the master layer-cake input of unit 3: the torus LOG
`MasterCutoffData` (periodic analogue of `gaussianLogSourceMasterData`) and the uniform exponential
moment of the (heat-shifted) torus LOG cutoff family, uniform in the heat shift `tau >= 0`
(including the exact kernel `tau = 0`) and in `n >= 1`
(torus form of `gaussianLogSource_finiteIR_uniform_exponential`; no infrared parameter `T` is
needed on the torus).

The adaptive scale is the Euclidean logarithmic scale `gaussianLogAdaptiveScale` (reused as a
scalar function), with heat time = square of the length scale; the band cap is logarithmic,
`1 + 4 b K log(a/T_u)`, and the size envelope is `n^(2/3)` exactly as in the Euclidean LOG chain.
Everything is at Mellin level with an arbitrary coupling `b >= 0`; the normalization constant of the
kernel is absorbed into `b` in `PeriodicLogPartitionUniform`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicLogGreen_measurable (τ : ℝ) :
    Measurable (periodicUnshiftedMellinHeatGreen (ι := ι) (periodicLogMellinExponent ι) τ) := by
  unfold periodicUnshiftedMellinHeatGreen
  have hm : Measurable (fun q : ℝ × PeriodicTorus ι => (q.1 + τ, q.2)) := by fun_prop
  have hh := (periodicGaussianHeat_joint_measurable (ι := ι)).comp hm
  have hf : Measurable (fun q : ℝ × PeriodicTorus ι =>
      q.1 ^ (periodicLogMellinExponent ι) *
        ((periodicGaussianHeat (q.1 + τ) q.2).re - 1)) :=
    (by fun_prop : Measurable (fun q : ℝ × PeriodicTorus ι =>
      q.1 ^ (periodicLogMellinExponent ι))).mul
      ((Complex.continuous_re.measurable.comp hh).sub measurable_const)
  exact (hf.stronglyMeasurable.integral_prod_left'
    (μ := (volume : Measure ℝ).restrict (Set.Ioi 0))).measurable

/-- Adaptive lower heat time: the square of the logarithmic adaptive length scale (cap `sqrt a`). -/
def periodicLogAdaptiveTime (a A b : ℝ) (n : ℕ) (u : ℝ) (ι : Type u) [Fintype ι] : ℝ :=
  (gaussianLogAdaptiveScale (Real.sqrt a) A b (n : ℝ) u (Fintype.card ι : ℝ)) ^ 2

lemma periodicLogAdaptiveTime_pos_le (a A b u : ℝ) (n : ℕ) (ha : 0 < a) (hA : 0 < A)
    (hb : 0 ≤ b) (hu : 0 < u) :
    0 < periodicLogAdaptiveTime a A b n u ι ∧ periodicLogAdaptiveTime a A b n u ι ≤ a := by
  have h := gaussianLogAdaptiveScale_pos_le (Real.sqrt a) A b (n : ℝ) u (Fintype.card ι : ℝ)
    (Real.sqrt_pos.mpr ha) hA hb (Nat.cast_nonneg n) hu
  refine ⟨pow_pos h.1 2, ?_⟩
  calc _ ≤ (Real.sqrt a) ^ 2 := pow_le_pow_left₀ h.1.le h.2 2
    _ = a := Real.sq_sqrt ha.le

lemma periodicLog_sq_rpow_card (l : ℝ) (hl : 0 < l) :
    (l ^ 2) ^ (periodicLogMellinExponent ι + 1) = l ^ (Fintype.card ι : ℝ) := by
  rw [periodicLogMellinExponent_add_one, ← Real.rpow_natCast, ← Real.rpow_mul hl.le]
  congr 1
  push_cast
  ring

/-- Coefficient of the near-field term: `M/(d/2)`. -/
def periodicLogNearConst (M : ℝ) (ι : Type u) [Fintype ι] : ℝ := M / ((Fintype.card ι : ℝ) / 2)

lemma periodicLogNearConst_nonneg (M : ℝ) (hM : 0 ≤ M) : 0 ≤ periodicLogNearConst M ι := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  unfold periodicLogNearConst
  positivity

lemma periodicLogAdaptive_near_le (a A b u M : ℝ) (n : ℕ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : 0 < A) (hb : 0 ≤ b) (hu : 0 < u) (hM : 0 ≤ M)
    (hAC : 8 * periodicLogNearConst M ι ≤ A) :
    b * (n : ℝ) * (M * (periodicLogAdaptiveTime a A b n u ι ^ (periodicLogMellinExponent ι + 1) /
      (periodicLogMellinExponent ι + 1))) ≤ u / 8 := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hα := gaussianLogAdaptiveScale_pos_le (Real.sqrt a) A b (n : ℝ) u (Fintype.card ι : ℝ)
    (Real.sqrt_pos.mpr ha) hA hb (Nat.cast_nonneg n) hu
  have h := gaussianLogAdaptiveScale_near_error_le (Real.sqrt a) A b (n : ℝ) u
    (Fintype.card ι : ℝ) (periodicLogNearConst M ι) (Real.sqrt_pos.mpr ha) hA hb
    (Nat.cast_nonneg n) hu hd (periodicLogNearConst_nonneg M hM) hAC
  have hT : periodicLogAdaptiveTime a A b n u ι ^ (periodicLogMellinExponent ι + 1) =
      (gaussianLogAdaptiveScale (Real.sqrt a) A b (n : ℝ) u (Fintype.card ι : ℝ)) ^
        (Fintype.card ι : ℝ) := by
    unfold periodicLogAdaptiveTime
    exact periodicLog_sq_rpow_card _ hα.1
  rw [hT, periodicLogMellinExponent_add_one]
  unfold periodicLogNearConst at h
  calc _ = b * (n : ℝ) * (M / ((Fintype.card ι : ℝ) / 2)) *
        (gaussianLogAdaptiveScale (Real.sqrt a) A b (n : ℝ) u (Fintype.card ι : ℝ)) ^
          (Fintype.card ι : ℝ) := by ring
    _ ≤ _ := h

/-- Logarithmic band mass at the adaptive time. -/
lemma periodicLogAdaptive_log_mass_le (a A b u : ℝ) (n : ℕ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : 0 < A) (hb : 0 ≤ b) (hn : 1 ≤ n) (hu : 0 < u) :
    Real.log (a / periodicLogAdaptiveTime a A b n u ι) ≤
      4 / (Fintype.card ι : ℝ) * (A * (1 + b)) ^ (1 / 2 : ℝ) * ((n : ℝ) / u) ^ (1 / 2 : ℝ) := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hα := gaussianLogAdaptiveScale_pos_le (Real.sqrt a) A b (n : ℝ) u (Fintype.card ι : ℝ)
    (Real.sqrt_pos.mpr ha) hA hb (Nat.cast_nonneg n) hu
  have hs1 : Real.sqrt a ≤ 1 := by
    rw [Real.sqrt_le_one]; exact ha1
  have h := gaussianLogAdaptiveScale_log_mass_le (Real.sqrt a) A b (n : ℝ) u
    (Fintype.card ι : ℝ) (Real.sqrt_pos.mpr ha) hs1 hA hb hn' hu hd
  have he : a / periodicLogAdaptiveTime a A b n u ι =
      (Real.sqrt a / gaussianLogAdaptiveScale (Real.sqrt a) A b (n : ℝ) u
        (Fintype.card ι : ℝ)) ^ 2 := by
    unfold periodicLogAdaptiveTime
    rw [div_pow, Real.sq_sqrt ha.le]
  rw [he, Real.log_pow]
  have h2 : 4 / (Fintype.card ι : ℝ) * (A * (1 + b)) ^ (1 / 2 : ℝ) * ((n : ℝ) / u) ^ (1 / 2 : ℝ) =
      2 * (2 / (Fintype.card ι : ℝ) * (A * (1 + b)) ^ (1 / 2 : ℝ) *
        ((n : ℝ) / u) ^ (1 / 2 : ℝ)) := by ring
  rw [h2]
  push_cast
  linarith

def periodicLogAdaptiveBand (τ a b A : ℝ) (n : ℕ) (u : ℝ) (ρ : PeriodicTorus ι → ℝ) :
    PeriodicTorus ι × PeriodicTorus ι → ℝ :=
  periodicLogMasterBand τ (periodicLogAdaptiveTime a A b n u ι) a (2 * b) ρ

def periodicLogAdaptiveCap (a b A : ℝ) (n : ℕ) (u : ℝ) (ι : Type u) [Fintype ι] : ℝ :=
  1 + 4 * b * (periodicLogBandConst ι * Real.log (a / periodicLogAdaptiveTime a A b n u ι))

/-- Size constant `C_1 = 32 b K / d * (A (1+b))^(1/2)`. -/
def periodicLogAdaptiveC1 (A b : ℝ) (ι : Type u) [Fintype ι] : ℝ :=
  32 * b * periodicLogBandConst ι / (Fintype.card ι : ℝ) * (A * (1 + b)) ^ (1 / 2 : ℝ)

lemma periodicLogAdaptiveC1_nonneg (A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) :
    0 ≤ periodicLogAdaptiveC1 A b ι := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hK := periodicLogBandConst_pos (ι := ι)
  unfold periodicLogAdaptiveC1
  positivity

lemma periodicLogAdaptive_cap_ess_bounds (τ a b A : ℝ) (hτ : 0 ≤ τ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : 0 < A) (hb : 0 ≤ b) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (n : ℕ) (hn : 1 ≤ n) (u : ℝ)
    (hu : 1 ≤ u) :
    0 < periodicLogAdaptiveCap a b A n u ι ∧
      periodicLogAdaptiveCap a b A n u ι ≤
        1 + periodicLogAdaptiveC1 A b ι * ((n : ℝ) / u) ^ (1 / 2 : ℝ) ∧
      (eLpNormEssSup (periodicLogAdaptiveBand τ a b A n u ρ)
        ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))).toReal ≤
        1 + periodicLogAdaptiveC1 A b ι * ((n : ℝ) / u) ^ (1 / 2 : ℝ) := by
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have hK := periodicLogBandConst_pos (ι := ι)
  have hu0 : 0 < u := by linarith
  have hT := periodicLogAdaptiveTime_pos_le (ι := ι) a A b u n ha hA hb hu0
  have hl0 := periodicLog_log_ratio_nonneg _ a hT.1 hT.2
  have hl := periodicLogAdaptive_log_mass_le (ι := ι) a A b u n ha ha1 hA hb hn hu0
  have hR : 0 ≤ (A * (1 + b)) ^ (1 / 2 : ℝ) * ((n : ℝ) / u) ^ (1 / 2 : ℝ) := by positivity
  have hBK : 0 ≤ b * periodicLogBandConst ι := by positivity
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = (b * periodicLogBandConst ι) / (Fintype.card ι : ℝ) *
      ((A * (1 + b)) ^ (1 / 2 : ℝ) * ((n : ℝ) / u) ^ (1 / 2 : ℝ)) := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZ]; positivity
  have hC1 : periodicLogAdaptiveC1 A b ι * ((n : ℝ) / u) ^ (1 / 2 : ℝ) = 32 * Z := by
    rw [hZ]; unfold periodicLogAdaptiveC1; ring
  have hbound : (b * periodicLogBandConst ι) *
      Real.log (a / periodicLogAdaptiveTime a A b n u ι) ≤ 4 * Z := by
    have := mul_le_mul_of_nonneg_left hl hBK
    calc _ ≤ _ := this
      _ = 4 * Z := by rw [hZ]; ring
  have hess := essential_periodicLogMasterBand_le τ (periodicLogAdaptiveTime a A b n u ι) a (2 * b)
    hτ hT.1 hT.2 ha1 ρ
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 * b)] at hess
  have e1 : 4 * b * (periodicLogBandConst ι *
      Real.log (a / periodicLogAdaptiveTime a A b n u ι)) =
      4 * ((b * periodicLogBandConst ι) * Real.log (a / periodicLogAdaptiveTime a A b n u ι)) := by
    ring
  have e2 : 4 * (2 * b) * (periodicLogBandConst ι *
      Real.log (a / periodicLogAdaptiveTime a A b n u ι)) =
      8 * ((b * periodicLogBandConst ι) * Real.log (a / periodicLogAdaptiveTime a A b n u ι)) := by
    ring
  refine ⟨?_, ?_, ?_⟩
  · unfold periodicLogAdaptiveCap
    have : 0 ≤ 4 * b * (periodicLogBandConst ι *
        Real.log (a / periodicLogAdaptiveTime a A b n u ι)) := by positivity
    linarith
  · unfold periodicLogAdaptiveCap
    rw [hC1]
    linarith [hbound, e1, hZ0]
  · unfold periodicLogAdaptiveBand
    rw [hC1]
    linarith [hbound, e2, hess, hZ0]

lemma periodicLogAdaptive_size_bound (τ a b A u₀ : ℝ) (hτ : 0 ≤ τ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hA : 0 < A) (hb : 0 ≤ b) (hu₀ : 1 ≤ u₀) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (n : ℕ) (hn : 1 ≤ n) :
    BddAbove (masterCutoffValues (periodicCappedDensityMeasure ρ)
      (fun u => periodicLogAdaptiveBand τ a b A n u ρ)
      (fun u => periodicLogAdaptiveCap a b A n u ι) u₀) ∧
    masterCutoffSize (periodicCappedDensityMeasure ρ)
      (fun u => periodicLogAdaptiveBand τ a b A n u ρ)
      (fun u => periodicLogAdaptiveCap a b A n u ι) u₀ ≤
      (2 + periodicLogAdaptiveC1 A b ι) ^ 2 * (n : ℝ) ^ (2 / 3 : ℝ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h := masterCutoffSize_le_adaptive_power (periodicCappedDensityMeasure ρ)
    (fun u => periodicLogAdaptiveBand τ a b A n u ρ)
    (fun u => periodicLogAdaptiveCap a b A n u ι) (n : ℝ) u₀ (1 / 2 : ℝ) 1
    (periodicLogAdaptiveC1 A b ι) hn' hu₀ (by norm_num) (by norm_num) (by norm_num)
    (periodicLogAdaptiveC1_nonneg A b hA hb)
    (fun u hu => (periodicLogAdaptive_cap_ess_bounds τ a b A hτ ha ha1 hA hb ρ n hn u
      (hu₀.trans hu)).2.1)
    (fun u hu => (periodicLogAdaptive_cap_ess_bounds τ a b A hτ ha ha1 hA hb ρ n hn u
      (hu₀.trans hu)).2.2)
  norm_num only at h
  exact h

/-- The torus LOG master data: the periodic analogue of `gaussianLogSourceMasterData`. -/
def periodicLogMasterCutoffData (τ a b A u₀ : ℝ) (hτ : 0 ≤ τ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hb : 0 ≤ b) (hA : 0 < A) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (n : ℕ) (hn : 1 ≤ n)
    (hAC : 8 * periodicLogNearConst M ι ≤ A) (hu₀ : 1 ≤ u₀)
    (hlow : 4 * (b * (2 * periodicLogTailConst ι a)) ≤ u₀)
    (hrow : 16 * (2 * b) ^ 2 * periodicLogBandRowControl a M ι ≤ 1 / glzUniversalTailConstant)
    (hop : 4 * |2 * b| * Real.sqrt (periodicLogBandRowControl a M ι) ≤
      1 / glzUniversalTailConstant) :
    MasterCutoffData (periodicCappedDensityMeasure ρ) n
      (fun ω => b * iidNegativeStatistic n (hoeffdingCentered (periodicCappedDensityMeasure ρ)
        (fun q : PeriodicTorus ι × PeriodicTorus ι =>
          periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2))) ω)
      u₀ := by
  have hT (u : ℝ) (hu : u₀ ≤ u) :=
    periodicLogAdaptiveTime_pos_le (ι := ι) a A b u n ha hA hb (by linarith)
  have hsize := periodicLogAdaptive_size_bound τ a b A u₀ hτ ha ha1 hA hb hu₀ ρ n hn
  have hcap (u : ℝ) (hu : u₀ ≤ u) :=
    periodicLogAdaptive_cap_ess_bounds τ a b A hτ ha ha1 hA hb ρ n hn u (hu₀.trans hu)
  refine { kernel := fun u => periodicLogAdaptiveBand τ a b A n u ρ
           cap := fun u => periodicLogAdaptiveCap a b A n u ι
           measurable := ?_
           memLp := ?_
           symmetric := ?_
           canonical := ?_
           cap_pos := fun u hu => (hcap u hu).1
           compare := ?_
           capped := ?_
           row := ?_
           joint := ?_
           operator := ?_
           size_finite := hsize.1 }
  · intro u hu
    exact measurable_periodicLogMasterBand _ _ _ _ ρ
  · intro u hu
    exact memLp_infty_periodicLogMasterBand _ _ _ _ hτ (hT u hu).1 (hT u hu).2 ha1 ρ
  · intro u hu x y
    exact periodicLogMasterBand_symmetric _ _ _ _ hτ (hT u hu).1.le ρ x y
  · intro u hu
    exact periodicLogMasterBand_canonical _ _ _ _ hτ (hT u hu).1 (hT u hu).2 ha1 ρ
  · intro u hu
    have hu0 : 0 < u := by linarith
    have hnear := periodicLogAdaptive_near_le (ι := ι) a A b u M n ha ha1 hA hb hu0 hM hAC
    have htail : b * (2 * periodicLogTailConst ι a) ≤ u / 4 := by linarith
    filter_upwards [periodicLogGreen_particle_comparison τ
      (periodicLogAdaptiveTime a A b n u ι) a b hτ (hT u hu).1 (hT u hu).2 ha1 hb ρ M hM hρ n hn]
      with ω hω
    intro hx
    unfold periodicLogAdaptiveBand periodicLogMasterBand
    rw [physical_iidNegativeStatistic_const_smul]
    nlinarith only [hω, hx, hnear, htail, hu0]
  · intro u hu
    apply Filter.Eventually.of_forall
    intro ω
    have hc := periodicLogMasterBand_particle_cap τ (periodicLogAdaptiveTime a A b n u ι) a (2 * b)
      hτ (hT u hu).1 (hT u hu).2 ha1 (by linarith : 0 ≤ 2 * b) ρ n hn ω
    change iidNegativeStatistic n (periodicLogMasterBand τ (periodicLogAdaptiveTime a A b n u ι) a
      (2 * b) ρ) ω ≤ 1 + 4 * b * (periodicLogBandConst ι *
        Real.log (a / periodicLogAdaptiveTime a A b n u ι))
    nlinarith only [hc]
  · intro u hu
    exact (periodicLogMasterBand_norm_fields τ _ a b hτ (hT u hu).1 (hT u hu).2 ha ha1 ρ M hM hρ
      hrow hop).1
  · intro u hu
    exact (periodicLogMasterBand_norm_fields τ _ a b hτ (hT u hu).1 (hT u hu).2 ha ha1 ρ M hM hρ
      hrow hop).2.1
  · intro u hu
    exact (periodicLogMasterBand_norm_fields τ _ a b hτ (hT u hu).1 (hT u hu).2 ha ha1 ρ M hM hρ
      hrow hop).2.2

lemma measurable_periodicLogCutoff_exponent (τ b : ℝ)
    (μ : Measure (PeriodicTorus ι)) [IsProbabilityMeasure μ] (n : ℕ) :
    Measurable (fun ω => b * iidNegativeStatistic n (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2))) ω) :=
  (measurable_physical_iidNegativeStatistic n _
    (stronglyMeasurable_hoeffdingCentered μ _
      ((periodicLogGreen_measurable (ι := ι) τ).stronglyMeasurable.comp_measurable
        (measurable_fst.sub measurable_snd))).measurable).const_mul b

/-- Uniform exponential moment of the torus LOG cutoff family at Mellin level, uniform in the heat
shift `tau >= 0` (including the exact kernel `tau = 0`) and in `n >= 1`
(torus form of `gaussianLogSource_finiteIR_uniform_exponential`; the coupling `b >= 0` is
arbitrary, the kernel normalization being absorbed in `b`). -/
theorem periodicLogMellinCutoff_uniform_exponential (b : ℝ) (hb : 0 ≤ b)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (b * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι =>
            periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (b * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι =>
            periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2))) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  let μ := periodicCappedDensityMeasure ρ
  have hL := glzUniversalTailConstant_pos
  obtain ⟨a, ha, ha1, hrow, hop⟩ := exists_periodicLogBand_small_scale (ι := ι) (2 * b) M
    (1 / glzUniversalTailConstant) (by positivity)
  have hTc := periodicLogTailConst_nonneg (ι := ι) a ha.le
  let A := 1 + 8 * periodicLogNearConst M ι
  let u₀ := 1 + 4 * (b * (2 * periodicLogTailConst ι a))
  have hAn := periodicLogNearConst_nonneg (ι := ι) M hM
  have hA : 0 < A := by dsimp [A]; linarith
  have hAC : 8 * periodicLogNearConst M ι ≤ A := by dsimp [A]; linarith
  have hT0 : 0 ≤ b * (2 * periodicLogTailConst ι a) := by positivity
  have hu₀ : 1 ≤ u₀ := by dsimp [u₀]; linarith
  have hlow : 4 * (b * (2 * periodicLogTailConst ι a)) ≤ u₀ := by dsimp [u₀]; linarith
  let I := {τ : ℝ // 0 ≤ τ}
  let X := fun (θ : I) (n : ℕ) (ω : Fin n → PeriodicTorus ι) =>
    b * iidNegativeStatistic n (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) θ.val (q.1 - q.2))) ω
  have hX (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      AEMeasurable (X θ n) (Measure.pi (fun _ : Fin n => μ)) :=
    (measurable_periodicLogCutoff_exponent θ.val b μ n).aemeasurable
  let data := fun (θ : I) (n : ℕ) (hn : 1 ≤ n) => periodicLogMasterCutoffData θ.val a b A u₀
    θ.property ha ha1.le hb hA ρ M hM hρ n hn hAC hu₀ hlow hrow.le hop.le
  let K := (2 + periodicLogAdaptiveC1 A b ι) ^ 2
  have hsize (θ : I) (n : ℕ) (hn : 1 ≤ n) :
      masterCutoffSize μ (data θ n hn).kernel (data θ n hn).cap u₀ ≤
        0 + K * (n : ℝ) ^ (2 / 3 : ℝ) := by
    have hz := (periodicLogAdaptive_size_bound θ.val a b A u₀ θ.property ha ha1.le hA hb hu₀ ρ n
      hn).2
    simpa only [data, periodicLogMasterCutoffData, K, zero_add] using hz
  obtain ⟨C, hC⟩ := master_uniform_sublinear_exponential_envelope μ X hX u₀ hu₀ data 0 K
    (2 / 3 : ℝ) (by norm_num) hsize
  exact ⟨C, fun τ hτ n hn => hC ⟨τ, hτ⟩ n hn⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogGreen_measurable
#print axioms DGRHS.Periodic.periodicLogAdaptiveTime_pos_le
#print axioms DGRHS.Periodic.periodicLog_sq_rpow_card
#print axioms DGRHS.Periodic.periodicLogAdaptive_near_le
#print axioms DGRHS.Periodic.periodicLogAdaptive_log_mass_le
#print axioms DGRHS.Periodic.periodicLogAdaptive_cap_ess_bounds
#print axioms DGRHS.Periodic.periodicLogAdaptive_size_bound
#print axioms DGRHS.Periodic.periodicLogMasterCutoffData
#print axioms DGRHS.Periodic.measurable_periodicLogCutoff_exponent
#print axioms DGRHS.Periodic.periodicLogMellinCutoff_uniform_exponential
