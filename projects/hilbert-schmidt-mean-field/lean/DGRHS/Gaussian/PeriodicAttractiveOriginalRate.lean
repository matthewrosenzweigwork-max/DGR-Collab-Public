import DGRHS.Gaussian.PeriodicAttractiveAffine
import DGRHS.Attractive.LogRateOptimization

/-!
Packet P11b, unit 2 (clause 2, final step): Theorem 2.6 (`thm:attractive-log-small-beta-partition`,
TeX 615-644), quantitative determinant assertion `eq:attQuantitativeDeterminantRate`, on the flat torus
(Remark 2.1), in the exact shape of `DGRHS.Attractive.exists_attractiveLog_original_quantitative_rate`.

The torus threshold `β_q(C_mom, ‖μ‖_∞, d)` is `periodicAttractiveQuantitativeThreshold`
(`≤ β_0/2` by construction, positive for `C_mom > 0`).  The Euclidean hypotheses that are automatic on the
torus for a bounded background density are not assumed: the singular pair-`L¹` hypothesis
`g_att ∈ L¹(μ⊗²)` and the exponential-integrability hypothesis `e^{4β h_μ^att} ∈ L¹(μ)` (the one-body
potential is bounded; TeX 646: "for a periodic uniform background ... the additional exponential-integrability
hypothesis ... is automatic").  The `_printed` restatement carries them as unused hypotheses.
The exponent `c ∈ (0, 1/4]` is explicit through `attractiveLogRatePower`; it is not the printed
`d/(2(2A+d))` (the printed power is unspecified, TeX 2953-2957).
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace DGRHS.Periodic
open DGRHS.Attractive DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The torus constant of the factorial moments `∫ |g|^p ≤ Cg^p p!` of the periodic LOG kernel. -/
def periodicLogMomentConstant (ι : Type u) [Fintype ι] [Nonempty ι] : ℝ :=
  Classical.choose (periodicLogKernel_abs_pow_bound (ι := ι))

lemma periodicLogMomentConstant_spec :
    0 < periodicLogMomentConstant ι ∧ ∀ p : ℕ, 1 ≤ p →
      Integrable (fun x => |periodicLogKernel (ι := ι) x| ^ p) (periodicHaar ι) ∧
      ∫ x, |periodicLogKernel (ι := ι) x| ^ p ∂periodicHaar ι ≤
        periodicLogMomentConstant ι ^ p * (p.factorial : ℝ) :=
  Classical.choose_spec (periodicLogKernel_abs_pow_bound (ι := ι))

/-- Uniform row constant of the centered heat-shifted LOG kernels for background densities `ρ ≤ M`. -/
def periodicRowConstant (ι : Type u) [Fintype ι] [Nonempty ι] (M : ℝ) : ℝ :=
  16 * (max 1 M * periodicLogMomentConstant ι)

lemma periodicRowConstant_pos (M : ℝ) : 0 < periodicRowConstant ι M := by
  have := (periodicLogMomentConstant_spec (ι := ι)).1
  unfold periodicRowConstant
  have h1 : 0 < max 1 M := lt_of_lt_of_le one_pos (le_max_left _ _)
  positivity

theorem periodicLogTruncCentered_rows_explicit (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (τ : ℝ) (hτ : 0 < τ) :
    RowFactorialMoments (periodicCappedDensityMeasure ρ)
      (periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ) (periodicRowConstant ι M) := by
  obtain ⟨hCg, hbd⟩ := periodicLogMomentConstant_spec (ι := ι)
  exact periodicLogTruncCentered_rows_core (periodicLogMomentConstant ι) hCg
    (fun τ hτ p hp => (periodicLogTruncKernel_integral_pow_le τ hτ p hp (hbd p hp).1).trans
      (hbd p hp).2) ρ M hM hρ τ hτ

/-- The torus quantitative threshold `β_q(C_mom, ‖μ‖_∞, d)` (≤ `β_0/2`). -/
def periodicAttractiveQuantitativeThreshold (ι : Type u) [Fintype ι] [Nonempty ι] (C M : ℝ) : ℝ :=
  min (attractiveBetaThreshold C / 2)
    ((attractiveMomentConstant * (periodicRowConstant ι M + 1))⁻¹)

lemma periodicAttractiveQuantitativeThreshold_pos (C M : ℝ) (hC : 0 < C) :
    0 < periodicAttractiveQuantitativeThreshold ι C M := by
  have hR := periodicRowConstant_pos (ι := ι) M
  exact lt_min (by have := attractiveBetaThreshold_pos hC; positivity)
    (inv_pos.mpr (by have := attractiveMomentConstant_pos; positivity))

lemma periodicAttractiveQuantitativeThreshold_half (C M : ℝ) :
    periodicAttractiveQuantitativeThreshold ι C M ≤ attractiveBetaThreshold C / 2 := min_le_left _ _

lemma periodicAttractiveQuantitativeThreshold_row_small (C M β : ℝ) (hβ : 0 ≤ β)
    (hsmall : β < periodicAttractiveQuantitativeThreshold ι C M) :
    β * (attractiveMomentConstant * periodicRowConstant ι M) < 1 := by
  have hR := periodicRowConstant_pos (ι := ι) M
  have hp : 0 < attractiveMomentConstant * (periodicRowConstant ι M + 1) := by
    have := attractiveMomentConstant_pos; positivity
  have hb := hsmall.trans_le (min_le_right _ _)
  rw [← one_div, lt_div_iff₀ hp] at hb
  have hle : attractiveMomentConstant * periodicRowConstant ι M ≤
      attractiveMomentConstant * (periodicRowConstant ι M + 1) := by
    nlinarith [attractiveMomentConstant_pos]
  exact (mul_le_mul_of_nonneg_left hle hβ).trans_lt hb

lemma periodic_integralOperator_neg {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (h : S × S → ℝ) (hh : MemLp h 2 (μ.prod μ)) :
    DGRHS.Kernel.integralOperator (-h) hh.neg = -DGRHS.Kernel.integralOperator h hh := by
  unfold DGRHS.Kernel.integralOperator
  rw [MemLp.toLp_neg, map_neg]

theorem exists_periodicAttractiveLog_original_quantitative_rate
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M C β : ℝ) (hM : 0 ≤ M) (hC : 0 < C) (hβ : 0 < β)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hrows : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal (|DGRHS.centeredKernel (periodicCappedDensityMeasure ρ)
        periodicAttractiveInteraction x y| ^ p) ∂periodicCappedDensityMeasure ρ) ≤
        ENNReal.ofReal (C ^ p * (p.factorial : ℝ)))
    (hsmall : β < periodicAttractiveQuantitativeThreshold ι C M) :
    let μ := periodicCappedDensityMeasure ρ
    let h := fun z : PeriodicTorus ι × PeriodicTorus ι =>
      DGRHS.centeredKernel μ periodicAttractiveInteraction z.1 z.2
    let I := DGRHS.interactionEnergy μ periodicAttractiveInteraction
    ∃ (hh : MemLp h 2 (μ.prod μ)) (κ : Type u) (eig : κ → ℝ)
      (b : HilbertBasis κ ℝ (Lp ℝ 2 μ)), Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ c ≤ 1 / 4 ∧ ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h
            (DGRHS.potential μ periodicAttractiveInteraction) I N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        periodicAttractiveLogPartition μ β N < ∞ ∧
        |(periodicAttractiveLogPartition μ β N).toReal -
          Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          K * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
  intro μ h I
  have hpair := periodicSingularAbsLog_density_finite ρ M hρ
  set R := periodicRowConstant ι M with hRdef
  have hRpos : 0 ≤ R := (periodicRowConstant_pos (ι := ι) M).le
  have hrowsτ : ∀ τ : ℝ, 0 < τ → RowFactorialMoments μ (periodicLogTruncCentered μ τ) R :=
    fun τ hτ => periodicLogTruncCentered_rows_explicit ρ M hM hρ τ hτ
  have hβ0 : β < attractiveBetaThreshold C / 2 :=
    hsmall.trans_le (periodicAttractiveQuantitativeThreshold_half C M)
  have hbase : β * (attractiveMomentConstant * C) < 1 :=
    (attractiveBetaThreshold_lt_iff hC).mp (by linarith [attractiveBetaThreshold_pos hC])
  have htwo : (2 * β) * (attractiveMomentConstant * C) < 1 :=
    (attractiveBetaThreshold_lt_iff hC).mp (by linarith)
  have hsmallR := periodicAttractiveQuantitativeThreshold_row_small C M β hβ.le hsmall
  obtain ⟨hhq, κ, eigq, b, hκ, hbq, hdetq, hlim, A, B, q', r, hA, hB, hq', hr, hRate⟩ :=
    exists_periodicAttractive_canonical_cutoff_rate ρ M hM hρ C R β hC.le hRpos hβ hrows hrowsτ
      hbase hsmallR
  have hq : periodicLogCentered μ = -h := periodicCentered_eq_neg_attractive μ
  have hneg : -periodicLogCentered μ = h := by rw [hq]; simp
  have hh : MemLp h 2 (μ.prod μ) := by
    have hn : MemLp (-periodicLogCentered μ) 2 (μ.prod μ) := hhq.neg
    rw [hneg] at hn
    exact hn
  have hop : DGRHS.Kernel.integralOperator h hh =
      -DGRHS.Kernel.integralOperator (periodicLogCentered μ) hhq := by
    simpa only [hneg] using periodic_integralOperator_neg μ (periodicLogCentered μ) hhq
  let eig := fun i => -eigq i
  have hb : ∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i := by
    intro i
    rw [hop]
    have hbi : DGRHS.Kernel.integralOperator (periodicLogCentered μ) hhq (b i) = eigq i • b i := hbq i
    change -(DGRHS.Kernel.integralOperator (periodicLogCentered μ) hhq (b i)) = (-eigq i) • b i
    rw [hbi]
    simp only [neg_smul]
  have heig : (fun i => β * eig i) = (fun i => -β * eigq i) := by
    funext i; dsimp [eig]; ring
  have hdet : 0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) := by rw [heig]; exact hdetq
  obtain ⟨D, hD, hAffine⟩ := periodicAttractiveLog_source_affine_comparison ρ M C β hM hC hβ hρ hrows htwo
  let W := Real.exp (β * I)
  let Ce := max (W * B) q' + 1
  let c := attractiveLogRatePower Ce r
  let K := (2 * (W * A) + Ce * Real.exp Ce + D) * (Real.exp 1 + 1) ^ c
  have hW : 0 < W := Real.exp_pos _
  have hCe : 0 < Ce := by
    dsimp [Ce]; have he := le_max_right (W * B) q'; linarith
  have hBce : W * B ≤ Ce := by
    dsimp [Ce]; have he := le_max_left (W * B) q'; linarith
  have hqce : q' ≤ Ce := by
    dsimp [Ce]; have he := le_max_right (W * B) q'; linarith
  obtain ⟨hc, hcquarter⟩ := attractiveLogRatePower_bounds Ce r hCe hr
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hstat (N : ℕ) (x : Fin N → PeriodicTorus ι) :
      DGRHS.CanonicalVariance.normalizedOffDiagonalSum (periodicLogCentered μ) x =
        -DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
    rw [hq]
    unfold DGRHS.CanonicalVariance.normalizedOffDiagonalSum DGRHS.CanonicalVariance.offDiagonalSum
    simp only [Pi.neg_apply, Finset.sum_neg_distrib, mul_neg]
  let Z := fun N => ∫ x : Fin N → PeriodicTorus ι, Real.exp
    (β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum (periodicLogCentered μ) x)
    ∂Measure.pi (fun _ : Fin N => μ)
  let z := (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -β * eigq i)))⁻¹
  have hZeq (N : ℕ) : DGRHS.Concentration.canonicalPartition μ β h N = Z N := by
    unfold DGRHS.Concentration.canonicalPartition Z
    congr 1
    funext x
    rw [hstat]
    congr 1
    ring
  refine ⟨hh, κ, eig, b, hκ, hb, hdet, K, c, hK, hc, hcquarter, ?_⟩
  intro N hN
  have hNr : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  let η := attractiveLogRateCutoff Ce (N : ℝ)
  obtain ⟨hη, hη1, hOpt⟩ := attractiveLogRateCutoff_bound (W * A) Ce D r (N : ℝ)
    (mul_nonneg hW.le hA) hCe hD hr hNr
  obtain ⟨hProper, hAff⟩ := hAffine N hN
  have hCan := (hRate η hη hη1 N hN).2
  have hmajor := power_cutoff_le_exponential_envelope (W * B) q' Ce η
    (mul_nonneg hW.le hB) hBce hqce hη hη1
  let S := ∫ x : Fin N → PeriodicTorus ι, Real.exp
    (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h
      (DGRHS.potential μ periodicAttractiveInteraction) I N x)
    ∂Measure.pi (fun _ : Fin N => μ)
  have hErr : |S - W * z| ≤ K * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
    rw [hZeq] at hAff
    have hDiff : |W * Z N - W * z| = W * |Z N - z| := by
      rw [← mul_sub, abs_mul, abs_of_pos hW]
    have hCan' : |Z N - z| ≤ 2 * A * η ^ r + B * η ^ (-q') / Real.sqrt (N : ℝ) := hCan
    calc
      _ ≤ |S - W * Z N| + |W * Z N - W * z| := abs_sub_le _ _ _
      _ ≤ D / Real.sqrt (N : ℝ) + W * (2 * A * η ^ r + B * η ^ (-q') / Real.sqrt (N : ℝ)) := by
        rw [hDiff]
        exact add_le_add hAff (mul_le_mul_of_nonneg_left hCan' hW.le)
      _ = 2 * (W * A) * η ^ r + (W * B) * η ^ (-q') / Real.sqrt (N : ℝ) + D / Real.sqrt (N : ℝ) := by
        ring
      _ ≤ 2 * (W * A) * η ^ r + Ce * Real.exp (Ce * (1 + Real.log (1 / η))) / Real.sqrt (N : ℝ) +
            D / Real.sqrt (N : ℝ) := by
        exact add_le_add (add_le_add le_rfl
          (div_le_div_of_nonneg_right hmajor (Real.sqrt_nonneg _))) le_rfl
      _ ≤ _ := hOpt
  have he : periodicAttractiveLogPartition μ β N = ENNReal.ofReal S := by
    unfold periodicAttractiveLogPartition
    rw [lintegral_congr_ae (periodicAttractiveSingularWeight_ae μ hpair β N)]
    exact (ofReal_integral_eq_lintegral_ofReal hProper
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm
  have hS : 0 ≤ S := integral_nonneg (fun _ => (Real.exp_pos _).le)
  refine ⟨hProper, by rw [he]; exact ENNReal.ofReal_lt_top, ?_⟩
  rw [he, ENNReal.toReal_ofReal hS, heig]
  exact hErr

/-- The same theorem with the two printed hypotheses (`g_att ∈ L¹(μ⊗²)` and
`e^{4β h_μ^att} ∈ L¹(μ)`) restated literally (unused; both are automatic on the torus). -/
theorem exists_periodicAttractiveLog_original_quantitative_rate_printed
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M C β : ℝ) (hM : 0 ≤ M) (hC : 0 < C) (hβ : 0 < β)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (_hpair : (∫⁻ z, periodicSingularAbsLog z ∂(periodicCappedDensityMeasure ρ).prod
      (periodicCappedDensityMeasure ρ)) < ∞)
    (hrows : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal (|DGRHS.centeredKernel (periodicCappedDensityMeasure ρ)
        periodicAttractiveInteraction x y| ^ p) ∂periodicCappedDensityMeasure ρ) ≤
        ENNReal.ofReal (C ^ p * (p.factorial : ℝ)))
    (hsmall : β < periodicAttractiveQuantitativeThreshold ι C M)
    (_htail : Integrable (fun x => Real.exp (4 * β * DGRHS.potential
      (periodicCappedDensityMeasure ρ) periodicAttractiveInteraction x))
      (periodicCappedDensityMeasure ρ)) :
    let μ := periodicCappedDensityMeasure ρ
    let h := fun z : PeriodicTorus ι × PeriodicTorus ι =>
      DGRHS.centeredKernel μ periodicAttractiveInteraction z.1 z.2
    let I := DGRHS.interactionEnergy μ periodicAttractiveInteraction
    ∃ (hh : MemLp h 2 (μ.prod μ)) (κ : Type u) (eig : κ → ℝ)
      (b : HilbertBasis κ ℝ (Lp ℝ 2 μ)), Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ c ≤ 1 / 4 ∧ ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h
            (DGRHS.potential μ periodicAttractiveInteraction) I N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        periodicAttractiveLogPartition μ β N < ∞ ∧
        |(periodicAttractiveLogPartition μ β N).toReal -
          Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          K * (Real.exp 1 + (N : ℝ)) ^ (-c) :=
  exists_periodicAttractiveLog_original_quantitative_rate ρ M C β hM hC hβ hρ hrows hsmall

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogMomentConstant
#print axioms DGRHS.Periodic.periodicLogMomentConstant_spec
#print axioms DGRHS.Periodic.periodicRowConstant
#print axioms DGRHS.Periodic.periodicRowConstant_pos
#print axioms DGRHS.Periodic.periodicLogTruncCentered_rows_explicit
#print axioms DGRHS.Periodic.periodicAttractiveQuantitativeThreshold
#print axioms DGRHS.Periodic.periodicAttractiveQuantitativeThreshold_pos
#print axioms DGRHS.Periodic.periodicAttractiveQuantitativeThreshold_half
#print axioms DGRHS.Periodic.periodicAttractiveQuantitativeThreshold_row_small
#print axioms DGRHS.Periodic.periodic_integralOperator_neg
#print axioms DGRHS.Periodic.exists_periodicAttractiveLog_original_quantitative_rate
#print axioms DGRHS.Periodic.exists_periodicAttractiveLog_original_quantitative_rate_printed
