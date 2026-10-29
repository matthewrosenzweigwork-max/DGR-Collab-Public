import DGRHS.Gaussian.PeriodicLogParticleLink
import DGRHS.Attractive.SourceUniform
import DGRHS.Attractive.SourceMomentThreshold
import DGRHS.Attractive.RowMoments
import DGRHS.Decoupling.Product

/-!
Packet P11d (follow-up F1 of the P11b review, section 5): Theorem 2.6 (`thm:attractive-log-small-beta-partition`,
TeX 615-644), uniform-bound assertion `eq:attUniformBoundStatement`, on the flat torus (Remark 2.1, TeX 492-496)
for the POINTWISE kernel `periodicLogPairFun` (`PeriodicLogParticleLink.lean`): pointwise even, measurable,
smooth off `0`, and Haar-a.e. equal to `periodicLogKernel`.

`PeriodicAttractiveLogPartition` states the same two clauses for `periodicLogKernel`, a `Classical.choice`
a.e.-class representative; that is faithful for `μ ≪ Haar` but not for measures with a Haar-singular part
(e.g. arclength on a circle subgroup for `d ≥ 2`), which integrate the kernel on a Haar-null set.  Here the
attractive interaction is `W(x,y) = -periodicLogPairFun(x-y)`, the printed pointwise `-g_d` (the value `0` at
`0` is immaterial: the singular weight and `periodicSingularAbsLogPw` impose `+∞` on the diagonal and
`hpair` forces the diagonal to be `μ⊗μ`-null).  Hypotheses, constants and conclusions are those of the
`periodicLogKernel` exports; the proof is the same generic `W`-statement
`DGRHS.Attractive.source_uniform_partition` instantiated with the pointwise kernel.  No hypothesis is added.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
open DGRHS.Attractive
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The torus attractive logarithmic interaction `W(x,y) = -g(x - y)` (TeX 2977) with the pointwise kernel
`g = periodicLogPairFun`. -/
def periodicAttractiveInteractionPw (x y : PeriodicTorus ι) : ℝ := -periodicLogPairFun (x - y)

/-- `|g_att|` on the torus with the value `+∞` on the diagonal (the singular logarithm). -/
def periodicSingularAbsLogPw (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ≥0∞ :=
  if p.1 = p.2 then ∞ else ENNReal.ofReal |periodicLogPairFun (p.1 - p.2)|

lemma measurable_periodicSingularAbsLogPw : Measurable (periodicSingularAbsLogPw (ι := ι)) := by
  have hd : MeasurableSet {p : PeriodicTorus ι × PeriodicTorus ι | p.1 = p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  exact Measurable.ite hd measurable_const
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (measurable_periodicLogPairFun.comp (measurable_fst.sub measurable_snd))))

lemma measurable_periodicLogPairFunPair :
    Measurable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogPairFun (p.1 - p.2)) :=
  measurable_periodicLogPairFun.comp (measurable_fst.sub measurable_snd)

/-- The singular pair-`L¹` assumption `g_att ∈ L¹(μ⊗²)` is equivalent to integrability of the
totalized kernel together with `μ⊗μ`-nullness of the diagonal. -/
theorem periodicSingularAbsLogPw_finite_iff (μ : Measure (PeriodicTorus ι)) :
    (∫⁻ p, periodicSingularAbsLogPw p ∂μ.prod μ) < ∞ ↔
      Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogPairFun (p.1 - p.2))
        (μ.prod μ) ∧ (∀ᵐ p : PeriodicTorus ι × PeriodicTorus ι ∂μ.prod μ, p.1 ≠ p.2) := by
  constructor
  · intro hf
    have hn : ∀ᵐ p : PeriodicTorus ι × PeriodicTorus ι ∂μ.prod μ, p.1 ≠ p.2 := by
      filter_upwards [ae_lt_top measurable_periodicSingularAbsLogPw hf.ne] with p hp he
      simp [periodicSingularAbsLogPw, he] at hp
    have hbound : ∀ p : PeriodicTorus ι × PeriodicTorus ι,
        ENNReal.ofReal ‖periodicLogPairFun (p.1 - p.2)‖ ≤ periodicSingularAbsLogPw p := by
      intro p
      by_cases hz : p.1 = p.2
      · simp [periodicSingularAbsLogPw, hz]
      · simp [periodicSingularAbsLogPw, hz, Real.norm_eq_abs]
    refine ⟨⟨measurable_periodicLogPairFunPair.aestronglyMeasurable, ?_⟩, hn⟩
    apply (hasFiniteIntegral_iff_norm _).mpr
    exact (lintegral_mono hbound).trans_lt hf
  · rintro ⟨hi, hn⟩
    have he : periodicSingularAbsLogPw =ᵐ[μ.prod μ]
        (fun p : PeriodicTorus ι × PeriodicTorus ι =>
          ENNReal.ofReal ‖periodicLogPairFun (p.1 - p.2)‖) := by
      filter_upwards [hn] with p hp
      simp [periodicSingularAbsLogPw, hp, Real.norm_eq_abs]
    rw [lintegral_congr_ae he]
    exact (hasFiniteIntegral_iff_norm _).mp hi.hasFiniteIntegral

/-- The singular pair-`L¹` assumption excludes every off-diagonal particle collision almost surely
under the iid law (torus form of `DGRHS.Gaussian.singularAbsLog_iid_collision_free`). -/
theorem periodicSingularAbsLogPw_iid_collision_free (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ] (hf : (∫⁻ p, periodicSingularAbsLogPw p ∂μ.prod μ) < ∞) (N : ℕ) :
    ∀ᵐ x : Fin N → PeriodicTorus ι ∂Measure.pi (fun _ : Fin N => μ),
      ∀ i j : Fin N, i ≠ j → x i ≠ x j := by
  classical
  have hne := ((periodicSingularAbsLogPw_finite_iff μ).mp hf).2
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun x h => (h hij).elim
  · exact (DGRHS.Decoupling.pair_eval_measurePreserving μ i j hij).quasiMeasurePreserving.ae hne
      |>.mono (fun x hx _ => hx)

/-- The literal attractive singular Boltzmann weight of the torus: `1` for `β = 0`; for `β ≠ 0`
`exp(-β N F_N^att)` off collisions and `+∞` at a particle collision (where `g_att = -g = -∞`). -/
def periodicAttractiveSingularWeightPw (μ : Measure (PeriodicTorus ι)) (β : ℝ) (N : ℕ)
    (x : Fin N → PeriodicTorus ι) : ℝ≥0∞ := by
  classical
  exact if β = 0 then 1 else
    if ∀ i j : Fin N, i ≠ j → x i ≠ x j then
      ENNReal.ofReal (Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ periodicAttractiveInteractionPw p.1 p.2)
        (DGRHS.potential μ periodicAttractiveInteractionPw)
        (DGRHS.interactionEnergy μ periodicAttractiveInteractionPw) N x))
    else ∞

theorem periodicAttractiveSingularWeightPw_ae (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p, periodicSingularAbsLogPw p ∂μ.prod μ) < ∞) (β : ℝ) (N : ℕ) :
    periodicAttractiveSingularWeightPw μ β N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun x => ENNReal.ofReal (Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ periodicAttractiveInteractionPw p.1 p.2)
        (DGRHS.potential μ periodicAttractiveInteractionPw)
        (DGRHS.interactionEnergy μ periodicAttractiveInteractionPw) N x))) := by
  filter_upwards [periodicSingularAbsLogPw_iid_collision_free μ hpair N] with x hx
  by_cases hb : β = 0
  · simp [periodicAttractiveSingularWeightPw, hb]
  · simp only [periodicAttractiveSingularWeightPw, ite_eq_right hb, ite_eq_left hx]

/-- The torus attractive partition function `K^att_{N,β}(μ)` as the extended lower integral of the
singular weight over `μ^{⊗N}`. -/
def periodicAttractiveLogPartitionPw (μ : Measure (PeriodicTorus ι)) (β : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, periodicAttractiveSingularWeightPw μ β N x ∂Measure.pi (fun _ : Fin N => μ)

/-- The explicit uniform constant `C_ub^att(β,μ)` of TeX 2586-2594. -/
def periodicAttractiveUniformConstantPw (μ : Measure (PeriodicTorus ι)) (C β : ℝ) : ℝ :=
  Real.exp (β * |DGRHS.interactionEnergy μ periodicAttractiveInteractionPw|) *
    Real.sqrt (2 / (1 - (β * (attractiveMomentConstant * C)) ^ 2)) *
    Real.sqrt (∫ x, Real.exp (2 * β * DGRHS.potential μ periodicAttractiveInteractionPw x) ∂μ)

lemma periodicAttractiveInteractionPw_uncurry :
    Function.uncurry (periodicAttractiveInteractionPw (ι := ι)) =
      -(fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogPairFun (p.1 - p.2)) := by
  funext p
  simp [Function.uncurry, periodicAttractiveInteractionPw]

lemma periodicAttractiveInteractionPw_symm (x y : PeriodicTorus ι) :
    periodicAttractiveInteractionPw x y = periodicAttractiveInteractionPw y x := by
  unfold periodicAttractiveInteractionPw
  rw [← neg_sub y x, periodicLogPairFun_neg]

theorem periodicAttractiveLogPw_source_uniform (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p, periodicSingularAbsLogPw p ∂μ.prod μ) < ∞)
    (C β : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal
        (|DGRHS.centeredKernel μ periodicAttractiveInteractionPw x y| ^ p) ∂μ) ≤
          ENNReal.ofReal (C ^ p * (p.factorial : ℝ)))
    (hβ : 0 ≤ β) (hsmall : β * (attractiveMomentConstant * C) < 1)
    (htail : Integrable
      (fun x => Real.exp (2 * β * DGRHS.potential μ periodicAttractiveInteractionPw x)) μ) :
    ∀ N : ℕ, 0 < N →
    Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β * (N : ℝ) *
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ periodicAttractiveInteractionPw p.1 p.2)
        (DGRHS.potential μ periodicAttractiveInteractionPw)
        (DGRHS.interactionEnergy μ periodicAttractiveInteractionPw) N x))
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ x : Fin N → PeriodicTorus ι, Real.exp (-β * (N : ℝ) *
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ periodicAttractiveInteractionPw p.1 p.2)
        (DGRHS.potential μ periodicAttractiveInteractionPw)
        (DGRHS.interactionEnergy μ periodicAttractiveInteractionPw) N x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      Real.exp (β * |DGRHS.interactionEnergy μ periodicAttractiveInteractionPw|) *
        Real.sqrt (2 / (1 - (β * (attractiveMomentConstant * C)) ^ 2)) *
        Real.sqrt (∫ x, Real.exp
          (2 * β * DGRHS.potential μ periodicAttractiveInteractionPw x) ∂μ) := by
  have hWi : Integrable (Function.uncurry (periodicAttractiveInteractionPw (ι := ι))) (μ.prod μ) := by
    rw [periodicAttractiveInteractionPw_uncurry]
    exact ((periodicSingularAbsLogPw_finite_iff μ).mp hpair).1.neg
  have hWm : StronglyMeasurable (Function.uncurry (periodicAttractiveInteractionPw (ι := ι))) := by
    rw [periodicAttractiveInteractionPw_uncurry]
    exact measurable_periodicLogPairFunPair.neg.stronglyMeasurable
  have hm := (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ
    (Function.uncurry periodicAttractiveInteractionPw) hWm).measurable
  have hr := rowFactorialMoments_of_lintegral μ
    (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      DGRHS.centeredKernel μ periodicAttractiveInteractionPw p.1 p.2) hm C hC hrow
  intro N hN
  exact source_uniform_partition periodicAttractiveInteractionPw hWm hWi
    periodicAttractiveInteractionPw_symm C β hr hβ hsmall htail N hN

/-- Theorem 2.6 (uniform bound `eq:attUniformBoundStatement`) on the torus, exact shape of
`DGRHS.Attractive.attractiveLogPartition_uniform`: for every probability measure `μ` on `𝕋^d` with
`g_att ∈ L¹(μ⊗²)` and the factorial-moment bound `eq:attMomentAssumption`, every `0 ≤ β` with
`β C_* C_mom < 1` and `e^{2β h_μ^att} ∈ L¹(μ)`, and every `N ≥ 1`, the partition function is finite
and bounded by the explicit constant `C_ub^att(β,μ)`. -/
theorem periodicAttractiveLogPartitionPw_uniform (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p, periodicSingularAbsLogPw p ∂μ.prod μ) < ∞)
    (C β : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal
        (|DGRHS.centeredKernel μ periodicAttractiveInteractionPw x y| ^ p) ∂μ) ≤
          ENNReal.ofReal (C ^ p * (p.factorial : ℝ)))
    (hβ : 0 ≤ β) (hsmall : β * (attractiveMomentConstant * C) < 1)
    (htail : Integrable
      (fun x => Real.exp (2 * β * DGRHS.potential μ periodicAttractiveInteractionPw x)) μ) :
    ∀ N : ℕ, 0 < N →
      periodicAttractiveLogPartitionPw μ β N ≤
        ENNReal.ofReal (periodicAttractiveUniformConstantPw μ C β) ∧
      periodicAttractiveLogPartitionPw μ β N < ∞ := by
  intro N hN
  obtain ⟨hi, hb⟩ := periodicAttractiveLogPw_source_uniform μ hpair C β hC hrow hβ hsmall htail N hN
  have he : periodicAttractiveLogPartitionPw μ β N = ENNReal.ofReal
      (∫ x : Fin N → PeriodicTorus ι, Real.exp (-β * (N : ℝ) *
        DGRHS.CLT.sourceCanonicalModulatedEnergy
          (fun p => DGRHS.centeredKernel μ periodicAttractiveInteractionPw p.1 p.2)
          (DGRHS.potential μ periodicAttractiveInteractionPw)
          (DGRHS.interactionEnergy μ periodicAttractiveInteractionPw) N x)
        ∂Measure.pi (fun _ : Fin N => μ)) := by
    unfold periodicAttractiveLogPartitionPw
    rw [lintegral_congr_ae (periodicAttractiveSingularWeightPw_ae μ hpair β N)]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm
  rw [he]
  exact ⟨ENNReal.ofReal_le_ofReal hb, ENNReal.ofReal_lt_top⟩

/-- Theorem 2.6 (uniform bound) with the printed threshold `β_0 = 1/(C_* C_mom)`: exact shape of
`DGRHS.Attractive.attractiveLogPartition_uniform_threshold`. -/
theorem periodicAttractiveLogPartitionPw_uniform_threshold (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p, periodicSingularAbsLogPw p ∂μ.prod μ) < ∞)
    (C β : ℝ) (hC : 0 < C)
    (hrow : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal
        (|DGRHS.centeredKernel μ periodicAttractiveInteractionPw x y| ^ p) ∂μ) ≤
          ENNReal.ofReal (C ^ p * (p.factorial : ℝ)))
    (hβ : 0 ≤ β) (hsmall : β < attractiveBetaThreshold C)
    (htail : Integrable
      (fun x => Real.exp (2 * β * DGRHS.potential μ periodicAttractiveInteractionPw x)) μ) :
    0 < attractiveBetaThreshold C ∧ ∀ N : ℕ, 0 < N →
      periodicAttractiveLogPartitionPw μ β N ≤
        ENNReal.ofReal (periodicAttractiveUniformConstantPw μ C β) ∧
      periodicAttractiveLogPartitionPw μ β N < ∞ :=
  ⟨attractiveBetaThreshold_pos hC, periodicAttractiveLogPartitionPw_uniform μ hpair C β hC.le
    hrow hβ ((attractiveBetaThreshold_lt_iff hC).mp hsmall) htail⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicSingularAbsLogPw_finite_iff
#print axioms DGRHS.Periodic.periodicSingularAbsLogPw_iid_collision_free
#print axioms DGRHS.Periodic.periodicAttractiveSingularWeightPw_ae
#print axioms DGRHS.Periodic.periodicAttractiveLogPw_source_uniform
#print axioms DGRHS.Periodic.periodicAttractiveLogPartitionPw_uniform
#print axioms DGRHS.Periodic.periodicAttractiveLogPartitionPw_uniform_threshold
