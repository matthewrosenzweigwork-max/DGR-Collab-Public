import DGRHS.Gaussian.PeriodicLogReality
import DGRHS.Attractive.SourceUniform
import DGRHS.Attractive.SourceMomentThreshold
import DGRHS.Attractive.RowMoments
import DGRHS.Decoupling.Product

/-!
Packet P11b, unit 2 (clause 1): Theorem 2.6 (`thm:attractive-log-small-beta-partition`, TeX 615-644),
uniform-bound assertion `eq:attUniformBoundStatement`, on the flat torus (Remark 2.1, TeX 492-496), in the
exact shape of the Euclidean exports `DGRHS.Attractive.attractiveLogPartition_uniform` and
`attractiveLogPartition_uniform_threshold` (`Attractive/SourceLogPartition.lean`).

The attractive interaction on the torus is `-g` for the zero-average repulsive periodic (spectral)
logarithmic kernel `g = periodicLogKernel` (TeX 2961-2977: "The attractive interaction is `-g_d`"), the
exact transposition of `g_att = log |x|`.  As in the Euclidean statement, `μ` is an arbitrary
probability measure on the torus, the hypothesis `g_att ∈ L¹(μ⊗²)` is encoded literally with the value
`+∞` on the diagonal (`periodicSingularAbsLog`, whose finiteness is equivalent to pair integrability and
collision-nullness), the factorial-moment hypothesis `eq:attMomentAssumption` has its supremum over the
second variable outside the integral, and the explicit constant of TeX 2586-2594 is exported.  The
universal constant `C_* = 8 e²` and `β_0 = 1/(C_* C_mom)` are the Euclidean ones
(`attractiveMomentConstant`, `attractiveBetaThreshold`): the proof is the generic `W`-statement
(`DGRHS.Attractive.source_uniform_partition`, TeX 2490-2595) instantiated with `W(x,y) = -g(x-y)`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
open DGRHS.Attractive
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The torus attractive logarithmic interaction `W(x,y) = -g(x - y)` (TeX 2977). -/
def periodicAttractiveInteraction (x y : PeriodicTorus ι) : ℝ := -periodicLogKernel (x - y)

/-- `|g_att|` on the torus with the value `+∞` on the diagonal (the singular logarithm). -/
def periodicSingularAbsLog (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ≥0∞ :=
  if p.1 = p.2 then ∞ else ENNReal.ofReal |periodicLogKernel (p.1 - p.2)|

lemma measurable_periodicSingularAbsLog : Measurable (periodicSingularAbsLog (ι := ι)) := by
  have hd : MeasurableSet {p : PeriodicTorus ι × PeriodicTorus ι | p.1 = p.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  exact Measurable.ite hd measurable_const
    (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (periodicLogKernel_measurable.comp (measurable_fst.sub measurable_snd))))

lemma measurable_periodicLogKernelPair :
    Measurable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1 - p.2)) :=
  periodicLogKernel_measurable.comp (measurable_fst.sub measurable_snd)

/-- The singular pair-`L¹` assumption `g_att ∈ L¹(μ⊗²)` is equivalent to integrability of the
totalized kernel together with `μ⊗μ`-nullness of the diagonal. -/
theorem periodicSingularAbsLog_finite_iff (μ : Measure (PeriodicTorus ι)) :
    (∫⁻ p, periodicSingularAbsLog p ∂μ.prod μ) < ∞ ↔
      Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1 - p.2))
        (μ.prod μ) ∧ (∀ᵐ p : PeriodicTorus ι × PeriodicTorus ι ∂μ.prod μ, p.1 ≠ p.2) := by
  constructor
  · intro hf
    have hn : ∀ᵐ p : PeriodicTorus ι × PeriodicTorus ι ∂μ.prod μ, p.1 ≠ p.2 := by
      filter_upwards [ae_lt_top measurable_periodicSingularAbsLog hf.ne] with p hp he
      simp [periodicSingularAbsLog, he] at hp
    have hbound : ∀ p : PeriodicTorus ι × PeriodicTorus ι,
        ENNReal.ofReal ‖periodicLogKernel (p.1 - p.2)‖ ≤ periodicSingularAbsLog p := by
      intro p
      by_cases hz : p.1 = p.2
      · simp [periodicSingularAbsLog, hz]
      · simp [periodicSingularAbsLog, hz, Real.norm_eq_abs]
    refine ⟨⟨measurable_periodicLogKernelPair.aestronglyMeasurable, ?_⟩, hn⟩
    apply (hasFiniteIntegral_iff_norm _).mpr
    exact (lintegral_mono hbound).trans_lt hf
  · rintro ⟨hi, hn⟩
    have he : periodicSingularAbsLog =ᵐ[μ.prod μ]
        (fun p : PeriodicTorus ι × PeriodicTorus ι =>
          ENNReal.ofReal ‖periodicLogKernel (p.1 - p.2)‖) := by
      filter_upwards [hn] with p hp
      simp [periodicSingularAbsLog, hp, Real.norm_eq_abs]
    rw [lintegral_congr_ae he]
    exact (hasFiniteIntegral_iff_norm _).mp hi.hasFiniteIntegral

/-- The singular pair-`L¹` assumption excludes every off-diagonal particle collision almost surely
under the iid law (torus form of `DGRHS.Gaussian.singularAbsLog_iid_collision_free`). -/
theorem periodicSingularAbsLog_iid_collision_free (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ] (hf : (∫⁻ p, periodicSingularAbsLog p ∂μ.prod μ) < ∞) (N : ℕ) :
    ∀ᵐ x : Fin N → PeriodicTorus ι ∂Measure.pi (fun _ : Fin N => μ),
      ∀ i j : Fin N, i ≠ j → x i ≠ x j := by
  classical
  have hne := ((periodicSingularAbsLog_finite_iff μ).mp hf).2
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
def periodicAttractiveSingularWeight (μ : Measure (PeriodicTorus ι)) (β : ℝ) (N : ℕ)
    (x : Fin N → PeriodicTorus ι) : ℝ≥0∞ := by
  classical
  exact if β = 0 then 1 else
    if ∀ i j : Fin N, i ≠ j → x i ≠ x j then
      ENNReal.ofReal (Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ periodicAttractiveInteraction p.1 p.2)
        (DGRHS.potential μ periodicAttractiveInteraction)
        (DGRHS.interactionEnergy μ periodicAttractiveInteraction) N x))
    else ∞

theorem periodicAttractiveSingularWeight_ae (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p, periodicSingularAbsLog p ∂μ.prod μ) < ∞) (β : ℝ) (N : ℕ) :
    periodicAttractiveSingularWeight μ β N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun x => ENNReal.ofReal (Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ periodicAttractiveInteraction p.1 p.2)
        (DGRHS.potential μ periodicAttractiveInteraction)
        (DGRHS.interactionEnergy μ periodicAttractiveInteraction) N x))) := by
  filter_upwards [periodicSingularAbsLog_iid_collision_free μ hpair N] with x hx
  by_cases hb : β = 0
  · simp [periodicAttractiveSingularWeight, hb]
  · simp only [periodicAttractiveSingularWeight, ite_eq_right hb, ite_eq_left hx]

/-- The torus attractive partition function `K^att_{N,β}(μ)` as the extended lower integral of the
singular weight over `μ^{⊗N}`. -/
def periodicAttractiveLogPartition (μ : Measure (PeriodicTorus ι)) (β : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, periodicAttractiveSingularWeight μ β N x ∂Measure.pi (fun _ : Fin N => μ)

/-- The explicit uniform constant `C_ub^att(β,μ)` of TeX 2586-2594. -/
def periodicAttractiveUniformConstant (μ : Measure (PeriodicTorus ι)) (C β : ℝ) : ℝ :=
  Real.exp (β * |DGRHS.interactionEnergy μ periodicAttractiveInteraction|) *
    Real.sqrt (2 / (1 - (β * (attractiveMomentConstant * C)) ^ 2)) *
    Real.sqrt (∫ x, Real.exp (2 * β * DGRHS.potential μ periodicAttractiveInteraction x) ∂μ)

lemma periodicAttractiveInteraction_uncurry :
    Function.uncurry (periodicAttractiveInteraction (ι := ι)) =
      -(fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1 - p.2)) := by
  funext p
  simp [Function.uncurry, periodicAttractiveInteraction]

lemma periodicAttractiveInteraction_symm (x y : PeriodicTorus ι) :
    periodicAttractiveInteraction x y = periodicAttractiveInteraction y x := by
  unfold periodicAttractiveInteraction
  rw [← neg_sub y x, periodicLogKernel_even]

theorem periodicAttractiveLog_source_uniform (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p, periodicSingularAbsLog p ∂μ.prod μ) < ∞)
    (C β : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal
        (|DGRHS.centeredKernel μ periodicAttractiveInteraction x y| ^ p) ∂μ) ≤
          ENNReal.ofReal (C ^ p * (p.factorial : ℝ)))
    (hβ : 0 ≤ β) (hsmall : β * (attractiveMomentConstant * C) < 1)
    (htail : Integrable
      (fun x => Real.exp (2 * β * DGRHS.potential μ periodicAttractiveInteraction x)) μ) :
    ∀ N : ℕ, 0 < N →
    Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β * (N : ℝ) *
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ periodicAttractiveInteraction p.1 p.2)
        (DGRHS.potential μ periodicAttractiveInteraction)
        (DGRHS.interactionEnergy μ periodicAttractiveInteraction) N x))
      (Measure.pi (fun _ : Fin N => μ)) ∧
    (∫ x : Fin N → PeriodicTorus ι, Real.exp (-β * (N : ℝ) *
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ periodicAttractiveInteraction p.1 p.2)
        (DGRHS.potential μ periodicAttractiveInteraction)
        (DGRHS.interactionEnergy μ periodicAttractiveInteraction) N x)
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      Real.exp (β * |DGRHS.interactionEnergy μ periodicAttractiveInteraction|) *
        Real.sqrt (2 / (1 - (β * (attractiveMomentConstant * C)) ^ 2)) *
        Real.sqrt (∫ x, Real.exp
          (2 * β * DGRHS.potential μ periodicAttractiveInteraction x) ∂μ) := by
  have hWi : Integrable (Function.uncurry (periodicAttractiveInteraction (ι := ι))) (μ.prod μ) := by
    rw [periodicAttractiveInteraction_uncurry]
    exact ((periodicSingularAbsLog_finite_iff μ).mp hpair).1.neg
  have hWm : StronglyMeasurable (Function.uncurry (periodicAttractiveInteraction (ι := ι))) := by
    rw [periodicAttractiveInteraction_uncurry]
    exact measurable_periodicLogKernelPair.neg.stronglyMeasurable
  have hm := (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ
    (Function.uncurry periodicAttractiveInteraction) hWm).measurable
  have hr := rowFactorialMoments_of_lintegral μ
    (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      DGRHS.centeredKernel μ periodicAttractiveInteraction p.1 p.2) hm C hC hrow
  intro N hN
  exact source_uniform_partition periodicAttractiveInteraction hWm hWi
    periodicAttractiveInteraction_symm C β hr hβ hsmall htail N hN

/-- Theorem 2.6 (uniform bound `eq:attUniformBoundStatement`) on the torus, exact shape of
`DGRHS.Attractive.attractiveLogPartition_uniform`: for every probability measure `μ` on `𝕋^d` with
`g_att ∈ L¹(μ⊗²)` and the factorial-moment bound `eq:attMomentAssumption`, every `0 ≤ β` with
`β C_* C_mom < 1` and `e^{2β h_μ^att} ∈ L¹(μ)`, and every `N ≥ 1`, the partition function is finite
and bounded by the explicit constant `C_ub^att(β,μ)`. -/
theorem periodicAttractiveLogPartition_uniform (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p, periodicSingularAbsLog p ∂μ.prod μ) < ∞)
    (C β : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal
        (|DGRHS.centeredKernel μ periodicAttractiveInteraction x y| ^ p) ∂μ) ≤
          ENNReal.ofReal (C ^ p * (p.factorial : ℝ)))
    (hβ : 0 ≤ β) (hsmall : β * (attractiveMomentConstant * C) < 1)
    (htail : Integrable
      (fun x => Real.exp (2 * β * DGRHS.potential μ periodicAttractiveInteraction x)) μ) :
    ∀ N : ℕ, 0 < N →
      periodicAttractiveLogPartition μ β N ≤
        ENNReal.ofReal (periodicAttractiveUniformConstant μ C β) ∧
      periodicAttractiveLogPartition μ β N < ∞ := by
  intro N hN
  obtain ⟨hi, hb⟩ := periodicAttractiveLog_source_uniform μ hpair C β hC hrow hβ hsmall htail N hN
  have he : periodicAttractiveLogPartition μ β N = ENNReal.ofReal
      (∫ x : Fin N → PeriodicTorus ι, Real.exp (-β * (N : ℝ) *
        DGRHS.CLT.sourceCanonicalModulatedEnergy
          (fun p => DGRHS.centeredKernel μ periodicAttractiveInteraction p.1 p.2)
          (DGRHS.potential μ periodicAttractiveInteraction)
          (DGRHS.interactionEnergy μ periodicAttractiveInteraction) N x)
        ∂Measure.pi (fun _ : Fin N => μ)) := by
    unfold periodicAttractiveLogPartition
    rw [lintegral_congr_ae (periodicAttractiveSingularWeight_ae μ hpair β N)]
    exact (ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm
  rw [he]
  exact ⟨ENNReal.ofReal_le_ofReal hb, ENNReal.ofReal_lt_top⟩

/-- Theorem 2.6 (uniform bound) with the printed threshold `β_0 = 1/(C_* C_mom)`: exact shape of
`DGRHS.Attractive.attractiveLogPartition_uniform_threshold`. -/
theorem periodicAttractiveLogPartition_uniform_threshold (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ]
    (hpair : (∫⁻ p, periodicSingularAbsLog p ∂μ.prod μ) < ∞)
    (C β : ℝ) (hC : 0 < C)
    (hrow : ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal
        (|DGRHS.centeredKernel μ periodicAttractiveInteraction x y| ^ p) ∂μ) ≤
          ENNReal.ofReal (C ^ p * (p.factorial : ℝ)))
    (hβ : 0 ≤ β) (hsmall : β < attractiveBetaThreshold C)
    (htail : Integrable
      (fun x => Real.exp (2 * β * DGRHS.potential μ periodicAttractiveInteraction x)) μ) :
    0 < attractiveBetaThreshold C ∧ ∀ N : ℕ, 0 < N →
      periodicAttractiveLogPartition μ β N ≤
        ENNReal.ofReal (periodicAttractiveUniformConstant μ C β) ∧
      periodicAttractiveLogPartition μ β N < ∞ :=
  ⟨attractiveBetaThreshold_pos hC, periodicAttractiveLogPartition_uniform μ hpair C β hC.le
    hrow hβ ((attractiveBetaThreshold_lt_iff hC).mp hsmall) htail⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicSingularAbsLog_finite_iff
#print axioms DGRHS.Periodic.periodicSingularAbsLog_iid_collision_free
#print axioms DGRHS.Periodic.periodicAttractiveSingularWeight_ae
#print axioms DGRHS.Periodic.periodicAttractiveLog_source_uniform
#print axioms DGRHS.Periodic.periodicAttractiveLogPartition_uniform
#print axioms DGRHS.Periodic.periodicAttractiveLogPartition_uniform_threshold
