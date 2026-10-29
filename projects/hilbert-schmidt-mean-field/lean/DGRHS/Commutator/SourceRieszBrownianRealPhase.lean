import DGRHS.Commutator.SourceRieszPhysicalBrownianPhaseAssembly

/-! A jointly real-time measurable version of the actual centered Brownian
phase, for the existing source finite-Ito comparison interface. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

def sourceRieszBrownianRealPhaseProcess (A : Ω→ℝ) (R : ℝ≥0→Ω→ℝ)
    (r : ℝ) (ω : Ω) : ℝ := R (Real.toNNReal r) ω-A ω

lemma measurable_sourceRieszBrownianRealPhaseProcess
    (F : Filtration ℝ≥0 mΩ) (A : Ω→ℝ) (hA : StronglyMeasurable[F 0] A)
    (R : ℝ≥0→Ω→ℝ) (hR : IsStronglyPredictable F R) :
    Measurable (Function.uncurry (sourceRieszBrownianRealPhaseProcess A R)) := by
  have hRm := (hR.mono (sourceRiesz_predictable_le_product F)).measurable
  have ht : Measurable (fun p:ℝ×Ω=>(Real.toNNReal p.1,p.2)) := by fun_prop
  have hh := hRm.comp ht
  exact hh.sub (((hA.mono (F.le 0)).measurable).comp measurable_snd)

lemma sourceRieszBrownianRealPhaseProcess_zero
    (A : Ω→ℝ) (R : ℝ≥0→Ω→ℝ) (hR0 : ∀ ω,R 0 ω=A ω) :
    ∀ ω,sourceRieszBrownianRealPhaseProcess A R 0 ω=0 := by
  intro ω
  simp only [sourceRieszBrownianRealPhaseProcess,Real.toNNReal_zero,hR0,sub_self]

lemma sourceRieszBrownianRealPhaseProcess_ae_eq
    (P : Measure Ω) (A : Ω→ℝ) (R M : ℝ≥0→Ω→ℝ)
    (he : ∀ᵐ ω ∂P,∀ r,R r ω=A ω+M r ω) :
    ∀ᵐ ω ∂P,∀ r:ℝ≥0,sourceRieszBrownianRealPhaseProcess A R r ω=M r ω := by
  filter_upwards [he] with ω hω
  intro r
  have hn : Real.toNNReal (r:ℝ)=r := Subtype.ext (Real.coe_toNNReal _ r.coe_nonneg)
  simp only [sourceRieszBrownianRealPhaseProcess,hn,hω,add_sub_cancel_left]

lemma sourceRieszBrownianRealPhaseProcess_continuous
    (P : Measure Ω) (A : Ω→ℝ) (R : ℝ≥0→Ω→ℝ)
    (hc : ∀ᵐ ω ∂P,Continuous (fun r=>R r ω)) :
    ∀ᵐ ω ∂P,Continuous (fun r:ℝ=>sourceRieszBrownianRealPhaseProcess A R r ω) := by
  filter_upwards [hc] with ω hω
  exact (hω.comp (by fun_prop : Continuous Real.toNNReal)).sub continuous_const

lemma sourceRieszBrownianRealPhaseProcess_expected_export
    (P : Measure Ω) (A : Ω→ℝ) (R M : ℝ≥0→Ω→ℝ)
    (hR0 : ∀ ω,R 0 ω=A ω) (he : ∀ᵐ ω ∂P,∀ r,R r ω=A ω+M r ω)
    (H : ℝ→Ω→ℝ) (q : ℝ) (s : ℝ≥0)
    (hi : (∫ ω,sourceRieszFinitePhase (A ω+M s ω) ∂P)=
      (∫ ω,sourceRieszFinitePhase (A ω) ∂P)-q •
        (∫ r in Ioc 0 (s:ℝ),∫ ω,
          sourceRieszFinitePhase (A ω+M (Real.toNNReal r) ω)*(H r ω:ℂ) ∂P)) :
    let M₀ := sourceRieszBrownianRealPhaseProcess A R
    let χ := fun r:ℝ=>∫ ω,sourceRieszFinitePhase (A ω+M₀ r ω) ∂P
    χ s=χ 0-q • (∫ r in Ioc 0 (s:ℝ),∫ ω,
      sourceRieszFinitePhase (A ω+M₀ r ω)*(H r ω:ℂ) ∂P) := by
  intro M₀ χ
  have hn : Real.toNNReal (s:ℝ)=s := Subtype.ext (Real.coe_toNNReal _ s.coe_nonneg)
  have hχs : χ s=(∫ ω,sourceRieszFinitePhase (A ω+M s ω) ∂P) := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    simp only [M₀,sourceRieszBrownianRealPhaseProcess,hn,hω,add_sub_cancel_left]
  have hχ0 : χ 0=∫ ω,sourceRieszFinitePhase (A ω) ∂P := by
    apply integral_congr_ae
    exact ae_of_all _ (fun ω=>by
      simp only [M₀,sourceRieszBrownianRealPhaseProcess,Real.toNNReal_zero,hR0,sub_self,add_zero])
  have hh : (∫ r in Ioc 0 (s:ℝ),∫ ω,
      sourceRieszFinitePhase (A ω+M (Real.toNNReal r) ω)*(H r ω:ℂ) ∂P)=
      ∫ r in Ioc 0 (s:ℝ),∫ ω,
        sourceRieszFinitePhase (A ω+M₀ r ω)*(H r ω:ℂ) ∂P := by
    apply integral_congr_ae
    exact ae_of_all _ (fun r=>integral_congr_ae (by
      filter_upwards [he] with ω hω
      simp only [M₀,sourceRieszBrownianRealPhaseProcess,hω,add_sub_cancel_left]))
  rw [hχs,hχ0]
  exact hi.trans (congrArg (fun z:ℂ=>(∫ ω,sourceRieszFinitePhase (A ω) ∂P)-q • z) hh)

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianRealPhaseProcess
#print axioms DGRHS.Commutator.sourceRieszBrownianRealPhaseProcess
#check @DGRHS.Commutator.measurable_sourceRieszBrownianRealPhaseProcess
#print axioms DGRHS.Commutator.measurable_sourceRieszBrownianRealPhaseProcess
#check @DGRHS.Commutator.sourceRieszBrownianRealPhaseProcess_zero
#print axioms DGRHS.Commutator.sourceRieszBrownianRealPhaseProcess_zero
#check @DGRHS.Commutator.sourceRieszBrownianRealPhaseProcess_ae_eq
#print axioms DGRHS.Commutator.sourceRieszBrownianRealPhaseProcess_ae_eq
#check @DGRHS.Commutator.sourceRieszBrownianRealPhaseProcess_continuous
#print axioms DGRHS.Commutator.sourceRieszBrownianRealPhaseProcess_continuous
#check @DGRHS.Commutator.sourceRieszBrownianRealPhaseProcess_expected_export
#print axioms DGRHS.Commutator.sourceRieszBrownianRealPhaseProcess_expected_export
