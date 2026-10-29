import DGRHS.Commutator.SourceRieszSamplewiseTrigExpectation

/-! Expectation of the primitive cosine/sine Ito identities with the actual
finite Brownian integrals of the transformed predictable coefficients. Their
properness and zero mean are proved from the supplied filtered Brownian family.
The predictable phase agrees simultaneously with the original initial statistic
plus its constructed integral; no independence from that integral is assumed.
This is a conditional primitive-Ito consumer, not a general Ito theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω α : Type*} [mΩ : MeasurableSpace Ω] [Fintype α]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

noncomputable def sourceRieszPredictableSinL2
    (R : ℝ≥0→Ω→ℝ) (hR : IsStronglyPredictable F R)
    (U : ℝ≥0→Ω→ℝ) (hU : IsStronglyPredictable F U)
    (K : ℝ) (hb : ∀ r ω,‖U r ω‖≤K) :
    Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T) :=
  sourceRieszPredictableBoundedL2 P F T (fun r ω=>Real.sin (R r ω)*U r ω)
    (sourceRieszPredictable_sin_mul_bound F R U hR hU K hb).1 K
    (sourceRieszPredictable_sin_mul_bound F R U hR hU K hb).2

noncomputable def sourceRieszPredictableCosL2
    (R : ℝ≥0→Ω→ℝ) (hR : IsStronglyPredictable F R)
    (U : ℝ≥0→Ω→ℝ) (hU : IsStronglyPredictable F U)
    (K : ℝ) (hb : ∀ r ω,‖U r ω‖≤K) :
    Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T) :=
  sourceRieszPredictableBoundedL2 P F T (fun r ω=>Real.cos (R r ω)*U r ω)
    (sourceRieszPredictable_cos_mul_bound F R U hR hU K hb).1 K
    (sourceRieszPredictable_cos_mul_bound F R U hR hU K hb).2

theorem sourceRieszBrownian_samplewise_trig_expected_phase
    (B : α→ℝ≥0→Ω→ℝ) (hB : SourceRieszFilteredBrownianFamily P F B)
    (U : α→ℝ≥0→Ω→ℝ) (hU : ∀ b,IsStronglyPredictable F (U b))
    (K : ℝ) (hb : ∀ b r ω,‖U b r ω‖≤K)
    (A : Ω→ℝ) (hA : StronglyMeasurable[F 0] A)
    (R : ℝ≥0→Ω→ℝ) (hR : IsStronglyPredictable F R)
    (H : ℝ≥0→Ω→ℝ) (hH : Measurable (Function.uncurry H))
    (C : ℝ) (hHb : ∀ r ω,‖H r ω‖≤C) (q : ℝ) (s : ℝ≥0) :
    let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hb b)
    let M := sourceRieszBrownianFamilyProcess P F B T g
    let gs := fun b=>sourceRieszPredictableSinL2 P F T R hR (U b) (hU b) K (hb b)
    let gc := fun b=>sourceRieszPredictableCosL2 P F T R hR (U b) (hU b) K (hb b)
    let Ns := sourceRieszBrownianFamilyProcess P F B T gs
    let Nc := sourceRieszBrownianFamilyProcess P F B T gc
    (∀ᵐ ω ∂P,∀ r,R r ω=A ω+M r ω) →
    (∀ᵐ ω ∂P,Real.cos (A ω+M s ω)=Real.cos (A ω)-Ns s ω-
      q*(∫ r in Ioc 0 s,Real.cos (R r ω)*H r ω ∂sourceRieszBrownianTimeOn T)) →
    (∀ᵐ ω ∂P,Real.sin (A ω+M s ω)=Real.sin (A ω)+Nc s ω-
      q*(∫ r in Ioc 0 s,Real.sin (R r ω)*H r ω ∂sourceRieszBrownianTimeOn T)) →
    (∫ ω,sourceRieszFinitePhase (A ω+M s ω) ∂P)=
      (∫ ω,sourceRieszFinitePhase (A ω) ∂P)-q •
        (∫ r in Ioc 0 s,∫ ω,sourceRieszFinitePhase (A ω+M r ω)*(H r ω:ℂ) ∂P
          ∂sourceRieszBrownianTimeOn T) := by
  dsimp only
  intro hphase hcos hsin
  let g := fun b=>sourceRieszPredictableBoundedL2 P F T (U b) (hU b) K (hb b)
  let M := sourceRieszBrownianFamilyProcess P F B T g
  let gs := fun b=>sourceRieszPredictableSinL2 P F T R hR (U b) (hU b) K (hb b)
  let gc := fun b=>sourceRieszPredictableCosL2 P F T R hR (U b) (hU b) K (hb b)
  have hm := sourceRieszBrownianFamilyProcess_martingale P F B hB T g
  have hAm : Measurable A := (hA.mono (F.le 0)).measurable
  have hYm : Measurable (fun ω=>A ω+M s ω) :=
    hAm.add ((hm.1.stronglyAdapted s).mono (F.le s)).measurable
  have hRm : Measurable (Function.uncurry R) :=
    (hR.mono (sourceRiesz_predictable_le_product F)).measurable
  have hiH : Integrable (Function.uncurry H)
      (((sourceRieszBrownianTimeOn T).restrict (Ioc 0 s)).prod P) :=
    (integrable_const C).mono' hH.aestronglyMeasurable (ae_of_all _ (fun p=>hHb p.1 p.2))
  have hs0 := sourceRieszBrownianFamilyProcess_mean_zero P F B hB T gs s
  have hc0 := sourceRieszBrownianFamilyProcess_mean_zero P F B hB T gc s
  have he := sourceRiesz_samplewise_trig_expected_phase P
    ((sourceRieszBrownianTimeOn T).restrict (Ioc 0 s)) A (fun ω=>A ω+M s ω)
    hAm hYm R H hRm hH hiH
    (sourceRieszBrownianFamilyProcess P F B T gs s)
    (sourceRieszBrownianFamilyProcess P F B T gc s)
    hs0.1 hc0.1 hs0.2 hc0.2 q hcos hsin
  rw [he]
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ (fun r=>integral_congr_ae (by
    filter_upwards [hphase] with ω hω
    rw [hω r]))

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszPredictableSinL2
#print axioms DGRHS.Commutator.sourceRieszPredictableSinL2
#check @DGRHS.Commutator.sourceRieszPredictableCosL2
#print axioms DGRHS.Commutator.sourceRieszPredictableCosL2
#check @DGRHS.Commutator.sourceRieszBrownian_samplewise_trig_expected_phase
#print axioms DGRHS.Commutator.sourceRieszBrownian_samplewise_trig_expected_phase
