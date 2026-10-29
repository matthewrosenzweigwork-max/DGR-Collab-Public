import DGRHS.Commutator.SourceRieszBrownianTimeIsometryAE

/-! Proper second moments, initial and terminal identities, and initial-sigma-algebra
weighted mean zero for the actual constructed scalar Brownian integral process.
The initial multiplier may depend on the actual initial particle configuration;
no independence between it and the terminal stochastic integral is assumed.
A continuous modification and the common-driver bracket remain separate. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace DGRHS.Commutator
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
variable (B : ℝ≥0→Ω→ℝ) (hB : IsPreBrownianReal B P) (hBa : StronglyAdapted F B)
variable (hind : ∀ s t,s≤t →
  Indep (MeasurableSpace.comap (fun ω=>B t ω-B s ω) (borel ℝ)) (F s) P)

theorem sourceRieszBrownianProcess_zero_no_continuity
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    sourceRieszBrownianProcess P F T B hB hBa hind g 0=ᵐ[P] (fun _=>0) := by
  have he := sourceRieszBrownianProcessL2_coe P F T B hB hBa hind g 0
  rw [sourceRieszBrownianProcessL2_zero_no_continuity P F T B hB hBa hind g] at he
  exact he.symm.trans (Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=P))

theorem sourceRieszBrownianProcess_terminal_no_continuity
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    sourceRieszBrownianProcess P F T B hB hBa hind g T=ᵐ[P]
      (sourceRieszBrownianIntegral P F T B hB hBa hind g : Ω→ℝ) := by
  have he := sourceRieszBrownianProcessL2_coe P F T B hB hBa hind g T
  rw [sourceRieszBrownianProcessL2_terminal_no_continuity P F T B hB hBa hind g] at he
  exact he.symm

theorem sourceRieszBrownianProcess_second_moment_no_continuity
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0) :
    Integrable (fun ω=>(sourceRieszBrownianProcess P F T B hB hBa hind g t ω)^2) P ∧
      (∫ ω,(sourceRieszBrownianProcess P F T B hB hBa hind g t ω)^2 ∂P)=
        ∫ p in Ioc 0 t ×ˢ (univ : Set Ω),(g p)^2 ∂sourceRieszBrownianPredictableMeasure P F T := by
  refine ⟨((sourceRieszBrownianProcess_martingale P F T B hB hBa hind g).2 t).integrable_sq,?_⟩
  rw [←sourceRieszBrownianProcessL2_norm_sq_no_continuity P F T B hB hBa hind g t,sourceRiesz_L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [sourceRieszBrownianProcessL2_coe P F T B hB hBa hind g t] with ω hω
  rw [hω]

theorem sourceRieszBrownianProcess_initial_weighted_zero_no_continuity
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0)
    (Z : Ω→ℝ) (hZ : StronglyMeasurable[F 0] Z) (hZL : MemLp Z 2 P) :
    Integrable (fun ω=>Z ω*sourceRieszBrownianProcess P F T B hB hBa hind g t ω) P ∧
      (∫ ω,Z ω*sourceRieszBrownianProcess P F T B hB hBa hind g t ω ∂P)=0 := by
  let M := sourceRieszBrownianProcess P F T B hB hBa hind g
  have hm := sourceRieszBrownianProcess_martingale P F T B hB hBa hind g
  have hi := hZL.integrable_mul (hm.2 t)
  have he := condExp_mul_of_stronglyMeasurable_left hZ hi ((hm.2 t).integrable one_le_two)
  change P[fun ω=>Z ω*M t ω | F 0]=ᵐ[P] (fun ω=>Z ω*(P[M t | F 0]) ω) at he
  have hz : P[M t | F 0]=ᵐ[P] (fun _=>0) :=
    (hm.1.2 0 t bot_le).trans (sourceRieszBrownianProcess_zero_no_continuity P F T B hB hBa hind g)
  have hp : P[fun ω=>Z ω*M t ω | F 0]=ᵐ[P] (fun _=>0) := by
    filter_upwards [he,hz] with ω hω h0
    simpa only [h0,mul_zero] using hω
  refine ⟨hi,?_⟩
  rw [←integral_condExp (F.le 0),integral_congr_ae hp,integral_zero]

theorem sourceRieszBrownianProcess_initial_phase_zero_no_continuity
    (g : Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) (t : ℝ≥0)
    (Z : Ω→ℝ) (hZ : StronglyMeasurable[F 0] Z) :
    (∫ ω,Real.cos (Z ω)*sourceRieszBrownianProcess P F T B hB hBa hind g t ω ∂P)=0 ∧
    (∫ ω,Real.sin (Z ω)*sourceRieszBrownianProcess P F T B hB hBa hind g t ω ∂P)=0 := by
  have hc : StronglyMeasurable[F 0] (fun ω=>Real.cos (Z ω)) := Real.continuous_cos.comp_stronglyMeasurable hZ
  have hs : StronglyMeasurable[F 0] (fun ω=>Real.sin (Z ω)) := Real.continuous_sin.comp_stronglyMeasurable hZ
  have hcL : MemLp (fun ω=>Real.cos (Z ω)) 2 P :=
    MemLp.of_bound (hc.mono (F.le 0)).aestronglyMeasurable 1
      (ae_of_all _ fun ω=>by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (Z ω))
  have hsL : MemLp (fun ω=>Real.sin (Z ω)) 2 P :=
    MemLp.of_bound (hs.mono (F.le 0)).aestronglyMeasurable 1
      (ae_of_all _ fun ω=>by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (Z ω))
  exact ⟨(sourceRieszBrownianProcess_initial_weighted_zero_no_continuity P F T B hB hBa hind g t _ hc hcL).2,
    (sourceRieszBrownianProcess_initial_weighted_zero_no_continuity P F T B hB hBa hind g t _ hs hsL).2⟩

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszBrownianProcess_zero_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcess_zero_no_continuity
#check @DGRHS.Commutator.sourceRieszBrownianProcess_terminal_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcess_terminal_no_continuity
#check @DGRHS.Commutator.sourceRieszBrownianProcess_second_moment_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcess_second_moment_no_continuity
#check @DGRHS.Commutator.sourceRieszBrownianProcess_initial_weighted_zero_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcess_initial_weighted_zero_no_continuity
#check @DGRHS.Commutator.sourceRieszBrownianProcess_initial_phase_zero_no_continuity
#print axioms DGRHS.Commutator.sourceRieszBrownianProcess_initial_phase_zero_no_continuity
