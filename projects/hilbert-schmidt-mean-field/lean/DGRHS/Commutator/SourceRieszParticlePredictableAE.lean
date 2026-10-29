import DGRHS.Commutator.SourceRieszBrownianFamily

/-! Predictable versions of the actual stopped particle-gradient coordinates
on the supplied filtration, for AE-continuous adapted particle paths. We take
a predictable version of the continuously clamped gradient coordinate, clamp
its scalar range to its proved gradient bound, and then apply the deterministic
left-continuous horizon cutoff. The result agrees with the physical coefficient
simultaneously at every time almost surely and is genuinely bounded predictable
L2 data for the frozen integral construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_particle_stopped_coordinate_predictable_ae
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (T : ℝ≥0) (f : ℝ→E→ℝ)
    (hgrad : ContinuousOn (fun p : ℝ×E=>gradient (f p.1) p.2) (Icc 0 (T:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ r∈Icc 0 (T:ℝ),∀ z,‖gradient (f r) z‖≤(G:ℝ))
    (X : ℝ≥0→Ω→E) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun r=>X r ω)) (j : ι) :
    ∃ U : ℝ≥0→Ω→ℝ,IsStronglyPredictable F U ∧
      (∀ r ω,‖U r ω‖≤(G:ℝ)) ∧
      ∀ᵐ ω ∂P,∀ r,U r ω=(sourceRieszStoppedGradient (T:ℝ) f (r:ℝ) (X r ω)) j := by
  let ge := fun p : ℝ×E=>gradient (f (projIcc 0 (T:ℝ) T.coe_nonneg p.1)) p.2
  have hge : Continuous ge := by
    have hc : Continuous (fun p : ℝ×E=>
        ((projIcc 0 (T:ℝ) T.coe_nonneg p.1 : ℝ),p.2)) :=
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_fst)).prodMk continuous_snd
    exact hgrad.comp_continuous hc (fun p=>
      ⟨(projIcc 0 (T:ℝ) T.coe_nonneg p.1).property,mem_univ _⟩)
  let Y := fun (r : ℝ≥0) ω=>(ge ((r:ℝ),X r ω)) j
  have hYa : StronglyAdapted F Y := fun r=>
    (PiLp.continuous_apply 2 (fun _:ι=>ℝ) j).comp_stronglyMeasurable
      (hge.comp_stronglyMeasurable (stronglyMeasurable_const.prodMk (hXa r)))
  have hYc : ∀ᵐ ω ∂P,Continuous (fun r=>Y r ω) := by
    filter_upwards [hXc] with ω hω
    exact (PiLp.continuous_apply 2 (fun _:ι=>ℝ) j).comp
      (hge.comp (NNReal.continuous_coe.prodMk hω))
  have hYb (r : ℝ≥0) (ω : Ω) : |Y r ω|≤(G:ℝ) := by
    exact (PiLp.norm_apply_le (ge ((r:ℝ),X r ω)) j).trans
      (hb _ (projIcc 0 (T:ℝ) T.coe_nonneg (r:ℝ)).property _)
  let V := sourceRieszPredictableVersion F Y hYa
  let ψ := fun z:ℝ=>max (-(G:ℝ)) (min (G:ℝ) z)
  have hψ : Continuous ψ := continuous_const.max (continuous_const.min continuous_id)
  have hψb (z : ℝ) : |ψ z|≤(G:ℝ) := by
    exact abs_le.mpr ⟨le_max_left _ _,max_le (by linarith [G.coe_nonneg]) (min_le_left _ _)⟩
  let U := fun (r:ℝ≥0) ω=>(if r≤T then (1:ℝ) else 0)*ψ (V r ω)
  have hc : IsStronglyPredictable F (fun (r:ℝ≥0) (_:Ω)=>if r≤T then (1:ℝ) else 0) :=
    sourceRiesz_adapted_predictable_of_leftContinuous (fun _=>stronglyMeasurable_const)
      (fun _ r=>sourceRiesz_cutoff_leftContinuous T r)
  have hp : IsStronglyPredictable F U :=
    hc.mul (hψ.comp_stronglyMeasurable (sourceRieszPredictableVersion_predictable F Y hYa))
  refine ⟨U,hp,?_,?_⟩
  · intro r ω
    by_cases hr : r≤T
    · simpa only [U,if_pos hr,one_mul,Real.norm_eq_abs] using hψb (V r ω)
    · simp only [U,if_neg hr,zero_mul,norm_zero]
      exact G.coe_nonneg
  · filter_upwards [sourceRieszPredictableVersion_ae_eq P F Y hYa hYc] with ω hω
    intro r
    have hy := abs_le.mp (hYb r ω)
    change (if r≤T then (1:ℝ) else 0)*ψ (V r ω)=_
    have hv : V r ω=Y r ω := hω r
    rw [hv,show ψ (Y r ω)=Y r ω from by
      dsimp only [ψ]
      rw [min_eq_right hy.2,max_eq_right hy.1]]
    by_cases hr : r≤T
    · have hr' : (r:ℝ)∈Icc 0 (T:ℝ) := ⟨r.coe_nonneg,hr⟩
      simp only [if_pos hr,one_mul,Y,ge,sourceRieszStoppedGradient,if_pos hr',
        projIcc_of_mem T.coe_nonneg hr']
    · have hr' : ¬(r:ℝ)∈Icc 0 (T:ℝ) := fun hh=>hr hh.2
      simp [hr,sourceRieszStoppedGradient,hr']

variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

def sourceRieszPredictableBoundedL2 (U : ℝ≥0→Ω→ℝ) (hU : IsStronglyPredictable F U)
    (K : ℝ) (hb : ∀ r ω,‖U r ω‖≤K) :
    Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T) :=
  (MemLp.of_bound hU.aestronglyMeasurable K (ae_of_all _ (fun p=>hb p.1 p.2))).toLp (Function.uncurry U)

lemma sourceRieszPredictableBoundedL2_coe_product (U : ℝ≥0→Ω→ℝ) (hU : IsStronglyPredictable F U)
    (K : ℝ) (hb : ∀ r ω,‖U r ω‖≤K) :
    (sourceRieszPredictableBoundedL2 P F T U hU K hb : ℝ≥0×Ω→ℝ)=ᵐ[(sourceRieszBrownianTimeOn T).prod P]
      Function.uncurry U := by
  have he := (MemLp.of_bound (p:=2) hU.aestronglyMeasurable K
    (ae_of_all (sourceRieszBrownianPredictableMeasure P F T) (fun p=>hb p.1 p.2))).coeFn_toLp
  exact ae_of_ae_trim (sourceRiesz_predictable_le_product F) he

lemma sourceRieszPredictableBoundedL2_energy (U : ℝ≥0→Ω→ℝ) (hU : IsStronglyPredictable F U)
    (K : ℝ) (hb : ∀ r ω,‖U r ω‖≤K) :
    ∀ᵐ ω ∂P,∀ t,sourceRieszBrownianEnergy P F T
      (sourceRieszPredictableBoundedL2 P F T U hU K hb) t ω=
        ∫ r in Ioc 0 t,(U r ω)^2 ∂sourceRieszBrownianTimeOn T := by
  have he := sourceRieszPredictableBoundedL2_coe_product P F T U hU K hb
  have hs := (Measure.measurePreserving_swap (μ:=P) (ν:=sourceRieszBrownianTimeOn T)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  intro t
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [hω] with r hr _
  exact congrArg (fun z:ℝ=>z^2) hr

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceRiesz_particle_stopped_coordinate_predictable_ae
#print axioms DGRHS.Commutator.exists_sourceRiesz_particle_stopped_coordinate_predictable_ae
#check @DGRHS.Commutator.sourceRieszPredictableBoundedL2
#print axioms DGRHS.Commutator.sourceRieszPredictableBoundedL2
#check @DGRHS.Commutator.sourceRieszPredictableBoundedL2_coe_product
#print axioms DGRHS.Commutator.sourceRieszPredictableBoundedL2_coe_product
#check @DGRHS.Commutator.sourceRieszPredictableBoundedL2_energy
#print axioms DGRHS.Commutator.sourceRieszPredictableBoundedL2_energy
