import DGRHS.Commutator.SourceRieszBrownianFamilyStopping

/-! Pointwise supported versions of the individual physical gradient
coefficients, followed by simultaneous finite weighted/stopped identification
of the actual common-Brownian-family integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma exists_sourceRiesz_particle_stopped_coordinate_predictable_support
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (a : ℝ≥0) (c : ℝ) (f : ℝ→E→ℝ)
    (hgrad : ContinuousOn (fun p:ℝ×E=>gradient (f p.1) p.2) (Icc 0 (a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ r∈Icc 0 (a:ℝ),∀ z,‖gradient (f r) z‖≤(G:ℝ))
    (X : ℝ≥0→Ω→E) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun r=>X r ω)) (j : ι) :
    ∃ U : ℝ≥0→Ω→ℝ,IsStronglyPredictable F U ∧
      (∀ r ω,‖U r ω‖≤|c| * (G:ℝ)) ∧
      (∀ r ω,a<r → U r ω=0) ∧
      ∀ᵐ ω ∂P,∀ r,U r ω=c*(sourceRieszStoppedGradient (a:ℝ) f (r:ℝ) (X r ω)) j := by
  obtain ⟨V,hV,hVb,he⟩ := exists_sourceRiesz_particle_stopped_coordinate_predictable_ae
    P F a f hgrad G hb X hXa hXc j
  let U := fun (r:ℝ≥0) ω=>(if r≤a then (1:ℝ) else 0)*(c*V r ω)
  have hcut : IsStronglyPredictable F (fun (r:ℝ≥0) (_:Ω)=>if r≤a then (1:ℝ) else 0) :=
    sourceRiesz_adapted_predictable_of_leftContinuous (fun _=>stronglyMeasurable_const)
      (fun _ r=>sourceRiesz_cutoff_leftContinuous a r)
  refine ⟨U,hcut.mul (hV.const_mul c),?_,?_,?_⟩
  · intro r ω
    by_cases hr : r≤a
    · simpa only [U,if_pos hr,one_mul,norm_mul,Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left (hVb r ω) (abs_nonneg c)
    · simp only [U,if_neg hr,zero_mul,norm_zero]
      positivity
  · intro r ω hr
    simp only [U,if_neg (not_le.mpr hr),zero_mul]
  · filter_upwards [he] with ω hω
    intro r
    by_cases hr : r≤a
    · simp only [U,if_pos hr,one_mul,hω r]
    · have hr' : ¬(r:ℝ)∈Icc 0 (a:ℝ) := fun hh=>hr hh.2
      simp [U,hr,sourceRieszStoppedGradient,hr']

theorem exists_sourceRiesz_physical_finite_stopped_family
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (N k : ℕ) (t : Fin k→ℝ≥0) (c : ℝ) (f : Fin k→ℝ→E→ℝ)
    (hgrad : ∀ a,ContinuousOn (fun p:ℝ×E=>gradient (f a p.1) p.2)
      (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ≥0→Ω→Fin N→E) (hXa : ∀ i,StronglyAdapted F (fun r ω=>X r ω i))
    (hXc : ∀ i,∀ᵐ ω ∂P,Continuous (fun r=>X r ω i))
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hB : SourceRieszFilteredBrownianFamily P F B) :
    ∃ U : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ,
    ∃ hU : ∀ a b,IsStronglyPredictable F (U a b),
    ∃ hUb : ∀ a b r ω,‖U a b r ω‖≤|c| * (G:ℝ),
      (∀ a b r ω,t a<r → U a b r ω=0) ∧
      (∀ᵐ ω ∂P,∀ a b r,U a b r ω=
        c*(sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) ∧
      let g := fun a b=>sourceRieszPredictableBoundedL2 P F T (U a b) (hU a b)
        (|c| * (G:ℝ)) (hUb a b)
      ∀ θ:Fin k→ℝ,∀ᵐ ω ∂P,∀ r,
        sourceRieszBrownianFamilyProcess P F B T (fun b=>∑ a,θ a • g a b) r ω=
          ∑ a,θ a*sourceRieszBrownianFamilyProcess P F B T (g a) (min r (t a)) ω := by
  classical
  choose U hU hUb hz he using fun (a:Fin k) (b:Fin N×ι)=>
    exists_sourceRiesz_particle_stopped_coordinate_predictable_support P F (t a) c (f a)
      (hgrad a) G (hb a) (fun r ω=>X r ω b.1) (hXa b.1) (hXc b.1) b.2
  refine ⟨U,hU,hUb,hz,?_,?_⟩
  · filter_upwards [ae_all_iff.2 (fun a=>ae_all_iff.2 (fun b=>he a b))] with ω hω
    exact hω
  · intro g θ
    exact sourceRieszBrownianFamilyProcess_finite_stopped_sum P F T B hB t θ g
      (fun a b=>sourceRieszPredictableBoundedL2_stopped_support P F T
        (U a b) (hU a b) (|c| * (G:ℝ)) (hUb a b) (t a) (hz a b))

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceRiesz_particle_stopped_coordinate_predictable_support
#print axioms DGRHS.Commutator.exists_sourceRiesz_particle_stopped_coordinate_predictable_support
#check @DGRHS.Commutator.exists_sourceRiesz_physical_finite_stopped_family
#print axioms DGRHS.Commutator.exists_sourceRiesz_physical_finite_stopped_family
