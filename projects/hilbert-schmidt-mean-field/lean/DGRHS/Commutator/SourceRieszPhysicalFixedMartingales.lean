import DGRHS.Commutator.SourceRieszPhysicalStoppedFamily
import DGRHS.Commutator.SourceRieszBrownianRealPhase

/-! Candidate: fixed individual actual martingales are chosen before all weights.
The real-time normalization is the unscaled empirical-test martingale used by
the original dynamic endpoint. Joint measurability and zero initial value are
proved for these chosen versions; their identification with the actual common
Brownian integrals holds on one event for all times. No particle Itô identity,
expected phase identity, or independence from the completed noise is asserted. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

lemma exists_sourceRieszBrownianFamily_real_normalized_versions
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (N k : ℕ) (hN : 0<N)
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hB : SourceRieszFilteredBrownianFamily P F B)
    (g : Fin k→(Fin N×ι)→Lp ℝ 2 (sourceRieszBrownianPredictableMeasure P F T)) :
    ∃ m : Fin k→ℝ→Ω→ℝ,
      (∀ a,Measurable (Function.uncurry (m a))) ∧
      (∀ a ω,m a 0 ω=0) ∧
      (∀ a,∀ᵐ ω ∂P,Continuous (fun r : ℝ => m a r ω)) ∧
      (∀ a,Martingale (fun r : ℝ≥0 => m a (r:ℝ)) F P) ∧
      (∀ a (r : ℝ≥0),MemLp (m a (r:ℝ)) 2 P) ∧
      ∀ᵐ ω ∂P,∀ (a : Fin k) (r : ℝ≥0),
        Real.sqrt N*m a r ω=sourceRieszBrownianFamilyProcess P F B T (g a) r ω := by
  classical
  choose R hR hR0 he hc using fun a : Fin k =>
    exists_sourceRieszBrownianFamily_predictable_phase P F B hB T (g a)
      (fun _ => 0) stronglyMeasurable_const
  let J := fun a => sourceRieszBrownianRealPhaseProcess (fun _ => 0) (R a)
  let m := fun a r ω => J a r ω / Real.sqrt N
  have hn : Real.sqrt (N:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hN))
  have hscale (a : Fin k) (r : ℝ) (ω : Ω) : Real.sqrt N*m a r ω=J a r ω := by
    dsimp only [m]
    field_simp [hn]
  have heR (a : Fin k) (r : ℝ≥0) :
      sourceRieszBrownianFamilyProcess P F B T (g a) r =ᵐ[P] R a r := by
    filter_upwards [he a] with ω hω
    simpa only [zero_add] using (hω r).symm
  have hmR (a : Fin k) : Martingale (R a) F P :=
    (sourceRieszBrownianFamilyProcess_martingale P F B hB T (g a)).1.congr
      (hR a).stronglyAdapted (heR a)
  have hmfun (a : Fin k) : (fun r : ℝ≥0 => m a (r:ℝ)) =
      (Real.sqrt (N:ℝ))⁻¹ • R a := by
    funext r ω
    have hr : Real.toNNReal (r:ℝ)=r := Subtype.ext (Real.coe_toNNReal _ r.coe_nonneg)
    simp only [m,J,sourceRieszBrownianRealPhaseProcess,hr,sub_zero,
      Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  refine ⟨m,?_,?_,?_,?_,?_,?_⟩
  · intro a
    exact (measurable_sourceRieszBrownianRealPhaseProcess F (fun _ => 0)
      stronglyMeasurable_const (R a) (hR a)).div_const _
  · intro a ω
    dsimp only [m,J]
    rw [sourceRieszBrownianRealPhaseProcess_zero (fun _ => 0) (R a) (hR0 a) ω,zero_div]
  · intro a
    filter_upwards [sourceRieszBrownianRealPhaseProcess_continuous P (fun _ => 0) (R a) (hc a)]
      with ω hω
    exact hω.div_const _
  · intro a
    rw [hmfun a]
    exact (hmR a).smul _
  · intro a r
    have hL : MemLp (R a r) 2 P :=
      (memLp_congr_ae (heR a r)).mp
        ((sourceRieszBrownianFamilyProcess_martingale P F B hB T (g a)).2.1 r)
    have hm := congrFun (hmfun a) r
    rw [hm]
    convert hL.const_mul (Real.sqrt (N:ℝ))⁻¹ using 1 <;>
      ext ω <;> simp only [Pi.smul_apply,smul_eq_mul]
  · filter_upwards [ae_all_iff.2 (fun a =>
      sourceRieszBrownianRealPhaseProcess_ae_eq P (fun _ => 0) (R a)
        (sourceRieszBrownianFamilyProcess P F B T (g a)) (he a))] with ω hω
    intro a r
    exact (hscale a r ω).trans (hω a r)

theorem exists_sourceRiesz_physical_fixed_martingales
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (N k : ℕ) (hN : 0<N) (t : Fin k→ℝ≥0) (c : ℝ) (f : Fin k→ℝ→E→ℝ)
    (hgrad : ∀ a,ContinuousOn (fun p:ℝ×E => gradient (f a p.1) p.2)
      (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ≥0→Ω→Fin N→E) (hXa : ∀ i,StronglyAdapted F (fun r ω => X r ω i))
    (hXc : ∀ i,∀ᵐ ω ∂P,Continuous (fun r => X r ω i))
    (B : (Fin N×ι)→ℝ≥0→Ω→ℝ) (hB : SourceRieszFilteredBrownianFamily P F B) :
    ∃ V : Fin k→(Fin N×ι)→ℝ≥0→Ω→ℝ,
    ∃ hV : ∀ a b,IsStronglyPredictable F (V a b),
    ∃ hVb : ∀ a b r ω,‖V a b r ω‖≤|c| * (G:ℝ),
      (∀ a b r ω,t a<r → V a b r ω=0) ∧
      (∀ᵐ ω ∂P,∀ a b r,V a b r ω=
        c*(sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) ∧
      let g := fun a b => sourceRieszPredictableBoundedL2 P F T (V a b) (hV a b)
        (|c| * (G:ℝ)) (hVb a b)
      ∃ m : Fin k→ℝ→Ω→ℝ,
        (∀ a,Measurable (Function.uncurry (m a))) ∧
        (∀ a ω,m a 0 ω=0) ∧
        (∀ a,∀ᵐ ω ∂P,Continuous (fun r : ℝ => m a r ω)) ∧
        (∀ a,Martingale (fun r : ℝ≥0 => m a (r:ℝ)) F P) ∧
        (∀ a (r : ℝ≥0),MemLp (m a (r:ℝ)) 2 P) ∧
        (∀ᵐ ω ∂P,∀ (a : Fin k) (r : ℝ≥0),
          Real.sqrt N*m a r ω=sourceRieszBrownianFamilyProcess P F B T (g a) r ω) ∧
        ∀ θ : Fin k→ℝ,∀ᵐ ω ∂P,∀ r:ℝ≥0,
          sourceRieszBrownianFamilyProcess P F B T (fun b => ∑ a,θ a • g a b) r ω=
            ∑ a,θ a*(Real.sqrt N*m a (min (r:ℝ) (t a:ℝ)) ω) := by
  classical
  obtain ⟨V,hV,hVb,hVz,hVe,hId⟩ := exists_sourceRiesz_physical_finite_stopped_family
    P F T N k t c f hgrad G hb X hXa hXc B hB
  refine ⟨V,hV,hVb,hVz,hVe,?_⟩
  intro g
  obtain ⟨m,hmm,hm0,hmc,hMart,hLp,hme⟩ := exists_sourceRieszBrownianFamily_real_normalized_versions
    P F T N k hN B hB g
  refine ⟨m,hmm,hm0,hmc,hMart,hLp,hme,?_⟩
  intro θ
  filter_upwards [hId θ,hme] with ω hIω hmω
  intro r
  rw [hIω r]
  apply Finset.sum_congr rfl
  intro a _
  simpa only [NNReal.coe_min] using
    congrArg (fun z : ℝ => θ a*z) (hmω a (min r (t a))).symm

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceRieszBrownianFamily_real_normalized_versions
#print axioms DGRHS.Commutator.exists_sourceRieszBrownianFamily_real_normalized_versions
#check @DGRHS.Commutator.exists_sourceRiesz_physical_fixed_martingales
#print axioms DGRHS.Commutator.exists_sourceRiesz_physical_fixed_martingales
