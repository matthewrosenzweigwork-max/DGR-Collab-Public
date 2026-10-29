import DGRHS.Commutator.SourceRieszParticlePredictableAE

/-! The actual finite weighted stopped particle-gradient coordinates admit
bounded predictable versions on the original supplied filtration. Only adapted
AE-continuous particle paths and the stated joint gradient continuity and bound
are used; no process bracket is an input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem exists_sourceRiesz_finite_stopped_coefficients_predictable_ae
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (N k : ℕ) (t : Fin k→ℝ≥0) (θ : Fin k→ℝ) (c : ℝ)
    (f : Fin k→ℝ→E→ℝ)
    (hgrad : ∀ a,ContinuousOn (fun p : ℝ×E=>gradient (f a p.1) p.2)
      (Icc 0 (t a:ℝ) ×ˢ univ))
    (G : ℝ≥0) (hb : ∀ a,∀ r∈Icc 0 (t a:ℝ),∀ z,‖gradient (f a r) z‖≤(G:ℝ))
    (X : ℝ≥0→Ω→Fin N→E) (hXa : ∀ i,StronglyAdapted F (fun r ω=>X r ω i))
    (hXc : ∀ i,∀ᵐ ω ∂P,Continuous (fun r=>X r ω i)) :
    ∃ U : (Fin N×ι)→ℝ≥0→Ω→ℝ,
      (∀ b,IsStronglyPredictable F (U b)) ∧
      (∀ b r ω,‖U b r ω‖≤|c| *((G:ℝ)*(∑ a,|θ a|))) ∧
      ∀ᵐ ω ∂P,∀ r b,U b r ω=
        c*((∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2) := by
  classical
  choose V hp hVb he using fun (a:Fin k) (b:Fin N×ι)=>
    exists_sourceRiesz_particle_stopped_coordinate_predictable_ae P F (t a) (f a)
      (hgrad a) G (hb a) (fun r ω=>X r ω b.1) (hXa b.1) (hXc b.1) b.2
  let U := fun (b:Fin N×ι) r ω=>c*(∑ a,θ a*V a b r ω)
  have hUp (b : Fin N×ι) : IsStronglyPredictable F (U b) := by
    change StronglyMeasurable[F.predictable] (Function.uncurry (U b))
    have hp' (a : Fin k) : StronglyMeasurable[F.predictable]
        (fun p:ℝ≥0×Ω=>θ a*V a b p.1 p.2) := (hp a b).const_mul (θ a)
    have hm := (Finset.stronglyMeasurable_sum Finset.univ (fun a _=>hp' a)).const_mul c
    convert hm using 1
    funext p
    simp only [U,Function.uncurry,Finset.sum_apply]
  have hUb (b : Fin N×ι) (r : ℝ≥0) (ω : Ω) :
      ‖U b r ω‖≤|c| *((G:ℝ)*(∑ a,|θ a|)) := by
    dsimp only [U]
    rw [norm_mul,Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
    calc
      ‖∑ a,θ a*V a b r ω‖ ≤ ∑ a,‖θ a*V a b r ω‖ := norm_sum_le _ _
      _ ≤ ∑ a,|θ a| *(G:ℝ) := Finset.sum_le_sum fun a _=>by
        rw [norm_mul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hVb a b r ω) (abs_nonneg _)
      _ = (G:ℝ)*(∑ a,|θ a|) := by rw [←Finset.sum_mul,mul_comm]
  refine ⟨U,hUp,hUb,?_⟩
  filter_upwards [ae_all_iff.2 (fun a=>ae_all_iff.2 (fun b=>he a b))] with ω hω
  intro r b
  dsimp only [U]
  congr 1
  calc
    ∑ a,θ a*V a b r ω = ∑ a,θ a*
      (sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2 :=
        Finset.sum_congr rfl (fun a _=>congrArg (fun z:ℝ=>θ a*z) (hω a b r))
    _ = (∑ a,θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) b.2 := by
      have hh := map_sum (PiLp.projₗ (𝕜:=ℝ) 2 (β:=fun _:ι=>ℝ) b.2)
        (fun a=>θ a • sourceRieszStoppedGradient (t a:ℝ) (f a) (r:ℝ) (X r ω b.1)) Finset.univ
      simpa only [PiLp.projₗ_apply,PiLp.smul_apply,smul_eq_mul] using hh.symm

end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceRiesz_finite_stopped_coefficients_predictable_ae
#print axioms DGRHS.Commutator.exists_sourceRiesz_finite_stopped_coefficients_predictable_ae
