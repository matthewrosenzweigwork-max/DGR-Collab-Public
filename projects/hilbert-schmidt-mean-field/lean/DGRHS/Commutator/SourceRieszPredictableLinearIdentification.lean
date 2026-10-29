import DGRHS.Commutator.SourceRieszPhysicalStoppedFamily

/-! Equality of actual predictable L2 classes from simultaneous physical
coefficient identities, and finite weighted linearity at the integrand level. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace DGRHS.Commutator
variable {Ω α : Type*} [mΩ : MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P] (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0)

lemma sourceRieszPredictable_eq_trim_of_indistinguishable
    (U V : ℝ≥0→Ω→ℝ) (hU : IsStronglyPredictable F U) (hV : IsStronglyPredictable F V)
    (he : ∀ᵐ ω ∂P,∀ r,U r ω=V r ω) :
    Function.uncurry U=ᵐ[sourceRieszBrownianPredictableMeasure P F T] Function.uncurry V := by
  have hp : Function.uncurry U=ᵐ[(sourceRieszBrownianTimeOn T).prod P] Function.uncurry V := by
    apply (Measure.ae_prod_iff_ae_ae
      ((hU.mono (sourceRiesz_predictable_le_product F)).measurableSet_eq_fun
        (hV.mono (sourceRiesz_predictable_le_product F)))).mpr
    exact ae_of_all _ (fun r=>he.mono (fun ω hω=>hω r))
  exact StronglyMeasurable.ae_eq_trim_of_stronglyMeasurable
    (sourceRiesz_predictable_le_product F) hU hV hp

lemma sourceRieszPredictableBoundedL2_linear_combination [Fintype α]
    (U : ℝ≥0→Ω→ℝ) (hU : IsStronglyPredictable F U) (K : ℝ) (hUb : ∀ r ω,‖U r ω‖≤K)
    (V : α→ℝ≥0→Ω→ℝ) (hV : ∀ a,IsStronglyPredictable F (V a))
    (L : ℝ) (hVb : ∀ a r ω,‖V a r ω‖≤L) (θ : α→ℝ)
    (he : ∀ᵐ ω ∂P,∀ r,U r ω=∑ a,θ a*V a r ω) :
    sourceRieszPredictableBoundedL2 P F T U hU K hUb=
      ∑ a,θ a • sourceRieszPredictableBoundedL2 P F T (V a) (hV a) L (hVb a) := by
  let g := fun a=>sourceRieszPredictableBoundedL2 P F T (V a) (hV a) L (hVb a)
  have hsum : IsStronglyPredictable F (fun r ω=>∑ a,θ a*V a r ω) := by
    change StronglyMeasurable[F.predictable] (fun p:ℝ≥0×Ω=>∑ a,θ a*V a p.1 p.2)
    have hh := Finset.stronglyMeasurable_sum Finset.univ (fun a _=>(hV a).const_mul (θ a))
    convert hh using 1
    funext p
    simp only [Function.uncurry,Finset.sum_apply]
  have het := sourceRieszPredictable_eq_trim_of_indistinguishable P F T U _ hU hsum he
  have hu := (MemLp.of_bound (p:=2) hU.aestronglyMeasurable K
    (ae_of_all (sourceRieszBrownianPredictableMeasure P F T) (fun p=>hUb p.1 p.2))).coeFn_toLp
  have hv a := (MemLp.of_bound (p:=2) (hV a).aestronglyMeasurable L
    (ae_of_all (sourceRieszBrownianPredictableMeasure P F T) (fun p=>hVb a p.1 p.2))).coeFn_toLp
  change (sourceRieszPredictableBoundedL2 P F T U hU K hUb : ℝ≥0×Ω→ℝ)=ᵐ[
    sourceRieszBrownianPredictableMeasure P F T] Function.uncurry U at hu
  change ∀ a,(g a : ℝ≥0×Ω→ℝ)=ᵐ[sourceRieszBrownianPredictableMeasure P F T]
    Function.uncurry (V a) at hv
  change sourceRieszPredictableBoundedL2 P F T U hU K hUb=∑ a,θ a • g a
  apply Lp.ext
  filter_upwards [hu,het,Lp.coeFn_finsetSum Finset.univ (fun a=>θ a • g a),
    ae_all_iff.2 (fun a=>Lp.coeFn_smul (θ a) (g a)),ae_all_iff.2 hv]
      with p hup hep hsp hmp hvp
  rw [hup,hep,hsp]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [hmp a]
  simpa only [Pi.smul_apply,smul_eq_mul,Function.uncurry] using congrArg (fun x:ℝ=>θ a*x) (hvp a).symm

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszPredictable_eq_trim_of_indistinguishable
#print axioms DGRHS.Commutator.sourceRieszPredictable_eq_trim_of_indistinguishable
#check @DGRHS.Commutator.sourceRieszPredictableBoundedL2_linear_combination
#print axioms DGRHS.Commutator.sourceRieszPredictableBoundedL2_linear_combination
