/- Native exponential/power domination: a proper positive exponential moment
and a genuine lower bound supply the unbounded one-body L2 obligation. -/
import DGRHS.Gaussian.LogPhysicalConvolution
import DGRHS.Gaussian.SingularLogIntegrability
import DGRHS.Attractive.SourceLogUniform
import Mathlib.Analysis.Complex.Exponential
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive
variable {S : Type*} [MeasurableSpace S]

lemma memLp_two_of_lower_bound_exp (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S→ℝ) (hF : AEStronglyMeasurable F μ) (L θ : ℝ) (hθ : 0<θ)
    (hlower : ∀ᵐ x ∂μ,L≤F x)
    (hexp : Integrable (fun x=>Real.exp (θ*F x)) μ) : MemLp F 2 μ := by
  apply (memLp_two_iff_integrable_sq hF).mpr
  apply ((integrable_const (L^2)).add (hexp.const_mul (2/θ^2))).mono'
    (hF.pow 2)
  filter_upwards [hlower] with x hx
  change ‖(F x)^2‖ ≤ L^2+(2/θ^2)*Real.exp (θ*F x)
  rw [Real.norm_eq_abs,abs_sq]
  change (F x)^2≤L^2+(2/θ^2)*Real.exp (θ*F x)
  by_cases hf : 0≤F x
  · have hp := Real.pow_div_factorial_le_exp (θ*F x) (mul_nonneg hθ.le hf) 2
    norm_num only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_ofNat,
      Nat.cast_one,mul_one] at hp
    have ht : 0<θ^2 := sq_pos_of_pos hθ
    have hpow : (F x)^2≤(2/θ^2)*Real.exp (θ*F x) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ ht).mpr
      nlinarith
    linarith [sq_nonneg L]
  · have hneg : F x<0 := lt_of_not_ge hf
    have hsq : (F x)^2≤L^2 := by nlinarith
    exact hsq.trans (le_add_of_nonneg_right (by positivity))

theorem attractiveLogPotential_memLp_two {ι : Type*} [Fintype ι]
    (β : ℝ) (hβ : 0<β) (hd : 0<(Fintype.card ι:ℝ))
    (ρ : EuclideanSpace ℝ ι→ℝ) (M : ℝ) (hM : 0≤M)
    [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hpair : Integrable DGRHS.Gaussian.logPhysicalPair
      ((DGRHS.Gaussian.gaussianRieszDensityMeasure ρ).prod
        (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)))
    (hexp : Integrable (fun x=>Real.exp (4*β*DGRHS.potential
      (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) attractiveLogInteraction x))
      (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)) :
    MemLp (DGRHS.potential (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)
      attractiveLogInteraction) 2 (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ) := by
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  let q := (Fintype.card ι:ℝ)/4
  have hq : 0<q := by dsimp [q];positivity
  have hdim : 0<(Fintype.card ι:ℝ)/2-q := by dsimp [q];linarith
  have he (x : EuclideanSpace ℝ ι) : DGRHS.potential μ attractiveLogInteraction x =
      -DGRHS.Gaussian.logPhysicalPotential μ x := by
    simp only [DGRHS.potential,attractiveLogInteraction,
      DGRHS.Gaussian.logPhysicalPotential,DGRHS.Gaussian.logPhysicalPair,integral_neg,neg_neg]
  have hm : AEStronglyMeasurable (DGRHS.potential μ attractiveLogInteraction) μ := by
    have hef : DGRHS.potential μ attractiveLogInteraction =
        (fun x => -DGRHS.Gaussian.logPhysicalPotential μ x) := funext he
    rw [hef]
    have hg := DGRHS.Gaussian.measurable_logPhysicalPair (E:=EuclideanSpace ℝ ι)
    exact hg.stronglyMeasurable.integral_prod_right'.neg.aestronglyMeasurable
  apply memLp_two_of_lower_bound_exp μ _ hm
    (-DGRHS.Gaussian.gaussianRieszPhysicalPotentialConstant q M ι) (4*β)
    (by positivity) _ hexp
  apply Filter.Eventually.of_forall
  intro x
  rw [he]
  exact neg_le_neg (DGRHS.Gaussian.logPhysicalPotential_proper_bounds
    q hq hdim ρ M hM hρ hpair x).2.2
end DGRHS.Attractive
#check @DGRHS.Attractive.attractiveLogPotential_memLp_two
#print axioms DGRHS.Attractive.memLp_two_of_lower_bound_exp
#print axioms DGRHS.Attractive.attractiveLogPotential_memLp_two
