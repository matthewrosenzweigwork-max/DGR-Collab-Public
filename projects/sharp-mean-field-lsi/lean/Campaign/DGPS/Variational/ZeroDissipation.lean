import DGPS.Analysis.RelativeFisher
import DGPS.Analysis.WeightedForms
import DGPS.Model.ScalarRate
import DGPS.Variational.FrozenGibbs

/-!
# Zero dissipation and frozen fixed points under Lipschitz data (DEF033)

INTERFACES/common_lemmas.md DEF033.

For Lipschitz interaction data `A` and a weak-drift provider `b`:

* for every absolute-admissible `ρ`, `D(ρ) = 0` iff `ρ m = P(ρ m)`, where `P = frozenGibbs A`;
* every probability `ν` with `ν = P ν` has a positive Lipschitz density (that of `P ν`), is the
  measure `ρ m` of an absolute-admissible `ρ` (`√p`), and that `ρ` has zero dissipation.

Route: the relative square root `v = u p^(-1/2)` has the weak gradient given by the product rule
with the Lipschitz factor `p^(-1/2)`; the pointwise identity `4 p |∇v|² = |2∇u - u ∇log p|²` of the
positive-reference Fisher identity, together with `∇log p = -b_ρ` (the frozen potential of `ρ m` is
`V + W * (ρ m)`), identifies the dissipation score with `2 √p ∇v`; a zero weak gradient on the
connected torus makes `v` constant, and mass one normalizes the constant.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS

variable {d : ℕ}

theorem def033_integral_coordPartial (φ : Torus d → ℝ) (hφ : IsSmoothPeriodic φ) (j : Fin d) :
    ∫ x, coordPartial j φ x ∂haar d = 0 := by
  have h := (isWeakGradient_const (d := d) 1).ibp φ hφ j
  simpa using h

theorem def033_isWeakGradientLp_one {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) : IsWeakGradientLp 1 u g :=
  ⟨h.memLp.mono_exponent one_le_two, h.memLp_grad.mono_exponent one_le_two, h.ibp⟩

/-- The logarithm of the frozen Gibbs density of `ρ m` has the `L¹` weak gradient `-b_ρ`. -/
theorem def033_log_weakGradient (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) :
    IsWeakGradientLp 1 (fun x => Real.log ((frozenGibbs A (densityMeasure ρ)).density x))
      (fun x => -(b.force ρ x)) := by
  set ν := densityMeasure ρ with hν
  have hlog : ∀ x, Real.log ((frozenGibbs A ν).density x) =
      -interactionPotential A ρ x - Real.log (frozenPartition A ν) := by
    intro x
    show Real.log (Real.exp (-frozenPotential A ν x) / frozenPartition A ν) = _
    rw [Real.log_div (Real.exp_pos _).ne' (frozenPartition_pos A ν).ne', Real.log_exp]
    rfl
  have hw := b.weak_gradient ρ
  have hbd : MemLp (interactionPotential A ρ) ∞ (haar d) := by
    refine memLp_top_of_bound (C := frozenSupBound A)
      (frozenPotential_continuous A (ν : Measure (Torus d))).measurable.aestronglyMeasurable
      ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_frozenPotential_le A (ν : Measure (Torus d)) x
  have e : (fun x => Real.log ((frozenGibbs A ν).density x)) =
      fun x => -interactionPotential A ρ x - Real.log (frozenPartition A ν) := funext hlog
  rw [e]
  refine ⟨hw.memLp.neg.sub (memLp_const _), hw.memLp_grad.neg, fun φ hφ j => ?_⟩
  have i1 := integrable_mul_top hbd (hφ.memLp_top_coordPartial j)
  have i2 : Integrable (fun x => coordPartial j φ x) (haar d) :=
    (hφ.memLp_top_coordPartial j).integrable le_top
  have h1 := hw.ibp φ hφ j
  have i1' : Integrable (fun x => -(interactionPotential A ρ x * coordPartial j φ x))
      (haar d) := i1.neg
  simp only [sub_mul, neg_mul]
  rw [integral_sub i1' (i2.const_mul _), integral_neg, integral_const_mul,
    def033_integral_coordPartial φ hφ j, h1]
  simp [integral_neg]

section Core

variable (A : InteractionData d) (hLip : LipschitzData A) (b : AbsoluteDrift A)
  (ρ : AbsoluteDensity d)

/-- Core equivalence: `D(ρ) = 0` iff `ρ = p` a.e., for the frozen Gibbs density `p` of `ρ m`. -/
theorem def033_dissipation_zero_iff_density_ae (hLip : LipschitzData A) :
    scalarDissipation A b ρ = 0 ↔
      ρ.density =ᵐ[haar d] (frozenGibbs A (densityMeasure ρ)).density := by
  set P := frozenGibbs A (densityMeasure ρ) with hPdef
  have hP : P.hasPositiveLipschitzDensity := frozenGibbs_hasPositiveLipschitzDensity A hLip _
  have hpos : ∀ x, 0 < P.density x := RelativeFisher.density_pos hP
  set u := ρ.sqrt with hu
  have hg := isWeakGradient_weakGradient ρ.sqrt_mem
  set g := weakGradient ρ.sqrt ρ.sqrt_mem with hgdef
  have hG := RelativeFisher.mul_rpow_isWeakGradient hP (r := (-(1 / 2) : ℝ)) (by norm_num) hg
  set G : Torus d → Tangent d := fun x => P.density x ^ (-(1 / 2) : ℝ) • g x +
        u x • (((-(1 / 2) : ℝ) * P.density x ^ (-(1 / 2) - 1 : ℝ)) •
          RelativeFisher.lipGradVec P.density x) with hGdef
  have hforce : (fun x => -(b.force ρ x)) =ᵐ[haar d]
      fun x => (P.density x)⁻¹ • RelativeFisher.lipGradVec P.density x :=
    (def033_log_weakGradient A b ρ).ae_eq_of_one
      (def033_isWeakGradientLp_one (RelativeFisher.isWeakGradient_log hP))
  -- the score equals `S` a.e.
  have hscore : (fun x => scalarScore A b ρ x) =ᵐ[haar d] fun x =>
      (2 : ℝ) • g x - u x • ((P.density x)⁻¹ • RelativeFisher.lipGradVec P.density x) := by
    filter_upwards [hforce] with x hx
    have hx' : b.force ρ x = -((P.density x)⁻¹ • RelativeFisher.lipGradVec P.density x) := by
      rw [← hx]; simp
    simp only [scalarScore, hx', smul_neg, sub_eq_add_neg]
    rfl
  have hmeas : AEMeasurable (fun x => ENNReal.ofReal (‖scalarScore A b ρ x‖ ^ 2)) (haar d) := by
    have h1 : AEStronglyMeasurable (fun x => scalarScore A b ρ x) (haar d) :=
      (hg.memLp_grad.aestronglyMeasurable.const_smul (2 : ℝ)).add
        (ρ.memLp_sqrt.aestronglyMeasurable.smul (b.measurable_force ρ).aestronglyMeasurable)
    exact (h1.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have hD : scalarDissipation A b ρ = 0 ↔ ∀ᵐ x ∂haar d, G x = 0 := by
    unfold scalarDissipation
    rw [lintegral_eq_zero_iff' hmeas]
    constructor
    · intro h
      filter_upwards [h, hscore] with x hx hs
      have h0 : ‖scalarScore A b ρ x‖ ^ 2 ≤ 0 := by
        have : ENNReal.ofReal (‖scalarScore A b ρ x‖ ^ 2) = 0 := hx
        exact ENNReal.ofReal_eq_zero.1 this
      have hS : ‖(2 : ℝ) • g x - u x • ((P.density x)⁻¹ • RelativeFisher.lipGradVec P.density x)‖
          ^ 2 = 0 := by
        rw [← hs]; exact le_antisymm h0 (by positivity)
      rw [← RelativeFisher.gradient_identity (hpos x)] at hS
      have : ‖G x‖ ^ 2 = 0 := by
        have h4 : (4 * P.density x) ≠ 0 := by have := hpos x; positivity
        exact (mul_eq_zero.1 hS).resolve_left h4
      exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
    · intro h
      filter_upwards [h, hscore] with x hx hs
      have hS : ‖(2 : ℝ) • g x - u x • ((P.density x)⁻¹ • RelativeFisher.lipGradVec P.density x)‖
          ^ 2 = 0 := by
        rw [← RelativeFisher.gradient_identity (hpos x)]
        have : ‖G x‖ = 0 := norm_eq_zero.2 hx
        rw [this]; simp
      show ENNReal.ofReal (‖scalarScore A b ρ x‖ ^ 2) = 0
      rw [hs, hS]; simp
  rw [hD]
  constructor
  · intro h
    have hv := (energy_zero_iff (w := fun _ => (1 : ℝ)) (c := 1) (C := 1) measurable_const
      (Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩) one_pos hG).1
      (integral_eq_zero_of_ae (by filter_upwards [h] with x hx; simp [hx]))
    obtain ⟨a, ha⟩ := hv
    have hden : ρ.density =ᵐ[haar d] fun x => a ^ 2 * P.density x := by
      filter_upwards [ha, P.ae_pos] with x hx hp
      have hu1 : u x = a * P.density x ^ (1 / 2 : ℝ) := by
        rw [← hx, mul_assoc, ← Real.rpow_add hp]; norm_num; rfl
      show u x ^ 2 = _
      rw [hu1, mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hp.le]
    have h1 : a ^ 2 = 1 := by
      have := ρ.integral_density
      rw [integral_congr_ae hden, integral_const_mul, P.mass_one, mul_one] at this
      exact this
    filter_upwards [hden] with x hx
    rw [hx, h1, one_mul]
  · intro h
    have hv : (fun x => u x * P.density x ^ (-(1 / 2) : ℝ)) =ᵐ[haar d] fun _ => (1 : ℝ) := by
      filter_upwards [h, ρ.sqrt_nonneg] with x hx hu0
      have hux : u x = P.density x ^ (1 / 2 : ℝ) := by
        have : u x = Real.sqrt (u x ^ 2) := (Real.sqrt_sq hu0).symm
        rw [this]
        have hx' : u x ^ 2 = P.density x := hx
        rw [hx', Real.sqrt_eq_rpow]
      rw [hux, ← Real.rpow_add (hpos x)]; norm_num
    have h1 : IsWeakGradient (fun x => u x * P.density x ^ (-(1 / 2) : ℝ)) (fun _ => 0) :=
      (isWeakGradient_const (d := d) 1).congr_ae hv.symm (Eventually.of_forall fun _ => rfl)
    exact hG.ae_eq h1

end Core

/-- **DEF033 (zero dissipation and frozen fixed points).**  Under Lipschitz data, an
absolute-admissible `ρ` has `D(ρ) = 0` iff `ρ m = P(ρ m)`; and every fixed probability `ν = P ν`
has a positive Lipschitz density, lies in the absolute domain (`ν = ρ m` for an absolute-admissible
`ρ`) and has zero dissipation. -/
theorem zeroDissipation_iff_frozenFixedPoint (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) :
    (∀ ρ : AbsoluteDensity d, scalarDissipation A b ρ = 0 ↔
      (densityMeasure ρ : Measure (Torus d)) = (frozenGibbs A (densityMeasure ρ)).measure) ∧
    (∀ ν : ProbabilityMeasure (Torus d), (ν : Measure (Torus d)) = (frozenGibbs A ν).measure →
      (frozenGibbs A ν).hasPositiveLipschitzDensity ∧
        ∃ ρ : AbsoluteDensity d, densityMeasure ρ = ν ∧ scalarDissipation A b ρ = 0) := by
  have key : ∀ ρ : AbsoluteDensity d, scalarDissipation A b ρ = 0 ↔
      (densityMeasure ρ : Measure (Torus d)) = (frozenGibbs A (densityMeasure ρ)).measure := by
    intro ρ
    rw [def033_dissipation_zero_iff_density_ae A b ρ hLip, densityMeasure_coe,
      BoundedPositiveReference.measure,
      withDensity_eq_iff_of_sigmaFinite
        ((ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
        ((frozenGibbs A (densityMeasure ρ)).measurable_ofReal_density.aemeasurable)]
    constructor
    · intro h
      filter_upwards [h] with x hx
      show ENNReal.ofReal (ρ.sqrt x ^ 2) = _
      exact congrArg ENNReal.ofReal hx
    · intro h
      filter_upwards [h, ρ.sqrt_nonneg] with x hx _
      have h2 : ENNReal.ofReal (ρ.sqrt x ^ 2) =
          ENNReal.ofReal ((frozenGibbs A (densityMeasure ρ)).density x) := hx
      exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _)
        (RelativeFisher.density_pos (frozenGibbs_hasPositiveLipschitzDensity A hLip _) x).le).1 h2
  refine ⟨key, fun ν hν => ?_⟩
  have hP := frozenGibbs_hasPositiveLipschitzDensity A hLip ν
  refine ⟨hP, ?_⟩
  set P := frozenGibbs A ν with hPdef
  have hpos : ∀ x, 0 < P.density x := RelativeFisher.density_pos hP
  obtain ⟨L, c, hc, hcP, hL⟩ := hP
  have hH := RelativeFisher.isWeakGradient_of_top
    (RelativeFisher.isWeakGradientLp_rpow hL hcP hc (r := (1 / 2 : ℝ)) (by norm_num))
  let ρ : AbsoluteDensity d :=
    { sqrt := fun x => P.density x ^ (1 / 2 : ℝ)
      sqrt_mem := ⟨_, hH⟩
      sqrt_nonneg := Eventually.of_forall fun x => (Real.rpow_pos_of_pos (hpos x) _).le
      mass_one := by
        have : ∀ x, (P.density x ^ (1 / 2 : ℝ)) ^ 2 = P.density x := fun x => by
          rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (hpos x).le]
        simp only [this]
        exact P.mass_one }
  have hρν : densityMeasure ρ = ν := by
    apply Subtype.ext
    refine (densityMeasure_coe ρ).trans (Eq.trans ?_ hν.symm)
    rw [BoundedPositiveReference.measure]
    refine withDensity_congr_ae (Eventually.of_forall fun x => ?_)
    show ENNReal.ofReal ((P.density x ^ (1 / 2 : ℝ)) ^ 2) = _
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (hpos x).le]
  refine ⟨ρ, hρν, (key ρ).2 ?_⟩
  rw [hρν]
  exact hν

end DGPS
