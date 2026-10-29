import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.Topology.Sequences

/-! The actual centered real L2 Hilbert space and density of its bounded
measurable representatives, as used in source Lemma 3.7, lines 659–670.

The centered space is the closed kernel of the integral functional. The
density proof centers the pinned dense family of actual L2 simple functions.
No density, conditional-expectation, or spectral-gap premise is assumed.

Development construction; protected acceptance remains separate.
Every declaration has a public name.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace PeriodicAttractiveLogGas.CenteredL2

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The actual integral on real L2, realized as the continuous inner
product with the constant one. -/
def mean : Lp ℝ 2 μ →L[ℝ] ℝ :=
  innerSL ℝ (Lp.const 2 μ (1 : ℝ))

theorem mean_eq_integral (f : Lp ℝ 2 μ) :
    mean μ f = ∫ x, f x ∂μ := by
  change ⟪Lp.const 2 μ (1 : ℝ), f⟫_ℝ = ∫ x, f x ∂μ
  simpa only [indicatorConstLp_univ, setIntegral_univ] using
    (L2.inner_indicatorConstLp_one (𝕜 := ℝ) (μ := μ)
      (s := Set.univ) MeasurableSet.univ (measure_ne_top μ _) f)

theorem integrable_coe (f : Lp ℝ 2 μ) : Integrable f μ :=
  (Lp.memLp f).integrable (by simp)

omit [IsProbabilityMeasure μ] in
theorem integrable_sq_coe (f : Lp ℝ 2 μ) :
    Integrable (fun x ↦ f x ^ 2) μ :=
  (Lp.memLp f).integrable_sq

@[simp]
theorem mean_const (c : ℝ) : mean μ (Lp.const 2 μ c) = c := by
  rw [mean_eq_integral]
  calc
    (∫ x, Lp.const 2 μ c x ∂μ) = ∫ _ : Ω, c ∂μ :=
      integral_congr_ae (Lp.coeFn_const 2 μ c)
    _ = c := by simp

/-- Centered classes are exactly the kernel of the actual integral. -/
def centeredSubspace : Submodule ℝ (Lp ℝ 2 μ) :=
  (mean μ).ker

@[simp]
theorem mem_centeredSubspace_iff (f : Lp ℝ 2 μ) :
    f ∈ centeredSubspace μ ↔ ∫ x, f x ∂μ = 0 := by
  change mean μ f = 0 ↔ ∫ x, f x ∂μ = 0
  rw [mean_eq_integral]

theorem isClosed_centeredSubspace :
    IsClosed (centeredSubspace μ : Set (Lp ℝ 2 μ)) :=
  (mean μ).isClosed_ker

/-- The actual closed centered Hilbert subspace, with inherited norm and
inner product, not a second function space or a choice of representatives. -/
abbrev Centered := ↥(centeredSubspace μ)

/-- Completeness comes from the proved closedness of the actual kernel. -/
instance centeredCompleteSpace : CompleteSpace (Centered μ) :=
  (isClosed_centeredSubspace μ).isComplete.completeSpace_coe

@[simp]
theorem mean_coe_eq_zero (f : Centered μ) : mean μ (f : Lp ℝ 2 μ) = 0 :=
  f.property

@[simp]
theorem integral_coe_eq_zero (f : Centered μ) :
    (∫ x, (f : Lp ℝ 2 μ) x ∂μ) = 0 := by
  rw [← mean_eq_integral]
  exact mean_coe_eq_zero μ f

/-- Subtracting the actual mean is an everywhere-defined continuous
linear map on the ambient L2 space. -/
def centerAmbient : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.id ℝ (Lp ℝ 2 μ) - (Lp.constL 2 μ ℝ).comp (mean μ)

@[simp]
theorem centerAmbient_apply (f : Lp ℝ 2 μ) :
    centerAmbient μ f = f - Lp.const 2 μ (mean μ f) := rfl

theorem centerAmbient_mem (f : Lp ℝ 2 μ) :
    centerAmbient μ f ∈ centeredSubspace μ := by
  change mean μ (centerAmbient μ f) = 0
  rw [centerAmbient_apply, map_sub, mean_const, sub_self]

/-- The continuous centering map with its actual closed-subspace codomain. -/
def center : Lp ℝ 2 μ →L[ℝ] Centered μ :=
  (centerAmbient μ).codRestrict (centeredSubspace μ) (centerAmbient_mem μ)

@[simp]
theorem coe_center (f : Lp ℝ 2 μ) :
    (center μ f : Lp ℝ 2 μ) = f - Lp.const 2 μ (mean μ f) := rfl

@[simp]
theorem center_coe (f : Centered μ) : center μ (f : Lp ℝ 2 μ) = f := by
  apply Subtype.ext
  rw [coe_center, mean_coe_eq_zero, map_zero, sub_zero]

theorem center_surjective : Function.Surjective (center μ) :=
  fun f ↦ ⟨(f : Lp ℝ 2 μ), center_coe μ f⟩

/-- The representative of the centered L2 class agrees almost everywhere
with subtraction of the actual integral. -/
theorem coeFn_center (f : Lp ℝ 2 μ) :
    ((center μ f : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ]
      fun x ↦ f x - ∫ y, f y ∂μ := by
  rw [coe_center]
  filter_upwards [Lp.coeFn_sub f (Lp.const 2 μ (mean μ f)),
    Lp.coeFn_const 2 μ (mean μ f)] with x hs hc
  calc
    (f - Lp.const 2 μ (mean μ f)) x = f x - Lp.const 2 μ (mean μ f) x := hs
    _ = f x - mean μ f := congrArg (fun r : ℝ ↦ f x - r) hc
    _ = f x - ∫ y, f y ∂μ := by rw [mean_eq_integral]

/-- Existence of an everywhere bounded measurable representative of the
actual L2 equivalence class. No bound on a chosen L2 representative at null
points is imposed. -/
def HasBoundedRepresentative (f : Lp ℝ 2 μ) : Prop :=
  ∃ g : Ω → ℝ, Measurable g ∧ ∃ C : ℝ,
    (∀ x, ‖g x‖ ≤ C) ∧ ((f : Ω → ℝ) =ᵐ[μ] g)

omit [IsProbabilityMeasure μ] in
theorem hasBoundedRepresentative_zero : HasBoundedRepresentative μ 0 := by
  refine ⟨fun _ ↦ 0, measurable_const, 0, fun _ ↦ by simp, ?_⟩
  exact Lp.coeFn_zero ℝ 2 μ

omit [IsProbabilityMeasure μ] in
theorem hasBoundedRepresentative_add {f h : Lp ℝ 2 μ}
    (hf : HasBoundedRepresentative μ f) (hh : HasBoundedRepresentative μ h) :
    HasBoundedRepresentative μ (f + h) := by
  rcases hf with ⟨g, hg, C, hC, hfg⟩
  rcases hh with ⟨k, hk, D, hD, hhk⟩
  refine ⟨fun x ↦ g x + k x, hg.add hk, C + D, ?_, ?_⟩
  · intro x
    exact (norm_add_le _ _).trans (add_le_add (hC x) (hD x))
  · filter_upwards [Lp.coeFn_add f h, hfg, hhk] with x hx hfx hhx
    change (f + h) x = g x + k x
    calc
      (f + h) x = f x + h x := by simpa only [Pi.add_apply] using hx
      _ = g x + k x := by rw [hfx, hhx]

omit [IsProbabilityMeasure μ] in
theorem hasBoundedRepresentative_smul (a : ℝ) {f : Lp ℝ 2 μ}
    (hf : HasBoundedRepresentative μ f) : HasBoundedRepresentative μ (a • f) := by
  rcases hf with ⟨g, hg, C, hC, hfg⟩
  refine ⟨fun x ↦ a * g x, measurable_const.mul hg, ‖a‖ * C, ?_, ?_⟩
  · intro x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg a)
  · filter_upwards [Lp.coeFn_smul a f, hfg] with x hx hfx
    change (a • f) x = a * g x
    calc
      (a • f) x = a * f x := by simpa only [Pi.smul_apply, smul_eq_mul] using hx
      _ = a * g x := by rw [hfx]

theorem hasBoundedRepresentative_const (c : ℝ) :
    HasBoundedRepresentative μ (Lp.const 2 μ c) :=
  ⟨fun _ ↦ c, measurable_const, ‖c‖, fun _ ↦ le_rfl, Lp.coeFn_const 2 μ c⟩

/-- Bounded measurable representatives form a real linear submodule of
the ambient actual L2 space. -/
def boundedAmbient : Submodule ℝ (Lp ℝ 2 μ) where
  carrier := {f | HasBoundedRepresentative μ f}
  zero_mem' := hasBoundedRepresentative_zero μ
  add_mem' := hasBoundedRepresentative_add μ
  smul_mem' := fun a _ hf ↦ hasBoundedRepresentative_smul μ a hf

/-- The bounded-representative linear submodule of the centered space. -/
def boundedRepresentatives : Submodule ℝ (Centered μ) :=
  (boundedAmbient μ).comap (centeredSubspace μ).subtype

@[simp]
theorem mem_boundedRepresentatives_iff (f : Centered μ) :
    f ∈ boundedRepresentatives μ ↔ HasBoundedRepresentative μ (f : Lp ℝ 2 μ) :=
  Iff.rfl

omit [IsProbabilityMeasure μ] in
theorem hasBoundedRepresentative_simple (f : Lp.simpleFunc ℝ 2 μ) :
    HasBoundedRepresentative μ (f : Lp ℝ 2 μ) := by
  let g : SimpleFunc Ω ℝ := Lp.simpleFunc.toSimpleFunc f
  obtain ⟨C, hC⟩ := g.exists_forall_norm_le
  refine ⟨g, g.measurable, C, hC, ?_⟩
  exact (Lp.simpleFunc.toSimpleFunc_eq_toFun f).symm

theorem center_mem_boundedRepresentatives {f : Lp ℝ 2 μ}
    (hf : HasBoundedRepresentative μ f) : center μ f ∈ boundedRepresentatives μ := by
  change centerAmbient μ f ∈ boundedAmbient μ
  rw [centerAmbient_apply]
  exact (boundedAmbient μ).sub_mem hf (hasBoundedRepresentative_const μ _)

/-- Actual density: center the pinned dense family of L2 simple functions
using the continuous surjective centering map. -/
theorem dense_boundedRepresentatives :
    Dense (boundedRepresentatives μ : Set (Centered μ)) := by
  apply (center_surjective μ).denseRange.dense_of_mapsTo (center μ).continuous
    (Lp.simpleFunc.dense (E := ℝ) (p := 2) (μ := μ) ENNReal.ofNat_ne_top)
  intro f hf
  exact center_mem_boundedRepresentatives μ
    (hasBoundedRepresentative_simple μ (⟨f, hf⟩ : Lp.simpleFunc ℝ 2 μ))

/-- Density yields actual sequences in the centered Hilbert norm. -/
theorem exists_bounded_sequence (f : Centered μ) :
    ∃ u : ℕ → Centered μ, (∀ n, u n ∈ boundedRepresentatives μ) ∧
      Tendsto u atTop (𝓝 f) :=
  mem_closure_iff_seq_limit.mp (dense_boundedRepresentatives μ f)

omit [IsProbabilityMeasure μ] in
/-- Every representative of an L2 class inherits its actual L2 membership. -/
theorem memLp_representative (f : Lp ℝ 2 μ) {g : Ω → ℝ}
    (hfg : (f : Ω → ℝ) =ᵐ[μ] g) : MemLp g 2 μ :=
  MemLp.ae_eq hfg (Lp.memLp f)

omit [IsProbabilityMeasure μ] in
theorem toLp_representative (f : Lp ℝ 2 μ) {g : Ω → ℝ}
    (hfg : (f : Ω → ℝ) =ᵐ[μ] g) :
    (memLp_representative μ f hfg).toLp g = f := by
  apply Lp.ext
  exact (memLp_representative μ f hfg).coeFn_toLp.trans hfg.symm

theorem integral_representative_eq_mean (f : Lp ℝ 2 μ) {g : Ω → ℝ}
    (hfg : (f : Ω → ℝ) =ᵐ[μ] g) : (∫ x, g x ∂μ) = mean μ f :=
  (integral_congr_ae hfg).symm.trans (mean_eq_integral μ f).symm

/-- Membership in the bounded centered submodule supplies a globally
bounded measurable, genuinely centered representative, including for zero. -/
theorem exists_bounded_centered_representative {f : Centered μ}
    (hf : f ∈ boundedRepresentatives μ) :
    ∃ g : Ω → ℝ, ∃ C : ℝ, Measurable g ∧ 0 ≤ C ∧
      (∀ x, ‖g x‖ ≤ C) ∧ (((f : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] g) ∧
      (∫ x, g x ∂μ) = 0 ∧ MemLp g 2 μ := by
  rcases (mem_boundedRepresentatives_iff μ f).mp hf with ⟨g, hg, C, hC, hfg⟩
  refine ⟨g, max C 0, hg, le_max_right _ _,
    fun x ↦ (hC x).trans (le_max_left _ _), hfg, ?_, memLp_representative μ _ hfg⟩
  rw [integral_representative_eq_mean μ _ hfg, mean_coe_eq_zero]

omit [IsProbabilityMeasure μ] in
/-- The actual L2 norm squared is the actual finite second integral. -/
theorem norm_sq_eq_integral_sq (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  simpa only [L2.inner_def, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using
    (real_inner_self_eq_norm_sq f).symm

omit [IsProbabilityMeasure μ] in
theorem norm_sq_eq_integral_sq_representative (f : Lp ℝ 2 μ) {g : Ω → ℝ}
    (hfg : (f : Ω → ℝ) =ᵐ[μ] g) : ‖f‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
  rw [norm_sq_eq_integral_sq]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  exact congrArg (fun r : ℝ ↦ r ^ 2) hx

theorem centered_norm_sq_eq_integral_sq (f : Centered μ) :
    ‖f‖ ^ 2 = ∫ x, (f : Lp ℝ 2 μ) x ^ 2 ∂μ :=
  norm_sq_eq_integral_sq μ (f : Lp ℝ 2 μ)

/-- Actual variance of a centered L2 representative equals its Hilbert
norm squared. Both the first and second integrals are finite. -/
theorem centered_variance_eq_norm_sq (f : Centered μ) :
    ProbabilityTheory.variance ((f : Lp ℝ 2 μ) : Ω → ℝ) μ = ‖f‖ ^ 2 := by
  rw [ProbabilityTheory.variance_of_integral_eq_zero
    (Lp.aestronglyMeasurable (f : Lp ℝ 2 μ)).aemeasurable (integral_coe_eq_zero μ f)]
  exact (centered_norm_sq_eq_integral_sq μ f).symm

/-- The same variance identity is independent of the representative,
including the globally bounded representatives used in the source proof. -/
theorem centered_variance_representative {f : Centered μ} {g : Ω → ℝ}
    (hfg : ((f : Lp ℝ 2 μ) : Ω → ℝ) =ᵐ[μ] g) :
    ProbabilityTheory.variance g μ = ‖f‖ ^ 2 := by
  have hg : MemLp g 2 μ := memLp_representative μ _ hfg
  have hz : (∫ x, g x ∂μ) = 0 := by
    rw [integral_representative_eq_mean μ _ hfg, mean_coe_eq_zero]
  rw [ProbabilityTheory.variance_of_integral_eq_zero hg.aemeasurable hz]
  exact (norm_sq_eq_integral_sq_representative μ (f : Lp ℝ 2 μ) hfg).symm

/-- For an arbitrary real L2 class, centering produces exactly its
variance as the centered Hilbert norm squared. -/
theorem variance_eq_norm_center_sq (f : Lp ℝ 2 μ) :
    ProbabilityTheory.variance (f : Ω → ℝ) μ = ‖center μ f‖ ^ 2 := by
  rw [ProbabilityTheory.variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable]
  change (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) = ‖(center μ f : Lp ℝ 2 μ)‖ ^ 2
  rw [norm_sq_eq_integral_sq]
  apply integral_congr_ae
  filter_upwards [(coeFn_center μ f).symm] with x hx
  exact congrArg (fun r : ℝ ↦ r ^ 2) hx

end PeriodicAttractiveLogGas.CenteredL2
