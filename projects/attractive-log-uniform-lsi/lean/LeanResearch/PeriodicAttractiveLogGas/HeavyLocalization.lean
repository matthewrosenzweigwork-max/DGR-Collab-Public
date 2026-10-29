import LeanResearch.PeriodicAttractiveLogGas.HeavyPartition
import LeanResearch.PeriodicAttractiveLogGas.ConfigurationLipschitzDomain

/-! The finite square localization in the proof of `thm:heavy-coercivity`.
The functions below are the actual `HeavyPartition.zetaValue` times the given
observable. The derivative identity includes the boundary of the heavy region:
where the sum of squares differs from one, the observable vanishes locally.
The development note records the exact centralized checking status. -/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped BigOperators Topology NNReal

namespace PeriodicAttractiveLogGas.HeavyLocalization

open MeshCells SmoothOccupations HeavyScales HeavyPartition SeparatedRadius

/-- Bounded continuous maps on the compact configuration torus preserve physical
Euclidean Lipschitz regularity under multiplication. -/
theorem lipschitz_lift_mul {N : ℕ} (f g : C(Configuration N, ℝ)) {K L : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y)))
    (hg : LipschitzWith L (fun y ↦ g (configurationQuotient N y))) :
    LipschitzWith (‖f‖₊ * L + K * ‖g‖₊)
      (fun y ↦ (f * g) (configurationQuotient N y)) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro y z
  change ‖f (configurationQuotient N y) * g (configurationQuotient N y) -
      f (configurationQuotient N z) * g (configurationQuotient N z)‖ ≤ _
  calc
    _ = ‖f (configurationQuotient N y) *
        (g (configurationQuotient N y) - g (configurationQuotient N z)) +
        (f (configurationQuotient N y) - f (configurationQuotient N z)) *
          g (configurationQuotient N z)‖ := by congr 1; ring
    _ ≤ ‖f (configurationQuotient N y) *
        (g (configurationQuotient N y) - g (configurationQuotient N z))‖ +
        ‖(f (configurationQuotient N y) - f (configurationQuotient N z)) *
          g (configurationQuotient N z)‖ := norm_add_le _ _
    _ = ‖f (configurationQuotient N y)‖ *
        ‖g (configurationQuotient N y) - g (configurationQuotient N z)‖ +
        ‖f (configurationQuotient N y) - f (configurationQuotient N z)‖ *
          ‖g (configurationQuotient N z)‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖f‖ * ((L : ℝ) * ‖y - z‖) + ((K : ℝ) * ‖y - z‖) * ‖g‖ :=
      add_le_add
        (mul_le_mul (f.norm_coe_le_norm _)
          (lipschitzWith_iff_norm_sub_le.mp hg y z) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul (lipschitzWith_iff_norm_sub_le.mp hf y z)
          (g.norm_coe_le_norm _) (norm_nonneg _) (by positivity))
    _ = _ := by
      change _ = (‖f‖ * (L : ℝ) + (K : ℝ) * ‖g‖) * ‖y - z‖
      ring

private theorem innerSL_injective_real {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {v w : E} (h : innerSL ℝ v = innerSL ℝ w) : v = w := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  calc
    ‖v - w‖ = ‖innerSL ℝ (v - w)‖ := (innerSL_apply_norm ℝ (v - w)).symm
    _ = 0 := by rw [map_sub, h, sub_self, norm_zero]

/-- The actual totalized descended gradients obey the product rule on a single
full set for every measure absolutely continuous with respect to Haar. -/
theorem ae_descendedLiftGradient_mul {N : ℕ} (μ : Measure (Configuration N))
    (hμ : μ ≪ referenceMeasure N) (f g : C(Configuration N, ℝ)) {K L : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y)))
    (hg : LipschitzWith L (fun y ↦ g (configurationQuotient N y))) :
    ∀ᵐ X ∂μ, descendedLiftGradient (f * g) X =
      f X • descendedLiftGradient g X + g X • descendedLiftGradient f X := by
  filter_upwards
    [ae_hasFDerivAt_configurationLift_of_absolutelyContinuous f hf hμ,
      ae_hasFDerivAt_configurationLift_of_absolutelyContinuous g hg hμ,
      ae_hasFDerivAt_configurationLift_of_absolutelyContinuous (f * g)
        (lipschitz_lift_mul f g hf hg) hμ] with X hdf hdg hdp
  let y := configurationCenteredLift X
  have hy : configurationQuotient N y = X := configurationQuotient_centeredLift X
  have hp := (hdf y hy).mul (hdg y hy)
  have he := (hdp y hy).unique hp
  apply innerSL_injective_real
  calc
    _ = f X • innerSL ℝ (descendedLiftGradient g X) +
        g X • innerSL ℝ (descendedLiftGradient f X) := by simpa only [hy] using he
    _ = _ := by
      ext v
      simp only [add_apply, smul_apply, innerSL_apply_apply, inner_add_left,
        inner_smul_left, conj_trivial, smul_eq_mul]

private theorem sum_square_expansion {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : ℝ) (u : ι → ℝ) (v : E) (w : ι → E) :
    (∑ i, ‖u i • v + t • w i‖ ^ 2) =
      (∑ i, u i ^ 2) * ‖v‖ ^ 2 +
        2 * t * (∑ i, u i * inner ℝ v (w i)) + t ^ 2 * ∑ i, ‖w i‖ ^ 2 := by
  classical
  calc
    _ = ∑ i, (u i ^ 2 * ‖v‖ ^ 2 +
        2 * t * (u i * inner ℝ v (w i)) + t ^ 2 * ‖w i‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_add_sq_real, norm_smul, norm_smul]
      simp only [Real.norm_eq_abs, mul_pow, sq_abs, inner_smul_left,
        inner_smul_right, conj_trivial]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]

/-- Finite IMS at a point of genuine differentiability. The only partition
input is the pointwise identity wherever the observable is nonzero. No
derivative cancellation or zero-set derivative is an assumption. -/
theorem finite_ims_of_hasFDerivAt {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (u : ι → E → ℝ) (y v : E) (w : ι → E)
    (hf : HasFDerivAt f (innerSL ℝ v) y)
    (hu : ∀ i, HasFDerivAt (u i) (innerSL ℝ (w i)) y)
    (hpartition : ∀ z, f z ≠ 0 → (∑ i, u i z ^ 2) = 1) :
    (∑ i, ‖u i y • v + f y • w i‖ ^ 2) =
      ‖v‖ ^ 2 + f y ^ 2 * ∑ i, ‖w i‖ ^ 2 := by
  classical
  have hS : HasFDerivAt (fun z ↦ ∑ i, u i z ^ 2)
      (∑ i, (2 * u i y) • innerSL ℝ (w i)) y := by
    simpa only [Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat] using
      HasFDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ (hu i).pow 2)
  by_cases hfy : f y = 0
  · by_cases hSy : (∑ i, u i y ^ 2) = 1
    · rw [sum_square_expansion, hSy, hfy]
      ring
    · have hzero : f =ᶠ[𝓝 y] fun _ ↦ 0 := by
        filter_upwards [hS.continuousAt.eventually_ne hSy] with z hz
        by_contra hz0
        exact hz (hpartition z hz0)
      have hd0 : HasFDerivAt f (0 : E →L[ℝ] ℝ) y :=
        (hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hzero
      have hv0 : v = 0 := by
        apply innerSL_injective_real
        simpa only [map_zero] using hf.unique hd0
      simp only [hfy, hv0, smul_zero, zero_smul, add_zero, norm_zero,
        zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, zero_mul]
  · have hconst : (fun z ↦ ∑ i, u i z ^ 2) =ᶠ[𝓝 y] fun _ ↦ (1 : ℝ) := by
      filter_upwards [hf.continuousAt.eventually_ne hfy] with z hz
      exact hpartition z hz
    have hd0 : HasFDerivAt (fun z ↦ ∑ i, u i z ^ 2) (0 : E →L[ℝ] ℝ) y :=
      (hasFDerivAt_const (1 : ℝ) y).congr_of_eventuallyEq hconst
    have he := congrArg (fun T : E →L[ℝ] ℝ ↦ T v) (hS.unique hd0)
    have hcross : 2 * (∑ i, u i y * inner ℝ v (w i)) = 0 := by
      simpa only [sum_apply, smul_apply, zero_apply, innerSL_apply_apply, smul_eq_mul,
        mul_assoc, Finset.mul_sum, real_inner_comm] using he
    have hc : (∑ i, u i y * inner ℝ v (w i)) = 0 := by linarith
    rw [sum_square_expansion, hpartition y hfy, hc]
    ring

/-- Squared continuous observables are genuinely integrable against any finite
measure on the configuration torus. -/
theorem integrable_continuous_sq {N : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (f : C(Configuration N, ℝ)) :
    Integrable (fun X ↦ f X ^ 2) μ := by
  apply memLp_one_iff_integrable.mp
  refine MemLp.of_bound (f.continuous.measurable.pow_const 2).aestronglyMeasurable
    (‖f‖ ^ 2) (Eventually.of_forall ?_)
  intro X
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm X) 2

/-- A finite family of actual continuous maps satisfies IMS on a common full
set when its squared sum equals one wherever the observable is nonzero. -/
theorem ae_finite_ims {N : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (Configuration N)) (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) (u : ι → C(Configuration N, ℝ))
    {K : ℝ≥0} {L : ι → ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y)))
    (hu : ∀ i, LipschitzWith (L i) (fun y ↦ u i (configurationQuotient N y)))
    (hpartition : ∀ X, f X ≠ 0 → (∑ i, u i X ^ 2) = 1) :
    ∀ᵐ X ∂μ, (∑ i, ‖descendedLiftGradient (u i * f) X‖ ^ 2) =
      ‖descendedLiftGradient f X‖ ^ 2 + f X ^ 2 * ∑ i, ‖descendedLiftGradient (u i) X‖ ^ 2 := by
  classical
  have hdu : ∀ᵐ X ∂μ, ∀ i, ∀ y : Gradient N, configurationQuotient N y = X →
      HasFDerivAt (fun z ↦ u i (configurationQuotient N z))
        (innerSL ℝ (descendedLiftGradient (u i) X)) y :=
    ae_all_iff.2 fun i ↦ ae_hasFDerivAt_configurationLift_of_absolutelyContinuous
      (u i) (hu i) hμ
  have hprod : ∀ᵐ X ∂μ, ∀ i, descendedLiftGradient (u i * f) X =
      u i X • descendedLiftGradient f X + f X • descendedLiftGradient (u i) X :=
    ae_all_iff.2 fun i ↦ ae_descendedLiftGradient_mul μ hμ (u i) f (hu i) hf
  filter_upwards [ae_hasFDerivAt_configurationLift_of_absolutelyContinuous f hf hμ,
    hdu, hprod] with X hdf hduX hpX
  let y := configurationCenteredLift X
  have hy : configurationQuotient N y = X := configurationQuotient_centeredLift X
  calc
    _ = ∑ i, ‖u i X • descendedLiftGradient f X +
        f X • descendedLiftGradient (u i) X‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hpX i]
    _ = _ := by
      simpa only [hy] using finite_ims_of_hasFDerivAt
        (fun z ↦ f (configurationQuotient N z))
        (fun i z ↦ u i (configurationQuotient N z)) y
        (descendedLiftGradient f X) (fun i ↦ descendedLiftGradient (u i) X)
        (hdf y hy) (fun i ↦ hduX i y hy)
        (fun z hz ↦ hpartition (configurationQuotient N z) hz)

/-- Integrability of the finite localization cost uses the actual L2 gradients
and the compact-space bound on the observable. -/
theorem integrable_finite_localization_cost {N : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (f : C(Configuration N, ℝ)) (u : ι → C(Configuration N, ℝ))
    {L : ι → ℝ≥0}
    (hu : ∀ i, LipschitzWith (L i) (fun y ↦ u i (configurationQuotient N y))) :
    Integrable (fun X ↦ f X ^ 2 * ∑ i, ‖descendedLiftGradient (u i) X‖ ^ 2) μ := by
  classical
  have hsum : Integrable (fun X ↦ ∑ i, ‖descendedLiftGradient (u i) X‖ ^ 2) μ :=
    integrable_finsetSum _ fun i _ ↦ integrable_sq_norm_descendedLiftGradient μ (u i) (hu i)
  apply hsum.bdd_mul (f.continuous.measurable.pow_const 2).aestronglyMeasurable
  filter_upwards [] with X
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (f.norm_coe_le_norm X) 2

/-- The squared-L2 decomposition is a finite integral identity, with every
summand integrable. -/
theorem finite_localized_l2_identity {N : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (f : C(Configuration N, ℝ)) (u : ι → C(Configuration N, ℝ))
    (hpartition : ∀ X, f X ≠ 0 → (∑ i, u i X ^ 2) = 1) :
    (∫ X, f X ^ 2 ∂μ) = ∑ i, ∫ X, (u i * f) X ^ 2 ∂μ := by
  classical
  calc
    _ = ∫ X, ∑ i, (u i * f) X ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with X
      by_cases h : f X = 0
      · simp only [ContinuousMap.mul_apply, h, mul_zero, zero_pow (by decide : 2 ≠ 0),
          Finset.sum_const_zero]
      · simp only [ContinuousMap.mul_apply, mul_pow, ← Finset.sum_mul, hpartition X h, one_mul]
    _ = _ := integral_finsetSum _ fun i _ ↦ integrable_continuous_sq μ (u i * f)

/-- Integral IMS for a finite family of actual Lipschitz continuous maps. -/
theorem finite_ims_integral_identity {N : ℕ} {ι : Type*} [Fintype ι]
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    (f : C(Configuration N, ℝ)) (u : ι → C(Configuration N, ℝ))
    {K : ℝ≥0} {L : ι → ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y)))
    (hu : ∀ i, LipschitzWith (L i) (fun y ↦ u i (configurationQuotient N y)))
    (hpartition : ∀ X, f X ≠ 0 → (∑ i, u i X ^ 2) = 1) :
    (∑ i, ∫ X, ‖descendedLiftGradient (u i * f) X‖ ^ 2 ∂μ) =
      (∫ X, ‖descendedLiftGradient f X‖ ^ 2 ∂μ) +
        ∫ X, f X ^ 2 * ∑ i, ‖descendedLiftGradient (u i) X‖ ^ 2 ∂μ := by
  classical
  calc
    _ = ∫ X, ∑ i, ‖descendedLiftGradient (u i * f) X‖ ^ 2 ∂μ :=
      (integral_finsetSum _ fun i _ ↦ integrable_sq_norm_descendedLiftGradient μ
        (u i * f) (lipschitz_lift_mul (u i) f (hu i) hf)).symm
    _ = ∫ X, ‖descendedLiftGradient f X‖ ^ 2 +
        f X ^ 2 * ∑ i, ‖descendedLiftGradient (u i) X‖ ^ 2 ∂μ :=
      integral_congr_ae (ae_finite_ims μ hμ f u hf hu hpartition)
    _ = _ := integral_add (integrable_sq_norm_descendedLiftGradient μ f hf)
      (integrable_finite_localization_cost μ f u hu)

/-- This constant is chosen only from the proved physical Lipschitz regularity
of the actual partition function; it is not a new partition or analytic premise. -/
def zetaLiftConstant {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) : ℝ≥0 :=
  Classical.choose (zeta_physical_lipschitz hN hβ₀ hβ hδ hJ a m)

theorem zetaValue_lift_lipschitz {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) :
    LipschitzWith (zetaLiftConstant hN hβ₀ hβ hδ hJ a m)
      (fun y ↦ zetaValue hN (source_mesh_pos hJ) hδ β₀ a m (configurationQuotient N y)) :=
  (Classical.choose_spec (zeta_physical_lipschitz hN hβ₀ hβ hδ hJ a m)).lift

def localizedValue {N J : ℕ} (hN : 0 < N) (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 < δ) (β₀ : ℝ) (F : C(Configuration N, ℝ))
    (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) : C(Configuration N, ℝ) :=
  zetaValue hN hJ hδ β₀ a m * F

@[simp] theorem localizedValue_apply {N J : ℕ} (hN : 0 < N) (hJ : 0 < J) {δ : ℝ}
    (hδ : 0 < δ) (β₀ : ℝ) (F : C(Configuration N, ℝ))
    (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) (X : Configuration N) :
    localizedValue hN hJ hδ β₀ F a m X = zeta N J hJ β₀ δ a m X * F X := rfl

theorem localized_lift_lipschitz {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) :
    LipschitzWith (‖zetaValue hN (source_mesh_pos hJ) hδ β₀ a m‖₊ * L +
      zetaLiftConstant hN hβ₀ hβ hδ hJ a m * ‖F‖₊)
      (fun y ↦ localizedValue hN (source_mesh_pos hJ) hδ β₀ F a m (configurationQuotient N y)) :=
  lipschitz_lift_mul _ F (zetaValue_lift_lipschitz hN hβ₀ hβ hδ hJ a m) hF

theorem localizedValue_eq_zero_off_openSet {N J : ℕ} (hN : 0 < N) (hJ : 0 < J)
    {β₀ δ : ℝ} (hδ : 0 < δ) (F : C(Configuration N, ℝ))
    (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ))
    {X : Configuration N} (hX : X ∉ SeparatedRadius.separatedOpenSet N J hJ β₀ δ a m) :
    localizedValue hN hJ hδ β₀ F a m X = 0 := by
  rw [localizedValue_apply, zeta_eq_zero_off_openSet hJ hδ a m hX, zero_mul]

theorem integrable_localized_sq {N J : ℕ} (hN : 0 < N) (hJ : 0 < J)
    {β₀ δ : ℝ} (hδ : 0 < δ) (β : ℝ) (F : C(Configuration N, ℝ))
    (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) :
    Integrable (fun X ↦ localizedValue hN hJ hδ β₀ F a m X ^ 2)
      (gibbsMeasure greenRealRepresentative N β) :=
  integrable_continuous_sq _ _

theorem integrable_localized_gradient_sq {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (β : ℝ) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (a : MeshIndex J) (m : Fin (sourceScaleCount β₀ δ)) :
    Integrable (fun X ↦
      ‖descendedLiftGradient (localizedValue hN (source_mesh_pos hJ) hδ β₀ F a m) X‖ ^ 2)
      (gibbsMeasure greenRealRepresentative N β) :=
  integrable_sq_norm_descendedLiftGradient _ _
    (localized_lift_lipschitz hN hβ₀ hβ hδ hJ F hF a m)

/-- The whole actual finite family obeys the product-gradient rule on one
Gibbs-full set; the observable has no symmetry or collision support condition. -/
theorem ae_localized_gradient {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (β : ℝ) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y))) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β, ∀ a : MeshIndex J,
      ∀ m : Fin (sourceScaleCount β₀ δ),
      descendedLiftGradient (localizedValue hN (source_mesh_pos hJ) hδ β₀ F a m) X =
        zeta N J (source_mesh_pos hJ) β₀ δ a m X • descendedLiftGradient F X +
          F X • descendedLiftGradient (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) X := by
  apply ae_all_iff.2
  intro a
  apply ae_all_iff.2
  intro m
  exact ae_descendedLiftGradient_mul (gibbsMeasure greenRealRepresentative N β)
    (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
    (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) F
    (zetaValue_lift_lipschitz hN hβ₀ hβ hδ hJ a m) hF

private theorem partition_unity_of_nonzero {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (F : C(Configuration N, ℝ))
    (hsupport : ∀ X, maximumOccupation N J (source_mesh_pos hJ) X ≤ δ → F X = 0)
    (X : Configuration N) (hX : F X ≠ 0) :
    (∑ p : MeshIndex J × Fin (sourceScaleCount β₀ δ),
      zetaValue hN (source_mesh_pos hJ) hδ β₀ p.1 p.2 X ^ 2) = 1 := by
  have hh : δ < maximumOccupation N J (source_mesh_pos hJ) X :=
    lt_of_not_ge fun hle ↦ hX (hsupport X hle)
  rw [Fintype.sum_prod_type]
  change (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
    zeta N J (source_mesh_pos hJ) β₀ δ a m X ^ 2) = 1
  exact squared_partition_unity hN hβ₀ hβ hδ hδ1 hJ X hh

/-- The finite localized L2 identity for the actual heavy partition and the
original Gibbs measure. -/
theorem localized_l2_identity {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (β : ℝ) (F : C(Configuration N, ℝ))
    (hsupport : ∀ X, maximumOccupation N J (source_mesh_pos hJ) X ≤ δ → F X = 0) :
    (∫ X, F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) =
      ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
        ∫ X, localizedValue hN (source_mesh_pos hJ) hδ β₀ F a m X ^ 2
          ∂gibbsMeasure greenRealRepresentative N β := by
  simpa only [Fintype.sum_prod_type, localizedValue] using
    finite_localized_l2_identity (gibbsMeasure greenRealRepresentative N β) F
      (fun p : MeshIndex J × Fin (sourceScaleCount β₀ δ) ↦
        zetaValue hN (source_mesh_pos hJ) hδ β₀ p.1 p.2)
      (partition_unity_of_nonzero hN hβ₀ hβ hδ hδ1 hJ F hsupport)

/-- Actual global AE IMS, including the boundary where the observable is zero. -/
theorem ae_localized_gradient_sq_identity {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (β : ℝ) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (hsupport : ∀ X, maximumOccupation N J (source_mesh_pos hJ) X ≤ δ → F X = 0) :
    ∀ᵐ X ∂gibbsMeasure greenRealRepresentative N β,
      (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
        ‖descendedLiftGradient (localizedValue hN (source_mesh_pos hJ) hδ β₀ F a m) X‖ ^ 2) =
      ‖descendedLiftGradient F X‖ ^ 2 + F X ^ 2 *
        ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
          ‖descendedLiftGradient (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) X‖ ^ 2 := by
  simpa only [Fintype.sum_prod_type, localizedValue] using
    ae_finite_ims (gibbsMeasure greenRealRepresentative N β)
      (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F
      (fun p : MeshIndex J × Fin (sourceScaleCount β₀ δ) ↦
        zetaValue hN (source_mesh_pos hJ) hδ β₀ p.1 p.2) hF
      (fun p ↦ zetaValue_lift_lipschitz hN hβ₀ hβ hδ hJ p.1 p.2)
      (partition_unity_of_nonzero hN hβ₀ hβ hδ hδ1 hJ F hsupport)

theorem integrable_localization_cost {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ)
    (hJ : sourceResolution β₀ δ ≤ J) (β : ℝ) (F : C(Configuration N, ℝ)) :
    Integrable (fun X ↦ F X ^ 2 *
      ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
        ‖descendedLiftGradient (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) X‖ ^ 2)
      (gibbsMeasure greenRealRepresentative N β) := by
  simpa only [Fintype.sum_prod_type] using
    integrable_finite_localization_cost (gibbsMeasure greenRealRepresentative N β) F
      (fun p : MeshIndex J × Fin (sourceScaleCount β₀ δ) ↦
        zetaValue hN (source_mesh_pos hJ) hδ β₀ p.1 p.2)
      (fun p ↦ zetaValue_lift_lipschitz hN hβ₀ hβ hδ hJ p.1 p.2)

/-- IMS as an identity of the actual unscaled ambient energies. -/
theorem localized_energy_identity {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (β : ℝ) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (hsupport : ∀ X, maximumOccupation N J (source_mesh_pos hJ) X ≤ δ → F X = 0) :
    (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
      ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
        (localizedValue hN (source_mesh_pos hJ) hδ β₀ F a m)
        (localized_lift_lipschitz hN hβ₀ hβ hδ hJ F hF a m))) =
      ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) +
      ∫ X, F X ^ 2 * ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
        ‖descendedLiftGradient (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) X‖ ^ 2
          ∂gibbsMeasure greenRealRepresentative N β := by
  simp_rw [configurationLipschitzAmbient_energy_eq_integral]
  simpa only [Fintype.sum_prod_type, localizedValue] using
    finite_ims_integral_identity (gibbsMeasure greenRealRepresentative N β)
      (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F
      (fun p : MeshIndex J × Fin (sourceScaleCount β₀ δ) ↦
        zetaValue hN (source_mesh_pos hJ) hδ β₀ p.1 p.2) hF
      (fun p ↦ zetaValue_lift_lipschitz hN hβ₀ hβ hδ hJ p.1 p.2)
      (partition_unity_of_nonzero hN hβ₀ hβ hδ hδ1 hJ F hsupport)

/-- The localization cost uses the sharp actual partition estimate only where
the observable is nonzero; the complementary contribution is literally zero. -/
theorem localization_cost_le {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (β : ℝ) (F : C(Configuration N, ℝ))
    (hsupport : ∀ X, maximumOccupation N J (source_mesh_pos hJ) X ≤ δ → F X = 0) :
    (∫ X, F X ^ 2 * ∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
      ‖descendedLiftGradient (zetaValue hN (source_mesh_pos hJ) hδ β₀ a m) X‖ ^ 2
        ∂gibbsMeasure greenRealRepresentative N β) ≤
      (32 * (sourceScaleCount β₀ δ : ℝ) ^ 2 * scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 /
        (δ ^ 3 * N)) * (∫ X, F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) := by
  let C : ℝ := 32 * (sourceScaleCount β₀ δ : ℝ) ^ 2 *
    scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 / (δ ^ 3 * N)
  calc
    _ ≤ ∫ X, C * F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β := by
      apply integral_mono_ae (integrable_localization_cost hN hβ₀ hβ hδ hJ β F)
        ((integrable_continuous_sq (gibbsMeasure greenRealRepresentative N β) F).const_mul C)
      filter_upwards [ae_partition_gradient_sq_le_gibbs hN hβ₀ hβ hδ hδ1 hJ
        greenRealRepresentative β] with X hX
      by_cases hh : δ < maximumOccupation N J (source_mesh_pos hJ) X
      · calc
          _ ≤ F X ^ 2 * C := mul_le_mul_of_nonneg_left (hX hh) (sq_nonneg _)
          _ = C * F X ^ 2 := mul_comm _ _
      · rw [hsupport X (le_of_not_gt hh)]
        simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, mul_zero, le_refl]
    _ = _ := integral_const_mul C _

/-- Quantitative IMS for the actual products, before the separately owned
source scale and particle-threshold arithmetic. -/
theorem localized_energy_le {N J : ℕ} (hN : 0 < N) {β₀ δ : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ : β₀ < 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hJ : sourceResolution β₀ δ ≤ J) (β : ℝ) (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (hsupport : ∀ X, maximumOccupation N J (source_mesh_pos hJ) X ≤ δ → F X = 0) :
    (∑ a : MeshIndex J, ∑ m : Fin (sourceScaleCount β₀ δ),
      ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β)
        (localizedValue hN (source_mesh_pos hJ) hδ β₀ F a m)
        (localized_lift_lipschitz hN hβ₀ hβ hδ hJ F hF a m))) ≤
      ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) +
      (32 * (sourceScaleCount β₀ δ : ℝ) ^ 2 * scaleGradientConstant β₀ δ ^ 2 * (J : ℝ) ^ 2 /
        (δ ^ 3 * N)) * (∫ X, F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) := by
  rw [localized_energy_identity hN hβ₀ hβ hδ hδ1 hJ β F hF hsupport]
  exact add_le_add le_rfl (localization_cost_le hN hβ₀ hβ hδ hδ1 hJ β F hsupport)

end PeriodicAttractiveLogGas.HeavyLocalization
