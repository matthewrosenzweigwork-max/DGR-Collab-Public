import DGPS.Lipschitz.T01ReferenceData
import DGPS.Frontier.LIP051.Close
import SharpSymmetricLSI.Paper.GroundT10

/-!
# Uniform exponential moments and the actual normalizer limit

The limit's exponential integrability is proved from the joint law and the uniform
particle moment, rather than imported as an additional Gaussian assumption.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace DGPS.Lipschitz

/-- A joint weak limit with a uniform moment of its positive continuous weight has
an integrable limiting weight and the corresponding weighted integral limits. -/
theorem t01_weighted_joint_limit {E : Type*} [TopologicalSpace E]
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {A : ∀ k, Ω k → E} {U : ∀ k, Ω k → ℝ}
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {A' : Ω' → E} {U' : Ω' → ℝ}
    (hconv : ∀ G : E × ℝ →ᵇ ℝ,
      Tendsto (fun k => ∫ x, G (A k x, U k x) ∂P k) atTop
        (𝓝 (∫ x, G (A' x, U' x) ∂P')))
    {w : ℝ → ℝ} (hw : Continuous w) (hw0 : ∀ u, 0 ≤ w u)
    {p B : ℝ} (hp : 1 < p)
    (hm : ∀ k, AEStronglyMeasurable (fun x => (A k x, U k x)) (P k))
    (hm' : AEStronglyMeasurable (fun x => (A' x, U' x)) P')
    (hi : ∀ k, Integrable (fun x => w (U k x)) (P k))
    (hpi : ∀ k, Integrable (fun x => w (U k x) ^ p) (P k))
    (hB : ∀ k, ∫ x, w (U k x) ^ p ∂P k ≤ B) :
    Integrable (fun x => w (U' x)) P' ∧
      ∀ Φ : E × ℝ →ᵇ ℝ,
        Tendsto (fun k => ∫ x, w (U k x) * Φ (A k x, U k x) ∂P k) atTop
          (𝓝 (∫ x, w (U' x) * Φ (A' x, U' x) ∂P')) := by
  have hfirst : ∀ k, ∫ x, w (U k x) ∂P k ≤ 1 + B := by
    intro k
    calc
      _ ≤ ∫ x, 1 + w (U k x) ^ p ∂P k :=
        integral_mono (hi k) ((integrable_const 1).add (hpi k))
          (fun x => SharpLSI.le_one_add_rpow (hw0 _) hp.le)
      _ = 1 + ∫ x, w (U k x) ^ p ∂P k := by
        rw [integral_add (integrable_const 1) (hpi k)]
        simp
      _ ≤ _ := add_le_add le_rfl (hB k)
  let f : ℕ → Ω' → ℝ := fun n x => min (w (U' x)) (n : ℝ)
  have hfm : AEStronglyMeasurable (fun x => w (U' x)) P' :=
    hw.comp_aestronglyMeasurable hm'.snd
  have hfi : ∀ n, Integrable (f n) P' := by
    intro n
    refine Integrable.of_bound (hfm.inf aestronglyMeasurable_const) (n : ℝ) ?_
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hw0 _) (Nat.cast_nonneg n))]
      exact min_le_right _ _
  have hfb : ∀ n, ∫ x, f n x ∂P' ≤ 1 + B := by
    intro n
    have ht := hconv (SharpLSI.truncW hw hw0
      (BoundedContinuousFunction.const (E × ℝ) (1 : ℝ)) (n : ℝ))
    simp only [SharpLSI.truncW_apply, BoundedContinuousFunction.const_apply, mul_one] at ht
    refine le_of_tendsto ht (Eventually.of_forall fun k => ?_)
    exact (integral_mono ((hi k).inf (integrable_const _)) (hi k)
      (fun x => min_le_left _ _)).trans (hfirst k)
  have hflim : ∀ᵐ x ∂P', Tendsto (fun n => f n x) atTop (𝓝 (w (U' x))) := by
    refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
    have he : ∀ᶠ n : ℕ in atTop, w (U' x) ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [he] with n hn
    exact (min_eq_left hn).symm
  obtain ⟨hlimi, -⟩ := SharpLSI.integrable_of_ae_tendsto_of_integral_le
    (fun n x => le_min (hw0 _) (Nat.cast_nonneg n)) hfi hfb hflim
  exact ⟨hlimi, fun Φ => SharpLSI.tendsto_weighted_gen hconv hw hw0 hp hm hm' hi hpi hB hlimi Φ⟩

end DGPS.Lipschitz
