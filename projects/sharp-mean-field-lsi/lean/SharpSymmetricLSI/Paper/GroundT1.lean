import SharpSymmetricLSI.Paper.GroundState
import SharpSymmetricLSI.Infra.ChainRule
import SharpSymmetricLSI.Paper.CondForce1

/-!
# R30 groundwork: weak calculus with Lipschitz factors

* Product rule `∇(f h) = (∇f) h + f ∇h` for an integrable weak-gradient pair `(f, g)` and a
  bounded measurable `h` with a bounded weak gradient: mollify `f` (smooth periodic `moll n f`),
  apply the smooth product rule with the roles exchanged, and pass to the `L¹` limit (all
  multipliers are bounded).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem lintegral_enorm_mul_sub_le {a u v : UnitAddTorus ι → ℝ} {B : ℝ} (ha : ∀ y, |a y| ≤ B) :
    ∫⁻ y, ‖a y * u y - a y * v y‖ₑ ≤ ENNReal.ofReal B * ∫⁻ y, ‖u y - v y‖ₑ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  rw [← mul_sub, enorm_mul, Real.enorm_eq_ofReal_abs (a y)]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (ha y)) _

omit [DecidableEq ι] in
theorem tendsto_lintegral_mul_sub {a : UnitAddTorus ι → ℝ} {B : ℝ} (ha : ∀ y, |a y| ≤ B)
    {u : ℕ → UnitAddTorus ι → ℝ} {v : UnitAddTorus ι → ℝ}
    (h : Tendsto (fun n => ∫⁻ y, ‖u n y - v y‖ₑ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ y, ‖a y * u n y - a y * v y‖ₑ) atTop (𝓝 0) := by
  have h2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B) h (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => bot_le)
    fun n => lintegral_enorm_mul_sub_le ha

omit [DecidableEq ι] in
theorem integrable_bdd_mul {a u : UnitAddTorus ι → ℝ} {B : ℝ} (ha : ∀ y, |a y| ≤ B)
    (ham : AEStronglyMeasurable a volume) (hu : Integrable u volume) :
    Integrable (fun y => a y * u y) volume :=
  hu.bdd_mul ham (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact ha y)

/-- **Product rule with a Lipschitz factor.** -/
theorem IsWeakGrad.mul_lip {f : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (hf : IsWeakGrad f g) (hfi : Integrable f volume) (hgi : ∀ k, Integrable (fun y => g y k) volume)
    {h : UnitAddTorus ι → ℝ} {gh : UnitAddTorus ι → ι → ℝ} (hh : IsWeakGrad h gh)
    (hc : Measurable h) {B L : ℝ} (hB : ∀ y, |h y| ≤ B)
    (hghm : ∀ k, Measurable fun y => gh y k) (hL : ∀ y k, |gh y k| ≤ L) :
    IsWeakGrad (fun y => f y * h y) (fun y k => g y k * h y + f y * gh y k) := by
  have hhm : AEStronglyMeasurable h volume := hc.aestronglyMeasurable
  have hhi : Integrable h volume := integrable_of_bdd hc hB
  have hghi : ∀ k, Integrable (fun y => gh y k) volume := fun k => integrable_of_bdd (hghm k)
    fun y => hL y k
  -- smooth approximations of `f`
  have hpair : ∀ n, IsWeakGrad (fun y => h y * moll n f y)
      (fun y k => gh y k * moll n f y + h y * moll n (fun z => g z k) y) := by
    intro n
    have hΘ : ContDiff ℝ ∞ (mollL n (f ∘ liftT)) :=
      contDiff_mollL n (locallyIntegrable_comp_liftT hfi)
    have hper : IsPer (mollL n (f ∘ liftT)) := fun m x => mollL_comp_liftT_add n f x m
    have := hh.mul_smooth hΘ hper
    have e : ∀ y k, Dk (mollL n (f ∘ liftT)) k (secT y) = moll n (fun z => g z k) y := by
      intro y k
      simp only [Dk]
      rw [fderiv_mollL_of_isWeakGrad hf n (secT y) k]
      rfl
    simp only [e] at this
    exact this
  have hmi : ∀ n, Integrable (moll n f) volume := fun n => integrable_moll n hfi
  have hmgi : ∀ n k, Integrable (moll n fun z => g z k) volume := fun n k => integrable_moll n (hgi k)
  have key := isWeakGrad_of_tendsto hpair
    (fun n => integrable_bdd_mul hB hhm (hmi n))
    (fun n k => (integrable_bdd_mul (fun y => hL y k) (hghm k).aestronglyMeasurable (hmi n)).add
      (integrable_bdd_mul hB hhm (hmgi n k)))
    (integrable_bdd_mul hB hhm hfi)
    (fun k => (integrable_bdd_mul (fun y => hL y k) (hghm k).aestronglyMeasurable hfi).add
      (integrable_bdd_mul hB hhm (hgi k)))
    (tendsto_lintegral_mul_sub hB (tendsto_moll hfi)) (fun k => ?_)
  · have e1 : (fun y => f y * h y) = fun y => h y * f y := by funext y; ring
    have e2 : (fun y k => g y k * h y + f y * gh y k) = fun y k => gh y k * f y + h y * g y k := by
      funext y k; ring
    rw [e1, e2]; exact key
  · have h1 := tendsto_lintegral_mul_sub (fun y => hL y k) (tendsto_moll hfi)
    have h2 := tendsto_lintegral_mul_sub hB (tendsto_moll (hgi k))
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => bot_le)
      fun n => ?_
    have hm1 : AEMeasurable (fun y => ‖gh y k * moll n f y - gh y k * f y‖ₑ) volume :=
      ((integrable_bdd_mul (fun y => hL y k) (hghm k).aestronglyMeasurable (hmi n)).sub
        (integrable_bdd_mul (fun y => hL y k) (hghm k).aestronglyMeasurable hfi)).aemeasurable.enorm
    refine (lintegral_mono fun y => ?_).trans (le_of_eq (lintegral_add_left' hm1 _))
    have : gh y k * moll n f y + h y * moll n (fun z => g z k) y - (gh y k * f y + h y * g y k) =
        (gh y k * moll n f y - gh y k * f y) + (h y * moll n (fun z => g z k) y - h y * g y k) := by
      ring
    simp only [Pi.add_apply]
    rw [this]
    exact enorm_add_le _ _

end SharpLSI
