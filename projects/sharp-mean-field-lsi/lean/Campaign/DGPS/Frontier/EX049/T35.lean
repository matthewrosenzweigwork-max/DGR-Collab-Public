import DGPS.Circle.StationaryFlux
import DGPS.Frontier.EX049.T25
import DGPS.Frontier.EX049.T32
import DGPS.Frontier.EX049.T33
import DGPS.Frontier.EX049.T34

/-!
# EX049.35: Periodic C1 multipliers

Task id: EX049.35 (node EX049, leaf formalization, Wave 7).

Let `a : ℝ → ℝ` be `C¹` and `2π`-periodic. Then `a` and `a'` are bounded on the fundamental
interval `[0, 2π]`, and multiplication by the induced circle function preserves the angular
`H¹` class, with weak derivative `a' v + a v'`.

## Provides

- `DGPS.Frontier.EX049.ex049_35_periodic_c1_multipliers`: the full statement, a conjunction of
  four claims: (1) `a` and `a'` are bounded on `[0, 2π]`; (2) the circle derivative of the lift
  of `a` is `a'`; (3) for every angular weak pair `(v, g)`, the pair `(a v, a' v + a g)` is an
  angular weak pair; (4) multiplication by the lift maps `AngularH1` into `AngularH1`.
- Helpers, each with full name `DGPS.Frontier.EX049.<name>`:
  - `continuous_of_coe_EX04935`: a circle function whose real lift is continuous is continuous.
  - `bound_EX04935`: `a` and `a'` are bounded on all of `ℝ`, by periodicity.
  - `angDeriv_coe_EX04935`: the circle derivative of a lift of `a` is `deriv a`.
  - `memLp_coe_EX04935`: an `L²` function for Haar measure is `L²` on `Ioo 0 (2π)` after lifting.
  - `memLp_bdd_mul_EX04935`: a bounded continuous multiplier preserves `L²` for Haar measure.
  - `integral_interval_EX04935`, `interval_congr_EX04935`: interval and `Ioo` integral bookkeeping.
  - `core_EX04935`: interval integration by parts against smooth periodic test functions.
  - `weak_Ioo_EX04935`: the circle weak identity restated on `Ioo 0 (2π)`.
  - `circle_mul_EX04935`: the weak-pair statement for an arbitrary lift `c` of `a`.

## R5 notes

- The multiplier is `a : ℝ → ℝ` with `ContDiff ℝ 1 a` and `Function.Periodic a (2 * π)`. The
  circle multiplier is `hper.lift : AngCircle → ℝ`, the function with `hper.lift ↑s = a s`.
  The specification's "periodic C1 function" is read as this pair.
- The circle derivative `a'` is `angDeriv hper.lift`. By `angDeriv_coe` it equals `deriv a` at
  every real representative, which is claim (2).
- "Bounded on a fundamental interval" is kept in its literal form,
  `∃ M, ∀ x ∈ Icc 0 (2π), |a x| ≤ M ∧ |deriv a x| ≤ M`. The proof obtains the bound on all of
  `ℝ` by periodicity, and this stronger form is used internally.
- Absolute continuity, a.e. derivatives and `L²` memberships are Mathlib's
  `AbsolutelyContinuousOnInterval`, `deriv` and `MemLp`, as in EX049.34. The weak derivative
  identity is the `IsAngularWeakDeriv` structure of `AngularNormalization`, tested against smooth
  circle functions, using the interval form of EX049.25.
- The product is stated for every angular weak pair `(v, g)`, with no extra hypothesis on `v`.
  The public `AngularH1` competitor domain is unchanged.
- The multiplier is only required to be `C¹` (not smooth). Test functions in the proof are smooth
  periodic functions, so no density of `C¹` test functions is needed. The route is the periodic
  AC representative of EX049.32 combined with the AC product rule of EX049.34.
- No hypothesis beyond `ContDiff` and periodicity is added. No sign, positivity or `a ≤ b`
  assumption is used.
-/

namespace DGPS.Frontier.EX049

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.AngularNormalization

/-! ### Continuity, bounds and lifts -/

lemma continuous_of_coe_EX04935 {F : AngCircle → ℝ}
    (h : Continuous fun s : ℝ => F (s : AngCircle)) : Continuous F := by
  have hq : Topology.IsQuotientMap ((↑) : ℝ → AngCircle) := QuotientAddGroup.isQuotientMap_mk _
  exact hq.continuous_iff.2 h

lemma bound_EX04935 {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a) (hper : Function.Periodic a (2 * π)) :
    ∃ M : ℝ, ∀ x : ℝ, |a x| ≤ M ∧ |deriv a x| ≤ M := by
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (ha.continuous.continuousOn (s := Icc (0 : ℝ) (2 * π)))
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((ha.continuous_deriv le_rfl).continuousOn (s := Icc (0 : ℝ) (2 * π)))
  refine ⟨max C₁ C₂, fun x => ⟨?_, ?_⟩⟩
  · obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos x
    have h := hC₁ y (Ico_subset_Icc_self hy)
    rw [hxy, ← Real.norm_eq_abs]
    exact h.trans (le_max_left _ _)
  · obtain ⟨y, hy, hxy⟩ :=
      (DGPS.Circle.StationaryFlux.periodic_deriv hper).exists_mem_Ico₀ Real.two_pi_pos x
    have h := hC₂ y (Ico_subset_Icc_self hy)
    rw [hxy, ← Real.norm_eq_abs]
    exact h.trans (le_max_right _ _)

lemma angDeriv_coe_EX04935 {a : ℝ → ℝ} {c : AngCircle → ℝ}
    (hc : ∀ s : ℝ, c (s : AngCircle) = a s) (s : ℝ) :
    angDeriv c (s : AngCircle) = deriv a s := by
  rw [DGPS.Circle.StationaryFlux.angDeriv_coe]
  have e : DGPS.Circle.StationaryFlux.lift c = a := by
    funext t
    exact hc t
  rw [e]

/-! ### Measure transport and multiplication -/

lemma memLp_coe_EX04935 {v : AngCircle → ℝ} (hv : MemLp v 2 angHaar) :
    MemLp (fun x : ℝ => v (x : AngCircle)) 2 (volume.restrict (Ioo 0 (2 * π))) := by
  rw [angHaar_eq_map_normalized_EX04925 0] at hv
  have hm : Measurable ((↑) : ℝ → AngCircle) := AddCircle.measurable_mk'
  have h1 := (memLp_map_measure_iff hv.aestronglyMeasurable hm.aemeasurable).1 hv
  have hpos : ENNReal.ofReal (2 * π) ≠ 0 := (ENNReal.ofReal_pos.2 Real.two_pi_pos).ne'
  have hfin : ENNReal.ofReal (2 * π) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 := h1.smul_measure hfin
  rw [smul_smul, ENNReal.mul_inv_cancel hpos hfin, one_smul, zero_add] at h2
  have hIoo : volume.restrict (Ioo (0 : ℝ) (2 * π)) = volume.restrict (Ioc (0 : ℝ) (2 * π)) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [hIoo]
  exact h2

lemma memLp_bdd_mul_EX04935 {c v : AngCircle → ℝ} {M : ℝ} (hc : Continuous c)
    (hcM : ∀ θ, |c θ| ≤ M) (hv : MemLp v 2 angHaar) :
    MemLp (fun θ => c θ * v θ) 2 angHaar := by
  refine MemLp.of_le_mul (c := M) hv (hc.aestronglyMeasurable.mul hv.aestronglyMeasurable) ?_
  refine ae_of_all _ fun θ => ?_
  have h1 : ‖c θ‖ ≤ M := by
    rw [Real.norm_eq_abs]
    exact hcM θ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

lemma integral_interval_EX04935 {T : ℝ} (hT : 0 ≤ T) (H : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..T, H x = ∫ x in Ioo 0 T, H x := by
  rw [intervalIntegral.integral_of_le hT, integral_Ioc_eq_integral_Ioo]

lemma interval_congr_EX04935 {H K : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 T → H x = K x) :
    ∫ x in (0 : ℝ)..T, H x = ∫ x in (0 : ℝ)..T, K x := by
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_ae measurableSet_Ioo h

/-! ### The interval integration by parts -/

lemma core_EX04935 {a F g φ : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (hper : Function.Periodic a (2 * π)) (hFp : Function.Periodic F (2 * π))
    (hFac : ∀ x y : ℝ, AbsolutelyContinuousOnInterval F x y)
    (hFg : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 (2 * π) → deriv F x = g x)
    (hgL : MemLp g 2 (volume.restrict (Ioo 0 (2 * π))))
    (hφ : ContDiff ℝ ∞ φ) (hφp : Function.Periodic φ (2 * π)) :
    ∫ x in (0 : ℝ)..(2 * π), a x * F x * deriv φ x
      = -∫ x in (0 : ℝ)..(2 * π), (deriv a x * F x + a x * g x) * φ x := by
  have hae : deriv F =ᵐ[volume.restrict (Ioo 0 (2 * π))] g :=
    (ae_restrict_iff' measurableSet_Ioo).2 hFg
  have hdF : MemLp (deriv F) 2 (volume.restrict (Ioo 0 (2 * π))) := hgL.ae_eq hae.symm
  have hda : MemLp (deriv a) 2 (volume.restrict (Ioo 0 (2 * π))) := by
    obtain ⟨M, hM⟩ := bound_EX04935 ha hper
    exact MemLp.of_bound (ha.continuous_deriv le_rfl).aestronglyMeasurable M
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact (hM x).2)
  have hAac : AbsolutelyContinuousOnInterval a 0 (2 * π) :=
    ContDiffOn.absolutelyContinuousOnInterval ha.contDiffOn
  have hφac : AbsolutelyContinuousOnInterval φ 0 (2 * π) :=
    ContDiffOn.absolutelyContinuousOnInterval (hφ.of_le (by exact_mod_cast le_top)).contDiffOn
  obtain ⟨hPac, hPder, -⟩ :=
    ex049_34_ac_products_h1_bounds_interval (hFac 0 (2 * π)) hAac hdF hda
  have hIBP := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hPac hφac
  have hPint : ∫ x in (0 : ℝ)..(2 * π), deriv (fun y => F y * a y) x * φ x
      = ∫ x in (0 : ℝ)..(2 * π), (deriv a x * F x + a x * g x) * φ x := by
    refine interval_congr_EX04935 Real.two_pi_pos.le ?_
    filter_upwards [hPder, hFg] with x h1 h2 hx
    rw [h1 hx, h2 hx]
    ring
  have hP : ∫ x in (0 : ℝ)..(2 * π), a x * F x * deriv φ x
      = ∫ x in (0 : ℝ)..(2 * π), F x * a x * deriv φ x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    show a x * F x * deriv φ x = F x * a x * deriv φ x
    ring
  have hB : F (2 * π) * a (2 * π) * φ (2 * π) - F 0 * a 0 * φ 0 = 0 := by
    have e1 : F (2 * π) = F 0 := by
      have := hFp 0
      rwa [zero_add] at this
    have e2 : a (2 * π) = a 0 := by
      have := hper 0
      rwa [zero_add] at this
    have e3 : φ (2 * π) = φ 0 := by
      have := hφp 0
      rwa [zero_add] at this
    rw [e1, e2, e3]
    ring
  rw [hP]
  linarith [hIBP, hPint, hB]

/-! ### The circle statement -/

lemma weak_Ioo_EX04935 {v g : AngCircle → ℝ}
    (hibp : ∀ ψ : AngCircle → ℝ, IsSmoothAngular ψ →
      ∫ x in (0 : ℝ)..(2 * π), v (x : AngCircle) * deriv (fun s : ℝ => ψ (s : AngCircle)) x
        = -∫ x in (0 : ℝ)..(2 * π), g (x : AngCircle) * ψ (x : AngCircle)) :
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → Function.Periodic φ (2 * π) →
      ∫ x in Ioo 0 (2 * π), v (x : AngCircle) * deriv φ x
        = -∫ x in Ioo 0 (2 * π), g (x : AngCircle) * φ x := by
  intro φ hφ hφp
  have hlift : (fun s : ℝ => hφp.lift (s : AngCircle)) = φ := funext hφp.lift_coe
  have hsm : IsSmoothAngular hφp.lift := by
    show ContDiff ℝ ∞ (fun s : ℝ => hφp.lift (s : AngCircle))
    rw [hlift]
    exact hφ
  have h := hibp hφp.lift hsm
  simp only [hφp.lift_coe] at h
  rw [integral_interval_EX04935 Real.two_pi_pos.le (fun x => v (x : AngCircle) * deriv φ x),
    integral_interval_EX04935 Real.two_pi_pos.le (fun x => g (x : AngCircle) * φ x)] at h
  exact h

lemma circle_mul_EX04935 {a : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (hper : Function.Periodic a (2 * π))
    {c : AngCircle → ℝ} (hc : ∀ s : ℝ, c (s : AngCircle) = a s) {v g : AngCircle → ℝ}
    (hvg : IsAngularWeakDeriv v g) :
    IsAngularWeakDeriv (fun θ => c θ * v θ) (fun θ => angDeriv c θ * v θ + c θ * g θ) := by
  obtain ⟨M, hM⟩ := bound_EX04935 ha hper
  have hcont : Continuous c := by
    refine continuous_of_coe_EX04935 ?_
    have e : (fun s : ℝ => c (s : AngCircle)) = a := funext hc
    rw [e]
    exact ha.continuous
  have hdc : Continuous (angDeriv c) := by
    refine continuous_of_coe_EX04935 ?_
    have e : (fun s : ℝ => angDeriv c (s : AngCircle)) = deriv a :=
      funext (angDeriv_coe_EX04935 hc)
    rw [e]
    exact ha.continuous_deriv le_rfl
  have hcM : ∀ θ, |c θ| ≤ M := by
    intro θ
    obtain ⟨s, rfl⟩ := DGPS.Circle.StationaryFlux.exists_coe θ
    rw [hc s]
    exact (hM s).1
  have hdM : ∀ θ, |angDeriv c θ| ≤ M := by
    intro θ
    obtain ⟨s, rfl⟩ := DGPS.Circle.StationaryFlux.exists_coe θ
    rw [angDeriv_coe_EX04935 hc s]
    exact (hM s).2
  obtain ⟨hv, hg, hibp⟩ := (isAngularWeakDeriv_iff_interval_EX04925 v g).1 hvg
  rw [isAngularWeakDeriv_iff_interval_EX04925]
  refine ⟨memLp_bdd_mul_EX04935 hcont hcM hv,
    (memLp_bdd_mul_EX04935 hdc hdM hv).add (memLp_bdd_mul_EX04935 hcont hcM hg), ?_⟩
  intro ψ hψ
  -- The derivative of `v` on `(0, 2π)`: its periodic AC representative `F`.
  have hweak := weak_Ioo_EX04935 hibp
  obtain ⟨c₀, -, -, F, ⟨-, hFp, hFac, hFint, hFf⟩, -⟩ :=
    ex049_32_periodic_weak_pairs_have_periodic_ac (2 * π) Real.two_pi_pos
      (fun x : ℝ => v (x : AngCircle)) (fun x : ℝ => g (x : AngCircle))
      (memLp_coe_EX04935 hv) (memLp_coe_EX04935 hg) hweak
  have hL1 : IntervalIntegrable (fun x : ℝ => g (x : AngCircle)) volume 0 (2 * π) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le Real.two_pi_pos.le]
    exact (memLp_coe_EX04935 hg).integrable one_le_two
  have hFg : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 (2 * π) → deriv F x = g (x : AngCircle) := by
    filter_upwards [hL1.ae_hasDerivAt_integral] with x hx hxI
    have hxU : x ∈ uIcc (0 : ℝ) (2 * π) := by
      rw [uIcc_of_le Real.two_pi_pos.le]
      exact Ioo_subset_Icc_self hxI
    have hD := (hx hxU 0 left_mem_uIcc).const_add c₀
    have hev : F =ᶠ[𝓝 x] fun y => c₀ + ∫ t in (0 : ℝ)..y, g (t : AngCircle) := by
      filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
      exact hFint y (Ioo_subset_Icc_self hy)
    exact (hD.congr_of_eventuallyEq hev).deriv
  have hFv : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 (2 * π) → F x = v (x : AngCircle) :=
    (ae_restrict_iff' measurableSet_Ioo).1 hFf
  have hkey := core_EX04935 ha hper hFp hFac hFg (memLp_coe_EX04935 hg)
    (hψ : ContDiff ℝ ∞ (fun s : ℝ => ψ (s : AngCircle))) (periodic_lift_EX04933 ψ)
  have hL : ∫ x in (0 : ℝ)..(2 * π),
      a x * v (x : AngCircle) * deriv (fun s : ℝ => ψ (s : AngCircle)) x
      = ∫ x in (0 : ℝ)..(2 * π), a x * F x * deriv (fun s : ℝ => ψ (s : AngCircle)) x :=
    interval_congr_EX04935 Real.two_pi_pos.le (by
      filter_upwards [hFv] with x hx hxI
      simp only [hx hxI])
  have hR : ∫ x in (0 : ℝ)..(2 * π),
      (deriv a x * v (x : AngCircle) + a x * g (x : AngCircle)) * ψ (x : AngCircle)
      = ∫ x in (0 : ℝ)..(2 * π), (deriv a x * F x + a x * g (x : AngCircle)) * ψ (x : AngCircle) :=
    interval_congr_EX04935 Real.two_pi_pos.le (by
      filter_upwards [hFv] with x hx hxI
      simp only [hx hxI])
  simp only [hc, angDeriv_coe_EX04935 hc]
  rw [hL, hR]
  exact hkey

/-! ### Main statement -/

/-- EX049.35: a real `C¹`, `2π`-periodic multiplier `a` and its derivative are bounded on
`[0, 2π]`; the circle multiplier `hper.lift` has circle derivative `a'`; and multiplication by it
sends angular weak pairs `(v, g)` to the pair `(a v, a' v + a g)`, hence preserves `AngularH1`. -/
theorem ex049_35_periodic_c1_multipliers (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a)
    (hper : Function.Periodic a (2 * π)) :
    (∃ M : ℝ, ∀ x ∈ Icc (0 : ℝ) (2 * π), |a x| ≤ M ∧ |deriv a x| ≤ M) ∧
    (∀ s : ℝ, angDeriv (hper.lift : AngCircle → ℝ) (s : AngCircle) = deriv a s) ∧
    (∀ v g : AngCircle → ℝ, IsAngularWeakDeriv v g →
      IsAngularWeakDeriv (fun θ => (hper.lift : AngCircle → ℝ) θ * v θ)
        (fun θ => angDeriv (hper.lift : AngCircle → ℝ) θ * v θ
          + (hper.lift : AngCircle → ℝ) θ * g θ)) ∧
    (∀ v : AngCircle → ℝ, AngularH1 v →
      AngularH1 (fun θ => (hper.lift : AngCircle → ℝ) θ * v θ)) := by
  obtain ⟨M, hM⟩ := bound_EX04935 ha hper
  have hc : ∀ s : ℝ, (hper.lift : AngCircle → ℝ) (s : AngCircle) = a s :=
    fun s => hper.lift_coe s
  refine ⟨⟨M, fun x _ => hM x⟩, fun s => angDeriv_coe_EX04935 hc s,
    fun v g hvg => circle_mul_EX04935 ha hper hc hvg, ?_⟩
  intro v hv
  obtain ⟨g, hvg⟩ := hv
  unfold AngularH1
  exact ⟨_, circle_mul_EX04935 ha hper hc hvg⟩

end DGPS.Frontier.EX049
