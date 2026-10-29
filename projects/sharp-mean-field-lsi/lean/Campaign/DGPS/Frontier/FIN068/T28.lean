import Mathlib

/-!
# FIN068.28: One parameter derivative under a compact integral

Provides:
* `DGPS.Frontier.FIN068.fin068_28_one_parameter_derivative_compact_integral`: for finite-dimensional
  real normed spaces `E`, `F`, an open `U ⊆ E` and `H : ℝ → E → F` jointly continuous on
  `[0,1] × U`, differentiable in the second argument with `p ↦ D_p H(t, p)` jointly continuous on
  `[0,1] × U`, the map `p ↦ ∫₀¹ H(t,p) dt` has Fréchet derivative `∫₀¹ D_p H(t,p) dt` at every
  `p ∈ U`.
* `DGPS.Frontier.FIN068.fin068_28_one_parameter_derivative_compact_integral_differentiableOn`: the
  same hypotheses give `DifferentiableOn ℝ (fun p => ∫ t in 0..1, H t p) U` together with the
  derivative formula `fderiv ℝ (fun p => ∫ t in 0..1, H t p) p = ∫ t in 0..1, fderiv ℝ (H t) p`
  for `p ∈ U`.
* Helpers: `DGPS.Frontier.FIN068.aestronglyMeasurable_uIoc_FIN06828` (continuous on `[0,1]` implies
  a.e. strongly measurable on `uIoc 0 1`), `DGPS.Frontier.FIN068.intervalIntegrable_Icc_FIN06828`
  (continuous on `[0,1]` implies interval integrable) and
  `DGPS.Frontier.FIN068.hasFDerivAt_integral_FIN06828` (the pointwise statement behind the main
  theorem).

R5 notes:
* The function `H : [0,1] × U → F` is encoded as `H : ℝ → E → F`; only its values on
  `Set.Icc 0 1 ×ˢ U` are used, and "jointly continuous" is `ContinuousOn (Function.uncurry H)
  (Set.Icc 0 1 ×ˢ U)`.
* "Differentiable in its second argument" is `DifferentiableAt ℝ (H t) p` for `t ∈ [0,1]`,
  `p ∈ U` (equivalent to differentiability on the open set `U`). `D_p H` is `fderiv ℝ (H t) p`,
  with codomain `E →L[ℝ] F`; no separate derivative function is introduced, and joint continuity
  of the derivative is `ContinuousOn (fun q : ℝ × E => fderiv ℝ (H q.1) q.2) (Set.Icc 0 1 ×ˢ U)`.
* The integral `∫₀¹` is the interval integral `∫ t in (0:ℝ)..1` (Lebesgue measure).
* Finite dimensionality of `E` and `F` is used for properness of `E` (compact closed balls) and
  completeness of `F`; no hypothesis beyond the specification is added.
* Non-literal reading: the specification's "differentiable" is the real Fréchet derivative.
  Joint continuity of `H` itself is only needed for integrability and measurability in `t`; the
  stated uniform bound comes from continuity of the derivative on a compact product.
-/

open MeasureTheory Set Metric

namespace DGPS.Frontier.FIN068

/-- A function continuous on `[0,1]` is a.e. strongly measurable for the restriction of Lebesgue
measure to `uIoc 0 1`. -/
theorem aestronglyMeasurable_uIoc_FIN06828
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ → G}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    AEStronglyMeasurable f (volume.restrict (uIoc (0 : ℝ) 1)) := by
  rw [uIoc_of_le zero_le_one]
  exact (hf.aestronglyMeasurable measurableSet_Icc).mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

/-- A function continuous on `[0,1]` is interval integrable on `0..1`. -/
theorem intervalIntegrable_Icc_FIN06828
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ → G}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    IntervalIntegrable f volume 0 1 :=
  hf.intervalIntegrable_of_Icc zero_le_one

/-- Core step at one point: derivative under the integral sign at `p ∈ U`. -/
theorem hasFDerivAt_integral_FIN06828
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {H : ℝ → E → F}
    (hH : ContinuousOn (Function.uncurry H) (Icc (0 : ℝ) 1 ×ˢ U))
    (hdiff : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, DifferentiableAt ℝ (H t) p)
    (hD : ContinuousOn (fun q : ℝ × E => fderiv ℝ (H q.1) q.2) (Icc (0 : ℝ) 1 ×ˢ U))
    {p : E} (hp : p ∈ U) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, H t x)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (H t) p) p := by
  have : CompleteSpace F := FiniteDimensional.complete ℝ F
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU p hp
  -- a smaller closed ball inside `U`
  have hcl : closedBall p (r / 2) ⊆ U :=
    (closedBall_subset_ball (by linarith)).trans hrU
  have hcomp : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall p (r / 2)) :=
    isCompact_Icc.prod (isCompact_closedBall p (r / 2))
  have hsub : Icc (0 : ℝ) 1 ×ˢ closedBall p (r / 2) ⊆ Icc (0 : ℝ) 1 ×ˢ U :=
    prod_mono (Subset.refl _) hcl
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn (hD.mono hsub)
  have hs : closedBall p (r / 2) ∈ nhds p := closedBall_mem_nhds p (by linarith)
  -- slices
  have hslice : ∀ x ∈ U, ContinuousOn (fun t => H t x) (Icc (0 : ℝ) 1) := by
    intro x hx
    have : ContinuousOn (fun t : ℝ => (t, x)) (Icc (0 : ℝ) 1) :=
      (continuousOn_id.prodMk continuousOn_const)
    exact hH.comp this (fun t ht => ⟨ht, hx⟩)
  have hsliceD : ContinuousOn (fun t => fderiv ℝ (H t) p) (Icc (0 : ℝ) 1) := by
    have : ContinuousOn (fun t : ℝ => (t, p)) (Icc (0 : ℝ) 1) :=
      (continuousOn_id.prodMk continuousOn_const)
    exact hD.comp this (fun t ht => ⟨ht, hp⟩)
  have hIoc : uIoc (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F := fun x t => H t x) (F' := fun x t => fderiv ℝ (H t) x)
    (bound := fun _ => C) (μ := volume) hs ?_ ?_ ?_ ?_ ?_ ?_
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds p hr) fun x hx => ?_
    exact aestronglyMeasurable_uIoc_FIN06828 (hslice x (hrU hx))
  · exact intervalIntegrable_Icc_FIN06828 (hslice p hp)
  · exact aestronglyMeasurable_uIoc_FIN06828 hsliceD
  · refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun t ht x hx => ?_)
    rw [hIoc] at ht
    exact hC (t, x) ⟨Ioc_subset_Icc_self ht, hx⟩
  · exact intervalIntegrable_const
  · refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun t ht x hx => ?_)
    rw [hIoc] at ht
    exact (hdiff t (Ioc_subset_Icc_self ht) x (hcl hx)).hasFDerivAt

/-- **FIN068.28.** Differentiation of `p ↦ ∫₀¹ H(t,p) dt` under the integral sign. -/
theorem fin068_28_one_parameter_derivative_compact_integral
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {H : ℝ → E → F}
    (hH : ContinuousOn (Function.uncurry H) (Icc (0 : ℝ) 1 ×ˢ U))
    (hdiff : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, DifferentiableAt ℝ (H t) p)
    (hD : ContinuousOn (fun q : ℝ × E => fderiv ℝ (H q.1) q.2) (Icc (0 : ℝ) 1 ×ˢ U)) :
    ∀ p ∈ U, HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, H t x)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (H t) p) p :=
  fun _ hp => hasFDerivAt_integral_FIN06828 hU hH hdiff hD hp

/-- Differentiability on `U` and the formula for the Fréchet derivative of the parameter
integral. -/
theorem fin068_28_one_parameter_derivative_compact_integral_differentiableOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {H : ℝ → E → F}
    (hH : ContinuousOn (Function.uncurry H) (Icc (0 : ℝ) 1 ×ˢ U))
    (hdiff : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ U, DifferentiableAt ℝ (H t) p)
    (hD : ContinuousOn (fun q : ℝ × E => fderiv ℝ (H q.1) q.2) (Icc (0 : ℝ) 1 ×ˢ U)) :
    DifferentiableOn ℝ (fun x => ∫ t in (0 : ℝ)..1, H t x) U ∧
      ∀ p ∈ U, fderiv ℝ (fun x => ∫ t in (0 : ℝ)..1, H t x) p
        = ∫ t in (0 : ℝ)..1, fderiv ℝ (H t) p :=
  ⟨fun p hp => (fin068_28_one_parameter_derivative_compact_integral hU hH hdiff hD p hp
      ).differentiableAt.differentiableWithinAt,
   fun p hp => (fin068_28_one_parameter_derivative_compact_integral hU hH hdiff hD p hp
      ).fderiv⟩

end DGPS.Frontier.FIN068
