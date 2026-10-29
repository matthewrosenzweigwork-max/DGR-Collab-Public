import DGPS.Circle.AngularNormalization
import DGPS.Frontier.EX049.T25
import DGPS.Frontier.EX049.T31
import DGPS.Frontier.EX049.T32
import DGPS.Frontier.EX049.T33

/-!
# EX049.02: Angular H1 has an absolutely continuous representative

Task id: EX049.02 (node EX049, the engineered rank-one sharp species).
Title: Angular H1 has an absolutely continuous representative.

Every real angular `H¹` function `u` on the circle `AngCircle = AddCircle (2π)` has a unique
continuous representative `v`. Its restriction to `[0, 2π]` is absolutely continuous, and its
almost-everywhere derivative on `(0, 2π)` is the angular weak derivative `g` of `u`. The two
endpoint values of `v` agree. Circle integrals of functions of `(v, g)` equal `(2π)⁻¹` times the
corresponding interval integrals over `[0, 2π]`.

Provides (every name is in the namespace `DGPS.Frontier.EX049`):
* `ex049_02_angular_h1_has_absolutely_continuous_representative`: the main statement above,
  for every `u` with `AngularH1 u`.
* `memLp_interval_EX04902`: an `L²` function on the circle gives an `L²` function on `(0, 2π)`.
* `qmp_EX04902`: the coordinate map `ℝ → AngCircle` is quasi-measure-preserving from
  `(0, 2π]` to `angHaar`.
* `ae_Ioc_EX04902` and `ae_Ioo_EX04902`: a circle almost-everywhere equality pulls back to the
  fundamental interval.
* `ae_circle_EX04902`: an almost-everywhere equality on the fundamental interval, for measurable
  circle functions, gives almost-everywhere equality on the circle.
* `cont_lift_EX04902`: a continuous periodic real function descends to a continuous circle
  function.
* `weak_interval_EX04902`: the angular weak identity restated on the open interval `(0, 2π)`.

R5 notes:
* The representative is the circle lift of the continuous periodic function supplied by
  EX049.32, applied to the fundamental-interval restrictions of `u` and of a weak derivative.
  Uniqueness is the uniqueness clause of EX049.32, transported to the circle. It is stated among
  all continuous circle functions that agree with `u` almost everywhere.
* The derivative conjunct quantifies over every weak derivative `g` of `u`. It is stated on the
  open interval `(0, 2π)`. The complement `{0, 2π}` is a null set, so this is the almost-everywhere
  statement of the specification. The representative does not depend on `g`; the proof re-runs
  EX049.32 for each `g` and identifies the outputs by its uniqueness clause.
* The integral identity uses the weak derivative `g` on the circle and on the interval, not the
  pointwise classical derivative. The two agree almost everywhere by the derivative conjunct.
* The integral identity holds for every `H : ℝ → ℝ → ℝ` for which `H (v θ) (g θ)` is integrable
  on the circle. No measurability is assumed of `H`. The integrability hypothesis is not used in
  the proof, because the change of variables of EX049.25 holds for every function. It is kept so
  that the statement is the one specified.
* The endpoint statement `v (0) = v (2π)` is trivial on the circle, since both points are the
  same point of `AddCircle (2π)`. It is included to match the specification.
* `angHaar` is the normalized Haar measure of EX049.25, and every almost-everywhere statement is
  with respect to it or to the fundamental-interval restriction of Lebesgue measure.
* `u` is not assumed measurable. Measurable versions of `u` and of the representative are used
  only where the transport lemma of EX049.33 requires measurability.
-/

namespace DGPS.Frontier.EX049

open MeasureTheory Set Filter Topology
open scoped ContDiff ENNReal
open Real
open DGPS.Circle.AngularNormalization

/-- An `L²` function on the circle gives an `L²` function on the open fundamental interval. -/
theorem memLp_interval_EX04902 {w : AngCircle → ℝ} (hw : MemLp w 2 angHaar) :
    MemLp (fun s : ℝ => w (s : AngCircle)) 2 (volume.restrict (Ioo 0 (2 * π))) := by
  have hne : ENNReal.ofReal (2 * π) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hM : Measure.map ((↑) : ℝ → AngCircle) (volume.restrict (Ioc 0 (2 * π)))
      = ENNReal.ofReal (2 * π) • angHaar := by
    have h := angHaar_eq_map_EX04925 0
    rw [zero_add] at h
    rw [h, smul_smul, ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top, one_smul]
  have hw' : MemLp w 2
      (Measure.map ((↑) : ℝ → AngCircle) (volume.restrict (Ioc 0 (2 * π)))) := by
    rw [hM]
    exact hw.smul_measure ENNReal.ofReal_ne_top
  have hc : MemLp (w ∘ ((↑) : ℝ → AngCircle)) 2 (volume.restrict (Ioc 0 (2 * π))) :=
    hw'.comp_of_map AddCircle.measurable_mk'.aemeasurable
  have e : volume.restrict (Ioo 0 (2 * π)) = volume.restrict (Ioc 0 (2 * π)) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [e]
  exact hc

/-- The coordinate map from the half-open fundamental interval to the circle is
quasi-measure-preserving for the normalized Haar measure. -/
theorem qmp_EX04902 :
    Measure.QuasiMeasurePreserving ((↑) : ℝ → AngCircle) (volume.restrict (Ioc 0 (2 * π)))
      angHaar := by
  have h0 : (ENNReal.ofReal (2 * π))⁻¹ ≠ 0 := inv_ofReal_two_pi_ne_zero_EX04933
  refine ⟨AddCircle.measurable_mk', ?_⟩
  have h := angHaar_eq_map_EX04925 0
  rw [zero_add] at h
  rw [h]
  exact Measure.absolutelyContinuous_smul h0

/-- An almost-everywhere equality on the circle pulls back to the half-open fundamental interval. -/
theorem ae_Ioc_EX04902 {w u : AngCircle → ℝ} (h : w =ᵐ[angHaar] u) :
    (fun s : ℝ => w (s : AngCircle)) =ᵐ[volume.restrict (Ioc 0 (2 * π))]
      (fun s : ℝ => u (s : AngCircle)) :=
  qmp_EX04902.ae (p := fun θ => w θ = u θ) h

/-- An almost-everywhere equality on the circle pulls back to the open fundamental interval. -/
theorem ae_Ioo_EX04902 {w u : AngCircle → ℝ} (h : w =ᵐ[angHaar] u) :
    (fun s : ℝ => w (s : AngCircle)) =ᵐ[volume.restrict (Ioo 0 (2 * π))]
      (fun s : ℝ => u (s : AngCircle)) := by
  have e : volume.restrict (Ioo 0 (2 * π)) = volume.restrict (Ioc 0 (2 * π)) :=
    Measure.restrict_congr_set Ioo_ae_eq_Ioc
  rw [e]
  exact ae_Ioc_EX04902 h

/-- For measurable circle functions, almost-everywhere equality on the fundamental interval
gives almost-everywhere equality on the circle. -/
theorem ae_circle_EX04902 {w u : AngCircle → ℝ} (hw : Measurable w) (hu : Measurable u)
    (h : (fun s : ℝ => w (s : AngCircle)) =ᵐ[volume.restrict (Ioc 0 (2 * π))]
      (fun s : ℝ => u (s : AngCircle))) :
    w =ᵐ[angHaar] u := by
  have key := ex049_33_fundamental_interval_measure_transport_ae 0 hw hu
  rw [zero_add] at key
  exact key.2 h

/-- A continuous `2π`-periodic real function descends to a continuous function on the circle. -/
theorem cont_lift_EX04902 {F : ℝ → ℝ} (hF : Continuous F)
    (hper : Function.Periodic F (2 * π)) :
    Continuous (hper.lift : AngCircle → ℝ) :=
  (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2 * π))).continuous_iff.2 hF

/-- The angular weak identity, restated for the fundamental interval `(0, 2π)`. -/
theorem weak_interval_EX04902 {u g : AngCircle → ℝ} (hw : IsAngularWeakDeriv u g)
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hper : Function.Periodic φ (2 * π)) :
    ∫ x in Ioo 0 (2 * π), u (x : AngCircle) * deriv φ x =
      -∫ x in Ioo 0 (2 * π), g (x : AngCircle) * φ x := by
  have e : ∀ x : ℝ, (hper.lift : AngCircle → ℝ) (x : AngCircle) = φ x := fun x => rfl
  have hs : IsSmoothAngular (hper.lift : AngCircle → ℝ) := by
    show ContDiff ℝ ∞ (fun s : ℝ => (hper.lift : AngCircle → ℝ) (s : AngCircle))
    simpa only [e] using hφ
  have h := (ibp_interval_iff_EX04925 u g (hper.lift : AngCircle → ℝ)).1 (hw.ibp _ hs)
  simp only [e, intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2 * π),
    integral_Ioc_eq_integral_Ioo] at h
  exact h

/-- **Main statement.** Every real angular `H¹` function has a unique continuous representative,
absolutely continuous on `[0, 2π]`, whose endpoint values agree, whose almost-everywhere derivative
on `(0, 2π)` is every angular weak derivative `g`, and whose circle integrals of functions of
`(v, g)` equal `(2π)⁻¹` times the interval integrals. -/
theorem ex049_02_angular_h1_has_absolutely_continuous_representative (u : AngCircle → ℝ)
    (hu : AngularH1 u) :
    ∃ v : AngCircle → ℝ, Continuous v ∧ v =ᵐ[angHaar] u ∧
      (∀ w : AngCircle → ℝ, Continuous w → w =ᵐ[angHaar] u → w = v) ∧
      AbsolutelyContinuousOnInterval (fun s : ℝ => v (s : AngCircle)) 0 (2 * π) ∧
      v ((0 : ℝ) : AngCircle) = v ((2 * π : ℝ) : AngCircle) ∧
      ∀ g : AngCircle → ℝ, IsAngularWeakDeriv u g →
        (∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo 0 (2 * π) →
          deriv (fun x : ℝ => v (x : AngCircle)) s = g (s : AngCircle)) ∧
        ∀ H : ℝ → ℝ → ℝ, Integrable (fun θ => H (v θ) (g θ)) angHaar →
          ∫ θ, H (v θ) (g θ) ∂angHaar =
            (2 * π)⁻¹ * ∫ s in (0:ℝ)..2 * π, H (v (s : AngCircle)) (g (s : AngCircle)) := by
  obtain ⟨g0, hg0⟩ := hu
  have hf : MemLp (fun s : ℝ => u (s : AngCircle)) 2 (volume.restrict (Ioo 0 (2 * π))) :=
    memLp_interval_EX04902 hg0.memLp
  have hg : MemLp (fun s : ℝ => g0 (s : AngCircle)) 2 (volume.restrict (Ioo 0 (2 * π))) :=
    memLp_interval_EX04902 hg0.memLp_deriv
  obtain ⟨_c0, -, -, F0, ⟨hF0c, hF0p, hF0ac, -, hF0ae⟩, hF0u⟩ :=
    ex049_32_periodic_weak_pairs_have_periodic_ac (2 * π) (by positivity)
      (fun s : ℝ => u (s : AngCircle)) (fun s : ℝ => g0 (s : AngCircle)) hf hg
      (weak_interval_EX04902 hg0)
  have hcont : Continuous (hF0p.lift : AngCircle → ℝ) := cont_lift_EX04902 hF0c hF0p
  have hvm : Measurable (hF0p.lift : AngCircle → ℝ) :=
    QuotientAddGroup.measurable_from_quotient.2 hF0c.measurable
  obtain ⟨um, hum, hu_ae⟩ : ∃ um : AngCircle → ℝ, Measurable um ∧ u =ᵐ[angHaar] um :=
    ⟨_, hg0.memLp.aestronglyMeasurable.measurable_mk, hg0.memLp.aestronglyMeasurable.ae_eq_mk⟩
  have hv_um : (hF0p.lift : AngCircle → ℝ) =ᵐ[angHaar] um := by
    refine ae_circle_EX04902 hvm hum ?_
    have e : volume.restrict (Ioo 0 (2 * π)) = volume.restrict (Ioc 0 (2 * π)) :=
      Measure.restrict_congr_set Ioo_ae_eq_Ioc
    rw [e] at hF0ae
    exact hF0ae.trans (ae_Ioc_EX04902 hu_ae)
  have hv_u : (hF0p.lift : AngCircle → ℝ) =ᵐ[angHaar] u := hv_um.trans hu_ae.symm
  have huniq : ∀ w : AngCircle → ℝ, Continuous w → w =ᵐ[angHaar] u →
      w = (hF0p.lift : AngCircle → ℝ) := by
    intro w hw hwu
    have hFw : (fun s : ℝ => w (s : AngCircle)) = F0 :=
      hF0u (fun s : ℝ => w (s : AngCircle)) (hw.comp (AddCircle.continuous_mk' (2 * π)))
        (periodic_lift_EX04933 w) (ae_Ioo_EX04902 hwu)
    funext θ
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact congrFun hFw s
  have hend : (hF0p.lift : AngCircle → ℝ) ((0 : ℝ) : AngCircle) =
      (hF0p.lift : AngCircle → ℝ) ((2 * π : ℝ) : AngCircle) := by
    have h := hF0p 0
    rw [zero_add] at h
    exact h.symm
  refine ⟨(hF0p.lift : AngCircle → ℝ), hcont, hv_u, huniq, hF0ac 0 (2 * π), hend, ?_⟩
  intro g hg'
  have hgL : MemLp (fun s : ℝ => g (s : AngCircle)) 2 (volume.restrict (Ioo 0 (2 * π))) :=
    memLp_interval_EX04902 hg'.memLp_deriv
  obtain ⟨c, -, -, Fg, ⟨-, -, -, hFgint, -⟩, hFgu⟩ :=
    ex049_32_periodic_weak_pairs_have_periodic_ac (2 * π) (by positivity)
      (fun s : ℝ => u (s : AngCircle)) (fun s : ℝ => g (s : AngCircle)) hf hgL
      (weak_interval_EX04902 hg')
  have hFg : Fg = F0 := (hFgu F0 hF0c hF0p hF0ae).symm
  refine ⟨?_, ?_⟩
  · have hV := (ex049_31_primitive_l2_derivative (by positivity : (0:ℝ) < 2 * π) hgL).2.1
    filter_upwards [hV] with x hx
    intro hxI
    have hEv : F0 =ᶠ[𝓝 x] (fun y : ℝ => c + ∫ t in (0:ℝ)..y, g (t : AngCircle)) := by
      filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
      rw [← hFg]
      exact hFgint y ⟨hy.1.le, hy.2.le⟩
    have hd : deriv F0 x = deriv (fun y : ℝ => ∫ t in (0:ℝ)..y, g (t : AngCircle)) x := by
      rw [hEv.deriv_eq, deriv_const_add]
    show deriv F0 x = g (x : AngCircle)
    rw [hd]
    exact hx hxI
  · intro H _
    have key := integral_angHaar_interval_EX04925 0 (fun θ => H (hF0p.lift θ) (g θ))
    rw [zero_add] at key
    exact key

end DGPS.Frontier.EX049
