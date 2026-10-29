import DGPS.Frontier.FIN068.T04
import DGPS.Frontier.FIN068.T05
import DGPS.FiniteN.QuarticSaddle

/-!
Task id and title: FIN068.07, Critical curve in the variable `z` (module
`DGPS.Frontier.FIN068.T07`).

Provides:
* `DGPS.Frontier.FIN068.fin068_07_critical_curve_variable`: there are `δu, δz > 0` and a function
  `a : ℝ → ℝ`, `C^∞` on `Set.Ioo (-δz) δz`, with `a 0 = 0` and
  `deriv (fun s => liftPotential_FIN06804 s z) (a z) = 0` (that is, `J_u(a z, z) = 0`) for
  `|z| < δz`, such that every `u` with `|u| < δu`, `|z| < δz` and `J_u(u, z) = 0` satisfies
  `u = a z`.
* `DGPS.Frontier.FIN068.fin068_07_critical_curve_variable_bound`: the same statement with the
  additional conclusion `|a z| < δu` for `|z| < δz` (the curve lies in the uniqueness window).
* Helper declarations, all with suffix `_FIN06807` and not part of the interface:
  `rect_FIN06807`, `liftSwap_FIN06807`, `critU_FIN06807` (definitions), `isOpen_rect_FIN06807`,
  `hasDerivAt_snd_FIN06807`, `liftSwap_contDiffOn_FIN06807`, `critU_eq_fderiv_FIN06807`,
  `critU_contDiffOn_FIN06807`, `critU_differentiableAt_FIN06807`, `ift_point_FIN06807`,
  `square_FIN06807`, `root_unique_FIN06807`, `core_FIN06807`.

Proof: `J = liftPotential_FIN06804` is `C^∞` on the open square `(-1, 1)^2` (FIN068.04). Read on
pairs `(z, u)`, so that the parameter `z` comes first, the function `critU (z, u) = J_u(u, z)` is
`C^∞` there (the Fréchet derivative of a `C^∞` function on an open set is `C^∞`). Its `u`-derivative
at the origin is `J_uu(0, 0) = A = b/5 - g'(4) > 0` (FIN068.05 for the value, the FIN065
certificate for the sign), and `critU (0, 0) = J_u(0, 0) = 0` (FIN068.05). By continuity, `J_uu > 0`
on a square `|z|, |u| < ε`. For fixed `z` this makes `u ↦ J_u(u, z)` strictly increasing on
`(-ε, ε)`, so it has at most one zero there. Mathlib's `ContDiffAt.implicitFunction` at the origin
gives `ψ` with `ψ 0 = 0`, `C^∞` at `0`, and `J_u(ψ z, z) = 0` for `z` near `0` (via
`ContDiffAt.eventually_apply_implicitFunction`). Shrinking to `|z| < δz` gives `|ψ z| < ε`. The
curve is `a = ψ`. Uniqueness is the monotonicity statement. Smoothness on the whole interval: at
each `z₁` with `|z₁| < δz`, the same implicit function theorem at `(z₁, ψ z₁)`, where the
`u`-derivative is positive, gives `ψ₁`, which is `C^∞` at `z₁`; by continuity of `ψ₁` and the
uniqueness above, `ψ₁ = ψ` on a neighbourhood of `z₁`, so `ψ` is `C^∞` at `z₁`.

R5 notes:
* No hypothesis is added. The statement is closed (existential in `δu, δz, a`).
* `J_u(u, z)` is read as `deriv (fun s => liftPotential_FIN06804 s z) u`, the derivative of the
  slice in the first variable, as in FIN068.05. The Fréchet reading differs only by the identity
  `critU_eq_fderiv_FIN06807` on the open square.
* "Smooth real function `a(z)` for `|z| < δz`" is read as `ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)`
  (real `C^∞` on the open interval). `a` is a total function `ℝ → ℝ`; only its values on the
  interval matter.
* The main statement is literal, so it does not say `|a z| < δu`. The second declaration
  `fin068_07_critical_curve_variable_bound` adds this (a strengthening, from the same proof), so
  that the uniqueness clause is not vacuous for the curve itself.
* The specification's "choose the neighbourhoods so that `J_uu > A/2`" is read as "so that `J_uu > 0`".
  Only positivity is needed for invertibility and for monotonicity, and the smaller bound is not
  used. Positivity comes from the continuity of `J_uu` at the origin, where it equals `A > 0`.
* `A > 0` is not a hypothesis. It is taken from the FIN065 certificate
  `DGPS.FiniteN.quartic_explicit_model_rational_certificate` (component `0 < b/5 - g'(4)`), the same
  source as FIN068.03. FIN068.03 itself is not imported, since it is not a listed prerequisite.
* Proof route, a non-literal reading of the specification: the Proof paragraph obtains the local
  uniqueness at graph points from the IFT's `eventually_apply_eq_iff_implicitFunction`. Here
  uniqueness in the whole square comes from strict monotonicity of `u ↦ J_u(u, z)` on
  `(-ε, ε)`, and the IFT (`ContDiffAt.implicitFunction`, `contDiffAt_implicitFunction`,
  `implicitFunction_apply_self`, `eventually_apply_implicitFunction`) is used only for existence
  and smoothness of a branch at a point. The result is the same statement.
* Variable order: the IFT of Mathlib takes `f : E₁ × E₂ → F` with the parameter in `E₁` and the
  unknown in `E₂`; so the equation is posed on pairs `(z, u)` (`critU_FIN06807`), with `ℝ`, `ℝ`
  and `ℝ` as the three spaces. `critU (z, u)` is `J_u(u, z)`.
* The rectangle used is the one of FIN068.04, `(-1, 1) × (-1, 1)` (`rect_FIN06807`). The numbers
  `δu` and `δz` are produced by the proof and are not specified further.
* The Morse coordinate and the weighted remainder parts of the node are not in this packet.
-/

open DGPS.Models DGPS.Circle.BesselMoments
open scoped ContDiff Topology

namespace DGPS.Frontier.FIN068

/-- The open rectangle `(-1, 1) × (-1, 1)` on which `J` is smooth (FIN068.04). -/
def rect_FIN06807 : Set (ℝ × ℝ) := Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1

/-- `J` read on pairs `(z, u)`, the parameter first: `liftSwap (z, u) = J(u, z)`. -/
noncomputable def liftSwap_FIN06807 (q : ℝ × ℝ) : ℝ := liftPotential_FIN06804 q.2 q.1

/-- `J_u` read on pairs `(z, u)`: `critU (z, u) = ∂J/∂u (u, z)`, as the one-variable derivative of
the slice `s ↦ J(s, z)` at `u`. -/
noncomputable def critU_FIN06807 (q : ℝ × ℝ) : ℝ :=
  deriv (fun s : ℝ => liftPotential_FIN06804 s q.1) q.2

lemma isOpen_rect_FIN06807 : IsOpen rect_FIN06807 := isOpen_Ioo.prod isOpen_Ioo

lemma hasDerivAt_snd_FIN06807 {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hg : DifferentiableAt ℝ g p) :
    HasDerivAt (fun s : ℝ => g (p.1, s)) (fderiv ℝ g p (0, 1)) p.2 := by
  have h1 : HasDerivAt (fun s : ℝ => ((p.1, s) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h2 : HasFDerivAt g (fderiv ℝ g p) (p.1, p.2) := hg.hasFDerivAt
  exact h2.comp_hasDerivAt p.2 h1

lemma liftSwap_contDiffOn_FIN06807 : ContDiffOn ℝ ∞ liftSwap_FIN06807 rect_FIN06807 := by
  have h := fin068_04_lift_two_ordinary_variables.1
  have hs : ContDiff ℝ ∞ (Prod.swap : ℝ × ℝ → ℝ × ℝ) := contDiff_snd.prodMk contDiff_fst
  refine h.comp hs.contDiffOn ?_
  intro q hq
  exact ⟨hq.2, hq.1⟩

lemma critU_eq_fderiv_FIN06807 :
    Set.EqOn critU_FIN06807 (fun q => fderiv ℝ liftSwap_FIN06807 q (0, 1)) rect_FIN06807 := by
  intro q hq
  have hd : DifferentiableAt ℝ liftSwap_FIN06807 q :=
    (liftSwap_contDiffOn_FIN06807.differentiableOn (by simp)).differentiableAt
      (isOpen_rect_FIN06807.mem_nhds hq)
  exact (hasDerivAt_snd_FIN06807 hd).deriv

lemma critU_contDiffOn_FIN06807 : ContDiffOn ℝ ∞ critU_FIN06807 rect_FIN06807 := by
  have h1 : ContDiffOn ℝ ∞ (fun q => fderiv ℝ liftSwap_FIN06807 q) rect_FIN06807 :=
    liftSwap_contDiffOn_FIN06807.fderiv_of_isOpen isOpen_rect_FIN06807 (by simp)
  exact (h1.clm_apply contDiffOn_const).congr critU_eq_fderiv_FIN06807

lemma critU_differentiableAt_FIN06807 {q : ℝ × ℝ} (hq : q ∈ rect_FIN06807) :
    DifferentiableAt ℝ critU_FIN06807 q :=
  (critU_contDiffOn_FIN06807.differentiableOn (by simp)).differentiableAt
    (isOpen_rect_FIN06807.mem_nhds hq)

/-- The smooth implicit function theorem at one point `(z₁, u₁)` of the rectangle at which the
`u`-derivative of `critU` is nonzero. -/
lemma ift_point_FIN06807 {q : ℝ × ℝ} (hq : q ∈ rect_FIN06807)
    (hne : fderiv ℝ critU_FIN06807 q (0, 1) ≠ 0) :
    ∃ ψ : ℝ → ℝ, ContDiffAt ℝ ∞ ψ q.1 ∧ ψ q.1 = q.2 ∧
      ∀ᶠ z in 𝓝 q.1, critU_FIN06807 (z, ψ z) = critU_FIN06807 q := by
  have hcd : ContDiffAt ℝ ∞ critU_FIN06807 q :=
    critU_contDiffOn_FIN06807.contDiffAt (isOpen_rect_FIN06807.mem_nhds hq)
  have hinv : (fderiv ℝ critU_FIN06807 q ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    set c := fderiv ℝ critU_FIN06807 q (0, 1) with hc
    have key : ∀ t : ℝ, fderiv ℝ critU_FIN06807 q (0, t) = t * c := fun t => by
      have : ((0, t) : ℝ × ℝ) = t • ((0, 1) : ℝ × ℝ) := by simp
      rw [this, map_smul, smul_eq_mul]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := c⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · refine ContinuousLinearMap.ext fun t => ?_
      simp [key]
      field_simp
    · refine ContinuousLinearMap.ext fun t => ?_
      simp [key]
      field_simp
  exact ⟨hcd.implicitFunction (by simp) hinv, hcd.contDiffAt_implicitFunction _ _,
    hcd.implicitFunction_apply_self _ _, hcd.eventually_apply_implicitFunction _ _⟩

/-- Positivity of `J_uu` on a square around the origin, and the strict monotonicity of `u ↦ J_u`
on it. -/
lemma square_FIN06807 :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z u : ℝ, |z| < ε → |u| < ε →
      (z, u) ∈ rect_FIN06807 ∧ 0 < fderiv ℝ critU_FIN06807 (z, u) (0, 1) := by
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, hA⟩, -, -⟩ :=
    DGPS.FiniteN.quartic_explicit_model_rational_certificate
  obtain ⟨-, -, h3, -⟩ := fin068_05_exact_jet
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ rect_FIN06807 := by simp [rect_FIN06807]
  have hpos0 : 0 < fderiv ℝ critU_FIN06807 (0, 0) (0, 1) := by
    have := (hasDerivAt_snd_FIN06807 (critU_differentiableAt_FIN06807 h0)).deriv
    have h3' : deriv (fun s : ℝ => critU_FIN06807 ((0 : ℝ), s)) 0 =
        quarticB / 5 - deriv besselRatio 4 := h3
    rw [← this]
    simpa [h3'] using hA
  have hcont : ContinuousAt (fun q => fderiv ℝ critU_FIN06807 q (0, 1)) (0, 0) := by
    have hc1 : ContinuousOn (fun q => fderiv ℝ critU_FIN06807 q) rect_FIN06807 :=
      critU_contDiffOn_FIN06807.continuousOn_fderiv_of_isOpen isOpen_rect_FIN06807 (by simp)
    exact (hc1.clm_apply continuousOn_const).continuousAt (isOpen_rect_FIN06807.mem_nhds h0)
  have hev : ∀ᶠ q in 𝓝 ((0 : ℝ), (0 : ℝ)),
      0 < fderiv ℝ critU_FIN06807 q (0, 1) ∧ q ∈ rect_FIN06807 :=
    (hcont.eventually (Ioi_mem_nhds hpos0)).and (isOpen_rect_FIN06807.mem_nhds h0)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun z u hz hu => ?_⟩
  have hd : dist ((z, u) : ℝ × ℝ) (0, 0) < ε := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    simpa using And.intro hz hu
  exact ⟨(hball hd).2, (hball hd).1⟩

/-- Uniqueness of the root of `u ↦ J_u(u, z)` in the square, by strict monotonicity. -/
lemma root_unique_FIN06807 {ε : ℝ}
    (hsq : ∀ z u : ℝ, |z| < ε → |u| < ε →
      (z, u) ∈ rect_FIN06807 ∧ 0 < fderiv ℝ critU_FIN06807 (z, u) (0, 1))
    {z u v : ℝ} (hz : |z| < ε) (hu : |u| < ε) (hv : |v| < ε)
    (hu0 : critU_FIN06807 (z, u) = 0) (hv0 : critU_FIN06807 (z, v) = 0) : u = v := by
  have hder : ∀ s : ℝ, |s| < ε →
      HasDerivAt (fun t : ℝ => critU_FIN06807 (z, t)) (fderiv ℝ critU_FIN06807 (z, s) (0, 1)) s :=
    fun s hs => hasDerivAt_snd_FIN06807 (critU_differentiableAt_FIN06807 (hsq z s hz hs).1)
  have hmono : StrictMonoOn (fun t : ℝ => critU_FIN06807 (z, t)) (Set.Ioo (-ε) ε) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) ?_ ?_
    · intro s hs
      exact (hder s (abs_lt.2 hs)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ioo] at hs
      rw [(hder s (abs_lt.2 hs)).deriv]
      exact (hsq z s hz (abs_lt.2 hs)).2
  exact hmono.injOn (abs_lt.1 hu) (abs_lt.1 hv) (hu0.trans hv0.symm)

/-- Core statement, in the variables `(z, u)`. -/
lemma core_FIN06807 :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz → |a z| < δu ∧ critU_FIN06807 (z, a z) = 0) ∧
      ∀ u z : ℝ, |u| < δu → |z| < δz → critU_FIN06807 (z, u) = 0 → u = a z := by
  obtain ⟨ε, hε, hsq⟩ := square_FIN06807
  obtain ⟨h1, -⟩ := fin068_05_exact_jet
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ rect_FIN06807 := by simp [rect_FIN06807]
  have hne0 : fderiv ℝ critU_FIN06807 ((0 : ℝ), (0 : ℝ)) (0, 1) ≠ 0 :=
    (hsq 0 0 (by simpa using hε) (by simpa using hε)).2.ne'
  obtain ⟨ψ, hψcd, hψ0, hψroot⟩ := ift_point_FIN06807 h0 hne0
  have hc00 : critU_FIN06807 ((0 : ℝ), (0 : ℝ)) = 0 := h1
  have hev : ∀ᶠ z in 𝓝 (0 : ℝ), |z| < ε ∧ |ψ z| < ε ∧ critU_FIN06807 (z, ψ z) = 0 := by
    have e1 : ∀ᶠ z in 𝓝 (0 : ℝ), |z| < ε :=
      (continuous_abs.continuousAt.eventually_lt continuousAt_const (by simpa using hε))
    have e2 : ∀ᶠ z in 𝓝 (0 : ℝ), |ψ z| < ε := by
      refine (continuous_abs.continuousAt.comp hψcd.continuousAt).eventually_lt
        continuousAt_const ?_
      simpa [hψ0] using hε
    have e3 : ∀ᶠ z in 𝓝 (0 : ℝ), critU_FIN06807 (z, ψ z) = 0 := by
      filter_upwards [hψroot] with z hz
      rw [hz, hc00]
    exact e1.and (e2.and e3)
  obtain ⟨δ, hδ, hδall⟩ := Metric.eventually_nhds_iff.1 hev
  have hδ' : ∀ z : ℝ, |z| < δ → |z| < ε ∧ |ψ z| < ε ∧ critU_FIN06807 (z, ψ z) = 0 := fun z hz =>
    hδall (by simpa [Real.dist_eq] using hz)
  -- smoothness at every point of the interval
  have hsm : ∀ z1 : ℝ, |z1| < δ → ContDiffAt ℝ ∞ ψ z1 := by
    intro z1 hz1
    obtain ⟨hz1ε, hψ1ε, hroot⟩ := hδ' z1 hz1
    have hq := hsq z1 (ψ z1) hz1ε hψ1ε
    obtain ⟨ψ₁, hcd₁, h₁eq, h₁root⟩ := ift_point_FIN06807 hq.1 hq.2.ne'
    have h₁eq' : ψ₁ z1 = ψ z1 := h₁eq
    have e1 : ∀ᶠ z in 𝓝 z1, |z| < δ :=
      continuous_abs.continuousAt.eventually_lt continuousAt_const hz1
    have e2 : ∀ᶠ z in 𝓝 z1, |z| < ε :=
      continuous_abs.continuousAt.eventually_lt continuousAt_const hz1ε
    have e3 : ∀ᶠ z in 𝓝 z1, |ψ₁ z| < ε := by
      refine (continuous_abs.continuousAt.comp hcd₁.continuousAt).eventually_lt
        continuousAt_const ?_
      simpa [h₁eq'] using hψ1ε
    have hqq : critU_FIN06807 ((z1, ψ z1) : ℝ × ℝ) = 0 := hroot
    have hev₁ : ψ =ᶠ[𝓝 z1] ψ₁ := by
      filter_upwards [e1, e2, e3, h₁root] with z hz1' hz2 hz3 hz4
      exact root_unique_FIN06807 hsq hz2 (hδ' z hz1').2.1 hz3 (hδ' z hz1').2.2
        (hz4.trans hqq)
    exact hcd₁.congr_of_eventuallyEq hev₁
  refine ⟨ε, δ, hε, hδ, ψ, fun z hz => ?_, hψ0, fun z hz => ?_, ?_⟩
  · exact (hsm z (abs_lt.2 hz)).contDiffWithinAt
  · exact ⟨(hδ' z hz).2.1, (hδ' z hz).2.2⟩
  · intro u z hu hz hu0
    exact root_unique_FIN06807 hsq (hδ' z hz).1 hu (hδ' z hz).2.1 hu0 (hδ' z hz).2.2

/-- Critical curve, with the graph kept inside the uniqueness window: there are `δu, δz > 0` and a
smooth `a` on `|z| < δz` with `a 0 = 0`, `|a z| < δu` and `J_u(a z, z) = 0`, and every zero of
`J_u(·, z)` in `|u| < δu` equals `a z`. -/
theorem fin068_07_critical_curve_variable_bound :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz → |a z| < δu ∧
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      ∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z :=
  core_FIN06807

/-- Main declaration. Critical curve in the variable `z`: there are `δu, δz > 0` and a smooth real
function `a` on `|z| < δz` with `a 0 = 0` and `J_u(a z, z) = 0`, and every solution of
`J_u(u, z) = 0` with `|u| < δu`, `|z| < δz` has `u = a z`. Here `J_u(u, z)` is
`deriv (fun s => liftPotential_FIN06804 s z) u`. -/
theorem fin068_07_critical_curve_variable :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      ∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4⟩ := fin068_07_critical_curve_variable_bound
  exact ⟨δu, δz, hu, hz, a, h1, h2, fun z hz' => (h3 z hz').2, h4⟩

end DGPS.Frontier.FIN068
