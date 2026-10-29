import DGPS.Frontier.FIN068.T05
import DGPS.Frontier.FIN068.T07
import DGPS.FiniteN.QuarticSaddle

/-!
Task id and title: FIN068.23, First derivative of the critical curve (module
`DGPS.Frontier.FIN068.T23`).

Provides:
* `DGPS.Frontier.FIN068.fin068_23_first_derivative_critical_curve`: there are `δu, δz > 0` and a
  function `a : ℝ → ℝ`, `C^∞` on `Set.Ioo (-δz) δz`, with `a 0 = 0`, `J_u(a z, z) = 0` for
  `|z| < δz`, every `u` with `|u| < δu`, `|z| < δz` and `J_u(u, z) = 0` satisfying `u = a z`
  (the curve of FIN068.07), and `a'(0) = d / (32 A)`, with `A = b/5 - g'(4)` and
  `d = b - 4 g'(4)` written out.
* `DGPS.Frontier.FIN068.fin068_23_first_derivative_critical_curve_any`: the derivative identity
  for every `a : ℝ → ℝ` that is `C^∞` on `Set.Ioo (-δz) δz` (for some `δz > 0`), satisfies
  `a 0 = 0`, and solves `J_u(a z, z) = 0` for `|z| < δz`. Its conclusion is `a'(0) = d / (32 A)`.
* Helper declarations, all with suffix `_FIN06823` and not part of the interface:
  `hasDerivAt_fst_FIN06823` (derivative along the first coordinate),
  `critU_chain_FIN06823` (chain rule for `z ↦ critU (z, a z)` at `0`),
  `deriv_curve_core_FIN06823` (the identity `0 = -d/32 + a'(0) A`, then division by `A`).

Proof: differentiate `z ↦ J_u(a z, z) = critU (z, a z)` at `0` by the chain rule. Its
derivative is `fderiv critU (0,0) (1, a'(0)) = J_uz(0,0) + a'(0) J_uu(0,0) = -d/32 + a'(0) A`
(FIN068.05 gives both partials). The function vanishes on a neighbourhood of `0`, so its
derivative there is `0`. Hence `a'(0) A = d/32`, and `A > 0` (FIN065 certificate) gives the value.

R5 notes:
* No hypothesis is added beyond the curve data of FIN068.07. The `_any` declaration has the
  hypotheses `0 < δz`, `ContDiffOn` on `Set.Ioo (-δz) δz`, `a 0 = 0` and the root equation on
  `|z| < δz`. These are the properties the curve has by FIN068.07, and the derivative at `0` is
  defined only through the smoothness on a neighbourhood of `0`.
* The main declaration is the FIN068.07 curve packaged with the derivative conclusion. It is
  obtained from `fin068_07_critical_curve_variable` (the uniqueness clause is carried through
  unchanged) and the `_any` declaration. Uniqueness is not used in the derivative proof.
* `A` and `d` are written out as `quarticB / 5 - deriv besselRatio 4` and
  `quarticB - 4 * deriv besselRatio 4`, as in FIN068.05. The conclusion is therefore
  `deriv a 0 = (quarticB - 4 * deriv besselRatio 4) / (32 * (quarticB / 5 - deriv besselRatio 4))`.
* `A > 0` is not a hypothesis. It comes from the FIN065 certificate
  `DGPS.FiniteN.quartic_explicit_model_rational_certificate` (component `0 < b/5 - g'(4)`),
  the same source as FIN068.07. This is the "divide by `A > 0`" step of the specification.
* `J_u(u, z)` is read as `deriv (fun s => liftPotential_FIN06804 s z) u`, as in FIN068.07. The
  partial `J_uz` of FIN068.05 (inner derivative in `u`, outer in `z`) is the one that enters the
  chain rule, since the chain-rule derivative is taken along `z` for `critU (z, a z)`.
* `a'(0)` is `deriv a 0`. Differentiability at `0` is obtained from `ContDiffOn` on the open
  interval `Set.Ioo (-δz) δz`, which contains `0`; no separate hypothesis is used.
* The specification's "chain rule applies on a neighbourhood" is used via the equation holding
  on `Set.Ioo (-δz) δz`, which is a neighbourhood of `0`. No identification with the `Morse`
  coordinate or the weighted remainder is part of this packet.
-/

open DGPS.Models DGPS.Circle.BesselMoments
open scoped ContDiff Topology

namespace DGPS.Frontier.FIN068

lemma hasDerivAt_fst_FIN06823 {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ} (hg : DifferentiableAt ℝ g p) :
    HasDerivAt (fun s : ℝ => g (s, p.2)) (fderiv ℝ g p (1, 0)) p.1 := by
  have h1 : HasDerivAt (fun s : ℝ => ((s, p.2) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) p.1 :=
    (hasDerivAt_id' p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h2 : HasFDerivAt g (fderiv ℝ g p) (p.1, p.2) := hg.hasFDerivAt
  exact h2.comp_hasDerivAt p.1 h1

/-- Chain rule for `z ↦ J_u(a z, z) = critU (z, a z)` at `0`, when `a 0 = 0`. -/
lemma critU_chain_FIN06823 {a : ℝ → ℝ} {c : ℝ} (ha : HasDerivAt a c 0) (ha0 : a 0 = 0) :
    HasDerivAt (fun z : ℝ => critU_FIN06807 (z, a z))
      (fderiv ℝ critU_FIN06807 (0, 0) (1, 0) + c * fderiv ℝ critU_FIN06807 (0, 0) (0, 1)) 0 := by
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ rect_FIN06807 := by simp [rect_FIN06807]
  have hd := critU_differentiableAt_FIN06807 h0
  have hF : HasFDerivAt critU_FIN06807 (fderiv ℝ critU_FIN06807 (0, a 0)) (0, a 0) := by
    rw [ha0]
    exact hd.hasFDerivAt
  have hpair : HasDerivAt (fun z : ℝ => ((z, a z) : ℝ × ℝ)) ((1, c) : ℝ × ℝ) 0 :=
    (hasDerivAt_id' 0).prodMk ha
  have hcomp := hF.comp_hasDerivAt (0 : ℝ) hpair
  rw [ha0] at hcomp
  have hsplit : ((1, c) : ℝ × ℝ) = (1, 0) + c • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, smul_eq_mul] at hcomp
  exact hcomp

/-- The identity `0 = -d/32 + a'(0) A` at `0`, from the chain rule and FIN068.05, and then the
division by `A`. -/
lemma deriv_curve_core_FIN06823 {δz : ℝ} (hδ : 0 < δz) {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)) (ha0 : a 0 = 0)
    (hroot : ∀ z : ℝ, |z| < δz → critU_FIN06807 (z, a z) = 0) :
    deriv a 0 = (quarticB - 4 * deriv besselRatio 4) / (32 * (quarticB / 5 - deriv besselRatio 4)) := by
  obtain ⟨-, -, h3, h4, -, -⟩ := fin068_05_exact_jet
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, hA⟩, -, -⟩ :=
    DGPS.FiniteN.quartic_explicit_model_rational_certificate
  have hmem : Set.Ioo (-δz) δz ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ
  have hda : DifferentiableAt ℝ a 0 :=
    (ha.differentiableOn (by simp)).differentiableAt hmem
  have hac : HasDerivAt a (deriv a 0) 0 := hda.hasDerivAt
  have hchain := critU_chain_FIN06823 hac ha0
  -- the composed function vanishes on a neighbourhood of `0`, so its derivative there is `0`
  have hev : (fun z : ℝ => critU_FIN06807 (z, a z)) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [hmem] with z hz
    exact hroot z (abs_lt.2 hz)
  have hzero : HasDerivAt (fun z : ℝ => critU_FIN06807 (z, a z)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev
  have huniq := hzero.unique hchain
  -- the two partials at the origin
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ rect_FIN06807 := by simp [rect_FIN06807]
  have hd := critU_differentiableAt_FIN06807 h0
  have hJuz : fderiv ℝ critU_FIN06807 (0, 0) (1, 0) = -(quarticB - 4 * deriv besselRatio 4) / 32 := by
    rw [← h4]
    exact (hasDerivAt_fst_FIN06823 hd).deriv.symm
  have hJuu : fderiv ℝ critU_FIN06807 (0, 0) (0, 1) = quarticB / 5 - deriv besselRatio 4 := by
    rw [← h3]
    exact (hasDerivAt_snd_FIN06807 hd).deriv.symm
  rw [hJuz, hJuu] at huniq
  have hne : 32 * (quarticB / 5 - deriv besselRatio 4) ≠ 0 := mul_ne_zero (by norm_num) hA.ne'
  rw [eq_div_iff hne]
  linear_combination (-32 : ℝ) * huniq

/-- Derivative of the critical curve at `0`, for every curve of the FIN068.07 type: a function
`a` that is `C^∞` on `(-δz, δz)`, with `a 0 = 0` and `J_u(a z, z) = 0` there, satisfies
`a'(0) = d / (32 A)`. -/
lemma fin068_23_first_derivative_critical_curve_any {δz : ℝ} (hδ : 0 < δz) {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)) (ha0 : a 0 = 0)
    (hroot : ∀ z : ℝ, |z| < δz → deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) :
    deriv a 0 = (quarticB - 4 * deriv besselRatio 4) / (32 * (quarticB / 5 - deriv besselRatio 4)) :=
  deriv_curve_core_FIN06823 hδ ha ha0 (fun z hz => hroot z hz)

/-- Main declaration. First derivative of the critical curve: there are `δu, δz > 0` and a
function `a`, `C^∞` on `(-δz, δz)`, with `a 0 = 0`, `J_u(a z, z) = 0` for `|z| < δz`, every zero
`u` of `J_u(·, z)` with `|u| < δu`, `|z| < δz` equal to `a z`, and
`a'(0) = d / (32 A)`, where `A = b/5 - g'(4)` and `d = b - 4 g'(4)`. Here `J_u(u, z)` is
`deriv (fun s => liftPotential_FIN06804 s z) u`. -/
theorem fin068_23_first_derivative_critical_curve :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      (∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z) ∧
      deriv a 0 = (quarticB - 4 * deriv besselRatio 4) / (32 * (quarticB / 5 - deriv besselRatio 4)) := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4⟩ := fin068_07_critical_curve_variable
  exact ⟨δu, δz, hu, hz, a, h1, h2, h3, h4,
    fin068_23_first_derivative_critical_curve_any hz h1 h2 h3⟩

end DGPS.Frontier.FIN068
