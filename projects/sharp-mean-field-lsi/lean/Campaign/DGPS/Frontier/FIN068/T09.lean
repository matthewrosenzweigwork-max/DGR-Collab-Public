import DGPS.Frontier.FIN068.T23
import DGPS.Frontier.FIN068.T04
import DGPS.FiniteN.QuarticSaddle

/-!
Task id and title: FIN068.09, Reduced quartic coefficient (module
`DGPS.Frontier.FIN068.T09`).

Provides:
* `DGPS.Frontier.FIN068.fin068_09_reduced_quartic_coefficient`: there are `δu, δz > 0` and a
  function `a : ℝ → ℝ`, `C^∞` on `Set.Ioo (-δz) δz`, with `a 0 = 0`, `J_u(a z, z) = 0` for
  `|z| < δz`, every `u` with `|u| < δu`, `|z| < δz` and `J_u(u, z) = 0` satisfying `u = a z`
  (the FIN068.07 curve, packaged as in FIN068.23), and, for `q z = J(a z, z)` with `J` the lifted
  potential of FIN068.04: `q 0 = ψ(w₋)`, `q'(0) = 0` and `q''(0) = -2 c₄`, where
  `c₄ = b d / (10240 A)`, `A = b/5 - g'(4)` and `d = b - 4 g'(4)` are written out.
* `DGPS.Frontier.FIN068.fin068_09_reduced_quartic_coefficient_any`: the same three conclusions for
  any `a` that is `C^∞` on `Set.Ioo (-δz) δz` (for some `δz > 0`), satisfies `a 0 = 0`, and solves
  `J_u(a z, z) = 0` for `|z| < δz`.
* Helper declarations, all with suffix `_FIN06809` and not part of the interface:
  `potF_FIN06809` (`J` read on pairs `(u, z)`), `rect_FIN06809` (the open rectangle
  `(-1, 1) × (-1, 1)`), `dzPot_FIN06809` (the Fréchet partial of `potF_FIN06809` in the second
  coordinate), `isOpen_rect_FIN06809`, `mem_rect_FIN06809`, `potF_contDiffOn_FIN06809`,
  `potF_differentiableAt_FIN06809`, `dzPot_contDiffOn_FIN06809`, `dzPot_differentiableAt_FIN06809`,
  `dzPot_eq_slice_FIN06809`, `hasDerivAt_q_FIN06809`, `eventually_curve_FIN06809`,
  `q_zero_FIN06809`, `dzPot_zero_FIN06809`.

Proof: `q'(z) = J_u(a z, z) a'(z) + J_z(a z, z)` by the chain rule. The first term vanishes on the
curve, so `q'(z) = ∂_z J(a z, z)` on a neighbourhood of `0`. Differentiating this at `0` by the
chain rule gives `q''(0) = ∂_z∂_u J(0,0) a'(0) + ∂_z∂_z J(0,0)`. FIN068.05 gives both partials
(`-d/32` and `d/256`), FIN068.23 gives `a'(0) = d/(32 A)`, and the identity `4A - d = -b/5` (a ring
identity in `b`, `g'(4)`) closes the computation.

R5 notes:
* No hypothesis is added beyond the curve data of FIN068.07/.23 (in the `_any` declaration, the
  hypotheses `0 < δz`, `ContDiffOn` on `Set.Ioo (-δz) δz`, `a 0 = 0` and the root equation on
  `|z| < δz`). The main declaration is the existential packaging of the FIN068.23 curve together
  with the three conclusions; the uniqueness clause is carried through unchanged and not used.
* `ψ(w₋)` is read as `quarticPsi_FIN066 !₂[-4, 0]` (the point `w₋ = (-4, 0)` of
  `EuclideanSpace ℝ (Fin 2)`). The value `q 0 = ψ(w₋)` is obtained from the FIN068.04 identity
  `quarticPsi_FIN066 !₂[-4 + u, y] = J(u, y²)` at `u = 0`, `y = 0`.
* `J(u, z)` is `liftPotential_FIN06804 u z`, so the signed variable `z` is used throughout; the
  conclusions about `q` concern a neighbourhood of `0` and do not use `z ≥ 0`.
* `q'(0)` and `q''(0)` are read as `deriv q 0` and `deriv (deriv q) 0` for the total function
  `q z = liftPotential_FIN06804 (a z) z`. Its derivative at `0` is determined by its values on the
  neighbourhood `{|z| < δ}` where `a` is smooth, so no value of `a` outside that set is used.
  The formula `q'(z) = ∂_z J(a z, z)` is established on a whole neighbourhood of `0`, not only at
  `0`, because the second derivative requires it.
* The Taylor coefficient is not used: the statement concerns `q''(0)` itself, which equals
  `-2 c₄`, as in the specification. The coefficient of `z²` is `-c₄`.
* `c₄` is not a separate definition. It appears as the explicit quotient
  `quarticB * (quarticB - 4 * deriv besselRatio 4) / (10240 * (quarticB / 5 - deriv besselRatio 4))`,
  multiplied by `-2`, with `g'(4) = deriv besselRatio 4` (the derivative value).
* `A > 0` is not a hypothesis. It is taken from the FIN065 certificate
  `DGPS.FiniteN.quartic_explicit_model_rational_certificate` (component `0 < b/5 - g'(4)`), as in
  FIN068.03 and FIN068.23. It is used only to clear the denominator `A`.
* Partial-derivative conventions: `∂_z J(u, z)` is the Fréchet partial `fderiv ℝ potF (u, z) (0, 1)`,
  identified with the slice derivative `deriv (fun t => J u t) z` on the rectangle. The mixed partial
  `∂_u ∂_z J(0,0)` enters through FIN068.05 item `deriv (fun t => deriv (fun s => J t s) 0) 0`, and
  no Schwarz symmetry is used.
* The rectangle `(-1, 1) × (-1, 1)` of FIN068.04 is the domain of smoothness of `J`; membership of
  `(a z, z)` in it is obtained from continuity of `a` at `0` on a neighbourhood of `0`. No bound
  `δu ≤ 1` is assumed.
* The Morse coordinate, the weighted remainder and the FIN068.37/.38 Bessel identifications are not
  used. Everything here rests on the FIN068.03, .04, .05, .07 and .23 declarations as proved.
-/

open DGPS.Models DGPS.Circle.BesselMoments DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff Topology

namespace DGPS.Frontier.FIN068

/-- `J` read on pairs `(u, z)`: `potF_FIN06809 (u, z) = liftPotential_FIN06804 u z`. -/
noncomputable def potF_FIN06809 (p : ℝ × ℝ) : ℝ := liftPotential_FIN06804 p.1 p.2

/-- The open rectangle `(-1, 1) × (-1, 1)` on which `J` is smooth (FIN068.04). -/
def rect_FIN06809 : Set (ℝ × ℝ) := Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1

/-- The Fréchet partial of `potF_FIN06809` in its second coordinate. -/
noncomputable def dzPot_FIN06809 (p : ℝ × ℝ) : ℝ := fderiv ℝ potF_FIN06809 p (0, 1)

lemma isOpen_rect_FIN06809 : IsOpen rect_FIN06809 := isOpen_Ioo.prod isOpen_Ioo

lemma mem_rect_FIN06809 {p : ℝ × ℝ} (h1 : -1 < p.1) (h2 : p.1 < 1) (h3 : -1 < p.2)
    (h4 : p.2 < 1) : p ∈ rect_FIN06809 :=
  ⟨⟨h1, h2⟩, h3, h4⟩

lemma potF_contDiffOn_FIN06809 : ContDiffOn ℝ ∞ potF_FIN06809 rect_FIN06809 :=
  fin068_04_lift_two_ordinary_variables.1

lemma potF_differentiableAt_FIN06809 {p : ℝ × ℝ} (hp : p ∈ rect_FIN06809) :
    DifferentiableAt ℝ potF_FIN06809 p :=
  (potF_contDiffOn_FIN06809.differentiableOn (by simp)).differentiableAt
    (isOpen_rect_FIN06809.mem_nhds hp)

lemma dzPot_contDiffOn_FIN06809 : ContDiffOn ℝ ∞ dzPot_FIN06809 rect_FIN06809 := by
  have h1 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ potF_FIN06809 p) rect_FIN06809 :=
    potF_contDiffOn_FIN06809.fderiv_of_isOpen isOpen_rect_FIN06809 (by simp)
  have h2 : ContDiffOn ℝ ∞ (fun p => fderiv ℝ potF_FIN06809 p ((0 : ℝ), (1 : ℝ))) rect_FIN06809 :=
    h1.clm_apply contDiffOn_const
  exact h2

lemma dzPot_differentiableAt_FIN06809 {p : ℝ × ℝ} (hp : p ∈ rect_FIN06809) :
    DifferentiableAt ℝ dzPot_FIN06809 p :=
  (dzPot_contDiffOn_FIN06809.differentiableOn (by simp)).differentiableAt
    (isOpen_rect_FIN06809.mem_nhds hp)

/-- On the rectangle, the Fréchet partial in the second coordinate is the slice derivative. -/
lemma dzPot_eq_slice_FIN06809 {p : ℝ × ℝ} (hp : p ∈ rect_FIN06809) :
    dzPot_FIN06809 p = deriv (fun t : ℝ => liftPotential_FIN06804 p.1 t) p.2 :=
  (hasDerivAt_snd_FIN06807 (potF_differentiableAt_FIN06809 hp)).deriv.symm

/-- Derivative of `t ↦ J(a t, t)` at a point `z` of the curve domain, when `J_u(a z, z) = 0`. -/
lemma hasDerivAt_q_FIN06809 {δz : ℝ} {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)) {z : ℝ} (hz : z ∈ Set.Ioo (-δz) δz)
    (hroot : deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0)
    (hr : (a z, z) ∈ rect_FIN06809) :
    HasDerivAt (fun t : ℝ => liftPotential_FIN06804 (a t) t) (dzPot_FIN06809 (a z, z)) z := by
  have hda : DifferentiableAt ℝ a z :=
    (ha.differentiableOn (by simp)).differentiableAt (Ioo_mem_nhds hz.1 hz.2)
  have hpair : HasDerivAt (fun t : ℝ => ((a t, t) : ℝ × ℝ)) ((deriv a z, 1) : ℝ × ℝ) z :=
    hda.hasDerivAt.prodMk (hasDerivAt_id' z)
  have hF : HasFDerivAt potF_FIN06809 (fderiv ℝ potF_FIN06809 (a z, z)) (a z, z) :=
    (potF_differentiableAt_FIN06809 hr).hasFDerivAt
  have hcomp := hF.comp_hasDerivAt (f := fun t : ℝ => ((a t, t) : ℝ × ℝ)) z hpair
  have h1 : deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) =
      fderiv ℝ potF_FIN06809 (a z, z) (1, 0) :=
    (hasDerivAt_fst_FIN06823 (potF_differentiableAt_FIN06809 hr)).deriv
  have hsplit : ((deriv a z, 1) : ℝ × ℝ) = deriv a z • ((1, 0) : ℝ × ℝ) + ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have hval : fderiv ℝ potF_FIN06809 (a z, z) (deriv a z, 1) = dzPot_FIN06809 (a z, z) := by
    rw [hsplit, map_add, map_smul, smul_eq_mul, ← h1, hroot, mul_zero, zero_add]
    rfl
  rw [← hval]
  exact hcomp

/-- The curve stays in the rectangle, and `t ↦ (a t, t)` lies in it, on a neighbourhood of `0`. -/
lemma eventually_curve_FIN06809 {δz : ℝ} (hδ : 0 < δz) {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)) (ha0 : a 0 = 0) :
    ∀ᶠ z in 𝓝 (0 : ℝ), z ∈ Set.Ioo (-δz) δz ∧ (a z, z) ∈ rect_FIN06809 := by
  have hcont : ContinuousAt a 0 :=
    ha.continuousOn.continuousAt (Ioo_mem_nhds (by linarith : -δz < (0 : ℝ)) hδ)
  have h1 : ∀ᶠ z in 𝓝 (0 : ℝ), a z ∈ Set.Ioo (-1 : ℝ) 1 :=
    hcont.eventually_mem (by rw [ha0]; exact Ioo_mem_nhds (by norm_num) (by norm_num))
  have h2 : ∀ᶠ z in 𝓝 (0 : ℝ), z ∈ Set.Ioo (-1 : ℝ) 1 :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [h1, h2, Ioo_mem_nhds (by linarith : -δz < (0 : ℝ)) hδ] with z hz1 hz2 hz3
  exact ⟨hz3, mem_rect_FIN06809 hz1.1 hz1.2 hz2.1 hz2.2⟩

/-- The value `q 0 = ψ(w₋)`, from the FIN068.04 identity at `u = 0`, `y = 0`. -/
lemma q_zero_FIN06809 {a : ℝ → ℝ} (ha0 : a 0 = 0) :
    liftPotential_FIN06804 (a 0) 0 = quarticPsi_FIN066 !₂[-4, 0] := by
  rw [ha0]
  have h := fin068_04_lift_two_ordinary_variables.2 0 0 (by norm_num) (by norm_num)
  rw [add_zero, zero_pow two_ne_zero] at h
  exact h.symm

/-- The `z`-partial of `J` at the origin vanishes. -/
lemma dzPot_zero_FIN06809 : dzPot_FIN06809 (0, 0) = 0 := by
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ rect_FIN06809 :=
    mem_rect_FIN06809 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨-, h2, -⟩ := fin068_05_exact_jet
  rw [dzPot_eq_slice_FIN06809 h00]
  exact h2

/-- The algebra of the last step. With `D = b/5 - g'(4)` and `D ≠ 0`, the chain-rule value
`(b - 4g')/(32 D) · (-(b - 4g')/32) + (b - 4g')/256` equals `-2 · b(b - 4g')/(10240 D)`. -/
lemma final_alg_FIN06809 (B V D : ℝ) (hD : D ≠ 0) (hDdef : D = B / 5 - V) :
    (B - 4 * V) / (32 * D) * (-(B - 4 * V) / 32) + (B - 4 * V) / 256 =
      -2 * (B * (B - 4 * V) / (10240 * D)) := by
  have hV : V = B / 5 - D := by linarith
  subst hV
  field_simp
  ring

/-- Main declaration, with the derivative of the curve left as a hypothesis-free conclusion:
for any `a` that is `C^∞` on `(-δz, δz)`, with `a 0 = 0` and `J_u(a z, z) = 0` there,
`q z = J(a z, z)` satisfies `q 0 = ψ(w₋)`, `q'(0) = 0` and `q''(0) = -2 c₄`. -/
theorem fin068_09_reduced_quartic_coefficient_any {δz : ℝ} (hδ : 0 < δz) {a : ℝ → ℝ}
    (ha : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)) (ha0 : a 0 = 0)
    (hroot : ∀ z : ℝ, |z| < δz → deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) :
    liftPotential_FIN06804 (a 0) 0 = quarticPsi_FIN066 !₂[-4, 0] ∧
      deriv (fun z : ℝ => liftPotential_FIN06804 (a z) z) 0 = 0 ∧
      deriv (deriv (fun z : ℝ => liftPotential_FIN06804 (a z) z)) 0 =
        -2 * (quarticB * (quarticB - 4 * deriv besselRatio 4) /
          (10240 * (quarticB / 5 - deriv besselRatio 4))) := by
  obtain ⟨-, -, -, -, h5, h6⟩ := fin068_05_exact_jet
  have hA : 0 < quarticB / 5 - deriv besselRatio 4 := by
    obtain ⟨-, -, -, -, -, -, -, ⟨-, -, hA⟩, -, -⟩ :=
      DGPS.FiniteN.quartic_explicit_model_rational_certificate
    exact hA
  have hda0 : deriv a 0 =
      (quarticB - 4 * deriv besselRatio 4) / (32 * (quarticB / 5 - deriv besselRatio 4)) :=
    fin068_23_first_derivative_critical_curve_any hδ ha ha0 hroot
  have hdaZ : DifferentiableAt ℝ a 0 :=
    (ha.differentiableOn (by simp)).differentiableAt
      (Ioo_mem_nhds (by linarith : -δz < (0 : ℝ)) hδ)
  have hpair0 : HasDerivAt (fun t : ℝ => ((a t, t) : ℝ × ℝ)) ((deriv a 0, 1) : ℝ × ℝ) 0 :=
    hdaZ.hasDerivAt.prodMk (hasDerivAt_id' 0)
  have h00 : ((0 : ℝ), (0 : ℝ)) ∈ rect_FIN06809 :=
    mem_rect_FIN06809 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hz0 : (0 : ℝ) ∈ Set.Ioo (-δz) δz := ⟨by linarith, hδ⟩
  have hq0 := q_zero_FIN06809 ha0
  have hev := eventually_curve_FIN06809 hδ ha ha0
  have hderiv : ∀ z : ℝ, z ∈ Set.Ioo (-δz) δz → (a z, z) ∈ rect_FIN06809 →
      HasDerivAt (fun t : ℝ => liftPotential_FIN06804 (a t) t) (dzPot_FIN06809 (a z, z)) z :=
    fun z hz hr => hasDerivAt_q_FIN06809 ha hz (hroot z (abs_lt.2 hz)) hr
  have hq1 : deriv (fun z : ℝ => liftPotential_FIN06804 (a z) z) 0 = 0 := by
    have hr0 : (a 0, (0 : ℝ)) ∈ rect_FIN06809 := by
      rw [ha0]
      exact h00
    rw [(hderiv 0 hz0 hr0).deriv, ha0]
    exact dzPot_zero_FIN06809
  have hev' : deriv (fun z : ℝ => liftPotential_FIN06804 (a z) z) =ᶠ[𝓝 (0 : ℝ)]
      fun z : ℝ => dzPot_FIN06809 (a z, z) := by
    filter_upwards [hev] with z hz
    exact (hderiv z hz.1 hz.2).deriv
  have hdd := dzPot_differentiableAt_FIN06809 h00
  have hF0 : HasFDerivAt dzPot_FIN06809 (fderiv ℝ dzPot_FIN06809 (0, 0)) (a 0, 0) := by
    rw [ha0]
    exact hdd.hasFDerivAt
  have hc : HasDerivAt (fun z : ℝ => dzPot_FIN06809 (a z, z))
      (fderiv ℝ dzPot_FIN06809 (0, 0) (deriv a 0, 1)) 0 :=
    hF0.comp_hasDerivAt (f := fun z : ℝ => ((a z, z) : ℝ × ℝ)) 0 hpair0
  -- the `u`-direction partial of `∂_z J` at the origin
  have hfun1 : (fun s : ℝ => dzPot_FIN06809 (s, 0)) =ᶠ[𝓝 (0 : ℝ)]
      fun s : ℝ => deriv (fun t : ℝ => liftPotential_FIN06804 s t) 0 := by
    have hs : ∀ᶠ s in 𝓝 (0 : ℝ), (s, (0 : ℝ)) ∈ rect_FIN06809 := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
        with s hs
      exact mem_rect_FIN06809 hs.1 hs.2 (by norm_num) (by norm_num)
    filter_upwards [hs] with s hs'
    exact dzPot_eq_slice_FIN06809 hs'
  have e1 : fderiv ℝ dzPot_FIN06809 (0, 0) (1, 0) =
      -(quarticB - 4 * deriv besselRatio 4) / 32 := by
    have e1a : HasDerivAt (fun s : ℝ => dzPot_FIN06809 (s, 0))
        (fderiv ℝ dzPot_FIN06809 (0, 0) (1, 0)) 0 :=
      hasDerivAt_fst_FIN06823 hdd
    rw [← e1a.deriv, hfun1.deriv_eq]
    exact h5
  -- the `z`-direction partial of `∂_z J` at the origin
  have e2 : fderiv ℝ dzPot_FIN06809 (0, 0) (0, 1) = (quarticB - 4 * deriv besselRatio 4) / 256 := by
    have e2a : HasDerivAt (fun t : ℝ => dzPot_FIN06809 (0, t))
        (fderiv ℝ dzPot_FIN06809 (0, 0) (0, 1)) 0 :=
      hasDerivAt_snd_FIN06807 hdd
    have hs : ∀ᶠ t in 𝓝 (0 : ℝ), ((0 : ℝ), t) ∈ rect_FIN06809 := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
        with t ht
      exact mem_rect_FIN06809 (by norm_num) (by norm_num) ht.1 ht.2
    have hfun2 : (fun t : ℝ => dzPot_FIN06809 (0, t)) =ᶠ[𝓝 (0 : ℝ)]
        fun t : ℝ => deriv (fun s : ℝ => liftPotential_FIN06804 0 s) t := by
      filter_upwards [hs] with t ht
      exact dzPot_eq_slice_FIN06809 ht
    rw [← e2a.deriv, hfun2.deriv_eq]
    exact h6
  have hsplit2 : ((deriv a 0, 1) : ℝ × ℝ) = deriv a 0 • ((1, 0) : ℝ × ℝ) + ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have hA' : quarticB / 5 - deriv besselRatio 4 ≠ 0 := hA.ne'
  refine ⟨hq0, hq1, ?_⟩
  rw [hev'.deriv_eq, hc.deriv, hsplit2, map_add, map_smul, smul_eq_mul, e1, e2, hda0]
  exact final_alg_FIN06809 quarticB (deriv besselRatio 4) (quarticB / 5 - deriv besselRatio 4) hA' rfl

/-- Main declaration. Reduced quartic coefficient: the FIN068.07 curve `a` (packaged as in
FIN068.23) satisfies `q 0 = ψ(w₋)`, `q'(0) = 0` and `q''(0) = -2 c₄` for `q z = J(a z, z)`, with
`c₄ = b d / (10240 A)`, `A = b/5 - g'(4)`, `d = b - 4 g'(4)`. -/
theorem fin068_09_reduced_quartic_coefficient :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz → deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      (∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z) ∧
      liftPotential_FIN06804 (a 0) 0 = quarticPsi_FIN066 !₂[-4, 0] ∧
      deriv (fun z : ℝ => liftPotential_FIN06804 (a z) z) 0 = 0 ∧
      deriv (deriv (fun z : ℝ => liftPotential_FIN06804 (a z) z)) 0 =
        -2 * (quarticB * (quarticB - 4 * deriv besselRatio 4) /
          (10240 * (quarticB / 5 - deriv besselRatio 4))) := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, -⟩ := fin068_23_first_derivative_critical_curve
  obtain ⟨hq0, hq1, hq2⟩ := fin068_09_reduced_quartic_coefficient_any hz h1 h2 h3
  exact ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, hq0, hq1, hq2⟩

end DGPS.Frontier.FIN068
