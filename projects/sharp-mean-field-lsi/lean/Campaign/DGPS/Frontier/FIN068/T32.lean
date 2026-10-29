import DGPS.Frontier.FIN068.T31

/-!
Task id and title: FIN068.32, Smooth signed coordinate and base derivative (module
`DGPS.Frontier.FIN068.T32`).

Provides:
* `DGPS.Frontier.FIN068.fin068_32_smooth_signed_coordinate_base_derivative`: there are `δu, δz > 0`
  and a curve `a` with the critical-curve data of FIN068.24/FIN068.30/FIN068.31 (`C^∞` on
  `Set.Ioo (-δz) δz`, `a 0 = 0`, the critical equation for `J_u`, uniqueness of its zero in the
  window), and `δx, δy > 0` such that, with `x₀ y = -4 + a (y^2)` and
  `P = (-4-δx, -4+δx) × (-δy, δy)`: the segments `(x₀ y + t (x - x₀ y), y)`, `t ∈ [0,1]`, over
  `(x, y) ∈ P` lie in `R = (-5,-3) × (-1,1)`; the first-order condition `ψ_x (x₀ y, y) = 0` holds
  on `P`; `x₀` is `C^∞` on `(-δy, δy)` with `x₀' (0) = 0`; `φ y = ψ (x₀ y, y)` is `C^∞` on
  `(-δy, δy)`; there is the factor `a₂ (x, y) = 2 ∫₀¹ (1 - t) ψ_xx(x₀ y + t (x - x₀ y), y) dt`,
  `C^∞` on `P`, with `a₂ (-4, 0) = A` (`A = quarticA_FIN06803`), `A/2 ≤ a₂ ≤ 2A` on `P`, and
  `ψ(x, y) - ψ(x₀ y, y) = (1/2) (x - x₀ y)^2 a₂ (x, y)` on `P`; and there is the signed coordinate
  `v (x, y) = (x - x₀ y) * sqrt (a₂ (x, y))` which is `C^∞` on `P`, satisfies the energy identity
  `ψ(x, y) = v(x, y)^2 / 2 + φ y` on `P`, and at the base point `(-4, 0)` has `v = 0`,
  `v_x = fderiv v (-4, 0) (1, 0) = sqrt A` and `v_y = fderiv v (-4, 0) (0, 1) = 0`.
* Helper declarations, all with suffix `_FIN06832` (not part of the interface):
  `sq_mem_Ioo_FIN06832` (`y^2` lies in the curve window for small `|y|`),
  `x0_smooth_FIN06832` (smoothness of `x₀`), `x0_deriv_zero_FIN06832` (`x₀' (0) = 0`),
  `v_smooth_FIN06832` (smoothness of the signed coordinate from a positive smooth factor),
  `v_energy_FIN06832` (the algebraic identity `(h * sqrt c)^2 / 2 = h^2 c / 2` for `0 ≤ c`),
  `v_base_derivs_FIN06832` (the base-point derivatives of `h * sqrt c`).

Proof: FIN068.31 supplies the curve, the patch, the factor `a₂` with `A/2 ≤ a₂`, and the
factorization. The patch is shrunk in `y` so that `y^2` lies in the curve window, which makes
`x₀` smooth there. Since `a₂ ≥ A/2 > 0` on the patch, `sqrt ∘ a₂` is `C^∞` there (smoothness of the
square root away from `0`), so `v = (x - x₀ y) * sqrt (a₂)` is a product of `C^∞` functions; no sign
function is involved. Squaring gives `v^2 = (x - x₀ y)^2 a₂` (as `a₂ ≥ 0`), hence the energy
identity from the factorization of FIN068.31. At the base point the product rule gives
`D v = h(p₀) • D (sqrt a₂) + sqrt (a₂ p₀) • D h` with `h(p₀) = 0` (because `a 0 = 0`), so the
derivative of `sqrt a₂` is never needed: `D v (p₀) = sqrt A • D h (p₀)` where `h = x - x₀ y` has
`h_x = 1` and `h_y = -x₀'(0) = 0`, the latter from `x₀ y = -4 + a (y^2)`.

R5 notes:
* No hypothesis is added. The statement is closed (existential in the curve, the patch, the
  factor and the coordinate).
* Non-literal reading: "the positive-factor patch" is realised existentially. The patch here is the
  patch `P` of FIN068.31 shrunk in `y` (`δy' = min δy (min δz 1)`), so that `y^2 ∈ (-δz, δz)`; the
  curve window fact needed for the smoothness of `x₀` is not exposed by the statement of
  FIN068.31. So `P` here is a patch of the FIN068.31 kind, not literally the object chosen inside
  FIN068.31's existential. All conclusions of FIN068.31 that are needed downstream are restated for
  the shrunk patch so that it is pinned down.
* `φ` is `fun y => quarticPsi_FIN066 !₂[-4 + a (y^2), y]`, i.e. `ψ(x₀ y, y)`. The specification does
  not require `φ` to be smooth; smoothness of `x₀` and of `φ` on `(-δy, δy)` is recorded as an
  extra conjunct because the consuming tasks use both. It adds no hypothesis.
* `v` is given by its defining formula as a function on all of `ℝ × ℝ`
  (`∀ p, v p = (p.1 - (-4 + a (p.2^2))) * Real.sqrt (a₂ p)`); smoothness, the energy identity and the
  base-point facts are asserted on `P` or at `(-4, 0)` only. `Real.sqrt` is the nonnegative square
  root, which agrees with the specification's `sqrt` because `a₂ ≥ A/2 > 0` on `P`.
* `v_x` and `v_y` at `(-4, 0)` are read as the Fréchet derivative `fderiv ℝ v (-4, 0)` evaluated at
  the unit vectors `(1, 0)` and `(0, 1)` of `ℝ × ℝ`. Since `v` is `C^∞` on the open set `P` containing
  `(-4, 0)`, this is the same as the partial derivatives of the slices.
* `x₀' (0) = 0` is stated as `deriv (fun y => -4 + a (y^2)) 0 = 0`.
* `ψ(x, y)` is `quarticPsi_FIN066 !₂[x, y]`, and `A` is `quarticA_FIN06803` (FIN068.03). Positivity
  `0 < A` is taken from `fin068_03_constants_exact_cancellation`. Smoothness of `ψ` on `R` is
  inherited from FIN068.27, hence from FIN068.04 and the FIN068.37 and FIN068.38 identifications;
  this dependency is not repaired here.
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff Topology

namespace DGPS.Frontier.FIN068

/-- For `|y| < min δz 1` the square `y^2` lies in the curve window `(-δz, δz)`. -/
lemma sq_mem_Ioo_FIN06832 {δz y : ℝ} (hy : |y| < min δz 1) : y ^ 2 ∈ Set.Ioo (-δz) δz := by
  have hy1 : |y| < 1 := lt_of_lt_of_le hy (min_le_right _ _)
  have hyz : |y| < δz := lt_of_lt_of_le hy (min_le_left _ _)
  have hsq : y ^ 2 ≤ |y| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg y, mul_nonneg (abs_nonneg y) (sub_nonneg.2 hy1.le)]
  exact ⟨by nlinarith [sq_nonneg y, abs_nonneg y], lt_of_le_of_lt hsq hyz⟩

/-- The longitudinal curve `x₀ y = -4 + a (y^2)` is `C^∞` where `y^2` lies in the window of `a`. -/
lemma x0_smooth_FIN06832 {a : ℝ → ℝ} {δz : ℝ} {S : Set ℝ}
    (h1 : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)) (hS : ∀ y ∈ S, y ^ 2 ∈ Set.Ioo (-δz) δz) :
    ContDiffOn ℝ ∞ (fun y : ℝ => -4 + a (y ^ 2)) S :=
  contDiffOn_const.add
    (h1.comp (by fun_prop : ContDiff ℝ ∞ (fun y : ℝ => y ^ 2)).contDiffOn hS)

/-- `x₀' (0) = 0` for `x₀ y = -4 + a (y^2)`, since `y ↦ y^2` has zero derivative at `0`. -/
lemma x0_deriv_zero_FIN06832 {a : ℝ → ℝ} {δz : ℝ} (hz : 0 < δz)
    (h1 : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)) :
    deriv (fun y : ℝ => -4 + a (y ^ 2)) 0 = 0 := by
  have ha : DifferentiableAt ℝ a 0 :=
    (h1.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  have ha' : HasDerivAt a (deriv a ((fun y : ℝ => y ^ 2) 0)) ((fun y : ℝ => y ^ 2) 0) := by
    simpa using ha.hasDerivAt
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * 0) 0 := by
    simpa using hasDerivAt_pow 2 (0 : ℝ)
  have hc := (HasDerivAt.comp (h := fun y : ℝ => y ^ 2) (0 : ℝ) ha' hsq).const_add (-4)
  simpa using hc.deriv

/-- The signed coordinate `h * sqrt c` is `C^∞` where `h` and `c` are `C^∞` and `c ≠ 0`. -/
lemma v_smooth_FIN06832 {h c : ℝ × ℝ → ℝ} {P : Set (ℝ × ℝ)}
    (hh : ContDiffOn ℝ ∞ h P) (hc : ContDiffOn ℝ ∞ c P) (hpos : ∀ p ∈ P, c p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => h p * Real.sqrt (c p)) P :=
  hh.mul (hc.sqrt hpos)

/-- The energy identity in algebraic form: `(h * sqrt c)^2 / 2 = h^2 * c / 2` for `0 ≤ c`. -/
lemma v_energy_FIN06832 {h c : ℝ} (hc : 0 ≤ c) : (h * Real.sqrt c) ^ 2 / 2 = (1 / 2) * h ^ 2 * c := by
  rw [mul_pow, Real.sq_sqrt hc]
  ring

/-- Base-point derivatives of `v = h * sqrt c` at `p₀` when `h p₀ = 0` and `c` is differentiable at
`p₀` with `c p₀ ≠ 0`: `D v p₀ = sqrt (c p₀) • D h p₀`, evaluated at `(1, 0)` and `(0, 1)`. -/
lemma v_base_derivs_FIN06832 {h c : ℝ × ℝ → ℝ} {p₀ : ℝ × ℝ} {h' : ℝ × ℝ →L[ℝ] ℝ}
    (hh : HasFDerivAt h h' p₀) (hh0 : h p₀ = 0) (hc : DifferentiableAt ℝ c p₀)
    (hpos : c p₀ ≠ 0) :
    fderiv ℝ (fun p : ℝ × ℝ => h p * Real.sqrt (c p)) p₀ (1, 0) = Real.sqrt (c p₀) * h' (1, 0) ∧
    fderiv ℝ (fun p : ℝ × ℝ => h p * Real.sqrt (c p)) p₀ (0, 1) = Real.sqrt (c p₀) * h' (0, 1) := by
  have hs : DifferentiableAt ℝ (fun p : ℝ × ℝ => Real.sqrt (c p)) p₀ :=
    ((Real.contDiffAt_sqrt (n := 1) hpos).differentiableAt (by simp)).comp p₀ hc
  have hprod : HasFDerivAt (fun p : ℝ × ℝ => h p * Real.sqrt (c p)) _ p₀ := hh.mul hs.hasFDerivAt
  rw [hprod.fderiv]
  simp [hh0]

/-- Smooth signed coordinate and base derivative (FIN068.32). -/
theorem fin068_32_smooth_signed_coordinate_base_derivative :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      (∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z) ∧
      ∃ δx δy : ℝ, 0 < δx ∧ 0 < δy ∧
        (∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          t ∈ Set.Icc (0 : ℝ) 1 →
          (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2))), y) ∈
            Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) ∧
        (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, y]) (-4 + a (y ^ 2)) = 0) ∧
        ContDiffOn ℝ ∞ (fun y : ℝ => -4 + a (y ^ 2)) (Set.Ioo (-δy) δy) ∧
        deriv (fun y : ℝ => -4 + a (y ^ 2)) 0 = 0 ∧
        ContDiffOn ℝ ∞ (fun y : ℝ => quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y])
          (Set.Ioo (-δy) δy) ∧
        ∃ a₂ : ℝ × ℝ → ℝ,
          (∀ p : ℝ × ℝ, a₂ p = 2 * ∫ t in (0 : ℝ)..1, (1 - t) *
            deriv (deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, p.2]))
              (-4 + a (p.2 ^ 2) + t * (p.1 - (-4 + a (p.2 ^ 2))))) ∧
          ContDiffOn ℝ ∞ a₂ (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) ∧
          a₂ (-4, 0) = quarticA_FIN06803 ∧
          (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            quarticA_FIN06803 / 2 ≤ a₂ (x, y) ∧ a₂ (x, y) ≤ 2 * quarticA_FIN06803) ∧
          (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            quarticPsi_FIN066 !₂[x, y] - quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y] =
              (1 / 2) * (x - (-4 + a (y ^ 2))) ^ 2 * a₂ (x, y)) ∧
          ∃ v : ℝ × ℝ → ℝ,
            (∀ p : ℝ × ℝ, v p = (p.1 - (-4 + a (p.2 ^ 2))) * Real.sqrt (a₂ p)) ∧
            ContDiffOn ℝ ∞ v (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) ∧
            (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
              quarticPsi_FIN066 !₂[x, y] =
                v (x, y) ^ 2 / 2 + quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y]) ∧
            v (-4, 0) = 0 ∧
            fderiv ℝ v (-4, 0) (1, 0) = Real.sqrt quarticA_FIN06803 ∧
            fderiv ℝ v (-4, 0) (0, 1) = 0 := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, a₂, hdef, hsm,
    hbase, hbd, hfac⟩ := fin068_31_smoothness_positivity_factor
  obtain ⟨-, -, hApos, -⟩ := fin068_03_constants_exact_cancellation
  set δy' : ℝ := min δy (min δz 1) with hδy'
  have hδy'pos : 0 < δy' := lt_min hδy (lt_min hz one_pos)
  have hδy'δy : δy' ≤ δy := min_le_left _ _
  have hsubI : Set.Ioo (-δy') δy' ⊆ Set.Ioo (-δy) δy :=
    Set.Ioo_subset_Ioo (neg_le_neg hδy'δy) hδy'δy
  have hsub : Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy') δy' ⊆
      Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy :=
    Set.prod_mono subset_rfl hsubI
  have hy2 : ∀ y ∈ Set.Ioo (-δy') δy', y ^ 2 ∈ Set.Ioo (-δz) δz := by
    intro y hy
    refine sq_mem_Ioo_FIN06832 (lt_of_lt_of_le (abs_lt.mpr ⟨hy.1, hy.2⟩) ?_)
    exact min_le_right _ _
  have hx0 : ContDiffOn ℝ ∞ (fun y : ℝ => -4 + a (y ^ 2)) (Set.Ioo (-δy') δy') :=
    x0_smooth_FIN06832 h1 hy2
  have hx0d : deriv (fun y : ℝ => -4 + a (y ^ 2)) 0 = 0 := x0_deriv_zero_FIN06832 hz h1
  have hmem : ∀ y : ℝ, y ∈ Set.Ioo (-δy') δy' →
      (-4, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy') δy' :=
    fun y hy => ⟨⟨by linarith, by linarith⟩, hy⟩
  have hφ : ContDiffOn ℝ ∞ (fun y : ℝ => quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y])
      (Set.Ioo (-δy') δy') := by
    have hc := psi_smooth_FIN06827.comp
      (hx0.prodMk (by fun_prop : ContDiff ℝ ∞ (fun y : ℝ => y)).contDiffOn)
      (fun y hy => by
        have := hseg (-4) y 0 (hsub (hmem y hy)) ⟨le_rfl, zero_le_one⟩
        simpa using this)
    exact hc
  have hP' : Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy') δy' ∈ 𝓝 ((-4 : ℝ), (0 : ℝ)) :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
      ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  refine ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy', hδx, hδy'pos,
    fun x y t hP ht => hseg x y t (hsub hP) ht, fun x y hP => hcrit x y (hsub hP),
    hx0, hx0d, hφ, a₂, hdef, hsm.mono hsub, hbase,
    fun x y hP => hbd x y (hsub hP), fun x y hP => hfac x y (hsub hP), ?_⟩
  have hpos : ∀ p ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy') δy', a₂ p ≠ 0 := by
    intro p hp
    have := (hbd p.1 p.2 (hsub hp)).1
    linarith
  have hh : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.1 - (-4 + a (p.2 ^ 2)))
      (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy') δy') :=
    (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.1)).contDiffOn.sub
      (hx0.comp (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => p.2)).contDiffOn
        (fun p hp => hp.2))
  have hdc : DifferentiableAt ℝ a₂ (-4, 0) :=
    ((hsm.mono hsub).differentiableOn (by simp)).differentiableAt hP'
  have hx0diff : DifferentiableAt ℝ (fun y : ℝ => -4 + a (y ^ 2)) 0 :=
    (hx0.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  have hx0h : HasDerivAt (fun y : ℝ => -4 + a (y ^ 2)) 0 0 := by
    simpa [hx0d] using hx0diff.hasDerivAt
  have hcomp : HasFDerivAt ((fun y : ℝ => -4 + a (y ^ 2)) ∘ fun p : ℝ × ℝ => p.2)
      ((0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ) ((-4 : ℝ), (0 : ℝ)) :=
    HasDerivAt.comp_hasFDerivAt (x := ((-4 : ℝ), (0 : ℝ))) (f := fun p : ℝ × ℝ => p.2)
      hx0h (hasFDerivAt_snd)
  have hhd : HasFDerivAt (fun p : ℝ × ℝ => p.1 - (-4 + a (p.2 ^ 2)))
      (ContinuousLinearMap.fst ℝ ℝ ℝ - (0 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((-4 : ℝ), (0 : ℝ)) :=
    hasFDerivAt_fst.sub hcomp
  have hh0 : (fun p : ℝ × ℝ => p.1 - (-4 + a (p.2 ^ 2))) (-4, 0) = 0 := by
    simp [h2]
  obtain ⟨hdx, hdy⟩ := v_base_derivs_FIN06832 hhd hh0 hdc (by rw [hbase]; exact hApos.ne')
  rw [hbase] at hdx hdy
  simp at hdx hdy
  refine ⟨fun p => (p.1 - (-4 + a (p.2 ^ 2))) * Real.sqrt (a₂ p), fun p => rfl,
    v_smooth_FIN06832 hh (hsm.mono hsub) hpos, ?_, ?_, ?_, ?_⟩
  · intro x y hP
    have hf := hfac x y (hsub hP)
    have hge := (hbd x y (hsub hP)).1
    have hnn : 0 ≤ a₂ (x, y) := by linarith
    show quarticPsi_FIN066 !₂[x, y] =
      ((x - (-4 + a (y ^ 2))) * Real.sqrt (a₂ (x, y))) ^ 2 / 2 + _
    rw [v_energy_FIN06832 hnn]
    linarith
  · have e0 : a ((0 : ℝ) ^ 2) = 0 := by
      rw [show ((0 : ℝ) ^ 2) = 0 by norm_num]
      exact h2
    show ((-4 : ℝ) - (-4 + a ((0 : ℝ) ^ 2))) * Real.sqrt (a₂ (-4, 0)) = 0
    rw [e0]
    ring
  · exact hdx
  · exact hdy

end DGPS.Frontier.FIN068
