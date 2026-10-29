import DGPS.Frontier.FIN068.T30
import DGPS.Frontier.FIN068.T29
import DGPS.Frontier.FIN068.T05
import DGPS.Frontier.FIN068.T03
import DGPS.Frontier.FIN068.T04

/-!
Task id and title: FIN068.31, Smoothness and positivity of the factor (module
`DGPS.Frontier.FIN068.T31`).

Provides:
* `DGPS.Frontier.FIN068.fin068_31_smoothness_positivity_factor`: there are `δu, δz > 0` and a curve
  `a` with the critical-curve data of FIN068.24/FIN068.30 (`C^∞` on `Set.Ioo (-δz) δz`, `a 0 = 0`,
  the critical equation for `J_u`, uniqueness of its zero in the window), and `δx, δy > 0` such that,
  with `x₀ y = -4 + a (y^2)` and `P = (-4-δx, -4+δx) × (-δy, δy)`: the segments
  `(x₀ y + t (x - x₀ y), y)`, `t ∈ [0,1]`, over `(x, y) ∈ P` lie in `R = (-5,-3) × (-1,1)`; the
  first-order condition `ψ_x (x₀ y, y) = 0` holds on `P`; and there is a map
  `a₂ : ℝ × ℝ → ℝ` with `a₂ (x, y) = 2 ∫₀¹ (1 - t) ψ_xx(x₀ y + t (x - x₀ y), y) dt`, which is `C^∞`
  on `P`, satisfies `a₂ (-4, 0) = A` (`A = quarticA_FIN06803`), satisfies `A/2 ≤ a₂ ≤ 2A` on `P`,
  and gives the factorization `ψ(x, y) - ψ(x₀ y, y) = (1/2) (x - x₀ y)^2 a₂ (x, y)` on `P`.
* Helper declarations, all with suffix `_FIN06831` (not part of the interface):
  `iteratedFDeriv_slice_FIN06831` (iterated derivative of a parameter slice of a smooth map on an
  open set), `ddxPsi_FIN06831` (the slice second derivative `ψ_xx`),
  `ddxPsi_continuousAt_FIN06831` (continuity of `ψ_xx` at `(-4, 0)`), `ddxPsi_base_FIN06831`
  (`ψ_xx (-4, 0) = A`), `patchU_FIN06831` (the open set of `((x, y), t)` on which the integrand is
  smooth), `integrand_smooth_FIN06831` (openness of `patchU` and smoothness of the integrand there),
  `a2_smooth_FIN06831` (smoothness of `a₂` by FIN068.29), `integral_weight_const_FIN06831`
  (`∫₀¹ (1 - t) c dt = c / 2`), `integrand_continuousOn_FIN06831` (continuity of the integrand on
  `[0,1]`), `a2_bounds_FIN06831` (ordered integration of the pointwise bounds on `ψ_xx`).

Proof: FIN068.30 supplies the curve, the patch `P0`, the critical equation and the exact
factorization `ψ(x, y) - ψ(x₀ y, y) = h^2 ∫₀¹ (1 - t) ψ_xx(x₀ y + t h, y) dt`. `ψ_xx` is continuous at
`(-4, 0)` with value `A > 0` (FIN068.05 jet and FIN068.04 lift, `A = quarticA_FIN06803` by
FIN068.03), so there is `ρ ≤ 1/2` with `A/2 ≤ ψ_xx ≤ 2A` on the `ρ`-box. The patch is shrunk so that
`x₀ y` is within `ρ` of `-4` (continuity of the curve at `0`) and `|x + 4| < ρ`, `|y| < ρ`; every
segment point is then a convex combination of two points within `ρ` of `-4`, so the bounds hold
along every segment. Integrating against the nonnegative weight `1 - t`, whose integral is `1/2`,
gives `A/2 ≤ a₂ ≤ 2A` and, with the constant `ψ_xx = A` at the base point, `a₂ (-4, 0) = A`.
Smoothness of `a₂` is FIN068.29 applied to the explicit integrand `2 (1 - t) ψ_xx(F(x, y, t))`,
which is `C^∞` on the open set `patchU` (composition of the smooth segment map `F` with the
`C^∞` function `ψ_xx` on `R`, FIN068.27 machinery).

R5 notes:
* No hypothesis is added. The statement is closed (existential in the curve and the patch).
* Non-literal reading: "after shrinking the common patch" is realised existentially. The patch
  `P` here is obtained from the patch of FIN068.30 by shrinking (`δx = min ρ δx₀`,
  `δy = min (ε, δz, δy₀, ρ)`), so it is a patch of the FIN068.27/FIN068.30 kind, not literally the
  object chosen inside those existentials. The segment-containment, critical-equation and
  factorization facts for the shrunk patch are restated so that the patch is pinned down.
* `ψ(x, y)` is `quarticPsi_FIN066 !₂[x, y]`. `ψ_xx` is read as the second derivative of the slice
  `s ↦ ψ(s, y)`, `deriv (deriv (fun s => quarticPsi_FIN066 !₂[s, y]))`, as in FIN068.27 and
  FIN068.30. `x₀ y` is `-4 + a (y^2)`.
* `a₂` is given by its defining formula as a function on all of `ℝ × ℝ` (`∀ p, a₂ p = ...`); the
  smoothness, base value and bounds are asserted on `P` only. The integral is the interval
  integral `∫ t in (0:ℝ)..1` of `(1 - t) * ψ_xx(...)`, so `a₂` carries the factor `2` of the displayed
  `2 ∫₀¹ (1 - t) ψ_xx dt`.
* `A` is `quarticA_FIN06803`, the campaign constant of FIN068.03; positivity `0 < A` is taken from
  `fin068_03_constants_exact_cancellation`. The bound `A/2 ≤ a₂ ≤ 2A` is proved by the second route
  of the specification (pointwise bounds on `ψ_xx` along segments and ordered integration), and the
  base value uses the same unit integral `∫₀¹ 2 (1 - t) dt = 1`.
* The smoothness of the integrand is established on the open set `patchU` (a preimage of `R` under
  the segment map, intersected with `y^2 ∈ (-δz, δz)`), where FIN068.29 applies with
  `U = P` and the parameter set `[0,1]`; the continuity hypothesis of FIN068.29 is discharged by
  continuity of the iterated derivatives on `patchU` and the slice lemma
  `iteratedFDeriv_slice_FIN06831`.
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff Topology

namespace DGPS.Frontier.FIN068

/-- The iterated derivative in `p` of the slice `p ↦ Φ (p, t)` of a smooth function on an open set. -/
lemma iteratedFDeriv_slice_FIN06831 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {W : Set (E × ℝ)} (hW : IsOpen W) {Φ : E × ℝ → F}
    (hΦ : ContDiffOn ℝ ∞ Φ W) (k : ℕ) {t : ℝ} {p : E} (hp : (p, t) ∈ W) :
    iteratedFDeriv ℝ k (fun x : E => Φ (x, t)) p =
      (iteratedFDeriv ℝ k Φ (p, t)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E ℝ) := by
  set c : E × ℝ := (0, t) with hc
  set Wc : Set (E × ℝ) := (fun w => w + c) ⁻¹' W with hWc
  have hWco : IsOpen Wc := hW.preimage (continuous_id.add continuous_const)
  have hΦc : ContDiffOn ℝ ∞ (fun w => Φ (w + c)) Wc :=
    hΦ.comp (contDiff_id.add contDiff_const).contDiffOn (fun w hw => hw)
  have hpc : ContinuousLinearMap.inl ℝ E ℝ p ∈ Wc := by
    simpa [hWc, hc] using hp
  have hfun : (fun x : E => Φ (x, t)) =
      (fun w => Φ (w + c)) ∘ (ContinuousLinearMap.inl ℝ E ℝ) := by
    funext x; simp [hc]
  have hso : IsOpen (ContinuousLinearMap.inl ℝ E ℝ ⁻¹' Wc) :=
    hWco.preimage (ContinuousLinearMap.inl ℝ E ℝ).continuous
  have h1 := (ContinuousLinearMap.inl ℝ E ℝ).iteratedFDerivWithin_comp_right hΦc
    hWco.uniqueDiffOn hso.uniqueDiffOn hpc (i := k) (by exact_mod_cast le_top)
  have e1 : iteratedFDeriv ℝ k (fun x : E => Φ (x, t)) p =
      iteratedFDerivWithin ℝ k ((fun w => Φ (w + c)) ∘ (ContinuousLinearMap.inl ℝ E ℝ))
        (ContinuousLinearMap.inl ℝ E ℝ ⁻¹' Wc) p := by
    rw [← hfun]
    exact (iteratedFDerivWithin_of_isOpen k hso hpc).symm
  rw [e1, h1, iteratedFDerivWithin_of_isOpen k hWco hpc, iteratedFDeriv_comp_add_right]
  have : ContinuousLinearMap.inl ℝ E ℝ p + c = (p, t) := by simp [hc]
  rw [this]

/-- The second partial `ψ_xx(x, y)` of the named potential, as the second derivative of the slice
`s ↦ ψ(s, y)` evaluated at `x`. -/
noncomputable def ddxPsi_FIN06831 (x y : ℝ) : ℝ :=
  deriv (deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, y])) x

/-- `ψ_xx` is continuous at the base point `(-4, 0)`. -/
lemma ddxPsi_continuousAt_FIN06831 :
    ContinuousAt (fun q : ℝ × ℝ => ddxPsi_FIN06831 q.1 q.2) (-4, 0) := by
  have hRo : IsOpen (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    isOpen_Ioo.prod isOpen_Ioo
  obtain ⟨hD1, -⟩ := slice_FIN06827 hRo psi_smooth_FIN06827
  obtain ⟨hD2, -⟩ := slice_FIN06827 hRo hD1
  have hmem : ((-4 : ℝ), (0 : ℝ)) ∈ Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    Set.mk_mem_prod ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
  have hc := hD2.continuousOn.continuousAt (hRo.mem_nhds hmem)
  refine hc.congr ?_
  filter_upwards [hRo.mem_nhds hmem] with q hq
  exact (ddx_FIN06827 (p := q.1) (y := q.2) hq).symm

/-- The base value `ψ_xx(-4, 0) = A`. -/
lemma ddxPsi_base_FIN06831 : ddxPsi_FIN06831 (-4) 0 = quarticA_FIN06803 := by
  have hev : (fun s : ℝ => quarticPsi_FIN066 !₂[s, 0]) =ᶠ[𝓝 (-4 : ℝ)]
      fun s : ℝ => liftPotential_FIN06804 (s + 4) 0 := by
    have hn : {x : ℝ | |x + 4| < 1} ∈ 𝓝 (-4 : ℝ) := by
      refine (isOpen_lt (continuous_abs.comp (continuous_id.add continuous_const))
        continuous_const).mem_nhds ?_
      simp
    filter_upwards [hn] with x hx
    have h := fin068_04_lift_two_ordinary_variables.2 (x + 4) 0 hx (by norm_num)
    simpa using h
  have hd : deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, 0]) =ᶠ[𝓝 (-4 : ℝ)]
      fun s : ℝ => deriv (fun r : ℝ => liftPotential_FIN06804 r 0) (s + 4) := by
    filter_upwards [hev.eventuallyEq_nhds] with x hx
    rw [hx.deriv_eq]
    exact deriv_comp_add_const (f := fun r : ℝ => liftPotential_FIN06804 r 0) 4 x
  unfold ddxPsi_FIN06831
  rw [hd.deriv_eq]
  have h2 := deriv_comp_add_const (f := fun t : ℝ => deriv (fun r : ℝ => liftPotential_FIN06804 r 0) t)
    4 (-4)
  rw [show (-4 + 4 : ℝ) = 0 by norm_num] at h2
  rw [h2]
  exact fin068_05_exact_jet.2.2.1

/-- The open set `{((x, y), t) | y^2 ∈ (-δz, δz), (x₀ y + t (x - x₀ y), y) ∈ R}` on which the integrand
of `a₂` is smooth. -/
def patchU_FIN06831 (a : ℝ → ℝ) (δz : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} ∩
    Fmap_FIN06827 a ⁻¹' (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1)

/-- The integrand `2 (1 - t) ψ_xx(x₀ y + t (x - x₀ y), y)` of `a₂` is `C^∞` on `patchU`, which is
open. -/
lemma integrand_smooth_FIN06831 {a : ℝ → ℝ} {δz : ℝ}
    (h1 : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz)) :
    IsOpen (patchU_FIN06831 a δz) ∧
    ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => 2 * (1 - q.2) *
      ddxPsi_FIN06831 (-4 + a (q.1.2 ^ 2) + q.2 * (q.1.1 - (-4 + a (q.1.2 ^ 2)))) q.1.2)
      (patchU_FIN06831 a δz) := by
  have hRo : IsOpen (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hcont2 : Continuous fun q : (ℝ × ℝ) × ℝ => q.1.2 ^ 2 := by fun_prop
  have hS0o : IsOpen {q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} :=
    hcont2.isOpen_preimage _ isOpen_Ioo
  have ha' : ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => a (q.1.2 ^ 2))
      {q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} :=
    h1.comp (by fun_prop : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => q.1.2 ^ 2)).contDiffOn
      (fun q hq => hq)
  have hA : ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => -4 + a (q.1.2 ^ 2))
      {q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} :=
    contDiffOn_const.add ha'
  have hxq : ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => q.1.1)
      {q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} :=
    (by fun_prop : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => q.1.1)).contDiffOn
  have htq : ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => q.2)
      {q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} :=
    (by fun_prop : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => q.2)).contDiffOn
  have hyq : ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => q.1.2)
      {q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} :=
    (by fun_prop : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => q.1.2)).contDiffOn
  have hFc : ContDiffOn ℝ ∞ (Fmap_FIN06827 a)
      {q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} :=
    ContDiffOn.prodMk (hA.add (htq.mul (hxq.sub hA))) hyq
  refine ⟨hFc.continuousOn.isOpen_inter_preimage hS0o hRo, ?_⟩
  obtain ⟨hD1, -⟩ := slice_FIN06827 hRo psi_smooth_FIN06827
  obtain ⟨hD2, -⟩ := slice_FIN06827 hRo hD1
  have hFU : ContDiffOn ℝ ∞ (Fmap_FIN06827 a) (patchU_FIN06831 a δz) :=
    hFc.mono Set.inter_subset_left
  have hcomp : ContDiffOn ℝ ∞
      (fun q : (ℝ × ℝ) × ℝ => fderiv ℝ (fun r : ℝ × ℝ => fderiv ℝ
        (fun p : ℝ × ℝ => quarticPsi_FIN066 !₂[p.1, p.2]) r (1, 0)) (Fmap_FIN06827 a q) (1, 0))
      (patchU_FIN06831 a δz) :=
    hD2.comp hFU (fun q hq => hq.2)
  have hc1 : ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => 2 * (1 - q.2)) (patchU_FIN06831 a δz) :=
    contDiffOn_const.mul (contDiffOn_const.sub (htq.mono Set.inter_subset_left))
  refine (hc1.mul hcomp).congr ?_
  intro q hq
  have hd := ddx_FIN06827 (p := -4 + a (q.1.2 ^ 2) + q.2 * (q.1.1 - (-4 + a (q.1.2 ^ 2))))
    (y := q.1.2) hq.2
  exact congrArg (fun z : ℝ => 2 * (1 - q.2) * z) hd

/-- Smoothness of `a₂` on a rectangle `P` all of whose segments lie in the smooth patch: FIN068.29
applied to the explicit integrand. -/
lemma a2_smooth_FIN06831 {a : ℝ → ℝ} {δz δx δy : ℝ}
    (h1 : ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz))
    (hP : ∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
      t ∈ Set.Icc (0 : ℝ) 1 → ((x, y), t) ∈ patchU_FIN06831 a δz) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => 2 * ∫ t in (0 : ℝ)..1, (1 - t) *
      ddxPsi_FIN06831 (-4 + a (p.2 ^ 2) + t * (p.1 - (-4 + a (p.2 ^ 2)))) p.2)
      (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) := by
  obtain ⟨hUo, hΦ⟩ := integrand_smooth_FIN06831 h1
  set Φ : (ℝ × ℝ) × ℝ → ℝ := fun q => 2 * (1 - q.2) *
      ddxPsi_FIN06831 (-4 + a (q.1.2 ^ 2) + q.2 * (q.1.1 - (-4 + a (q.1.2 ^ 2)))) q.1.2 with hΦdef
  set P : Set (ℝ × ℝ) := Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy with hPdef
  have hPo : IsOpen P := isOpen_Ioo.prod isOpen_Ioo
  have hPU : ∀ p ∈ P, ∀ t ∈ Set.Icc (0 : ℝ) 1, (p, t) ∈ patchU_FIN06831 a δz :=
    fun p hp t ht => hP p.1 p.2 t hp ht
  have hsm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Φ (p, t)) P := by
    intro t ht
    exact hΦ.comp (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p, t))).contDiffOn
      (fun p hp => hPU p hp t ht)
  have hcont : ∀ k : ℕ, ContinuousOn
      (fun q : ℝ × (ℝ × ℝ) => iteratedFDeriv ℝ k (fun p : ℝ × ℝ => Φ (p, q.1)) q.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ P) := by
    intro k
    have hIk : ContinuousOn (iteratedFDeriv ℝ k Φ) (patchU_FIN06831 a δz) := by
      have := hΦ.continuousOn_iteratedFDerivWithin (m := k) (by exact_mod_cast le_top)
        hUo.uniqueDiffOn
      exact this.congr (fun x hx => (iteratedFDerivWithin_of_isOpen k hUo hx).symm)
    have hswap : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => (q.2, q.1))
        (Set.Icc (0 : ℝ) 1 ×ˢ P) := by fun_prop
    have hmaps : Set.MapsTo (fun q : ℝ × (ℝ × ℝ) => (q.2, q.1)) (Set.Icc (0 : ℝ) 1 ×ˢ P)
        (patchU_FIN06831 a δz) := fun q hq => hPU q.2 hq.2 q.1 hq.1
    have h2 := (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin k => ContinuousLinearMap.inl ℝ (ℝ × ℝ) ℝ) :
        ContinuousMultilinearMap ℝ (fun _ : Fin k => (ℝ × ℝ) × ℝ) ℝ →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin k => ℝ × ℝ) ℝ).continuous.comp_continuousOn
      (hIk.comp hswap hmaps)
    refine h2.congr (fun q hq => ?_)
    exact iteratedFDeriv_slice_FIN06831 hUo hΦ k (hPU q.2 hq.2 q.1 hq.1)
  have hT := (fin068_29_order_compact_parameter_integration hPo
    (H := fun t p => Φ (p, t)) hsm hcont).1
  refine hT.congr (fun p hp => ?_)
  simp only [hΦdef]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  simp only [mul_assoc]

/-- The weight `1 - t` integrates to `1/2`, so `∫ (1 - t) c = c / 2`. -/
lemma integral_weight_const_FIN06831 (c : ℝ) :
    ∫ t in (0 : ℝ)..1, (1 - t) * c = c / 2 := by
  rw [intervalIntegral.integral_mul_const]
  have h : ∫ x in (0 : ℝ)..1, (1 - x) = 1 / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    simp
    norm_num
  rw [h]
  ring

/-- The integrand `t ↦ (1 - t) ψ_xx(p + t (x - p), y)` is continuous on `[0,1]` when the segment
lies in `(-5, -3)` and `|y| < 1`. -/
lemma integrand_continuousOn_FIN06831 {y p x : ℝ} (hy : |y| < 1)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, p + t * (x - p) ∈ Set.Ioo (-5 : ℝ) (-3)) :
    ContinuousOn (fun t : ℝ => (1 - t) * ddxPsi_FIN06831 (p + t * (x - p)) y) (Set.Icc 0 1) := by
  obtain ⟨-, -, c2⟩ := hasDerivAt_slice_FIN06830 hy
  have : ContinuousOn (fun t : ℝ => ddxPsi_FIN06831 (p + t * (x - p)) y) (Set.Icc 0 1) :=
    c2.comp (by fun_prop : Continuous fun t : ℝ => p + t * (x - p)).continuousOn hseg
  exact (continuousOn_const.sub continuousOn_id).mul this

/-- Ordered integration: if `A/2 ≤ ψ_xx ≤ 2A` along the segment then `A/2 ≤ a₂ ≤ 2A`. -/
lemma a2_bounds_FIN06831 {A y p x : ℝ} (hy : |y| < 1)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, p + t * (x - p) ∈ Set.Ioo (-5 : ℝ) (-3))
    (hlo : ∀ t ∈ Set.Icc (0 : ℝ) 1, A / 2 ≤ ddxPsi_FIN06831 (p + t * (x - p)) y)
    (hhi : ∀ t ∈ Set.Icc (0 : ℝ) 1, ddxPsi_FIN06831 (p + t * (x - p)) y ≤ 2 * A) :
    A / 2 ≤ 2 * ∫ t in (0 : ℝ)..1, (1 - t) * ddxPsi_FIN06831 (p + t * (x - p)) y ∧
    2 * ∫ t in (0 : ℝ)..1, (1 - t) * ddxPsi_FIN06831 (p + t * (x - p)) y ≤ 2 * A := by
  have hc := integrand_continuousOn_FIN06831 hy hseg
  have hint : IntervalIntegrable (fun t : ℝ => (1 - t) * ddxPsi_FIN06831 (p + t * (x - p)) y)
      MeasureTheory.volume 0 1 := hc.intervalIntegrable_of_Icc zero_le_one
  have hconst : ∀ c : ℝ, IntervalIntegrable (fun t : ℝ => (1 - t) * c) MeasureTheory.volume 0 1 :=
    fun c => (continuousOn_const.sub continuousOn_id |>.mul continuousOn_const
      ).intervalIntegrable_of_Icc zero_le_one
  have hnn : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ 1 - t := fun t ht => sub_nonneg.2 ht.2
  have h1 := intervalIntegral.integral_mono_on zero_le_one (hconst (A / 2)) hint
    (fun t ht => mul_le_mul_of_nonneg_left (hlo t ht) (hnn t ht))
  have h2 := intervalIntegral.integral_mono_on zero_le_one hint (hconst (2 * A))
    (fun t ht => mul_le_mul_of_nonneg_left (hhi t ht) (hnn t ht))
  rw [integral_weight_const_FIN06831] at h1 h2
  constructor <;> linarith

/-- Smoothness and positivity of the factor (FIN068.31). -/
theorem fin068_31_smoothness_positivity_factor :
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
              (1 / 2) * (x - (-4 + a (y ^ 2))) ^ 2 * a₂ (x, y)) := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx0, δy0, hδx0, hδy0, hseg0, hcrit0, hfac0⟩ :=
    fin068_30_exact_second_order_factorization
  refine ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, ?_⟩
  obtain ⟨-, -, hApos, -⟩ := fin068_03_constants_exact_cancellation
  obtain ⟨r, hr, hrG⟩ := Metric.continuousAt_iff.1 ddxPsi_continuousAt_FIN06831
    (quarticA_FIN06803 / 2) (by linarith)
  have hG : ∀ s y : ℝ, |s + 4| < r → |y| < r →
      quarticA_FIN06803 / 2 ≤ ddxPsi_FIN06831 s y ∧
        ddxPsi_FIN06831 s y ≤ 2 * quarticA_FIN06803 := by
    intro s y hs hy
    have hd : dist (s, y) ((-4 : ℝ), (0 : ℝ)) < r := by
      rw [Prod.dist_eq]
      refine max_lt ?_ ?_
      · rw [Real.dist_eq]
        simpa [sub_neg_eq_add] using hs
      · rw [Real.dist_eq, sub_zero]
        exact hy
    have h0 := @hrG (s, y) hd
    have h : dist (ddxPsi_FIN06831 s y) (ddxPsi_FIN06831 (-4) 0) < quarticA_FIN06803 / 2 := h0
    rw [Real.dist_eq, ddxPsi_base_FIN06831] at h
    obtain ⟨hl, hh⟩ := abs_lt.mp h
    constructor <;> linarith
  set ρ : ℝ := min r (1 / 2) with hρ
  have hρpos : 0 < ρ := lt_min hr (by norm_num)
  have hρr : ρ ≤ r := min_le_left _ _
  have hρ2 : ρ ≤ 1 / 2 := min_le_right _ _
  have hc0 : ContinuousAt a 0 :=
    h1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  obtain ⟨ε, hε, hεa⟩ := Metric.continuousAt_iff.1 hc0 ρ hρpos
  set δx : ℝ := min ρ δx0 with hδxdef
  set δy : ℝ := min (min (min ε δz) δy0) ρ with hδydef
  have hδx : 0 < δx := lt_min hρpos hδx0
  have hδy : 0 < δy := lt_min (lt_min (lt_min hε hz) hδy0) hρpos
  have hyprop : ∀ y : ℝ, |y| < δy →
      y ^ 2 < ε ∧ y ^ 2 < δz ∧ |y| < ρ ∧ |y| < δy0 ∧ |y| < 1 := by
    intro y hy
    have hyρ : |y| < ρ := lt_of_lt_of_le hy (min_le_right _ _)
    have hy1 : |y| < 1 := by linarith
    have hy0 : |y| < δy0 :=
      lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_right _ _))
    have hy2 : |y| < min ε δz :=
      lt_of_lt_of_le hy (((min_le_left _ _).trans (min_le_left _ _)))
    have hsq : y ^ 2 ≤ |y| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg y, mul_nonneg (abs_nonneg y) (sub_nonneg.2 hy1.le)]
    exact ⟨lt_of_le_of_lt hsq (lt_of_lt_of_le hy2 (min_le_left _ _)),
      lt_of_le_of_lt hsq (lt_of_lt_of_le hy2 (min_le_right _ _)), hyρ, hy0, hy1⟩
  have hα : ∀ y : ℝ, |y| < δy → |a (y ^ 2)| < ρ := by
    intro y hy
    have hd : dist (y ^ 2) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg y)]
      exact (hyprop y hy).1
    have := hεa hd
    rwa [Real.dist_eq, h2, sub_zero] at this
  have hP0 : ∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
      (x, y) ∈ Set.Ioo (-4 - δx0) (-4 + δx0) ×ˢ Set.Ioo (-δy0) δy0 := by
    intro x y hP
    obtain ⟨⟨hx1, hx2⟩, hy⟩ := hP
    have hxd : δx ≤ δx0 := min_le_right _ _
    have hy' : |y| < δy := abs_lt.mpr hy
    obtain ⟨-, -, -, hy0, -⟩ := hyprop y hy'
    exact ⟨⟨by linarith, by linarith⟩, abs_lt.mp hy0⟩
  have hxρ : ∀ x : ℝ, x ∈ Set.Ioo (-4 - δx) (-4 + δx) → |x + 4| < ρ := by
    intro x hx
    have hxd : δx ≤ ρ := min_le_left _ _
    exact abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsegG : ∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
      t ∈ Set.Icc (0 : ℝ) 1 →
      |(-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2)))) + 4| < ρ := by
    intro x y t hP ht
    have hy' : |y| < δy := abs_lt.mpr hP.2
    have hxr := abs_lt.mp (hxρ x hP.1)
    have har := abs_lt.mp (hα y hy')
    have hconv := (convex_Ioo (-ρ) ρ)
      (show a (y ^ 2) ∈ Set.Ioo (-ρ) ρ from ⟨har.1, har.2⟩)
      (show x + 4 ∈ Set.Ioo (-ρ) ρ from ⟨hxr.1, hxr.2⟩)
      (sub_nonneg.2 ht.2) ht.1 (by ring)
    simp only [smul_eq_mul] at hconv
    have e : (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2)))) + 4
        = (1 - t) * a (y ^ 2) + t * (x + 4) := by ring
    rw [e]
    exact abs_lt.mpr ⟨hconv.1, hconv.2⟩
  have hPU : ∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
      t ∈ Set.Icc (0 : ℝ) 1 → ((x, y), t) ∈ patchU_FIN06831 a δz := by
    intro x y t hP ht
    have hy' : |y| < δy := abs_lt.mpr hP.2
    have hz2 := (hyprop y hy').2.1
    refine ⟨?_, hseg0 x y t (hP0 x y hP) ht⟩
    exact ⟨by nlinarith [sq_nonneg y], hz2⟩
  refine ⟨δx, δy, hδx, hδy, ?_, ?_, ?_⟩
  · intro x y t hP ht
    exact hseg0 x y t (hP0 x y hP) ht
  · intro x y hP
    exact hcrit0 x y (hP0 x y hP)
  refine ⟨fun p : ℝ × ℝ => 2 * ∫ t in (0 : ℝ)..1, (1 - t) *
    deriv (deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, p.2]))
      (-4 + a (p.2 ^ 2) + t * (p.1 - (-4 + a (p.2 ^ 2)))), fun p => rfl, ?_, ?_, ?_, ?_⟩
  · exact a2_smooth_FIN06831 h1 hPU
  · have key : ∀ t : ℝ, (1 - t) * ddxPsi_FIN06831
        (-4 + a ((0 : ℝ) ^ 2) + t * ((-4 : ℝ) - (-4 + a ((0 : ℝ) ^ 2)))) 0 =
        (1 - t) * quarticA_FIN06803 := by
      intro t
      have e0 : a ((0 : ℝ) ^ 2) = 0 := by
        rw [show ((0 : ℝ) ^ 2) = 0 by norm_num]
        exact h2
      rw [e0]
      have e1 : (-4 : ℝ) + 0 + t * ((-4 : ℝ) - (-4 + 0)) = -4 := by ring
      rw [e1, ddxPsi_base_FIN06831]
    show 2 * ∫ t in (0 : ℝ)..1, (1 - t) * ddxPsi_FIN06831
        (-4 + a ((0 : ℝ) ^ 2) + t * ((-4 : ℝ) - (-4 + a ((0 : ℝ) ^ 2)))) 0 = _
    rw [intervalIntegral.integral_congr (fun t _ => key t), integral_weight_const_FIN06831]
    ring
  · intro x y hP
    have hy' : |y| < δy := abs_lt.mpr hP.2
    obtain ⟨-, -, hyρ, -, hy1⟩ := hyprop y hy'
    have hsegR : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        -4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2))) ∈ Set.Ioo (-5 : ℝ) (-3) :=
      fun t ht => (hseg0 x y t (hP0 x y hP) ht).1
    have hb := fun t (ht : t ∈ Set.Icc (0 : ℝ) 1) =>
      hG (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2)))) y
        (lt_of_lt_of_le (hsegG x y t hP ht) hρr) (lt_of_lt_of_le hyρ hρr)
    exact a2_bounds_FIN06831 hy1 hsegR (fun t ht => (hb t ht).1) (fun t ht => (hb t ht).2)
  · intro x y hP
    dsimp only
    rw [hfac0 x y (hP0 x y hP)]
    ring

end DGPS.Frontier.FIN068
