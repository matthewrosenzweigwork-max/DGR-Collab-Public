import DGPS.Frontier.FIN068.T04
import DGPS.Frontier.FIN068.T24

/-!
Task id and title: FIN068.27, Segment stays in a common smooth patch (module
`DGPS.Frontier.FIN068.T27`).

Provides:
* `DGPS.Frontier.FIN068.fin068_27_segment_stays_common_smooth_patch`: there are `δu, δz > 0` and a
  curve `a` with the critical-curve data of FIN068.24 (`C^∞` on `Set.Ioo (-δz) δz`, `a 0 = 0`, the
  critical equation for `J_u` and uniqueness of its zero in the window), and there are `δx, δy > 0`
  such that, for `x₀ y = -4 + a (y^2)`: the fixed rectangle `R = (-5,-3) × (-1,1)` is relatively
  compact, the named potential `ψ` is `C^∞` on `R` (as a function of the pair `(x, y)`), for
  `(x, y)` in the open rectangle `P = (-4-δx, -4+δx) × (-δy, δy)` and `t ∈ [0,1]` the point
  `(x₀ y + t (x - x₀ y), y)` lies in `R`, and the integrand `2 (1 - t) ψ_xx(x₀ y + t (x - x₀ y), y)`
  of `a₂` is `C^∞` jointly in `((x, y), t)` on an open set `U` containing `P ×ˢ Icc 0 1`.
* Helper declarations, all with suffix `_FIN06827` (not part of the interface):
  `slice_FIN06827` (the first-variable partial derivative of a `C^∞` function on an open set is
  `C^∞` and is the slice derivative), `psi_smooth_FIN06827` (`ψ` is `C^∞` on `R`, from FIN068.04),
  `ddx_FIN06827` (the slice second derivative of `ψ` equals the second partial derivative on `R`),
  `Fmap_FIN06827` (the segment point map `((x, y), t) ↦ (x₀ y + t (x - x₀ y), y)`).

Proof: the curve and its continuity at `0` give a `y`-radius on which `x₀ y` is within `1/2` of
`-4`; the convex combination of two points within `1/2` of `-4` stays within `1/2` of `-4`, so the
segment lies in `R`. Smoothness of `ψ` on `R` is FIN068.04's identity `ψ(-4 + u, y) = J(u, y^2)`
composed with a smooth map. The slice derivatives of `ψ` are first partial derivatives of `ψ` on
the open set `R`, and the integrand is a smooth composition on the open set `U`.

R5 notes:
* No hypothesis is added. The curve conjuncts (`C^∞`, `a 0 = 0`, critical equation, uniqueness)
  are those of FIN068.24, which is the curve `x₀` of FIN068.23; they are carried unchanged, so the
  `a` in this statement is the FIN068.24 curve (the existential is over the curve satisfying those
  characterizing properties, and the proof takes it from FIN068.24).
* The fixed rectangle is `R = Set.Ioo (-5) (-3) ×ˢ Set.Ioo (-1) 1`, with `x`-interval `|x + 4| < 1`
  and `y`-interval `|y| < 1`. The rectangle `P` has `x`-half-width `δx` and `y`-radius `δy`, both
  existentially chosen (the proof uses `δx = 1/2`). `P` is an open rectangle about `(-4, 0)`.
  "Relatively compact" is stated as `IsCompact (closure R)`.
* "`ψ` is smooth on `R`": `ψ` is read as the function of the pair `(x, y)`,
  `quarticPsi_FIN066 !₂[x, y]`, and smooth means real `C^∞` (`ContDiffOn ℝ ∞`). The proof uses
  FIN068.04 part 2, which identifies `ψ(-4 + u, y)` with `J(u, y^2)` for `|u| < 1`, `y^2 < 1`; so
  smoothness depends on FIN068.04 and, through it, on the FIN068.37 and FIN068.38 identifications.
  This dependency is inherited, not repaired here.
* `ψ_xx` is read as the second derivative in the first coordinate of the slice `s ↦ ψ(s, y)`,
  `deriv (deriv (fun s => quarticPsi_FIN066 !₂[s, y])) p`, as in FIN068.11. The integrand is
  `2 (1 - t) ψ_xx(x₀ y + t (x - x₀ y), y)` exactly as written in FIN068.11 (with the factor `2` and
  the weight `1 - t`); the integral itself and its evaluation belong to FIN068.28 and FIN068.29.
* The specification asks for joint continuity of every parameter derivative on compact
  subrectangles of `P` times `[0, 1]`. The proof gives the stronger statement: the integrand is
  `C^∞` jointly in `((x, y), t)` on an open set `U` containing `P ×ˢ Icc 0 1`. This implies joint
  continuity of every iterated derivative on `P ×ˢ Icc 0 1` and on every compact subset of it,
  and it is the form the later integral tasks need. The domain `U` is chosen in the proof
  (`y^2 ∈ (-δz, δz)` and the segment point in `R`), so the domain restrictions are owned here.
* The domain restriction `y^2 ∈ (-δz, δz)` is the one of FIN068.24, so that `x₀ y = -4 + a (y^2)`
  is `C^∞`; the proof chooses `δy` below `δz` in the square, and below `1`.
* The name `fin068_27_segment_stays_common_smooth_patch` is the main declaration.
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff Topology

namespace DGPS.Frontier.FIN068

/-- The first-variable slice derivative of a `C^∞` function on an open set: its derivative in the
first variable is `fderiv f (u, z) (1, 0)`, and that function is again `C^∞` on the set. -/
lemma slice_FIN06827 {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ f q (1, 0)) U ∧
      ∀ u z : ℝ, (u, z) ∈ U → HasDerivAt (fun s : ℝ => f (s, z)) (fderiv ℝ f (u, z) (1, 0)) u := by
  refine ⟨?_, ?_⟩
  · have h1 : ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => fderiv ℝ f q) U :=
      hf.fderiv_of_isOpen hU (by simp)
    exact h1.clm_apply contDiffOn_const
  · intro u z hz
    have hd : DifferentiableAt ℝ f (u, z) :=
      (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hz)
    have hg : HasDerivAt (fun s : ℝ => (s, z)) ((1 : ℝ), (0 : ℝ)) u :=
      (hasDerivAt_id u).prodMk (hasDerivAt_const u z)
    exact hd.hasFDerivAt.comp_hasDerivAt u hg

/-- `ψ(x, y) = quarticPsi_FIN066 !₂[x, y]` is `C^∞` on the fixed rectangle `R`, since
`ψ(-4 + u, y) = J(u, y^2)` there (FIN068.04) with `J` smooth on `(-1, 1)²`. -/
lemma psi_smooth_FIN06827 :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => quarticPsi_FIN066 !₂[p.1, p.2])
      (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) := by
  have hJ := fin068_04_lift_two_ordinary_variables.1
  have hmap : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.1 + 4, p.2 ^ 2))
      (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1 + 4, p.2 ^ 2))).contDiffOn
  have hcomp := hJ.comp hmap (by
    intro p hp
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    dsimp only
    exact Set.mk_mem_prod ⟨by linarith, by linarith⟩ ⟨by nlinarith, by nlinarith⟩)
  refine hcomp.congr ?_
  intro p hp
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  have key := fin068_04_lift_two_ordinary_variables.2 (p.1 + 4) p.2
    (abs_lt.mpr ⟨by linarith, by linarith⟩) (by nlinarith)
  rw [show -4 + (p.1 + 4) = p.1 by ring] at key
  exact key

/-- The slice second derivative of `ψ` on `R` is the second partial derivative of `ψ` in the first
variable, as a function of the pair `(p, y)`. -/
lemma ddx_FIN06827 {p y : ℝ} (hp : (p, y) ∈ Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) :
    deriv (deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, y])) p =
      fderiv ℝ (fun r : ℝ × ℝ => fderiv ℝ
        (fun q : ℝ × ℝ => quarticPsi_FIN066 !₂[q.1, q.2]) r (1, 0)) (p, y) (1, 0) := by
  have hRo : IsOpen (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    isOpen_Ioo.prod isOpen_Ioo
  obtain ⟨hD1, hs1⟩ := slice_FIN06827 hRo psi_smooth_FIN06827
  obtain ⟨-, hs2⟩ := slice_FIN06827 hRo hD1
  have hopen : IsOpen {s : ℝ | (s, y) ∈ Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1} :=
    hRo.preimage (by fun_prop)
  have heq : deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, y]) =ᶠ[𝓝 p]
      (fun s : ℝ => fderiv ℝ (fun q : ℝ × ℝ => quarticPsi_FIN066 !₂[q.1, q.2]) (s, y) (1, 0)) := by
    filter_upwards [hopen.mem_nhds hp] with s hs
    exact (hs1 s y hs).deriv
  rw [heq.deriv_eq]
  exact (hs2 p y hp).deriv

/-- The segment point `((x, y), t) ↦ (x₀ y + t (x - x₀ y), y)` with `x₀ y = -4 + a (y^2)`. -/
noncomputable def Fmap_FIN06827 (a : ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ × ℝ :=
  (-4 + a (q.1.2 ^ 2) + q.2 * (q.1.1 - (-4 + a (q.1.2 ^ 2))), q.1.2)

/-- Segment stays in a common smooth patch (FIN068.27). -/
theorem fin068_27_segment_stays_common_smooth_patch :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      (∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z) ∧
      ∃ δx δy : ℝ, 0 < δx ∧ 0 < δy ∧
        IsCompact (closure (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1)) ∧
        ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => quarticPsi_FIN066 !₂[p.1, p.2])
          (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) ∧
        (∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          t ∈ Set.Icc (0 : ℝ) 1 →
          (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2))), y) ∈
            Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) ∧
        ∃ U : Set ((ℝ × ℝ) × ℝ), IsOpen U ∧
          (∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            t ∈ Set.Icc (0 : ℝ) 1 → ((x, y), t) ∈ U) ∧
          ContDiffOn ℝ ∞
            (fun q : (ℝ × ℝ) × ℝ => 2 * (1 - q.2) *
              deriv (deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, q.1.2]))
                (-4 + a (q.1.2 ^ 2) + q.2 * (q.1.1 - (-4 + a (q.1.2 ^ 2)))))
            U := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, -⟩ := fin068_24_curve_taylor_bound_composition
  refine ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, ?_⟩
  -- continuity of the curve at `0`
  have hc0 : ContinuousAt a 0 :=
    h1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  obtain ⟨ε, hε, hεa⟩ := Metric.continuousAt_iff.1 hc0 (1 / 2) (by norm_num)
  -- the `y`-radius
  obtain ⟨δy, hδy, hyprop⟩ : ∃ δy : ℝ, 0 < δy ∧ ∀ y : ℝ, |y| < δy →
      y ^ 2 < ε ∧ y ^ 2 < δz ∧ |y| < 1 := by
    refine ⟨min (min ε δz) 1, lt_min (lt_min hε hz) one_pos, fun y hy => ?_⟩
    have hy1 : |y| < 1 := lt_of_lt_of_le hy (min_le_right _ _)
    have hy2 : |y| < min ε δz := lt_of_lt_of_le hy (min_le_left _ _)
    have hsq : y ^ 2 ≤ |y| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg y, mul_nonneg (abs_nonneg y) (sub_nonneg.2 hy1.le)]
    refine ⟨?_, ?_, hy1⟩
    · exact lt_of_le_of_lt hsq (lt_of_lt_of_le hy2 (min_le_left _ _))
    · exact lt_of_le_of_lt hsq (lt_of_lt_of_le hy2 (min_le_right _ _))
  -- the curve stays within `1/2` of `-4` on the `y`-radius
  have hα : ∀ y : ℝ, |y| < δy → -(1 / 2 : ℝ) < a (y ^ 2) ∧ a (y ^ 2) < 1 / 2 := by
    intro y hy
    have hd : dist (y ^ 2) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg y)]
      exact (hyprop y hy).1
    have := hεa hd
    rw [Real.dist_eq, h2, sub_zero] at this
    exact abs_lt.mp this
  -- the segment stays in `R`
  have hmemR : ∀ x y t : ℝ, x ∈ Set.Ioo (-4 - (1 / 2 : ℝ)) (-4 + 1 / 2) → |y| < δy →
      t ∈ Set.Icc (0 : ℝ) 1 →
      (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2))), y) ∈
        Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    intro x y t hx hy ht
    obtain ⟨hα1, hα2⟩ := hα y hy
    obtain ⟨hx1, hx2⟩ := hx
    have hconv := (convex_Ioo (-(1 / 2 : ℝ)) (1 / 2))
      (show a (y ^ 2) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) from ⟨hα1, hα2⟩)
      (show x + 4 ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) from ⟨by linarith, by linarith⟩)
      (sub_nonneg.2 ht.2) ht.1 (by ring)
    simp only [smul_eq_mul] at hconv
    obtain ⟨hc1, hc2⟩ := hconv
    have e : -4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2)))
        = -4 + ((1 - t) * a (y ^ 2) + t * (x + 4)) := by ring
    rw [e]
    exact Set.mk_mem_prod ⟨by linarith, by linarith⟩ (abs_lt.mp (hyprop y hy).2.2)
  -- the patch: `P = (-4 - 1/2, -4 + 1/2) × (-δy, δy)`
  have hmemPR : ∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - (1 / 2 : ℝ)) (-4 + 1 / 2) ×ˢ Set.Ioo (-δy) δy →
      t ∈ Set.Icc (0 : ℝ) 1 →
      (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2))), y) ∈
        Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    intro x y t hP ht
    obtain ⟨hx, hy⟩ := hP
    exact hmemR x y t hx (abs_lt.mpr hy) ht
  have hRo : IsOpen (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    isOpen_Ioo.prod isOpen_Ioo
  have hcpt : IsCompact (closure (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
    rw [closure_prod_eq, closure_Ioo (show (-5 : ℝ) ≠ -3 by norm_num),
      closure_Ioo (show (-1 : ℝ) ≠ 1 by norm_num)]
    exact isCompact_Icc.prod isCompact_Icc
  -- the open set `U`
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
  have hUo : IsOpen ({q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} ∩
      Fmap_FIN06827 a ⁻¹' (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1)) :=
    hFc.continuousOn.isOpen_inter_preimage hS0o hRo
  have hPU : ∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - (1 / 2 : ℝ)) (-4 + 1 / 2) ×ˢ Set.Ioo (-δy) δy →
      t ∈ Set.Icc (0 : ℝ) 1 →
      ((x, y), t) ∈ {q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} ∩
        Fmap_FIN06827 a ⁻¹' (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) := by
    intro x y t hP ht
    obtain ⟨hx, hy⟩ := hP
    have hy' : |y| < δy := abs_lt.mpr hy
    have hyy : y ^ 2 ∈ Set.Ioo (-δz) δz :=
      ⟨by nlinarith [sq_nonneg y], (hyprop y hy').2.1⟩
    exact ⟨hyy, hmemR x y t hx hy' ht⟩
  -- smoothness of the integrand on `U`
  obtain ⟨hD1, -⟩ := slice_FIN06827 hRo psi_smooth_FIN06827
  obtain ⟨hD2, -⟩ := slice_FIN06827 hRo hD1
  have hFU : ContDiffOn ℝ ∞ (Fmap_FIN06827 a)
      ({q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} ∩
        Fmap_FIN06827 a ⁻¹' (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1)) :=
    hFc.mono Set.inter_subset_left
  have hcomp : ContDiffOn ℝ ∞
      (fun q : (ℝ × ℝ) × ℝ => fderiv ℝ (fun r : ℝ × ℝ => fderiv ℝ
        (fun p : ℝ × ℝ => quarticPsi_FIN066 !₂[p.1, p.2]) r (1, 0)) (Fmap_FIN06827 a q) (1, 0))
      ({q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} ∩
        Fmap_FIN06827 a ⁻¹' (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1)) :=
    hD2.comp hFU (fun q hq => hq.2)
  have hc1 : ContDiffOn ℝ ∞ (fun q : (ℝ × ℝ) × ℝ => 2 * (1 - q.2))
      ({q : (ℝ × ℝ) × ℝ | q.1.2 ^ 2 ∈ Set.Ioo (-δz) δz} ∩
        Fmap_FIN06827 a ⁻¹' (Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1)) :=
    contDiffOn_const.mul (contDiffOn_const.sub (htq.mono Set.inter_subset_left))
  refine ⟨1 / 2, δy, by norm_num, hδy, hcpt, psi_smooth_FIN06827, hmemPR, _, hUo, hPU, ?_⟩
  refine (hc1.mul hcomp).congr ?_
  intro q hq
  have hd := ddx_FIN06827 (p := -4 + a (q.1.2 ^ 2) + q.2 * (q.1.1 - (-4 + a (q.1.2 ^ 2))))
    (y := q.1.2) hq.2
  exact congrArg (fun z : ℝ => 2 * (1 - q.2) * z) hd

end DGPS.Frontier.FIN068
