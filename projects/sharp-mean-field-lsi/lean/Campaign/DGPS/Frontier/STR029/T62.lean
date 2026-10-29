import DGPS.Frontier.STR029.T01
import DGPS.Frontier.STR029.T16
import DGPS.Frontier.STR029.T34
import DGPS.Frontier.STR029.T50
import DGPS.Frontier.STR029.T53

/-!
# STR029.62: A global optimizer in a positive chart is fully critical

Task id: STR029.62. Title: A global optimizer in a positive chart is fully critical.

Frozen statement: if a positive-entropy global optimizer has the positive `C^{2,α}` logarithmic
representation supplied by `.01`, and `r = I_h/(2H_h)`, then `D_u J(h, r - 1, u)[v] = 0` for every
mean-zero `C^{2,α}` direction `v`. Its full `G` vanishes; in the IFT neighborhood its
complementary component equals `ψ`.

Proof route of this file. The chart function `u = a cos + b sin + w` of `.01` gives the angular
competitor `gLift h (u + s v) = exp((u + s v - log Z + log Z_h)/2)` of the same family. It lies in
the angular admissible domain, its angular entropy is the chart entropy and its angular Fisher
information is the chart Fisher information. By the a.e. representation, `gAng h ρ` is a.e. equal to
`gLift h u`, and the angular quotient is invariant under a.e. changes. Global optimality of `ρ` is
transferred to the angular problem (`optimizer_transfer_STR02901`), and the positive entropy of
the competitor for small `s` follows from continuity of the chart entropy along the curve.
The scalar Fermat rule then gives `∫ G v dm = 0` for each mean-zero `C^{2,1/2}` direction, Fourier
completeness (STR029.34) gives `G = 0` in `L²`, and continuity gives `G ≡ 0` pointwise. Then
`P G = 0` is the vanishing of the variational range map, and STR029.16 identifies the
complementary component. No identity with an upstream projected Euler map is used.

## Provides

* `DGPS.Frontier.STR029.str029_62_global_optimizer_positive_chart_fully_critical`: the main
  statement. For an `AbsoluteDensity 1` of positive entropy that minimizes `I/(2H)` among positive
  entropy absolute densities, with the angular a.e. representation `ρ = ρ(h, a cos + b sin + w)`,
  `w ∈ C^{2,1/2} ∩ E`, and `r = I/(2H)` in angular units: (1) the Gateaux derivative of
  `s ↦ J(h, r - 1, u + s v)` at `0` is `0` for every mean-zero `C^{2,1/2}` direction `v`;
  (2) `G(h, r - 1, u)` vanishes at every point; (3) the element `wE` of `E` with value `w` is a zero
  of the variational range map at `(a, b, h, r - 1)`, and `wE = ψ (a, b, h, r - 1)` for every
  graph triple `(U, V, ψ)` of the shape of STR029.16 whose `U` contains the point and `V` contains
  `wE`.
* `DGPS.Frontier.STR029.cosFreq_isC2_STR02962`: `cos (k t)` is periodic and `C^{2,1/2}`.
* `DGPS.Frontier.STR029.sinFreq_isC2_STR02962`: `sin (k t)` is periodic and `C^{2,1/2}`.
* `DGPS.Frontier.STR029.fermat_STR02962`: a local minimum of `s ↦ J(h, γ, u + s v)` at `0` forces
  `∫ G v dm = 0` (scalar Fermat rule with the first variation of STR029.50).
* `DGPS.Frontier.STR029.localMin_of_quot_STR02962`: real algebra: if `F(s)/(2H(s))` is not below its
  value at `0` near `0`, then `F - 2 r H` with `r = F(0)/(2H(0))` has a local minimum at `0`.
* `DGPS.Frontier.STR029.localMin_Jchart_of_quot_STR02962`: the same, for the chart functional
  `J(h, r - 1, ·)` with `r = I(u)/(2H(u))`.
* `DGPS.Frontier.STR029.periodic_deriv_STR02962`: the derivative of a periodic function is periodic.
* `DGPS.Frontier.STR029.continuous_gradG_STR02962`: `G` is continuous for `C^{2,1/2}` `u`.
* `DGPS.Frontier.STR029.periodic_gradG_STR02962`: `G` is `2π`-periodic for `C^{2,1/2}` `u`.
* `DGPS.Frontier.STR029.meanT_const_mul_STR02962`: the normalized mean is homogeneous.
* `DGPS.Frontier.STR029.normInt_eq_meanT_STR02962`: the normalized integral of STR029.34 is the
  normalized mean of STR029.01.
* `DGPS.Frontier.STR029.meanT_cos_STR02962`, `DGPS.Frontier.STR029.meanT_sin_STR02962`: the
  normalized means of `cos (n t)` and `sin (n t)` vanish for `n ≠ 0`.
* `DGPS.Frontier.STR029.ae_circle_iff_STR02962`: a.e. statements on the circle measure reduce to
  `volume.restrict (Ioc 0 (2π))`.
* `DGPS.Frontier.STR029.gradG_zero_of_tests_STR02962`: if `∫ G v dm = 0` for every mean-zero
  `C^{2,1/2}` direction `v`, then `G ≡ 0` pointwise (Fourier completeness of STR029.34, then
  continuity of `G`).
* `DGPS.Frontier.STR029.quot_step_fully_critical_STR02962`: helper, not the specification
  statement. If `u` is `C^{2,1/2}` with positive chart entropy, and along every mean-zero direction
  the quotient `I/(2H)` is not decreased near `s = 0` with positive entropy there (hypothesis
  `hquot`), then with `r = I(u)/(2H(u))`: `D_u J(h, r - 1, u)[v] = 0` for every mean-zero
  direction `v`, and `G(h, r - 1, u) ≡ 0`. The main statement discharges `hquot`.
* `DGPS.Frontier.STR029.angSec_mem_STR02962`: `angSec θ ∈ [0, 2π]` on the angular circle.
* `DGPS.Frontier.STR029.coe_angSec_STR02962`: the real representative `angSec θ` projects back to `θ`.
* `DGPS.Frontier.STR029.integral_angSec_STR02962`: pushforward of the normalized angular Haar
  integral to `(2π)⁻¹ ∫_0^{2π}`.
* `DGPS.Frontier.STR029.integral_ibp_periodic_STR02962`: integration by parts over one period for
  periodic `f`, `g` with continuous derivatives.
* `DGPS.Frontier.STR029.isAngularWeakDeriv_lift_STR02962`: a periodic `f` with continuous
  derivative `f'` gives `IsAngularWeakDeriv (f ∘ angSec) (f' ∘ angSec)` (smooth-to-weak step).
* `DGPS.Frontier.STR029.qAng_eq_qT_STR02962`: the angular reference density is `q_h ∘ angSec`.
* `DGPS.Frontier.STR029.logZ_STR02962`, `DGPS.Frontier.STR029.logZh_STR02962`: the logarithms of
  the normalizing means of `exp(h cos 3t + u)` and `exp(h cos 3t)`.
* `DGPS.Frontier.STR029.gLift_STR02962`: the angular square root `exp((u - log Z + log Z_h)/2)`
  of the chart density, on the circle through `angSec`.
* `DGPS.Frontier.STR029.gLift_sq_STR02962`: `gLift² q_h = ρ(h, u) ∘ angSec` for continuous `u`.
* `DGPS.Frontier.STR029.measurable_angSec_STR02962`: `angSec` is measurable.
* `DGPS.Frontier.STR029.integrable_comp_angSec_STR02962`: continuous functions composed with
  `angSec` are integrable for the angular Haar measure.
* `DGPS.Frontier.STR029.meanT_nonneg_STR02962`: the normalized mean of a nonnegative function is
  nonnegative.
* `DGPS.Frontier.STR029.isAngularWeakDeriv_gLift_STR02962`: `gLift` has the weak derivative
  `gLift · u' / 2` for `C^{2,1/2}` `u`.
* `DGPS.Frontier.STR029.angDomain_gLift_STR02962`: `gLift h u` lies in the angular admissible
  domain (`H¹`, nonnegative, mass one).
* `DGPS.Frontier.STR029.angEntropy_gLift_STR02962`: the angular entropy of `gLift h u` is the chart
  entropy.
* `DGPS.Frontier.STR029.fisherChart_nonneg_STR02962`: the chart Fisher information is nonnegative.
* `DGPS.Frontier.STR029.angFisher_gLift_STR02962`: the angular Fisher information of `gLift h u` is
  `ofReal` of the chart Fisher information.
* `DGPS.Frontier.STR029.isAngularWeakDeriv_congr_STR02962`: weak derivatives are invariant under
  a.e. changes of the function.
* `DGPS.Frontier.STR029.angFisher_congr_STR02962`, `DGPS.Frontier.STR029.angEntropy_congr_STR02962`:
  the angular Fisher information and entropy are invariant under a.e. changes.
* `DGPS.Frontier.STR029.gAng_ae_eq_gLift_STR02962`: the a.e. representation of the density gives
  `gAng h ρ =ᵐ gLift h u`.
* `DGPS.Frontier.STR029.uT_isC2_STR02962`: `a cos + b sin + w` is `C^{2,1/2}` for `C^{2,1/2}` `w`.
* `DGPS.Frontier.STR029.isC2_add_smul_STR02962`: `u + s v` is `C^{2,1/2}` for `C^{2,1/2}` `u`, `v`.
* `DGPS.Frontier.STR029.ofReal_quot_STR02962`: `ofReal a / (2 ofReal b) = ofReal (a/(2b))` for
  `b > 0`.
* `DGPS.Frontier.STR029.hquot_of_angular_min_STR02962`: angular quotient minimality of `g0 =ᵐ gLift h u`
  gives the hypothesis `hquot` of `quot_step_fully_critical_STR02962` (eventual positivity of the
  entropy and quotient inequality along every `C^{2,1/2}` direction).
* `DGPS.Frontier.STR029.Rpar_eq_zero_of_gradG_zero_STR02962`: if `G` vanishes pointwise at
  `a cos + b sin + w`, the variational range map vanishes at `(a, b, h, γ, w)` (T15 pointwise
  formula for the range map).

## R5 notes

* Hölder exponent. `α = 1/2` throughout, as fixed in the node preamble and in all prerequisites
  (`IsC2Alpha_STR02901 (1/2)`, `E_STR02969`, `Rpar_STR02916`). General `α` is not formalized.
* Parameter `h`. Any real `h` is allowed; no smallness of `h` is used.
* Global optimizer. `hpos : 0 < ordinaryEntropy h ρ` and `hmin`, the minimality of
  `ordinaryFisher/(2 ordinaryEntropy)` (in `ℝ≥0∞`, the compiled `str025_quot`) over all positive
  entropy `ρ' : AbsoluteDensity 1`, exactly the hypotheses of the gate theorem of STR029.01. The
  global minimality is used only through `optimizer_transfer_STR02901` to the angular problem.
* Representation of `.01`. The "positive `C^{2,α}` logarithmic representation" is read as the data
  `a b : ℝ`, `w : ℝ → ℝ` with `IsC2Alpha_STR02901 (1/2) w`, `InE_STR02901 w`, and the angular a.e.
  identity of STR029.01: for `angHaar`-a.e. `θ`,
  `ρ.density (angEquiv.symm θ) = rhoT_STR02901 h (uT_STR02901 a b w) (angSec θ)`. The identity is
  a.e. because STR029.01 identifies densities up to null sets, and the chart function is
  `u = a cos + b sin + w`. It is a hypothesis for a single `ρ`; STR029.01 supplies it for
  sequences of optimizers, eventually. `InE_STR02901 w` is used only for the element `wE` of `E` in
  the third conclusion; the first two conclusions use only `IsC2Alpha_STR02901 (1/2) w`.
* The Haar mean of `u` is not assumed to vanish (it does for `w ∈ E`); only `w ∈ E` is used.
* The rate `r`. `hr : r = I/(2H)` with `I = (angFisher_STR02901 h (gAng_STR02901 h ρ)).toReal` and
  `H = angEntropy_STR02901 h (gAng_STR02901 h ρ)`: angular units for `m(dt) = dt/(2π)`, the units of
  `J` in STR029.50 and of the rate coordinate `p₃ = I/(2H) - 1` of STR029.01. The physical quotient
  is `4π²` times this (`str025_quot_toReal_STR02901`). Since `ρ` has positive entropy, `H > 0`,
  and `I` is finite.
* Directional derivative. `D_u J(h, r - 1, u)[v] = 0` is the Gateaux statement
  `HasDerivAt (fun s => Jchart_STR02950 h (r - 1) (u + s v)) 0 0`, as in STR029.49 and STR029.50.
  No Fréchet derivative on a bundled `C^{2,α}` space is claimed. A mean-zero direction is
  `v` with `IsC2Alpha_STR02901 (1/2) v` and `meanT_STR02901 v = 0`. `J(h, γ, u)` is
  `fisherChart - 2 (1 + γ) entropyChart` (`Jchart_STR02950`), the chart form of STR029.50.
* "Its full `G` vanishes". `G = gradG_STR02950 h (r - 1) u` for `u = uT_STR02901 a b w`, the
  full normalized variational gradient (not `P G`), vanishing at every real `t` (pointwise, from
  `L²` vanishing and continuity), not only almost everywhere.
* "In the IFT neighborhood its complementary component equals `ψ`". The complementary component of
  `u` in the chart `(a, b, h, γ, w)` is the element `wE : E_STR02969` with value `w`. The third
  conclusion has two parts. First, `Rpar_STR02916 (a, b, h, r - 1) wE = 0`, from `G ≡ 0` and the
  T15 pointwise formula `R = P G`. Second, for every `(U, V, ψ)` with the graph property
  `∀ p ∈ U, ∀ w' ∈ V, Rpar p w' = 0 ↔ w' = ψ p` (the property delivered by
  `str029_16_unique_smooth_range_graph`), if `(a, b, h, r - 1) ∈ U` and `wE ∈ V` then
  `wE = ψ (a, b, h, r - 1)`. The memberships are premises: whether the optimizer lies in the
  neighborhood is the localization of STR029.01 and is not asserted here. The neighborhood is
  quantified over all graph triples, so the triple of STR029.16 is a special case.
* Proof route. The specification tests against every nonconstant sine and cosine and obtains the
  constant coefficient from STR029.12. Here the statement `∫ G v dm = 0` is obtained for every
  mean-zero `C^{2,1/2}` direction at once and `gradG_zero_of_tests_STR02962` applies Fourier
  completeness; the constant coefficient comes from the mean identity of STR029.50
  (`meanT (G · 1) = 0`), which is the content of the STR029.12 normalization used there. Positivity of
  `ρ(h, u + s v)` is automatic for continuous `u + s v` (`rhoT_pos_STR02901`); the competitor is
  placed in the angular domain by the identities above, and the entropy stays positive for small
  `s` by continuity of `s ↦ entropyChart (u + s v)` (STR029.49).
* The conditional helper `quot_step_fully_critical_STR02962` keeps its extra hypothesis `hquot`; the
  main statement does not carry it, since `hquot` is proved from global optimality in
  `hquot_of_angular_min_STR02962`.
* Axioms of the main statement: `propext`, `Classical.choice`, `Quot.sound`.
-/

open DGPS.Analysis.PeriodicHolder
open Filter Topology
open MeasureTheory Set
open DGPS.Circle.AngularNormalization
open scoped ENNReal
open DGPS DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Frontier.STR029

theorem cosFreq_isC2_STR02962 (k : ℕ) :
    IsC2Alpha_STR02901 (1 / 2) (fun t => Real.cos ((k : ℝ) * t)) := by
  have hper : Function.Periodic (fun t => Real.cos ((k : ℝ) * t)) (2 * Real.pi) := by
    intro t
    show Real.cos ((k : ℝ) * (t + 2 * Real.pi)) = Real.cos ((k : ℝ) * t)
    rw [show (k : ℝ) * (t + 2 * Real.pi) = (k : ℝ) * t + (k : ℝ) * (2 * Real.pi) by ring,
      Real.cos_add_nat_mul_two_pi]
  have hd1 : deriv (fun t => Real.cos ((k : ℝ) * t)) =
      fun t => -((k : ℝ) * Real.sin ((k : ℝ) * t)) := by
    funext t
    have h : HasDerivAt (fun t => Real.cos ((k : ℝ) * t))
        (-Real.sin ((k : ℝ) * t) * ((k : ℝ) * 1)) t :=
      ((hasDerivAt_id' t).const_mul (k : ℝ)).cos
    rw [h.deriv]; ring
  have hdd : deriv (deriv (fun t => Real.cos ((k : ℝ) * t))) =
      fun t => -((k : ℝ) ^ 2 * Real.cos ((k : ℝ) * t)) := by
    rw [hd1]; funext t
    have h : HasDerivAt (fun t => -((k : ℝ) * Real.sin ((k : ℝ) * t)))
        (-((k : ℝ) * (Real.cos ((k : ℝ) * t) * ((k : ℝ) * 1)))) t :=
      (((hasDerivAt_id' t).const_mul (k : ℝ)).sin.const_mul (k : ℝ)).neg
    rw [h.deriv]; ring
  have hdiff : Differentiable ℝ (fun t => Real.cos ((k : ℝ) * t)) := by fun_prop
  have hdiff1 : Differentiable ℝ (deriv (fun t => Real.cos ((k : ℝ) * t))) := by
    rw [hd1]; fun_prop
  have hc2 : Continuous (deriv (deriv (fun t => Real.cos ((k : ℝ) * t)))) := by
    rw [hdd]; fun_prop
  have hgper : Function.Periodic (fun t => -((k : ℝ) ^ 2 * Real.cos ((k : ℝ) * t)))
      (2 * Real.pi) := by
    intro t
    show -((k : ℝ) ^ 2 * Real.cos ((k : ℝ) * (t + 2 * Real.pi))) =
      -((k : ℝ) ^ 2 * Real.cos ((k : ℝ) * t))
    rw [show (k : ℝ) * (t + 2 * Real.pi) = (k : ℝ) * t + (k : ℝ) * (2 * Real.pi) by ring,
      Real.cos_add_nat_mul_two_pi]
  have hgd : Differentiable ℝ (fun t => -((k : ℝ) ^ 2 * Real.cos ((k : ℝ) * t))) := by
    fun_prop
  have hg' : deriv (fun t => -((k : ℝ) ^ 2 * Real.cos ((k : ℝ) * t))) =
      fun t => (k : ℝ) ^ 2 * ((k : ℝ) * Real.sin ((k : ℝ) * t)) := by
    funext t
    have h : HasDerivAt (fun t => -((k : ℝ) ^ 2 * Real.cos ((k : ℝ) * t)))
        (-((k : ℝ) ^ 2 * (-Real.sin ((k : ℝ) * t) * ((k : ℝ) * 1)))) t :=
      ((((hasDerivAt_id' t).const_mul (k : ℝ)).cos).const_mul ((k : ℝ) ^ 2)).neg
    rw [h.deriv]; ring
  have hb : Bdd (deriv (fun t => -((k : ℝ) ^ 2 * Real.cos ((k : ℝ) * t)))) := by
    refine ⟨|(k : ℝ) ^ 2 * (k : ℝ)|, fun x => ?_⟩
    simp only [hg']
    rw [show (k : ℝ) ^ 2 * ((k : ℝ) * Real.sin ((k : ℝ) * x)) =
      ((k : ℝ) ^ 2 * (k : ℝ)) * Real.sin ((k : ℝ) * x) by ring, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  obtain ⟨⟨-, h2⟩, -⟩ := c0_of_deriv_STR02953 (α := 1 / 2) (by norm_num) (by norm_num)
    hgper hgd hb
  unfold IsC2Alpha_STR02901
  refine ⟨hper, hdiff, hdiff1, hc2, ?_⟩
  rw [hdd]
  exact h2

theorem sinFreq_isC2_STR02962 (k : ℕ) :
    IsC2Alpha_STR02901 (1 / 2) (fun t => Real.sin ((k : ℝ) * t)) := by
  have hper : Function.Periodic (fun t => Real.sin ((k : ℝ) * t)) (2 * Real.pi) := by
    intro t
    show Real.sin ((k : ℝ) * (t + 2 * Real.pi)) = Real.sin ((k : ℝ) * t)
    rw [show (k : ℝ) * (t + 2 * Real.pi) = (k : ℝ) * t + (k : ℝ) * (2 * Real.pi) by ring,
      Real.sin_add_nat_mul_two_pi]
  have hd1 : deriv (fun t => Real.sin ((k : ℝ) * t)) =
      fun t => (k : ℝ) * Real.cos ((k : ℝ) * t) := by
    funext t
    have h : HasDerivAt (fun t => Real.sin ((k : ℝ) * t))
        (Real.cos ((k : ℝ) * t) * ((k : ℝ) * 1)) t :=
      ((hasDerivAt_id' t).const_mul (k : ℝ)).sin
    rw [h.deriv]; ring
  have hdd : deriv (deriv (fun t => Real.sin ((k : ℝ) * t))) =
      fun t => -((k : ℝ) ^ 2 * Real.sin ((k : ℝ) * t)) := by
    rw [hd1]; funext t
    have h : HasDerivAt (fun t => (k : ℝ) * Real.cos ((k : ℝ) * t))
        ((k : ℝ) * (-Real.sin ((k : ℝ) * t) * ((k : ℝ) * 1))) t :=
      (((hasDerivAt_id' t).const_mul (k : ℝ)).cos.const_mul (k : ℝ))
    rw [h.deriv]; ring
  have hdiff : Differentiable ℝ (fun t => Real.sin ((k : ℝ) * t)) := by fun_prop
  have hdiff1 : Differentiable ℝ (deriv (fun t => Real.sin ((k : ℝ) * t))) := by
    rw [hd1]; fun_prop
  have hc2 : Continuous (deriv (deriv (fun t => Real.sin ((k : ℝ) * t)))) := by
    rw [hdd]; fun_prop
  have hgper : Function.Periodic (fun t => -((k : ℝ) ^ 2 * Real.sin ((k : ℝ) * t)))
      (2 * Real.pi) := by
    intro t
    show -((k : ℝ) ^ 2 * Real.sin ((k : ℝ) * (t + 2 * Real.pi))) =
      -((k : ℝ) ^ 2 * Real.sin ((k : ℝ) * t))
    rw [show (k : ℝ) * (t + 2 * Real.pi) = (k : ℝ) * t + (k : ℝ) * (2 * Real.pi) by ring,
      Real.sin_add_nat_mul_two_pi]
  have hgd : Differentiable ℝ (fun t => -((k : ℝ) ^ 2 * Real.sin ((k : ℝ) * t))) := by
    fun_prop
  have hg' : deriv (fun t => -((k : ℝ) ^ 2 * Real.sin ((k : ℝ) * t))) =
      fun t => -((k : ℝ) ^ 2 * ((k : ℝ) * Real.cos ((k : ℝ) * t))) := by
    funext t
    have h : HasDerivAt (fun t => -((k : ℝ) ^ 2 * Real.sin ((k : ℝ) * t)))
        (-((k : ℝ) ^ 2 * (Real.cos ((k : ℝ) * t) * ((k : ℝ) * 1)))) t :=
      ((((hasDerivAt_id' t).const_mul (k : ℝ)).sin).const_mul ((k : ℝ) ^ 2)).neg
    rw [h.deriv]; ring
  have hb : Bdd (deriv (fun t => -((k : ℝ) ^ 2 * Real.sin ((k : ℝ) * t)))) := by
    refine ⟨|(k : ℝ) ^ 2 * (k : ℝ)|, fun x => ?_⟩
    simp only [hg']
    rw [show -((k : ℝ) ^ 2 * ((k : ℝ) * Real.cos ((k : ℝ) * x))) =
      -((k : ℝ) ^ 2 * (k : ℝ)) * Real.cos ((k : ℝ) * x) by ring, abs_mul]
    rw [abs_neg]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  obtain ⟨⟨-, h2⟩, -⟩ := c0_of_deriv_STR02953 (α := 1 / 2) (by norm_num) (by norm_num)
    hgper hgd hb
  unfold IsC2Alpha_STR02901
  refine ⟨hper, hdiff, hdiff1, hc2, ?_⟩
  rw [hdd]
  exact h2

/-- Fermat step: a local minimum of the directional profile gives vanishing directional derivative. -/
theorem fermat_STR02962 (h γ : ℝ) {u v : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) (hv : IsC2Alpha_STR02901 (1 / 2) v)
    (hmin : IsLocalMin (fun s : ℝ => Jchart_STR02950 h γ (fun t => u t + s * v t)) 0) :
    meanT_STR02901 (fun t => gradG_STR02950 h γ u t * v t) = 0 :=
  hmin.hasDerivAt_eq_zero (str029_50_integrate_variation_compute_mean_variation h γ hu hv)

/-- Real-algebra core of the quotient step: if `F 0 / (2 H 0) ≤ F s / (2 H s)` near `0`, then
`s ↦ F s - 2 r H s` with `r = F 0 / (2 H 0)` has a local minimum at `0`. -/
theorem localMin_of_quot_STR02962 {F H : ℝ → ℝ} {r : ℝ} (hr : r = F 0 / (2 * H 0))
    (hH0 : 0 < H 0) (hH : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < H s)
    (hq : ∀ᶠ s in 𝓝 (0 : ℝ), F 0 / (2 * H 0) ≤ F s / (2 * H s)) :
    IsLocalMin (fun s => F s - 2 * r * H s) 0 := by
  have hF0 : 2 * r * H 0 = F 0 := by rw [hr]; field_simp
  unfold IsLocalMin IsMinFilter
  filter_upwards [hH, hq] with s hs hqs
  have h2 : r * (2 * H s) ≤ F s := by
    rw [hr]; exact (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * H s)).mp hqs
  show F 0 - 2 * r * H 0 ≤ F s - 2 * r * H s
  rw [hF0]; linarith

theorem periodic_deriv_STR02962 {w : ℝ → ℝ} (hw : Function.Periodic w (2 * Real.pi)) :
    Function.Periodic (deriv w) (2 * Real.pi) := by
  intro t
  rw [← deriv_comp_add_const]
  have hfun : (fun x => w (x + 2 * Real.pi)) = w := funext hw
  rw [hfun]

theorem continuous_gradG_STR02962 (h γ : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    Continuous (gradG_STR02950 h γ u) := by
  have hu0 : Continuous u := hu.2.1.continuous
  have hR : Continuous (rhoT_STR02901 h u) := continuous_rho_STR02950 h hu0
  have hd : Continuous (deriv u) := hu.2.2.1.continuous
  have hdd : Continuous (deriv (deriv u)) := hu.2.2.2.1
  unfold gradG_STR02950
  fun_prop

theorem periodic_gradG_STR02962 (h γ : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    Function.Periodic (gradG_STR02950 h γ u) (2 * Real.pi) := by
  have hp : Function.Periodic u (2 * Real.pi) := hu.1
  have hρ := periodic_rho_STR02950 h hp
  have hd := periodic_deriv_STR02962 hp
  have hdd := periodic_deriv_STR02962 hd
  intro t
  unfold gradG_STR02950
  rw [hρ t, hp t, hd t, hdd t,
    show 3 * (t + 2 * Real.pi) = 3 * t + ((3 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring,
    Real.sin_add_nat_mul_two_pi]

theorem meanT_const_mul_STR02962 (a : ℝ) (f : ℝ → ℝ) :
    meanT_STR02901 (fun t => a * f t) = a * meanT_STR02901 f := by
  unfold meanT_STR02901
  rw [intervalIntegral.integral_const_mul]
  ring

theorem normInt_eq_meanT_STR02962 (f : ℝ → ℝ) : normInt_STR02933 f = meanT_STR02901 f := by
  unfold normInt_STR02933 meanT_STR02901
  rw [intervalIntegral.integral_of_le (by positivity)]

theorem meanT_cos_STR02962 {n : ℕ} (hn : n ≠ 0) :
    meanT_STR02901 (fun t => Real.cos ((n : ℝ) * t)) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
    rw [show (n : ℝ) * (2 * Real.pi) = ((2 * n : ℕ) : ℝ) * Real.pi by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  unfold meanT_STR02901
  rw [intervalIntegral.integral_comp_mul_left Real.cos hn', integral_cos, hs]
  simp

theorem meanT_sin_STR02962 {n : ℕ} (hn : n ≠ 0) :
    meanT_STR02901 (fun t => Real.sin ((n : ℝ) * t)) = 0 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hc : Real.cos ((n : ℝ) * (2 * Real.pi)) = 1 := Real.cos_nat_mul_two_pi n
  unfold meanT_STR02901
  rw [intervalIntegral.integral_comp_mul_left Real.sin hn', integral_sin, hc]
  simp

theorem ae_circle_iff_STR02962 {P : ℝ → Prop} :
    (∀ᵐ t ∂circleMeasure_STR02934, P t) ↔
      ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))), P t := by
  have hc : ENNReal.ofReal (2 * Real.pi)⁻¹ ≠ 0 :=
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  unfold circleMeasure_STR02934
  exact Measure.ae_ennreal_smul_measure_iff hc

/-- Fourier step: if the directional test identities hold for every mean-zero `C^{2,1/2}`
direction, then `G` vanishes pointwise. -/
theorem gradG_zero_of_tests_STR02962 (h γ : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (htest : ∀ v : ℝ → ℝ, IsC2Alpha_STR02901 (1 / 2) v → meanT_STR02901 v = 0 →
      meanT_STR02901 (fun t => gradG_STR02950 h γ u t * v t) = 0) :
    ∀ t : ℝ, gradG_STR02950 h γ u t = 0 := by
  have hGc : Continuous (gradG_STR02950 h γ u) := continuous_gradG_STR02962 h γ hu
  have hGp : Function.Periodic (gradG_STR02950 h γ u) (2 * Real.pi) :=
    periodic_gradG_STR02962 h γ hu
  set G := gradG_STR02950 h γ u with hGdef
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hGc.continuousOn
  have hbound : ∀ᵐ t ∂circleMeasure_STR02934, ‖G t‖ ≤ C := by
    rw [ae_circle_iff_STR02962]
    exact ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht => hC t ⟨ht.1.le, ht.2⟩)
  have hGL : MemLp G 2 circleMeasure_STR02934 :=
    MemLp.of_bound hGc.aestronglyMeasurable C hbound
  set x : Lp ℝ 2 circleMeasure_STR02934 := MemLp.toLp G hGL with hxdef
  have hx_ae : ⇑x =ᵐ[circleMeasure_STR02934] G := MemLp.coeFn_toLp hGL
  have hx_restrict : ⇑x =ᵐ[volume.restrict (Set.Ioc 0 (2 * Real.pi))] G :=
    (ae_circle_iff_STR02962 (P := fun t => x t = G t)).mp hx_ae
  have hperp : ∀ i, inner ℝ (trigBasisLp_STR02934 i) x = (0 : ℝ) := by
    intro i
    rw [inner_trigBasisLp_STR02934]
    have hcongr : normInt_STR02933 (fun t => x t * trigBasisFun_STR02934 i t) =
        meanT_STR02901 (fun t => G t * trigBasisFun_STR02934 i t) := by
      rw [← normInt_eq_meanT_STR02962]
      unfold normInt_STR02933
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hx_restrict] with t ht
      simp only [ht]
    rw [hcongr]
    rcases i with _ | ⟨b, k⟩
    · simp only [trigBasisFun_STR02934, mul_one]
      exact str029_50_integrate_variation_compute_mean_mean_zero h γ hu
    · cases b
      · have hf : (fun t => G t * trigBasisFun_STR02934 (some (false, k)) t) =
            fun t => Real.sqrt 2 * (G t * Real.cos (((k + 1 : ℕ) : ℝ) * t)) := by
          funext t
          simp only [trigBasisFun_STR02934]
          ring
        have key : meanT_STR02901 (fun t => G t * Real.cos (((k + 1 : ℕ) : ℝ) * t)) = 0 :=
          htest _ (cosFreq_isC2_STR02962 (k + 1)) (meanT_cos_STR02962 (Nat.succ_ne_zero k))
        rw [hf, meanT_const_mul_STR02962, key, mul_zero]
      · have hf : (fun t => G t * trigBasisFun_STR02934 (some (true, k)) t) =
            fun t => Real.sqrt 2 * (G t * Real.sin (((k + 1 : ℕ) : ℝ) * t)) := by
          funext t
          simp only [trigBasisFun_STR02934]
          ring
        have key : meanT_STR02901 (fun t => G t * Real.sin (((k + 1 : ℕ) : ℝ) * t)) = 0 :=
          htest _ (sinFreq_isC2_STR02962 (k + 1)) (meanT_sin_STR02962 (Nat.succ_ne_zero k))
        rw [hf, meanT_const_mul_STR02962, key, mul_zero]
  have hmem : x ∈ (Submodule.span ℝ (Set.range trigBasisLp_STR02934))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hperp i
    | zero => simp
    | add y z _ _ hy hz => rw [inner_add_left, hy, hz, add_zero]
    | smul a y _ hy => rw [real_inner_smul_left, hy, mul_zero]
  rw [orthogonal_trigBasisLp_eq_bot_STR02934, Submodule.mem_bot] at hmem
  have hG0 : G =ᵐ[circleMeasure_STR02934] 0 := by
    have h1 := hx_ae
    rw [hmem] at h1
    exact h1.symm.trans (Lp.coeFn_zero ℝ 2 circleMeasure_STR02934)
  have hae0 : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))), G t = 0 :=
    (ae_circle_iff_STR02962 (P := fun t => G t = 0)).mp hG0
  have hae1 : ∀ᵐ t, t ∈ Set.Ioc 0 (2 * Real.pi) → G t = 0 :=
    (ae_restrict_iff' measurableSet_Ioc).mp hae0
  have hzero : ∀ t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi), G t = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t0, ht0, hGt0⟩ := hcon
    have hUopen : IsOpen (G ⁻¹' {0}ᶜ ∩ Set.Ioo 0 (2 * Real.pi)) :=
      (isClosed_singleton.isOpen_compl.preimage hGc).inter isOpen_Ioo
    have hUne : (G ⁻¹' {0}ᶜ ∩ Set.Ioo 0 (2 * Real.pi)).Nonempty := ⟨t0, hGt0, ht0⟩
    have hpos : 0 < volume (G ⁻¹' {0}ᶜ ∩ Set.Ioo 0 (2 * Real.pi)) :=
      hUopen.measure_pos volume hUne
    have hsub : G ⁻¹' {0}ᶜ ∩ Set.Ioo 0 (2 * Real.pi) ⊆
        {t | ¬ (t ∈ Set.Ioc 0 (2 * Real.pi) → G t = 0)} := by
      intro t ht
      exact fun hh => (Set.mem_compl_singleton_iff.mp ht.1) (hh ⟨ht.2.1, ht.2.2.le⟩)
    exact absurd (measure_mono_null hsub (ae_iff.mp hae1)) hpos.ne'
  have hIcc : Set.Icc (0 : ℝ) (2 * Real.pi) ⊆ {t | G t = 0} := by
    rw [← closure_Ioo (by linarith [Real.pi_pos] : (0 : ℝ) < 2 * Real.pi).ne]
    exact closure_minimal hzero (isClosed_eq hGc continuous_const)
  intro t
  obtain ⟨y, hy, hGy⟩ := hGp.exists_mem_Ico₀ Real.two_pi_pos t
  rw [hGy]
  exact hIcc ⟨hy.1, hy.2.le⟩

/-- Quotient-to-chart step: if `u` has positive chart entropy and the quotient `I/(2H)` of the
direction `u + s v` is not below its value at `s = 0` near `s = 0`, then the functional
`J(h, r - 1, u + s v)` with `r = I(u)/(2H(u))` has a local minimum at `s = 0`. -/
theorem localMin_Jchart_of_quot_STR02962 (h : ℝ) {u v : ℝ → ℝ} {r : ℝ}
    (hr : r = fisherChart_STR02949 h u / (2 * entropyChart_STR02949 h u))
    (hH0 : 0 < entropyChart_STR02949 h u)
    (hH : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < entropyChart_STR02949 h (fun t => u t + s * v t))
    (hq : ∀ᶠ s in 𝓝 (0 : ℝ),
      fisherChart_STR02949 h u / (2 * entropyChart_STR02949 h u) ≤
        fisherChart_STR02949 h (fun t => u t + s * v t) /
          (2 * entropyChart_STR02949 h (fun t => u t + s * v t))) :
    IsLocalMin (fun s : ℝ => Jchart_STR02950 h (r - 1) (fun t => u t + s * v t)) 0 := by
  have hu0 : (fun t => u t + (0 : ℝ) * v t) = u := by
    funext t
    simp
  have key := localMin_of_quot_STR02962
    (F := fun s : ℝ => fisherChart_STR02949 h (fun t => u t + s * v t))
    (H := fun s : ℝ => entropyChart_STR02949 h (fun t => u t + s * v t))
    (r := r) (by simp only [hu0]; exact hr) (by simp only [hu0]; exact hH0) hH
    (by simp only [hu0]; exact hq)
  have hJ : ∀ s : ℝ, Jchart_STR02950 h (r - 1) (fun t => u t + s * v t) =
      fisherChart_STR02949 h (fun t => u t + s * v t) -
        2 * r * entropyChart_STR02949 h (fun t => u t + s * v t) := by
    intro s
    unfold Jchart_STR02950
    rw [show (1 : ℝ) + (r - 1) = r by ring]
  have hfun : (fun s : ℝ => Jchart_STR02950 h (r - 1) (fun t => u t + s * v t)) =
      fun s : ℝ => fisherChart_STR02949 h (fun t => u t + s * v t) -
        2 * r * entropyChart_STR02949 h (fun t => u t + s * v t) := funext hJ
  rw [hfun]
  exact key

theorem angSec_mem_STR02962 (θ : AngCircle) : angSec θ ∈ Set.Icc 0 (2 * Real.pi) := by
  have h := (AddCircle.equivIoc (2 * Real.pi) 0 θ).2
  exact ⟨h.1.le, le_of_le_of_eq h.2 (zero_add _)⟩

theorem coe_angSec_STR02962 (θ : AngCircle) : ((angSec θ : ℝ) : AngCircle) = θ := by
  unfold angSec
  simp

theorem integral_angSec_STR02962 (Φ : ℝ → ℝ) :
    ∫ θ, Φ (angSec θ) ∂angHaar = (2 * Real.pi)⁻¹ * ∫ s in (0 : ℝ)..(2 * Real.pi), Φ s := by
  have h1 : ∫ a in (0 : ℝ)..(0 + 2 * Real.pi), Φ (angSec (a : AngCircle)) =
      ∫ b : AngCircle, Φ (angSec b) :=
    AddCircle.intervalIntegral_preimage (2 * Real.pi) 0 (fun θ : AngCircle => Φ (angSec θ))
  have h2 : ∫ a in (0 : ℝ)..(0 + 2 * Real.pi), Φ (angSec (a : AngCircle)) =
      ∫ s in (0 : ℝ)..(2 * Real.pi), Φ s := by
    rw [zero_add, intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_of_le Real.two_pi_pos.le]
    refine setIntegral_congr_fun measurableSet_Ioc (fun a ha => ?_)
    have hmem : a ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) := by rw [zero_add]; exact ha
    show Φ (AddCircle.equivIoc (2 * Real.pi) 0 (a : AngCircle) : ℝ) = Φ a
    rw [AddCircle.equivIoc_coe_of_mem hmem]
  unfold angHaar
  rw [AddCircle.integral_haarAddCircle, smul_eq_mul, ← h2, h1]

theorem integral_ibp_periodic_STR02962 {f f' g g' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hfc : Continuous f')
    (hfp : Function.Periodic f (2 * Real.pi))
    (hg : ∀ x, HasDerivAt g (g' x) x) (hgc : Continuous g')
    (hgp : Function.Periodic g (2 * Real.pi)) :
    ∫ s in (0 : ℝ)..(2 * Real.pi), f s * g' s = -∫ s in (0 : ℝ)..(2 * Real.pi), f' s * g s := by
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * Real.pi)
    (fun x _ => hf x) (fun x _ => hg x) (hfc.intervalIntegrable _ _) (hgc.intervalIntegrable _ _)
  have e1 : f (2 * Real.pi) = f 0 := by simpa using hfp 0
  have e2 : g (2 * Real.pi) = g 0 := by simpa using hgp 0
  rw [h, e1, e2]
  ring

theorem isAngularWeakDeriv_lift_STR02962 {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hfc : Continuous f') (hfp : Function.Periodic f (2 * Real.pi)) :
    IsAngularWeakDeriv (fun θ => f (angSec θ)) (fun θ => f' (angSec θ)) := by
  have hcont : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hsec : Measurable angSec :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (2 * Real.pi) 0).measurable
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hcont.continuousOn
  obtain ⟨C', hC'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hfc.continuousOn
  refine ⟨?_, ?_, ?_⟩
  · exact MemLp.of_bound (hcont.measurable.comp hsec).aestronglyMeasurable C
      (ae_of_all _ fun θ => hC _ (angSec_mem_STR02962 θ))
  · exact MemLp.of_bound (hfc.measurable.comp hsec).aestronglyMeasurable C'
      (ae_of_all _ fun θ => hC' _ (angSec_mem_STR02962 θ))
  · intro ψ hψ
    unfold IsSmoothAngular at hψ
    have hdiff : Differentiable ℝ (fun s : ℝ => ψ (s : AngCircle)) := hψ.differentiable (by simp)
    have hcd : Continuous (deriv (fun s : ℝ => ψ (s : AngCircle))) :=
      hψ.continuous_deriv (by simp)
    have hper : Function.Periodic (fun s : ℝ => ψ (s : AngCircle)) (2 * Real.pi) := by
      intro s
      show ψ ((s + 2 * Real.pi : ℝ) : AngCircle) = ψ ((s : ℝ) : AngCircle)
      rw [AddCircle.coe_add_period]
    have hIBP : ∫ s in (0 : ℝ)..(2 * Real.pi), f s * deriv (fun s : ℝ => ψ (s : AngCircle)) s =
        -∫ s in (0 : ℝ)..(2 * Real.pi), f' s * ψ (s : AngCircle) :=
      integral_ibp_periodic_STR02962 hf hfc hfp (fun x => (hdiff x).hasDerivAt) hcd hper
    have key1 : ∫ θ, f (angSec θ) * angDeriv ψ θ ∂angHaar =
        (2 * Real.pi)⁻¹ * ∫ s in (0 : ℝ)..(2 * Real.pi),
          f s * deriv (fun s : ℝ => ψ (s : AngCircle)) s :=
      integral_angSec_STR02962 (fun s => f s * deriv (fun s : ℝ => ψ (s : AngCircle)) s)
    have key2 : ∫ θ, f' (angSec θ) * ψ θ ∂angHaar =
        (2 * Real.pi)⁻¹ * ∫ s in (0 : ℝ)..(2 * Real.pi), f' s * ψ (s : AngCircle) := by
      have h := integral_angSec_STR02962 (fun s => f' s * ψ (s : AngCircle))
      simp only [coe_angSec_STR02962] at h
      exact h
    show ∫ θ, f (angSec θ) * angDeriv ψ θ ∂angHaar = -∫ θ, f' (angSec θ) * ψ θ ∂angHaar
    rw [key1, key2, hIBP]
    ring

/-- Conditional helper (not the specification statement; it adds the hypothesis `hquot`).
Assume `u` is `C^{2,1/2}` with positive chart
entropy, and that for every mean-zero `C^{2,1/2}` direction `v` the quotient `I/(2H)` is
not decreased near `s = 0` along `u + s v`, and the entropy stays positive there. Then with
`r = I(u)/(2H(u))`, every directional derivative of `J(h, r - 1, ·)` at `u` vanishes and
`G = gradG(h, r - 1, u)` vanishes pointwise. -/
theorem quot_step_fully_critical_STR02962
    (h : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (hH0 : 0 < entropyChart_STR02949 h u)
    (hquot : ∀ v : ℝ → ℝ, IsC2Alpha_STR02901 (1 / 2) v → meanT_STR02901 v = 0 →
      (∀ᶠ s in 𝓝 (0 : ℝ), 0 < entropyChart_STR02949 h (fun t => u t + s * v t)) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ),
        fisherChart_STR02949 h u / (2 * entropyChart_STR02949 h u) ≤
          fisherChart_STR02949 h (fun t => u t + s * v t) /
            (2 * entropyChart_STR02949 h (fun t => u t + s * v t)))) :
    (∀ v : ℝ → ℝ, IsC2Alpha_STR02901 (1 / 2) v → meanT_STR02901 v = 0 →
        HasDerivAt
          (fun s : ℝ => Jchart_STR02950 h
            (fisherChart_STR02949 h u / (2 * entropyChart_STR02949 h u) - 1)
            (fun t => u t + s * v t)) 0 0) ∧
      ∀ t : ℝ, gradG_STR02950 h
        (fisherChart_STR02949 h u / (2 * entropyChart_STR02949 h u) - 1) u t = 0 := by
  set r := fisherChart_STR02949 h u / (2 * entropyChart_STR02949 h u) with hr
  set γ := r - 1 with hγ
  have hcrit : ∀ v : ℝ → ℝ, IsC2Alpha_STR02901 (1 / 2) v → meanT_STR02901 v = 0 →
      meanT_STR02901 (fun t => gradG_STR02950 h γ u t * v t) = 0 := by
    intro v hv hv0
    obtain ⟨hH, hq⟩ := hquot v hv hv0
    have hmin := localMin_Jchart_of_quot_STR02962 h hr hH0 hH hq
    exact fermat_STR02962 h γ hu hv hmin
  refine ⟨fun v hv hv0 => ?_, gradG_zero_of_tests_STR02962 h γ hu hcrit⟩
  have hd := str029_50_integrate_variation_compute_mean_variation h γ hu hv
  rw [hcrit v hv hv0] at hd
  exact hd

/-! ### From the angular minimizer to the chart -/

theorem qAng_eq_qT_STR02962 (h : ℝ) (θ : AngCircle) :
    qAng_STR02901 h θ = qT_STR02901 h (angSec θ) := by
  obtain ⟨y, rfl⟩ := angEquiv.surjective θ
  have hs : DGPS.Examples.ThreeSpeciesCircle.pt (SharpLSI.secT y 0) = y := by
    have e : (fun _ : Fin 1 => SharpLSI.secT y 0) = SharpLSI.secT y := by
      funext i; rw [Subsingleton.elim i 0]
    show torusLift (fun _ : Fin 1 => SharpLSI.secT y 0) = y
    rw [e]; exact SharpLSI.liftT_secT y
  rw [qAng_comp_STR02901, angSec_angEquiv]
  have e : referenceDensity h y =
      referenceDensity h (DGPS.Examples.ThreeSpeciesCircle.pt (SharpLSI.secT y 0)) := by
    rw [hs]
  rw [e, referenceDensity_pt, besselI_zero_eq_meanT_STR02901]
  unfold qT_STR02901
  rw [show 2 * Real.pi * 3 * SharpLSI.secT y 0 = 3 * (2 * Real.pi * SharpLSI.secT y 0) by ring]

/-- `log` of the normalizing constant of the chart density. -/
noncomputable def logZ_STR02962 (h : ℝ) (u : ℝ → ℝ) : ℝ :=
  Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)))

/-- `log` of the normalizing constant of the reference density. -/
noncomputable def logZh_STR02962 (h : ℝ) : ℝ :=
  Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s))))

/-- The angular square-root density `sqrt (rho(h, u) / q_h)` attached to a chart function `u`,
written on the circle through the section `angSec`. -/
noncomputable def gLift_STR02962 (h : ℝ) (u : ℝ → ℝ) (θ : AngCircle) : ℝ :=
  Real.exp ((u (angSec θ) - logZ_STR02962 h u + logZh_STR02962 h) / 2)

theorem gLift_sq_STR02962 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) (θ : AngCircle) :
    gLift_STR02962 h u θ ^ 2 * qAng_STR02901 h θ = rhoT_STR02901 h u (angSec θ) := by
  have hZ : 0 < meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)) :=
    meanT_pos_STR02901 (by fun_prop) fun s => Real.exp_pos _
  have hZh : 0 < meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s))) :=
    meanT_pos_STR02901 (by fun_prop) fun s => Real.exp_pos _
  have e1 : Real.exp (u (angSec θ) - logZ_STR02962 h u + logZh_STR02962 h) =
      Real.exp (u (angSec θ)) /
        meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)) *
        meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s))) := by
    unfold logZ_STR02962 logZh_STR02962
    rw [Real.exp_add, Real.exp_sub, Real.exp_log hZ, Real.exp_log hZh]
  have e2 : Real.exp (h * Real.cos (3 * angSec θ) + u (angSec θ)) =
      Real.exp (h * Real.cos (3 * angSec θ)) * Real.exp (u (angSec θ)) := Real.exp_add _ _
  rw [qAng_eq_qT_STR02962]
  unfold gLift_STR02962 qT_STR02901 rhoT_STR02901
  rw [sq, ← Real.exp_add, add_halves, e1, e2]
  field_simp

theorem measurable_angSec_STR02962 : Measurable angSec :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIoc (2 * Real.pi) 0).measurable

theorem integrable_comp_angSec_STR02962 {Φ : ℝ → ℝ} (hΦ : Continuous Φ) :
    Integrable (fun θ => Φ (angSec θ)) angHaar := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi)).exists_bound_of_continuousOn
    hΦ.continuousOn
  exact Integrable.of_bound (hΦ.measurable.comp measurable_angSec_STR02962).aestronglyMeasurable C
    (ae_of_all _ fun θ => hC _ (angSec_mem_STR02962 θ))

theorem meanT_nonneg_STR02962 {F : ℝ → ℝ} (hF : ∀ t, 0 ≤ F t) : 0 ≤ meanT_STR02901 F := by
  unfold meanT_STR02901
  have : 0 ≤ ∫ t in (0 : ℝ)..(2 * Real.pi), F t :=
    intervalIntegral.integral_nonneg Real.two_pi_pos.le (fun t _ => hF t)
  positivity

theorem isAngularWeakDeriv_gLift_STR02962 (h : ℝ) {u : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    IsAngularWeakDeriv (gLift_STR02962 h u)
      (fun θ => gLift_STR02962 h u θ * deriv u (angSec θ) / 2) := by
  have hc : Continuous u := hu.2.1.continuous
  have hc' : Continuous (deriv u) := hu.2.2.1.continuous
  set F : ℝ → ℝ := fun s => Real.exp ((u s - logZ_STR02962 h u + logZh_STR02962 h) / 2) with hF
  have hd : ∀ x, HasDerivAt F (F x * deriv u x / 2) x := by
    intro x
    have h1 : HasDerivAt u (deriv u x) x := (hu.2.1 x).hasDerivAt
    have h2 := (((h1.sub_const (logZ_STR02962 h u)).add_const (logZh_STR02962 h)).div_const 2).exp
    convert h2 using 1
    ring
  have hFc : Continuous (fun x => F x * deriv u x / 2) := by
    rw [hF]; fun_prop
  have hFp : Function.Periodic F (2 * Real.pi) := by
    intro x
    show Real.exp ((u (x + 2 * Real.pi) - logZ_STR02962 h u + logZh_STR02962 h) / 2) =
      Real.exp ((u x - logZ_STR02962 h u + logZh_STR02962 h) / 2)
    rw [hu.1 x]
  exact isAngularWeakDeriv_lift_STR02962 hd hFc hFp

theorem angDomain_gLift_STR02962 (h : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    AngDomain_STR02901 h (gLift_STR02962 h u) := by
  have hc : Continuous u := hu.2.1.continuous
  refine ⟨⟨_, isAngularWeakDeriv_gLift_STR02962 h hu⟩,
    Filter.Eventually.of_forall fun θ => (Real.exp_pos _).le, ?_⟩
  calc ∫ θ, gLift_STR02962 h u θ ^ 2 * qAng_STR02901 h θ ∂angHaar
      = ∫ θ, rhoT_STR02901 h u (angSec θ) ∂angHaar :=
        integral_congr_ae (Filter.Eventually.of_forall (gLift_sq_STR02962 h hc))
    _ = meanT_STR02901 (rhoT_STR02901 h u) := integral_angSec_STR02962 _
    _ = 1 := meanT_rho_STR02950 h hc

theorem angEntropy_gLift_STR02962 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) :
    angEntropy_STR02901 h (gLift_STR02962 h u) = entropyChart_STR02949 h u := by
  have hlog : ∀ θ, Real.log (gLift_STR02962 h u θ ^ 2) =
      u (angSec θ) - logZ_STR02962 h u + logZh_STR02962 h := by
    intro θ
    unfold gLift_STR02962
    rw [Real.log_pow, Real.log_exp]
    push_cast
    ring
  set G : ℝ → ℝ := fun s => 1 * (u s * rhoT_STR02901 h u s) +
    (-logZ_STR02962 h u + logZh_STR02962 h) * rhoT_STR02901 h u s with hG
  have hpt : ∀ θ, gLift_STR02962 h u θ ^ 2 * Real.log (gLift_STR02962 h u θ ^ 2) *
      qAng_STR02901 h θ = G (angSec θ) := by
    intro θ
    have := gLift_sq_STR02962 h hu θ
    show _ = 1 * (u (angSec θ) * rhoT_STR02901 h u (angSec θ)) +
        (-logZ_STR02962 h u + logZh_STR02962 h) * rhoT_STR02901 h u (angSec θ)
    rw [hlog θ, ← this]
    ring
  unfold angEntropy_STR02901
  calc ∫ θ, gLift_STR02962 h u θ ^ 2 * Real.log (gLift_STR02962 h u θ ^ 2) *
        qAng_STR02901 h θ ∂angHaar
      = ∫ θ, G (angSec θ) ∂angHaar := integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = meanT_STR02901 G := integral_angSec_STR02962 G
    _ = 1 * meanT_STR02901 (fun s => u s * rhoT_STR02901 h u s) +
        (-logZ_STR02962 h u + logZh_STR02962 h) * meanT_STR02901 (rhoT_STR02901 h u) :=
        meanT_comb2_STR02950 (hu.mul (continuous_rho_STR02950 h hu))
          (continuous_rho_STR02950 h hu) _ _
    _ = entropyChart_STR02949 h u := by
        rw [meanT_rho_STR02950 h hu]
        unfold entropyChart_STR02949 logZ_STR02962 logZh_STR02962
        ring

theorem fisherChart_nonneg_STR02962 (h : ℝ) {u : ℝ → ℝ} (hu : Continuous u) :
    0 ≤ fisherChart_STR02949 h u :=
  meanT_nonneg_STR02962 fun t => mul_nonneg (sq_nonneg _) (rhoT_pos_STR02901 h hu t).le

theorem angFisher_gLift_STR02962 (h : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    angFisher_STR02901 h (gLift_STR02962 h u) = ENNReal.ofReal (fisherChart_STR02949 h u) := by
  have hc : Continuous u := hu.2.1.continuous
  have hc' : Continuous (deriv u) := hu.2.2.1.continuous
  have hρ := continuous_rho_STR02950 h hc
  set G : ℝ → ℝ := fun s => (1 / 4) * (deriv u s ^ 2 * rhoT_STR02901 h u s) with hG
  have hpt : ∀ θ, ENNReal.ofReal (qAng_STR02901 h θ) *
      ‖gLift_STR02962 h u θ * deriv u (angSec θ) / 2‖ₑ ^ 2 =
      ENNReal.ofReal (G (angSec θ)) := by
    intro θ
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      ← ENNReal.ofReal_mul (qAng_pos_STR02901 h θ).le, sq_abs]
    congr 1
    show qAng_STR02901 h θ * (gLift_STR02962 h u θ * deriv u (angSec θ) / 2) ^ 2 =
      1 / 4 * (deriv u (angSec θ) ^ 2 * rhoT_STR02901 h u (angSec θ))
    rw [← gLift_sq_STR02962 h hc θ]
    ring
  have hint : Integrable (fun θ => G (angSec θ)) angHaar :=
    integrable_comp_angSec_STR02962 (by rw [hG]; fun_prop)
  have hnn : 0 ≤ᵐ[angHaar] (fun θ => G (angSec θ)) :=
    Filter.Eventually.of_forall fun θ => by
      have := rhoT_pos_STR02901 h hc (angSec θ)
      show 0 ≤ (1 / 4) * (deriv u (angSec θ) ^ 2 * rhoT_STR02901 h u (angSec θ))
      positivity
  rw [angFisher_eq_STR02901 h (isAngularWeakDeriv_gLift_STR02962 h hu)]
  calc 4 * ∫⁻ θ, ENNReal.ofReal (qAng_STR02901 h θ) *
        ‖gLift_STR02962 h u θ * deriv u (angSec θ) / 2‖ₑ ^ 2 ∂angHaar
      = 4 * ∫⁻ θ, ENNReal.ofReal (G (angSec θ)) ∂angHaar := by rw [lintegral_congr hpt]
    _ = 4 * ENNReal.ofReal (∫ θ, G (angSec θ) ∂angHaar) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
    _ = 4 * ENNReal.ofReal (meanT_STR02901 G) := by rw [integral_angSec_STR02962 G]; rfl
    _ = ENNReal.ofReal (fisherChart_STR02949 h u) := by
        have e : meanT_STR02901 G = (1 / 4) * fisherChart_STR02949 h u :=
          meanT_const_mul_STR02962 (1 / 4) _
        rw [e, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

/-! ### Almost-everywhere invariance and the chart quotient -/

theorem isAngularWeakDeriv_congr_STR02962 {f f' G : AngCircle → ℝ} (hf : f =ᵐ[angHaar] f')
    (hG : IsAngularWeakDeriv f G) : IsAngularWeakDeriv f' G where
  memLp := hG.memLp.ae_eq hf
  memLp_deriv := hG.memLp_deriv
  ibp ψ hψ := by
    rw [← hG.ibp ψ hψ]
    refine integral_congr_ae ?_
    filter_upwards [hf] with θ hθ
    rw [hθ]

theorem angFisher_congr_STR02962 (h : ℝ) {f f' : AngCircle → ℝ} (hf : f =ᵐ[angHaar] f') :
    angFisher_STR02901 h f = angFisher_STR02901 h f' := by
  unfold angFisher_STR02901
  apply le_antisymm
  · exact le_iInf₂ fun G hG => iInf₂_le G (isAngularWeakDeriv_congr_STR02962 hf.symm hG)
  · exact le_iInf₂ fun G hG => iInf₂_le G (isAngularWeakDeriv_congr_STR02962 hf hG)

theorem angEntropy_congr_STR02962 (h : ℝ) {f f' : AngCircle → ℝ} (hf : f =ᵐ[angHaar] f') :
    angEntropy_STR02901 h f = angEntropy_STR02901 h f' := by
  unfold angEntropy_STR02901
  refine integral_congr_ae ?_
  filter_upwards [hf] with θ hθ
  rw [hθ]

/-- The angular square root of an absolute density with the representation `ρ(h, u)` is `gLift`. -/
theorem gAng_ae_eq_gLift_STR02962 (h : ℝ) (ρ : AbsoluteDensity 1) {u : ℝ → ℝ}
    (hu : Continuous u)
    (hrep : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u (angSec θ)) :
    gAng_STR02901 h ρ =ᵐ[angHaar] gLift_STR02962 h u := by
  have hnn : 0 ≤ᵐ[angHaar] gAng_STR02901 h ρ := (angDomain_gAng_STR02901 h ρ).2.1
  filter_upwards [hrep, hnn] with θ hθ hθ0
  have h1 := density_eq_gAng_sq_STR02901 h ρ (angEquiv.symm θ)
  rw [angEquiv.apply_symm_apply] at h1
  have h2 := gLift_sq_STR02962 h hu θ
  have hq : qAng_STR02901 h θ = referenceDensity h (angEquiv.symm θ) := rfl
  have hqpos := qAng_pos_STR02901 h θ
  have h3 : gAng_STR02901 h ρ θ ^ 2 = gLift_STR02962 h u θ ^ 2 := by
    apply mul_right_cancel₀ hqpos.ne'
    rw [h2, ← hθ, h1, hq]
  exact (sq_eq_sq₀ hθ0 (by unfold gLift_STR02962; exact (Real.exp_pos _).le)).1 h3

theorem uT_isC2_STR02962 (a b : ℝ) {w : ℝ → ℝ} (hw : IsC2Alpha_STR02901 (1 / 2) w) :
    IsC2Alpha_STR02901 (1 / 2) (uT_STR02901 a b w) := by
  have h := (a • cosC2_STR02915 + b • sinC2_STR02915 + PeriodicC2_STR02969.mk w hw).isC2
  have e : (a • cosC2_STR02915 + b • sinC2_STR02915 + PeriodicC2_STR02969.mk w hw).val =
      uT_STR02901 a b w := by
    funext s
    simp only [PeriodicC2_STR02969.val_add, PeriodicC2_STR02969.val_smul, cosC2_val_STR02915,
      sinC2_val_STR02915, Pi.add_apply, Pi.smul_apply, smul_eq_mul, uT_STR02901]
    rfl
  rwa [e] at h

theorem isC2_add_smul_STR02962 {u v : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (hv : IsC2Alpha_STR02901 (1 / 2) v) (s : ℝ) :
    IsC2Alpha_STR02901 (1 / 2) (fun t => u t + s * v t) :=
  (PeriodicC2_STR02969.mk u hu + s • PeriodicC2_STR02969.mk v hv).isC2

theorem ofReal_quot_STR02962 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ENNReal.ofReal a / (2 * ENNReal.ofReal b) = ENNReal.ofReal (a / (2 * b)) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_ofNat]

/-- Angular quotient minimality of `g0 =ᵐ gLift h u` gives the chart hypothesis `hquot` of
`quot_step_fully_critical_STR02962` along every `C^{2,1/2}` direction. -/
theorem hquot_of_angular_min_STR02962 (h : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (hH0 : 0 < entropyChart_STR02949 h u) {g0 : AngCircle → ℝ}
    (hg0 : g0 =ᵐ[angHaar] gLift_STR02962 h u)
    (hmin : ∀ g' : AngCircle → ℝ, AngDomain_STR02901 h g' → 0 < angEntropy_STR02901 h g' →
      angQuot_STR02901 h g0 ≤ angQuot_STR02901 h g')
    {v : ℝ → ℝ} (hv : IsC2Alpha_STR02901 (1 / 2) v) :
    (∀ᶠ s in 𝓝 (0 : ℝ), 0 < entropyChart_STR02949 h (fun t => u t + s * v t)) ∧
      (∀ᶠ s in 𝓝 (0 : ℝ),
        fisherChart_STR02949 h u / (2 * entropyChart_STR02949 h u) ≤
          fisherChart_STR02949 h (fun t => u t + s * v t) /
            (2 * entropyChart_STR02949 h (fun t => u t + s * v t))) := by
  have hcont := (str029_49_first_variations_entropy_fisher_information h hu hv).1.continuousAt
  have hu0 : (fun t => u t + (0 : ℝ) * v t) = u := by
    funext t
    simp
  have h0 : (0 : ℝ) < entropyChart_STR02949 h (fun t => u t + (0 : ℝ) * v t) := by
    rw [hu0]; exact hH0
  have hpos : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < entropyChart_STR02949 h (fun t => u t + s * v t) :=
    ContinuousAt.eventually_lt (f := fun _ : ℝ => (0 : ℝ)) continuousAt_const hcont h0
  refine ⟨hpos, ?_⟩
  filter_upwards [hpos] with s hs
  have hc : IsC2Alpha_STR02901 (1 / 2) (fun t => u t + s * v t) := isC2_add_smul_STR02962 hu hv s
  have key := hmin (gLift_STR02962 h (fun t => u t + s * v t)) (angDomain_gLift_STR02962 h hc)
    (by rw [angEntropy_gLift_STR02962 h hc.2.1.continuous]; exact hs)
  unfold angQuot_STR02901 at key
  rw [angFisher_congr_STR02962 h hg0, angEntropy_congr_STR02962 h hg0,
    angFisher_gLift_STR02962 h hu, angEntropy_gLift_STR02962 h hu.2.1.continuous,
    angFisher_gLift_STR02962 h hc, angEntropy_gLift_STR02962 h hc.2.1.continuous,
    ofReal_quot_STR02962 _ hH0, ofReal_quot_STR02962 _ hs] at key
  exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg (fisherChart_nonneg_STR02962 h hc.2.1.continuous)
    (by positivity))).1 key

/-- If the gradient `G` vanishes pointwise along `a cos + b sin + w`, the variational range map
vanishes at the corresponding point of the chart `ℝ⁴ × E`. -/
theorem Rpar_eq_zero_of_gradG_zero_STR02962 (a b h γ : ℝ) (wE : E_STR02969)
    (hG : ∀ t, gradG_STR02950 h γ
      (uT_STR02901 a b ((wE : E_STR02969) : PeriodicC2_STR02969).val) t = 0) :
    Rpar_STR02916 (a, b, h, γ) wE = 0 := by
  have key : ∀ t, ((Rpar_STR02916 (a, b, h, γ) wE : Y_STR02969) :
      PeriodicHolder_STR02968).val t = 0 := by
    intro t
    have e := str029_15_smooth_variational_range_map_pointwise (a, b, h, γ, wE) t
    have hz : gradG_STR02950 h γ
        (uT_STR02901 a b ((wE : E_STR02969) : PeriodicC2_STR02969).val) = fun _ => 0 := funext hG
    change ((Rvar_STR02915 (a, b, h, γ, wE) : Y_STR02969) : PeriodicHolder_STR02968).val t = 0
    rw [e]
    dsimp only
    rw [hz]
    simp [projP_STR02953, pair_STR02953, meanT_STR02901]
  exact Submodule.coe_eq_zero.1 (PeriodicHolder_STR02968.val_eq_zero.1 (funext key))

/-- STR029.62. A positive-entropy global optimizer `ρ` of the ordinary problem (minimality of
`I_h/(2 H_h)` among positive-entropy absolute densities) with the positive logarithmic representation
`ρ = ρ(h, a cos + b sin + w)`, `w ∈ C^{2,1/2} ∩ E`, of STR029.01 (angular a.e. identity), and
`r = I_h/(2 H_h)` in angular units, satisfies: (1) `D_u J(h, r - 1, u)[v] = 0` for every
mean-zero `C^{2,1/2}` direction `v`, with `u = a cos + b sin + w`; (2) the full gradient
`G(h, r - 1, u)` vanishes at every point; (3) the element `wE` of `E` with value `w` is a zero of
the variational range map at `(a, b, h, r - 1)`, and in every graph neighbourhood `(U, V, ψ)` of
STR029.16 that contains the parameter point and `wE`, `wE = ψ (a, b, h, r - 1)`. -/
theorem str029_62_global_optimizer_positive_chart_fully_critical
    (h : ℝ) (ρ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h ρ)
    (hmin : ∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
      ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤
        ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ'))
    (a b : ℝ) (w : ℝ → ℝ) (hw : IsC2Alpha_STR02901 (1 / 2) w) (hwE : InE_STR02901 w)
    (hrep : ∀ᵐ θ ∂angHaar,
      ρ.density (angEquiv.symm θ) = rhoT_STR02901 h (uT_STR02901 a b w) (angSec θ))
    (r : ℝ)
    (hr : r = (angFisher_STR02901 h (gAng_STR02901 h ρ)).toReal /
      (2 * angEntropy_STR02901 h (gAng_STR02901 h ρ))) :
    (∀ v : ℝ → ℝ, IsC2Alpha_STR02901 (1 / 2) v → meanT_STR02901 v = 0 →
        HasDerivAt (fun s : ℝ => Jchart_STR02950 h (r - 1)
          (fun t => uT_STR02901 a b w t + s * v t)) 0 0) ∧
      (∀ t : ℝ, gradG_STR02950 h (r - 1) (uT_STR02901 a b w) t = 0) ∧
      ∃ wE : E_STR02969, ((wE : PeriodicC2_STR02969).val = w) ∧
        Rpar_STR02916 (a, b, h, r - 1) wE = 0 ∧
        ∀ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
          (∀ p ∈ U, ∀ w' ∈ V, Rpar_STR02916 p w' = 0 ↔ w' = ψ p) →
          (a, b, h, r - 1) ∈ U → wE ∈ V → wE = ψ (a, b, h, r - 1) := by
  have hu := uT_isC2_STR02962 a b hw
  have hc : Continuous (uT_STR02901 a b w) := hu.2.1.continuous
  have hae := gAng_ae_eq_gLift_STR02962 h ρ hc hrep
  have H0 : angEntropy_STR02901 h (gAng_STR02901 h ρ) =
      entropyChart_STR02949 h (uT_STR02901 a b w) :=
    (angEntropy_congr_STR02962 h hae).trans (angEntropy_gLift_STR02962 h hc)
  have F0 : angFisher_STR02901 h (gAng_STR02901 h ρ) =
      ENNReal.ofReal (fisherChart_STR02949 h (uT_STR02901 a b w)) :=
    (angFisher_congr_STR02962 h hae).trans (angFisher_gLift_STR02962 h hu)
  have hH0 : 0 < entropyChart_STR02949 h (uT_STR02901 a b w) := by
    rw [← H0]
    exact (ordinaryEntropy_pos_iff_STR02901 h ρ).1 hpos
  have hmin' := (optimizer_transfer_STR02901 h ρ).1 (fun ρ' hρ' => hmin ρ' hρ')
  have hrc : r = fisherChart_STR02949 h (uT_STR02901 a b w) /
      (2 * entropyChart_STR02949 h (uT_STR02901 a b w)) := by
    rw [hr, F0, H0, ENNReal.toReal_ofReal (fisherChart_nonneg_STR02962 h hc)]
  subst hrc
  obtain ⟨hD, hG⟩ := quot_step_fully_critical_STR02962 h hu hH0
    (fun v hv _ => hquot_of_angular_min_STR02962 h hu hH0 hae hmin' hv)
  refine ⟨hD, hG, ⟨PeriodicC2_STR02969.mk w hw,
    (str029_69_completeness_closed_complements_range_spaces_E.1 _).2 hwE⟩, rfl, ?_, ?_⟩
  · exact Rpar_eq_zero_of_gradG_zero_STR02962 a b h _ _ hG
  · intro U V ψ hgraph hpU hwV
    exact (hgraph _ hpU _ hwV).1 (Rpar_eq_zero_of_gradG_zero_STR02962 a b h _ _ hG)

end DGPS.Frontier.STR029
