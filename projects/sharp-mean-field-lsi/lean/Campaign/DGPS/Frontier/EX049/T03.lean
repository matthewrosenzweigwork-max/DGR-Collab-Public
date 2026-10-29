import DGPS.Frontier.EX049.T02
import DGPS.Frontier.EX049.T25
import DGPS.Frontier.EX049.T34
import DGPS.Frontier.EX049.T35
import DGPS.Frontier.EX049.T36

/-!
# EX049.03: Angular products and periodic integration by parts

Task id: EX049.03 (node EX049, leaf formalization; prerequisites EX049.02, EX049.34, EX049.35,
EX049.36; the normalized-Haar interval formula is EX049.25). Here `angHaar` is the normalized
Haar measure of the angular circle `AngCircle = AddCircle (2 * π)`.

## Provides

- `DGPS.Frontier.EX049.ex049_03_angular_products_periodic_integration_parts`: the conjunction of
  (a) for angular `H¹` functions `u`, `v` the product `u v` is angular `H¹`; for all weak
  derivatives `g`, `h` of `u`, `v` the product `u v` has weak derivative `g v + u h`, and both
  `u v` and `g v + u h` are integrable;
  (b) for a periodic `C¹` function `a` (lifted to the circle as `hper.lift`) and an angular `H¹`
  function `v`, the product `hper.lift * v` is angular `H¹`; for every weak derivative `g` of `v`
  it has weak derivative `angDeriv hper.lift * v + hper.lift * g`, and both products are
  integrable;
  (c) for periodic `C¹` `a` and angular `H¹` `v`, the square `v²` is angular `H¹`; for every weak
  derivative `w` of `v²` the products `hper.lift * w` and `angDeriv hper.lift * v²` are
  integrable and `∫ hper.lift * w dm = -∫ angDeriv hper.lift * v² dm`.
- `DGPS.Frontier.EX049.integrable_weak_EX04903`: the functions of a weak-derivative pair are
  integrable on the probability space.
- `DGPS.Frontier.EX049.angularH1_prod_EX04903`: products of angular `H¹` functions are angular `H¹`.
- `DGPS.Frontier.EX049.prod_weak_EX04903`: the product rule `(u v)' = g v + u h` for weak
  derivatives.
- `DGPS.Frontier.EX049.sq_weak_EX04903`: the weak derivative of `v²` is `2 g v` (written as
  `g v + v g`).
- `DGPS.Frontier.EX049.ibp_EX04903`: the periodic integration by parts identity for a lifted
  `C¹` multiplier against `v²`.
- `DGPS.Frontier.EX049.prod_ibp_EX04903`, `DGPS.Frontier.EX049.prod_interval_EX04903`,
  `DGPS.Frontier.EX049.sq_interval_EX04903`, `DGPS.Frontier.EX049.sq_ae_EX04903`: interval and
  circle versions of the product and square integration by parts identities.
- `DGPS.Frontier.EX049.int_circle_EX04903`, `DGPS.Frontier.EX049.angDeriv_coe_EX04903`,
  `DGPS.Frontier.EX049.coe_two_pi_EX04903`, `DGPS.Frontier.EX049.bdd_EX04903`,
  `DGPS.Frontier.EX049.memLp_mul_bdd_EX04903`, `DGPS.Frontier.EX049.intervalCongr_EX04903`:
  bookkeeping lemmas (normalized Haar as an interval average, circle derivative of a pullback,
  endpoint identification, boundedness, `L²` multiplication, a.e. congruence on `(0, 2π)`).

## R5 notes

- The angular `H¹` notion is EX049.02's `AngularH1` from `DGPS.Circle.AngularNormalization`
  (a weak derivative in `L²(angHaar)` tested against smooth angular functions). It is not
  redefined here.
- The absolutely continuous representatives of EX049.02 are used only inside proofs. The
  statements are about the given a.e.-defined functions `u`, `v`, `g`, `h`, `w`; no
  representative is assumed or chosen in a statement. Products are pointwise products of the
  given functions, and every equality of derivatives is an almost-everywhere equality.
- The product clause (a) and the multiplier clause (b) are stated for all weak derivatives of the
  factors, not for a chosen one. Uniqueness up to a.e. equality of weak derivatives is proved
  inside the proof (EX049.25), so this is the same content as the formula `(uv)' = u'v + uv'`.
- Periodicity of the multiplier is the Mathlib hypothesis `Function.Periodic a (2 * π)` on `ℝ`,
  with `a` of class `C¹` on all of `ℝ` (the global `ContDiff ℝ 1 a` of EX049.35). The circle
  multiplier is `hper.lift`, so the multiplier is a function on `AngCircle`.
- The derivative of the lifted multiplier on the circle is `angDeriv` (the angular derivative of
  EX049.35 / `AngularNormalization`), not Mathlib's `deriv` on the circle. On `ℝ` it equals
  `deriv a` (`angDeriv_coe_EX04935`).
- Integrability is part of the statements (a), (b), (c). The specification says that "all
  displayed products are integrable"; integrability of the products in (a) and (b) is recorded
  in the conclusions rather than left implicit, and integrability of `a w` and `a' v²` in (c) is
  part of the conclusion.
- In (c) the identity is stated for every weak derivative `w` of `v²`, with the existence of such
  a `w` asserted as the first conjunct `AngularH1 (v²)`. Since weak derivatives are unique up to
  almost-everywhere equality, this is the specification's `(v²)'`.
- The integral `∫ a (v²)' dm` is taken against the normalized Haar probability `angHaar`, as in
  the specification (`dm = dθ/(2π)`). The factor `1/(2π)` of EX049.33 enters through the interval
  average `integral_angHaar_interval_EX04925`, not through a separate hypothesis.
- The integral identity on `(0, 2π)` (`prod_interval_EX04903`, `sq_interval_EX04903`) uses
  the endpoint products of EX049.02 (`v(0) = v(2π)` for the representative) together with the
  periodic endpoint values of the multiplier; these are derived from the circle identity
  `(2π) = 0` in `AngCircle`, not assumed.
-/

open MeasureTheory Set Filter
open scoped ContDiff
open Real
open DGPS.Circle.AngularNormalization

namespace DGPS.Frontier.EX049

theorem integrable_weak_EX04903 {u g : AngCircle → ℝ} (h : IsAngularWeakDeriv u g) :
    Integrable u angHaar ∧ Integrable g angHaar :=
  ⟨h.memLp.integrable one_le_two, h.memLp_deriv.integrable one_le_two⟩

theorem int_circle_EX04903 (f : AngCircle → ℝ) :
    ∫ θ, f θ ∂angHaar = (2 * π)⁻¹ * ∫ x in (0:ℝ)..2 * π, f (x : AngCircle) := by
  have h := integral_angHaar_interval_EX04925 0 f
  rw [zero_add] at h
  exact h

theorem angDeriv_coe_EX04903 (ψ : AngCircle → ℝ) (s : ℝ) :
    angDeriv ψ (s : AngCircle) = deriv (fun t : ℝ => ψ (t : AngCircle)) s :=
  angDeriv_coe_EX04935 (a := fun t : ℝ => ψ (t : AngCircle)) (c := ψ) (fun _ => rfl) s

theorem coe_two_pi_EX04903 : ((2 * π : ℝ) : AngCircle) = ((0 : ℝ) : AngCircle) := by
  rw [AddCircle.coe_period, AddCircle.coe_zero]

theorem bdd_EX04903 {c : AngCircle → ℝ} (hc : Continuous c) : ∃ M : ℝ, ∀ θ, |c θ| ≤ M := by
  obtain ⟨M, hM⟩ :=
    (isCompact_univ : IsCompact (univ : Set AngCircle)).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨M, fun θ => by
    have h := hM θ (mem_univ θ)
    rwa [Real.norm_eq_abs] at h⟩

theorem memLp_mul_bdd_EX04903 {c v : AngCircle → ℝ} {M : ℝ} (hc : Continuous c)
    (hcM : ∀ θ, |c θ| ≤ M) (hv : MemLp v 2 angHaar) :
    MemLp (fun θ => v θ * c θ) 2 angHaar :=
  (memLp_bdd_mul_EX04935 hc hcM hv).ae_eq
    (Filter.Eventually.of_forall fun θ => mul_comm (c θ) (v θ))

theorem intervalCongr_EX04903 {f g : ℝ → ℝ}
    (h : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 (2 * π) → f x = g x) :
    ∫ x in (0:ℝ)..2 * π, f x = ∫ x in (0:ℝ)..2 * π, g x := by
  have hT : (0:ℝ) ≤ 2 * π := by positivity
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_ae measurableSet_Ioo h

theorem prod_interval_EX04903 {u v q : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 (2 * π))
    (hv : AbsolutelyContinuousOnInterval v 0 (2 * π))
    (hq : ContDiff ℝ 1 q) (hu0 : u 0 = u (2 * π)) (hv0 : v 0 = v (2 * π))
    (hq0 : q 0 = q (2 * π)) :
    ∫ x in (0:ℝ)..2 * π, u x * v x * deriv q x =
      -∫ x in (0:ℝ)..2 * π, (deriv u x * v x + u x * deriv v x) * q x := by
  have hqAC : AbsolutelyContinuousOnInterval q 0 (2 * π) :=
    (hq.contDiffOn.mono (subset_univ _)).absolutelyContinuousOnInterval
  have hqc : ContinuousOn q (uIcc 0 (2 * π)) := hq.continuous.continuousOn
  have hq'c : Continuous (deriv q) := hq.continuous_deriv_one
  have hAC : AbsolutelyContinuousOnInterval (fun x => u x * v x) 0 (2 * π) := hu.fun_mul hv
  have hmain : ∫ x in (0:ℝ)..2 * π,
      (deriv (fun y => u y * v y) x * q x + u x * v x * deriv q x) =
      u (2 * π) * v (2 * π) * q (2 * π) - u 0 * v 0 * q 0 :=
    ex049_36_integration_parts_explicit_endpoint_values hAC hqAC
  have hB : u (2 * π) * v (2 * π) * q (2 * π) - u 0 * v 0 * q 0 = 0 := by
    rw [← hu0, ← hv0, ← hq0, sub_self]
  have hdu : IntervalIntegrable (deriv u) volume 0 (2 * π) := hu.intervalIntegrable_deriv
  have hdv : IntervalIntegrable (deriv v) volume 0 (2 * π) := hv.intervalIntegrable_deriv
  have hI1a : IntervalIntegrable (fun x => deriv u x * v x) volume 0 (2 * π) :=
    hdu.mul_continuousOn hv.continuousOn
  have hI1b : IntervalIntegrable (fun x => u x * deriv v x) volume 0 (2 * π) :=
    hdv.continuousOn_mul hu.continuousOn
  have hI1 : IntervalIntegrable (fun x => (deriv u x * v x + u x * deriv v x) * q x) volume
      0 (2 * π) :=
    (hI1a.add hI1b).mul_continuousOn hqc
  have hI2 : IntervalIntegrable (fun x => u x * v x * deriv q x) volume 0 (2 * π) :=
    ((hu.continuousOn.mul hv.continuousOn).mul hq'c.continuousOn).intervalIntegrable
  have hcongr : ∫ x in (0:ℝ)..2 * π,
      (deriv (fun y => u y * v y) x * q x + u x * v x * deriv q x) =
      ∫ x in (0:ℝ)..2 * π,
        ((deriv u x * v x + u x * deriv v x) * q x + u x * v x * deriv q x) :=
    intervalCongr_EX04903 (by
      filter_upwards [deriv_mul_ae_EX04934 hu hv] with x hx hmem
      simp only [hx hmem])
  have hsplit : ∫ x in (0:ℝ)..2 * π,
      ((deriv u x * v x + u x * deriv v x) * q x + u x * v x * deriv q x) =
      (∫ x in (0:ℝ)..2 * π, (deriv u x * v x + u x * deriv v x) * q x) +
        ∫ x in (0:ℝ)..2 * π, u x * v x * deriv q x :=
    intervalIntegral.integral_add hI1 hI2
  linarith

theorem prod_ibp_EX04903 {U V g h ψ : AngCircle → ℝ}
    (hUAC : AbsolutelyContinuousOnInterval (fun s : ℝ => U (s : AngCircle)) 0 (2 * π))
    (hVAC : AbsolutelyContinuousOnInterval (fun s : ℝ => V (s : AngCircle)) 0 (2 * π))
    (hUe : U ((0 : ℝ) : AngCircle) = U ((2 * π : ℝ) : AngCircle))
    (hVe : V ((0 : ℝ) : AngCircle) = V ((2 * π : ℝ) : AngCircle))
    (hUd : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo 0 (2 * π) →
      deriv (fun x : ℝ => U (x : AngCircle)) s = g (s : AngCircle))
    (hVd : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo 0 (2 * π) →
      deriv (fun x : ℝ => V (x : AngCircle)) s = h (s : AngCircle))
    (hψ : IsSmoothAngular ψ) :
    ∫ θ, U θ * V θ * angDeriv ψ θ ∂angHaar = -∫ θ, (g θ * V θ + U θ * h θ) * ψ θ ∂angHaar := by
  have hψs : ContDiff ℝ ∞ (fun s : ℝ => ψ (s : AngCircle)) := hψ
  have hψ1 : ContDiff ℝ 1 (fun s : ℝ => ψ (s : AngCircle)) :=
    hψs.of_le (by exact_mod_cast le_top)
  have hψ0 : ψ ((0 : ℝ) : AngCircle) = ψ ((2 * π : ℝ) : AngCircle) :=
    (congrArg ψ coe_two_pi_EX04903).symm
  have hint : ∫ x in (0:ℝ)..2 * π,
      U (x : AngCircle) * V (x : AngCircle) * deriv (fun t : ℝ => ψ (t : AngCircle)) x =
      -∫ x in (0:ℝ)..2 * π,
        (deriv (fun t : ℝ => U (t : AngCircle)) x * V (x : AngCircle) +
          U (x : AngCircle) * deriv (fun t : ℝ => V (t : AngCircle)) x) * ψ (x : AngCircle) :=
    prod_interval_EX04903 hUAC hVAC hψ1 hUe hVe hψ0
  have hcongr : ∫ x in (0:ℝ)..2 * π,
      (deriv (fun t : ℝ => U (t : AngCircle)) x * V (x : AngCircle) +
        U (x : AngCircle) * deriv (fun t : ℝ => V (t : AngCircle)) x) * ψ (x : AngCircle) =
      ∫ x in (0:ℝ)..2 * π,
        (g (x : AngCircle) * V (x : AngCircle) + U (x : AngCircle) * h (x : AngCircle)) *
          ψ (x : AngCircle) :=
    intervalCongr_EX04903 (by
      filter_upwards [hUd, hVd] with x h1 h2 hmem
      simp only [h1 hmem, h2 hmem])
  have hkey : ∫ x in (0:ℝ)..2 * π,
      U (x : AngCircle) * V (x : AngCircle) * deriv (fun t : ℝ => ψ (t : AngCircle)) x =
      -∫ x in (0:ℝ)..2 * π,
        (g (x : AngCircle) * V (x : AngCircle) + U (x : AngCircle) * h (x : AngCircle)) *
          ψ (x : AngCircle) := by
    rw [hint, hcongr]
  rw [int_circle_EX04903, int_circle_EX04903]
  simp only [angDeriv_coe_EX04903]
  rw [hkey, mul_neg]

theorem prod_weak_EX04903 {u v g h : AngCircle → ℝ}
    (hu : IsAngularWeakDeriv u g) (hv : IsAngularWeakDeriv v h) :
    IsAngularWeakDeriv (fun θ => u θ * v θ) (fun θ => g θ * v θ + u θ * h θ) := by
  obtain ⟨U, hUc, hUae, -, hUAC, hUe, hUd⟩ :=
    ex049_02_angular_h1_has_absolutely_continuous_representative u ⟨g, hu⟩
  obtain ⟨V, hVc, hVae, -, hVAC, hVe, hVd⟩ :=
    ex049_02_angular_h1_has_absolutely_continuous_representative v ⟨h, hv⟩
  obtain ⟨hUd', -⟩ := hUd g hu
  obtain ⟨hVd', -⟩ := hVd h hv
  obtain ⟨MU, hMU⟩ := bdd_EX04903 hUc
  obtain ⟨MV, hMV⟩ := bdd_EX04903 hVc
  have hVmem : MemLp V 2 angHaar := hv.memLp.ae_eq hVae.symm
  have hcore : IsAngularWeakDeriv (fun θ => U θ * V θ) (fun θ => g θ * V θ + U θ * h θ) :=
    { memLp := memLp_bdd_mul_EX04935 hUc hMU hVmem
      memLp_deriv := (memLp_mul_bdd_EX04903 hVc hMV hu.memLp_deriv).add
        (memLp_bdd_mul_EX04935 hUc hMU hv.memLp_deriv)
      ibp := fun ψ hψ => prod_ibp_EX04903 hUAC hVAC hUe hVe hUd' hVd' hψ }
  refine isAngularWeakDeriv_congr_EX04925 ?_ ?_ hcore
  · filter_upwards [hUae, hVae] with θ h1 h2
    simp only [h1, h2]
  · filter_upwards [hUae, hVae] with θ h1 h2
    simp only [h1, h2]

theorem angularH1_prod_EX04903 {u v : AngCircle → ℝ} (hu : AngularH1 u) (hv : AngularH1 v) :
    AngularH1 (fun θ => u θ * v θ) := by
  obtain ⟨g, hg⟩ := hu
  obtain ⟨h, hh⟩ := hv
  exact ⟨_, prod_weak_EX04903 hg hh⟩

theorem sq_weak_EX04903 {v g : AngCircle → ℝ} (hv : IsAngularWeakDeriv v g) :
    IsAngularWeakDeriv (fun θ => v θ ^ 2) (fun θ => g θ * v θ + v θ * g θ) := by
  have e : (fun θ => v θ ^ 2) = fun θ => v θ * v θ := funext fun θ => sq (v θ)
  rw [e]
  exact prod_weak_EX04903 hv hv

theorem sq_ae_EX04903 {V g : AngCircle → ℝ}
    (hVAC : AbsolutelyContinuousOnInterval (fun s : ℝ => V (s : AngCircle)) 0 (2 * π))
    (hVd : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioo 0 (2 * π) →
      deriv (fun x : ℝ => V (x : AngCircle)) s = g (s : AngCircle)) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo 0 (2 * π) →
      deriv (fun y : ℝ => V (y : AngCircle) ^ 2) x =
        g (x : AngCircle) * V (x : AngCircle) + V (x : AngCircle) * g (x : AngCircle) := by
  have e : (fun y : ℝ => V (y : AngCircle) ^ 2) =
      fun y : ℝ => V (y : AngCircle) * V (y : AngCircle) :=
    funext fun y => sq _
  filter_upwards [deriv_mul_ae_EX04934 hVAC hVAC, hVd] with x hx1 hx2 hmem
  rw [e, hx1 hmem, hx2 hmem]

theorem sq_interval_EX04903 {V a : ℝ → ℝ} (ha : ContDiff ℝ 1 a)
    (hV : AbsolutelyContinuousOnInterval V 0 (2 * π)) (hVe : V 0 = V (2 * π))
    (hae : a 0 = a (2 * π)) :
    ∫ x in (0:ℝ)..2 * π, a x * deriv (fun y => V y ^ 2) x =
      -∫ x in (0:ℝ)..2 * π, deriv a x * V x ^ 2 := by
  have h := (ex049_36_integration_parts_explicit_endpoint_values_square_weight ha hV).2
  rw [← hVe, ← hae] at h
  linarith

theorem ibp_EX04903 {a : ℝ → ℝ} {L v g w : AngCircle → ℝ} (ha : ContDiff ℝ 1 a)
    (hLa : ∀ s : ℝ, L (s : AngCircle) = a s)
    (hv : IsAngularWeakDeriv v g) (hw : IsAngularWeakDeriv (fun θ => v θ ^ 2) w) :
    Integrable (fun θ => L θ * w θ) angHaar ∧
      Integrable (fun θ => angDeriv L θ * v θ ^ 2) angHaar ∧
      ∫ θ, L θ * w θ ∂angHaar = -∫ θ, angDeriv L θ * v θ ^ 2 ∂angHaar := by
  have hae : a 0 = a (2 * π) := by
    have h := congrArg L coe_two_pi_EX04903
    rw [hLa, hLa] at h
    exact h.symm
  have hLc : Continuous L := by
    refine continuous_of_coe_EX04935 ?_
    have e : (fun s : ℝ => L (s : AngCircle)) = a := funext hLa
    rw [e]
    exact ha.continuous
  have hLd : ∀ s : ℝ, angDeriv L (s : AngCircle) = deriv a s := angDeriv_coe_EX04935 hLa
  have hDc : Continuous (angDeriv L) := by
    refine continuous_of_coe_EX04935 ?_
    have e : (fun s : ℝ => angDeriv L (s : AngCircle)) = deriv a := funext hLd
    rw [e]
    exact ha.continuous_deriv_one
  obtain ⟨ML, hML⟩ := bdd_EX04903 hLc
  obtain ⟨MD, hMD⟩ := bdd_EX04903 hDc
  have hsq2 : Integrable (fun θ => v θ ^ 2) angHaar := hv.memLp.integrable_sq
  have hI1 : Integrable (fun θ => L θ * w θ) angHaar :=
    (memLp_bdd_mul_EX04935 hLc hML hw.memLp_deriv).integrable one_le_two
  have hmeas : AEStronglyMeasurable (fun θ => angDeriv L θ * v θ ^ 2) angHaar :=
    hDc.aestronglyMeasurable.mul hsq2.aestronglyMeasurable
  have hbnd : ∀ᵐ θ ∂angHaar, ‖angDeriv L θ * v θ ^ 2‖ ≤ MD * v θ ^ 2 := by
    refine Filter.Eventually.of_forall fun θ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (v θ))]
    exact mul_le_mul_of_nonneg_right (hMD θ) (sq_nonneg (v θ))
  have hI2 : Integrable (fun θ => angDeriv L θ * v θ ^ 2) angHaar :=
    Integrable.mono' (hsq2.const_mul MD) hmeas hbnd
  have hw' := sq_weak_EX04903 hv
  have hweq : w =ᵐ[angHaar] fun θ => g θ * v θ + v θ * g θ :=
    angularWeakDeriv_ae_eq_EX04925 hw hw'
  obtain ⟨V, -, hVae, -, hVAC, hVe, hVd⟩ :=
    ex049_02_angular_h1_has_absolutely_continuous_representative v ⟨g, hv⟩
  obtain ⟨hVd', -⟩ := hVd g hv
  have hwV : w =ᵐ[angHaar] fun θ => g θ * V θ + V θ * g θ := by
    filter_upwards [hweq, hVae] with θ h1 h2
    simp only [h1, h2]
  have hsqw : ∫ θ, L θ * w θ ∂angHaar = ∫ θ, L θ * (g θ * V θ + V θ * g θ) ∂angHaar :=
    integral_congr_ae (by
      filter_upwards [hwV] with θ hθ
      simp only [hθ])
  have hVv : ∫ θ, angDeriv L θ * v θ ^ 2 ∂angHaar = ∫ θ, angDeriv L θ * V θ ^ 2 ∂angHaar :=
    integral_congr_ae (by
      filter_upwards [hVae] with θ hθ
      simp only [hθ])
  have hcirc1 : ∫ θ, L θ * (g θ * V θ + V θ * g θ) ∂angHaar =
      (2 * π)⁻¹ * ∫ x in (0:ℝ)..2 * π,
        a x * (g (x : AngCircle) * V (x : AngCircle) + V (x : AngCircle) * g (x : AngCircle)) := by
    rw [int_circle_EX04903]
    simp only [hLa]
  have hcirc2 : ∫ θ, angDeriv L θ * V θ ^ 2 ∂angHaar =
      (2 * π)⁻¹ * ∫ x in (0:ℝ)..2 * π, deriv a x * V (x : AngCircle) ^ 2 := by
    rw [int_circle_EX04903]
    simp only [hLd]
  have hcomp : ∫ x in (0:ℝ)..2 * π,
      a x * (g (x : AngCircle) * V (x : AngCircle) + V (x : AngCircle) * g (x : AngCircle)) =
      ∫ x in (0:ℝ)..2 * π, a x * deriv (fun y : ℝ => V (y : AngCircle) ^ 2) x :=
    intervalCongr_EX04903 (by
      filter_upwards [sq_ae_EX04903 hVAC hVd'] with x hsq' hmem
      rw [hsq' hmem])
  have hsq : ∫ x in (0:ℝ)..2 * π, a x * deriv (fun y : ℝ => V (y : AngCircle) ^ 2) x =
      -∫ x in (0:ℝ)..2 * π, deriv a x * V (x : AngCircle) ^ 2 :=
    sq_interval_EX04903 ha hVAC hVe hae
  refine ⟨hI1, hI2, ?_⟩
  rw [hVv, hsqw, hcirc1, hcirc2, hcomp, hsq]
  ring

theorem ex049_03_angular_products_periodic_integration_parts :
    (∀ u v : AngCircle → ℝ, AngularH1 u → AngularH1 v →
      AngularH1 (fun θ => u θ * v θ) ∧
      ∀ g h : AngCircle → ℝ, IsAngularWeakDeriv u g → IsAngularWeakDeriv v h →
        IsAngularWeakDeriv (fun θ => u θ * v θ) (fun θ => g θ * v θ + u θ * h θ) ∧
        Integrable (fun θ => u θ * v θ) angHaar ∧
        Integrable (fun θ => g θ * v θ + u θ * h θ) angHaar) ∧
    (∀ (a : ℝ → ℝ) (_ha : ContDiff ℝ 1 a) (hper : Function.Periodic a (2 * π))
      (v : AngCircle → ℝ), AngularH1 v →
      AngularH1 (fun θ => (hper.lift : AngCircle → ℝ) θ * v θ) ∧
      ∀ g : AngCircle → ℝ, IsAngularWeakDeriv v g →
        IsAngularWeakDeriv (fun θ => (hper.lift : AngCircle → ℝ) θ * v θ)
            (fun θ => angDeriv (hper.lift : AngCircle → ℝ) θ * v θ +
              (hper.lift : AngCircle → ℝ) θ * g θ) ∧
        Integrable (fun θ => (hper.lift : AngCircle → ℝ) θ * v θ) angHaar ∧
        Integrable (fun θ => angDeriv (hper.lift : AngCircle → ℝ) θ * v θ +
          (hper.lift : AngCircle → ℝ) θ * g θ) angHaar) ∧
    (∀ (a : ℝ → ℝ) (_ha : ContDiff ℝ 1 a) (hper : Function.Periodic a (2 * π))
      (v : AngCircle → ℝ), AngularH1 v →
      AngularH1 (fun θ => v θ ^ 2) ∧
      ∀ w : AngCircle → ℝ, IsAngularWeakDeriv (fun θ => v θ ^ 2) w →
        Integrable (fun θ => (hper.lift : AngCircle → ℝ) θ * w θ) angHaar ∧
        Integrable (fun θ => angDeriv (hper.lift : AngCircle → ℝ) θ * v θ ^ 2) angHaar ∧
        ∫ θ, (hper.lift : AngCircle → ℝ) θ * w θ ∂angHaar =
          -∫ θ, angDeriv (hper.lift : AngCircle → ℝ) θ * v θ ^ 2 ∂angHaar) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v hu hv
    refine ⟨angularH1_prod_EX04903 hu hv, ?_⟩
    intro g h hug hvh
    have hw := prod_weak_EX04903 hug hvh
    exact ⟨hw, (integrable_weak_EX04903 hw).1, (integrable_weak_EX04903 hw).2⟩
  · intro a ha hper v hv
    have hm := ex049_35_periodic_c1_multipliers a ha hper
    refine ⟨hm.2.2.2 v hv, ?_⟩
    intro g hvg
    have hw := hm.2.2.1 v g hvg
    exact ⟨hw, (integrable_weak_EX04903 hw).1, (integrable_weak_EX04903 hw).2⟩
  · intro a ha hper v hv
    obtain ⟨g, hvg⟩ := hv
    refine ⟨⟨_, sq_weak_EX04903 hvg⟩, ?_⟩
    intro w hw
    exact ibp_EX04903 (L := (hper.lift : AngCircle → ℝ)) ha (fun s => hper.lift_coe s) hvg hw

end DGPS.Frontier.EX049
