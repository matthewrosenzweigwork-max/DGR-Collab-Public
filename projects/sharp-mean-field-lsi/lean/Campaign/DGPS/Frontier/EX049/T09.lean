import DGPS.Frontier.EX049.T03
import DGPS.Frontier.EX049.T08
import DGPS.Frontier.EX049.T25

/-!
# EX049.09: Full-H1 ground-state identity

For every real `h ≥ 2` and every real angular `H¹` function `v`, put `w = v √q_h`
(`groundStateConj h v`).  Then, with `m = angHaar`, `μ_h = circleReference h`, `b = (log q_h)'`
and `𝒱_h = groundPot h`:

* `∫ w² dm = ∫ v² dμ_h`,
* `∫ (v')² dμ_h = ∫ ((w')² + 𝒱_h w²) dm`,
* `∫ (w')² dm ≤ ∫ (v')² dμ_h + K h ∫ v² dμ_h` with `K = max 1 C0`, where `C0` is the absolute
  witness of the EX037 bound `𝒱_h ≥ h² sin² / 4 - C0 h`.

The proof is the global square completion: `w' = √q (v' + b v / 2)` almost everywhere, so
`(v')² q = (w' - b w / 2)²`, and the periodic integration by parts of EX049.03 turns the cross
term `-b w w'` into `b' w² / 2`.  No smoothness of `v` is used.

## Provides

* `DGPS.Frontier.EX049.ex049_09_full_h1_ground_state_identity`: the three conclusions above, for
  an EX037 witness `C0` selected inside the statement, for every `h ≥ 2`, every `v` with
  `AngularH1 v`, every weak derivative `v'` of `v` and every weak derivative `w'` of the conjugate;
  the conjugate itself is `AngularH1`.
* `DGPS.Frontier.EX049.ex049_09_full_h1_ground_state_identity_of_witness`: the same statement for
  an arbitrary `C0` satisfying the EX037 bound (no positivity of `C0` is needed).
* `DGPS.Frontier.EX049.ex049_09_full_h1_ground_state_identity_weak`: the explicit weak derivative
  `(b / 2) √q v + √q v'` of `w` for every `h > 0`.
* `DGPS.Frontier.EX049.ex049_09_full_h1_ground_state_identity_integrable`: every integral in the
  three conclusions is an integral of an integrable function, for every `h > 0`.

## R5 notes

* The weak derivatives are universally quantified: `v'` ranges over every `v'` with
  `IsAngularWeakDeriv v v'` and `w'` over every `w'` with `IsAngularWeakDeriv w w'`, so the
  statement does not depend on a choice of representative.  Existence of `w'` is the conjunct
  `AngularH1 (groundStateConj h v)`; existence of `v'` is the hypothesis `AngularH1 v`.
* `M_h(v)` is read as `∫ v² ∂circleReference h` and `E_h(v)` as `∫ (v')² ∂circleReference h`;
  `∫ ... dm` is the integral against `angHaar`.
* `w = v √q_h` is `groundStateConj h v θ = v θ * Real.sqrt (qAng h θ)` (the factor `√q` stands on
  the right).
* `𝒱_h`, a function of the lifted angle, is read on the circle as `θ ↦ groundPot h (angSec θ)`,
  the reading fixed by EX049.25; it is the circle function `b² / 4 + b' / 2` with
  `b θ = driftB h (angSec θ)` and `b' = angDeriv b`.
* The constant: `C0` is existentially quantified in `ex049_09_full_h1_ground_state_identity`
  together with its defining EX037 inequality
  `h² sin² t / 4 - C0 h ≤ groundPot h t` (all `h ≥ 2`, all real `t`), and `K` is `max 1 C0`.
  The positivity `0 < C0` is part of the conjunction.  The witness comes from
  `DGPS.Examples.engineered_drift_and_ground_potential`; the statement is also proved for every
  `C0` that satisfies the inequality.
* The first two conclusions and the weak-derivative formula need only `0 < h`; the domain `h ≥ 2`
  of the statement is used only through the EX037 lower bound of `𝒱_h`.
* The numerical lower bound of the potential enters only through
  `-(K h) ≤ groundPot h (angSec θ)`, obtained from the EX037 bound together with
  `sin² ≥ 0` and `C0 ≤ K`.
* No smoothness of `v` is assumed or used.  The cited EX038 smooth identity is not needed.
-/

open MeasureTheory Real Set Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.AngularNormalization DGPS.Circle.StationaryFlux DGPS.Examples.EngineeredRankOne
  DGPS.Examples.EngineeredGroundState

namespace DGPS.Frontier.EX049

/-! ### The ground state `√q_h` as a smooth multiplier -/

lemma angDeriv_sqrt_EX04909 (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    angDeriv (fun θ : AngCircle => Real.sqrt (qAng h θ)) θ =
      driftB h (angSec θ) / 2 * Real.sqrt (qAng h θ) := by
  have h1 := (hasDerivAt_sqrtQ h hh (angSec θ)).deriv
  have e : sqrtQ h (angSec θ) = Real.sqrt (qAng h θ) := by
    unfold sqrtQ
    exact congrArg (fun x : AngCircle => Real.sqrt (qAng h x)) (coe_angSec θ)
  unfold angDeriv
  show deriv (sqrtQ h) (angSec θ) = _
  rw [h1, e]

/-- The weak derivative of `w = v √q_h`: `w' = (b / 2) √q v + √q v'`. -/
theorem ex049_09_full_h1_ground_state_identity_weak (h : ℝ) (hh : 0 < h)
    {v v' : AngCircle → ℝ} (hv : IsAngularWeakDeriv v v') :
    IsAngularWeakDeriv (groundStateConj h v)
      (fun θ => driftB h (angSec θ) / 2 * Real.sqrt (qAng h θ) * v θ +
        Real.sqrt (qAng h θ) * v' θ) := by
  have hF : ContDiff ℝ 1 (fun s : ℝ => (fun θ : AngCircle => Real.sqrt (qAng h θ)) (s : AngCircle)) :=
    (contDiff_sqrtQ h hh).of_le (by exact_mod_cast le_top)
  have h1 := (mul_weak_EX04942 (F := fun θ : AngCircle => Real.sqrt (qAng h θ)) hF).1 v v' hv
  have e1 : groundStateConj h v = fun θ => Real.sqrt (qAng h θ) * v θ :=
    funext fun θ => mul_comm _ _
  rw [e1]
  convert h1 using 1
  funext θ
  rw [angDeriv_sqrt_EX04909 h hh]

/-! ### Change of density -/

lemma mass_EX04909 (h : ℝ) (hh : 0 < h) (v : AngCircle → ℝ) :
    ∫ θ, groundStateConj h v θ ^ 2 ∂angHaar = ∫ θ, v θ ^ 2 ∂circleReference h := by
  rw [integral_circleReference h hh]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  show (v θ * Real.sqrt (qAng h θ)) ^ 2 = v θ ^ 2 * qAng h θ
  rw [mul_pow, Real.sq_sqrt (qAng_pos h hh θ).le]

lemma conj_energy_EX04909 (h : ℝ) (hh : 0 < h) {v v' w' : AngCircle → ℝ}
    (hv : IsAngularWeakDeriv v v') (hw : IsAngularWeakDeriv (groundStateConj h v) w') :
    ∫ θ, v' θ ^ 2 ∂circleReference h =
      ∫ θ, (w' θ - driftB h (angSec θ) / 2 * groundStateConj h v θ) ^ 2 ∂angHaar := by
  have hae := angularWeakDeriv_ae_eq_EX04925 hw (ex049_09_full_h1_ground_state_identity_weak h hh hv)
  rw [integral_circleReference h hh]
  refine integral_congr_ae ?_
  filter_upwards [hae] with θ hθ
  rw [hθ]
  have hs : Real.sqrt (qAng h θ) ^ 2 = qAng h θ := Real.sq_sqrt (qAng_pos h hh θ).le
  show v' θ ^ 2 * qAng h θ = (driftB h (angSec θ) / 2 * Real.sqrt (qAng h θ) * v θ +
    Real.sqrt (qAng h θ) * v' θ - driftB h (angSec θ) / 2 * (v θ * Real.sqrt (qAng h θ))) ^ 2
  linear_combination (-(v' θ ^ 2)) * hs

/-! ### Square completion with the periodic integration by parts -/

lemma continuous_drift_EX04909 (h : ℝ) (hh : 0 < h) :
    Continuous (fun θ : AngCircle => driftB h (angSec θ)) := by
  refine continuous_of_coe_EX04935 ?_
  have e : (fun s : ℝ => driftB h (angSec (s : AngCircle))) = driftB h :=
    funext (driftB_angSec_EX04925 h hh)
  rw [e]
  exact (contDiff_driftB h hh).continuous

lemma groundPot_circle_EX04909 (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    groundPot h (angSec θ) = driftB h (angSec θ) ^ 2 / 4 +
      angDeriv (fun θ : AngCircle => driftB h (angSec θ)) θ / 2 := by
  unfold groundPot
  rw [angDeriv_driftB_EX04925 h hh]

lemma square_completion_EX04909 (h : ℝ) (hh : 0 < h) {w w' : AngCircle → ℝ}
    (hw : IsAngularWeakDeriv w w') :
    Integrable (fun θ => groundPot h (angSec θ) * w θ ^ 2) angHaar ∧
      ∫ θ, (w' θ - driftB h (angSec θ) / 2 * w θ) ^ 2 ∂angHaar =
        ∫ θ, (w' θ ^ 2 + groundPot h (angSec θ) * w θ ^ 2) ∂angHaar := by
  have ha : ContDiff ℝ 1 (driftB h) := (contDiff_driftB h hh).of_le (by exact_mod_cast le_top)
  obtain ⟨hI2, hI3, hibp⟩ := ibp_EX04903 (a := driftB h) (L := fun θ => driftB h (angSec θ))
    (v := w) (g := w') (w := fun θ => w' θ * w θ + w θ * w' θ) ha
    (driftB_angSec_EX04925 h hh) hw (sq_weak_EX04903 hw)
  obtain ⟨M, hM⟩ := bdd_EX04903 (continuous_drift_EX04909 h hh)
  have hI4 : Integrable (fun θ => (w θ * driftB h (angSec θ)) ^ 2) angHaar :=
    (memLp_mul_bdd_EX04903 (continuous_drift_EX04909 h hh) hM hw.memLp).integrable_sq
  have hI1 : Integrable (fun θ => w' θ ^ 2) angHaar := hw.memLp_deriv.integrable_sq
  have hV : Integrable (fun θ => groundPot h (angSec θ) * w θ ^ 2) angHaar := by
    have e : (fun θ => groundPot h (angSec θ) * w θ ^ 2) = fun θ =>
        (1 / 4) * (w θ * driftB h (angSec θ)) ^ 2 +
          (1 / 2) * (angDeriv (fun θ : AngCircle => driftB h (angSec θ)) θ * w θ ^ 2) := by
      funext θ
      rw [groundPot_circle_EX04909 h hh θ]
      ring
    rw [e]
    exact (hI4.const_mul _).add (hI3.const_mul _)
  refine ⟨hV, ?_⟩
  have key : ∀ θ : AngCircle, (w' θ - driftB h (angSec θ) / 2 * w θ) ^ 2 =
      (w' θ ^ 2 + groundPot h (angSec θ) * w θ ^ 2) -
        (1 / 2) * (driftB h (angSec θ) * (w' θ * w θ + w θ * w' θ) +
          angDeriv (fun θ : AngCircle => driftB h (angSec θ)) θ * w θ ^ 2) := by
    intro θ
    rw [groundPot_circle_EX04909 h hh θ]
    ring
  have hG : ∫ θ, (driftB h (angSec θ) * (w' θ * w θ + w θ * w' θ) +
      angDeriv (fun θ : AngCircle => driftB h (angSec θ)) θ * w θ ^ 2) ∂angHaar = 0 := by
    rw [integral_add hI2 hI3, hibp]
    ring
  have hA : Integrable (fun θ => w' θ ^ 2 + groundPot h (angSec θ) * w θ ^ 2) angHaar := hI1.add hV
  have hB : Integrable (fun θ => (1 / 2) * (driftB h (angSec θ) * (w' θ * w θ + w θ * w' θ) +
      angDeriv (fun θ : AngCircle => driftB h (angSec θ)) θ * w θ ^ 2)) angHaar :=
    (hI2.add hI3).const_mul _
  calc ∫ θ, (w' θ - driftB h (angSec θ) / 2 * w θ) ^ 2 ∂angHaar
      = ∫ θ, ((w' θ ^ 2 + groundPot h (angSec θ) * w θ ^ 2) -
          (1 / 2) * (driftB h (angSec θ) * (w' θ * w θ + w θ * w' θ) +
            angDeriv (fun θ : AngCircle => driftB h (angSec θ)) θ * w θ ^ 2)) ∂angHaar :=
        integral_congr_ae (Eventually.of_forall key)
    _ = ∫ θ, (w' θ ^ 2 + groundPot h (angSec θ) * w θ ^ 2) ∂angHaar -
          (1 / 2) * ∫ θ, (driftB h (angSec θ) * (w' θ * w θ + w θ * w' θ) +
            angDeriv (fun θ : AngCircle => driftB h (angSec θ)) θ * w θ ^ 2) ∂angHaar := by
        rw [integral_sub hA hB, integral_const_mul]
    _ = ∫ θ, (w' θ ^ 2 + groundPot h (angSec θ) * w θ ^ 2) ∂angHaar := by
        rw [hG]
        ring

/-! ### The core statement for a fixed potential bound -/

lemma core_EX04909 (h : ℝ) (hh : 0 < h) (K : ℝ)
    (hK : ∀ θ : AngCircle, -(K * h) ≤ groundPot h (angSec θ))
    {v v' w' : AngCircle → ℝ} (hv : IsAngularWeakDeriv v v')
    (hw : IsAngularWeakDeriv (groundStateConj h v) w') :
    ∫ θ, v' θ ^ 2 ∂circleReference h =
        ∫ θ, (w' θ ^ 2 + groundPot h (angSec θ) * groundStateConj h v θ ^ 2) ∂angHaar ∧
      ∫ θ, w' θ ^ 2 ∂angHaar ≤
        ∫ θ, v' θ ^ 2 ∂circleReference h + K * h * ∫ θ, v θ ^ 2 ∂circleReference h := by
  obtain ⟨hV, hsc⟩ := square_completion_EX04909 h hh hw
  have hE := (conj_energy_EX04909 h hh hv hw).trans hsc
  refine ⟨hE, ?_⟩
  rw [hE, ← mass_EX04909 h hh v]
  have hw2 : Integrable (fun θ => groundStateConj h v θ ^ 2) angHaar := hw.memLp.integrable_sq
  have hw'2 : Integrable (fun θ => w' θ ^ 2) angHaar := hw.memLp_deriv.integrable_sq
  have hmono : ∫ θ, (w' θ ^ 2 + (-(K * h)) * groundStateConj h v θ ^ 2) ∂angHaar ≤
      ∫ θ, (w' θ ^ 2 + groundPot h (angSec θ) * groundStateConj h v θ ^ 2) ∂angHaar :=
    integral_mono (hw'2.add (hw2.const_mul _)) (hw'2.add hV) fun θ => by
      have := mul_le_mul_of_nonneg_right (hK θ) (sq_nonneg (groundStateConj h v θ))
      linarith
  have hsplit : ∫ θ, (w' θ ^ 2 + (-(K * h)) * groundStateConj h v θ ^ 2) ∂angHaar =
      ∫ θ, w' θ ^ 2 ∂angHaar + (-(K * h)) * ∫ θ, groundStateConj h v θ ^ 2 ∂angHaar := by
    rw [integral_add hw'2 (hw2.const_mul _), integral_const_mul]
  linarith

/-! ### Public statements -/

/-- EX049.09 for an arbitrary witness `C0` of the EX037 lower bound; `K = max 1 C0`. -/
theorem ex049_09_full_h1_ground_state_identity_of_witness (C0 : ℝ)
    (hC0 : ∀ h : ℝ, 2 ≤ h → ∀ t : ℝ, h ^ 2 * Real.sin t ^ 2 / 4 - C0 * h ≤ groundPot h t)
    (h : ℝ) (hh : 2 ≤ h) (v : AngCircle → ℝ) (hv : AngularH1 v) :
    AngularH1 (groundStateConj h v) ∧
      ∀ v' w' : AngCircle → ℝ, IsAngularWeakDeriv v v' →
        IsAngularWeakDeriv (groundStateConj h v) w' →
        ∫ θ, groundStateConj h v θ ^ 2 ∂angHaar = ∫ θ, v θ ^ 2 ∂circleReference h ∧
        ∫ θ, v' θ ^ 2 ∂circleReference h =
          ∫ θ, (w' θ ^ 2 + groundPot h (angSec θ) * groundStateConj h v θ ^ 2) ∂angHaar ∧
        ∫ θ, w' θ ^ 2 ∂angHaar ≤
          ∫ θ, v' θ ^ 2 ∂circleReference h +
            max 1 C0 * h * ∫ θ, v θ ^ 2 ∂circleReference h := by
  have hh0 : 0 < h := by linarith
  refine ⟨?_, fun v' w' hv' hw' => ?_⟩
  · obtain ⟨v', hv'⟩ := hv
    exact ⟨_, ex049_09_full_h1_ground_state_identity_weak h hh0 hv'⟩
  · have hK : ∀ θ : AngCircle, -(max 1 C0 * h) ≤ groundPot h (angSec θ) := by
      intro θ
      have h1 := hC0 h hh (angSec θ)
      have h2 : 0 ≤ h ^ 2 * Real.sin (angSec θ) ^ 2 / 4 := by positivity
      have h3 : C0 * h ≤ max 1 C0 * h := mul_le_mul_of_nonneg_right (le_max_right _ _) hh0.le
      linarith
    obtain ⟨h2, h3⟩ := core_EX04909 h hh0 (max 1 C0) hK hv' hw'
    exact ⟨mass_EX04909 h hh0 v, h2, h3⟩

/-- EX049.09: full-H1 ground-state identity.  For the absolute EX037 witness `C0` (selected
inside the statement) and `K = max 1 C0`, every `h ≥ 2` and every angular `H¹` function `v`, with
`w = v √q_h`: `∫ w² dm = M_h(v)`, `E_h(v) = ∫ ((w')² + 𝒱_h w²) dm` and
`∫ (w')² dm ≤ E_h(v) + K h M_h(v)`. -/
theorem ex049_09_full_h1_ground_state_identity :
    ∃ C0 : ℝ, 0 < C0 ∧
      (∀ h : ℝ, 2 ≤ h → ∀ t : ℝ, h ^ 2 * Real.sin t ^ 2 / 4 - C0 * h ≤ groundPot h t) ∧
      ∀ h : ℝ, 2 ≤ h → ∀ v : AngCircle → ℝ, AngularH1 v →
        AngularH1 (groundStateConj h v) ∧
          ∀ v' w' : AngCircle → ℝ, IsAngularWeakDeriv v v' →
            IsAngularWeakDeriv (groundStateConj h v) w' →
            ∫ θ, groundStateConj h v θ ^ 2 ∂angHaar = ∫ θ, v θ ^ 2 ∂circleReference h ∧
            ∫ θ, v' θ ^ 2 ∂circleReference h =
              ∫ θ, (w' θ ^ 2 + groundPot h (angSec θ) * groundStateConj h v θ ^ 2) ∂angHaar ∧
            ∫ θ, w' θ ^ 2 ∂angHaar ≤
              ∫ θ, v' θ ^ 2 ∂circleReference h +
                max 1 C0 * h * ∫ θ, v θ ^ 2 ∂circleReference h := by
  obtain ⟨C, hC, hCb⟩ := DGPS.Examples.engineered_drift_and_ground_potential
  have hbound : ∀ h : ℝ, 2 ≤ h → ∀ t : ℝ,
      h ^ 2 * Real.sin t ^ 2 / 4 - C * h ≤ groundPot h t := fun h hh t => (hCb h hh t).2.2
  exact ⟨C, hC, hbound, fun h hh v hv =>
    ex049_09_full_h1_ground_state_identity_of_witness C hbound h hh v hv⟩

/-- Every integral in the three conclusions is the integral of an integrable function. -/
theorem ex049_09_full_h1_ground_state_identity_integrable (h : ℝ) (hh : 0 < h)
    {v v' w' : AngCircle → ℝ} (hv : IsAngularWeakDeriv v v')
    (hw : IsAngularWeakDeriv (groundStateConj h v) w') :
    Integrable (fun θ => v θ ^ 2) (circleReference h) ∧
      Integrable (fun θ => v' θ ^ 2) (circleReference h) ∧
      Integrable (fun θ => groundStateConj h v θ ^ 2) angHaar ∧
      Integrable (fun θ => w' θ ^ 2) angHaar ∧
      Integrable (fun θ => groundPot h (angSec θ) * groundStateConj h v θ ^ 2) angHaar :=
  ⟨((memLp_circleReference_iff_EX04925 h hh v).2 hv.memLp).integrable_sq,
    ((memLp_circleReference_iff_EX04925 h hh v').2 hv.memLp_deriv).integrable_sq,
    hw.memLp.integrable_sq, hw.memLp_deriv.integrable_sq,
    (square_completion_EX04909 h hh hw).1⟩

end DGPS.Frontier.EX049
