import SharpSymmetricLSI.Paper.CosineGenerator

/-!
# The diagonal term of Lemma 3.7: the one-dimensional inequality (Phase 3, lane C)

For smooth periodic `u`, `ψ` on the circle (an index type with one element) with
`sup ψ - inf ψ ≤ κ'`:
`a e^{-κ'} ∫ e^{-ψ} (u')² ≤ ∫ e^{-ψ} ((u'')² + ψ'' (u')²)` (`diag_1d`), the inequality of
Step 3 of the proof of Lemma 3.7 for one fibre. Route: the one-dimensional Bochner identity
`∫ e^{-ψ}(Au)² = ∫ e^{-ψ}((u'')² + ψ''(u')²)`, `Au = u'' - ψ'u'`; then
`∫ e^{-ψ}(u')² = -∫ e^{-ψ}(Au)(u - c)`, the weighted Poincaré inequality (Haar Poincaré and
density comparison) and `-xy ≤ tx²/2 + y²/(2t)` (in place of Cauchy–Schwarz).
-/

open MeasureTheory Set Filter
open scoped Real ContDiff

namespace SharpLSI

section OneD

variable {η : Type*} [Fintype η] [DecidableEq η]

/-- A continuous periodic function attains its maximum and minimum. -/
theorem periodic_max_min {Φ : (η → ℝ) → ℝ} (hc : Continuous Φ) (hp : IsPer Φ) :
    ∃ a b, ∀ x, Φ b ≤ Φ x ∧ Φ x ≤ Φ a := by
  have hK : IsCompact (univ.pi fun _ : η => Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hne : (univ.pi fun _ : η => Icc (0 : ℝ) 1).Nonempty :=
    ⟨0, fun i _ => ⟨le_rfl, zero_le_one⟩⟩
  obtain ⟨a, -, ha⟩ := hK.exists_isMaxOn hne hc.continuousOn
  obtain ⟨b, -, hb⟩ := hK.exists_isMinOn hne hc.continuousOn
  refine ⟨a, b, fun x => ?_⟩
  have hx : x = (fun i => Int.fract (x i)) + intVec (fun i => ⌊x i⌋) := by
    funext i
    simp only [Pi.add_apply, intVec]
    exact (Int.fract_add_floor (x i)).symm
  have hmem : (fun i => Int.fract (x i)) ∈ univ.pi fun _ : η => Icc (0 : ℝ) 1 :=
    fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  rw [hx, hp]
  exact ⟨hb hmem, ha hmem⟩

theorem Dk_sub_const {u : (η → ℝ) → ℝ} (c : ℝ) (k : η) (x : η → ℝ) :
    Dk (fun x => u x - c) k x = Dk u k x := by
  simp only [Dk, fderiv_sub_const]

/-- The one-dimensional inequality of Step 3 of Lemma 3.7. -/
theorem diag_1d [Unique η] {u ψ : (η → ℝ) → ℝ} (hu : ContDiff ℝ ∞ u) (hψ : ContDiff ℝ ∞ ψ)
    (pu : IsPer u) (pψ : IsPer ψ) {κ' : ℝ} (hosc : ∀ a b, ψ a - ψ b ≤ κ') :
    4 * π ^ 2 * Real.exp (-κ') *
        ∫ y, Real.exp (-ψ (secT y)) * Dk u default (secT y) ^ 2 ≤
      ∫ y, Real.exp (-ψ (secT y)) * (Dk (Dk u default) default (secT y) ^ 2 +
        Dk (Dk ψ default) default (secT y) * Dk u default (secT y) ^ 2) := by
  set q : η := default
  have hDu := contDiff_Dk hu q
  have hD2u := contDiff_Dk hDu q
  have hD3u := contDiff_Dk hD2u q
  have hDψ := contDiff_Dk hψ q
  have hD2ψ := contDiff_Dk hDψ q
  have pDu := pu.Dk q
  have pD2u := pDu.Dk q
  have pD3u := pD2u.Dk q
  have pDψ := pψ.Dk q
  have pD2ψ := pDψ.Dk q
  have hE : Continuous fun x => Real.exp (-ψ x) := Real.continuous_exp.comp hψ.continuous.neg
  have pE : IsPer fun x => Real.exp (-ψ x) := fun m x => by simp only [pψ m x]
  set Au : (η → ℝ) → ℝ := fun x => Dk (Dk u q) q x - Dk ψ q x * Dk u q x with hAu
  have hA : ContDiff ℝ ∞ Au := hD2u.sub (hDψ.mul hDu)
  have pA : IsPer Au := fun m x => by simp only [hAu, pD2u m x, pDψ m x, pDu m x]
  have hDA : ∀ x, Dk Au q x = Dk (Dk (Dk u q) q) q x -
      (Dk (Dk ψ q) q x * Dk u q x + Dk ψ q x * Dk (Dk u q) q x) := by
    intro x
    have d1 := (hD2u.differentiable (by simp)) x
    have d2 := (hDψ.differentiable (by simp)) x
    have d3 := (hDu.differentiable (by simp)) x
    show fderiv ℝ Au x (Pi.single q 1) = _
    rw [hAu, fderiv_fun_sub d1 (by exact d2.mul d3 : DifferentiableAt ℝ
      (fun y => Dk ψ q y * Dk u q y) x), fderiv_fun_mul d2 d3]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Dk]
    ring
  have I : ∀ {Φ : (η → ℝ) → ℝ}, Continuous Φ → IsPer Φ →
      Integrable (fun y => Φ (secT y)) volume := fun hc hp => integrable_secT hc hp
  -- notation for the integrals
  set e : UnitAddTorus η → ℝ := fun y => Real.exp (-ψ (secT y)) with he
  have he0 : ∀ y, 0 < e y := fun y => Real.exp_pos _
  -- Step 1: the Bochner identity
  have ibp1 := ibp_weighted hu hA hψ pu pA pψ q
  have ibp2 := ibp_weighted hDu hDu hψ pDu pDu pψ q
  have iJ1 : Integrable (fun y => e y * Dk (Dk u q) q (secT y) ^ 2) volume :=
    I (Φ := fun x => Real.exp (-ψ x) * Dk (Dk u q) q x ^ 2) (hE.mul (hD2u.continuous.pow 2))
      (fun m x => by simp only [pψ m x, pD2u m x])
  have iJ2 : Integrable (fun y => e y * (Dk (Dk ψ q) q (secT y) * Dk u q (secT y) ^ 2)) volume :=
    I (Φ := fun x => Real.exp (-ψ x) * (Dk (Dk ψ q) q x * Dk u q x ^ 2))
      (hE.mul (hD2ψ.continuous.mul (hDu.continuous.pow 2)))
      (fun m x => by simp only [pψ m x, pD2ψ m x, pDu m x])
  have iJ3 : Integrable (fun y => e y * ((Dk (Dk (Dk u q) q) q (secT y) -
      Dk ψ q (secT y) * Dk (Dk u q) q (secT y)) * Dk u q (secT y))) volume :=
    I (Φ := fun x => Real.exp (-ψ x) * ((Dk (Dk (Dk u q) q) q x - Dk ψ q x * Dk (Dk u q) q x) *
      Dk u q x))
      (hE.mul ((hD3u.continuous.sub (hDψ.continuous.mul hD2u.continuous)).mul hDu.continuous))
      (fun m x => by simp only [pψ m x, pD3u m x, pDψ m x, pD2u m x, pDu m x])
  have hJ4 : ∫ y, e y * (Dk u q (secT y) * Dk Au q (secT y)) =
      (∫ y, e y * ((Dk (Dk (Dk u q) q) q (secT y) - Dk ψ q (secT y) * Dk (Dk u q) q (secT y)) *
        Dk u q (secT y))) - ∫ y, e y * (Dk (Dk ψ q) q (secT y) * Dk u q (secT y) ^ 2) := by
    rw [← integral_sub iJ3 iJ2]
    congr 1; funext y; rw [hDA]; ring
  have hB : ∫ y, e y * (Au (secT y) * Au (secT y)) =
      ∫ y, e y * (Dk (Dk u q) q (secT y) ^ 2 +
        Dk (Dk ψ q) q (secT y) * Dk u q (secT y) ^ 2) := by
    have h1 : ∫ y, e y * (Au (secT y) * Au (secT y)) =
        -∫ y, e y * (Dk u q (secT y) * Dk Au q (secT y)) := ibp1
    have h2 : ∫ y, e y * ((Dk (Dk (Dk u q) q) q (secT y) -
        Dk ψ q (secT y) * Dk (Dk u q) q (secT y)) * Dk u q (secT y)) =
        -∫ y, e y * Dk (Dk u q) q (secT y) ^ 2 := by
      rw [ibp2]; congr 2; funext y; ring
    have hs : ∫ y, e y * (Dk (Dk u q) q (secT y) ^ 2 +
        Dk (Dk ψ q) q (secT y) * Dk u q (secT y) ^ 2) =
        (∫ y, e y * Dk (Dk u q) q (secT y) ^ 2) +
          ∫ y, e y * (Dk (Dk ψ q) q (secT y) * Dk u q (secT y) ^ 2) := by
      rw [← integral_add iJ1 iJ2]; congr 1; funext y; ring
    rw [h1, hJ4, h2, hs]
    ring
  -- Step 2: `∫ e (u')² = -∫ e (Au)(u - c)`
  have iE : Integrable e volume := I (Φ := fun x => Real.exp (-ψ x)) hE pE
  have iEu : Integrable (fun y => e y * u (secT y)) volume :=
    I (Φ := fun x => Real.exp (-ψ x) * u x) (hE.mul hu.continuous)
      (fun m x => by simp only [pψ m x, pu m x])
  have hZ : 0 < ∫ y, e y := integral_exp_pos iE
  set c := (∫ y, e y * u (secT y)) / ∫ y, e y with hc
  have hEu : ∫ y, e y * u (secT y) = c * ∫ y, e y := by rw [hc, div_mul_cancel₀ _ hZ.ne']
  have pw : IsPer (fun x => u x - c) := fun m x => by simp only [pu m x]
  have ibp3 := ibp_weighted hu (hu.sub contDiff_const) hψ pu pw pψ q
  simp_rw [Dk_sub_const] at ibp3
  set I1 := ∫ y, e y * Dk u q (secT y) ^ 2 with hI1
  have hI : I1 = -∫ y, e y * (Au (secT y) * (u (secT y) - c)) := by
    rw [show ∫ y, e y * (Au (secT y) * (u (secT y) - c)) =
      -∫ y, e y * (Dk u q (secT y) * Dk u q (secT y)) from ibp3, neg_neg, hI1]
    congr 1; funext y; ring
  -- Step 3: `-xy ≤ t x²/2 + y²/(2t)`
  set t := Real.exp κ' / (4 * π ^ 2) with ht
  have ht0 : 0 < t := by positivity
  have iA2 : Integrable (fun y => e y * (Au (secT y) * Au (secT y))) volume :=
    I (Φ := fun x => Real.exp (-ψ x) * (Au x * Au x)) (hE.mul (hA.continuous.mul hA.continuous))
      (fun m x => by simp only [pψ m x, pA m x])
  have iV : Integrable (fun y => e y * (u (secT y) - c) ^ 2) volume :=
    I (Φ := fun x => Real.exp (-ψ x) * (u x - c) ^ 2) (hE.mul ((hu.continuous.sub
      continuous_const).pow 2)) (fun m x => by simp only [pψ m x, pu m x])
  have iAw : Integrable (fun y => e y * (Au (secT y) * (u (secT y) - c))) volume :=
    I (Φ := fun x => Real.exp (-ψ x) * (Au x * (u x - c))) (hE.mul (hA.continuous.mul
      (hu.continuous.sub continuous_const))) (fun m x => by simp only [pψ m x, pA m x, pu m x])
  set B := ∫ y, e y * (Au (secT y) * Au (secT y)) with hBdef
  set V := ∫ y, e y * (u (secT y) - c) ^ 2 with hVdef
  have hstep3 : I1 ≤ t / 2 * B + 1 / (2 * t) * V := by
    have hs : ∫ y, (t / 2 * (e y * (Au (secT y) * Au (secT y))) +
        1 / (2 * t) * (e y * (u (secT y) - c) ^ 2)) = t / 2 * B + 1 / (2 * t) * V := by
      rw [integral_add (iA2.const_mul _) (iV.const_mul _), integral_const_mul, integral_const_mul]
    rw [hI, ← integral_neg, ← hs]
    refine integral_mono iAw.neg ((iA2.const_mul _).add (iV.const_mul _)) fun y => ?_
    have key : t / 2 * (e y * (Au (secT y) * Au (secT y))) +
        1 / (2 * t) * (e y * (u (secT y) - c) ^ 2) - -(e y * (Au (secT y) * (u (secT y) - c))) =
        e y * (t * Au (secT y) + (u (secT y) - c)) ^ 2 / (2 * t) := by
      field_simp; ring
    have : 0 ≤ e y * (t * Au (secT y) + (u (secT y) - c)) ^ 2 / (2 * t) := by
      have := he0 y; positivity
    simp only [Pi.neg_apply]
    linarith
  -- Step 4: the weighted Poincaré inequality `V ≤ t I1`
  obtain ⟨xa, xb, hab⟩ := periodic_max_min hψ.continuous pψ
  set Emax := Real.exp (-ψ xb)
  set Emin := Real.exp (-ψ xa)
  have hEmax : ∀ y, e y ≤ Emax := fun y =>
    Real.exp_le_exp.mpr (neg_le_neg (hab (secT y)).1)
  have hEmin : ∀ y, Emin ≤ e y := fun y =>
    Real.exp_le_exp.mpr (neg_le_neg (hab (secT y)).2)
  have hEmin0 : 0 < Emin := Real.exp_pos _
  set c0 := ∫ y, u (secT y) with hc0
  have iu : Integrable (fun y => u (secT y)) volume := I hu.continuous pu
  have iU2 : Integrable (fun y => (u (secT y) - c0) ^ 2) volume :=
    I (Φ := fun x => (u x - c0) ^ 2) ((hu.continuous.sub continuous_const).pow 2)
      (fun m x => by simp only [pu m x])
  have iV0 : Integrable (fun y => e y * (u (secT y) - c0) ^ 2) volume :=
    I (Φ := fun x => Real.exp (-ψ x) * (u x - c0) ^ 2) (hE.mul ((hu.continuous.sub
      continuous_const).pow 2)) (fun m x => by simp only [pψ m x, pu m x])
  -- (a) the weighted mean minimizes
  have ha : V ≤ ∫ y, e y * (u (secT y) - c0) ^ 2 := by
    have hd : (∫ y, e y * (u (secT y) - c0) ^ 2) - V = (c - c0) ^ 2 * ∫ y, e y := by
      rw [hVdef, ← integral_sub iV0 iV]
      have : ∀ y, e y * (u (secT y) - c0) ^ 2 - e y * (u (secT y) - c) ^ 2 =
          (c - c0) * (2 * (e y * u (secT y)) - (c + c0) * e y) := fun y => by ring
      simp_rw [this]
      rw [integral_const_mul, integral_sub (iEu.const_mul 2) (iE.const_mul _), integral_const_mul,
        integral_const_mul, hEu]
      ring
    have : 0 ≤ (c - c0) ^ 2 * ∫ y, e y := by positivity
    linarith
  -- (b) density bound
  have hb : ∫ y, e y * (u (secT y) - c0) ^ 2 ≤ Emax * ∫ y, (u (secT y) - c0) ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono iV0 (iU2.const_mul _) fun y =>
      mul_le_mul_of_nonneg_right (hEmax y) (sq_nonneg _)
  -- (c) the Haar Poincaré inequality
  have hcP : 4 * π ^ 2 * ∫ y, (u (secT y) - c0) ^ 2 ≤ ∫ y, Dk u q (secT y) ^ 2 := by
    set ut : UnitAddTorus η → ℝ := fun y => u (secT y) with hutdef
    have hut : ut ∘ liftT = u := funext pu.secT_liftT
    have hw := isWeakGrad_of_contDiff (f := ut) (by rw [hut]; exact hu.of_le (by simp))
    simp only [hut] at hw
    obtain ⟨Cu, hCu⟩ := periodic_bounded hu.continuous pu
    have hum : MemLp ut 2 volume := MemLp.of_bound iu.aestronglyMeasurable Cu
      (Eventually.of_forall fun y => hCu _)
    have hgm : ∀ k, MemLp (fun y => fderiv ℝ u (secT y) (Pi.single k 1)) 2 volume := by
      intro k
      obtain ⟨C, hC⟩ := periodic_bounded (contDiff_Dk hu k).continuous (pu.Dk k)
      exact MemLp.of_bound (I (contDiff_Dk hu k).continuous (pu.Dk k)).aestronglyMeasurable C
        (Eventually.of_forall fun y => hC _)
    have hP := poincare_torus hw hum hgm
    rw [Fintype.sum_unique, ProbabilityTheory.variance_eq_integral
      iu.aestronglyMeasurable.aemeasurable] at hP
    exact hP
  -- (d) back to the weighted measure
  have hd : ∫ y, Dk u q (secT y) ^ 2 ≤ Emin⁻¹ * I1 := by
    rw [hI1, ← integral_const_mul]
    have iD : Integrable (fun y => Dk u q (secT y) ^ 2) volume :=
      I (Φ := fun x => Dk u q x ^ 2) (hDu.continuous.pow 2) (fun m x => by simp only [pDu m x])
    have iD' : Integrable (fun y => e y * Dk u q (secT y) ^ 2) volume :=
      I (Φ := fun x => Real.exp (-ψ x) * Dk u q x ^ 2) (hE.mul (hDu.continuous.pow 2))
        (fun m x => by simp only [pψ m x, pDu m x])
    refine integral_mono iD (iD'.const_mul _) fun y => ?_
    rw [← mul_assoc]
    calc Dk u q (secT y) ^ 2 = 1 * Dk u q (secT y) ^ 2 := (one_mul _).symm
      _ ≤ Emin⁻¹ * e y * Dk u q (secT y) ^ 2 := by
        gcongr
        rw [le_inv_mul_iff₀ hEmin0, mul_one]; exact hEmin y
  have hratio : Emax * Emin⁻¹ ≤ Real.exp κ' := by
    rw [← Real.exp_neg, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [hosc xa xb])
  have hI10 : 0 ≤ I1 := integral_nonneg fun y => mul_nonneg (he0 y).le (sq_nonneg _)
  have hpi : 0 < 4 * π ^ 2 := by positivity
  have hstep4 : V ≤ t * I1 := by
    have h1 : ∫ y, (u (secT y) - c0) ^ 2 ≤ (4 * π ^ 2)⁻¹ * (Emin⁻¹ * I1) := by
      rw [le_inv_mul_iff₀ hpi]; exact hcP.trans hd
    calc V ≤ Emax * ((4 * π ^ 2)⁻¹ * (Emin⁻¹ * I1)) :=
          ha.trans (hb.trans (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le))
      _ = (Emax * Emin⁻¹) * (4 * π ^ 2)⁻¹ * I1 := by ring
      _ ≤ Real.exp κ' * (4 * π ^ 2)⁻¹ * I1 := by gcongr
      _ = t * I1 := by rw [ht]; ring
  -- Step 5: combine
  have hfin : I1 ≤ t * B := by
    have h2 : 1 / (2 * t) * V ≤ 1 / (2 * t) * (t * I1) :=
      mul_le_mul_of_nonneg_left hstep4 (by positivity)
    have : 1 / (2 * t) * (t * I1) = I1 / 2 := by field_simp
    rw [this] at h2
    linarith
  rw [← hB]
  calc 4 * π ^ 2 * Real.exp (-κ') * I1 ≤ 4 * π ^ 2 * Real.exp (-κ') * (t * B) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = B := by
        rw [ht, Real.exp_neg]
        field_simp

end OneD

end SharpLSI
