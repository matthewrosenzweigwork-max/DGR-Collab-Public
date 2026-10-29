import FullLabeledLSI.Paper.Sec5CondB
import FullLabeledLSI.Paper.Sec5CondC

/-!
# Conditional laws for a random subset, part D: conditional expectation, score identity, Jensen
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d N : ℕ}

/-! ### (T5) Conditional expectations -/

/-- `E_ν[F | X_S = a, X_i = x]` for `ν = Q · volume` (`SharpLSI.condRatio`). -/
noncomputable def condRatioS (Q F : Config N d → ℝ) (S : Finset (Fin N)) (i : Fin N)
    (a : S → Torus d) (x : Torus d) : ℝ :=
  (∫ z, F (assembleS S i a x z) * Q (assembleS S i a x z)
    ∂(volume : Measure (RestIdx S i → Torus d))) / margQS Q S i a x

section aux
variable {Q : Config N d → ℝ} {c C : ℝ}

theorem sec5D_measurable_slice (S : Finset (Fin N)) (i : Fin N) (a : S → Torus d) (x : Torus d) :
    Measurable fun z : RestIdx S i → Torus d => assembleS S i a x z :=
  (measurable_assembleS S i).comp ((measurable_const (a := (a, x))).prodMk measurable_id)

theorem sec5D_integrable_Q (hQ : IsBddDens Q c C) (S : Finset (Fin N)) (i : Fin N)
    (a : S → Torus d) (x : Torus d) :
    Integrable (fun z => Q (assembleS S i a x z)) (volume : Measure (RestIdx S i → Torus d)) :=
  Integrable.of_bound (hQ.meas.comp (sec5D_measurable_slice S i a x)).aestronglyMeasurable C
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hQ.pos.le.trans (hQ.lower _))]; exact hQ.upper _)

/-- `F ∈ L¹(Q · volume)` iff `F Q ∈ L¹(volume)`. -/
theorem sec5D_integrable_mul_Q (hQ : IsBddDens Q c C) {G : Config N d → ℝ}
    (hG : Integrable G (qMeasure Q)) : Integrable (fun X => G X * Q X) (volume : Measure (Config N d)) := by
  have h := (integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (Config N d)))
    (ENNReal.measurable_ofReal.comp hQ.meas) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hG
  refine h.congr (Eventually.of_forall fun X => ?_)
  show (ENNReal.ofReal (Q X)).toReal • G X = G X * Q X
  rw [ENNReal.toReal_ofReal (hQ.pos.le.trans (hQ.lower X)), smul_eq_mul, mul_comm]

end aux

section ratio
variable {Q : Config N d → ℝ} {c C : ℝ} (hQ : IsBddDens Q c C) {S : Finset (Fin N)} {i : Fin N}
  (hi : i ∉ S) {ν : Measure (Config N d)} [IsFiniteMeasure ν] (hν : ν = qMeasure Q)
  {F : Config N d → ℝ} (hFm : Measurable F)

include hQ hFm in
theorem measurable_condRatioS :
    Measurable (Function.uncurry (condRatioS Q F S i)) := by
  have h1 : Measurable fun q : (S → Torus d) × Torus d =>
      ∫ z, F (assembleS S i q.1 q.2 z) * Q (assembleS S i q.1 q.2 z)
        ∂(volume : Measure (RestIdx S i → Torus d)) :=
    (((hFm.mul hQ.meas).comp (measurable_assembleS S i)).stronglyMeasurable.integral_prod_right'
      ).measurable
  exact h1.div (measurable_margQS hQ S i)

include hQ hFm in
theorem abs_condRatioS_le {B : ℝ} (hFB : ∀ X, |F X| ≤ B) (a : S → Torus d) (x : Torus d) :
    |condRatioS Q F S i a x| ≤ B := by
  have hQ0 : ∀ X, 0 ≤ Q X := fun X => hQ.pos.le.trans (hQ.lower X)
  have hm : 0 < margQS Q S i a x := hQ.pos.trans_le (margQS_bounds hQ S i a x).1
  have hQi := sec5D_integrable_Q hQ S i a x
  unfold condRatioS
  rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
  calc |∫ z, F (assembleS S i a x z) * Q (assembleS S i a x z)
        ∂(volume : Measure (RestIdx S i → Torus d))|
      ≤ ∫ z, |F (assembleS S i a x z) * Q (assembleS S i a x z)|
          ∂(volume : Measure (RestIdx S i → Torus d)) := abs_integral_le_integral_abs
    _ ≤ ∫ z, B * Q (assembleS S i a x z) ∂(volume : Measure (RestIdx S i → Torus d)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hQi.const_mul B) (Eventually.of_forall fun z => ?_)
        show |F _ * Q _| ≤ B * Q _
        rw [abs_mul, abs_of_nonneg (hQ0 _)]
        exact mul_le_mul_of_nonneg_right (hFB _) (hQ0 _)
    _ = B * margQS Q S i a x := by rw [integral_const_mul]; rfl

include hQ hFm in
/-- Pointwise Cauchy–Schwarz: `r² · m ≤ ∫ F² Q dz` (`SharpLSI.condRatio_sq_mul_le`). -/
theorem condRatioS_sq_mul_le (a : S → Torus d) (x : Torus d) :
    ENNReal.ofReal (condRatioS Q F S i a x ^ 2) * ENNReal.ofReal (margQS Q S i a x) ≤
      ∫⁻ z, ENNReal.ofReal (F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z))
        ∂(volume : Measure (RestIdx S i → Torus d)) := by
  set μz := (volume : Measure (RestIdx S i → Torus d))
  have hzm := sec5D_measurable_slice (d := d) S i a x
  set A := ∫⁻ z, ENNReal.ofReal (F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z)) ∂μz
  by_cases hA : A = ⊤
  · rw [hA]; exact le_top
  have hQ0 : ∀ X, 0 ≤ Q X := fun X => hQ.pos.le.trans (hQ.lower X)
  have hF2m : Measurable fun z => F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z) :=
    ((hFm.comp hzm).pow_const 2).mul (hQ.meas.comp hzm)
  have hF2i : Integrable (fun z => F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z)) μz := by
    refine (lintegral_ofReal_ne_top_iff_integrable hF2m.aestronglyMeasurable
      (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hQ0 _))).mp hA
  have hQi := sec5D_integrable_Q hQ S i a x
  have hFQi : Integrable (fun z => F (assembleS S i a x z) * Q (assembleS S i a x z)) μz := by
    refine (hF2i.add hQi).mono' ((hFm.comp hzm).mul (hQ.meas.comp hzm)).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hQ0 _)]
    have h1 := hQ0 (assembleS S i a x z)
    have hF : |F (assembleS S i a x z)| ≤ F (assembleS S i a x z) ^ 2 + 1 := by
      nlinarith [sq_abs (F (assembleS S i a x z)), sq_nonneg (|F (assembleS S i a x z)| - 1),
        abs_nonneg (F (assembleS S i a x z))]
    calc |F (assembleS S i a x z)| * Q (assembleS S i a x z)
        ≤ (F (assembleS S i a x z) ^ 2 + 1) * Q (assembleS S i a x z) :=
          mul_le_mul_of_nonneg_right hF h1
      _ = F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z) + Q (assembleS S i a x z) := by
          ring
  set m := margQS Q S i a x
  have hm : 0 < m := hQ.pos.trans_le (margQS_bounds hQ S i a x).1
  set B := ∫ z, F (assembleS S i a x z) * Q (assembleS S i a x z) ∂μz
  set r := condRatioS Q F S i a x
  have hr : r = B / m := rfl
  have hmQ : m = ∫ z, Q (assembleS S i a x z) ∂μz := rfl
  have h0 : 0 ≤ ∫ z, (F (assembleS S i a x z) - r) ^ 2 * Q (assembleS S i a x z) ∂μz :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hQ0 _)
  have hexp : ∫ z, (F (assembleS S i a x z) - r) ^ 2 * Q (assembleS S i a x z) ∂μz =
      (∫ z, F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z) ∂μz) - 2 * r * B
        + r ^ 2 * m := by
    have e : ∀ z, (F (assembleS S i a x z) - r) ^ 2 * Q (assembleS S i a x z) =
        F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z) -
          2 * r * (F (assembleS S i a x z) * Q (assembleS S i a x z)) +
          r ^ 2 * Q (assembleS S i a x z) := fun z => by ring
    simp_rw [e]
    rw [integral_add (f := fun z => F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z) -
        2 * r * (F (assembleS S i a x z) * Q (assembleS S i a x z)))
        (g := fun z => r ^ 2 * Q (assembleS S i a x z)) (hF2i.sub (hFQi.const_mul _))
        (hQi.const_mul _),
      integral_sub (f := fun z => F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z))
        (g := fun z => 2 * r * (F (assembleS S i a x z) * Q (assembleS S i a x z))) hF2i
        (hFQi.const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  have hBr : B = r * m := by rw [hr]; field_simp
  have hle : r ^ 2 * m ≤ ∫ z, F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z) ∂μz := by
    rw [hexp, hBr] at h0; nlinarith
  calc ENNReal.ofReal (r ^ 2) * ENNReal.ofReal m = ENNReal.ofReal (r ^ 2 * m) :=
        (ENNReal.ofReal_mul (sq_nonneg _)).symm
    _ ≤ ENNReal.ofReal (∫ z, F (assembleS S i a x z) ^ 2 * Q (assembleS S i a x z) ∂μz) :=
        ENNReal.ofReal_le_ofReal hle
    _ = A := ofReal_integral_eq_lintegral_ofReal hF2i
        (Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hQ0 _))

include hQ hi hν hFm in
/-- **`condRatioS` is the conditional expectation**, for `F ∈ L¹(ν)` (L¹ version of
`SharpLSI.condRatio_ae_eq_condExp`; needed because the score is only `L²`). -/
theorem condRatioS_ae_eq_condExp (hFi : Integrable F ν) :
    (fun X => condRatioS Q F S i (restrictS S X) (X i)) =ᵐ[ν]
      ν[F | MeasurableSpace.comap (fun X : Config N d => (restrictS S X, X i)) inferInstance] := by
  subst hν
  have hQ0 : ∀ X, 0 ≤ Q X := fun X => hQ.pos.le.trans (hQ.lower X)
  have hπ : Measurable fun X : Config N d => (restrictS S X, X i) :=
    (measurable_restrictS S).prodMk (measurable_pi_apply i)
  have hm : MeasurableSpace.comap (fun X : Config N d => (restrictS S X, X i)) inferInstance ≤
      MeasurableSpace.pi := measurable_iff_comap_le.mp hπ
  have hR := measurable_condRatioS (S := S) (i := i) hQ hFm
  have hRπ : Measurable fun X : Config N d => condRatioS Q F S i (restrictS S X) (X i) :=
    hR.comp hπ
  have hFQ := sec5D_integrable_mul_Q hQ hFi
  -- integrability of the ratio
  have hRint : Integrable (fun X : Config N d => condRatioS Q F S i (restrictS S X) (X i))
      (qMeasure Q) := by
    refine ⟨hRπ.aestronglyMeasurable, ?_⟩
    have hbound : ∀ (a : S → Torus d) (x : Torus d),
        ‖condRatioS Q F S i a x‖ₑ * ENNReal.ofReal (margQS Q S i a x) ≤
          ∫⁻ z, ‖F (assembleS S i a x z) * Q (assembleS S i a x z)‖ₑ
            ∂(volume : Measure (RestIdx S i → Torus d)) := by
      intro a x
      have hm0 : 0 < margQS Q S i a x := hQ.pos.trans_le (margQS_bounds hQ S i a x).1
      have hRm : condRatioS Q F S i a x * margQS Q S i a x =
          ∫ z, F (assembleS S i a x z) * Q (assembleS S i a x z)
            ∂(volume : Measure (RestIdx S i → Torus d)) := by
        unfold condRatioS; field_simp
      calc ‖condRatioS Q F S i a x‖ₑ * ENNReal.ofReal (margQS Q S i a x)
          = ‖condRatioS Q F S i a x‖ₑ * ‖margQS Q S i a x‖ₑ := by
            rw [Real.enorm_eq_ofReal hm0.le]
        _ = ‖condRatioS Q F S i a x * margQS Q S i a x‖ₑ := (enorm_mul _ _).symm
        _ = ‖∫ z, F (assembleS S i a x z) * Q (assembleS S i a x z)
              ∂(volume : Measure (RestIdx S i → Torus d))‖ₑ := by rw [hRm]
        _ ≤ _ := enorm_integral_le_lintegral_enorm _
    have h1 : ∫⁻ X, ‖condRatioS Q F S i (restrictS S X) (X i)‖ₑ ∂(qMeasure Q) =
        ∫⁻ X, ‖condRatioS Q F S i (restrictS S X) (X i)‖ₑ * ENNReal.ofReal (Q X) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ (f := fun X => ENNReal.ofReal (Q X))
        (ENNReal.measurable_ofReal.comp hQ.meas) hRπ.enorm]
      exact lintegral_congr fun X => by rw [Pi.mul_apply, mul_comm]
    have h2 := lintegral_revealCur hQ hi
      (F := fun a x => ‖condRatioS Q F S i a x‖ₑ) hR.enorm
    have h3 : ∫⁻ a, ∫⁻ x, ‖condRatioS Q F S i a x‖ₑ * ENNReal.ofReal (margQS Q S i a x) ∂haar d
        ∂(volume : Measure (S → Torus d)) ≤ ∫⁻ X, ‖F X * Q X‖ₑ := by
      rw [lintegral_assembleS hi (G := fun X => ‖F X * Q X‖ₑ) (hFm.mul hQ.meas).enorm]
      exact lintegral_mono fun a => lintegral_mono fun x => hbound a x
    unfold HasFiniteIntegral
    rw [h1]
    exact (h2.trans_le h3).trans_lt hFQ.2
  have hgm : Measurable[MeasurableSpace.comap (fun X : Config N d => (restrictS S X, X i))
      inferInstance] fun X : Config N d => condRatioS Q F S i (restrictS S X) (X i) :=
    hR.comp (measurable_iff_comap_le.mpr le_rfl)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hFi (fun s _ _ => hRint.integrableOn)
    (fun s hs _ => ?_) hgm.aestronglyMeasurable
  obtain ⟨T, hT, rfl⟩ := hs
  have hset : MeasurableSet ((fun X : Config N d => (restrictS S X, X i)) ⁻¹' T) := hπ hT
  rw [← integral_indicator hset, ← integral_indicator hset]
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun X => ENNReal.ofReal (Q X))
      (ENNReal.measurable_ofReal.comp hQ.meas) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul (f := fun X => ENNReal.ofReal (Q X))
      (ENNReal.measurable_ofReal.comp hQ.meas) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hQ0 _), smul_eq_mul]
  have i1 := sec5D_integrable_mul_Q hQ (hRint.indicator hset)
  have i2 := sec5D_integrable_mul_Q hQ (hFi.indicator hset)
  rw [integral_assembleS hi (G := fun X => Q X * _) (by simpa only [mul_comm] using i1),
    integral_assembleS hi (G := fun X => Q X * _) (by simpa only [mul_comm] using i2)]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  obtain ⟨a, x⟩ := q
  by_cases hax : (a, x) ∈ T
  · have hmem : ∀ z, assembleS S i a x z ∈
        (fun X : Config N d => (restrictS S X, X i)) ⁻¹' T := fun z => by
      simpa [restrictS_assembleS, assembleS_cur hi] using hax
    simp only [Set.indicator_of_mem (hmem _), restrictS_assembleS, assembleS_cur hi]
    have e1 : ∫ z, Q (assembleS S i a x z) * condRatioS Q F S i a x
        ∂(volume : Measure (RestIdx S i → Torus d)) =
        condRatioS Q F S i a x * margQS Q S i a x := by
      simp_rw [mul_comm (Q _)]
      rw [integral_const_mul]; rfl
    have e2 : ∫ z, Q (assembleS S i a x z) * F (assembleS S i a x z)
        ∂(volume : Measure (RestIdx S i → Torus d)) =
        ∫ z, F (assembleS S i a x z) * Q (assembleS S i a x z)
          ∂(volume : Measure (RestIdx S i → Torus d)) := by
      congr 1; funext z; ring
    have hm0 : 0 < margQS Q S i a x := hQ.pos.trans_le (margQS_bounds hQ S i a x).1
    rw [e1, e2]
    unfold condRatioS
    rw [div_mul_cancel₀ _ hm0.ne']
  · have hmem : ∀ z, assembleS S i a x z ∉
        (fun X : Config N d => (restrictS S X, X i)) ⁻¹' T := fun z h => hax (by
      simpa [restrictS_assembleS, assembleS_cur hi] using h)
    simp [Set.indicator_of_notMem (hmem _)]

include hQ hi hν hFm in
/-- The bounded special case (the exact analogue of `SharpLSI.condRatio_ae_eq_condExp`). -/
theorem condRatioS_ae_eq_condExp_bdd {B : ℝ} (hFB : ∀ X, |F X| ≤ B) :
    (fun X => condRatioS Q F S i (restrictS S X) (X i)) =ᵐ[ν]
      ν[F | MeasurableSpace.comap (fun X : Config N d => (restrictS S X, X i)) inferInstance] :=
  condRatioS_ae_eq_condExp hQ hi hν hFm
    (Integrable.of_bound hFm.aestronglyMeasurable B
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hFB X))

end ratio

/-! ### (T6) The conditional score identity -/

section score
variable {Q : Config N d → ℝ} {c C : ℝ} (hQ : IsBddDens Q c C) {S : Finset (Fin N)} {i : Fin N}
  {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}

include hQ in
/-- **(5.20), algebraic form, for ALL `(a, x)`:** `(∇ₓ ρ)/ρ = E[∇_{i,k}Q / Q | X_S = a, X_i = x]`.
No integrability or weak-gradient hypothesis is needed (`Q > 0`, `ZcS > 0`). -/
theorem condRatioS_score (k : Fin d) (a : S → Torus d) (x : Torus d) :
    gradCondS Q GQ S i a x k / condDensS Q S i a x =
      condRatioS Q (fun Y => GQ (flat Y) (i, k) / Q Y) S i a x := by
  have hQne : ∀ X, Q X ≠ 0 := fun X => (hQ.pos.trans_le (hQ.lower X)).ne'
  have hZ : 0 < ZcS Q S i a := hQ.pos.trans_le (ZcS_bounds hQ S i a).1
  have hm : 0 < margQS Q S i a x := hQ.pos.trans_le (margQS_bounds hQ S i a x).1
  have hnum : ∫ z, (GQ (flat (assembleS S i a x z)) (i, k) / Q (assembleS S i a x z)) *
      Q (assembleS S i a x z) ∂(volume : Measure (RestIdx S i → Torus d)) =
      gradMargS GQ S i a x k := by
    unfold gradMargS
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    exact div_mul_cancel₀ _ (hQne _)
  unfold condRatioS gradCondS condDensS
  rw [hnum]
  field_simp

include hQ in
/-- The score `GQ_{(i,k)}/Q` is in `L¹(ν)` as soon as `GQ_{(i,k)} ∈ L¹(volume)`. -/
theorem integrable_score {ν : Measure (Config N d)} (hν : ν = qMeasure Q) (k : Fin d)
    (hGi : Integrable (fun y => GQ y (i, k)) volume) :
    Integrable (fun Y : Config N d => GQ (flat Y) (i, k) / Q Y) ν := by
  subst hν
  have hQne : ∀ X, Q X ≠ 0 := fun X => (hQ.pos.trans_le (hQ.lower X)).ne'
  have hg1 : Integrable (fun X : Config N d => GQ (flat X) (i, k)) volume :=
    (SharpLSI.measurePreserving_flat' N).integrable_comp_of_integrable hGi
  refine (integrable_withDensity_iff_integrable_smul' (f := fun X => ENNReal.ofReal (Q X))
    (ENNReal.measurable_ofReal.comp hQ.meas) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mpr ?_
  refine hg1.congr (Eventually.of_forall fun X => ?_)
  show GQ (flat X) (i, k) = (ENNReal.ofReal (Q X)).toReal • (GQ (flat X) (i, k) / Q X)
  rw [ENNReal.toReal_ofReal (hQ.pos.le.trans (hQ.lower X)), smul_eq_mul, mul_div_cancel₀ _ (hQne X)]

include hQ in
/-- **(5.20) as a statement about `ν`-a.e. `X`:** the log-gradient of the conditional density at
`(X_S, X_i)` is the conditional expectation of the score `∇_{i,k} log Q` given `(X_S, X_i)`. -/
theorem score_ae_eq_condExp {S : Finset (Fin N)} {i : Fin N} (hi : i ∉ S)
    {ν : Measure (Config N d)} [IsFiniteMeasure ν] (hν : ν = qMeasure Q)
    (hGm : ∀ p, Measurable fun y => GQ y p) (k : Fin d)
    (hGi : Integrable (fun y => GQ y (i, k)) volume) :
    (fun X => gradCondS Q GQ S i (restrictS S X) (X i) k / condDensS Q S i (restrictS S X) (X i))
      =ᵐ[ν] ν[fun Y : Config N d => GQ (flat Y) (i, k) / Q Y |
        MeasurableSpace.comap (fun X : Config N d => (restrictS S X, X i)) inferInstance] := by
  have hFm : Measurable fun Y : Config N d => GQ (flat Y) (i, k) / Q Y :=
    ((hGm (i, k)).comp SharpLSI.measurable_flat).div hQ.meas
  have h := condRatioS_ae_eq_condExp hQ hi hν hFm (integrable_score hQ hν k hGi)
  refine Filter.EventuallyEq.trans (Eventually.of_forall fun X => ?_) h
  exact condRatioS_score hQ k (restrictS S X) (X i)

end score

/-! ### (T7) Conditional Jensen / Fisher-type consequence -/

section jensen
variable {Q : Config N d → ℝ} {c C : ℝ} (hQ : IsBddDens Q c C) {S : Finset (Fin N)} {i : Fin N}
  (hi : i ∉ S) {ν : Measure (Config N d)} (hν : ν = qMeasure Q)

include hQ hi hν in
/-- **Conditional Jensen** for the explicit ratio (`SharpLSI.lintegral_condRatio_sq_le`), no
integrability needed. -/
theorem lintegral_condRatioS_sq_le {F : Config N d → ℝ} (hFm : Measurable F) :
    ∫⁻ X, ENNReal.ofReal (condRatioS Q F S i (restrictS S X) (X i) ^ 2) ∂ν ≤
      ∫⁻ X, ENNReal.ofReal (F X ^ 2) ∂ν := by
  subst hν
  have hR := measurable_condRatioS (S := S) (i := i) hQ hFm
  have hπ : Measurable fun X : Config N d => (restrictS S X, X i) :=
    (measurable_restrictS S).prodMk (measurable_pi_apply i)
  have hf : Measurable fun X => ENNReal.ofReal (Q X) := ENNReal.measurable_ofReal.comp hQ.meas
  have hg1 : Measurable fun X : Config N d =>
      ENNReal.ofReal (condRatioS Q F S i (restrictS S X) (X i) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hR.comp hπ).pow_const 2)
  have hg2 : Measurable fun X : Config N d => ENNReal.ofReal (F X ^ 2) :=
    ENNReal.measurable_ofReal.comp (hFm.pow_const 2)
  rw [lintegral_withDensity_eq_lintegral_mul _ hf hg1,
    lintegral_withDensity_eq_lintegral_mul _ hf hg2]
  simp only [Pi.mul_apply]
  simp_rw [mul_comm (ENNReal.ofReal (Q _))]
  rw [lintegral_revealCur hQ hi
      (F := fun a x => ENNReal.ofReal (condRatioS Q F S i a x ^ 2))
      (ENNReal.measurable_ofReal.comp (hR.pow_const 2)),
    lintegral_assembleS hi (G := fun X => ENNReal.ofReal (F X ^ 2) * ENNReal.ofReal (Q X))
      (hg2.mul hf)]
  refine lintegral_mono fun a => lintegral_mono fun x => ?_
  refine (condRatioS_sq_mul_le hQ hFm a x).trans (le_of_eq ?_)
  refine lintegral_congr fun z => ?_
  rw [ENNReal.ofReal_mul (sq_nonneg _)]

variable {GQ : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}

include hQ hi hν in
/-- `∫ |E[s_{i,k} | X_S, X_i]|² dν ≤ ∫ s_{i,k}² dν` for the score `s_{i,k} = GQ_{(i,k)}/Q`
written through the gradient of the conditional density. -/
theorem lintegral_score_sq_le (hGm : ∀ p, Measurable fun y => GQ y p) (k : Fin d) :
    ∫⁻ X, ENNReal.ofReal ((gradCondS Q GQ S i (restrictS S X) (X i) k /
        condDensS Q S i (restrictS S X) (X i)) ^ 2) ∂ν ≤
      ∫⁻ X, ENNReal.ofReal ((GQ (flat X) (i, k) / Q X) ^ 2) ∂ν := by
  have hFm : Measurable fun Y : Config N d => GQ (flat Y) (i, k) / Q Y :=
    ((hGm (i, k)).comp SharpLSI.measurable_flat).div hQ.meas
  have h := lintegral_condRatioS_sq_le hQ hi hν hFm
  simp_rw [← condRatioS_score hQ k] at h
  exact h

include hQ hi hν in
/-- Summed over the `d` components (squared Euclidean norm of the score). -/
theorem lintegral_score_sq_sum_le (hGm : ∀ p, Measurable fun y => GQ y p) :
    ∑ k, ∫⁻ X, ENNReal.ofReal ((gradCondS Q GQ S i (restrictS S X) (X i) k /
        condDensS Q S i (restrictS S X) (X i)) ^ 2) ∂ν ≤
      ∑ k, ∫⁻ X, ENNReal.ofReal ((GQ (flat X) (i, k) / Q X) ^ 2) ∂ν :=
  Finset.sum_le_sum fun k _ => lintegral_score_sq_le hQ hi hν hGm k

end jensen

end SharpLSI.FL
