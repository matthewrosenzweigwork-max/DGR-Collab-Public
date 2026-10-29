import FullLabeledLSI.Nonvacuity.Prop82.Poincare
import SharpSymmetricLSI.Paper.CosineDissipation
import SharpSymmetricLSI.Paper.CircleLSIExt

/-!
# Lane C, module C3: closed forms for bounded densities

For a bounded measurable density `ρ ≥ 0` of mass one (with `√ρ ∈ H¹` where a Fisher information
is involved) the real quantities `entropy`, `fisher`, `firstMode`, `forceEnergy`, `realGap`,
`realDiss` have the closed forms below. None of them needs the gap hypothesis of `Admissible`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

open SharpLSI

/-- Bounded measurable probability density. -/
structure BddDens (ρ : Torus 1 → ℝ) (B : ℝ) : Prop where
  meas : Measurable ρ
  nonneg : ∀ x, 0 ≤ ρ x
  le : ∀ x, ρ x ≤ B
  mass : ∫ x, ρ x ∂haar 1 = 1

theorem BddDens.integrable {ρ : Torus 1 → ℝ} {B : ℝ} (h : BddDens ρ B) :
    Integrable ρ (haar 1) := integrable_of_integral_eq_one h.mass

theorem BddDens.B_nonneg {ρ : Torus 1 → ℝ} {B : ℝ} (h : BddDens ρ B) : 0 ≤ B :=
  (h.nonneg (Classical.arbitrary _)).trans (h.le _)

theorem integrable_mul_log {ρ : Torus 1 → ℝ} {B : ℝ} (h : BddDens ρ B) :
    Integrable (fun x => ρ x * Real.log (ρ x)) (haar 1) := by
  refine Integrable.of_bound (h.meas.mul (Real.measurable_log.comp h.meas)).aestronglyMeasurable
    (B ^ 2 + 1) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have h0 := h.nonneg x
  have h1 := h.le x
  have hB := h.B_nonneg
  constructor
  · rcases h0.eq_or_lt with h2 | h2
    · rw [← h2]; simp only [zero_mul]; linarith [sq_nonneg B]
    · have := Real.log_le_sub_one_of_pos h2
      have h3 := Real.one_sub_inv_le_log_of_pos h2
      have : ρ x * (1 - (ρ x)⁻¹) ≤ ρ x * Real.log (ρ x) :=
        mul_le_mul_of_nonneg_left h3 h0
      have e : ρ x * (1 - (ρ x)⁻¹) = ρ x - 1 := by field_simp
      nlinarith [sq_nonneg B]
  · rcases h0.eq_or_lt with h2 | h2
    · rw [← h2]; simp only [zero_mul]; linarith [sq_nonneg B]
    · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h2) h0
      nlinarith [sq_nonneg (ρ x - B), mul_nonneg h0 (sub_nonneg.2 h1)]

theorem entropy_eq_integral_C {ρ : Torus 1 → ℝ} {B : ℝ} (h : BddDens ρ B) :
    entropy ρ = ∫ x, ρ x * Real.log (ρ x) ∂haar 1 := by
  unfold entropy
  rw [(klDiv_densMeasure_bdd h.meas h.nonneg h.mass h.le).2]
  have hi := integrable_mul_log h
  have e : ∀ x, klFun (ρ x) = ρ x * Real.log (ρ x) + 1 - ρ x := fun x => klFun_apply _
  simp_rw [e]
  have hi1 : Integrable (fun x => ρ x * Real.log (ρ x) + 1) (haar 1) := hi.add (integrable_const 1)
  rw [integral_sub hi1 h.integrable, integral_add hi (integrable_const 1), h.mass]
  simp

theorem klDiv_ne_top_of_bdd {ρ : Torus 1 → ℝ} {B : ℝ} (h : BddDens ρ B) :
    klDiv (densMeasure ρ) (haar 1) ≠ ⊤ :=
  (klDiv_densMeasure_bdd h.meas h.nonneg h.mass h.le).1

theorem firstMode_eq_moments_C {ρ : Torus 1 → ℝ} (hi : Integrable ρ (haar 1)) :
    firstMode ρ = (∫ x, gCos x * ρ x ∂haar 1) ^ 2 + (∫ x, sCos x * ρ x ∂haar 1) ^ 2 :=
  firstMode_eq hi

/-- The Fisher information of a density with `√ρ ∈ H¹`. -/
theorem fisher_eq_sqrt {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    fisher ρ = 4 * ∫ x, weakGrad (fun y => Real.sqrt (ρ y)) x 0 ^ 2 ∂haar 1 := by
  unfold fisher
  rw [fisherInfo_densMeasure_eq h0 h1 hH, ENNReal.toReal_ofReal]
  exact mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _)

theorem entropy_fisher_finite_C' {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    klDiv (densMeasure ρ) (haar 1) ≠ ⊤ ∧ fisherInfo (densMeasure ρ) (haar 1) ≠ ⊤ := by
  have hq := circle_quantitative_lsi_aux h0 h1 hH
  exact ⟨hq.1, hq.2.1⟩

/-- `gap` is the real gap, without assuming positivity of the gap. -/
theorem gap_eq_real_C' {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    gap cosV (cosW 1) (densMeasure ρ) = (realGap ρ : EReal) := by
  have hkl : klDiv (densMeasure ρ) (haar 1) = ENNReal.ofReal (entropy ρ) :=
    (ENNReal.ofReal_toReal (entropy_fisher_finite_C' h0 h1 hH).1).symm
  rw [(cosine_free_energy_aux (by norm_num : (0 : Real) < 1)).2.2.2.1 ρ h0 h1,
    hkl, EReal.coe_ennreal_ofReal, max_eq_left (entropy_nonneg ρ), ← EReal.coe_add]
  congr 1
  unfold realGap
  ring

theorem admissible_of_realGap_pos {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x)))
    (hG : 0 < realGap ρ) : Admissible cosV (cosW 1) ρ := by
  refine ⟨h0, h1, hH, ?_⟩
  rw [gap_eq_real_C' h0 h1 hH]
  exact_mod_cast hG

/-- Moments `∫ e ρ` of a density against the basic trigonometric polynomials. -/
theorem integrable_trig_mul {ρ : Torus 1 → ℝ} (hi : Integrable ρ (haar 1)) :
    Integrable (fun x => gCos x * ρ x) (haar 1) ∧ Integrable (fun x => sCos x * ρ x) (haar 1) :=
  ⟨integrable_mul_bdd hi continuous_gCos abs_gCos_le, integrable_mul_bdd hi continuous_sCos abs_sCos_le⟩

/-- The interaction part of `realDiss - 2 R realGap`, as a function of the four moments
`C = ∫ gCos ρ`, `S = ∫ sCos ρ`, `P = ∫ gCos² ρ`, `Q = ∫ sCos gCos ρ`. -/
noncomputable def interaction (C S P Q : ℝ) : ℝ :=
  (2 * aCos - realRate) * (C ^ 2 + S ^ 2) +
    aCos * (S ^ 2 * P - 2 * C * S * Q + C ^ 2 * (1 - P))

/-- Closed form of the force energy. -/
theorem forceEnergy_eq_moments {ρ : Torus 1 → ℝ} (hi : Integrable ρ (haar 1))
    (h1 : ∫ x, ρ x ∂haar 1 = 1) :
    forceEnergy ρ = aCos * ((∫ x, sCos x * ρ x ∂haar 1) ^ 2 * (∫ x, gCos x ^ 2 * ρ x ∂haar 1) -
      2 * (∫ x, gCos x * ρ x ∂haar 1) * (∫ x, sCos x * ρ x ∂haar 1) *
        (∫ x, sCos x * gCos x * ρ x ∂haar 1) +
      (∫ x, gCos x * ρ x ∂haar 1) ^ 2 * (1 - ∫ x, gCos x ^ 2 * ρ x ∂haar 1)) := by
  set C := ∫ x, gCos x * ρ x ∂haar 1 with hC
  set S := ∫ x, sCos x * ρ x ∂haar 1 with hS
  have hGc : ContDiff ℝ 1 (gConv ρ ∘ liftT) := (contDiff_gConv_lift h1).of_le le_top
  have hgrad : ∀ᵐ x ∂haar 1,
      weakGrad (gConv ρ) x 0 = 2 * π * (S * gCos x - C * sCos x) := by
    filter_upwards [weakGrad_ae_eq_of_contDiff hGc] with x hx
    rw [hx]
    simp only
    rw [gConv_lift h1, fderiv_trig_lift, ← gCos_secT, ← sCos_secT]
    ring
  have i1 : Integrable (fun x => gCos x ^ 2 * ρ x) (haar 1) :=
    integrable_mul_bdd hi (continuous_gCos.pow 2) (fun y => by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (abs_gCos_le y))
  have i2 : Integrable (fun x => sCos x * gCos x * ρ x) (haar 1) :=
    integrable_mul_bdd hi (continuous_sCos.mul continuous_gCos) (fun y => by
      rw [abs_mul]; nlinarith [abs_sCos_le y, abs_gCos_le y, abs_nonneg (sCos y), abs_nonneg (gCos y)])
  unfold forceEnergy
  have hpt : ∀ᵐ x ∂haar 1, ρ x * weakGrad (gConv ρ) x 0 ^ 2 =
      aCos * (S ^ 2 * (gCos x ^ 2 * ρ x) - 2 * C * S * (sCos x * gCos x * ρ x) +
        C ^ 2 * (ρ x - gCos x ^ 2 * ρ x)) := by
    filter_upwards [hgrad] with x hx
    rw [hx]
    have hs : sCos x ^ 2 = 1 - gCos x ^ 2 := by linarith [gCos_sq_add_sCos_sq x]
    unfold aCos
    have : (S * gCos x - C * sCos x) ^ 2 = S ^ 2 * gCos x ^ 2 - 2 * C * S * (sCos x * gCos x) +
        C ^ 2 * (1 - gCos x ^ 2) := by rw [← hs]; ring
    calc ρ x * (2 * π * (S * gCos x - C * sCos x)) ^ 2
        = ρ x * (2 * π) ^ 2 * (S * gCos x - C * sCos x) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  have hX : Integrable (fun x => S ^ 2 * (gCos x ^ 2 * ρ x)) (haar 1) := i1.const_mul _
  have hY : Integrable (fun x => 2 * C * S * (sCos x * gCos x * ρ x)) (haar 1) := i2.const_mul _
  have hZ : Integrable (fun x => C ^ 2 * (ρ x - gCos x ^ 2 * ρ x)) (haar 1) :=
    (hi.sub i1).const_mul _
  have hXY : Integrable (fun x => S ^ 2 * (gCos x ^ 2 * ρ x) -
      2 * C * S * (sCos x * gCos x * ρ x)) (haar 1) := hX.sub hY
  rw [integral_congr_ae hpt, integral_const_mul, integral_add hXY hZ, integral_sub hX hY,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_sub hi i1, h1]

/-- The four moments of a density. -/
noncomputable def momC (ρ : Torus 1 → ℝ) : ℝ := ∫ x, gCos x * ρ x ∂haar 1
noncomputable def momS (ρ : Torus 1 → ℝ) : ℝ := ∫ x, sCos x * ρ x ∂haar 1
noncomputable def momP (ρ : Torus 1 → ℝ) : ℝ := ∫ x, gCos x ^ 2 * ρ x ∂haar 1
noncomputable def momQ (ρ : Torus 1 → ℝ) : ℝ := ∫ x, sCos x * gCos x * ρ x ∂haar 1

theorem realGap_eq {ρ : Torus 1 → ℝ} {B : ℝ} (h : BddDens ρ B) :
    realGap ρ = (∫ x, ρ x * Real.log (ρ x) ∂haar 1) + (momC ρ ^ 2 + momS ρ ^ 2) / 2 := by
  unfold realGap
  rw [entropy_eq_integral_C h, firstMode_eq_moments_C h.integrable]
  rfl

/-- Closed form of the quantity minimized by an optimizer. -/
theorem realDiss_sub_eq {ρ : Torus 1 → ℝ} {B : ℝ} (h : BddDens ρ B)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    realDiss ρ - 2 * realRate * realGap ρ =
      4 * (∫ x, weakGrad (fun y => Real.sqrt (ρ y)) x 0 ^ 2 ∂haar 1)
        - 2 * realRate * (∫ x, ρ x * Real.log (ρ x) ∂haar 1)
        + interaction (momC ρ) (momS ρ) (momP ρ) (momQ ρ) := by
  unfold realDiss
  rw [fisher_eq_sqrt h.nonneg h.mass hH, realGap_eq h, firstMode_eq_moments_C h.integrable,
    forceEnergy_eq_moments h.integrable h.mass]
  unfold interaction momC momS momP momQ
  ring

end SharpLSI.FL.Prop82
