import SharpSymmetricLSI.Paper.AppAEvol1

/-!
# Lemma A.1, existence (1): the modified flux and the weighted kernel integral

The Picard scheme uses the drift computed from the normalized positive part
`P(η) = η⁺ / max(1, ∫η⁺)`: `ã(η) = ∇V + b_{P(η)}`, `|ã(η)| ≤ A = L_V + C_b` for every `η`, and
`N(η) = η ã(η)` satisfies `|N(η)| ≤ A|η|`,
`|N(η) - N(ζ)| ≤ A|η - ζ| + 2 C_b |ζ| ∫|η - ζ|`.
For probability densities `P(η) = η`, so `N(η) = η a_η` (up to null sets).
The kernel integral: `∫₀ᵗ c(t-u)^{-1/2} e^{μu} du ≤ e^{μt}/√μ`.
-/

open MeasureTheory Set Filter Topology
open scoped Real ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The normalized positive part `η⁺ / max(1, ∫η⁺)`. -/
noncomputable def posNorm (η : Torus d → ℝ) (y : Torus d) : ℝ :=
  max (η y) 0 / max 1 (∫ z, max (η z) 0 ∂haar d)

/-- The modified flux `N(η) = η (∇V + b_{P(η)})`. -/
noncomputable def modFlux (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (η : Torus d → ℝ)
    (y : Torus d) (k : Fin d) : ℝ :=
  η y * (lipGrad V y k + bForceL W (posNorm η) y k)

theorem posNorm_nonneg (η : Torus d → ℝ) (y : Torus d) : 0 ≤ posNorm η y :=
  div_nonneg (le_max_right _ _) (zero_le_one.trans (le_max_left _ _))

theorem integrable_posNorm {η : Torus d → ℝ} (hη : Integrable η (haar d)) :
    Integrable (posNorm η) (haar d) :=
  (hη.pos_part).div_const _

theorem integral_posNorm_le {η : Torus d → ℝ} (hη : Integrable η (haar d)) :
    ∫ y, posNorm η y ∂haar d ≤ 1 := by
  unfold posNorm
  rw [integral_div]
  have h0 : 0 ≤ ∫ z, max (η z) 0 ∂haar d := integral_nonneg fun z => le_max_right _ _
  rw [div_le_one (zero_lt_one.trans_le (le_max_left _ _))]
  exact le_max_right _ _

theorem integral_abs_posNorm_sub_le {η ζ : Torus d → ℝ} (hη : Integrable η (haar d))
    (hζ : Integrable ζ (haar d)) :
    ∫ y, |posNorm η y - posNorm ζ y| ∂haar d ≤ 2 * ∫ y, |η y - ζ y| ∂haar d := by
  set a := max 1 (∫ z, max (η z) 0 ∂haar d)
  set b := max 1 (∫ z, max (ζ z) 0 ∂haar d)
  have ha : 1 ≤ a := le_max_left _ _
  have hb : 1 ≤ b := le_max_left _ _
  have hpη := hη.pos_part
  have hpζ := hζ.pos_part
  have hmζ : ∫ z, max (ζ z) 0 ∂haar d ≤ b := le_max_right _ _
  have hm0 : 0 ≤ ∫ z, max (ζ z) 0 ∂haar d := integral_nonneg fun z => le_max_right _ _
  -- `|max x 0 - max y 0| ≤ |x - y|`
  have hpos : ∀ y, |max (η y) 0 - max (ζ y) 0| ≤ |η y - ζ y| := fun y =>
    abs_max_sub_max_le_abs (η y) (ζ y) 0
  have hab : |a - b| ≤ ∫ y, |η y - ζ y| ∂haar d := by
    have h1 : |a - b| ≤ |(∫ z, max (η z) 0 ∂haar d) - ∫ z, max (ζ z) 0 ∂haar d| := by
      simp only [a, b]
      rw [max_comm 1, max_comm 1]
      exact abs_max_sub_max_le_abs _ _ _
    refine h1.trans ?_
    rw [← integral_sub hpη hpζ]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) (hη.sub hζ).abs (Eventually.of_forall hpos))
  have hpt : ∀ y, |posNorm η y - posNorm ζ y| ≤
      |max (η y) 0 - max (ζ y) 0| + max (ζ y) 0 * (|a - b| / b) := fun y => by
    unfold posNorm
    have e : max (η y) 0 / a - max (ζ y) 0 / b =
        (max (η y) 0 - max (ζ y) 0) / a + max (ζ y) 0 * ((b - a) / (a * b)) := by
      field_simp; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < a)]
      exact div_le_self (abs_nonneg _) ha
    · rw [abs_mul, abs_of_nonneg (le_max_right _ _), abs_div, abs_sub_comm,
        abs_of_pos (by positivity : (0 : ℝ) < a * b)]
      refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
      rw [div_le_div_iff₀ (by positivity) (by linarith)]
      have := mul_nonneg (mul_nonneg (abs_nonneg (a - b)) (by linarith : (0 : ℝ) ≤ b))
        (by linarith : (0 : ℝ) ≤ a - 1)
      nlinarith
  calc ∫ y, |posNorm η y - posNorm ζ y| ∂haar d
      ≤ ∫ y, (|max (η y) 0 - max (ζ y) 0| + max (ζ y) 0 * (|a - b| / b)) ∂haar d :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          ((hpη.sub hpζ).abs.add (hpζ.mul_const _)) (Eventually.of_forall hpt)
    _ = ∫ y, |max (η y) 0 - max (ζ y) 0| ∂haar d +
          (∫ z, max (ζ z) 0 ∂haar d) * (|a - b| / b) := by
        rw [integral_add (f := fun y => |max (η y) 0 - max (ζ y) 0|)
          (g := fun y => max (ζ y) 0 * (|a - b| / b)) (hpη.sub hpζ).abs (hpζ.mul_const _),
          integral_mul_const]
    _ ≤ ∫ y, |η y - ζ y| ∂haar d + 1 * ∫ y, |η y - ζ y| ∂haar d := by
        refine add_le_add (integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hη.sub hζ).abs (Eventually.of_forall hpos)) ?_
        calc (∫ z, max (ζ z) 0 ∂haar d) * (|a - b| / b) ≤ b * (|a - b| / b) := by
              gcongr
          _ = |a - b| := by field_simp
          _ ≤ 1 * ∫ y, |η y - ζ y| ∂haar d := by rw [one_mul]; exact hab
    _ = 2 * ∫ y, |η y - ζ y| ∂haar d := by ring

/-- `|b_h| ≤ C_b ∫|h|`. -/
theorem abs_bForceL_le_integral {Cb : ℝ} (hCb : ∀ x y k, |bGrad W x y k| ≤ Cb)
    (hyp : Hyp V W KV KW) {h : Torus d → ℝ} (hh : Integrable h (haar d)) (x : Torus d)
    (k : Fin d) : |bForceL W h x k| ≤ Cb * ∫ y, |h y| ∂haar d := by
  unfold bForceL
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
    (hh.abs.const_mul Cb) (Eventually.of_forall fun y => ?_)
  show |bGrad W x y k * h y| ≤ Cb * |h y|
  rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hCb x y k) (abs_nonneg _)

theorem bForceL_sub {Cb : ℝ} (hCb : ∀ x y k, |bGrad W x y k| ≤ Cb) (hyp : Hyp V W KV KW)
    {h h' : Torus d → ℝ} (hh : Integrable h (haar d)) (hh' : Integrable h' (haar d))
    (x : Torus d) (k : Fin d) :
    bForceL W h x k - bForceL W h' x k = bForceL W (fun y => h y - h' y) x k := by
  have hm : AEStronglyMeasurable (fun y => bGrad W x y k) (haar d) :=
    ((measurable_bGrad hyp k).comp measurable_prodMk_left).aestronglyMeasurable
  have hi : ∀ {g : Torus d → ℝ}, Integrable g (haar d) →
      Integrable (fun y => bGrad W x y k * g y) (haar d) := fun {g} hg =>
    hg.bdd_mul (c := Cb) hm (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hCb x y k)
  unfold bForceL
  rw [← integral_sub (hi hh) (hi hh')]
  congr 1; funext y; ring

section Bounds

variable {LV Cb : ℝ} (hLV : ∀ x k, |lipGrad V x k| ≤ LV) (hCb : ∀ x y k, |bGrad W x y k| ≤ Cb)
  (hyp : Hyp V W KV KW)
include hLV hCb hyp

theorem abs_modFlux_le {η : Torus d → ℝ} (hη : Integrable η (haar d)) (y : Torus d) (k : Fin d) :
    |modFlux V W η y k| ≤ (LV + Cb) * |η y| := by
  have hC0 : 0 ≤ Cb := (abs_nonneg _).trans (hCb y y k)
  unfold modFlux
  rw [abs_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  refine (abs_add_le _ _).trans (add_le_add (hLV y k) ?_)
  refine (abs_bForceL_le_integral hCb hyp (integrable_posNorm hη) y k).trans ?_
  have : ∫ z, |posNorm η z| ∂haar d ≤ 1 := by
    simp_rw [abs_of_nonneg (posNorm_nonneg η _)]; exact integral_posNorm_le hη
  nlinarith

theorem abs_modFlux_sub_le {η ζ : Torus d → ℝ} (hη : Integrable η (haar d))
    (hζ : Integrable ζ (haar d)) (y : Torus d) (k : Fin d) :
    |modFlux V W η y k - modFlux V W ζ y k| ≤
      (LV + Cb) * |η y - ζ y| + |ζ y| * (2 * Cb * ∫ z, |η z - ζ z| ∂haar d) := by
  have hC0 : 0 ≤ Cb := (abs_nonneg _).trans (hCb y y k)
  have e : modFlux V W η y k - modFlux V W ζ y k =
      (η y - ζ y) * (lipGrad V y k + bForceL W (posNorm η) y k) +
        ζ y * (bForceL W (fun z => posNorm η z - posNorm ζ z) y k) := by
    unfold modFlux
    rw [← bForceL_sub hCb hyp (integrable_posNorm hη) (integrable_posNorm hζ)]
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    refine (abs_add_le _ _).trans (add_le_add (hLV y k) ?_)
    refine (abs_bForceL_le_integral hCb hyp (integrable_posNorm hη) y k).trans ?_
    have : ∫ z, |posNorm η z| ∂haar d ≤ 1 := by
      simp_rw [abs_of_nonneg (posNorm_nonneg η _)]; exact integral_posNorm_le hη
    nlinarith
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_bForceL_le_integral hCb hyp
      ((integrable_posNorm hη).sub (integrable_posNorm hζ)) y k).trans ?_
    have := integral_abs_posNorm_sub_le hη hζ
    calc Cb * ∫ z, |posNorm η z - posNorm ζ z| ∂haar d
        ≤ Cb * (2 * ∫ z, |η z - ζ z| ∂haar d) := mul_le_mul_of_nonneg_left this hC0
      _ = 2 * Cb * ∫ z, |η z - ζ z| ∂haar d := by ring

end Bounds

/-- **The weighted kernel integral** `∫₀ᵗ c(t-u)^{-1/2} e^{μu} du ≤ e^{μt}/√μ`. -/
theorem setIntegral_divConst_exp_le {t μ : ℝ} (ht : 0 < t) (hμ : 0 < μ) :
    ∫ u in Ioc 0 t, divConst (t - u) * Real.exp (μ * u) ≤ Real.exp (μ * t) / Real.sqrt μ := by
  set c : ℝ := 2 * (4 * π) ^ (-(1 : ℝ) / 2) with hc
  set g : ℝ → ℝ := fun s => s ^ (-(1 : ℝ) / 2) * Real.exp (-(μ * s)) with hg
  have hgi : IntegrableOn g (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 : ℝ) / 2) (b := μ)
      (by norm_num) one_pos hμ
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [hg, Real.rpow_one, neg_mul]
  have hg0 : ∀ s, 0 ≤ s → 0 ≤ g s := fun s hs => by simp only [hg]; positivity
  -- pointwise form on `Ioo 0 t`
  have hpt : ∀ u ∈ Ioo 0 t, divConst (t - u) * Real.exp (μ * u) =
      Real.exp (μ * t) * c * g (t - u) := fun u hu => by
    rw [divConst_eq (sub_pos.2 hu.2), hg]
    simp only
    rw [show μ * u = μ * t + -(μ * (t - u)) by ring, Real.exp_add]; ring
  have e1 : ∫ u in Ioc 0 t, divConst (t - u) * Real.exp (μ * u) =
      ∫ u in Ioc 0 t, Real.exp (μ * t) * c * g (t - u) := by
    have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ t := by
      rw [ae_iff]; simp
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    filter_upwards [hne] with u hu hmem
    exact hpt u ⟨hmem.1, lt_of_le_of_ne hmem.2 hu⟩
  have e2 : ∫ u in Ioc 0 t, g (t - u) = ∫ s in Ioc 0 t, g s := by
    rw [← intervalIntegral.integral_of_le ht.le, ← intervalIntegral.integral_of_le ht.le,
      intervalIntegral.integral_comp_sub_left (fun s => g s) t]
    simp
  have e3 : ∫ s in Ioi (0 : ℝ), g s = (1 / μ) ^ ((1 : ℝ) / 2) * Real.Gamma (1 / 2) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := μ) (by norm_num) hμ
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    simp only [hg]; norm_num
  have hle : ∫ s in Ioc 0 t, g s ≤ ∫ s in Ioi (0 : ℝ), g s :=
    setIntegral_mono_set hgi ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun s (hs : s ∈ Ioi (0 : ℝ)) => hg0 s hs.le))
      Ioc_subset_Ioi_self.eventuallyLE
  rw [e1, integral_const_mul, e2]
  have hc' : c * ((1 / μ) ^ ((1 : ℝ) / 2) * Real.Gamma (1 / 2)) = 1 / Real.sqrt μ := by
    rw [hc, Real.Gamma_one_half_eq, Real.div_rpow zero_le_one hμ.le, Real.one_rpow,
      ← Real.sqrt_eq_rpow]
    rw [show (4 * π) ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt (4 * π) by
      rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -(1 / 2) by ring,
        Real.rpow_neg (by positivity), inv_eq_one_div]]
    rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
    have : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
    field_simp
  calc Real.exp (μ * t) * c * ∫ s in Ioc 0 t, g s
      ≤ Real.exp (μ * t) * c * ∫ s in Ioi (0 : ℝ), g s := by
        gcongr
    _ = Real.exp (μ * t) / Real.sqrt μ := by rw [e3, mul_assoc, hc']; ring

end SharpLSI
