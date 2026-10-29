import Mathlib
import SharpSymmetricLSI.Infra.Entropy

/-!
# Section 6 helpers: continuity of the entropy and quadratic terms (Lemma 6.2)

Real-analysis part: the function `phi x = x² log x²` is `C¹`, with growth
`|phi' x| ≤ c (1 + |x|^κ)` for `κ > 1`, hence the Lipschitz-type estimate
`|phi x - phi y| ≤ c (1 + |x|^κ + |y|^κ) |x - y|`.
-/

noncomputable section

open Real

namespace SharpLSI.FL.Sec6

/-- `phi x = x² log x²` (value zero at zero). -/
def phi (x : ℝ) : ℝ := x ^ 2 * Real.log (x ^ 2)

/-- Derivative of `phi`, valid also at `0`. -/
def dphi (x : ℝ) : ℝ := 2 * x * (Real.log (x ^ 2) + 1)

lemma phi_eq (x : ℝ) : phi x = 2 * x * (x * Real.log x) := by
  unfold phi; rw [Real.log_pow]; push_cast; ring

lemma continuous_phi : Continuous phi := by
  have : phi = fun x => 2 * x * (x * Real.log x) := funext phi_eq
  rw [this]; exact (continuous_const.mul continuous_id).mul Real.continuous_mul_log

lemma hasDerivAt_phi (x : ℝ) : HasDerivAt phi (dphi x) x := by
  by_cases hx : x = 0
  · subst hx
    have hd : dphi 0 = 0 := by simp [dphi]
    rw [hd, hasDerivAt_iff_tendsto_slope]
    have hc : Continuous (fun x : ℝ => 2 * (x * Real.log x)) :=
      continuous_const.mul Real.continuous_mul_log
    have h0 : Filter.Tendsto (fun x : ℝ => 2 * (x * Real.log x)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      simpa using this
    refine h0.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : x ≠ 0 := hx
    simp only [slope_def_field, phi_eq, mul_zero, Real.log_zero, sub_zero]
    field_simp
  · have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h2 : HasDerivAt (fun x : ℝ => Real.log (x ^ 2)) (2 * x / x ^ 2) x :=
      h1.log (pow_ne_zero 2 hx)
    have key : HasDerivAt ((fun x : ℝ => x ^ 2) * fun x => Real.log (x ^ 2)) (dphi x) x := by
      convert h1.mul h2 using 1
      simp only [dphi]
      field_simp
    exact key

/-- Growth of `x log x` on the unit ball. -/
lemma abs_mul_log_le_one {x : ℝ} (hx : |x| ≤ 1) : |x * Real.log x| ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | h0
  · simp
  · have hpos : 0 < |x| := abs_pos.mpr h0
    have h := Real.abs_log_mul_self_lt |x| hpos hx
    rw [Real.log_abs, abs_mul, abs_abs] at h
    rw [abs_mul, mul_comm]
    exact h.le

/-- Growth bound for `dphi`: `|dphi x| ≤ c (1 + |x|^κ)` with an explicit constant. -/
lemma abs_dphi_le {κ : ℝ} (hκ : 1 < κ) (x : ℝ) :
    |dphi x| ≤ (6 + 4 / (κ - 1)) * (1 + |x| ^ κ) := by
  have hκ0 : 0 < κ - 1 := by linarith
  have hc : 0 ≤ 4 / (κ - 1) := by positivity
  have hdphi : dphi x = 4 * (x * Real.log x) + 2 * x := by
    unfold dphi; rw [Real.log_pow]; push_cast; ring
  have hxk : 0 ≤ |x| ^ κ := Real.rpow_nonneg (abs_nonneg x) κ
  rw [hdphi]
  by_cases hx : |x| ≤ 1
  · have h1 := abs_mul_log_le_one hx
    calc |4 * (x * Real.log x) + 2 * x| ≤ |4 * (x * Real.log x)| + |2 * x| := abs_add_le _ _
      _ = 4 * |x * Real.log x| + 2 * |x| := by simp [abs_mul]
      _ ≤ 4 * 1 + 2 * 1 := by gcongr
      _ ≤ (6 + 4 / (κ - 1)) * (1 + |x| ^ κ) := by nlinarith
  · rw [not_le] at hx
    have hx1 : 1 ≤ |x| := hx.le
    have hlog : Real.log |x| ≤ |x| ^ (κ - 1) / (κ - 1) :=
      Real.log_le_rpow_div (abs_nonneg x) hκ0
    have hlog0 : 0 ≤ Real.log |x| := Real.log_nonneg hx1
    have hpow : |x| * |x| ^ (κ - 1) = |x| ^ κ := by
      rw [← Real.rpow_one_add' (abs_nonneg x) (by linarith)]
      ring_nf
    have hxle : |x| ≤ |x| ^ κ := by
      calc |x| = |x| ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ |x| ^ κ := Real.rpow_le_rpow_of_exponent_le hx1 hκ.le
    have h2 : |x| * Real.log |x| ≤ |x| ^ κ / (κ - 1) := by
      calc |x| * Real.log |x| ≤ |x| * (|x| ^ (κ - 1) / (κ - 1)) := by gcongr
        _ = |x| ^ κ / (κ - 1) := by rw [← hpow]; ring
    have hxl : |x * Real.log x| = |x| * Real.log |x| := by
      rw [abs_mul, ← Real.log_abs x, abs_of_nonneg hlog0]
    calc |4 * (x * Real.log x) + 2 * x| ≤ |4 * (x * Real.log x)| + |2 * x| := abs_add_le _ _
      _ = 4 * (|x| * Real.log |x|) + 2 * |x| := by simp [abs_mul, hxl]
      _ ≤ 4 * (|x| ^ κ / (κ - 1)) + 2 * |x| ^ κ := by gcongr
      _ = (4 / (κ - 1) + 2) * |x| ^ κ := by ring
      _ ≤ (6 + 4 / (κ - 1)) * (1 + |x| ^ κ) := by nlinarith

/-- Lipschitz-type estimate for `phi`. -/
lemma abs_phi_sub_phi_le {κ : ℝ} (hκ : 1 < κ) (x y : ℝ) :
    |phi x - phi y| ≤ (6 + 4 / (κ - 1)) * (1 + |x| ^ κ + |y| ^ κ) * |x - y| := by
  set c : ℝ := 6 + 4 / (κ - 1) with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ 4 / (κ - 1) := div_nonneg (by norm_num) (by linarith)
    rw [hc]; linarith
  set M : ℝ := max |x| |y| with hM
  have hM0 : 0 ≤ M := le_trans (abs_nonneg x) (le_max_left _ _)
  have hMk : M ^ κ ≤ |x| ^ κ + |y| ^ κ := by
    rcases le_total |x| |y| with h | h
    · rw [hM, max_eq_right h]; linarith [Real.rpow_nonneg (abs_nonneg x) κ]
    · rw [hM, max_eq_left h]; linarith [Real.rpow_nonneg (abs_nonneg y) κ]
  have hxI : x ∈ Set.Icc (-M) M := by
    constructor
    · have := neg_abs_le x; have := le_max_left |x| |y|; linarith
    · have := le_abs_self x; have := le_max_left |x| |y|; linarith
  have hyI : y ∈ Set.Icc (-M) M := by
    constructor
    · have := neg_abs_le y; have := le_max_right |x| |y|; linarith
    · have := le_abs_self y; have := le_max_right |x| |y|; linarith
  have hbound : ∀ z ∈ Set.Icc (-M) M, ‖dphi z‖ ≤ c * (1 + |x| ^ κ + |y| ^ κ) := by
    intro z hz
    have hzM : |z| ≤ M := abs_le.mpr ⟨hz.1, hz.2⟩
    have h1 : |z| ^ κ ≤ M ^ κ := Real.rpow_le_rpow (abs_nonneg z) hzM (by linarith)
    have := abs_dphi_le hκ z
    rw [Real.norm_eq_abs]
    calc |dphi z| ≤ c * (1 + |z| ^ κ) := this
      _ ≤ c * (1 + |x| ^ κ + |y| ^ κ) := by
        apply mul_le_mul_of_nonneg_left _ hc0
        linarith
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := phi) (f' := dphi) (s := Set.Icc (-M) M) (x := y) (y := x)
    (fun z _ => (hasDerivAt_phi z).hasDerivWithinAt) hbound (convex_Icc _ _) hyI hxI
  simpa [Real.norm_eq_abs] using this


/-! ### Measure-theoretic part -/

section Measure

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `|∫ F| ≤ ‖F‖₁`, without integrability assumptions. -/
lemma abs_integral_le_eLpNorm_one {F : Ω → ℝ} (hF : AEStronglyMeasurable F P) :
    |∫ ω, F ω ∂P| ≤ (eLpNorm F 1 P).toReal := by
  have h := norm_integral_le_lintegral_norm (μ := P) F
  rw [Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  rw [eLpNorm_one_eq_lintegral_enorm hF]
  simp only [ofReal_norm]

/-- Hölder for a pointwise product bound. -/
lemma eLpNorm_le_of_abs_le_mul {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r] {F A G : Ω → ℝ}
    (hF : AEStronglyMeasurable F P) (hA : AEStronglyMeasurable A P)
    (hG : AEStronglyMeasurable G P) (h : ∀ᵐ ω ∂P, |F ω| ≤ |A ω| * |G ω|) :
    eLpNorm F r P ≤ eLpNorm A p P * eLpNorm G q P := by
  calc eLpNorm F r P ≤ eLpNorm (A * G) r P := by
        refine eLpNorm_mono_ae hF ?_
        filter_upwards [h] with ω hω
        simpa [abs_mul] using hω
    _ = eLpNorm (A • G) r P := rfl
    _ ≤ eLpNorm A p P * eLpNorm G q P := eLpNorm_smul_le_mul_eLpNorm hA hG

/-- The Hölder exponent `s` with `1/2 = 1/q + 1/s`. -/
def sExp (q : ℝ≥0∞) : ℝ≥0∞ := (2⁻¹ - q⁻¹)⁻¹

lemma inv_lt_inv_two {q : ℝ≥0∞} (hq : 2 < q) : q⁻¹ < 2⁻¹ := ENNReal.inv_lt_inv.mpr hq

lemma sExp_ne_top {q : ℝ≥0∞} (hq : 2 < q) : sExp q ≠ ⊤ := by
  unfold sExp
  rw [Ne, ENNReal.inv_eq_top, tsub_eq_zero_iff_le, not_le]
  exact inv_lt_inv_two hq

lemma one_le_sExp {q : ℝ≥0∞} : 1 ≤ sExp q := by
  unfold sExp
  rw [ENNReal.one_le_inv]
  calc 2⁻¹ - q⁻¹ ≤ 2⁻¹ := tsub_le_self
    _ ≤ 1 := by
      rw [ENNReal.inv_le_one]; norm_num

lemma holderTriple_sExp {q : ℝ≥0∞} (hq : 2 < q) :
    ENNReal.HolderTriple (2⁻¹ + q⁻¹)⁻¹ (sExp q) 1 := by
  refine ⟨?_⟩
  have hle : q⁻¹ ≤ 2⁻¹ := (inv_lt_inv_two hq).le
  simp only [inv_inv, sExp, inv_one]
  rw [add_assoc, add_tsub_cancel_of_le hle, ENNReal.inv_two_add_inv_two]

lemma eLpNorm_one_const [IsProbabilityMeasure P] {p : ℝ≥0∞} (h0 : p ≠ 0) (htop : p ≠ ⊤) :
    eLpNorm (fun _ : Ω => (1 : ℝ)) p P = 1 := by
  rw [eLpNorm_const' (1 : ℝ) h0 htop]
  simp

/-- Quadratic/weighted term: `|∫ (X² - Y²) W| ≤ ‖X - Y‖₂ (‖X‖_q + ‖Y‖_q) ‖W‖_s`. -/
lemma abs_integral_sq_sub_sq_mul_le {q : ℝ≥0∞} (hq : 2 < q) {X Y W : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P)
    (hW : AEStronglyMeasurable W P) {δ B₁ B₂ β : ℝ} (hδ : 0 ≤ δ) (hB₁ : 0 ≤ B₁)
    (hB₂ : 0 ≤ B₂) (hβ : 0 ≤ β) (h1 : eLpNorm (X - Y) 2 P ≤ ENNReal.ofReal δ)
    (h2 : eLpNorm X q P ≤ ENNReal.ofReal B₁) (h3 : eLpNorm Y q P ≤ ENNReal.ofReal B₂)
    (h4 : eLpNorm W (sExp q) P ≤ ENNReal.ofReal β) :
    |∫ ω, (X ω ^ 2 - Y ω ^ 2) * W ω ∂P| ≤ δ * (B₁ + B₂) * β := by
  have h2q : ENNReal.HolderTriple 2 q (2⁻¹ + q⁻¹)⁻¹ := ENNReal.HolderTriple.of 2 q
  have h3q : ENNReal.HolderTriple (2⁻¹ + q⁻¹)⁻¹ (sExp q) 1 := holderTriple_sExp hq
  have hXY : AEStronglyMeasurable (X - Y) P := hX.sub hY
  have hXpY : AEStronglyMeasurable (X + Y) P := hX.add hY
  have hq1 : 1 ≤ q := (by norm_num : (1 : ℝ≥0∞) ≤ 2).trans hq.le
  have hprod : AEStronglyMeasurable ((X - Y) * (X + Y)) P := hXY.mul hXpY
  have s1 : eLpNorm ((X - Y) * (X + Y)) (2⁻¹ + q⁻¹)⁻¹ P ≤
      eLpNorm (X - Y) 2 P * eLpNorm (X + Y) q P :=
    eLpNorm_le_of_abs_le_mul hprod hXY hXpY (Filter.Eventually.of_forall fun ω => by
      simp [abs_mul])
  have s2 : eLpNorm (fun ω => (X ω ^ 2 - Y ω ^ 2) * W ω) 1 P ≤
      eLpNorm ((X - Y) * (X + Y)) (2⁻¹ + q⁻¹)⁻¹ P * eLpNorm W (sExp q) P := by
    refine eLpNorm_le_of_abs_le_mul (p := (2⁻¹ + q⁻¹)⁻¹) (q := sExp q)
      (((hX.pow 2).sub (hY.pow 2)).mul hW) hprod hW (Filter.Eventually.of_forall fun ω => ?_)
    have : (X ω ^ 2 - Y ω ^ 2) = (X ω - Y ω) * (X ω + Y ω) := by ring
    simp only [this, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, abs_mul]
    exact le_rfl
  have s3 : eLpNorm (X + Y) q P ≤ ENNReal.ofReal (B₁ + B₂) := by
    calc eLpNorm (X + Y) q P ≤ eLpNorm X q P + eLpNorm Y q P := eLpNorm_add_le hq1
      _ ≤ ENNReal.ofReal B₁ + ENNReal.ofReal B₂ := add_le_add h2 h3
      _ = ENNReal.ofReal (B₁ + B₂) := (ENNReal.ofReal_add hB₁ hB₂).symm
  have s4 : eLpNorm (fun ω => (X ω ^ 2 - Y ω ^ 2) * W ω) 1 P ≤
      ENNReal.ofReal (δ * (B₁ + B₂) * β) := by
    calc _ ≤ _ := s2
      _ ≤ (eLpNorm (X - Y) 2 P * eLpNorm (X + Y) q P) * eLpNorm W (sExp q) P := by gcongr
      _ ≤ (ENNReal.ofReal δ * ENNReal.ofReal (B₁ + B₂)) * ENNReal.ofReal β := by gcongr
      _ = ENNReal.ofReal (δ * (B₁ + B₂) * β) := by
        rw [← ENNReal.ofReal_mul hδ, ← ENNReal.ofReal_mul (by positivity)]
  exact (abs_integral_le_eLpNorm_one (((hX.pow 2).sub (hY.pow 2)).mul hW)).trans
    (ENNReal.toReal_le_of_le_ofReal (by positivity) s4)

/-- `(A)`: `|∫ X² - ∫ Y²| ≤ ‖X - Y‖₂ (‖X‖_q + ‖Y‖_q)`. -/
lemma abs_integral_sq_sub_sq_le [IsProbabilityMeasure P] {q : ℝ≥0∞} (hq : 2 < q)
    {X Y : Ω → ℝ} (hX : MemLp X q P) (hY : MemLp Y q P) {δ B₁ B₂ : ℝ} (hδ : 0 ≤ δ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (h1 : eLpNorm (X - Y) 2 P ≤ ENNReal.ofReal δ)
    (h2 : eLpNorm X q P ≤ ENNReal.ofReal B₁) (h3 : eLpNorm Y q P ≤ ENNReal.ofReal B₂) :
    |∫ ω, X ω ^ 2 ∂P - ∫ ω, Y ω ^ 2 ∂P| ≤ δ * (B₁ + B₂) := by
  have hX2 : MemLp X 2 P := hX.mono_exponent hq.le
  have hY2 : MemLp Y 2 P := hY.mono_exponent hq.le
  have hs0 : sExp q ≠ 0 := (zero_lt_one.trans_le one_le_sExp).ne'
  have hW : eLpNorm (fun _ : Ω => (1 : ℝ)) (sExp q) P ≤ ENNReal.ofReal 1 := by
    rw [eLpNorm_one_const hs0 (sExp_ne_top hq)]; simp
  have := abs_integral_sq_sub_sq_mul_le hq hX.aestronglyMeasurable hY.aestronglyMeasurable
    aestronglyMeasurable_const hδ hB₁ hB₂ zero_le_one h1 h2 h3 hW
  simp only [mul_one] at this
  rw [integral_sub hX2.integrable_sq hY2.integrable_sq] at this
  simpa using this

/-- Quadratic term on a probability space: `∫ X² ≤ B²`. -/
lemma integral_sq_le [IsProbabilityMeasure P] {q : ℝ≥0∞} (hq : 2 < q) {X : Ω → ℝ}
    (hX : MemLp X q P) {B : ℝ} (hB : 0 ≤ B) (h : eLpNorm X q P ≤ ENNReal.ofReal B) :
    ∫ ω, X ω ^ 2 ∂P ≤ B ^ 2 := by
  have h0 : MemLp (fun _ : Ω => (0 : ℝ)) q P := memLp_const 0
  have h1 : eLpNorm (X - fun _ : Ω => (0 : ℝ)) 2 P ≤ ENNReal.ofReal B := by
    have : (X - fun _ : Ω => (0 : ℝ)) = X := by ext; simp
    rw [this]
    exact (eLpNorm_le_eLpNorm_of_exponent_le hq.le).trans h
  have h2 : eLpNorm (fun _ : Ω => (0 : ℝ)) q P ≤ ENNReal.ofReal 0 := by simp
  have := abs_integral_sq_sub_sq_le hq hX h0 (δ := B) (B₁ := B) (B₂ := 0) hB hB le_rfl h1 h h2
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero,
    sub_zero, add_zero] at this
  nlinarith [le_abs_self (∫ ω, X ω ^ 2 ∂P)]

/-! ### Entropy -/

/-- `psi t = t log t`. -/
def psi (t : ℝ) : ℝ := t * Real.log t

/-- The constant in the growth bound for `phi'`. -/
def cphi (κ : ℝ) : ℝ := 6 + 4 / (κ - 1)

lemma cphi_nonneg {κ : ℝ} (hκ : 1 < κ) : 0 ≤ cphi κ := by
  unfold cphi
  have : 0 ≤ 4 / (κ - 1) := div_nonneg (by norm_num) (by linarith)
  linarith

lemma half_toReal_gt_one {q : ℝ≥0∞} (hq : 2 < q) (hq' : q ≠ ⊤) : 1 < q.toReal / 2 := by
  have : (2 : ℝ≥0∞).toReal < q.toReal := (ENNReal.toReal_lt_toReal (by simp) hq').mpr hq
  simp at this
  linarith

lemma eLpNorm_abs_rpow_le {q : ℝ≥0∞} (hq : 2 < q) (hq' : q ≠ ⊤) {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X P) {B : ℝ} (hB : 0 ≤ B) (h : eLpNorm X q P ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => |X ω| ^ (q.toReal / 2)) 2 P ≤ ENNReal.ofReal (B ^ (q.toReal / 2)) := by
  have hκ : 0 < q.toReal / 2 := by linarith [half_toReal_gt_one hq hq']
  have key := eLpNorm_norm_rpow (p := (2 : ℝ≥0∞)) X hX hκ
  have e2 : (2 : ℝ≥0∞) * ENNReal.ofReal (q.toReal / 2) = q := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num),
      show (2 : ℝ) * (q.toReal / 2) = q.toReal by ring, ENNReal.ofReal_toReal hq']
  simp only [Real.norm_eq_abs] at key
  rw [key, e2, ← ENNReal.ofReal_rpow_of_nonneg hB hκ.le]
  exact ENNReal.rpow_le_rpow h hκ.le

lemma aesm_abs_rpow {X : Ω → ℝ} (hX : AEStronglyMeasurable X P) (κ : ℝ) :
    AEStronglyMeasurable (fun ω => |X ω| ^ κ) P :=
  (hX.norm.aemeasurable.pow_const κ).aestronglyMeasurable

lemma aesm_phi {X : Ω → ℝ} (hX : AEStronglyMeasurable X P) :
    AEStronglyMeasurable (fun ω => phi (X ω)) P :=
  continuous_phi.comp_aestronglyMeasurable hX

/-- `1 + |X|^κ + |Y|^κ` is in `L²` with a norm bound. -/
lemma eLpNorm_g_le [IsProbabilityMeasure P] {q : ℝ≥0∞} (hq : 2 < q) (hq' : q ≠ ⊤)
    {X Y : Ω → ℝ} (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P) {B : ℝ}
    (hB : 0 ≤ B) (h1 : eLpNorm X q P ≤ ENNReal.ofReal B) (h2 : eLpNorm Y q P ≤ ENNReal.ofReal B) :
    eLpNorm (fun ω => 1 + |X ω| ^ (q.toReal / 2) + |Y ω| ^ (q.toReal / 2)) 2 P ≤
      ENNReal.ofReal (1 + 2 * B ^ (q.toReal / 2)) := by
  have hκ : 0 ≤ B ^ (q.toReal / 2) := Real.rpow_nonneg hB _
  have a1 := eLpNorm_abs_rpow_le hq hq' hX hB h1
  have a2 := eLpNorm_abs_rpow_le hq hq' hY hB h2
  have hsum : (fun ω => 1 + |X ω| ^ (q.toReal / 2) + |Y ω| ^ (q.toReal / 2)) =
      ((fun _ : Ω => (1 : ℝ)) + fun ω => |X ω| ^ (q.toReal / 2)) +
        fun ω => |Y ω| ^ (q.toReal / 2) := rfl
  rw [hsum]
  calc _ ≤ eLpNorm ((fun _ : Ω => (1 : ℝ)) + fun ω => |X ω| ^ (q.toReal / 2)) 2 P +
        eLpNorm (fun ω => |Y ω| ^ (q.toReal / 2)) 2 P :=
        eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (fun _ : Ω => (1 : ℝ)) 2 P + eLpNorm (fun ω => |X ω| ^ (q.toReal / 2)) 2 P) +
        eLpNorm (fun ω => |Y ω| ^ (q.toReal / 2)) 2 P := by
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ (ENNReal.ofReal 1 + ENNReal.ofReal (B ^ (q.toReal / 2))) +
        ENNReal.ofReal (B ^ (q.toReal / 2)) := by
        gcongr
        rw [eLpNorm_one_const (by norm_num) (by norm_num)]; simp
    _ = ENNReal.ofReal (1 + 2 * B ^ (q.toReal / 2)) := by
        rw [← ENNReal.ofReal_add zero_le_one hκ, ← ENNReal.ofReal_add (by positivity) hκ]
        congr 1; ring

/-- `phi ∘ X` is integrable for `X ∈ L^q`, `q > 2`. -/
lemma integrable_phi [IsProbabilityMeasure P] {q : ℝ≥0∞} (hq : 2 < q) (hq' : q ≠ ⊤)
    {X : Ω → ℝ} (hX : MemLp X q P) : Integrable (fun ω => phi (X ω)) P := by
  set κ := q.toReal / 2 with hκdef
  have hκ : 1 < κ := half_toReal_gt_one hq hq'
  have hX2 : MemLp X 2 P := hX.mono_exponent hq.le
  have hBfin : eLpNorm X q P ≤ ENNReal.ofReal (eLpNorm X q P).toReal :=
    (ENNReal.ofReal_toReal (memLp_iff.mp hX).ne).ge
  have hg1 := eLpNorm_abs_rpow_le hq hq' hX.aestronglyMeasurable ENNReal.toReal_nonneg hBfin
  have hg : MemLp (fun ω => |X ω| ^ κ) 2 P :=
    lt_of_le_of_lt hg1 ENNReal.ofReal_lt_top
  have hg' : MemLp (fun ω => 1 + |X ω| ^ κ) 2 P := (memLp_const (1 : ℝ)).add hg
  have hprod : Integrable ((fun ω => 1 + |X ω| ^ κ) * fun ω => |X ω|) P :=
    hg'.integrable_mul hX2.norm
  refine Integrable.mono' (hprod.const_mul (cphi κ)) (aesm_phi hX.aestronglyMeasurable)
    (Filter.Eventually.of_forall
    fun ω => ?_)
  have hb := abs_phi_sub_phi_le hκ (X ω) 0
  have h0 : phi 0 = 0 := by simp [phi]
  have hz : |(0 : ℝ)| ^ κ = 0 := by
    rw [abs_zero]; exact Real.zero_rpow (by linarith)
  rw [h0, hz] at hb
  simp only [Real.norm_eq_abs, Pi.mul_apply, sub_zero, add_zero] at hb ⊢
  calc _ ≤ _ := hb
    _ = _ := by simp only [cphi]; ring

lemma ent_toReal_eq [IsProbabilityMeasure P] {q : ℝ≥0∞} (hq : 2 < q) (hq' : q ≠ ⊤)
    {X : Ω → ℝ} (hX : MemLp X q P) :
    (ent P (fun ω => X ω ^ 2)).toReal =
      max (∫ ω, phi (X ω) ∂P - psi (∫ ω, X ω ^ 2 ∂P)) 0 := by
  have hX2 : MemLp X 2 P := hX.mono_exponent hq.le
  rw [ent_eq_formula P _ (fun ω => sq_nonneg _) hX2.integrable_sq (integrable_phi hq hq' hX),
    ENNReal.toReal_ofReal']
  rfl

lemma abs_ent_toReal_sub_le [IsProbabilityMeasure P] {q : ℝ≥0∞} (hq : 2 < q) (hq' : q ≠ ⊤)
    {X Y : Ω → ℝ} (hX : MemLp X q P) (hY : MemLp Y q P) :
    |(ent P (fun ω => X ω ^ 2)).toReal - (ent P (fun ω => Y ω ^ 2)).toReal| ≤
      |∫ ω, phi (X ω) ∂P - ∫ ω, phi (Y ω) ∂P| +
        |psi (∫ ω, X ω ^ 2 ∂P) - psi (∫ ω, Y ω ^ 2 ∂P)| := by
  rw [ent_toReal_eq hq hq' hX, ent_toReal_eq hq hq' hY]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have := abs_sub (∫ ω, phi (X ω) ∂P - ∫ ω, phi (Y ω) ∂P)
    (psi (∫ ω, X ω ^ 2 ∂P) - psi (∫ ω, Y ω ^ 2 ∂P))
  refine le_trans (le_of_eq (by congr 1; ring)) this

/-- `|∫ phi X - ∫ phi Y| ≤ c (1 + 2 B^κ) ‖X - Y‖₂`. -/
lemma abs_integral_phi_sub_le [IsProbabilityMeasure P] {q : ℝ≥0∞} (hq : 2 < q) (hq' : q ≠ ⊤)
    {X Y : Ω → ℝ} (hX : MemLp X q P) (hY : MemLp Y q P) {δ B : ℝ} (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (h1 : eLpNorm X q P ≤ ENNReal.ofReal B) (h2 : eLpNorm Y q P ≤ ENNReal.ofReal B)
    (h3 : eLpNorm (X - Y) 2 P ≤ ENNReal.ofReal δ) :
    |∫ ω, phi (X ω) ∂P - ∫ ω, phi (Y ω) ∂P| ≤
      cphi (q.toReal / 2) * (1 + 2 * B ^ (q.toReal / 2)) * δ := by
  set κ := q.toReal / 2 with hκdef
  have hκ : 1 < κ := half_toReal_gt_one hq hq'
  have hc := cphi_nonneg hκ
  have hBκ : 0 ≤ B ^ κ := Real.rpow_nonneg hB _
  rw [← integral_sub (integrable_phi hq hq' hX) (integrable_phi hq hq' hY)]
  refine (abs_integral_le_eLpNorm_one ((aesm_phi hX.aestronglyMeasurable).sub
    (aesm_phi hY.aestronglyMeasurable))).trans
    (ENNReal.toReal_le_of_le_ofReal (by positivity) ?_)
  have hg := eLpNorm_g_le hq hq' hX.aestronglyMeasurable hY.aestronglyMeasurable hB h1 h2
  have hA : AEStronglyMeasurable (fun ω => cphi κ * (1 + |X ω| ^ κ + |Y ω| ^ κ)) P :=
    (aestronglyMeasurable_const.mul
      ((aestronglyMeasurable_const.add (aesm_abs_rpow hX.aestronglyMeasurable κ)).add
        (aesm_abs_rpow hY.aestronglyMeasurable κ)))
  have hmain : eLpNorm (fun ω => phi (X ω) - phi (Y ω)) 1 P ≤
      eLpNorm (fun ω => cphi κ * (1 + |X ω| ^ κ + |Y ω| ^ κ)) 2 P * eLpNorm (X - Y) 2 P :=
    eLpNorm_le_of_abs_le_mul (p := 2) (q := 2) ((aesm_phi hX.aestronglyMeasurable).sub
      (aesm_phi hY.aestronglyMeasurable)) hA
      (hX.aestronglyMeasurable.sub hY.aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => by
        have hb := abs_phi_sub_phi_le hκ (X ω) (Y ω)
        have hpos : 0 ≤ cphi κ * (1 + |X ω| ^ κ + |Y ω| ^ κ) := by
          have := Real.rpow_nonneg (abs_nonneg (X ω)) κ
          have := Real.rpow_nonneg (abs_nonneg (Y ω)) κ
          positivity
        rw [abs_of_nonneg hpos]
        simpa [cphi] using hb)
  have hscal : eLpNorm (fun ω => cphi κ * (1 + |X ω| ^ κ + |Y ω| ^ κ)) 2 P ≤
      ENNReal.ofReal (cphi κ) * ENNReal.ofReal (1 + 2 * B ^ κ) := by
    have : (fun ω => cphi κ * (1 + |X ω| ^ κ + |Y ω| ^ κ)) =
        cphi κ • fun ω => 1 + |X ω| ^ κ + |Y ω| ^ κ := rfl
    rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
    gcongr
  calc _ ≤ _ := hmain
    _ ≤ (ENNReal.ofReal (cphi κ) * ENNReal.ofReal (1 + 2 * B ^ κ)) * ENNReal.ofReal δ := by
      gcongr
    _ = ENNReal.ofReal (cphi κ * (1 + 2 * B ^ κ) * δ) := by
      rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul (by positivity)]

/-! ### The two moduli of Lemma 6.2 -/

/-- Lemma 6.2, (6.16), as a modulus. -/
theorem entropy_modulus (q : ℝ≥0∞) (hq : 2 < q) (hq' : q ≠ ⊤) (B ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X Y : Ω → ℝ), MemLp X q P → MemLp Y q P →
      eLpNorm X q P ≤ ENNReal.ofReal B → eLpNorm Y q P ≤ ENNReal.ofReal B →
      eLpNorm (X - Y) 2 P ≤ ENNReal.ofReal δ →
      |(ent P (fun ω => X ω ^ 2)).toReal - (ent P (fun ω => Y ω ^ 2)).toReal| ≤ ε ∧
        |∫ ω, X ω ^ 2 ∂P - ∫ ω, Y ω ^ 2 ∂P| ≤ ε := by
  set B' : ℝ := max B 1 with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set κ := q.toReal / 2 with hκdef
  have hκ : 1 < κ := half_toReal_gt_one hq hq'
  set c := cphi κ with hcdef
  have hc : 0 ≤ c := cphi_nonneg hκ
  set G : ℝ := 1 + 2 * B' ^ κ with hGdef
  have hG : 0 < G := by
    have := Real.rpow_nonneg hB'pos.le κ
    positivity
  have huc : UniformContinuousOn psi (Set.Icc 0 (B' ^ 2)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous Real.continuous_mul_log.continuousOn
  obtain ⟨η, hη, hηH⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
  set δ : ℝ := min (min (η / (4 * B')) (ε / (2 * (c + 1) * G))) (ε / (2 * B')) with hδdef
  have hδpos : 0 < δ := by
    have : 0 < c + 1 := by linarith
    positivity
  have hδ1 : δ ≤ η / (4 * B') := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ ε / (2 * (c + 1) * G) := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ ε / (2 * B') := min_le_right _ _
  refine ⟨δ, hδpos, ?_⟩
  intro Ω _ P _ X Y hX hY hXB hYB hXY
  have hXB' : eLpNorm X q P ≤ ENNReal.ofReal B' := hXB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hYB' : eLpNorm Y q P ≤ ENNReal.ofReal B' := hYB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hquad := abs_integral_sq_sub_sq_le hq hX hY hδpos.le hB'pos.le hB'pos.le hXY hXB' hYB'
  have hquad2 : δ * (B' + B') ≤ ε := by
    calc δ * (B' + B') ≤ ε / (2 * B') * (B' + B') := by gcongr
      _ = ε := by field_simp; ring
  refine ⟨?_, hquad.trans hquad2⟩
  have hs : ∫ ω, X ω ^ 2 ∂P ∈ Set.Icc 0 (B' ^ 2) :=
    ⟨integral_nonneg fun ω => sq_nonneg _, integral_sq_le hq hX hB'pos.le hXB'⟩
  have ht : ∫ ω, Y ω ^ 2 ∂P ∈ Set.Icc 0 (B' ^ 2) :=
    ⟨integral_nonneg fun ω => sq_nonneg _, integral_sq_le hq hY hB'pos.le hYB'⟩
  have hdist : dist (∫ ω, X ω ^ 2 ∂P) (∫ ω, Y ω ^ 2 ∂P) < η := by
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (hquad.trans ?_) (half_lt_self hη)
    calc δ * (B' + B') ≤ η / (4 * B') * (B' + B') := by gcongr
      _ = η / 2 := by field_simp; ring
  have hpsi := hηH _ hs _ ht hdist
  rw [Real.dist_eq] at hpsi
  have hphi := abs_integral_phi_sub_le hq hq' hX hY hδpos.le hB'pos.le hXB' hYB' hXY
  have hphi2 : c * (1 + 2 * B' ^ κ) * δ ≤ ε / 2 := by
    have h1 : c * G * δ ≤ (c + 1) * G * δ := by gcongr; linarith
    have h2 : (c + 1) * G * δ ≤ (c + 1) * G * (ε / (2 * (c + 1) * G)) := by gcongr
    have h3 : (c + 1) * G * (ε / (2 * (c + 1) * G)) = ε / 2 := by
      have : 0 < c + 1 := by linarith
      field_simp
    exact le_trans h1 (h3 ▸ h2)
  calc _ ≤ _ := abs_ent_toReal_sub_le hq hq' hX hY
    _ ≤ ε / 2 + ε / 2 := add_le_add (hphi.trans hphi2) hpsi.le
    _ = ε := by ring

/-- Lemma 6.2, (6.17), as a modulus. -/
theorem weighted_modulus (q : ℝ≥0∞) (hq : 2 < q) (_hq' : q ≠ ⊤) (B : ℝ) (Bs : ℝ≥0∞ → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X Y W : Ω → ℝ), MemLp X q P → MemLp Y q P →
      eLpNorm X q P ≤ ENNReal.ofReal B → eLpNorm Y q P ≤ ENNReal.ofReal B →
      (∀ s : ℝ≥0∞, 1 ≤ s → s ≠ ⊤ → MemLp W s P ∧ eLpNorm W s P ≤ ENNReal.ofReal (Bs s)) →
      eLpNorm (X - Y) 2 P ≤ ENNReal.ofReal δ →
      |∫ ω, (X ω ^ 2 - Y ω ^ 2) * W ω ∂P| ≤ ε := by
  set B' : ℝ := max B 1 with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set β : ℝ := max (Bs (sExp q)) 0 with hβdef
  have hβ : 0 ≤ β := le_max_right _ _
  set δ : ℝ := ε / (2 * B' * (β + 1)) with hδdef
  have hδpos : 0 < δ := by positivity
  refine ⟨δ, hδpos, ?_⟩
  intro Ω _ P _ X Y W hX hY hXB hYB hW hXY
  have hXB' : eLpNorm X q P ≤ ENNReal.ofReal B' := hXB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hYB' : eLpNorm Y q P ≤ ENNReal.ofReal B' := hYB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  obtain ⟨hWmem, hWB⟩ := hW (sExp q) one_le_sExp (sExp_ne_top hq)
  have hWB' : eLpNorm W (sExp q) P ≤ ENNReal.ofReal β :=
    hWB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have := abs_integral_sq_sub_sq_mul_le hq hX.aestronglyMeasurable hY.aestronglyMeasurable
    hWmem.aestronglyMeasurable hδpos.le hB'pos.le hB'pos.le hβ hXY hXB' hYB' hWB'
  refine this.trans ?_
  have hβ1 : 0 < β + 1 := by linarith
  calc δ * (B' + B') * β = ε * β / (β + 1) := by
        rw [hδdef]; field_simp; ring
    _ ≤ ε := by
        rw [div_le_iff₀ hβ1]; nlinarith

end Measure

end SharpLSI.FL.Sec6
