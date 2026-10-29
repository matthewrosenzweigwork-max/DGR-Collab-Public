import SharpSymmetricLSI.Paper.CosineTest
import SharpSymmetricLSI.Infra.Entropy

/-!
# Lemma 2.5, part 1: the entropy of `(1 + t g)²` for bounded `g` (manuscript (2.6))

`ent_one_add_ge`: on a probability space, for `|g| ≤ A` and `0 < t A ≤ 1/16`,
`Ent((1 + t g)²) ≥ 2 t² Var(g) - 25 t³ A³`.  (This is the lower half of (2.6) with an explicit
constant, which is all that the proof of Lemma 2.5 uses.)
-/

open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

/-- The final real-number estimate in `ent_one_add_ge`. -/
theorem ent_one_add_final {t A V Q D : ℝ} (hA : 0 < A) (ht : 0 < t) (hτ : t * A ≤ 1 / 16)
    (hV : V ≤ A ^ 2) (hQ0 : 0 ≤ Q) (hQ : 4 * t ^ 2 * V - 5 * t ^ 3 * A ^ 3 ≤ Q)
    (hD0 : 0 < D) (hD : D ≤ 1 + 11 * (t * A)) :
    2 * t ^ 2 * V - 25 * t ^ 3 * A ^ 3 ≤ Q / (2 * D) := by
  set τ := t * A with hτdef
  have hτ0 : 0 < τ := mul_pos ht hA
  have h1 : 1 - 11 * τ ≤ 1 / D := by
    have : 1 / (1 + 11 * τ) ≤ 1 / D := one_div_le_one_div_of_le hD0 hD
    have h2 : 1 - 11 * τ ≤ 1 / (1 + 11 * τ) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg τ]
    linarith
  have h3 : Q / (2 * D) = Q / 2 * (1 / D) := by field_simp
  have h11 : 0 ≤ 1 - 11 * τ := by linarith
  have h4 : Q / 2 * (1 - 11 * τ) ≤ Q / 2 * (1 / D) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h5 : (4 * t ^ 2 * V - 5 * t ^ 3 * A ^ 3) / 2 * (1 - 11 * τ) ≤ Q / 2 * (1 - 11 * τ) :=
    mul_le_mul_of_nonneg_right (by linarith) h11
  rw [h3]
  refine le_trans ?_ (h5.trans h4)
  have h6 : t ^ 3 * A * V ≤ t ^ 3 * A * A ^ 2 := mul_le_mul_of_nonneg_left hV (by positivity)
  have hτe : τ = t * A := rfl
  have e : (4 * t ^ 2 * V - 5 * t ^ 3 * A ^ 3) / 2 * (1 - 11 * τ) =
      2 * t ^ 2 * V - 5 / 2 * t ^ 3 * A ^ 3 - 22 * (t ^ 3 * A * V) + 55 / 2 * (t ^ 4 * A ^ 4) := by
    rw [hτe]; ring
  rw [e]
  have h7 : 0 ≤ t ^ 4 * A ^ 4 := by positivity
  have h8 : t ^ 3 * A * A ^ 2 = t ^ 3 * A ^ 3 := by ring
  nlinarith

section Ent

variable {α : Type*} [MeasurableSpace α]

set_option maxHeartbeats 1600000 in
theorem ent_one_add_ge (P : Measure α) [IsProbabilityMeasure P] (g : α → ℝ)
    (hgm : AEStronglyMeasurable g P) {A t : ℝ} (hA : 0 < A) (ht : 0 < t)
    (hτ : t * A ≤ 1 / 16) (hg : ∀ x, |g x| ≤ A) :
    ENNReal.ofReal (2 * t ^ 2 * ((∫ x, g x ^ 2 ∂P) - (∫ x, g x ∂P) ^ 2) - 25 * t ^ 3 * A ^ 3) ≤
      ent P (fun x => (1 + t * g x) ^ 2) := by
  classical
  set τ := t * A with hτdef
  have hτ0 : 0 < τ := mul_pos ht hA
  set a := ∫ x, g x ∂P with ha
  set b := ∫ x, g x ^ 2 ∂P with hb
  have hgA : ∀ x, ‖g x‖ ≤ A := fun x => by simpa [Real.norm_eq_abs] using hg x
  have hint : Integrable g P := Integrable.of_bound hgm A (Filter.Eventually.of_forall hgA)
  have hgsqm : AEStronglyMeasurable (fun x => g x ^ 2) P := hgm.pow 2
  have hgsq : ∀ x, g x ^ 2 ≤ A ^ 2 := fun x => by
    have := hg x
    nlinarith [abs_nonneg (g x), sq_abs (g x)]
  have hint2 : Integrable (fun x => g x ^ 2) P :=
    Integrable.of_bound hgsqm (A ^ 2) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hgsq x)
  have ha_abs : |a| ≤ A := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := g) (C := A) (Filter.Eventually.of_forall hgA)
    simpa [Real.norm_eq_abs] using this
  have hb0 : 0 ≤ b := integral_nonneg fun x => sq_nonneg _
  have hbA : b ≤ A ^ 2 := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := fun x => g x ^ 2) (C := A ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hgsq x)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  have haA := abs_le.1 ha_abs
  -- the mean `m` of `u = (1 + t g)²`
  set m := 1 + 2 * t * a + t ^ 2 * b with hmdef
  have hu_eq : (fun x => (1 + t * g x) ^ 2) = fun x => (1 + 2 * t * g x) + t ^ 2 * g x ^ 2 := by
    funext x; ring
  have hu_int : Integrable (fun x => (1 + t * g x) ^ 2) P := by
    rw [hu_eq]
    exact ((integrable_const 1).add (hint.const_mul (2 * t))).add (hint2.const_mul (t ^ 2))
  have hm : ∫ x, (1 + t * g x) ^ 2 ∂P = m := by
    have i1 : Integrable (fun x => 1 + 2 * t * g x) P :=
      (integrable_const 1).add (hint.const_mul (2 * t))
    have i2 : Integrable (fun x => t ^ 2 * g x ^ 2) P := hint2.const_mul (t ^ 2)
    have i3 : Integrable (fun x => (1 : ℝ)) P := integrable_const 1
    have i4 : Integrable (fun x => 2 * t * g x) P := hint.const_mul (2 * t)
    rw [hu_eq, integral_add i1 i2, integral_add i3 i4, integral_const_mul, integral_const_mul]
    simp [ha, hb, hmdef]
  have hm_lo : 1 - 2 * τ ≤ m := by
    have : 2 * t * a ≥ -(2 * τ) := by nlinarith [haA.1]
    have : 0 ≤ t ^ 2 * b := by positivity
    simp only [hmdef]; linarith
  have hm_hi : m ≤ 1 + 3 * τ := by
    have h1 : 2 * t * a ≤ 2 * τ := by nlinarith [haA.2]
    have h2 : t ^ 2 * b ≤ τ ^ 2 := by
      have : t ^ 2 * b ≤ t ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_left hbA (by positivity)
      calc t ^ 2 * b ≤ t ^ 2 * A ^ 2 := this
        _ = τ ^ 2 := by rw [hτdef]; ring
    have : τ ^ 2 ≤ τ := by nlinarith
    simp only [hmdef]; linarith
  have hm_pos : 0 < m := by linarith
  -- range of `u`
  have hu_rng : ∀ x, 1 - 2 * τ ≤ (1 + t * g x) ^ 2 ∧ (1 + t * g x) ^ 2 ≤ 1 + 3 * τ := by
    intro x
    have hx : |t * g x| ≤ τ := by
      rw [abs_mul, abs_of_pos ht]; exact mul_le_mul_of_nonneg_left (hg x) ht.le
    have hx' := abs_le.1 hx
    constructor <;> nlinarith [sq_nonneg (t * g x)]
  have hdiff : ∀ x, |(1 + t * g x) ^ 2 - m| ≤ 5 * τ := fun x => by
    obtain ⟨h1, h2⟩ := hu_rng x
    rw [abs_le]; constructor <;> linarith
  -- the pointwise lower bound for the integrand of `ent`
  set δ : ℝ := 6 * τ with hδ
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  set c0 : ℝ := 1 / (2 * m * (1 + δ)) with hc0
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  have hpt : ∀ x, c0 * ((1 + t * g x) ^ 2 - m) ^ 2 ≤
      m * klFun ((1 + t * g x) ^ 2 / m) := by
    intro x
    set u := (1 + t * g x) ^ 2 with hu
    set w := u / m - 1 with hw
    have hwδ : |w| ≤ δ := by
      have : w = (u - m) / m := by rw [hw]; field_simp
      rw [this, abs_div, abs_of_pos hm_pos, div_le_iff₀ hm_pos]
      have := hdiff x
      have h7 : (7 : ℝ) / 8 ≤ m := by linarith
      calc |u - m| ≤ 5 * τ := this
        _ ≤ δ * m := by rw [hδ]; nlinarith
    have hT := (mul_log_taylor_bounds hδ1 hwδ).1
    have hk : klFun (u / m) = (1 + w) * Real.log (1 + w) - w := by
      rw [klFun_apply]
      have : u / m = 1 + w := by rw [hw]; ring
      rw [this]; ring
    have hk2 : w ^ 2 / (2 * (1 + δ)) ≤ klFun (u / m) := by rw [hk]; linarith
    have : m * (w ^ 2 / (2 * (1 + δ))) = c0 * (u - m) ^ 2 := by
      have : w = (u - m) / m := by rw [hw]; field_simp
      rw [this, hc0]; field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left hk2 hm_pos.le
  -- integrate
  have hG_int : Integrable (fun x => c0 * ((1 + t * g x) ^ 2 - m) ^ 2) P := by
    refine Integrable.of_bound ?_ (c0 * (5 * τ) ^ 2) (Filter.Eventually.of_forall fun x => ?_)
    · have hc : Continuous fun s : ℝ => c0 * ((1 + t * s) ^ 2 - m) ^ 2 := by fun_prop
      exact hc.comp_aestronglyMeasurable hgm
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ hc0pos.le
      have := abs_le.1 (hdiff x)
      nlinarith
  have hlow : ENNReal.ofReal (∫ x, c0 * ((1 + t * g x) ^ 2 - m) ^ 2 ∂P) ≤
      ent P (fun x => (1 + t * g x) ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hG_int
      (Filter.Eventually.of_forall fun x => by positivity)]
    unfold ent
    rw [if_pos hu_int]
    simp only [hm]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
  refine le_trans ?_ hlow
  apply ENNReal.ofReal_le_ofReal
  -- `∫ (u - m)² ≥ 4 t² V - 5 t³ A³`
  set θ : ℝ := τ with hθ
  have hθ0 : 0 < θ := hτ0
  have hθ1 : θ ≤ 1 := by linarith
  set c1 : ℝ := 4 * t ^ 2 * (1 - θ) with hc1
  set c2 : ℝ := -(8 * t ^ 2 * (1 - θ) * a) with hc2
  set c3 : ℝ := 4 * t ^ 2 * (1 - θ) * a ^ 2 - (1 / θ - 1) * t ^ 4 * A ^ 4 with hc3
  have hpt2 : ∀ x, c1 * g x ^ 2 + c2 * g x + c3 ≤ ((1 + t * g x) ^ 2 - m) ^ 2 := by
    intro x
    set X := 2 * t * (g x - a) with hX
    set Y := t ^ 2 * (g x ^ 2 - b) with hY
    have hum : (1 + t * g x) ^ 2 - m = X + Y := by
      simp only [hX, hY, hmdef]; ring
    have hY2 : Y ^ 2 ≤ t ^ 4 * A ^ 4 := by
      have h1 : |g x ^ 2 - b| ≤ A ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (g x), hgsq x]
      have h2 : (g x ^ 2 - b) ^ 2 ≤ (A ^ 2) ^ 2 := by
        have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
        exact this
      calc Y ^ 2 = t ^ 4 * (g x ^ 2 - b) ^ 2 := by rw [hY]; ring
        _ ≤ t ^ 4 * (A ^ 2) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = t ^ 4 * A ^ 4 := by ring
    have hid : (X + Y) ^ 2 - ((1 - θ) * X ^ 2 - (1 / θ - 1) * Y ^ 2) = (θ * X + Y) ^ 2 / θ := by
      field_simp; ring
    have hnn : 0 ≤ (θ * X + Y) ^ 2 / θ := by positivity
    have hX2 : (1 - θ) * X ^ 2 = c1 * g x ^ 2 + c2 * g x + c3 + (1 / θ - 1) * t ^ 4 * A ^ 4 := by
      simp only [hX, hc1, hc2, hc3]; ring
    have h1θ : 0 ≤ 1 / θ - 1 := by
      rw [sub_nonneg, le_div_iff₀ hθ0]; linarith
    have : (1 / θ - 1) * Y ^ 2 ≤ (1 / θ - 1) * (t ^ 4 * A ^ 4) :=
      mul_le_mul_of_nonneg_left hY2 h1θ
    rw [hum]
    linarith
  have hL_int : Integrable (fun x => c1 * g x ^ 2 + c2 * g x + c3) P :=
    ((hint2.const_mul c1).add (hint.const_mul c2)).add (integrable_const c3)
  have hQlow : c1 * b + c2 * a + c3 ≤ ∫ x, ((1 + t * g x) ^ 2 - m) ^ 2 ∂P := by
    have hQi : Integrable (fun x => ((1 + t * g x) ^ 2 - m) ^ 2) P := by
      have := hG_int.const_mul (1 / c0)
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only; field_simp
    have := integral_mono hL_int hQi hpt2
    have j1 : Integrable (fun x => c1 * g x ^ 2) P := hint2.const_mul c1
    have j2 : Integrable (fun x => c2 * g x) P := hint.const_mul c2
    have j3 : Integrable (fun x => c1 * g x ^ 2 + c2 * g x) P := j1.add j2
    have j4 : Integrable (fun _ : α => c3) P := integrable_const c3
    rw [integral_add j3 j4, integral_add j1 j2, integral_const_mul,
      integral_const_mul] at this
    simpa [ha, hb] using this
  have hQ0 : 0 ≤ ∫ x, ((1 + t * g x) ^ 2 - m) ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have hV : b - a ^ 2 ≤ A ^ 2 := by nlinarith [sq_nonneg a]
  have hlowV : 4 * t ^ 2 * (b - a ^ 2) - 5 * t ^ 3 * A ^ 3 ≤ c1 * b + c2 * a + c3 := by
    have hθA : θ = t * A := rfl
    have e1 : c1 * b + c2 * a + c3 = 4 * t ^ 2 * (1 - θ) * (b - a ^ 2) -
        (1 / θ - 1) * t ^ 4 * A ^ 4 := by
      simp only [hc1, hc2, hc3]; ring
    have e2 : (1 / θ - 1) * t ^ 4 * A ^ 4 ≤ t ^ 3 * A ^ 3 := by
      have : (1 / θ - 1) * t ^ 4 * A ^ 4 = t ^ 3 * A ^ 3 - t ^ 4 * A ^ 4 := by
        rw [hθA]; field_simp
      rw [this]; nlinarith [pow_pos ht 4, pow_pos hA 4]
    have e3 : 4 * t ^ 2 * θ * (b - a ^ 2) ≤ 4 * t ^ 3 * A ^ 3 := by
      have : 4 * t ^ 2 * θ * (b - a ^ 2) ≤ 4 * t ^ 2 * θ * A ^ 2 :=
        mul_le_mul_of_nonneg_left hV (by positivity)
      calc _ ≤ _ := this
        _ = 4 * t ^ 3 * A ^ 3 := by rw [hθA]; ring
    rw [e1]; nlinarith
  rw [integral_const_mul]
  have hD0 : 0 < 2 * m * (1 + δ) / 2 := by positivity
  have hfin := ent_one_add_final (V := b - a ^ 2) (Q := ∫ x, ((1 + t * g x) ^ 2 - m) ^ 2 ∂P)
    (D := m * (1 + δ)) hA ht hτ hV hQ0 (hlowV.trans hQlow) (by positivity) (by
      rw [hδ]; nlinarith)
  calc 2 * t ^ 2 * (b - a ^ 2) - 25 * t ^ 3 * A ^ 3
      ≤ (∫ x, ((1 + t * g x) ^ 2 - m) ^ 2 ∂P) / (2 * (m * (1 + δ))) := hfin
    _ = c0 * ∫ x, ((1 + t * g x) ^ 2 - m) ^ 2 ∂P := by rw [hc0]; field_simp

end Ent

end SharpLSI.FL
