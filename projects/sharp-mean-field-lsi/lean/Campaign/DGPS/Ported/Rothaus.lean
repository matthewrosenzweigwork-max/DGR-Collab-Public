-- Ported-from: SharpSymmetricLSI.Paper.Rothaus @ d880f61501024eacf8cdb0c6a7de5c821c02d412
import SharpSymmetricLSI.Paper.TorusLSI
import SharpSymmetricLSI.Infra.Calculus
import SharpSymmetricLSI.Infra.Centering

/-!
# Rothaus' lemma (Phase 3, lane C; R43)

`Ent_P(f²) ≤ Ent_P((f - E f)²) + 2 Var_P(f)`, by a direct second-order Taylor argument
(route supplied by the integrator; not a transcription of Rothaus 1985 / BGL Lemma 5.1.4):
for bounded `g` and `ε > 0`, `ψ(t) = Ent((a+tg)² + ε)` has `ψ(0) = ψ'(0) = 0` and
`ψ'' ≤ 2 Ent(g²) + 4 E g²` (variational inequality, `(a+tg)² ≤ h_t`); then `ε → 0` and
truncation.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real

namespace DGPS.Ported.Rothaus

open SharpLSI (ent entR var ent_le_liminf ent_eq_ofReal_entR taylor2 ent_eq_formula)

variable {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]

/-- Ported from `SharpLSI.abs_sq_log_sq_le` (legacy `Paper/R7Positive`, not built). -/
theorem abs_sq_log_sq_le {m M : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M) (hM : 1 ≤ M) :
    |m ^ 2 * Real.log (m ^ 2)| ≤ 1 + M ^ 2 * Real.log (M ^ 2) := by
  have hM2 : 0 ≤ M ^ 2 * Real.log (M ^ 2) :=
    mul_nonneg (sq_nonneg _) (Real.log_nonneg (by nlinarith))
  rcases le_or_gt (m ^ 2) 1 with h | h
  · rcases (sq_nonneg m).eq_or_lt with h0 | h0
    · rw [← h0, zero_mul, abs_zero]; linarith
    · have := Real.abs_log_mul_self_lt (m ^ 2) h0 h
      rw [mul_comm] at this; linarith
  · have h1 : m ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hm hmM 2
    have hl : 0 ≤ Real.log (m ^ 2) := Real.log_nonneg h.le
    rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hl)]
    have := Real.log_le_log (by linarith) h1
    nlinarith

omit [IsProbabilityMeasure P] in
/-- Ported from `SharpLSI.ent_congr_ae` (legacy `Paper/R37Particle`, not built). -/
theorem ent_congr_ae {u v : α → ℝ} (huv : u =ᵐ[P] v) : ent P u = ent P v := by
  unfold ent
  have hi : Integrable u P ↔ Integrable v P := integrable_congr huv
  have hint : ∫ y, u y ∂P = ∫ y, v y ∂P := integral_congr_ae huv
  by_cases h : Integrable u P
  · simp only [h, hi.mp h, ↓reduceIte, hint]
    refine lintegral_congr_ae ?_
    filter_upwards [huv] with x hx
    rw [hx]
  · simp only [h, mt hi.mpr h, ↓reduceIte]

theorem bdd_integrable {G : α → ℝ} (hG : Measurable G) (D : ℝ) (hD : ∀ x, |G x| ≤ D) :
    Integrable G P :=
  Integrable.of_bound hG.aestronglyMeasurable D
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hD x)

theorem abs_log_le_of_mem {c C y : ℝ} (hc : 0 < c) (hy : c ≤ y) (hyC : y ≤ C) :
    |Real.log y| ≤ |Real.log c| + |Real.log C| := by
  have h1 := Real.log_le_log hc hy; have h2 := Real.log_le_log (lt_of_lt_of_le hc hy) hyC
  rw [abs_le]; constructor
  · have := neg_abs_le (Real.log c); have := abs_nonneg (Real.log C); linarith
  · have := le_abs_self (Real.log C); have := abs_nonneg (Real.log c); linarith

theorem integrable_sq_log_sq {g : α → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) P :=
  bdd_integrable (P := P) ((hg.pow_const 2).mul (Real.measurable_log.comp (hg.pow_const 2)))
    (1 + max B 1 ^ 2 * Real.log (max B 1 ^ 2)) fun x => by
      have := abs_sq_log_sq_le (abs_nonneg (g x)) ((hB x).trans (le_max_left _ _)) (le_max_right _ _)
      rwa [sq_abs] at this

/-- Step 0: `E[g² log h] - E[g²] log E[h] ≤ Ent(g²)` for bounded `g`, `c ≤ h ≤ C`. -/
theorem integral_sq_mul_log_le {g h : α → ℝ} (hg : Measurable g) (hhm : Measurable h)
    {B c C : ℝ} (hc : 0 < c) (hB : ∀ x, |g x| ≤ B) (hhc : ∀ x, c ≤ h x) (hhC : ∀ x, h x ≤ C) :
    ∫ x, g x ^ 2 * Real.log (h x) ∂P - (∫ x, g x ^ 2 ∂P) * Real.log (∫ x, h x ∂P) ≤
      entR P (fun x => g x ^ 2) := by
  have hh0 : ∀ x, 0 < h x := fun x => lt_of_lt_of_le hc (hhc x)
  have hg2 : Integrable (fun x => g x ^ 2) P := bdd_integrable (hg.pow_const 2) (B ^ 2) fun x => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  have hhi : Integrable h P := bdd_integrable hhm (|C|) fun x => by
    rw [abs_of_pos (hh0 x)]; exact (hhC x).trans (le_abs_self C)
  have hglogh : Integrable (fun x => g x ^ 2 * Real.log (h x)) P :=
    bdd_integrable ((hg.pow_const 2).mul (Real.measurable_log.comp hhm))
      (B ^ 2 * (|Real.log c| + |Real.log C|)) fun x => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2)
          (abs_log_le_of_mem hc (hhc x) (hhC x)) (abs_nonneg _) (sq_nonneg _)
  have hglogg := integrable_sq_log_sq (P := P) hg hB
  set m := ∫ x, g x ^ 2 ∂P with hm
  set E := ∫ x, h x ∂P with hE
  have hE0 : 0 < E := by
    have : c ≤ E := by
      calc c = ∫ _x, c ∂P := by simp
        _ ≤ E := integral_mono (integrable_const c) hhi hhc
    linarith
  have hm0 : 0 ≤ m := integral_nonneg fun x => sq_nonneg _
  unfold entR
  rcases hm0.eq_or_lt with h0 | hmpos
  · -- `g = 0` a.e.
    have hz : (fun x => g x ^ 2) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hg2).mp h0.symm
    have e1 : ∫ x, g x ^ 2 * Real.log (h x) ∂P = 0 := by
      rw [integral_congr_ae (hz.mono fun x hx => by simp only [Pi.zero_apply] at hx ⊢; rw [hx, zero_mul])]
      simp
    have e2 : ∫ x, g x ^ 2 * Real.log (g x ^ 2) ∂P = 0 := by
      rw [integral_congr_ae (hz.mono fun x hx => by simp only [Pi.zero_apply] at hx ⊢; rw [hx, zero_mul])]
      simp
    rw [e1, e2, ← hm, ← h0]; simp
  have hpt : ∀ x, g x ^ 2 * Real.log (h x) - g x ^ 2 * Real.log E + g x ^ 2 * Real.log m -
      g x ^ 2 * Real.log (g x ^ 2) ≤ m * h x / E - g x ^ 2 := fun x => by
    rcases (sq_nonneg (g x)).eq_or_lt with hz | hp
    · rw [← hz]; simp only [zero_mul, sub_zero, add_zero, Real.log_zero, mul_zero]
      exact div_nonneg (mul_nonneg hm0 (hh0 x).le) hE0.le
    · have hr : 0 < m * h x / (E * g x ^ 2) := by have := hh0 x; positivity
      have hl := Real.log_le_sub_one_of_pos hr
      rw [Real.log_div (by have := hh0 x; positivity) (by positivity),
        Real.log_mul hmpos.ne' (hh0 x).ne', Real.log_mul hE0.ne' hp.ne'] at hl
      have := mul_le_mul_of_nonneg_left hl hp.le
      have hgx : g x ≠ 0 := fun h0 => by rw [h0] at hp; simp at hp
      have e : g x ^ 2 * (m * h x / (E * g x ^ 2) - 1) = m * h x / E - g x ^ 2 := by
        field_simp
      nlinarith
  have i1 : Integrable (fun x => g x ^ 2 * Real.log (h x) - g x ^ 2 * Real.log E +
      g x ^ 2 * Real.log m - g x ^ 2 * Real.log (g x ^ 2)) P :=
    ((hglogh.sub (hg2.mul_const _)).add (hg2.mul_const _)).sub hglogg
  have i2 : Integrable (fun x => m * h x / E - g x ^ 2) P := ((hhi.const_mul m).div_const E).sub hg2
  have hint := integral_mono i1 i2 hpt
  have ia : Integrable (fun x => g x ^ 2 * Real.log (h x) - g x ^ 2 * Real.log E) P :=
    hglogh.sub (hg2.mul_const _)
  have ib : Integrable (fun x => g x ^ 2 * Real.log (h x) - g x ^ 2 * Real.log E +
      g x ^ 2 * Real.log m) P := ia.add (hg2.mul_const _)
  rw [integral_sub (f := fun x => g x ^ 2 * Real.log (h x) - g x ^ 2 * Real.log E +
      g x ^ 2 * Real.log m) (g := fun x => g x ^ 2 * Real.log (g x ^ 2)) ib hglogg,
    integral_add (f := fun x => g x ^ 2 * Real.log (h x) - g x ^ 2 * Real.log E)
      (g := fun x => g x ^ 2 * Real.log m) ia (hg2.mul_const _),
    integral_sub (f := fun x => g x ^ 2 * Real.log (h x)) (g := fun x => g x ^ 2 * Real.log E)
      hglogh (hg2.mul_const _),
    integral_sub (f := fun x => m * h x / E) (g := fun x => g x ^ 2) ((hhi.const_mul m).div_const E) hg2,
    integral_div, integral_const_mul, integral_mul_const, integral_mul_const] at hint
  have e : m * E / E = m := by field_simp
  rw [e] at hint
  linarith

theorem hasDerivAt_integral_bdd {F F' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hFm : ∀ x, Measurable (F x)) (hF'm : ∀ x, Measurable (F' x)) {L0 L1 : ℝ}
    (hF : ∀ x ∈ s, ∀ ω, |F x ω| ≤ L0) (hF' : ∀ x ∈ s, ∀ ω, |F' x ω| ≤ L1)
    (hd : ∀ ω, ∀ x ∈ s, HasDerivAt (F · ω) (F' x ω) x) :
    HasDerivAt (fun x => ∫ ω, F x ω ∂P) (∫ ω, F' t ω ∂P) t :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall fun x => (hFm x).aestronglyMeasurable)
    (bdd_integrable (hFm t) L0 (hF t (mem_of_mem_nhds hs)))
    (hF'm t).aestronglyMeasurable
    (Eventually.of_forall fun ω x hx => by rw [Real.norm_eq_abs]; exact hF' x hx ω)
    (integrable_const L1) (Eventually.of_forall hd)).2

/-- Step 1: the smoothed inequality for bounded `g`. -/
theorem rothaus_bdd_eps {g : α → ℝ} (hg : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) (a : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    entR P (fun ω => (a + g ω) ^ 2 + ε) ≤ entR P (fun ω => g ω ^ 2) + 2 * ∫ ω, g ω ^ 2 ∂P := by
  set A := |a| + 2 * B with hA
  set C := A ^ 2 + ε with hC
  set s : Set ℝ := Ioo (-1) 2 with hs
  have hB0 : ∀ ω, 0 ≤ B := fun ω => (abs_nonneg _).trans (hB ω)
  set h : ℝ → α → ℝ := fun x ω => (a + x * g ω) ^ 2 + ε with hh
  have hAx : ∀ x ∈ s, ∀ ω, |a + x * g ω| ≤ A := fun x hx ω => by
    have hx2 : |x| ≤ 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    calc |a + x * g ω| ≤ |a| + |x| * |g ω| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |a| + 2 * B := by
        linarith [mul_le_mul hx2 (hB ω) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
  have hhε : ∀ x ω, ε ≤ h x ω := fun x ω => by simp only [hh]; nlinarith [sq_nonneg (a + x * g ω)]
  have hhC : ∀ x ∈ s, ∀ ω, h x ω ≤ C := fun x hx ω => by
    simp only [hh, hC]
    have := hAx x hx ω
    nlinarith [sq_abs (a + x * g ω), abs_nonneg (a + x * g ω)]
  have hh0 : ∀ x ω, 0 < h x ω := fun x ω => lt_of_lt_of_le hε (hhε x ω)
  have hlog : ∀ x ∈ s, ∀ ω, |Real.log (h x ω)| ≤ |Real.log ε| + |Real.log C| := fun x hx ω =>
    abs_log_le_of_mem hε (hhε x ω) (hhC x hx ω)
  set Λ := |Real.log ε| + |Real.log C|
  have hΛ : 0 ≤ Λ := by positivity
  have hm : ∀ x, Measurable (h x) := fun x =>
    ((measurable_const.add (measurable_const.mul hg)).pow_const 2).add measurable_const
  -- the integrands and their derivatives
  set F0 : ℝ → α → ℝ := fun x ω => h x ω * Real.log (h x ω)
  set F1 : ℝ → α → ℝ := fun x ω => 2 * g ω * (a + x * g ω) * (Real.log (h x ω) + 1)
  set F2 : ℝ → α → ℝ := fun x ω =>
    2 * g ω ^ 2 * (Real.log (h x ω) + 1) + (2 * g ω * (a + x * g ω)) ^ 2 / h x ω
  set G1 : ℝ → α → ℝ := fun x ω => 2 * g ω * (a + x * g ω)
  have dh : ∀ ω x, HasDerivAt (fun x => h x ω) (G1 x ω) x := fun ω x => by
    have := ((((hasDerivAt_id' x).mul_const (g ω)).const_add a).pow 2).add_const ε
    convert this using 1; simp [G1]; ring
  have dG1 : ∀ ω x, HasDerivAt (fun x => G1 x ω) (2 * g ω ^ 2) x := fun ω x => by
    have := (((hasDerivAt_id' x).mul_const (g ω)).const_add a).const_mul (2 * g ω)
    convert this using 1; ring
  have dF0 : ∀ ω, ∀ x ∈ s, HasDerivAt (F0 · ω) (F1 x ω) x := fun ω x _ => by
    have := (dh ω x).mul ((dh ω x).log (hh0 x ω).ne')
    convert this using 1
    simp only [F1, G1]; field_simp [(hh0 x ω).ne']
  have dF1 : ∀ ω, ∀ x ∈ s, HasDerivAt (F1 · ω) (F2 x ω) x := fun ω x _ => by
    have := (dG1 ω x).mul (((dh ω x).log (hh0 x ω).ne').add_const 1)
    convert this using 1
    simp only [F2, G1]; field_simp [(hh0 x ω).ne']
  have dM0 : ∀ ω, ∀ x ∈ s, HasDerivAt (h · ω) (G1 x ω) x := fun ω x _ => dh ω x
  have dM1 : ∀ ω, ∀ x ∈ s, HasDerivAt (G1 · ω) (2 * g ω ^ 2) x := fun ω x _ => dG1 ω x
  -- measurability and bounds
  have mG1 : ∀ x, Measurable (G1 x) := fun x =>
    (measurable_const.mul hg).mul (measurable_const.add (measurable_const.mul hg))
  have mF0 : ∀ x, Measurable (F0 x) := fun x => (hm x).mul (Real.measurable_log.comp (hm x))
  have mF1 : ∀ x, Measurable (F1 x) := fun x =>
    (mG1 x).mul ((Real.measurable_log.comp (hm x)).add measurable_const)
  have mF2 : ∀ x, Measurable (F2 x) := fun x =>
    ((measurable_const.mul (hg.pow_const 2)).mul ((Real.measurable_log.comp (hm x)).add
      measurable_const)).add (((mG1 x).pow_const 2).div (hm x))
  have bG1 : ∀ x ∈ s, ∀ ω, |G1 x ω| ≤ 2 * B * A := fun x hx ω => by
    simp only [G1, abs_mul, abs_two]
    have := hAx x hx ω
    have := hB ω
    nlinarith [abs_nonneg (g ω), abs_nonneg (a + x * g ω)]
  have bh : ∀ x ∈ s, ∀ ω, |h x ω| ≤ C := fun x hx ω => by
    rw [abs_of_pos (hh0 x ω)]; exact hhC x hx ω
  have bF0 : ∀ x ∈ s, ∀ ω, |F0 x ω| ≤ C * Λ := fun x hx ω => by
    simp only [F0, abs_mul]
    exact mul_le_mul (bh x hx ω) (hlog x hx ω) (abs_nonneg _) (by have := hhε x ω; positivity)
  have bF1 : ∀ x ∈ s, ∀ ω, |F1 x ω| ≤ 2 * B * A * (Λ + 1) := fun x hx ω => by
    have h1 : |F1 x ω| = |G1 x ω| * |Real.log (h x ω) + 1| := by simp only [F1, G1, abs_mul]
    rw [h1]
    exact mul_le_mul (bG1 x hx ω) ((abs_add_le _ _).trans (by rw [abs_one]; linarith [hlog x hx ω]))
      (abs_nonneg _) (by have := hB0 ω; positivity)
  have bF2 : ∀ x ∈ s, ∀ ω, |F2 x ω| ≤ 2 * B ^ 2 * (Λ + 1) + (2 * B * A) ^ 2 / ε := fun x hx ω => by
    simp only [F2]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (sq_nonneg _)]
      have hg2 : g ω ^ 2 ≤ B ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB ω) 2
      have hl : |Real.log (h x ω) + 1| ≤ Λ + 1 :=
        (abs_add_le _ _).trans (by rw [abs_one]; linarith [hlog x hx ω])
      have := hB0 ω
      calc 2 * g ω ^ 2 * |Real.log (h x ω) + 1| ≤ 2 * B ^ 2 * (Λ + 1) := by gcongr
        _ = _ := rfl
    · rw [abs_div, abs_of_pos (hh0 x ω), abs_of_nonneg (sq_nonneg _)]
      have h1 : G1 x ω ^ 2 ≤ (2 * B * A) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (bG1 x hx ω) 2
      calc (2 * g ω * (a + x * g ω)) ^ 2 / h x ω ≤ (2 * B * A) ^ 2 / h x ω :=
            div_le_div_of_nonneg_right h1 (hh0 x ω).le
        _ ≤ (2 * B * A) ^ 2 / ε := div_le_div_of_nonneg_left (sq_nonneg _) hε (hhε x ω)
  have bG2 : ∀ x ∈ s, ∀ ω, |2 * g ω ^ 2| ≤ 2 * B ^ 2 := fun x _ ω => by
    rw [abs_mul, abs_two, abs_of_nonneg (sq_nonneg _)]
    have := pow_le_pow_left₀ (abs_nonneg _) (hB ω) 2
    rw [sq_abs] at this; linarith
  have hsn : ∀ x ∈ s, s ∈ 𝓝 x := fun x hx => isOpen_Ioo.mem_nhds hx
  have m2 : Measurable (fun ω => 2 * g ω ^ 2) := measurable_const.mul (hg.pow_const 2)
  have dΦ : ∀ x ∈ s, HasDerivAt (fun x => ∫ ω, F0 x ω ∂P) (∫ ω, F1 x ω ∂P) x := fun x hx =>
    hasDerivAt_integral_bdd (hsn x hx) mF0 mF1 bF0 bF1 dF0
  have dD1 : ∀ x ∈ s, HasDerivAt (fun x => ∫ ω, F1 x ω ∂P) (∫ ω, F2 x ω ∂P) x := fun x hx =>
    hasDerivAt_integral_bdd (hsn x hx) mF1 mF2 bF1 bF2 dF1
  have dM : ∀ x ∈ s, HasDerivAt (fun x => ∫ ω, h x ω ∂P) (∫ ω, G1 x ω ∂P) x := fun x hx =>
    hasDerivAt_integral_bdd (hsn x hx) hm mG1 bh bG1 dM0
  have dM1 : ∀ x ∈ s, HasDerivAt (fun x => ∫ ω, G1 x ω ∂P) (∫ ω, 2 * g ω ^ 2 ∂P) x :=
    fun x hx => hasDerivAt_integral_bdd (F' := fun _ ω => 2 * g ω ^ 2) (hsn x hx) mG1
      (fun _ => m2) bG1 bG2 dM1
  have hMpos : ∀ x ∈ s, 0 < ∫ ω, h x ω ∂P := fun x hx => by
    have : ∫ _ : α, ε ∂P ≤ ∫ ω, h x ω ∂P :=
      integral_mono (integrable_const ε) (bdd_integrable (hm x) C (bh x hx)) (hhε x)
    simp at this; linarith
  set M := fun x => ∫ ω, h x ω ∂P
  set M1 := fun x => ∫ ω, G1 x ω ∂P
  set M2 := ∫ ω, 2 * g ω ^ 2 ∂P
  set ψ : ℝ → ℝ := fun x => (∫ ω, F0 x ω ∂P) - M x * Real.log (M x) with hψ
  set ψ' : ℝ → ℝ := fun x => (∫ ω, F1 x ω ∂P) - M1 x * (Real.log (M x) + 1) with hψ'
  set ψ'' : ℝ → ℝ := fun x =>
    (∫ ω, F2 x ω ∂P) - (M2 * (Real.log (M x) + 1) + M1 x * (M1 x / M x)) with hψ''
  have dψ : ∀ x ∈ s, HasDerivAt ψ (ψ' x) x := fun x hx => by
    have := (dΦ x hx).sub ((dM x hx).mul ((dM x hx).log (hMpos x hx).ne'))
    convert this using 1
    simp only [ψ', M, M1]; field_simp [(hMpos x hx).ne']
  have dψ' : ∀ x ∈ s, HasDerivAt ψ' (ψ'' x) x := fun x hx => by
    have := (dD1 x hx).sub ((dM1 x hx).mul (((dM x hx).log (hMpos x hx).ne').add_const 1))
    convert this using 1
  -- the second-derivative bound
  set Ig := ∫ ω, g ω ^ 2 ∂P
  have hg2b : ∀ ω, |g ω ^ 2| ≤ B ^ 2 := fun ω => by
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB ω) 2
  have hψ''le : ∀ x ∈ s, ψ'' x ≤ 2 * entR P (fun ω => g ω ^ 2) + 4 * Ig := fun x hx => by
    have iL : Integrable (fun ω => g ω ^ 2 * Real.log (h x ω)) P :=
      bdd_integrable ((hg.pow_const 2).mul (Real.measurable_log.comp (hm x))) (B ^ 2 * Λ)
        fun ω => by
          rw [abs_mul]
          exact mul_le_mul (hg2b ω) (hlog x hx ω) (abs_nonneg _) (by have := hB0 ω; positivity)
    have iG : Integrable (fun ω => g ω ^ 2) P := bdd_integrable (hg.pow_const 2) _ hg2b
    have hpt : ∀ ω, F2 x ω ≤ 2 * (g ω ^ 2 * Real.log (h x ω)) + 6 * g ω ^ 2 := fun ω => by
      simp only [F2]
      have h1 : (2 * g ω * (a + x * g ω)) ^ 2 / h x ω ≤ 4 * g ω ^ 2 := by
        rw [div_le_iff₀ (hh0 x ω)]
        simp only [hh]
        nlinarith [sq_nonneg (g ω), sq_nonneg (a + x * g ω), mul_nonneg (sq_nonneg (g ω)) hε.le]
      nlinarith
    have hF2 : ∫ ω, F2 x ω ∂P ≤ 2 * (∫ ω, g ω ^ 2 * Real.log (h x ω) ∂P) + 6 * Ig := by
      calc ∫ ω, F2 x ω ∂P ≤ ∫ ω, (2 * (g ω ^ 2 * Real.log (h x ω)) + 6 * g ω ^ 2) ∂P :=
            integral_mono (bdd_integrable (mF2 x) _ (bF2 x hx)) ((iL.const_mul 2).add
              (iG.const_mul 6)) hpt
        _ = _ := by
          rw [integral_add (iL.const_mul 2) (iG.const_mul 6), integral_const_mul,
            integral_const_mul]
    have hM2 : M2 = 2 * Ig := integral_const_mul _ _
    have h0 := integral_sq_mul_log_le (P := P) hg (hm x) hε hB (hhε x) (fun ω => hhC x hx ω)
    have h3 : 0 ≤ M1 x * (M1 x / M x) := by
      rw [← mul_div_assoc]; exact div_nonneg (mul_self_nonneg _) (hMpos x hx).le
    simp only [ψ'', hM2]
    have : M x = ∫ ω, h x ω ∂P := rfl
    rw [this] at h3 ⊢
    nlinarith
  have hI : ∀ y ∈ uIcc (0 : ℝ) 1, y ∈ s := fun y hy => by
    rw [uIcc_of_le zero_le_one] at hy; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have key := taylor2 (f := ψ) (f' := ψ') (f'' := ψ'') (x₀ := 0) (x := 1)
    (fun y hy => dψ y (hI y hy)) (fun y hy => dψ' y (hI y hy)) (fun y hy => hψ''le y (hI y hy))
  have e0 : ∀ ω, h 0 ω = a ^ 2 + ε := fun ω => by simp [hh]
  have hM0 : M 0 = a ^ 2 + ε := by simp [M, e0]
  have hψ0 : ψ 0 = 0 := by simp [ψ, hM0, F0, e0]
  have hψ'0 : ψ' 0 = 0 := by
    have : ∀ ω, F1 0 ω = G1 0 ω * (Real.log (a ^ 2 + ε) + 1) := fun ω => by
      simp only [F1, G1, e0]
    simp only [ψ', hM0, this, integral_mul_const, M1, sub_self]
  have e1 : h 1 = fun ω => (a + g ω) ^ 2 + ε := by funext ω; simp [hh]
  have hψ1 : ψ 1 = entR P (fun ω => (a + g ω) ^ 2 + ε) := by
    rw [← e1]; rfl
  rw [hψ0, hψ'0, hψ1] at key
  linarith

theorem klFun_le_sq₀ {x : ℝ} (hx : 0 ≤ x) : klFun x ≤ (x - 1) ^ 2 := by
  rw [klFun_apply]
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · have := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h) hx
    nlinarith

theorem monotoneOn_klFun : MonotoneOn klFun (Ici 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 1) continuous_klFun.continuousOn ?_ ?_
  · intro x hx
    rw [interior_Ici] at hx
    exact (hasDerivAt_klFun (by linarith [mem_Ioi.mp hx])).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [deriv_klFun]; exact Real.log_nonneg (le_of_lt hx)

theorem klFun_shift {m k y : ℝ} (hm : 0 < m) (hk : 0 < k) (hy : 0 ≤ y) :
    m * klFun (y / m) = k * klFun (y / k) + (y * Real.log (k / m) + m - k) := by
  simp only [klFun_apply]
  rcases hy.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_div h.ne' hm.ne', Real.log_div h.ne' hk.ne', Real.log_div hk.ne' hm.ne']
    field_simp
    ring

theorem integrable_mul_klFun {F : α → ℝ} (hF : Measurable F) {m K : ℝ} (hm : 0 < m)
    (hF0 : ∀ x, 0 ≤ F x) (hFK : ∀ x, F x ≤ K) :
    Integrable (fun x => m * klFun (F x / m)) P := by
  refine bdd_integrable (measurable_const.mul (measurable_klFun.comp (hF.div_const m)))
    (m * (K / m + 1) ^ 2) fun x => ?_
  have h0 : 0 ≤ F x / m := div_nonneg (hF0 x) hm.le
  have h1 : F x / m ≤ K / m := div_le_div_of_nonneg_right (hFK x) hm.le
  rw [abs_of_nonneg (mul_nonneg hm.le (klFun_nonneg h0))]
  refine mul_le_mul_of_nonneg_left ((klFun_le_sq₀ h0).trans ?_) hm.le
  have hK : 0 ≤ K / m := h0.trans h1
  nlinarith

/-- Truncating from above at a level `≥ E F` does not increase the entropy. -/
theorem ent_min_le {F : α → ℝ} (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x) (hFi : Integrable F P)
    {K : ℝ} (hK : ∫ x, F x ∂P ≤ K) : ent P (fun x => min (F x) K) ≤ ent P F := by
  set m := ∫ x, F x ∂P with hm
  have hm0 : 0 ≤ m := integral_nonneg hF0
  have hK0 : 0 ≤ K := hm0.trans hK
  set Fk : α → ℝ := fun x => min (F x) K with hFk
  have hFkm : Measurable Fk := hF.min measurable_const
  have hFk0 : ∀ x, 0 ≤ Fk x := fun x => le_min (hF0 x) hK0
  have hFkK : ∀ x, Fk x ≤ K := fun x => min_le_right _ _
  have hFki : Integrable Fk P := bdd_integrable hFkm K fun x => by
    rw [abs_of_nonneg (hFk0 x)]; exact hFkK x
  set mk := ∫ x, Fk x ∂P with hmk
  have hmk0 : 0 ≤ mk := integral_nonneg hFk0
  have hmkm : mk ≤ m := integral_mono hFki hFi fun x => min_le_left _ _
  unfold ent
  simp only [hFki, hFi, ↓reduceIte]
  rw [← hm, ← hmk]
  rcases hmk0.eq_or_lt with h | hmkp
  · rw [← h]; simp
  have hmp : 0 < m := hmkp.trans_le hmkm
  have i1 := integrable_mul_klFun (P := P) hFkm hmkp hFk0 hFkK
  have i2 := integrable_mul_klFun (P := P) hFkm hmp hFk0 hFkK
  have nn : ∀ {c : ℝ}, 0 < c → 0 ≤ᵐ[P] fun x => c * klFun (Fk x / c) := fun hc =>
    Eventually.of_forall fun x => mul_nonneg hc.le (klFun_nonneg (div_nonneg (hFk0 x) hc.le))
  rw [← ofReal_integral_eq_lintegral_ofReal i1 (nn hmkp)]
  calc ENNReal.ofReal (∫ x, mk * klFun (Fk x / mk) ∂P)
      ≤ ENNReal.ofReal (∫ x, m * klFun (Fk x / m) ∂P) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have iB : Integrable (fun x => Fk x * Real.log (mk / m) + m - mk) P :=
          ((hFki.mul_const _).add (integrable_const m)).sub (integrable_const mk)
        have e : ∫ x, m * klFun (Fk x / m) ∂P =
            (∫ x, mk * klFun (Fk x / mk) ∂P) + ∫ x, (Fk x * Real.log (mk / m) + m - mk) ∂P := by
          rw [← integral_add i1 iB]
          exact integral_congr_ae (Eventually.of_forall fun x => klFun_shift hmp hmkp (hFk0 x))
        have eB : ∫ x, (Fk x * Real.log (mk / m) + m - mk) ∂P = m * klFun (mk / m) := by
          rw [integral_sub (f := fun x => Fk x * Real.log (mk / m) + m)
            ((hFki.mul_const _).add (integrable_const m)) (integrable_const mk),
            integral_add (f := fun x => Fk x * Real.log (mk / m)) (hFki.mul_const _)
              (integrable_const m), integral_mul_const,
            klFun_shift hmp hmkp hmk0, div_self hmkp.ne', klFun_one]
          simp [← hmk]
        rw [e, eB]
        linarith [mul_nonneg hmp.le (klFun_nonneg (div_nonneg hmk0 hmp.le))]
    _ = ∫⁻ x, ENNReal.ofReal (m * klFun (Fk x / m)) ∂P :=
        ofReal_integral_eq_lintegral_ofReal i2 (nn hmp)
    _ ≤ ∫⁻ x, ENNReal.ofReal (m * klFun (F x / m)) ∂P := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left ?_ hmp.le)
        by_cases hx : F x ≤ K
        · simp only [Fk, min_eq_left hx, le_refl]
        · rw [not_le] at hx
          simp only [Fk, min_eq_right hx.le]
          have h1 : 1 ≤ K / m := (one_le_div hmp).mpr hK
          exact monotoneOn_klFun h1 (h1.trans (div_le_div_of_nonneg_right hx.le hmp.le))
            (div_le_div_of_nonneg_right hx.le hmp.le)

theorem abs_mul_log_le_of_nonneg {y : ℝ} (hy : 0 ≤ y) : |y * Real.log y| ≤ (y - 1) ^ 2 + 1 + y := by
  have e : y * Real.log y = klFun y - 1 + y := by rw [klFun_apply]; ring
  rw [e, abs_le]
  have := klFun_nonneg hy
  have := klFun_le_sq₀ hy
  constructor <;> nlinarith

theorem sq_trunc {g T : ℝ} (hT : 0 ≤ T) : max (-T) (min g T) ^ 2 = min (g ^ 2) (T ^ 2) := by
  rcases le_total g T with h1 | h1
  · rw [min_eq_left h1]
    rcases le_total (-T) g with h2 | h2
    · rw [max_eq_right h2, min_eq_left (sq_le_sq' h2 h1)]
    · rw [max_eq_left h2, min_eq_right (by nlinarith)]; ring
  · rw [min_eq_right h1, max_eq_right (by linarith), min_eq_right (by nlinarith)]

/-- Rothaus' lemma for measurable `f`. -/
theorem rothaus_meas {f : α → ℝ} (hfm : Measurable f) (hf : MemLp f 2 P) :
    ent P (fun x => f x ^ 2) ≤ ent P (fun x => (f x - ∫ y, f y ∂P) ^ 2) + 2 * var P f := by
  set a := ∫ y, f y ∂P with ha
  set g : α → ℝ := fun x => f x - a with hg
  have hgm : Measurable g := hfm.sub measurable_const
  have hf2 : Integrable (fun x => f x ^ 2) P := hf.integrable_sq
  have hg2 : Integrable (fun x => g x ^ 2) P := (hf.sub (memLp_const a)).integrable_sq
  set V := ∫ x, g x ^ 2 ∂P with hV
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  have hvar : var P f = ENNReal.ofReal V := by
    rw [hV, ofReal_integral_eq_lintegral_ofReal hg2 (Eventually.of_forall fun x => sq_nonneg _)]
    unfold var ProbabilityTheory.evariance
    congr 1; funext X
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  set T : ℕ → ℝ := fun n => (n : ℝ) + 1 + V with hT
  have hT0 : ∀ n, 0 ≤ T n := fun n => by simp only [hT]; positivity
  set gt : ℕ → α → ℝ := fun n x => max (-(T n)) (min (g x) (T n)) with hgt
  have gtm : ∀ n, Measurable (gt n) := fun n => measurable_const.max (hgm.min measurable_const)
  have gtB : ∀ n x, |gt n x| ≤ T n := fun n x => abs_le.mpr
    ⟨le_max_left _ _, max_le (by linarith [hT0 n]) (min_le_right _ _)⟩
  have gtsq : ∀ n x, gt n x ^ 2 = min (g x ^ 2) (T n ^ 2) := fun n x => sq_trunc (hT0 n)
  have gtle : ∀ n x, gt n x ^ 2 ≤ g x ^ 2 := fun n x => by rw [gtsq]; exact min_le_left _ _
  have gtsqB : ∀ n x, |gt n x ^ 2| ≤ T n ^ 2 := fun n x => by
    rw [abs_of_nonneg (sq_nonneg _), gtsq]; exact min_le_right _ _
  have gt2i : ∀ n, Integrable (fun x => gt n x ^ 2) P := fun n =>
    bdd_integrable ((gtm n).pow_const 2) _ (gtsqB n)
  set u : ℕ → α → ℝ := fun n x => (a + gt n x) ^ 2 + 1 / ((n : ℝ) + 1) with hu
  have um : ∀ n, Measurable (u n) := fun n =>
    ((measurable_const.add (gtm n)).pow_const 2).add measurable_const
  have uB : ∀ n x, (a + gt n x) ^ 2 ≤ (|a| + T n) ^ 2 := fun n x => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans (by linarith [gtB n x])) 2
  have hεn : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have ui : ∀ n, Integrable (u n) P := fun n =>
    bdd_integrable (um n) ((|a| + T n) ^ 2 + 1 / ((n : ℝ) + 1)) fun x => by
      rw [abs_of_nonneg (by have := hεn n; positivity)]
      simp only [hu]; linarith [uB n x]
  -- the per-`n` bound
  have hbd : ∀ n, ent P (u n) ≤ ent P (fun x => g x ^ 2) + 2 * var P f := fun n => by
    have h1 := rothaus_bdd_eps (P := P) (gtm n) (gtB n) a (hεn n)
    have e1 : ent P (u n) = ENNReal.ofReal (entR P (u n)) :=
      ent_eq_ofReal_entR (C := (|a| + T n) ^ 2 + 1 / ((n : ℝ) + 1)) (um n) (hεn n) (fun x => by simp only [hu]; nlinarith [sq_nonneg (a + gt n x)])
        (fun x => by simp only [hu]; linarith [uB n x])
    have e2 : ent P (fun x => gt n x ^ 2) = ENNReal.ofReal (entR P (fun x => gt n x ^ 2)) :=
      ent_eq_formula P _ (fun x => sq_nonneg _) (gt2i n)
        (bdd_integrable (((gtm n).pow_const 2).mul (Real.measurable_log.comp ((gtm n).pow_const 2)))
          ((T n ^ 2 + 1) ^ 2 + 1 + T n ^ 2) fun x => by
            refine (abs_mul_log_le_of_nonneg (sq_nonneg _)).trans ?_
            have h0 := sq_nonneg (gt n x)
            have h2 : gt n x ^ 2 ≤ T n ^ 2 := le_of_abs_le (gtsqB n x)
            nlinarith [mul_nonneg h0 (sub_nonneg.2 h2), sq_nonneg (T n)])
    have e3 : ent P (fun x => gt n x ^ 2) ≤ ent P (fun x => g x ^ 2) := by
      have : (fun x => gt n x ^ 2) = fun x => min (g x ^ 2) (T n ^ 2) := funext (gtsq n)
      rw [this]
      refine ent_min_le (hgm.pow_const 2) (fun x => sq_nonneg _) hg2 ?_
      simp only [hT]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have e4 : ∫ x, gt n x ^ 2 ∂P ≤ V := integral_mono (gt2i n) hg2 (gtle n)
    have hu1 : u n = fun x => (a + gt n x) ^ 2 + 1 / ((n : ℝ) + 1) := rfl
    rw [e1, hvar]
    calc ENNReal.ofReal (entR P (u n))
        ≤ ENNReal.ofReal (entR P (fun x => gt n x ^ 2) + 2 * ∫ x, gt n x ^ 2 ∂P) :=
          ENNReal.ofReal_le_ofReal (by rw [hu1]; exact h1)
      _ ≤ ENNReal.ofReal (entR P (fun x => gt n x ^ 2)) + ENNReal.ofReal (2 * V) :=
          ENNReal.ofReal_add_le.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (by linarith)))
      _ ≤ ent P (fun x => g x ^ 2) + 2 * ENNReal.ofReal V := by
          rw [← e2, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          exact add_le_add e3 le_rfl
  -- pointwise and integral convergence
  have hpt : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x ^ 2)) := fun x => by
    have hev : (fun n : ℕ => (a + g x) ^ 2 + 1 / ((n : ℝ) + 1)) =ᶠ[atTop] fun n => u n x := by
      filter_upwards [eventually_ge_atTop ⌈|g x|⌉₊] with n hn
      have hgn : |g x| ≤ T n := by
        have := Nat.le_of_ceil_le hn; simp only [hT]; linarith
      have : gt n x = g x := by
        simp only [hgt]
        rw [min_eq_left (le_of_abs_le hgn), max_eq_right (neg_le_of_abs_le hgn)]
      simp only [hu, this]
    have : f x ^ 2 = (a + g x) ^ 2 + 0 := by simp [hg]
    rw [this]
    exact (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).congr' hev
  have hint : Tendsto (fun n => ∫ x, u n x ∂P) atTop (𝓝 (∫ x, f x ^ 2 ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => 2 * a ^ 2 + 2 * g x ^ 2 + 1)
      (fun n => (um n).aestronglyMeasurable) (((integrable_const _).add (hg2.const_mul 2)).add
        (integrable_const 1)) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall hpt)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := hεn n; positivity)]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [hu]
    nlinarith [sq_nonneg (a - gt n x), gtle n x]
  calc ent P (fun x => f x ^ 2) ≤ liminf (fun n => ent P (u n)) atTop :=
        ent_le_liminf ui hf2 (Eventually.of_forall hpt) hint
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.frequently (Eventually.of_forall hbd))

/-- **Rothaus' lemma**: `Ent(f²) ≤ Ent((f - E f)²) + 2 Var(f)` for `f ∈ L²`. -/
theorem rothaus {f : α → ℝ} (hf : MemLp f 2 P) :
    ent P (fun x => f x ^ 2) ≤ ent P (fun x => (f x - ∫ y, f y ∂P) ^ 2) + 2 * var P f := by
  have hm := hf.aestronglyMeasurable.aemeasurable
  set f' := hm.mk f
  have hff : f =ᵐ[P] f' := hm.ae_eq_mk
  have hf' : MemLp f' 2 P := hf.ae_eq hff
  have key := rothaus_meas hm.measurable_mk hf'
  have hi : ∫ y, f y ∂P = ∫ y, f' y ∂P := integral_congr_ae hff
  rw [ent_congr_ae (show (fun x => f x ^ 2) =ᵐ[P] fun x => f' x ^ 2 from
      hff.mono fun x hx => by simp only [hx]), hi,
    ent_congr_ae (show (fun x => (f x - ∫ y, f' y ∂P) ^ 2) =ᵐ[P]
      fun x => (f' x - ∫ y, f' y ∂P) ^ 2 from hff.mono fun x hx => by simp only [hx]),
    show var P f = var P f' from ProbabilityTheory.evariance_congr hff]
  exact key

end DGPS.Ported.Rothaus
