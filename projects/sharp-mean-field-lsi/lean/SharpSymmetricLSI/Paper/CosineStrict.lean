import SharpSymmetricLSI.Paper.CircleNear

/-!
# `r_{*,κ} > a` (Phase 3, lane C; R12 `cosine_strict`)

For admissible `ρ`, with `H = H(ρ|m)`, `I = I(ρ|m)`, `Q = Q(ρ)`, `G = H + κQ/2` and
`D = I + 2aκQ + κ²∫ρ|(g*ρ)'|²` ((3.4), (3.18)), `D - 2aG = (I - 2aH) + aκQ + κ²∫ρ|(g*ρ)'|²`
with every term nonnegative ((3.11)). If the quotient is `< c` then, using `H ≤ G ≤ (1+κ)H`
((3.20)), `0 ≤ I/(2H) - a ≤ (1+κ)(c - a)` and `Q/H ≤ 2(1+κ)(c - a)/(aκ)`. A sequence with
`c_n ↓ a` would contradict Lemma 3.3 (`Q/H → 1`).
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real

namespace SharpLSI

theorem cosine_quotient_bounds {κ : ℝ} (hκ : 0 < κ) {ρ : Torus 1 → ℝ}
    (hρ : Admissible cosV (cosW κ) ρ) {c : ℝ}
    (hq : dissipation cosV (cosW κ) ρ / (2 * (gap cosV (cosW κ) (densMeasure ρ)).toENNReal) <
      ENNReal.ofReal c) :
    0 < (klDiv (densMeasure ρ) (haar 1)).toReal ∧
    fisherInfo (densMeasure ρ) (haar 1) ≠ ⊤ ∧
    aCos ≤ (fisherInfo (densMeasure ρ) (haar 1)).toReal /
      (2 * (klDiv (densMeasure ρ) (haar 1)).toReal) ∧
    (fisherInfo (densMeasure ρ) (haar 1)).toReal / (2 * (klDiv (densMeasure ρ) (haar 1)).toReal)
      ≤ aCos + (1 + κ) * (c - aCos) ∧
    firstMode ρ / (klDiv (densMeasure ρ) (haar 1)).toReal ≤
      2 * (1 + κ) / (aCos * κ) * (c - aCos) := by
  obtain ⟨hρ0, hρ1, hH1, hgap⟩ := hρ
  have aux := circle_quantitative_lsi_aux hρ0 hρ1 hH1
  set H := (klDiv (densMeasure ρ) (haar 1)).toReal with hHdef
  set I := (fisherInfo (densMeasure ρ) (haar 1)).toReal with hIdef
  set Q := firstMode ρ with hQdef
  set J := ∫ x, ρ x * weakGrad (gConv ρ) x 0 ^ 2 ∂haar 1 with hJdef
  have ha : aCos = 4 * π ^ 2 := rfl
  have ha0 : 0 < aCos := by rw [ha]; positivity
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hI0 : 0 ≤ I := ENNReal.toReal_nonneg
  have hQ0 : 0 ≤ Q := Complex.normSq_nonneg _
  have hJ0 : 0 ≤ J := integral_nonneg fun x => mul_nonneg (hρ0 x) (sq_nonneg _)
  have hfi : fisherInfo (densMeasure ρ) (haar 1) = ENNReal.ofReal I :=
    (ENNReal.ofReal_toReal aux.2.1).symm
  have hkl : klDiv (densMeasure ρ) (haar 1) = ENNReal.ofReal H :=
    (ENNReal.ofReal_toReal aux.1).symm
  have hD : dissipation cosV (cosW κ) ρ =
      ENNReal.ofReal (I + 2 * aCos * κ * Q + κ ^ 2 * J) := by
    rw [cosine_dissipation_expansion_aux hκ hρ0 hρ1 aux.2.1, hfi,
      ← ENNReal.ofReal_add hI0 (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hG : gap cosV (cosW κ) (densMeasure ρ) = ((H + κ / 2 * Q : ℝ) : EReal) := by
    rw [(cosine_free_energy_aux hκ).2.2.2.1 ρ hρ0 hρ1, hkl, EReal.coe_ennreal_ofReal,
      max_eq_left hH0, ← EReal.coe_add]
  set G := H + κ / 2 * Q with hGdef
  have hG0 : 0 < G := by rw [hG] at hgap; exact_mod_cast hgap
  -- `Q ≤ 2H`
  have hcmp := cosine_entropy_comparison_aux hκ hρ0 hρ1
  have hQH : Q ≤ 2 * H := by
    have h := hcmp.1.trans hcmp.2.1
    rw [hkl, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have hHpos : 0 < H := by
    by_contra h
    have hH : H = 0 := le_antisymm (not_lt.mp h) hH0
    have : Q = 0 := le_antisymm (by linarith) hQ0
    rw [hGdef, hH, this] at hG0; simp at hG0
  -- the real quotient
  set D := I + 2 * aCos * κ * Q + κ ^ 2 * J with hDdef
  have hr : D / (2 * G) < c := by
    rw [hD, hG, EReal.real_coe_toENNReal, ← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_div_of_pos (by positivity)] at hq
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp hq
  have h311 : aCos / 6 * H ^ 2 ≤ I - 2 * aCos * H := aux.2.2.2
  have hdef0 : 0 ≤ I - 2 * aCos * H := le_trans (by positivity) h311
  have hexc : D - 2 * aCos * G = (I - 2 * aCos * H) + aCos * κ * Q + κ ^ 2 * J := by
    simp only [hDdef, hGdef]; ring
  have hDlt : D < 2 * G * c := by rwa [div_lt_iff₀ (by positivity), mul_comm] at hr
  have hGle : G ≤ (1 + κ) * H := by simp only [hGdef]; nlinarith
  have hca : aCos ≤ c := by
    by_contra h; push_neg at h
    have : 2 * G * c < 2 * G * aCos := by nlinarith
    nlinarith [hexc, mul_nonneg hκ.le hQ0, mul_nonneg (sq_nonneg κ) hJ0]
  have hE : D - 2 * aCos * G ≤ 2 * (1 + κ) * H * (c - aCos) := by
    have h1 : D - 2 * aCos * G < 2 * G * (c - aCos) := by linarith
    have h2 : 2 * G * (c - aCos) ≤ 2 * ((1 + κ) * H) * (c - aCos) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  have hT1 : I - 2 * aCos * H ≤ 2 * (1 + κ) * H * (c - aCos) := by
    have : 0 ≤ aCos * κ * Q + κ ^ 2 * J := by positivity
    linarith
  have hT2 : aCos * κ * Q ≤ 2 * (1 + κ) * H * (c - aCos) := by
    have : 0 ≤ κ ^ 2 * J := by positivity
    linarith
  refine ⟨hHpos, aux.2.1, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)]; linarith
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · rw [div_le_iff₀ hHpos]
    have hak : 0 < aCos * κ := by positivity
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hak]
    nlinarith

theorem cosine_strict_aux {κ : ℝ} (hκ : 0 < κ) : ENNReal.ofReal aCos < rStar cosV (cosW κ) := by
  have ha : aCos = 4 * π ^ 2 := rfl
  have ha0 : 0 < aCos := by rw [ha]; positivity
  by_contra hcon
  push_neg at hcon
  have hex : ∀ n : ℕ, ∃ ρ, Admissible cosV (cosW κ) ρ ∧
      dissipation cosV (cosW κ) ρ / (2 * (gap cosV (cosW κ) (densMeasure ρ)).toENNReal) <
        ENNReal.ofReal (aCos + 1 / (n + 1)) := by
    intro n
    have hlt : rStar cosV (cosW κ) < ENNReal.ofReal (aCos + 1 / (n + 1)) :=
      hcon.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        (by have : (0 : ℝ) < 1 / (n + 1) := by positivity
            linarith))
    unfold rStar at hlt
    obtain ⟨ρ, hlt⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hρ, hlt⟩ := iInf_lt_iff.mp hlt
    exact ⟨ρ, hρ, hlt⟩
  choose ρ hρA hρq using hex
  have hb := fun n => cosine_quotient_bounds hκ (hρA n) (hρq n)
  have hρ0 : ∀ n x, 0 ≤ ρ n x := fun n => (hρA n).1
  have hρ1 : ∀ n, ∫ x, ρ n x ∂haar 1 = 1 := fun n => (hρA n).2.1
  have hne : ∀ n, ¬ (ρ n =ᵐ[haar 1] fun _ => 1) := fun n h => by
    have h1 : densMeasure (ρ n) = haar 1 := by
      unfold densMeasure
      rw [withDensity_congr_ae (g := fun _ => (1 : ℝ≥0∞))
        (h.mono fun x hx => by simp only [hx, ENNReal.ofReal_one])]
      exact withDensity_one
    have := (hb n).1
    rw [h1, klDiv_self] at this
    simp at this
  have hδ : Tendsto (fun n : ℕ => (aCos + 1 / ((n : ℝ) + 1)) - aCos) atTop (𝓝 0) := by
    have e : (fun n : ℕ => (aCos + 1 / ((n : ℝ) + 1)) - aCos) = fun n : ℕ => 1 / ((n : ℝ) + 1) :=
      funext fun n => by ring
    rw [e]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => (fisherInfo (densMeasure (ρ n)) (haar 1)).toReal /
      (2 * (klDiv (densMeasure (ρ n)) (haar 1)).toReal)) atTop (𝓝 aCos) := by
    have hup : Tendsto (fun n : ℕ => aCos + (1 + κ) * ((aCos + 1 / ((n : ℝ) + 1)) - aCos)) atTop
        (𝓝 aCos) := by simpa using (hδ.const_mul (1 + κ)).const_add aCos
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (hb n).2.2.1) (fun n => (hb n).2.2.2.1)
  have hR11 := (circle_near_extremizers_aux hρ0 hρ1 hne (fun n => (hb n).2.1) hlim).2.2.2
  have hzero : Tendsto (fun n => firstMode (ρ n) / (klDiv (densMeasure (ρ n)) (haar 1)).toReal)
      atTop (𝓝 0) := by
    have hup : Tendsto (fun n : ℕ => 2 * (1 + κ) / (aCos * κ) *
        ((aCos + 1 / ((n : ℝ) + 1)) - aCos)) atTop (𝓝 0) := by
      simpa using hδ.const_mul (2 * (1 + κ) / (aCos * κ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => div_nonneg (Complex.normSq_nonneg _) (hb n).1.le) (fun n => (hb n).2.2.2.2)
  have := tendsto_nhds_unique hR11 hzero
  norm_num at this

end SharpLSI
