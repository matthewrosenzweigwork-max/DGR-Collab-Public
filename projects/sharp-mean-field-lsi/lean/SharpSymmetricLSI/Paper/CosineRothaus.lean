import SharpSymmetricLSI.Paper.CosineRemark39
import SharpSymmetricLSI.Paper.Rothaus

/-!
# Remark 3.9, Rothaus variant (Phase 3, lane C; R43)

Rothaus' lemma (`Paper/Rothaus.lean`) + the defective LSI (3.24) applied to `f - E f` give
`Ent(f²) ≤ (2/a) E(f) + (κ+2) Var(f)`, hence `r^all ≥ 2aλ/(2λ + (κ+2)a)`.
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real

namespace SharpLSI

theorem rAll_ge_rothaus {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) :
    2 * ENNReal.ofReal aCos * lamAll cosV (cosW κ) N /
        (2 * lamAll cosV (cosW κ) N + ENNReal.ofReal ((κ + 2) * aCos)) ≤
      rAll cosV (cosW κ) N := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  have hyp := cosine_hyp_all κ
  haveI := gibbs_isProbabilityMeasure hyp N
  set P := gibbs cosV (cosW κ) N with hP
  set L := lamAll cosV (cosW κ) N with hL
  unfold rAll
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨hf1, hent⟩ := hf
  set c := ∫ X, f X ∂P with hc
  have hg1 : MemH1C P (fun X => f X - c) := by
    have := memH1C_add_const hyp hf1 (-c); simpa [sub_eq_add_neg] using this
  have hEg : energy cosV (cosW κ) N (fun X => f X - c) = energy cosV (cosW κ) N f := by
    have := energy_add_const hyp hf1 (-c); simpa [sub_eq_add_neg] using this
  have hdef := cosine_defective_aux hκ hN hg1
  have hvar : ∫⁻ X, ENNReal.ofReal ((f X - c) ^ 2) ∂P = var P f := by
    unfold var ProbabilityTheory.evariance
    congr 1; funext X
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  rw [hEg, hvar] at hdef
  have hroth := rothaus (memLp_of_memH1C hyp hf1)
  set A := ent P (fun X => f X ^ 2) with hA
  set E := energy cosV (cosW κ) N f with hE
  set V := var P f with hV
  have hAle : A ≤ ENNReal.ofReal (2 / aCos) * E + ENNReal.ofReal (κ + 2) * V := by
    calc A ≤ (ENNReal.ofReal (2 / aCos) * E + ENNReal.ofReal κ * V) + 2 * V :=
          hroth.trans (add_le_add hdef le_rfl)
      _ = ENNReal.ofReal (2 / aCos) * E + ENNReal.ofReal (κ + 2) * V := by
          rw [add_assoc, ← add_mul, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ← ENNReal.ofReal_add hκ.le (by norm_num)]
  have hLV : L * V ≤ E := by
    rcases (zero_le : (0 : ℝ≥0∞) ≤ V).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact zero_le
    · have : L ≤ E / V := iInf₂_le f ⟨hf1, hpos⟩
      exact ENNReal.mul_le_of_le_div this
  have hAt : A ≠ ⊤ := (ent_sq_lt_top_aux hyp hf1).ne
  have hEt : E ≠ ⊤ := (energy_lt_top hyp hf1).ne
  have hVt : V ≠ ⊤ := ProbabilityTheory.evariance_ne_top (memLp_of_memH1C hyp hf1)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hent.ne') (Or.inl hAt)]
  by_cases hLt : L = ⊤
  · rw [hLt]
    have h1 : 2 * ENNReal.ofReal aCos * ⊤ = ⊤ :=
      ENNReal.mul_top (by simp [ha0])
    have h2 : 2 * (⊤ : ℝ≥0∞) + ENNReal.ofReal ((κ + 2) * aCos) = ⊤ := by simp
    rw [h1, h2, ENNReal.div_top, zero_mul]
    exact zero_le
  set l := L.toReal with hl
  have hLl : L = ENNReal.ofReal l := (ENNReal.ofReal_toReal hLt).symm
  have hl0 : 0 ≤ l := ENNReal.toReal_nonneg
  set Ar := A.toReal
  set Er := E.toReal
  set Vr := V.toReal
  have hAA : A = ENNReal.ofReal Ar := (ENNReal.ofReal_toReal hAt).symm
  have hEE : E = ENNReal.ofReal Er := (ENNReal.ofReal_toReal hEt).symm
  have hVV : V = ENNReal.ofReal Vr := (ENNReal.ofReal_toReal hVt).symm
  have hAr0 : 0 ≤ Ar := ENNReal.toReal_nonneg
  have hEr0 : 0 ≤ Er := ENNReal.toReal_nonneg
  have hVr0 : 0 ≤ Vr := ENNReal.toReal_nonneg
  have hb0 : 0 < (κ + 2) * aCos := by positivity
  rw [hAA, hEE, hVV, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hAle
  rw [hLl, hVV, hEE, ← ENNReal.ofReal_mul hl0, ENNReal.ofReal_le_ofReal_iff hEr0] at hLV
  rw [hLl, hAA, hEE]
  have hX : 2 * ENNReal.ofReal aCos * ENNReal.ofReal l /
      (2 * ENNReal.ofReal l + ENNReal.ofReal ((κ + 2) * aCos)) =
      ENNReal.ofReal (2 * aCos * l / (2 * l + (κ + 2) * aCos)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]; simp
    · rw [ENNReal.ofReal_add (by positivity) hb0.le, ENNReal.ofReal_mul (p := 2) (by norm_num)]; simp
  rw [hX, ← ENNReal.ofReal_mul (by positivity), show (2 : ℝ≥0∞) * ENNReal.ofReal Er =
    ENNReal.ofReal (2 * Er) by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h1 : aCos * l * Ar ≤ aCos * l * (2 / aCos * Er + (κ + 2) * Vr) :=
    mul_le_mul_of_nonneg_left hAle (by positivity)
  have h2 : aCos * l * (2 / aCos * Er + (κ + 2) * Vr) =
      2 * l * Er + (κ + 2) * aCos * (l * Vr) := by field_simp
  have h3 : (κ + 2) * aCos * (l * Vr) ≤ (κ + 2) * aCos * Er :=
    mul_le_mul_of_nonneg_left hLV hb0.le
  nlinarith

theorem cosine_labeled_lsi_rothaus_aux {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) :
    2 * ENNReal.ofReal aCos * lamAll cosV (cosW κ) N /
        (2 * lamAll cosV (cosW κ) N + ENNReal.ofReal ((κ + 2) * aCos)) ≤
      rAll cosV (cosW κ) N ∧
    (2 * κ * Real.exp (2 * κ) ≤ N →
      ENNReal.ofReal (aCos / (1 + (κ + 2) * Real.exp (2 * κ))) ≤ rAll cosV (cosW κ) N) := by
  refine ⟨rAll_ge_rothaus hκ hN, fun hNκ => ?_⟩
  have ha0 : 0 < aCos := by unfold aCos; positivity
  have hlam := (cosine_labeled_constants_aux hκ hN hNκ).1
  set c := aCos * Real.exp (-2 * κ) / 2 with hc
  have hc0 : 0 < c := by positivity
  set b := (κ + 2) * aCos with hb
  have hb0 : 0 < b := by positivity
  refine le_trans ?_ (rAll_ge_rothaus hκ hN)
  have hLt := lamAll_lt_top (κ := κ) hN
  set l := (lamAll cosV (cosW κ) N).toReal
  have hLl : lamAll cosV (cosW κ) N = ENNReal.ofReal l := (ENNReal.ofReal_toReal hLt.ne).symm
  have hcl' : c ≤ l := (ENNReal.ofReal_le_iff_le_toReal hLt.ne).mp hlam
  rw [hLl]
  have hXe : 2 * ENNReal.ofReal aCos * ENNReal.ofReal l /
      (2 * ENNReal.ofReal l + ENNReal.ofReal ((κ + 2) * aCos)) =
      ENNReal.ofReal (2 * aCos * l / (2 * l + (κ + 2) * aCos)) := by
    rw [ENNReal.ofReal_div_of_pos (by nlinarith)]
    congr 1
    · rw [ENNReal.ofReal_mul (by nlinarith), ENNReal.ofReal_mul (by norm_num)]; simp
    · rw [ENNReal.ofReal_add (by nlinarith) hb0.le, ENNReal.ofReal_mul (p := 2) (by norm_num)]
      simp [hb]
  rw [hXe]
  have e : aCos / (1 + (κ + 2) * Real.exp (2 * κ)) = 2 * aCos * c / (2 * c + b) := by
    have he : Real.exp (-2 * κ) * Real.exp (2 * κ) = 1 := by rw [← Real.exp_add]; simp
    have hep := Real.exp_pos (-2 * κ)
    have hep2 := Real.exp_pos (2 * κ)
    rw [div_eq_div_iff (by positivity) (by positivity), hc, hb]
    linear_combination (-(κ + 2) * aCos ^ 2) * he
  rw [e]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_left hcl' (by positivity : (0 : ℝ) ≤ 2 * aCos * b)]

end SharpLSI
