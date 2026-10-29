import FullLabeledLSI.Paper.AdmissibleFinite
import FullLabeledLSI.Statements.S07_Prop_3_1
import SharpSymmetricLSI.Paper.Defective25
import SharpSymmetricLSI.Statements.R17_Centered_Identities

/-!
# Mean-field step A: bounded H¹ densities, the conditional family, (M1)
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {β : Type*}

/-! ### A. Finite averages of bounded `H¹`-type densities -/

section avg

/-- Bundled data of a conditional one-particle law: a measurable probability density `ρ` on the torus
with `c ≤ ρ ≤ C` (`c > 0`) and an `L²` weak gradient `g`.  (This is what the conditional-law block
delivers for a.e. revealed configuration.) -/
structure IsBddH1Dens (ρ : Torus d → ℝ) (g : Torus d → Fin d → ℝ) (c C : ℝ) : Prop where
  pos : 0 < c
  meas : Measurable ρ
  ge : ∀ x, c ≤ ρ x
  le : ∀ x, ρ x ≤ C
  int_one : ∫ x, ρ x ∂haar d = 1
  grad : IsWeakGrad ρ g
  grad_L2 : ∀ k, MemLp (fun x => g x k) 2 (haar d)

/-- The average `ρ̄ = (1/n) ∑_{i∈R} ρ_i`. -/
noncomputable def avgDensR (R : Finset β) (ρ : β → Torus d → ℝ) (x : Torus d) : ℝ :=
  (R.card : ℝ)⁻¹ * ∑ i ∈ R, ρ i x

/-- The average of the gradients, `(1/n) ∑_{i∈R} g_i`. -/
noncomputable def avgGrad (R : Finset β) (g : β → Torus d → Fin d → ℝ) (x : Torus d)
    (k : Fin d) : ℝ :=
  (R.card : ℝ)⁻¹ * ∑ i ∈ R, g i x k

/-- The conditional family of F01 with `q = n = R.card`, `θₐ = 1/n`, `ρₐ = ρ_{e a}` for the
canonical enumeration `e = (Finset.equivFin R).symm : Fin n ≃ R`. -/
noncomputable def finFamily (R : Finset β) (ρ : β → Torus d → ℝ) : Family d where
  q := R.card
  θ := fun _ => (R.card : ℝ)⁻¹
  ρ := fun a => ρ ((R.equivFin.symm a : R) : β)

/-- Reindexing of sums over the family to sums over `R` (valid for any additive commutative monoid
target and any function `h` of the density; used for `msDiss`, `msGap`, `Family.bar`). -/
theorem finFamily_sum {M : Type*} [AddCommMonoid M] (R : Finset β) (ρ : β → Torus d → ℝ)
    (h : (Torus d → ℝ) → M) :
    ∑ a, h ((finFamily R ρ).ρ a) = ∑ i ∈ R, h (ρ i) := by
  have h1 : ∑ a, h ((finFamily R ρ).ρ a) = ∑ a, (fun i : R => h (ρ (i : β))) (R.equivFin.symm a) :=
    rfl
  rw [h1, Equiv.sum_comp R.equivFin.symm (fun i : R => h (ρ (i : β)))]
  exact Finset.sum_coe_sort R (fun i => h (ρ i))

/-- `bar` of the conditional family is `avgDensR`. -/
theorem finFamily_bar (R : Finset β) (ρ : β → Torus d → ℝ) :
    (finFamily R ρ).bar = avgDensR R ρ := by
  funext x
  have h1 : (finFamily R ρ).bar x = ∑ a, (R.card : ℝ)⁻¹ * ((finFamily R ρ).ρ a) x := rfl
  rw [h1, ← Finset.mul_sum, finFamily_sum R ρ (fun f => f x)]
  rfl

/-- `√ρ ∈ H¹(m)` from the bounded data (wrapper of `memH1_sqrt_of_ge`). -/
theorem IsBddH1Dens.memH1_sqrt {ρ : Torus d → ℝ} {g : Torus d → Fin d → ℝ} {c C : ℝ}
    (h : IsBddH1Dens ρ g c C) : MemH1 (haar d) (fun x => Real.sqrt (ρ x)) :=
  memH1_sqrt_of_ge h.meas h.grad h.grad_L2 h.pos h.ge h.le

/-- Admissibility of the conditional family from the weakest hypotheses (nonneg., normalised,
`√ρᵢ ∈ H¹`), for `R` nonempty. -/
theorem finFamily_admissible_of_memH1 {R : Finset β} (hR : R.Nonempty) {ρ : β → Torus d → ℝ}
    (h : ∀ i ∈ R, (∀ x, 0 ≤ ρ i x) ∧ ∫ x, ρ i x ∂haar d = 1 ∧
      MemH1 (haar d) (fun x => Real.sqrt (ρ i x))) :
    (finFamily R ρ).Admissible := by
  have hc : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  refine ⟨fun a => ?_, ?_, fun a => ?_⟩
  · exact inv_pos.mpr hc
  · show ∑ _a : Fin R.card, (R.card : ℝ)⁻¹ = 1
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hc.ne']
  · exact h _ (R.equivFin.symm a).2

/-- **(M2)** The conditional family of bounded `H¹` densities is admissible. -/
theorem finFamily_admissible {R : Finset β} (hR : R.Nonempty) {ρ : β → Torus d → ℝ}
    {g : β → Torus d → Fin d → ℝ} {c C : ℝ} (h : ∀ i ∈ R, IsBddH1Dens (ρ i) (g i) c C) :
    (finFamily R ρ).Admissible :=
  finFamily_admissible_of_memH1 hR fun i hi =>
    ⟨fun x => ((h i hi).pos.trans_le ((h i hi).ge x)).le, (h i hi).int_one, (h i hi).memH1_sqrt⟩

/-- The average of bounded `H¹` densities is a bounded `H¹` density (same constants), with weak
gradient `avgGrad`.  (Uses `IsWeakGrad.add`, `IsWeakGrad.cmul`, `memLp_finsetSum`.) -/
theorem IsBddH1Dens.avg {R : Finset β} (hR : R.Nonempty) {ρ : β → Torus d → ℝ}
    {g : β → Torus d → Fin d → ℝ} {c C : ℝ} (h : ∀ i ∈ R, IsBddH1Dens (ρ i) (g i) c C) :
    IsBddH1Dens (avgDensR R ρ) (avgGrad R g) c C := by
  have hc : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  have hint : ∀ i ∈ R, Integrable (ρ i) (haar d) := fun i hi => by
    by_contra hn
    have := (h i hi).int_one
    rw [integral_undef hn] at this
    exact zero_ne_one this
  obtain ⟨i₀, hi₀⟩ := hR
  refine ⟨(h i₀ hi₀).pos, ?_, fun x => ?_, fun x => ?_, ?_, ?_, fun k => ?_⟩
  · exact (Finset.measurable_sum R fun i hi => (h i hi).meas).const_mul _
  · unfold avgDensR
    have hS : (R.card : ℝ) * c ≤ ∑ i ∈ R, ρ i x := by
      simpa using Finset.card_nsmul_le_sum R (fun i => ρ i x) c fun i hi => (h i hi).ge x
    calc c = (R.card : ℝ)⁻¹ * ((R.card : ℝ) * c) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hS (inv_nonneg.2 hc.le)
  · unfold avgDensR
    have hS : ∑ i ∈ R, ρ i x ≤ (R.card : ℝ) * C := by
      simpa using Finset.sum_le_card_nsmul R (fun i => ρ i x) C fun i hi => (h i hi).le x
    calc _ ≤ (R.card : ℝ)⁻¹ * ((R.card : ℝ) * C) :=
          mul_le_mul_of_nonneg_left hS (inv_nonneg.2 hc.le)
      _ = C := by field_simp
  · unfold avgDensR
    rw [integral_const_mul, integral_finsetSum R hint]
    rw [Finset.sum_congr rfl fun i hi => (h i hi).int_one]
    simp [inv_mul_cancel₀ hc.ne']
  · exact (isWeakGrad_finsetSum R fun i hi => (h i hi).grad).cmul (R.card : ℝ)⁻¹
  · unfold avgGrad
    exact (memLp_finsetSum R fun i hi => (h i hi).grad_L2 k).const_mul _

end avg

/-! ### B. (M1) the definition of `r_ms`, applied to one family -/

/-- **(M1) The definition of `r_ms`, applied to one admissible family:** `2 r₀ G_θ ≤ D_θ` for
`r₀ ≤ r_ms`.  (No `Hyp` needed: if `G_θ = ⊤` or `⊥` then `(G_θ).toReal = 0`.) -/
theorem two_r_ms_gap_le {r₀ : ℝ} (hr₀ : 0 ≤ r₀) (hrr : ENNReal.ofReal r₀ ≤ rMs V W)
    {F : Family d} (hF : F.Admissible) :
    ENNReal.ofReal (2 * r₀ * (msGap V W F).toReal) ≤ msDiss V W F := by
  set G := msGap V W F
  by_cases hG : 0 < G
  · by_cases hGt : G = ⊤
    · rw [hGt]; simp
    have hadm : MsAdmissible V W F := ⟨hF, hG⟩
    have hle : rMs V W ≤ msDiss V W F / (2 * G.toENNReal) := iInf₂_le F hadm
    have hGe : G.toENNReal = ENNReal.ofReal G.toReal := EReal.toENNReal_of_ne_top hGt
    have hGpos : 0 < G.toReal := EReal.toReal_pos hG hGt
    have h2 : ENNReal.ofReal r₀ ≤ msDiss V W F / (2 * ENNReal.ofReal G.toReal) := by
      rw [← hGe]; exact hrr.trans hle
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hGpos]))
      (Or.inl (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))] at h2
    calc ENNReal.ofReal (2 * r₀ * G.toReal)
        = ENNReal.ofReal r₀ * (2 * ENNReal.ofReal G.toReal) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat]
          ring
      _ ≤ _ := h2
  · rw [not_lt] at hG
    have : G.toReal ≤ 0 := by
      rcases eq_or_ne G ⊥ with h | h
      · rw [h]; simp
      · exact EReal.toReal_nonpos hG
    rw [ENNReal.ofReal_of_nonpos (by nlinarith)]
    exact bot_le

end SharpLSI.FL
