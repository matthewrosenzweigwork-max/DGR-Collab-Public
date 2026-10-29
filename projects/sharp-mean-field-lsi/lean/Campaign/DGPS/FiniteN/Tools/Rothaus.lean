import DGPS.Foundations.Entropy
import DGPS.Ported.Rothaus

/-!
# Rothaus with quantitative tightening (FIN005)

For a probability `P`: `Ent_P(f²) ≤ Ent_P((f - Pf)²) + 2 Var_P(f)` (`rothaus_centering`), and the
consequence for defective inequalities: if `Ent_P(f²) ≤ A E(f) + B ‖f‖²` for all test functions
`f` and `Var_P(f) ≤ λ⁻¹ E(f)`, then `Ent_P(f²) ≤ (A + (B+2)/λ) E(f)` and the optimal LSI rate is
at least `2 / (A + (B+2)/λ)` (`rothaus_tightening`, `rothaus_with_quantitative_tightening`).

The entropy is `DGPS.homogeneousEntropy` (DEF004). The centering inequality is obtained from the
ported legacy Rothaus lemma `DGPS.Ported.Rothaus.rothaus` (the legacy `ent` agrees with
`homogeneousEntropy` on integrable functions, `homogeneousEntropy_eq_ent`).

The "smooth test functions" and the energy are abstract parameters: a predicate `Sm` on real
functions and an energy `E : (α → ℝ) → ℝ≥0∞`, with the structural hypotheses that test functions
are in `L²(P)`, are stable under subtracting constants, and that `E` is invariant under adding
constants. `lsiRate P Sm E` is the supremum of the `r ≥ 0` with `r Ent_P(f²) ≤ 2 E(f)` for all
test functions.
-/

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace DGPS.FiniteN.Tools.Rothaus

variable {α : Type*} [MeasurableSpace α]

/-- On integrable functions the legacy entropy `SharpLSI.ent` is `homogeneousEntropy`. -/
theorem homogeneousEntropy_eq_ent {P : Measure α} {v : α → ℝ} (hv : Integrable v P) :
    DGPS.homogeneousEntropy P v = SharpLSI.ent P v := by
  unfold SharpLSI.ent
  simp only [hv, ↓reduceIte]
  by_cases h : ∫ x, v x ∂P = 0
  · rw [DGPS.homogeneousEntropy_of_integral_eq_zero h]
    simp [h]
  · rw [DGPS.homogeneousEntropy_eq_lintegral_klFun h]

/-- Rothaus' centering inequality: `Ent_P(f²) ≤ Ent_P((f - Pf)²) + 2 Var_P(f)`, for `f ∈ L²(P)`.
The variance is the extended variance `evariance f P`; for `f ∈ L²` it is `ofReal (variance f P)`. -/
theorem rothaus_centering {P : Measure α} [IsProbabilityMeasure P] {f : α → ℝ}
    (hf : MemLp f 2 P) :
    DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤
      DGPS.homogeneousEntropy P (fun x => (f x - ∫ y, f y ∂P) ^ 2)
        + 2 * ProbabilityTheory.evariance f P := by
  have h1 : Integrable (fun x => f x ^ 2) P := hf.integrable_sq
  have h2 : Integrable (fun x => (f x - ∫ y, f y ∂P) ^ 2) P :=
    (hf.sub (memLp_const _)).integrable_sq
  rw [homogeneousEntropy_eq_ent h1, homogeneousEntropy_eq_ent h2]
  exact DGPS.Ported.Rothaus.rothaus hf

/-- `Ent_P(f²) ≤ Ent_P((f - Pf)²) + 2 Var_P(f)` with the real variance. -/
theorem rothaus_centering_variance {P : Measure α} [IsProbabilityMeasure P] {f : α → ℝ}
    (hf : MemLp f 2 P) :
    DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤
      DGPS.homogeneousEntropy P (fun x => (f x - ∫ y, f y ∂P) ^ 2)
        + ENNReal.ofReal (2 * ProbabilityTheory.variance f P) := by
  have h := rothaus_centering hf
  rwa [ENNReal.ofReal_mul (by norm_num), hf.ofReal_variance_eq, ENNReal.ofReal_ofNat]

/-- `LSIAt P Sm E r`: `r · Ent_P(f²) ≤ 2 E(f)` for every test function `f`. -/
def LSIAt (P : Measure α) (Sm : (α → ℝ) → Prop) (E : (α → ℝ) → ℝ≥0∞) (r : ℝ≥0) : Prop :=
  ∀ f, Sm f → (r : ℝ≥0∞) * DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤ 2 * E f

/-- The optimal LSI rate for the test class `Sm` and energy `E`: the supremum of the admissible
rates. -/
noncomputable def lsiRate (P : Measure α) (Sm : (α → ℝ) → Prop) (E : (α → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (_ : LSIAt P Sm E r), (r : ℝ≥0∞)

/-- Quantitative tightening: a defective LSI plus a Poincaré inequality gives a tight LSI. -/
theorem rothaus_tightening {P : Measure α} [IsProbabilityMeasure P]
    {Sm : (α → ℝ) → Prop} {E : (α → ℝ) → ℝ≥0∞}
    (hmem : ∀ f, Sm f → MemLp f 2 P)
    (hsub : ∀ f, Sm f → ∀ c : ℝ, Sm (fun x => f x - c))
    (hE : ∀ f, Sm f → ∀ c : ℝ, E (fun x => f x - c) = E f)
    {A B lam : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hdef : ∀ f, Sm f → DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤
      ENNReal.ofReal A * E f + ENNReal.ofReal B * ENNReal.ofReal (∫ x, f x ^ 2 ∂P))
    (hpoin : ∀ f, Sm f → ProbabilityTheory.evariance f P ≤ ENNReal.ofReal lam⁻¹ * E f) :
    (∀ f, Sm f → DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤
        ENNReal.ofReal (A + (B + 2) / lam) * E f) ∧
      ENNReal.ofReal (2 / (A + (B + 2) / lam)) ≤ lsiRate P Sm E := by
  have hC : 0 < A + (B + 2) / lam := by positivity
  have key : ∀ f, Sm f → DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤
      ENNReal.ofReal (A + (B + 2) / lam) * E f := by
    intro f hf
    set c := ∫ y, f y ∂P with hc
    have hg := hsub f hf c
    have hgm : MemLp (fun x => f x - c) 2 P := hmem _ hg
    have hfm := hmem f hf
    have hv : ENNReal.ofReal (∫ x, (f x - c) ^ 2 ∂P) = ProbabilityTheory.evariance f P := by
      rw [← hfm.ofReal_variance_eq, ProbabilityTheory.variance_eq_integral hfm.aemeasurable]
    have h1 := rothaus_centering hfm
    have h2 := hdef _ hg
    rw [hE f hf c, hv] at h2
    have h3 := hpoin f hf
    calc DGPS.homogeneousEntropy P (fun x => f x ^ 2)
        ≤ DGPS.homogeneousEntropy P (fun x => (f x - c) ^ 2)
            + 2 * ProbabilityTheory.evariance f P := h1
      _ ≤ (ENNReal.ofReal A * E f + ENNReal.ofReal B * ProbabilityTheory.evariance f P)
            + 2 * ProbabilityTheory.evariance f P := by gcongr
      _ = ENNReal.ofReal A * E f + ENNReal.ofReal (B + 2) * ProbabilityTheory.evariance f P := by
          rw [ENNReal.ofReal_add hB (by norm_num), ENNReal.ofReal_ofNat, add_mul, add_assoc]
      _ ≤ ENNReal.ofReal A * E f
            + ENNReal.ofReal (B + 2) * (ENNReal.ofReal lam⁻¹ * E f) := by gcongr
      _ = ENNReal.ofReal (A + (B + 2) / lam) * E f := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by linarith), ← add_mul, ← ENNReal.ofReal_add hA
            (by positivity), div_eq_mul_inv]
  refine ⟨key, ?_⟩
  have hr : 0 ≤ 2 / (A + (B + 2) / lam) := by positivity
  have hlsi : LSIAt P Sm E (2 / (A + (B + 2) / lam)).toNNReal := by
    intro f hf
    calc (((2 / (A + (B + 2) / lam)).toNNReal : ℝ≥0) : ℝ≥0∞) *
          DGPS.homogeneousEntropy P (fun x => f x ^ 2)
        ≤ ENNReal.ofReal (2 / (A + (B + 2) / lam)) *
            (ENNReal.ofReal (A + (B + 2) / lam) * E f) := by
          gcongr
          · exact le_of_eq rfl
          · exact key f hf
      _ = 2 * E f := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hr, div_mul_cancel₀ _ hC.ne', ENNReal.ofReal_ofNat]
  calc ENNReal.ofReal (2 / (A + (B + 2) / lam))
      = (((2 / (A + (B + 2) / lam)).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
    _ ≤ lsiRate P Sm E :=
        le_iSup_of_le (2 / (A + (B + 2) / lam)).toNNReal (le_iSup_of_le hlsi le_rfl)

/-- FIN005: Rothaus with quantitative tightening. For a probability `P`:
(1) `Ent_P(f²) ≤ Ent_P((f-Pf)²) + 2 Var_P(f)` for `f ∈ L²`;
(2) a defective LSI `Ent_P(f²) ≤ A E(f) + B ‖f‖²` together with `Var_P(f) ≤ λ⁻¹ E(f)` on the test
class gives `Ent_P(f²) ≤ (A + (B+2)/λ) E(f)`;
(3) the optimal LSI rate is at least `2 / (A + (B+2)/λ)`. -/
theorem rothaus_with_quantitative_tightening {P : Measure α} [IsProbabilityMeasure P] :
    (∀ f : α → ℝ, MemLp f 2 P →
      DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤
        DGPS.homogeneousEntropy P (fun x => (f x - ∫ y, f y ∂P) ^ 2)
          + 2 * ProbabilityTheory.evariance f P) ∧
    ∀ (Sm : (α → ℝ) → Prop) (E : (α → ℝ) → ℝ≥0∞),
      (∀ f, Sm f → MemLp f 2 P) →
      (∀ f, Sm f → ∀ c : ℝ, Sm (fun x => f x - c)) →
      (∀ f, Sm f → ∀ c : ℝ, E (fun x => f x - c) = E f) →
      ∀ {A B lam : ℝ}, 0 ≤ A → 0 ≤ B → 0 < lam →
      (∀ f, Sm f → DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤
        ENNReal.ofReal A * E f + ENNReal.ofReal B * ENNReal.ofReal (∫ x, f x ^ 2 ∂P)) →
      (∀ f, Sm f → ProbabilityTheory.evariance f P ≤ ENNReal.ofReal lam⁻¹ * E f) →
      (∀ f, Sm f → DGPS.homogeneousEntropy P (fun x => f x ^ 2) ≤
          ENNReal.ofReal (A + (B + 2) / lam) * E f) ∧
        ENNReal.ofReal (2 / (A + (B + 2) / lam)) ≤ lsiRate P Sm E :=
  ⟨fun _ hf => rothaus_centering hf,
    fun _ _ hmem hsub hE _ _ _ hA hB hlam hdef hpoin =>
      rothaus_tightening hmem hsub hE hA hB hlam hdef hpoin⟩

end DGPS.FiniteN.Tools.Rothaus

namespace DGPS.FiniteN

/-- Interface name from `declaration_ownership.json` (FIN005). -/
alias rothaus_with_quantitative_tightening :=
  DGPS.FiniteN.Tools.Rothaus.rothaus_with_quantitative_tightening

end DGPS.FiniteN
