import SharpSymmetricLSI.Infra.WeakGrad

/-!
# Entropy, variance, Fisher information (infrastructure for D3, D4)

* `ent P u` is `Ent_P(u)` of manuscript (1.3), valued in `ℝ≥0∞` through the nonnegative form
  `∫ ū · klFun(u/ū) dP`, `ū = ∫ u dP`, `klFun x = x log x + 1 - x`. It agrees with (1.3)
  whenever `u log u` is integrable (`ent_eq_formula`) and is `⊤` when the entropy integral
  diverges. For non-integrable `u`, where (1.3) is undefined, it is `⊤` by convention.
* `var` is `Var_P(f) = ∫ (f - ∫ f dP)² dP`, Mathlib's `ProbabilityTheory.evariance`.
* `fisherInfo ν P` is `I(ν|P)` of (1.4), `⊤` unless `ν ≪ P` and `√(dν/dP) ∈ H^1(P)`.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace SharpLSI

section Ent

variable {α : Type*} [MeasurableSpace α]

open Classical in
/-- `Ent_P(u)` (manuscript (1.3)), in `ℝ≥0∞`. -/
noncomputable def ent (P : Measure α) (u : α → ℝ) : ℝ≥0∞ :=
  if Integrable u P then
    ∫⁻ x, ENNReal.ofReal ((∫ y, u y ∂P) * klFun (u x / ∫ y, u y ∂P)) ∂P
  else ⊤

/-- Sanity lemma for D3: `ent` agrees with formula (1.3) for nonnegative integrable `u` with
`u log u` integrable (with `0 log 0 = 0`, automatic from `Real.log 0 = 0`). -/
theorem ent_eq_formula (P : Measure α) [IsProbabilityMeasure P] (u : α → ℝ)
    (hu : ∀ x, 0 ≤ u x) (hint : Integrable u P)
    (hlog : Integrable (fun x => u x * Real.log (u x)) P) :
    ent P u = ENNReal.ofReal (∫ x, u x * Real.log (u x) ∂P
      - (∫ x, u x ∂P) * Real.log (∫ x, u x ∂P)) := by
  unfold ent
  simp only [hint, ↓reduceIte]
  set c := ∫ x, u x ∂P with hc
  have hc0 : 0 ≤ c := integral_nonneg hu
  rcases hc0.eq_or_lt with h0 | h0
  · have hz : u =ᵐ[P] 0 := (integral_eq_zero_iff_of_nonneg hu hint).mp h0.symm
    have h1 : ∫ x, u x * Real.log (u x) ∂P = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      · filter_upwards [hz] with x hx; simp [hx]
    rw [← h0, h1]; simp
  · have hpt : ∀ x, c * klFun (u x / c) = u x * Real.log (u x) - u x * Real.log c + c - u x := by
      intro x
      unfold klFun
      rcases (hu x).eq_or_lt with h | h
      · rw [← h]; simp
      · rw [Real.log_div h.ne' h0.ne']; field_simp
    simp_rw [hpt]
    have hF : Integrable (fun x => u x * Real.log (u x) - u x * Real.log c + c - u x) P :=
      ((hlog.sub (hint.mul_const _)).add (integrable_const c)).sub hint
    have hnn : 0 ≤ᵐ[P] fun x => u x * Real.log (u x) - u x * Real.log c + c - u x :=
      Filter.Eventually.of_forall fun x => by
        simp only [Pi.zero_apply]
        rw [← hpt]; exact mul_nonneg hc0 (klFun_nonneg (div_nonneg (hu x) hc0))
    rw [← ofReal_integral_eq_lintegral_ofReal hF hnn]
    congr 1
    have i1 : Integrable (fun x => u x * Real.log c) P := hint.mul_const _
    have i2 : Integrable (fun x => u x * Real.log (u x) - u x * Real.log c) P := hlog.sub i1
    have i3 : Integrable (fun x => u x * Real.log (u x) - u x * Real.log c + c) P :=
      i2.add (integrable_const c)
    rw [integral_sub i3 hint, integral_add i2 (integrable_const c), integral_sub hlog i1,
      integral_mul_const, integral_const, ← hc]
    simp

/-- `Var_P(f)`, in `ℝ≥0∞`. -/
noncomputable abbrev var (P : Measure α) (f : α → ℝ) : ℝ≥0∞ := ProbabilityTheory.evariance f P

end Ent

section Fisher

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- Fisher information `I(ν|P) = 4 ∫ |∇√(dν/dP)|² dP` on a torus (manuscript (1.4)),
`⊤` unless `ν ≪ P` and `√(dν/dP) ∈ H^1(P)`. -/
noncomputable def fisherInfo (ν P : Measure (UnitAddTorus ι)) : ℝ≥0∞ :=
  if ν ≪ P ∧ MemH1 P (fun x => Real.sqrt (ν.rnDeriv P x).toReal) then
    4 * dirichlet P (fun x => Real.sqrt (ν.rnDeriv P x).toReal)
  else ⊤

/-- Fisher information on a configuration space `(𝕋^d)^N`. -/
noncomputable def fisherInfoC {N d : ℕ} (ν P : Measure (Config N d)) : ℝ≥0∞ :=
  fisherInfo (ν.map flat) (P.map flat)

end Fisher

end SharpLSI
