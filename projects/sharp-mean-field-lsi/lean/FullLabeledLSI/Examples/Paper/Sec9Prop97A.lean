import FullLabeledLSI.Examples.E01f_Deficit
import FullLabeledLSI.Examples.Paper.Sec9LamG

/-!
# Proposition 9.7, part A: Fourier coefficients, uniqueness of the Haar minimizer, `λ_G` bound

Lane C of the Section 9 formalization.  For `C = harmKernel k a` (`k ≥ 1`, `0 ≤ a < 1`):

* `chat_harm_k`: `Ĉ(n) = a` for `n = ±k` and `0` otherwise;
* `harmKernel_haarUnique`: Haar measure is the unique free-energy minimizer;
* `lamG_le_harm`: every reference-data `λ_G` is `≤ 4π² k² (1-a)` (uses lane D's proved `LaneD.lamG_formula`);
* `rMs_ge_of_deficit_nonneg`: nonnegative deficits give `r ≤ r_ms`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.P97

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR

theorem cosMode_complex_k (k : ℕ) (x : Torus 1) :
    (cosMode k x : ℂ) = (fourier (k : ℤ) (x 0) + fourier (-(k : ℤ)) (x 0)) / 2 := by
  unfold cosMode
  rw [fourier_neg, Complex.add_conj]
  simp

theorem chat_harm_k {k : ℕ} (hk : 1 ≤ k) (a : ℝ) (n : ℤ) :
    chat (harmKernel k a) n = if n = k ∨ n = -k then a else 0 := by
  unfold chat
  have hexp : ∀ x : Torus 1, fourier (-n) (x 0) * (harmKernel k a x : ℂ) =
      a * (fourier (-n + k) (x 0) + fourier (-n - k) (x 0)) := fun x => by
    unfold harmKernel
    push_cast
    rw [cosMode_complex_k, fourier_add, show -n - k = -n + -(k : ℤ) by ring, fourier_add]
    ring
  simp_rw [hexp]
  have hfi : ∀ m : ℤ, Integrable (fun x : Torus 1 => fourier m (x 0)) (haar 1) := fun m =>
    ((fourier m).continuous.comp (continuous_apply (0 : Fin 1))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_const_mul, integral_add (hfi _) (hfi _), int_fourier, int_fourier]
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hk0 : k ≠ 0 := by omega
  by_cases h1 : n = k
  · subst h1
    have e1 : (-(k : ℤ) + k = 0) := by ring
    have e2 : ¬ (-(k : ℤ) - k = 0) := by omega
    simp [e1, e2, hk0]
  · by_cases h2 : n = -k
    · subst h2
      simp [hk0]
    · have e1 : ¬ (-n + k = 0) := fun h => h1 (by omega)
      have e2 : ¬ (-n - k = 0) := fun h => h2 (by omega)
      simp [e1, e2, h1, h2]

theorem chat_harm_le_k {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (n : ℤ) :
    chat (harmKernel k a) n ≤ a := by
  rw [chat_harm_k hk]; split_ifs <;> linarith

/-! ### Uniqueness of the Haar minimizer -/

theorem harmKernel_haarUnique {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HaarUniqueMinimizer (attrW (harmKernel k a)) := by
  refine ⟨Def.harmKernel_isMinimizer hk ha0 ha1.le, fun μ hμ => ?_⟩
  have hC := Def.goodKernel_harmKernel hk a
  set G : Torus 1 → ℝ := fun x => -harmKernel k a x with hG
  have hGc : Continuous G := (continuous_of_isSmoothT hC.smooth).neg
  have hG0 : G 0 = -(2 * a) := by
    simp only [hG, Def.harmKernel_eq, Def.cosK_zero]; ring
  have hz : zeroV = fun _ => (0 : ℝ) := rfl
  unfold IsMinimizer at hμ
  rw [Def.Fstar_harm hk ha0 ha1.le, attrW_eq_WG, hz] at hμ
  have : IsProbabilityMeasure (μ : Measure (Torus 1)) := inferInstance
  rw [Sec8.freeEnergy_WG hGc] at hμ
  have hK : klDiv (μ : Measure (Torus 1)) (haar 1) ≠ ⊤ := by
    intro h
    rw [h] at hμ
    simp at hμ
  have hac : (μ : Measure (Torus 1)) ≪ haar 1 := (klDiv_ne_top_iff.1 hK).1
  set ρ := densOf (μ : Measure (Torus 1)) with hρ
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => ENNReal.toReal_nonneg
  have hρ1 : ∫ x, ρ x ∂haar 1 = 1 := integral_densOf_eq_one hac
  have hρi : Integrable ρ (haar 1) := integrable_densOf _
  have hμ' : (μ : Measure (Torus 1)) = densMeasure ρ := eq_densMeasure_densOf hac
  have hfe := fourier_entropy_bound_proved hk ρ hρ0 hρ1
  rw [← hμ', Def.normSq_fourier hρi k] at hfe
  set H := (klDiv (μ : Measure (Torus 1)) (haar 1)).toReal with hH
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hKH : klDiv (μ : Measure (Torus 1)) (haar 1) = ENNReal.ofReal H :=
    (ENNReal.ofReal_toReal hK).symm
  rw [hKH] at hfe
  have hn : Def.mcos k ρ ^ 2 + Def.msin k ρ ^ 2 ≤ H := (ENNReal.ofReal_le_ofReal_iff hH0).1 hfe
  have hQ := Def.Qint_neg_harm k a (μ : Measure (Torus 1))
  have e1 : ∫ x, Reg.cosK k x ∂(μ : Measure (Torus 1)) = Def.mcos k ρ :=
    (integral_densOf_mul hac (Reg.cosK k)).symm
  have e2 : ∫ x, sinK k x ∂(μ : Measure (Torus 1)) = Def.msin k ρ :=
    (integral_densOf_mul hac (sinK k)).symm
  rw [e1, e2] at hQ
  have hQ' : Sec8.Qint (μ : Measure (Torus 1)) G =
      -(2 * a) * (Def.mcos k ρ ^ 2 + Def.msin k ρ ^ 2) := hQ
  rw [← EReal.coe_ennreal_toReal hK, ← EReal.coe_add, EReal.coe_eq_coe_iff, hQ', hG0] at hμ
  set n := Def.mcos k ρ ^ 2 + Def.msin k ρ ^ 2 with hnn
  have hn0 : 0 ≤ n := by positivity
  -- H + (−2a n + 2a)/2 = a, so H = a n, hence n ≤ a n, n = 0, H = 0
  have hHeq : H = a * n := by linarith
  have hn00 : n = 0 := by nlinarith
  have hH00 : H = 0 := by rw [hHeq, hn00]; ring
  have hkl0 : klDiv (μ : Measure (Torus 1)) (haar 1) = 0 := by rw [hKH, hH00]; simp
  have hmu : (μ : Measure (Torus 1)) = haar 1 := (klDiv_eq_zero_iff.1 hkl0)
  exact Subtype.ext hmu

/-! ### The `λ_G` upper bound and the `r_ms` lower bound -/

theorem lamG_le_harm {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ)
    (he : IsRefEigenbasis (haar 1) e lam)
    (hCm : IsInverseOfIPlus (Tmat (attrW (harmKernel k a)) (haar 1) e) Cm) :
    lamG (lamShift lam) Cm ≤ ENNReal.ofReal (aCos * (k : ℝ) ^ 2 * (1 - a)) := by
  have hC := Def.goodKernel_harmKernel hk a
  have hmin := Def.harmKernel_isMinimizer hk ha0 ha1.le
  have hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat (harmKernel k a) n ≤ 1 - δ :=
    ⟨1 - a, by linarith, fun n _ => by have := chat_harm_le_k hk ha0 n; linarith⟩
  rw [LaneD.lamG_formula hC hmin (hyp_attr_aux hC) hsup e lam Cm he hCm]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  refine (iInf_le _ j).trans (le_of_eq ?_)
  have h1 : chat (harmKernel (j + 1) a) ((j : ℤ) + 1) = a := by
    rw [chat_harm_k hk]; simp
  rw [h1]
  congr 1
  push_cast
  ring

theorem rMs_ge_of_deficit_nonneg {k : ℕ} (hk : 1 ≤ k) {a : ℝ} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ F : Family 1, F.Admissible → 0 ≤ deficit (attrW (harmKernel k a)) r F) :
    ENNReal.ofReal r ≤ rMs zeroV (attrW (harmKernel k a)) := by
  obtain ⟨KV, KW, hyp⟩ := hyp_attr_aux (Def.goodKernel_harmKernel hk a)
  refine rMs_ge_of_deficit hyp hr fun F hF => ?_
  have := h F hF
  unfold deficit at this
  linarith

end SharpLSI.FL.Ex.P97
