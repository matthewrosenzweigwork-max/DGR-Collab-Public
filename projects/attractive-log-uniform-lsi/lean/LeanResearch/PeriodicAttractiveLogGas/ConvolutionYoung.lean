import LeanResearch.PeriodicAttractiveLogGas.GreenIntegrability
import LeanResearch.PeriodicAttractiveLogGas.PeriodicCalculus
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.FinCases

/-! Finite-output Young inequality for source Lemma 3.1.

The proof uses three-factor Hölder followed by Tonelli and Haar translation
invariance. The Hölder weights are `1/r`, `1/2`, and `1/2 - 1/r`; the last
weight is allowed to be zero, so the `r = 2`, `p = 1` endpoint is included.
The inner-product specialization uses the actual Euclidean planar norm and
has constant one. No convolution-integrability or Young conclusion is an
assumption. Transitive axiom inspection, integrated build and semantic review
are recorded separately from this mathematical declaration. -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal NNReal BigOperators Convolution

namespace PeriodicAttractiveLogGas

/-- The finite input exponent in source Lemma 3.1. -/
def youngExponent (r : ℝ) : ℝ := 2 * r / (r + 2)

theorem youngExponent_pos {r : ℝ} (hr : 2 ≤ r) : 0 < youngExponent r := by
  dsimp [youngExponent]
  exact div_pos (by linarith) (by linarith)

theorem one_le_youngExponent {r : ℝ} (hr : 2 ≤ r) : 1 ≤ youngExponent r := by
  dsimp [youngExponent]
  rw [le_div_iff₀ (by linarith : 0 < r + 2)]
  linarith

theorem youngExponent_lt_two {r : ℝ} (hr : 2 ≤ r) : youngExponent r < 2 := by
  dsimp [youngExponent]
  rw [div_lt_iff₀ (by linarith : 0 < r + 2)]
  linarith

@[simp] theorem youngExponent_two : youngExponent 2 = 1 := by
  norm_num [youngExponent]

theorem inv_youngExponent {r : ℝ} (hr : 2 ≤ r) :
    1 / youngExponent r = 1 / r + 1 / 2 := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith : 0 < r)
  have hr2 : r + 2 ≠ 0 := ne_of_gt (by linarith : 0 < r + 2)
  dsimp [youngExponent]
  field_simp [hr0, hr2]
  ring

theorem young_inv_nonneg {r : ℝ} (hr : 2 ≤ r) : 0 ≤ 1 / r :=
  le_of_lt (one_div_pos.mpr (by linarith))

theorem young_last_weight_nonneg {r : ℝ} (hr : 2 ≤ r) :
    0 ≤ 1 / 2 - 1 / r := by
  have hr0 : 0 < r := by linarith
  have h : 1 / r ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hr0).2
    linarith
  linarith

/-- Three-factor Hölder with nonnegative weights, including zero weights. -/
theorem lintegral_three_rpow_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f₀ f₁ f₂ : α → ℝ≥0∞}
    (h₀ : AEMeasurable f₀ μ) (h₁ : AEMeasurable f₁ μ)
    (h₂ : AEMeasurable f₂ μ) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : a + b + c = 1) :
    (∫⁻ x, f₀ x ^ a * f₁ x ^ b * f₂ x ^ c ∂μ) ≤
      (∫⁻ x, f₀ x ∂μ) ^ a * (∫⁻ x, f₁ x ∂μ) ^ b * (∫⁻ x, f₂ x ∂μ) ^ c := by
  let f : Fin 3 → α → ℝ≥0∞ := ![f₀, f₁, f₂]
  let w : Fin 3 → ℝ := ![a, b, c]
  have hm : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (f i) μ := by
    intro i _
    fin_cases i <;> simp only [f] <;> assumption
  have hw : ∑ i ∈ (Finset.univ : Finset (Fin 3)), w i = 1 := by
    simpa [w, Fin.sum_univ_succ, add_assoc] using hs
  have hn : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i <;> simp only [w] <;> assumption
  have h := ENNReal.lintegral_prod_norm_pow_le (Finset.univ : Finset (Fin 3)) hm hw hn
  simpa [f, w, Fin.prod_univ_succ, mul_assoc] using h

theorem young_factorization {r : ℝ} (hr : 2 ≤ r) (u v : ℝ≥0∞) :
    (u ^ youngExponent r * v ^ (2 : ℝ)) ^ (1 / r) *
        (u ^ youngExponent r) ^ (1 / 2 : ℝ) *
        (v ^ (2 : ℝ)) ^ (1 / 2 - 1 / r) = u * v := by
  have hr0 : r ≠ 0 := ne_of_gt (by linarith : 0 < r)
  have hr2 : r + 2 ≠ 0 := ne_of_gt (by linarith : 0 < r + 2)
  have hp : 0 ≤ youngExponent r := (youngExponent_pos hr).le
  have ha := young_inv_nonneg hr
  have hc := young_last_weight_nonneg hr
  have he₁ : youngExponent r * (1 / r) + youngExponent r * (1 / 2) = 1 := by
    dsimp [youngExponent]
    field_simp [hr0, hr2]
    ring
  have he₂ : (2 : ℝ) * (1 / r) + 2 * (1 / 2 - 1 / r) = 1 := by ring
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha]
  simp only [← ENNReal.rpow_mul]
  calc
    u ^ (youngExponent r * (1 / r)) * v ^ (2 * (1 / r)) *
        u ^ (youngExponent r * (1 / 2)) * v ^ (2 * (1 / 2 - 1 / r)) =
      (u ^ (youngExponent r * (1 / r)) * u ^ (youngExponent r * (1 / 2))) *
        (v ^ (2 * (1 / r)) * v ^ (2 * (1 / 2 - 1 / r))) := by ac_rfl
    _ = u * v := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hp ha)
        (mul_nonneg hp (by norm_num)),
        ← ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg (by norm_num) ha)
          (mul_nonneg (by norm_num) hc), he₁, he₂]
      simp

section Haar

variable {A : Type*} [MeasurableSpace A] [AddCommGroup A]
  [MeasurableAdd₂ A] [MeasurableNeg A] {μ : Measure A}
  [SFinite μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]

/-- The extended nonnegative finite-output Young inequality. It does not
require input finiteness, and all exponent operations have nonnegative powers. -/
theorem lintegral_young_two {r : ℝ} (hr : 2 ≤ r) {f g : A → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ x, (∫⁻ y, f y * g (x - y) ∂μ) ^ r ∂μ) ^ (1 / r) ≤
      (∫⁻ y, f y ^ youngExponent r ∂μ) ^ (1 / youngExponent r) *
        (∫⁻ y, g y ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have hrpos : 0 < r := by linarith
  have hr0 : r ≠ 0 := hrpos.ne'
  have ha := young_inv_nonneg hr
  have hc := young_last_weight_nonneg hr
  have hd : 0 ≤ r / 2 - 1 := by linarith
  let B : ℝ≥0∞ := ∫⁻ y, f y ^ youngExponent r ∂μ
  let C : ℝ≥0∞ := ∫⁻ y, g y ^ (2 : ℝ) ∂μ
  let H : A → A → ℝ≥0∞ := fun x y ↦ f y ^ youngExponent r * g (x - y) ^ (2 : ℝ)
  have hgsub (x : A) : AEMeasurable (fun y ↦ g (x - y)) μ :=
    hg.comp_quasiMeasurePreserving (μ.measurePreserving_sub_left x).quasiMeasurePreserving
  have hH : AEMeasurable (Function.uncurry H) (μ.prod μ) := by
    exact (hf.comp_snd.pow_const _).mul
      ((hg.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant μ μ)).pow_const _)
  have hHI : AEMeasurable (fun x ↦ ∫⁻ y, H x y ∂μ) μ := hH.lintegral_prod_right
  have hholder (x : A) : (∫⁻ y, f y * g (x - y) ∂μ) ≤
      (∫⁻ y, H x y ∂μ) ^ (1 / r) * B ^ (1 / 2 : ℝ) * C ^ (1 / 2 - 1 / r) := by
    have h := lintegral_three_rpow_le (a := 1 / r) (b := 1 / 2) (c := 1 / 2 - 1 / r)
      ((hf.pow_const (youngExponent r)).mul ((hgsub x).pow_const (2 : ℝ)))
      (hf.pow_const (youngExponent r))
      ((hgsub x).pow_const (2 : ℝ)) ha (by norm_num) hc (by ring)
    have hfac : (fun y ↦ (f y ^ youngExponent r * g (x - y) ^ (2 : ℝ)) ^ (1 / r) *
        (f y ^ youngExponent r) ^ (1 / 2 : ℝ) *
        (g (x - y) ^ (2 : ℝ)) ^ (1 / 2 - 1 / r)) =
        (fun y ↦ f y * g (x - y)) := by
      funext y
      exact young_factorization hr _ _
    simp only [Pi.mul_apply] at h
    rw [hfac, lintegral_sub_left_eq_self (fun y ↦ g y ^ (2 : ℝ)) x] at h
    exact h
  have hpoint (x : A) : (∫⁻ y, f y * g (x - y) ∂μ) ^ r ≤
      (∫⁻ y, H x y ∂μ) * B ^ (r / 2) * C ^ (r / 2 - 1) := by
    have h := ENNReal.rpow_le_rpow (hholder x) hrpos.le
    have he₁ : (1 / r) * r = 1 := by field_simp [hr0]
    have he₂ : (1 / 2 - 1 / r) * r = r / 2 - 1 := by field_simp [hr0]
    simpa only [ENNReal.mul_rpow_of_nonneg _ _ hrpos.le, ← ENNReal.rpow_mul,
      he₁, he₂, ENNReal.rpow_one, show (1 / 2 : ℝ) * r = r / 2 by ring] using h
  have hmass : (∫⁻ x, ∫⁻ y, H x y ∂μ ∂μ) = B * C := by
    rw [lintegral_lintegral_swap hH]
    calc
      (∫⁻ y, ∫⁻ x, H x y ∂μ ∂μ) =
          ∫⁻ y, f y ^ youngExponent r * C ∂μ := by
        apply lintegral_congr
        intro y
        change (∫⁻ x, f y ^ youngExponent r * g (x - y) ^ (2 : ℝ) ∂μ) =
          f y ^ youngExponent r * C
        have hgm : AEMeasurable (fun x ↦ g (x - y) ^ (2 : ℝ)) μ :=
          (hg.comp_quasiMeasurePreserving
            (measurePreserving_sub_right μ y).quasiMeasurePreserving).pow_const _
        rw [lintegral_const_mul'' _ hgm,
          lintegral_sub_right_eq_self (fun x ↦ g x ^ (2 : ℝ)) y]
      _ = B * C := lintegral_mul_const'' _ (hf.pow_const _)
  have hpower : (∫⁻ x, (∫⁻ y, f y * g (x - y) ∂μ) ^ r ∂μ) ≤
      B ^ (1 + r / 2) * C ^ (r / 2) := by
    calc
      (∫⁻ x, (∫⁻ y, f y * g (x - y) ∂μ) ^ r ∂μ) ≤
          ∫⁻ x, (∫⁻ y, H x y ∂μ) * B ^ (r / 2) * C ^ (r / 2 - 1) ∂μ :=
        lintegral_mono hpoint
      _ = (B * C) * B ^ (r / 2) * C ^ (r / 2 - 1) := by
        rw [lintegral_mul_const'' _ (hHI.mul_const _), lintegral_mul_const'' _ hHI, hmass]
      _ = (B ^ (1 : ℝ) * B ^ (r / 2)) * (C ^ (1 : ℝ) * C ^ (r / 2 - 1)) := by
        simp only [ENNReal.rpow_one]
        ac_rfl
      _ = B ^ (1 + r / 2) * C ^ (r / 2) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by positivity),
          ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) hd]
        congr 1
        congr 1
        ring
  have he₁ : (1 + r / 2) * (1 / r) = 1 / youngExponent r := by
    rw [inv_youngExponent hr]
    field_simp [hr0]
  have he₂ : (r / 2) * (1 / r) = (1 / 2 : ℝ) := by field_simp [hr0]
  have h := ENNReal.rpow_le_rpow hpower ha
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ ha, ← ENNReal.rpow_mul, he₁, he₂] using h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [AddCommGroup A] [MeasurableAdd₂ A] [MeasurableNeg A] [SFinite μ]
  [IsAddLeftInvariant μ] [IsNegInvariant μ] [InnerProductSpace ℝ E] in
theorem eLpNorm_ofReal_formula {F : A → E} (hF : AEStronglyMeasurable F μ)
    {s : ℝ} (hs : 0 < s) :
    eLpNorm F (ENNReal.ofReal s) μ = (∫⁻ x, ‖F x‖ₑ ^ s ∂μ) ^ (1 / s) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hs).ne'
    ENNReal.ofReal_ne_top hF, ENNReal.toReal_ofReal hs.le]

/-- Constant-one finite-output Young inequality for a real inner-product
convolution on an invariant commutative group. No input finiteness is needed
for this extended-valued inequality. -/
theorem eLpNorm_inner_convolution_le {r : ℝ} (hr : 2 ≤ r) {F G : A → E}
    (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ) :
    eLpNorm (fun x ↦ ∫ y, inner ℝ (F y) (G (x - y)) ∂μ) (ENNReal.ofReal r) μ ≤
      eLpNorm F (ENNReal.ofReal (youngExponent r)) μ * eLpNorm G 2 μ := by
  have hrpos : 0 < r := by linarith
  have hm : AEStronglyMeasurable (fun x ↦ ∫ y, inner ℝ (F y) (G (x - y)) ∂μ) μ := by
    simpa only [convolution_def, innerSL_apply_apply] using!
      (hF.convolution (L := innerSL ℝ) hG)
  have hnorm (x : A) : ‖∫ y, inner ℝ (F y) (G (x - y)) ∂μ‖ₑ ≤
      ∫⁻ y, ‖F y‖ₑ * ‖G (x - y)‖ₑ ∂μ :=
    (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_mono fun y ↦ enorm_inner_le_enorm (F y) (G (x - y)))
  calc
    eLpNorm (fun x ↦ ∫ y, inner ℝ (F y) (G (x - y)) ∂μ) (ENNReal.ofReal r) μ =
        (∫⁻ x, ‖∫ y, inner ℝ (F y) (G (x - y)) ∂μ‖ₑ ^ r ∂μ) ^ (1 / r) :=
      eLpNorm_ofReal_formula hm hrpos
    _ ≤ (∫⁻ x, (∫⁻ y, ‖F y‖ₑ * ‖G (x - y)‖ₑ ∂μ) ^ r ∂μ) ^ (1 / r) :=
      ENNReal.rpow_le_rpow (lintegral_mono fun x ↦
        ENNReal.rpow_le_rpow (hnorm x) hrpos.le) (young_inv_nonneg hr)
    _ ≤ (∫⁻ y, ‖F y‖ₑ ^ youngExponent r ∂μ) ^ (1 / youngExponent r) *
        (∫⁻ y, ‖G y‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) :=
      lintegral_young_two hr hF.enorm hG.enorm
    _ = eLpNorm F (ENNReal.ofReal (youngExponent r)) μ * eLpNorm G 2 μ := by
      rw [eLpNorm_ofReal_formula hF (youngExponent_pos hr)]
      congr 1
      simpa using (eLpNorm_ofReal_formula hG (s := (2 : ℝ)) (by norm_num)).symm

theorem memLp_inner_convolution {r : ℝ} (hr : 2 ≤ r) {F G : A → E}
    (hF : MemLp F (ENNReal.ofReal (youngExponent r)) μ) (hG : MemLp G 2 μ) :
    MemLp (fun x ↦ ∫ y, inner ℝ (F y) (G (x - y)) ∂μ) (ENNReal.ofReal r) μ :=
  (eLpNorm_inner_convolution_le hr hF.aestronglyMeasurable hG.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top hF.eLpNorm_lt_top hG.eLpNorm_lt_top)

theorem lpNorm_inner_convolution_le {r : ℝ} (hr : 2 ≤ r) {F G : A → E}
    (hF : MemLp F (ENNReal.ofReal (youngExponent r)) μ) (hG : MemLp G 2 μ) :
    lpNorm (fun x ↦ ∫ y, inner ℝ (F y) (G (x - y)) ∂μ) (ENNReal.ofReal r) μ ≤
      lpNorm F (ENNReal.ofReal (youngExponent r)) μ * lpNorm G 2 μ := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_lt_top hF.eLpNorm_lt_top hG.eLpNorm_lt_top).ne
    (eLpNorm_inner_convolution_le hr hF.aestronglyMeasurable hG.aestronglyMeasurable)
  simpa only [ENNReal.toReal_mul, toReal_eLpNorm] using h

omit [IsNegInvariant μ] in
/-- Finite input norms on a finite Haar measure give an actual integrable
convolution integrand at almost every output point, independently of the
totalized convention used by the Bochner integral. -/
theorem ae_integrable_inner_convolution [IsFiniteMeasure μ] {r : ℝ} (hr : 2 ≤ r)
    {F G : A → E} (hF : MemLp F (ENNReal.ofReal (youngExponent r)) μ)
    (hG : MemLp G 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ inner ℝ (F y) (G (x - y))) μ := by
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (youngExponent r) := by
    simpa using ENNReal.ofReal_le_ofReal (one_le_youngExponent hr)
  have h := (hF.integrable hp).ae_convolution_exists (L := innerSL ℝ)
    (hG.integrable (by norm_num))
  simpa only [ConvolutionExistsAt, innerSL_apply_apply] using! h

end Haar

/-- Haar convolution of planar vector fields using their real inner product. -/
def torusInnerConvolution (F G : Torus → PlanarSpace) (x : Torus) : ℝ :=
  ∫ y, inner ℝ (F y) (G (x - y)) ∂torusMeasure

/-- The exact source Young estimate, including actual `Lr` membership and
existence of the defining integral at almost every output point. -/
theorem torusInnerConvolution_young {r : ℝ} (hr : 2 ≤ r) {F G : Torus → PlanarSpace}
    (hF : MemLp F (ENNReal.ofReal (youngExponent r)) torusMeasure)
    (hG : MemLp G 2 torusMeasure) :
    MemLp (torusInnerConvolution F G) (ENNReal.ofReal r) torusMeasure ∧
      (∀ᵐ x ∂torusMeasure, Integrable (fun y ↦ inner ℝ (F y) (G (x - y))) torusMeasure) ∧
      lpNorm (torusInnerConvolution F G) (ENNReal.ofReal r) torusMeasure ≤
        lpNorm F (ENNReal.ofReal (youngExponent r)) torusMeasure * lpNorm G 2 torusMeasure := by
  exact ⟨memLp_inner_convolution hr hF hG,
    ae_integrable_inner_convolution hr hF hG, lpNorm_inner_convolution_le hr hF hG⟩

/-- The endpoint is `L1 * L2 → L2`, with the same unit constant. -/
theorem torusInnerConvolution_young_endpoint {F G : Torus → PlanarSpace}
    (hF : MemLp F 1 torusMeasure) (hG : MemLp G 2 torusMeasure) :
    MemLp (torusInnerConvolution F G) 2 torusMeasure ∧
      (∀ᵐ x ∂torusMeasure, Integrable (fun y ↦ inner ℝ (F y) (G (x - y))) torusMeasure) ∧
      lpNorm (torusInnerConvolution F G) 2 torusMeasure ≤
        lpNorm F 1 torusMeasure * lpNorm G 2 torusMeasure := by
  simpa using torusInnerConvolution_young (r := 2) le_rfl (F := F) (G := G)
    (by simpa using hF) hG

/-- The actual Green gradient supplies the first factor for every finite
real output exponent in the manuscript, without any extra moment premise. -/
theorem torusInnerConvolution_greenGradient_young {r : ℝ} (hr : 2 ≤ r)
    {G : Torus → PlanarSpace} (hG : MemLp G 2 torusMeasure) :
    MemLp (torusInnerConvolution greenGradient G) (ENNReal.ofReal r) torusMeasure ∧
      (∀ᵐ x ∂torusMeasure,
        Integrable (fun y ↦ inner ℝ (greenGradient y) (G (x - y))) torusMeasure) ∧
      lpNorm (torusInnerConvolution greenGradient G) (ENNReal.ofReal r) torusMeasure ≤
        lpNorm greenGradient (ENNReal.ofReal (youngExponent r)) torusMeasure *
          lpNorm G 2 torusMeasure :=
  torusInnerConvolution_young hr
    (memLp_greenGradient (youngExponent r) (one_le_youngExponent hr) (youngExponent_lt_two hr)) hG

end PeriodicAttractiveLogGas
