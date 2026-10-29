/- DGR source Step3, TeX2575–2595: proper exponential moments from even
factorial moments. The canonical-array factorial estimate is a separate upstream
proof obligation; no exponential integrability or expectation is assumed here.
Native Real.hasSum_cosh, geometric series and Fatou are reused at the pinned
Mathlib revision with their full primary sources/license captured in records. -/
import DGRHS.Concentration.MasterLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace DGRHS.Attractive

/-- Native Fatou for a nonnegative real limit, with proper approximants and a
finite expectation bound. Adapted from the accepted exponential Fatou proof. -/
lemma nonnegative_integrable_of_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hi : ∀ n,Integrable (f n) μ) (hnn : ∀ n,∀ᵐ x ∂μ,0 ≤ f n x)
    (hg : ∀ᵐ x ∂μ,0 ≤ g x) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ n,(∫ x,f n x ∂μ) ≤ M)
    (ht : ∀ᵐ x ∂μ,Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Integrable g μ ∧ (∫ x,g x ∂μ) ≤ M := by
  have hm : AEStronglyMeasurable g μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hi n).aestronglyMeasurable) ht
  have ht' := ht.mono fun x hx => ENNReal.tendsto_ofReal hx
  have hb' : ∀ n,(∫⁻ x,ENNReal.ofReal (f n x) ∂μ) ≤ ENNReal.ofReal M := by
    intro n
    rw [←ofReal_integral_eq_lintegral_ofReal (hi n) (hnn n)]
    exact ENNReal.ofReal_le_ofReal (hb n)
  have hFatou : (∫⁻ x,ENNReal.ofReal (g x) ∂μ) ≤ ENNReal.ofReal M := by
    calc
      _ = ∫⁻ x,liminf (fun n => ENNReal.ofReal (f n x)) atTop ∂μ :=
        lintegral_congr_ae (ht'.mono fun x hx => hx.liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ x,ENNReal.ofReal (f n x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => ENNReal.measurable_ofReal.comp_aemeasurable
          (hi n).aestronglyMeasurable.aemeasurable)
      _ ≤ ENNReal.ofReal M := liminf_le_of_frequently_le' (Frequently.of_forall hb')
  have hgi : Integrable g μ := ⟨hm,(hasFiniteIntegral_iff_ofReal hg).mpr
    (hFatou.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hgi,?_⟩
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hFatou
  rw [←ofReal_integral_eq_lintegral_ofReal hgi hg] at h
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hg),ENNReal.toReal_ofReal hM] using h

 theorem exponential_of_even_factorial_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : AEMeasurable X μ)
    (A t : ℝ) (hA : 0 ≤ A) (ht : |t| * A < 1)
    (hi : ∀ k : ℕ,Integrable (fun x => |X x|^(2*k)) μ)
    (hb : ∀ k : ℕ,(∫ x,|X x|^(2*k) ∂μ) ≤ A^(2*k)*((2*k).factorial : ℝ)) :
    Integrable (fun x => Real.exp (t*X x)) μ ∧
      (∫ x,Real.exp (t*X x) ∂μ) ≤ 2/(1-(t*A)^2) := by
  let q := (t*A)^2
  let B := fun k : ℕ => fun x : Ω => (t*X x)^(2*k)/((2*k).factorial : ℝ)
  have hq0 : 0 ≤ q := sq_nonneg _
  have hq1 : q < 1 := by
    have hh : |t*A| < 1 := by simpa only [abs_mul,abs_of_nonneg hA] using ht
    dsimp [q]
    nlinarith [sq_abs (t*A),abs_nonneg (t*A)]
  have hgeom : HasSum (fun k : ℕ => q^k) ((1-q)⁻¹) :=
    hasSum_geometric_of_abs_lt_one (by simpa only [abs_of_nonneg hq0] using hq1)
  have hEven (k : ℕ) (x : Ω) : |X x|^(2*k)=X x^(2*k) := by
    rw [←abs_pow]
    apply abs_of_nonneg
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hBi : ∀ k,Integrable (B k) μ := by
    intro k
    have hi' : Integrable (fun x => X x^(2*k)) μ := by simpa only [hEven] using hi k
    simpa only [B,mul_pow] using (hi'.const_mul (t^(2*k))).div_const ((2*k).factorial : ℝ)
  have hBn : ∀ k x,0 ≤ B k x := by
    intro k x
    dsimp [B]
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  have hBb : ∀ k,(∫ x,B k x ∂μ) ≤ q^k := by
    intro k
    have hf : 0 < ((2*k).factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
    have htp : 0 ≤ t^(2*k) := by rw [pow_mul];exact pow_nonneg (sq_nonneg _) _
    have hm := mul_le_mul_of_nonneg_left (hb k) htp
    simp only [hEven] at hm
    calc
      _ = t^(2*k)*(∫ x,X x^(2*k) ∂μ)/((2*k).factorial : ℝ) := by
        dsimp [B]
        simp_rw [mul_pow]
        rw [integral_div,integral_const_mul]
      _ ≤ (t^(2*k)*(A^(2*k)*((2*k).factorial : ℝ)))/((2*k).factorial : ℝ) :=
        div_le_div_of_nonneg_right hm hf.le
      _ = q^k := by
        dsimp [q]
        rw [←mul_assoc,mul_div_cancel_right₀ _ (ne_of_gt hf),←mul_pow,pow_mul]
  let P := fun n : ℕ => fun x : Ω => ∑ k ∈ Finset.range n,B k x
  have hPi : ∀ n,Integrable (P n) μ := fun n => integrable_finset_sum _ (fun k _ => hBi k)
  have hPn : ∀ n x,0 ≤ P n x := fun n x => Finset.sum_nonneg (fun k _ => hBn k x)
  have hPb : ∀ n,(∫ x,P n x ∂μ) ≤ (1-q)⁻¹ := by
    intro n
    dsimp [P]
    rw [integral_finset_sum _ (fun k _ => hBi k)]
    exact (Finset.sum_le_sum (fun k _ => hBb k)).trans
      (by rw [←hgeom.tsum_eq];exact hgeom.summable.sum_le_tsum _ (fun k _ => pow_nonneg hq0 _))
  have hPt : ∀ᵐ x ∂μ,Tendsto (fun n => P n x) atTop (𝓝 (Real.cosh (t*X x))) :=
    Filter.Eventually.of_forall fun x => (Real.hasSum_cosh (t*X x)).tendsto_sum_nat
  obtain ⟨hCosh,hCB⟩ := nonnegative_integrable_of_ae_tendsto μ P (fun x => Real.cosh (t*X x))
    hPi (fun n => Filter.Eventually.of_forall (hPn n))
    (Filter.Eventually.of_forall (fun x => (Real.cosh_pos _).le)) _
    (inv_nonneg.mpr (by linarith)) hPb hPt
  have hDom : ∀ x,Real.exp (t*X x) ≤ 2*Real.cosh (t*X x) := by
    intro x
    rw [Real.cosh_eq]
    nlinarith [Real.exp_pos (-(t*X x))]
  have hmExp : AEStronglyMeasurable (fun x : Ω => Real.exp (t*X x)) μ :=
    (Real.measurable_exp.comp_aemeasurable (hX.const_mul t)).aestronglyMeasurable
  have hExp : Integrable (fun x : Ω => Real.exp (t*X x)) μ := (hCosh.const_mul 2).mono'
    hmExp
    (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hDom x))
  refine ⟨hExp,?_⟩
  calc
    _ ≤ ∫ x,2*Real.cosh (t*X x) ∂μ := integral_mono hExp (hCosh.const_mul 2) hDom
    _ = 2*(∫ x,Real.cosh (t*X x) ∂μ) := integral_const_mul _ _
    _ ≤ 2*(1-q)⁻¹ := mul_le_mul_of_nonneg_left hCB (by norm_num)
    _ = _ := by rfl
end DGRHS.Attractive
#print axioms DGRHS.Attractive.nonnegative_integrable_of_ae_tendsto
#print axioms DGRHS.Attractive.exponential_of_even_factorial_moments
#check @DGRHS.Attractive.exponential_of_even_factorial_moments
