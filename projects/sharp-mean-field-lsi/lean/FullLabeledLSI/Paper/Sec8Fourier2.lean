import FullLabeledLSI.Paper.Sec8Fourier1

/-!
# Section 8.5 (Corollary 8.4), part 2: kernels of positive type

For a smooth `K` on `𝕋^ι` with `Re K̂(k) ≥ 0` for all `k` and a finite measure `ν`,
`∬ K(x - y) dν(x) dν(y) = ∑_k K̂(k) |ν̂(k)|² ≥ 0`.
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff

namespace SharpLSI.FL
namespace Sec8

open SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The Fourier transform of a measure, `ν̂(k) = ∫ e_{-k} dν`. -/
noncomputable def nuHat (ν : Measure (UnitAddTorus ι)) (k : ι → ℤ) : ℂ := ∫ t, mFourier (-k) t ∂ν

theorem mFourier_add_pt (n : ι → ℤ) (x y : UnitAddTorus ι) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem mFourier_sub_eq (k : ι → ℤ) (x y : UnitAddTorus ι) :
    mFourier k (x - y) = mFourier k x * mFourier (-k) y := by
  have h1 : mFourier k x = mFourier k (x - y) * mFourier k y := by
    rw [← mFourier_add_pt, sub_add_cancel]
  have h2 : mFourier k y * mFourier (-k) y = 1 := by
    rw [← mFourier_add, add_neg_cancel, mFourier_zero]; rfl
  calc mFourier k (x - y) = mFourier k (x - y) * (mFourier k y * mFourier (-k) y) := by
        rw [h2, mul_one]
    _ = mFourier k x * mFourier (-k) y := by rw [h1]; ring

theorem integral_mFourier_meas (ν : Measure (UnitAddTorus ι)) (k : ι → ℤ) :
    ∫ t, mFourier k t ∂ν = conj (nuHat ν k) := by
  unfold nuHat
  rw [← integral_conj]
  congr 1; funext t
  rw [mFourier_neg, Complex.conj_conj]

theorem hasSum_double {K : UnitAddTorus ι → ℝ} (hK : IsSmoothT K) (ν : Measure (UnitAddTorus ι))
    [IsFiniteMeasure ν] :
    HasSum (fun k : ι → ℤ => cf K k * ((Complex.normSq (nuHat ν k) : ℝ) : ℂ))
      (((∫ x, ∫ y, K (x - y) ∂ν ∂ν : ℝ)) : ℂ) := by
  set c : (ι → ℤ) → ℂ := fun k => cf K k with hc
  have hs : Summable fun k => ‖c k‖ := summable_cf_of_smooth hK
  have hKc : Continuous K := continuous_of_isSmoothT hK
  have hmeasNu : ∀ k, ‖nuHat ν k‖ ≤ (ν Set.univ).toReal := fun k => by
    unfold nuHat
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ t, ‖mFourier (-k) t‖ ∂ν ≤ ∫ t, (1 : ℝ) ∂ν :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (integrable_const _) (Eventually.of_forall fun t => norm_mFourier_le _ _)
      _ = (ν Set.univ).toReal := by simp; rfl
  -- inner sum over y
  have hinner : ∀ x : UnitAddTorus ι, HasSum (fun k => c k * mFourier k x * nuHat ν k)
      (∫ y, (K (x - y) : ℂ) ∂ν) := by
    intro x
    have h := hasSum_integral_of_dominated_convergence (μ := ν)
      (F := fun (k : ι → ℤ) (y : UnitAddTorus ι) => c k * mFourier k x * mFourier (-k) y)
      (f := fun y => (K (x - y) : ℂ)) (fun k _ => ‖c k‖)
      (fun k => ((continuous_const.mul (mFourier (-k)).continuous)).aestronglyMeasurable)
      (fun k => Eventually.of_forall fun y => by
        rw [norm_mul, norm_mul]
        have := norm_mFourier_le k x
        have := norm_mFourier_le (-k) y
        calc ‖c k‖ * ‖mFourier k x‖ * ‖mFourier (-k) y‖ ≤ ‖c k‖ * 1 * 1 := by gcongr
          _ = ‖c k‖ := by ring)
      (Eventually.of_forall fun _ => hs)
      (integrable_const _)
      (Eventually.of_forall fun y => by
        have := hasSum_cf_series hK (x - y)
        simpa [hc, mFourier_sub_eq, mul_assoc] using this)
    convert h using 1
    funext k
    rw [integral_const_mul]
    rfl
  have hout := hasSum_integral_of_dominated_convergence (μ := ν)
    (F := fun (k : ι → ℤ) (x : UnitAddTorus ι) => c k * mFourier k x * nuHat ν k)
    (f := fun x => ∫ y, (K (x - y) : ℂ) ∂ν) (fun k _ => ‖c k‖ * (ν Set.univ).toReal)
    (fun k => ((continuous_const.mul (mFourier k).continuous).mul
      continuous_const).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun x => by
      rw [norm_mul, norm_mul]
      have := norm_mFourier_le k x
      have := hmeasNu k
      calc ‖c k‖ * ‖mFourier k x‖ * ‖nuHat ν k‖ ≤ ‖c k‖ * 1 * (ν Set.univ).toReal := by gcongr
        _ = ‖c k‖ * (ν Set.univ).toReal := by ring)
    (Eventually.of_forall fun _ => hs.mul_right _)
    (integrable_const _)
    (Eventually.of_forall hinner)
  have e1 : (fun x => ∫ y, (K (x - y) : ℂ) ∂ν) = fun x => ((∫ y, K (x - y) ∂ν : ℝ) : ℂ) := by
    funext x; exact integral_complex_ofReal
  rw [e1, integral_complex_ofReal] at hout
  convert hout using 1
  funext k
  rw [integral_mul_const, integral_const_mul, integral_mFourier_meas,
    Complex.normSq_eq_conj_mul_self]
  ring

/-- **Kernels of positive type.** -/
theorem pos_type {K : UnitAddTorus ι → ℝ} (hK : IsSmoothT K) (hpos : ∀ k, 0 ≤ (cf K k).re)
    (ν : Measure (UnitAddTorus ι)) [IsFiniteMeasure ν] : 0 ≤ ∫ x, ∫ y, K (x - y) ∂ν ∂ν := by
  have h := Complex.hasSum_re (hasSum_double hK ν)
  rw [Complex.ofReal_re] at h
  refine h.nonneg fun k => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact mul_nonneg (hpos k) (Complex.normSq_nonneg _)

end Sec8
end SharpLSI.FL
