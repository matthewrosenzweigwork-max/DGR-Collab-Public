import DGRHS.Concentration.MomentPolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace DGRHS.Concentration

lemma normalization_scales (m : ℕ) (hm : 1 ≤ m) (v M : ℝ)
    (hv : 0 ≤ v) (hM : 0 < M) :
    let R := Real.sqrt (m : ℝ) * Real.sqrt v + (m : ℝ) * M ^ (1 / (m : ℝ))
    let t := (m : ℝ) / R
    0 < R ∧ 0 ≤ t ∧ t ^ 2 * v ≤ (m : ℝ) ∧ t ^ m * M ≤ 1 := by
  dsimp only
  let R := Real.sqrt (m : ℝ) * Real.sqrt v + (m : ℝ) * M ^ (1 / (m : ℝ))
  let t := (m : ℝ) / R
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmge : 0 ≤ (m : ℝ) := hmpos.le
  have hmne : m ≠ 0 := by omega
  have hrootge : 0 ≤ M ^ (1 / (m : ℝ)) := Real.rpow_nonneg hM.le _
  have hrootpos : 0 < M ^ (1 / (m : ℝ)) := Real.rpow_pos_of_pos hM _
  have hRpos : 0 < R := add_pos_of_nonneg_of_pos
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (mul_pos hmpos hrootpos)
  have htge : 0 ≤ t := div_nonneg hmge hRpos.le
  have hR1 : Real.sqrt (m : ℝ) * Real.sqrt v ≤ R :=
    le_add_of_nonneg_right (mul_nonneg hmge hrootge)
  have hR2 : (m : ℝ) * M ^ (1 / (m : ℝ)) ≤ R :=
    le_add_of_nonneg_left (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hRsq : (m : ℝ) * v ≤ R ^ 2 := by
    have hs := pow_le_pow_left₀
      (mul_nonneg (Real.sqrt_nonneg (m : ℝ)) (Real.sqrt_nonneg v)) hR1 2
    simpa only [mul_pow, Real.sq_sqrt hmge, Real.sq_sqrt hv] using hs
  have hvnorm : t ^ 2 * v ≤ (m : ℝ) := by
    dsimp [t]
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (pow_pos hRpos 2)]
    have hs := mul_le_mul_of_nonneg_left hRsq hmge
    nlinarith
  have htr : t * M ^ (1 / (m : ℝ)) ≤ 1 := by
    dsimp [t]
    rw [div_mul_eq_mul_div, div_le_iff₀ hRpos]
    simpa only [one_mul] using hR2
  have hMpow : (M ^ (1 / (m : ℝ))) ^ m = M := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hM.le hmne
  have hMnorm : t ^ m * M ≤ 1 := by
    have hp := pow_le_pow_left₀ (mul_nonneg htge hrootge) htr m
    simpa only [mul_pow, hMpow, one_pow] using hp
  exact ⟨hRpos, htge, hvnorm, hMnorm⟩

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

/-- Scalar even Rosenthal bound from actual moments and full coordinate independence. -/
theorem scalar_even_rosenthal_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (k : ℕ) (hk : 1 ≤ k) (hX : iIndepFun X μ)
    (hXm : ∀ i, AEStronglyMeasurable (X i) μ)
    (hh : ∀ i, Integrable (fun ω ↦ |X i ω| ^ (2 * k)) μ)
    (hc : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    (∫ ω, |∑ i, X i ω| ^ (2 * k) ∂μ) ^ (1 / ((2 * k : ℕ) : ℝ)) ≤
      3 * (Real.sqrt ((2 * k : ℕ) : ℝ) * Real.sqrt (∑ i, ∫ ω, X i ω ^ 2 ∂μ) +
        ((2 * k : ℕ) : ℝ) * (∑ i, ∫ ω, |X i ω| ^ (2 * k) ∂μ) ^ (1 / ((2 * k : ℕ) : ℝ))) := by
  classical
  let m := 2 * k
  let v := ∑ i, ∫ ω, X i ω ^ 2 ∂μ
  let M := ∑ i, ∫ ω, |X i ω| ^ m ∂μ
  let Q := ∫ ω, |∑ i, X i ω| ^ m ∂μ
  let R := Real.sqrt (m : ℝ) * Real.sqrt v + (m : ℝ) * M ^ (1 / (m : ℝ))
  have hm : 2 ≤ m := by dsimp [m]; omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmne : m ≠ 0 := by omega
  have hv : 0 ≤ v := Finset.sum_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg (X i ω)
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ ↦
    integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg (X i ω)) m
  have hQ : 0 ≤ Q := integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg _) m
  have hR : 0 ≤ R := add_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg hmpos.le (Real.rpow_nonneg hM _))
  change Q ^ (1 / (m : ℝ)) ≤ 3 * R
  by_cases hMzero : M = 0
  · have hXi : ∀ i, X i =ᵐ[μ] 0 := by
      intro i
      have hmi : (∫ ω, |X i ω| ^ m ∂μ) = 0 := by
        have hi : (∫ ω, |X i ω| ^ m ∂μ) ≤ M := by
          dsimp only [M]
          exact Finset.single_le_sum (f := fun j ↦ ∫ ω, |X j ω| ^ m ∂μ)
            (fun j _ ↦ integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg (X j ω)) m)
            (Finset.mem_univ i)
        exact le_antisymm (hi.trans_eq hMzero)
          (integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg (X i ω)) m)
      have hpow := (integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun ω ↦ pow_nonneg (abs_nonneg (X i ω)) m)
        (hh i)).mp hmi
      filter_upwards [hpow] with ω hω
      change X i ω = 0
      change |X i ω| ^ m = 0 at hω
      have ha : |X i ω| = 0 := by
        by_contra hne
        exact (pow_ne_zero m hne) hω
      exact abs_eq_zero.mp ha
    have hall : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 :=
      eventually_countable_forall.mpr hXi
    have hQzero : Q = 0 := by
      calc
        Q = ∫ ω, (0 : ℝ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hall] with ω hω
          simp [hω, hmne]
        _ = 0 := by simp
    rw [hQzero, Real.zero_rpow (ne_of_gt (div_pos zero_lt_one hmpos))]
    positivity
  · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
    let t := (m : ℝ) / R
    obtain ⟨hRpos, ht, hvnorm, hMnorm⟩ := normalization_scales m (by omega) v M hv hMpos
    change 0 < R at hRpos
    change 0 ≤ t at ht
    change t ^ 2 * v ≤ (m : ℝ) at hvnorm
    change t ^ m * M ≤ 1 at hMnorm
    let W : ι → Ω → ℝ := fun i ω ↦ t * X i ω
    have hWind : iIndepFun W μ := by
      simpa only [Function.comp_def] using
        hX.comp (fun i (x : ℝ) ↦ t * x) (fun i ↦ by fun_prop)
    have hWm : ∀ i, AEStronglyMeasurable (W i) μ :=
      fun i ↦ aestronglyMeasurable_const.mul (hXm i)
    have hWh : ∀ i, Integrable (fun ω ↦ |W i ω| ^ m) μ := by
      intro i
      convert (hh i).const_mul (t ^ m) using 1
      ext ω
      change |t * X i ω| ^ m = t ^ m * |X i ω| ^ m
      rw [abs_mul, abs_of_nonneg ht, mul_pow]
    have hWc : ∀ i, ∫ ω, W i ω ∂μ = 0 := by
      intro i
      dsimp [W]
      rw [integral_const_mul, hc i, mul_zero]
    have hWv : (∑ i, ∫ ω, W i ω ^ 2 ∂μ) ≤ (m : ℝ) := by
      calc
        _ = t ^ 2 * v := by
          simp only [W, mul_pow, integral_const_mul]
          rw [← Finset.mul_sum]
        _ ≤ _ := hvnorm
    have hWM : (∑ i, ∫ ω, |W i ω| ^ m ∂μ) ≤ 1 := by
      calc
        _ = t ^ m * M := by
          simp only [W, abs_mul, abs_of_nonneg ht, mul_pow, integral_const_mul]
          rw [← Finset.mul_sum]
        _ ≤ _ := hMnorm
    have hscaled : t ^ m * Q ≤ (m.factorial : ℝ) * Real.exp (m : ℝ) := by
      have hb := normalized_even_moment_bound μ W hWind hWm k hk hWh hWc hWv hWM
      have heq : (∫ ω, |∑ i, W i ω| ^ m ∂μ) = t ^ m * Q := by
        simp only [W, ← Finset.mul_sum, abs_mul, abs_of_nonneg ht, mul_pow, integral_const_mul, Q]
      rw [heq] at hb
      exact hb
    have hfac : (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by
      exact_mod_cast Nat.factorial_le_pow m
    have hscaled' : t ^ m * Q ≤ (m : ℝ) ^ m * Real.exp (m : ℝ) :=
      hscaled.trans (mul_le_mul_of_nonneg_right hfac (Real.exp_nonneg _))
    have htR : t * R = (m : ℝ) := by
      dsimp [t]
      field_simp [ne_of_gt hRpos]
    have hmul : Q * (m : ℝ) ^ m ≤ (Real.exp (m : ℝ) * R ^ m) * (m : ℝ) ^ m := by
      calc
        Q * (m : ℝ) ^ m = (t ^ m * Q) * R ^ m := by
          rw [← htR, mul_pow]
          ring
        _ ≤ ((m : ℝ) ^ m * Real.exp (m : ℝ)) * R ^ m :=
          mul_le_mul_of_nonneg_right hscaled' (pow_nonneg hR m)
        _ = _ := by ring
    have hQbound : Q ≤ Real.exp (m : ℝ) * R ^ m :=
      (mul_le_mul_iff_right₀ (pow_pos hmpos m)).mp (by simpa only [mul_comm] using hmul)
    have hQpow : Q ≤ (Real.exp 1 * R) ^ m := by
      simpa only [mul_pow, Real.exp_one_pow] using hQbound
    have hroot : Q ^ (m : ℝ)⁻¹ ≤ Real.exp 1 * R :=
      (Real.rpow_inv_le_iff_of_pos hQ (mul_nonneg (Real.exp_nonneg _) hR) hmpos).mpr
        (by simpa only [Real.rpow_natCast] using hQpow)
    have hroot' : Q ^ (1 / (m : ℝ)) ≤ Real.exp 1 * R := by
      simpa only [one_div] using hroot
    exact hroot'.trans (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hR)

/-- The supplied highest MemLp assumption discharges all moment and measurability obligations. -/
theorem scalar_even_rosenthal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (k : ℕ) (hk : 1 ≤ k) (hX : iIndepFun X μ)
    (hLp : ∀ i, MemLp (X i) (2 * k : ℕ) μ)
    (hc : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    (∫ ω, |∑ i, X i ω| ^ (2 * k) ∂μ) ^ (1 / ((2 * k : ℕ) : ℝ)) ≤
      3 * (Real.sqrt ((2 * k : ℕ) : ℝ) * Real.sqrt (∑ i, ∫ ω, X i ω ^ 2 ∂μ) +
        ((2 * k : ℕ) : ℝ) * (∑ i, ∫ ω, |X i ω| ^ (2 * k) ∂μ) ^ (1 / ((2 * k : ℕ) : ℝ))) := by
  apply scalar_even_rosenthal_integrable μ X k hk hX (fun i ↦ (hLp i).aestronglyMeasurable)
  · intro i
    simpa only [Real.norm_eq_abs] using (hLp i).integrable_norm_pow'
  · exact hc


/-- The actual highest moment of the finite sum is integrable under the supplied coordinate moments. -/
lemma sum_absolute_even_power_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (k : ℕ) (hX : iIndepFun X μ)
    (hXm : ∀ i, AEStronglyMeasurable (X i) μ)
    (hh : ∀ i, Integrable (fun ω ↦ |X i ω| ^ (2 * k)) μ) :
    Integrable (fun ω ↦ |∑ i, X i ω| ^ (2 * k)) μ := by
  classical
  have hi : Integrable (fun ω ↦
      ∑ l ∈ Finset.finsuppAntidiag Finset.univ (2 * k),
        ∏ i, X i ω ^ l i / ((l i).factorial : ℝ)) μ :=
    integrable_finsetSum _ (fun l hl ↦ mixed_power_integrable μ X hX hXm (2 * k) hh l hl)
  have hx (ω : Ω) : (∑ i, X i ω) ^ (2 * k) / ((2 * k).factorial : ℝ) =
      ∑ l ∈ Finset.finsuppAntidiag Finset.univ (2 * k),
        ∏ i, X i ω ^ l i / ((l i).factorial : ℝ) := by
    rw [sum_power_div_factorial_eq_coeff_prod Finset.univ (fun i ↦ X i ω) (2 * k),
      PowerSeries.coeff_prod]
    simp only [coeff_rescaled_formal_exp]
  have hfac : ((2 * k).factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k)
  have hp : Integrable (fun ω ↦ (∑ i, X i ω) ^ (2 * k)) μ := by
    apply (hi.mul_const ((2 * k).factorial : ℝ)).congr
    exact Filter.Eventually.of_forall fun ω ↦ ((div_eq_iff hfac).mp (hx ω)).symm
  simpa only [pow_abs_two_mul] using hp

/-- The endpoint expressed at an arbitrary positive even order. -/
theorem scalar_even_rosenthal_of_even (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (m : ℕ) (hm : 2 ≤ m) (heven : Even m) (hX : iIndepFun X μ)
    (hLp : ∀ i, MemLp (X i) (m : ℕ) μ) (hc : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    (∫ ω, |∑ i, X i ω| ^ m ∂μ) ^ (1 / (m : ℝ)) ≤
      3 * (Real.sqrt (m : ℝ) * Real.sqrt (∑ i, ∫ ω, X i ω ^ 2 ∂μ) +
        (m : ℝ) * (∑ i, ∫ ω, |X i ω| ^ m ∂μ) ^ (1 / (m : ℝ))) := by
  obtain ⟨k, hk⟩ := heven
  have hmk : m = 2 * k := by omega
  have hkpos : 1 ≤ k := by omega
  rw [hmk] at hLp ⊢
  exact scalar_even_rosenthal μ X k hkpos hX hLp hc

lemma scalar_even_moment_fin_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Fin 0 → Ω → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    (∫ ω, |∑ i, X i ω| ^ (2 * k) ∂μ) ^ (1 / ((2 * k : ℕ) : ℝ)) = 0 := by
  have hmne : 2 * k ≠ 0 := by omega
  have hmpos : 0 < ((2 * k : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * k by omega)
  have hI : (∫ ω, |∑ i, X i ω| ^ (2 * k) ∂μ) = 0 := by simp [hmne]
  rw [hI]
  exact Real.zero_rpow (ne_of_gt (div_pos zero_lt_one hmpos))

#print axioms DGRHS.Concentration.sum_absolute_even_power_integrable
#print axioms DGRHS.Concentration.scalar_even_rosenthal_of_even
#print axioms DGRHS.Concentration.scalar_even_moment_fin_zero

#print axioms DGRHS.Concentration.normalization_scales
#print axioms DGRHS.Concentration.scalar_even_rosenthal_integrable
#print axioms DGRHS.Concentration.scalar_even_rosenthal
end DGRHS.Concentration
