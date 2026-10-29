import DGRHS.Concentration.ExponentialTail

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Concentration

lemma essSup_toNNReal_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (a : ℝ) (ha : 0 ≤ a) (hf : ∀ᵐ x ∂μ, |f x| ≤ a) :
    (↑(eLpNormEssSup f μ).toNNReal : ℝ) ≤ a := by
  have hh := eLpNormEssSup_le_of_ae_bound (f := f) (C := a) (hf.mono fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx)
  simpa only [ENNReal.coe_toNNReal_eq_toReal,ENNReal.toReal_ofReal ha] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hh

/-- Coarse iid source parameter bounds use genuine section and product integrals.
The off-diagonal mask keeps repeated sample values and removes only equal labels. -/
theorem iidSourceABC_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : Ω × Ω → ℝ)
    (hSym : ∀ x y, h (y,x) = h (x,y))
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hAbs : ∀ᵐ p ∂μ.prod μ, |h p| ≤ a)
    (hRow : ∀ᵐ x ∂μ, (∫ y, (h (x,y))^2 ∂μ) ≤ b^2)
    (hJoint : (∫ p, (h p)^2 ∂μ.prod μ) ≤ c^2) :
    iidSourceA μ n h ≤ a ∧ iidSourceB μ n h ≤ Real.sqrt (n : ℝ)*b ∧
      iidSourceC μ n h ≤ (n : ℝ)*c := by
  have hMask : ∀ i j, ∀ᵐ p ∂μ.prod μ, |iidOffDiagonalKernel n h i j p| ≤ a := by
    intro i j
    filter_upwards [hAbs] with p hp
    by_cases hij : i ≠ j
    · simpa only [iidOffDiagonalKernel,ite_eq_left hij] using hp
    · simpa only [iidOffDiagonalKernel,ite_eq_right hij,abs_zero] using ha
  have hA : iidSourceA μ n h ≤ a := by
    change (↑(Finset.univ.sup fun ij : Fin n × Fin n ↦ (eLpNormEssSup (iidOffDiagonalKernel n h ij.1 ij.2) (μ.prod μ)).toNNReal) : ℝ) ≤ a
    apply le_trans _ (show (↑a.toNNReal : ℝ) = a from Real.coe_toNNReal a ha).le
    exact_mod_cast Finset.sup_le fun ij _ ↦ by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal a ha]
      exact essSup_toNNReal_bound (μ.prod μ) (iidOffDiagonalKernel n h ij.1 ij.2) a ha (hMask ij.1 ij.2)
  have hRowMask : ∀ i, ∀ᵐ x ∂μ, |kernelRowEnergy (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h) i x| ≤ (n : ℝ)*b^2 := by
    intro i
    filter_upwards [hRow] with x hx
    rw [abs_of_nonneg (Finset.sum_nonneg fun j _ ↦ integral_nonneg fun y ↦ sq_nonneg _)]
    calc
      _ ≤ ∑ _j : Fin n, b^2 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i ≠ j
        · simpa only [iidOffDiagonalKernel,ite_eq_left hij] using hx
        · simp only [iidOffDiagonalKernel,ite_eq_right hij,zero_pow (by norm_num : 2 ≠ 0),integral_zero]
          positivity
      _ = _ := by simp
  have hColMask : ∀ j, ∀ᵐ y ∂μ, |kernelColumnEnergy (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h) j y| ≤ (n : ℝ)*b^2 := by
    intro j
    filter_upwards [hRow] with y hy
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ integral_nonneg fun x ↦ sq_nonneg _)]
    calc
      _ ≤ ∑ _i : Fin n, b^2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hij : i ≠ j
        · simpa only [iidOffDiagonalKernel,ite_eq_left hij,hSym] using hy
        · simp only [iidOffDiagonalKernel,ite_eq_right hij,zero_pow (by norm_num : 2 ≠ 0),integral_zero]
          positivity
      _ = _ := by simp
  have hBsq : (iidSourceB μ n h)^2 ≤ (n : ℝ)*b^2 := by
    rw [iidSourceB,kernelSourceB,Real.sq_sqrt (by positivity)]
    apply max_le
    · apply le_trans _ (show (↑((n : ℝ)*b^2).toNNReal : ℝ) = (n : ℝ)*b^2 from Real.coe_toNNReal _ (by positivity)).le
      exact_mod_cast Finset.sup_le fun i _ ↦ by
        apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ (by positivity)]
        exact essSup_toNNReal_bound μ (kernelRowEnergy (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h) i) _ (by positivity) (hRowMask i)
    · apply le_trans _ (show (↑((n : ℝ)*b^2).toNNReal : ℝ) = (n : ℝ)*b^2 from Real.coe_toNNReal _ (by positivity)).le
      exact_mod_cast Finset.sup_le fun j _ ↦ by
        apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ (by positivity)]
        exact essSup_toNNReal_bound μ (kernelColumnEnergy (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h) j) _ (by positivity) (hColMask j)
  have hCsq : (iidSourceC μ n h)^2 ≤ (n : ℝ)^2*c^2 := by
    rw [iidSourceC,kernelSourceC,Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ integral_nonneg fun p ↦ sq_nonneg _)]
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, c^2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i ≠ j
        · simpa only [iidOffDiagonalKernel,ite_eq_left hij] using hJoint
        · simp only [iidOffDiagonalKernel,ite_eq_right hij,zero_pow (by norm_num : 2 ≠ 0),integral_zero]
          positivity
      _ = _ := by simp;ring
  refine ⟨hA,?_,?_⟩
  · have hs : (iidSourceB μ n h)^2 ≤ (Real.sqrt (n : ℝ)*b)^2 := by
      simpa only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] using hBsq
    have hnon : 0 ≤ iidSourceB μ n h := Real.sqrt_nonneg _
    nlinarith [mul_nonneg (Real.sqrt_nonneg (n : ℝ)) hb]
  · have hs : (iidSourceC μ n h)^2 ≤ ((n : ℝ)*c)^2 := by simpa only [mul_pow] using hCsq
    have hnon : 0 ≤ iidSourceC μ n h := Real.sqrt_nonneg _
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hc]

#print axioms DGRHS.Concentration.iidSourceABC_le
#check @DGRHS.Concentration.iidSourceABC_le
end DGRHS.Concentration
