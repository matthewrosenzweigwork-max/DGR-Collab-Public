import DGRHS.Concentration.RealMoments

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
namespace DGRHS.Concentration

lemma l2_integral_absolute_le_norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    (∫ x, |f x| ∂μ) ≤ ‖f‖ := by
  have h1 : MemLp (f : Ω → ℝ) 1 μ := (Lp.memLp f).mono_exponent (by norm_num)
  have he := real_absolute_lp_root μ (f : Ω → ℝ) 1 (by norm_num) (by simpa using h1)
  simp only [ENNReal.ofReal_one,Real.rpow_one,one_div_one] at he
  have hm := ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := (f : Ω → ℝ)) (μ := μ)
      (show (1 : ℝ≥0∞) ≤ 2 by norm_num))
  simpa only [ENNReal.ofReal_one,Real.rpow_one,one_div_one,Lp.norm_def] using he.symm.trans_le hm

lemma kernel_l2_test_abs_bound {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    (μ : Measure Ω) (ν : Measure Ψ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : Ω × Ψ → ℝ) (A : ℝ) (hA : 0 ≤ A) (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν)
    (hAES : AEStronglyMeasurable h (μ.prod ν))
    (hBound : ∀ᵐ p ∂μ.prod ν, |h p| ≤ A) :
    |∫ p, h p * f p.1 * g p.2 ∂μ.prod ν| ≤ A * ‖f‖ * ‖g‖ := by
  have hf : Integrable (fun x ↦ |f x|) μ := by
    simpa only [Real.norm_eq_abs] using (((Lp.memLp f).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable (by norm_num)).norm
  have hg : Integrable (fun y ↦ |g y|) ν := by
    simpa only [Real.norm_eq_abs] using (((Lp.memLp g).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable (by norm_num)).norm
  have hi := kernel_l2_test_integrable μ ν h A f g hAES hBound
  calc
    |∫ p, h p * f p.1 * g p.2 ∂μ.prod ν| ≤
        ∫ p, |h p * f p.1 * g p.2| ∂μ.prod ν := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun p : Ω × Ψ ↦ h p * f p.1 * g p.2) (μ := μ.prod ν)
    _ ≤ ∫ p, A * (|f p.1| * |g p.2|) ∂μ.prod ν := by
      apply integral_mono_ae hi.norm ((hf.mul_prod hg).const_mul A)
      filter_upwards [hBound] with p hp
      change |h p * f p.1 * g p.2| ≤ A * (|f p.1| * |g p.2|)
      simp only [abs_mul]
      nlinarith [mul_nonneg (abs_nonneg (f p.1)) (abs_nonneg (g p.2))]
    _ = A * (∫ x, |f x| ∂μ) * (∫ y, |g y| ∂ν) := by
      rw [integral_const_mul,integral_prod_mul (fun x ↦ |f x|) (fun y ↦ |g y|)]
      ring
    _ ≤ A * ‖f‖ * ‖g‖ := by
      gcongr
      · exact l2_integral_absolute_le_norm μ f
      · exact l2_integral_absolute_le_norm ν g

/-- The actual source test-value set, with the full finite L2 tuple normalization. -/
def kernelDTestValues {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {n q : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    (h : Fin n → Fin q → Ω × Ψ → ℝ) : Set ℝ :=
  {z | ∃ (f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)))
    (g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j))),
    ‖f‖ ≤ 1 ∧ ‖g‖ ≤ 1 ∧ z = kernelL2Bilinear μ ν h f g}

/-- Actual finite source D, not a supplied operator/test-bound premise. -/
def kernelSourceD {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {n q : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    (h : Fin n → Fin q → Ω × Ψ → ℝ) : ℝ := sSup (kernelDTestValues μ ν h)

lemma kernelDTestValues_zero {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ] {n q : ℕ}
    (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ j, SFinite (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) : 0 ∈ kernelDTestValues μ ν h := by
  refine ⟨0,0,by simp,by simp,?_⟩
  unfold kernelL2Bilinear
  symm
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply integral_eq_zero_of_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ i))] with p hp
  change h i j p * (0 : Lp ℝ 2 (μ i)) p.1 * (0 : Lp ℝ 2 (ν j)) p.2 = 0
  change (0 : Lp ℝ 2 (μ i)) p.1 = 0 at hp
  rw [hp,mul_zero,zero_mul]

lemma kernelDTestValues_bddAbove {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A) :
    BddAbove (kernelDTestValues μ ν h) := by
  refine ⟨∑ _i : Fin n, ∑ _j : Fin q, A,?_⟩
  rintro z ⟨f,g,hf,hg,rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have ht := kernel_l2_test_abs_bound (μ i) (ν j) (h i j) A hA (f i) (g j)
    (hAES i j) (hBound i j)
  have hfi := (PiLp.norm_apply_le f i).trans hf
  have hgj := (PiLp.norm_apply_le g j).trans hg
  exact (le_abs_self _).trans (ht.trans (by
    calc
      A * ‖f i‖ * ‖g j‖ ≤ A * 1 * 1 := by gcongr
      _ = A := by ring))

/-- Finiteness, nonnegativity, and all actual source tests follow from the bounded kernel. -/
theorem kernelSourceD_controls {Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A) :
    0 ≤ kernelSourceD μ ν h ∧
      ∀ (f : PiLp 2 (fun i ↦ Lp ℝ 2 (μ i)))
        (g : PiLp 2 (fun j ↦ Lp ℝ 2 (ν j))),
        ‖f‖ ≤ 1 → ‖g‖ ≤ 1 → kernelL2Bilinear μ ν h f g ≤ kernelSourceD μ ν h := by
  have hb := kernelDTestValues_bddAbove μ ν h A hA hAES hBound
  exact ⟨le_csSup hb (kernelDTestValues_zero μ ν h),fun f g hf hg ↦
    le_csSup hb ⟨f,g,hf,hg,rfl⟩⟩

theorem kernel_real_four_scale_sourceD {Ω Ψ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ψ] [MeasurableSpace.CountablyGenerated Ψ]
    {n q : ℕ} (μ : Fin n → Measure Ω) (ν : Fin q → Measure Ψ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)]
    (h : Fin n → Fin q → Ω × Ψ → ℝ) (A B C : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAES : ∀ i j, AEStronglyMeasurable (h i j) ((μ i).prod (ν j)))
    (hBound : ∀ i j, ∀ᵐ p ∂(μ i).prod (ν j), |h i j p| ≤ A)
    (hMeanRight : ∀ i j, ∀ᵐ x ∂μ i, ∫ y, h i j (x,y) ∂ν j = 0)
    (hMeanLeft : ∀ i j, ∀ᵐ y ∂ν j, ∫ x, h i j (x,y) ∂μ i = 0)
    (hRow : ∀ i, ∀ᵐ x ∂μ i, (∑ j, ∫ y, (h i j (x,y))^2 ∂ν j) ≤ B^2)
    (hColumn : ∀ j, ∀ᵐ y ∂ν j, kernelColumnEnergy μ h j y ≤ B^2)
    (hTrace : (∑ i, ∑ j, ∫ p, (h i j p)^2 ∂(μ i).prod (ν j)) ≤ C^2)
    (p : ℝ) (hp : 1 ≤ p) :
    (∫ ω, |kernelDecoupledSum h ω|^p ∂(Measure.pi μ).prod (Measure.pi ν))^(1/p) ≤
      13824*glzRealScale p A B C (kernelSourceD μ ν h) := by
  have hd := kernelSourceD_controls μ ν h A hA hAES hBound
  exact kernel_real_four_scale μ ν h A B C (kernelSourceD μ ν h) hA hB hC hd.1
    hAES hBound hMeanRight hMeanLeft hRow hColumn hTrace hd.2 p hp

#print axioms DGRHS.Concentration.kernel_real_four_scale_sourceD
#check @DGRHS.Concentration.kernel_real_four_scale_sourceD

#print axioms DGRHS.Concentration.kernel_l2_test_abs_bound
#print axioms DGRHS.Concentration.kernelDTestValues_bddAbove
#print axioms DGRHS.Concentration.kernelSourceD_controls
#check @DGRHS.Concentration.kernelSourceD_controls
end DGRHS.Concentration
