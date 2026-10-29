import DGRHS.Concentration.IidControls

/-! Remark 3.2 (`rem:Ustattail`, TeX lines 1084-1095 of
`source/extracted/DGR_PFunc_Current_20260902_145019_UTC.tex`) in the owner-approved corrected
form (owner decision 1.2 of `OWNER_DECISIONS_20261006.md`: "Remark 3.2 as an inequality with
equality for `N >= 2`").

For the iid single symmetric kernel `h`, with array `h_{ij} = h` for `i ≠ j` and `h_{ii} = 0`
(the declarations `iidSourceA/B/C/D`, i.e. the actual source quantities `A, B, C, D` of
Proposition 3.1 built from the masked array `iidOffDiagonalKernel n h`), this module proves:

* `A`: `A = 1_{N ≥ 2} ‖h‖_{L∞(μ⊗μ)}` (exact), hence `A ≤ ‖h‖_{L∞}` for all `N`, with equality
  exactly when `N ≥ 2` (and `‖h‖_∞ > 0`).  The printed equality fails at `N = 1` because the
  array is identically zero (witness `DGRHS.Original.sourceRemark32_equality_fails_at_one`).
* `B²`: `B² = (N-1) ‖h‖²_{L∞L²(μ)}` (exact, all `N`, with the *essential* supremum in `x`), hence
  `B² ≤ (N-1) · sup_x ∫ h(x,y)² dμ(y)` for the printed pointwise supremum.
* `C²`: `C² = N(N-1) ‖h‖²_{L²(μ⊗μ)}` (exact, all `N`).
* `D`: `D ≤ N ‖T_h‖_op` (as printed), and the sharper `D ≤ (N-1) ‖T_h‖_op`.

The printed right-hand sides with `N` (instead of `N-1` in `A`'s indicator) are all upper bounds
(`(N-1) ≤ N`), and these upper bounds are exactly the coarse forms consumed by
`DGRHS.Concentration.iid_master_tail` (see `iidSourceABC_le` and `iidSourceD_le_integralOperator`).
Norm conventions: `‖h‖_{L∞}` is the essential supremum for `μ⊗μ`; `‖h‖²_{L²(μ⊗μ)} = ∫ h² d(μ⊗μ)`. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Concentration

/-- Squared `L²(μ)`-norm of the row `h(x,·)`. -/
def remark32RowSq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : Ω × Ω → ℝ) (x : Ω) : ℝ :=
  ∫ y, (h (x,y))^2 ∂μ

/-- `‖h‖_{L∞(μ⊗μ)}` as the essential supremum (real part). -/
def remark32LinftyNorm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : Ω × Ω → ℝ) : ℝ :=
  (eLpNormEssSup h (μ.prod μ)).toReal

/-- `‖h‖²_{L∞L²(μ)}` with the essential supremum in `x` of the row energy. -/
def remark32LinftyL2Sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : Ω × Ω → ℝ) : ℝ :=
  (eLpNormEssSup (remark32RowSq μ h) μ).toReal

/-- `‖h‖²_{L∞L²(μ)}` with the printed pointwise supremum `sup_x ∫ h(x,y)² dμ(y)`, in `ℝ≥0∞`. -/
def remark32LinftyL2SqPointwise {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (h : Ω × Ω → ℝ) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal (remark32RowSq μ h x)

/-- `‖h‖²_{L²(μ⊗μ)} = ∫ h² d(μ⊗μ)`. -/
def remark32L2Sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : Ω × Ω → ℝ) : ℝ :=
  ∫ p, (h p)^2 ∂μ.prod μ

lemma remark32_card_filter_ne (n : ℕ) (i : Fin n) :
    ((Finset.univ.filter fun j : Fin n ↦ i ≠ j).card : ℝ) = ((n - 1 : ℕ) : ℝ) := by
  rw [Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]

lemma remark32_sum_ne {n : ℕ} (i : Fin n) (t : ℝ) :
    (∑ j : Fin n, if i ≠ j then t else 0) = ((n - 1 : ℕ) : ℝ) * t := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    remark32_card_filter_ne]

lemma remark32_sum_ne' {n : ℕ} (j : Fin n) (t : ℝ) :
    (∑ i : Fin n, if i ≠ j then t else 0) = ((n - 1 : ℕ) : ℝ) * t := by
  have : (∑ i : Fin n, if i ≠ j then t else 0) = ∑ i : Fin n, if j ≠ i then t else 0 :=
    Finset.sum_congr rfl fun i _ ↦ by simp only [ne_comm]
  rw [this, remark32_sum_ne]

lemma remark32_essSup_const_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (c : ℝ) (hc : 0 ≤ c) (f : Ω → ℝ) :
    (↑(eLpNormEssSup (fun x ↦ c * f x) μ).toNNReal : ℝ) = c * (eLpNormEssSup f μ).toReal := by
  have h1 : eLpNormEssSup (fun x ↦ c * f x) μ = ‖c‖ₑ * eLpNormEssSup f μ :=
    eLpNormEssSup_const_smul (μ := μ) c f
  rw [h1, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_mul, toReal_enorm,
    Real.norm_eq_abs, abs_of_nonneg hc]

/-- `A`: exact value of the first scale. -/
theorem remark32_A_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) :
    iidSourceA μ n h = if 2 ≤ n then remark32LinftyNorm μ h else 0 := by
  unfold iidSourceA kernelSourceA remark32LinftyNorm
  by_cases hn : 2 ≤ n
  · simp only [hn, ↓reduceIte]
    have hle : (Finset.univ.sup fun ij : Fin n × Fin n ↦
        (eLpNormEssSup (iidOffDiagonalKernel n h ij.1 ij.2) (μ.prod μ)).toNNReal) =
        (eLpNormEssSup h (μ.prod μ)).toNNReal := by
      apply le_antisymm
      · apply Finset.sup_le
        intro ij _
        by_cases hij : ij.1 ≠ ij.2
        · have : iidOffDiagonalKernel n h ij.1 ij.2 = h := by
            funext p; simp [iidOffDiagonalKernel, hij]
          rw [this]
        · have : iidOffDiagonalKernel n h ij.1 ij.2 = 0 := by
            funext p; simp [iidOffDiagonalKernel, hij]
          rw [this, eLpNormEssSup_zero]; simp
      · have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
          intro hh; have := congrArg Fin.val hh; simp at this
        have : iidOffDiagonalKernel n h ⟨0, by omega⟩ ⟨1, by omega⟩ = h := by
          funext p; simp [iidOffDiagonalKernel, h01]
        have hs := Finset.le_sup (f := fun ij : Fin n × Fin n ↦
          (eLpNormEssSup (iidOffDiagonalKernel n h ij.1 ij.2) (μ.prod μ)).toNNReal)
          (Finset.mem_univ ((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)))
        simpa only [this] using hs
    rw [hle, ENNReal.coe_toNNReal_eq_toReal]
  · simp only [hn, ↓reduceIte]
    have hz : (Finset.univ.sup fun ij : Fin n × Fin n ↦
        (eLpNormEssSup (iidOffDiagonalKernel n h ij.1 ij.2) (μ.prod μ)).toNNReal) = 0 := by
      apply le_antisymm _ (by positivity)
      apply Finset.sup_le
      intro ij _
      have hij : ¬ (ij.1 ≠ ij.2) := by
        intro hne; apply hne
        apply Fin.ext
        have := ij.1.isLt; have := ij.2.isLt
        omega
      have : iidOffDiagonalKernel n h ij.1 ij.2 = 0 := by
        funext p; simp [iidOffDiagonalKernel, hij]
      rw [this, eLpNormEssSup_zero]; simp
    rw [hz]; simp

theorem remark32_A_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) :
    iidSourceA μ n h ≤ remark32LinftyNorm μ h := by
  rw [remark32_A_eq]
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

theorem remark32_A_eq_of_two_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) (hn : 2 ≤ n) :
    iidSourceA μ n h = remark32LinftyNorm μ h := by
  rw [remark32_A_eq]; simp only [hn, ↓reduceIte]

theorem remark32_A_eq_zero_of_lt_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) (hn : n < 2) :
    iidSourceA μ n h = 0 := by
  rw [remark32_A_eq]; simp only [show ¬ 2 ≤ n by omega, ↓reduceIte]

/-- `B²`: exact value of the second scale for symmetric `h`. -/
theorem remark32_B_sq_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) (hSym : ∀ x y, h (x,y) = h (y,x)) :
    (iidSourceB μ n h)^2 = ((n - 1 : ℕ) : ℝ) * remark32LinftyL2Sq μ h := by
  have hc : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hRow : ∀ i : Fin n, kernelRowEnergy (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h) i =
      fun x ↦ ((n - 1 : ℕ) : ℝ) * remark32RowSq μ h x := by
    intro i; funext x
    unfold kernelRowEnergy remark32RowSq iidOffDiagonalKernel
    have : ∀ j : Fin n, (∫ y, ((if i ≠ j then h (x,y) else 0))^2 ∂μ) =
        if i ≠ j then ∫ y, (h (x,y))^2 ∂μ else 0 := by
      intro j
      by_cases hij : i ≠ j <;> simp [hij]
    rw [Finset.sum_congr rfl fun j _ ↦ this j, remark32_sum_ne]
  have hCol : ∀ j : Fin n, kernelColumnEnergy (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h) j =
      fun y ↦ ((n - 1 : ℕ) : ℝ) * remark32RowSq μ h y := by
    intro j; funext y
    unfold kernelColumnEnergy remark32RowSq iidOffDiagonalKernel
    have : ∀ i : Fin n, (∫ x, ((if i ≠ j then h (x,y) else 0))^2 ∂μ) =
        if i ≠ j then ∫ x, (h (y,x))^2 ∂μ else 0 := by
      intro i
      by_cases hij : i ≠ j
      · simp only [hij, ne_eq, not_false_eq_true, ↓reduceIte]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by simp only [hSym x y])
      · simp [hij]
    rw [Finset.sum_congr rfl fun i _ ↦ this i, remark32_sum_ne']
  unfold iidSourceB kernelSourceB remark32LinftyL2Sq
  rw [Real.sq_sqrt (le_max_of_le_left (NNReal.coe_nonneg _))]
  set E := (eLpNormEssSup (remark32RowSq μ h) μ).toReal with hE
  have hterm : ∀ i : Fin n, (eLpNormEssSup (kernelRowEnergy (fun _ : Fin n ↦ μ)
      (iidOffDiagonalKernel n h) i) μ).toNNReal = (((n - 1 : ℕ) : ℝ) * E).toNNReal := by
    intro i
    rw [hRow i]
    have := remark32_essSup_const_mul μ _ hc (remark32RowSq μ h)
    rw [← hE] at this
    rw [← this, Real.toNNReal_coe]
  have htermC : ∀ j : Fin n, (eLpNormEssSup (kernelColumnEnergy (fun _ : Fin n ↦ μ)
      (iidOffDiagonalKernel n h) j) μ).toNNReal = (((n - 1 : ℕ) : ℝ) * E).toNNReal := by
    intro j
    rw [hCol j]
    have := remark32_essSup_const_mul μ _ hc (remark32RowSq μ h)
    rw [← hE] at this
    rw [← this, Real.toNNReal_coe]
  have hEnn : 0 ≤ ((n - 1 : ℕ) : ℝ) * E := mul_nonneg hc ENNReal.toReal_nonneg
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · have : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
    simp only [Finset.sup_congr rfl fun i _ ↦ hterm i, Finset.sup_congr rfl fun j _ ↦ htermC j,
      Finset.sup_const Finset.univ_nonempty, Real.coe_toNNReal _ hEnn, max_self]

/-- Printed pointwise-supremum form of `B²`: an inequality. -/
theorem remark32_B_sq_le_pointwise {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) (hSym : ∀ x y, h (x,y) = h (y,x)) :
    ENNReal.ofReal ((iidSourceB μ n h)^2) ≤
      ((n - 1 : ℕ) : ℝ≥0∞) * remark32LinftyL2SqPointwise μ h := by
  rw [remark32_B_sq_eq μ n h hSym, ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_natCast]
  apply mul_le_mul_right
  refine (ENNReal.ofReal_toReal_le).trans ?_
  apply eLpNormEssSup_le_of_ae_enorm_bound
  refine Filter.Eventually.of_forall fun x ↦ ?_
  have hnn : 0 ≤ remark32RowSq μ h x := integral_nonneg fun y ↦ sq_nonneg _
  rw [Real.enorm_of_nonneg hnn]
  exact le_iSup (fun x ↦ ENNReal.ofReal (remark32RowSq μ h x)) x

/-- `C²`: exact value of the third scale. -/
theorem remark32_C_sq_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) :
    (iidSourceC μ n h)^2 = ((n * (n - 1) : ℕ) : ℝ) * remark32L2Sq μ h := by
  unfold iidSourceC kernelSourceC remark32L2Sq
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    integral_nonneg fun p ↦ sq_nonneg _)]
  have : ∀ i j : Fin n, (∫ p, (iidOffDiagonalKernel n h i j p)^2 ∂μ.prod μ) =
      if i ≠ j then ∫ p, (h p)^2 ∂μ.prod μ else 0 := by
    intro i j
    by_cases hij : i ≠ j <;> simp [iidOffDiagonalKernel, hij]
  rw [Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ this i j]
  rw [Finset.sum_congr rfl fun i _ ↦ remark32_sum_ne i _]
  rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- `D`: the printed bound. -/
theorem remark32_D_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : Ω × Ω → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) :
    iidSourceD μ n h ≤ (n : ℝ) * ‖DGRHS.Kernel.integralOperator h hh‖ :=
  iidSourceD_le_integralOperator μ n h hh

/-- Sharper `N`-indexing for `D`: the bilinear form on the masked array is at most `(N-1)‖T_h‖`. -/
lemma remark32_bilinear_pred_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : Ω × Ω → ℝ)
    (hh : MemLp h 2 (μ.prod μ))
    (f g : PiLp 2 (fun _ : Fin n ↦ Lp ℝ 2 μ)) (hf : ‖f‖ ≤ 1) (hg : ‖g‖ ≤ 1) :
    kernelL2Bilinear (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ)
      (iidOffDiagonalKernel n h) f g ≤ ((n - 1 : ℕ) : ℝ) * ‖DGRHS.Kernel.integralOperator h hh‖ := by
  let T := DGRHS.Kernel.integralOperator h hh
  have hPair : ∀ i j : Fin n, (∫ p, iidOffDiagonalKernel n h i j p * f i p.1 * g j p.2 ∂μ.prod μ) ≤
      (if i ≠ j then ‖T‖/2*‖f i‖^2 else 0) + (if i ≠ j then ‖T‖/2*‖g j‖^2 else 0) := by
    intro i j
    by_cases hij : i ≠ j
    · have hmask : iidOffDiagonalKernel n h i j = h := by
        funext p; simp [iidOffDiagonalKernel, hij]
      rw [hmask]
      simp only [hij, ne_eq, not_false_eq_true, ↓reduceIte]
      have h1 : (∫ p, h p * f i p.1 * g j p.2 ∂μ.prod μ) ≤ ‖T‖*‖f i‖*‖g j‖ := by
        rw [← DGRHS.Kernel.inner_integralOperator h hh (g j) (f i)]
        exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (by
          calc
            ‖T (g j)‖*‖f i‖ ≤ (‖T‖*‖g j‖)*‖f i‖ :=
              mul_le_mul_of_nonneg_right (T.le_opNorm (g j)) (norm_nonneg _)
            _ = ‖T‖*‖f i‖*‖g j‖ := by ring))
      nlinarith [mul_nonneg (norm_nonneg T) (sq_nonneg (‖f i‖ - ‖g j‖))]
    · have hmask : iidOffDiagonalKernel n h i j = 0 := by
        funext p; simp [iidOffDiagonalKernel, hij]
      rw [hmask]
      simp [hij]
  have hsum : kernelL2Bilinear (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ)
      (iidOffDiagonalKernel n h) f g ≤ ∑ i : Fin n, ∑ j : Fin n,
        ((if i ≠ j then ‖T‖/2*‖f i‖^2 else 0) + (if i ≠ j then ‖T‖/2*‖g j‖^2 else 0)) :=
    Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hPair i j
  have hf2 : ‖f‖^2 = ∑ i, ‖f i‖^2 := by rw [PiLp.norm_sq_eq_of_L2]
  have hg2 : ‖g‖^2 = ∑ j, ‖g j‖^2 := by rw [PiLp.norm_sq_eq_of_L2]
  have hfs : ‖f‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hf
  have hgs : ‖g‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg _) hg
  have e1 : ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖T‖/2*‖f i‖^2 else 0) =
      ((n - 1 : ℕ) : ℝ) * (‖T‖/2) * ‖f‖^2 := by
    rw [Finset.sum_congr rfl fun i _ ↦ remark32_sum_ne i _, hf2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have e2 : ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖T‖/2*‖g j‖^2 else 0) =
      ((n - 1 : ℕ) : ℝ) * (‖T‖/2) * ‖g‖^2 := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun j _ ↦ remark32_sum_ne' j _, hg2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hK : 0 ≤ ((n - 1 : ℕ) : ℝ) * (‖T‖/2) := by positivity
  simp only [Finset.sum_add_distrib] at hsum
  rw [e1, e2] at hsum
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hfs hgs) hK]

theorem remark32_D_le_pred {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : Ω × Ω → ℝ)
    (hh : MemLp h 2 (μ.prod μ)) :
    iidSourceD μ n h ≤ ((n - 1 : ℕ) : ℝ) * ‖DGRHS.Kernel.integralOperator h hh‖ := by
  apply csSup_le ⟨0, kernelDTestValues_zero (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ)
    (iidOffDiagonalKernel n h)⟩
  rintro z ⟨f, g, hf, hg, rfl⟩
  exact remark32_bilinear_pred_bound μ n h hh f g hf hg

/-- Remark 3.2 in the corrected form, all four quantities of Proposition 3.1 for the iid single
symmetric kernel.  `((n - 1 : ℕ) : ℝ) = N - 1` for `N ≥ 1`. -/
theorem remark32_inequality_form {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : Ω × Ω → ℝ)
    (hh : MemLp h ∞ (μ.prod μ)) (hSym : ∀ x y, h (x,y) = h (y,x)) :
    (iidSourceA μ n h ≤ remark32LinftyNorm μ h ∧
      (2 ≤ n → iidSourceA μ n h = remark32LinftyNorm μ h)) ∧
    ((iidSourceB μ n h)^2 = ((n - 1 : ℕ) : ℝ) * remark32LinftyL2Sq μ h ∧
      ENNReal.ofReal ((iidSourceB μ n h)^2) ≤
        ((n - 1 : ℕ) : ℝ≥0∞) * remark32LinftyL2SqPointwise μ h) ∧
    (iidSourceC μ n h)^2 = ((n * (n - 1) : ℕ) : ℝ) * remark32L2Sq μ h ∧
    (iidSourceD μ n h ≤ ((n - 1 : ℕ) : ℝ) *
        ‖DGRHS.Kernel.integralOperator h (hh.mono_exponent (show (2 : ℝ≥0∞) ≤ ∞ from le_top))‖ ∧
      iidSourceD μ n h ≤ (n : ℝ) *
        ‖DGRHS.Kernel.integralOperator h (hh.mono_exponent (show (2 : ℝ≥0∞) ≤ ∞ from le_top))‖) :=
  ⟨⟨remark32_A_le μ n h, remark32_A_eq_of_two_le μ n h⟩,
    ⟨remark32_B_sq_eq μ n h hSym, remark32_B_sq_le_pointwise μ n h hSym⟩,
    remark32_C_sq_eq μ n h,
    remark32_D_le_pred μ n h _, remark32_D_le μ n h _⟩

/-- The coarse forms consumed by `iid_master_tail` (via `iidSourceABC_le` and
`iidSourceD_le_integralOperator`) are implied by the exact identities, at the optimal parameters
`a = ‖h‖_∞`, `b = ‖h‖_{L∞L²}`, `c = ‖h‖_{L²(μ⊗μ)}`. -/
theorem remark32_consumed_forms {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : Ω × Ω → ℝ)
    (hh : MemLp h ∞ (μ.prod μ)) (hSym : ∀ x y, h (x,y) = h (y,x)) :
    iidSourceA μ n h ≤ remark32LinftyNorm μ h ∧
      iidSourceB μ n h ≤ Real.sqrt (n : ℝ) * Real.sqrt (remark32LinftyL2Sq μ h) ∧
      iidSourceC μ n h ≤ (n : ℝ) * Real.sqrt (remark32L2Sq μ h) ∧
      iidSourceD μ n h ≤ (n : ℝ) *
        ‖DGRHS.Kernel.integralOperator h (hh.mono_exponent (show (2 : ℝ≥0∞) ≤ ∞ from le_top))‖ := by
  have hE : 0 ≤ remark32LinftyL2Sq μ h := ENNReal.toReal_nonneg
  have hI : 0 ≤ remark32L2Sq μ h := integral_nonneg fun p ↦ sq_nonneg _
  have hn1 : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n 1
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  refine ⟨remark32_A_le μ n h, ?_, ?_, remark32_D_le μ n h _⟩
  · have hB : 0 ≤ iidSourceB μ n h := Real.sqrt_nonneg _
    have hsq : (iidSourceB μ n h)^2 ≤ ((n : ℝ) * remark32LinftyL2Sq μ h) := by
      rw [remark32_B_sq_eq μ n h hSym]
      exact mul_le_mul_of_nonneg_right hn1 hE
    calc iidSourceB μ n h = Real.sqrt ((iidSourceB μ n h)^2) := (Real.sqrt_sq hB).symm
      _ ≤ Real.sqrt ((n : ℝ) * remark32LinftyL2Sq μ h) := Real.sqrt_le_sqrt hsq
      _ = _ := Real.sqrt_mul hn0 _
  · have hC : 0 ≤ iidSourceC μ n h := Real.sqrt_nonneg _
    have hsq : (iidSourceC μ n h)^2 ≤ ((n : ℝ))^2 * remark32L2Sq μ h := by
      rw [remark32_C_sq_eq]
      have : ((n * (n - 1) : ℕ) : ℝ) ≤ ((n : ℝ))^2 := by
        push_cast [Nat.cast_mul]
        have : (((n - 1 : ℕ)) : ℝ) ≤ n := hn1
        nlinarith
      exact mul_le_mul_of_nonneg_right this hI
    calc iidSourceC μ n h = Real.sqrt ((iidSourceC μ n h)^2) := (Real.sqrt_sq hC).symm
      _ ≤ Real.sqrt (((n : ℝ))^2 * remark32L2Sq μ h) := Real.sqrt_le_sqrt hsq
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn0]

#print axioms DGRHS.Concentration.remark32_A_eq
#print axioms DGRHS.Concentration.remark32_B_sq_eq
#print axioms DGRHS.Concentration.remark32_B_sq_le_pointwise
#print axioms DGRHS.Concentration.remark32_C_sq_eq
#print axioms DGRHS.Concentration.remark32_D_le
#print axioms DGRHS.Concentration.remark32_D_le_pred
#print axioms DGRHS.Concentration.remark32_inequality_form
#print axioms DGRHS.Concentration.remark32_consumed_forms
end DGRHS.Concentration
