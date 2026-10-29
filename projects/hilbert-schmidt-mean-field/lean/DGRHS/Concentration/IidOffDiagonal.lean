import DGRHS.Concentration.SourceEssential
import DGRHS.Decoupling.Moment

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Concentration

/-- The diagonal is removed by unequal labels, regardless of repeated sample values. -/
def iidOffDiagonalKernel {Ω : Type*} (n : ℕ) (h : Ω × Ω → ℝ)
    (i j : Fin n) (p : Ω × Ω) : ℝ := if i ≠ j then h p else 0

def iidCoupledSum {Ω : Type*} (n : ℕ) (h : Ω × Ω → ℝ) (ω : Fin n → Ω) : ℝ :=
  DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (ω i,ω j))

abbrev iidSourceA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) :=
  kernelSourceA (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h)
abbrev iidSourceB {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) :=
  kernelSourceB (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h)
abbrev iidSourceC {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) :=
  kernelSourceC (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h)
abbrev iidSourceD {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) :=
  kernelSourceD (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h)

lemma iid_offDiagonal_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ) (hh : MemLp h ∞ (μ.prod μ)) :
    ∀ i j, MemLp (iidOffDiagonalKernel n h i j) ∞ (μ.prod μ) := by
  intro i j
  change MemLp (fun p ↦ if i ≠ j then h p else 0) ∞ (μ.prod μ)
  by_cases hij : i ≠ j
  · simpa only [ite_eq_left hij] using hh
  · simp [hij]

lemma iid_offDiagonal_canonical {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (h : Ω × Ω → ℝ)
    (hr : ∀ᵐ x ∂μ, ∫ y, h (x,y) ∂μ = 0) :
    ∀ i j, ∀ᵐ x ∂μ, ∫ y, iidOffDiagonalKernel n h i j (x,y) ∂μ = 0 := by
  intro i j
  by_cases hij : i ≠ j
  · simpa only [iidOffDiagonalKernel,ite_eq_left hij] using hr
  · simp only [iidOffDiagonalKernel,ite_eq_right hij,integral_zero]
    exact Filter.Eventually.of_forall fun _ ↦ True.intro

lemma iid_source_scales_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : Ω × Ω → ℝ)
    (hh : MemLp h ∞ (μ.prod μ)) :
    0 ≤ iidSourceA μ n h ∧ 0 ≤ iidSourceB μ n h ∧
      0 ≤ iidSourceC μ n h ∧ 0 ≤ iidSourceD μ n h := by
  have hp := iid_offDiagonal_memLp μ n h hh
  obtain ⟨ha,hb,hc,hbound,_,_,_⟩ := kernelSourceABC_controls
    (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ) (iidOffDiagonalKernel n h) hp
  have hd := kernelSourceD_controls (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ)
    (iidOffDiagonalKernel n h) (iidSourceA μ n h) ha (fun i j ↦ (hp i j).aestronglyMeasurable) hbound
  exact ⟨ha,hb,hc,hd.1⟩

lemma iid_coupled_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (h : Ω × Ω → ℝ)
    (hh : MemLp h ∞ (μ.prod μ)) (p : ℝ≥0∞) :
    MemLp (iidCoupledSum n h) p (Measure.pi (fun _ : Fin n ↦ μ)) := by
  unfold iidCoupledSum DGRHS.Decoupling.offDiagonalSum
  apply memLp_finsetSum
  intro i _
  apply memLp_finsetSum
  intro j _
  by_cases hij : i ≠ j
  · simp only [ite_eq_left hij]
    exact (hh.mono_exponent le_top).comp_measurePreserving
      (DGRHS.Decoupling.pair_eval_measurePreserving μ i j hij)
  · simp only [ite_eq_right hij]
    simp

/-- Actual iid symmetric off-diagonal even moments, with genuine factor-four decoupling
and all four scales constructed from the masked kernel. N=0/1 and zero scales are included. -/
theorem iid_even_four_scale_power {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (h : Ω × Ω → ℝ) (hm : Measurable h)
    (hh : MemLp h ∞ (μ.prod μ)) (hsymm : ∀ x y, h (x,y) = h (y,x))
    (hr : ∀ᵐ x ∂μ, ∫ y, h (x,y) ∂μ = 0) (k : ℕ) (hk : 1 ≤ k) :
    (∫ ω, |iidCoupledSum n h ω|^(2*k) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤
      (3456*glzScale (2*k) (iidSourceA μ n h) (iidSourceB μ n h)
        (iidSourceC μ n h) (iidSourceD μ n h))^(2*k) := by
  have hl := DGRHS.Decoupling.left_canonical_of_symmetric μ h hsymm hr
  have hml : ∀ i j, ∀ᵐ y ∂μ, ∫ x, iidOffDiagonalKernel n h i j (x,y) ∂μ = 0 := by
    intro i j
    by_cases hij : i ≠ j
    · simpa only [iidOffDiagonalKernel,ite_eq_left hij] using hl
    · simp only [iidOffDiagonalKernel,ite_eq_right hij,integral_zero]
      exact Filter.Eventually.of_forall fun _ ↦ True.intro
  have hd := DGRHS.Decoupling.scalar_even_moment_decoupling_symmetric μ n h hm hsymm k hk
    (hh.mono_exponent le_top) hr
  have he := kernel_even_four_scale_power_actual (fun _ : Fin n ↦ μ) (fun _ : Fin n ↦ μ)
    (iidOffDiagonalKernel n h) (iid_offDiagonal_memLp μ n h hh)
    (iid_offDiagonal_canonical μ n h hr) hml k hk
  have hsum : kernelDecoupledSum (iidOffDiagonalKernel n h) =
      (fun p : (Fin n → Ω) × (Fin n → Ω) ↦
        DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (p.1 i,p.2 j))) := by
    funext p
    unfold kernelDecoupledSum kernelColumnSum iidOffDiagonalKernel DGRHS.Decoupling.offDiagonalSum
    exact Finset.sum_comm
  rw [hsum] at he
  change (∫ ω, |iidCoupledSum n h ω|^(2*k) ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤ _ at hd
  have ht := hd.trans (mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 4^(2*k)))
  convert ht using 1
  rw [← mul_pow]
  congr 1
  ring

lemma iid_even_four_scale_root {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (h : Ω × Ω → ℝ) (hm : Measurable h)
    (hh : MemLp h ∞ (μ.prod μ)) (hsymm : ∀ x y, h (x,y) = h (y,x))
    (hr : ∀ᵐ x ∂μ, ∫ y, h (x,y) ∂μ = 0) (k : ℕ) (hk : 1 ≤ k) :
    (∫ ω, |iidCoupledSum n h ω|^(2*k) ∂Measure.pi (fun _ : Fin n ↦ μ))^(1/((2*k : ℕ) : ℝ)) ≤
      3456*glzScale (2*k) (iidSourceA μ n h) (iidSourceB μ n h)
        (iidSourceC μ n h) (iidSourceD μ n h) := by
  have ht := iid_even_four_scale_power μ n h hm hh hsymm hr k hk
  obtain ⟨ha,hb,hc,hd⟩ := iid_source_scales_nonneg μ n h hh
  have hn : 0 ≤ ∫ ω, |iidCoupledSum n h ω|^(2*k) ∂Measure.pi (fun _ : Fin n ↦ μ) :=
    integral_nonneg fun _ ↦ by positivity
  have hp : 0 < ((2*k : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*k by omega)
  have hR : 0 ≤ 3456*glzScale (2*k) (iidSourceA μ n h) (iidSourceB μ n h)
      (iidSourceC μ n h) (iidSourceD μ n h) := by unfold glzScale; positivity
  have hhroot := (Real.rpow_inv_le_iff_of_pos hn hR hp).mpr
    (by simpa only [Real.rpow_natCast] using ht)
  simpa only [one_div] using hhroot

/-- Every real p>=1 on the actual iid law, without a supplied tail/moment conclusion. -/
theorem iid_real_four_scale {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (h : Ω × Ω → ℝ) (hm : Measurable h)
    (hh : MemLp h ∞ (μ.prod μ)) (hsymm : ∀ x y, h (x,y) = h (y,x))
    (hr : ∀ᵐ x ∂μ, ∫ y, h (x,y) ∂μ = 0) (p : ℝ) (hp : 1 ≤ p) :
    (∫ ω, |iidCoupledSum n h ω|^p ∂Measure.pi (fun _ : Fin n ↦ μ))^(1/p) ≤
      55296*glzRealScale p (iidSourceA μ n h) (iidSourceB μ n h)
        (iidSourceC μ n h) (iidSourceD μ n h) := by
  have hp0 : 0 < p := by linarith
  let m := 2*Nat.ceil p
  have hpm : p ≤ (m : ℝ) := by
    have ht := Nat.le_ceil p
    dsimp [m]
    push_cast
    linarith [show (0 : ℝ) ≤ (Nat.ceil p : ℝ) from Nat.cast_nonneg _]
  have hm0 : 0 < (m : ℝ) := hp0.trans_le hpm
  have hmono := real_absolute_moment_root_mono (Measure.pi (fun _ : Fin n ↦ μ))
    (iidCoupledSum n h) p (m : ℝ) hp0 hm0 hpm
    (iid_coupled_memLp μ n h hh _) (iid_coupled_memLp μ n h hh _)
  simp only [Real.rpow_natCast] at hmono
  have hk : 1 ≤ Nat.ceil p := Nat.one_le_ceil_iff.mpr hp0
  have he := iid_even_four_scale_root μ n h hm hh hsymm hr (Nat.ceil p) hk
  obtain ⟨ha,hb,hc,hd⟩ := iid_source_scales_nonneg μ n h hh
  have hs := mul_le_mul_of_nonneg_left (glz_scale_even_ceil_le p
    (iidSourceA μ n h) (iidSourceB μ n h) (iidSourceC μ n h) (iidSourceD μ n h) hp ha hb hc hd)
      (by norm_num : (0 : ℝ) ≤ 3456)
  exact (hmono.trans he).trans (by nlinarith [hs])

/-- True iid concentration at every real parameter u>=1, including all zero scales. -/
theorem iid_four_scale_parameter_tail {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace.CountablyGenerated Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (h : Ω × Ω → ℝ) (hm : Measurable h)
    (hh : MemLp h ∞ (μ.prod μ)) (hsymm : ∀ x y, h (x,y) = h (y,x))
    (hr : ∀ᵐ x ∂μ, ∫ y, h (x,y) ∂μ = 0) (u t : ℝ) (hu : 1 ≤ u) (ht : 0 < t)
    (hThreshold : (55296*Real.exp 1)*glzRealScale u
      (iidSourceA μ n h) (iidSourceB μ n h) (iidSourceC μ n h) (iidSourceD μ n h) ≤ t) :
    (Measure.pi (fun _ : Fin n ↦ μ)).real {ω | t ≤ |iidCoupledSum n h ω|} ≤ Real.exp (-u) := by
  have hk : 1 ≤ Nat.ceil u := Nat.one_le_ceil_iff.mpr (by linarith)
  have hmu : u ≤ ((2*Nat.ceil u : ℕ) : ℝ) := by
    have ht := Nat.le_ceil u
    push_cast
    linarith [show (0 : ℝ) ≤ (Nat.ceil u : ℝ) from Nat.cast_nonneg _]
  obtain ⟨ha,hb,hc,hd⟩ := iid_source_scales_nonneg μ n h hh
  have hs := glz_scale_even_ceil_le u (iidSourceA μ n h) (iidSourceB μ n h)
    (iidSourceC μ n h) (iidSourceD μ n h) hu ha hb hc hd
  have hT : Real.exp 1*(3456*glzScale (2*Nat.ceil u) (iidSourceA μ n h) (iidSourceB μ n h)
      (iidSourceC μ n h) (iidSourceD μ n h)) ≤ t := by
    calc
      _ ≤ Real.exp 1*(3456*(16*glzRealScale u (iidSourceA μ n h) (iidSourceB μ n h)
        (iidSourceC μ n h) (iidSourceD μ n h))) := by gcongr
      _ = (55296*Real.exp 1)*glzRealScale u (iidSourceA μ n h) (iidSourceB μ n h)
        (iidSourceC μ n h) (iidSourceD μ n h) := by ring
      _ ≤ t := hThreshold
  have hi : Integrable (fun ω ↦ |iidCoupledSum n h ω|^(2*Nat.ceil u))
      (Measure.pi (fun _ : Fin n ↦ μ)) := by
    simpa only [Real.norm_eq_abs] using (iid_coupled_memLp μ n h hh
      (2*Nat.ceil u : ℕ)).integrable_norm_pow'
  have hbnd := absolute_moment_exponential_tail (Measure.pi (fun _ : Fin n ↦ μ))
    (iidCoupledSum n h) (2*Nat.ceil u) hi
    (3456*glzScale (2*Nat.ceil u) (iidSourceA μ n h) (iidSourceB μ n h)
      (iidSourceC μ n h) (iidSourceD μ n h)) t (by unfold glzScale; positivity) ht
      (iid_even_four_scale_power μ n h hm hh hsymm hr (Nat.ceil u) hk) hT
  exact hbnd.trans (Real.exp_monotone (neg_le_neg hmu))

lemma iid_coupled_sum_zero {Ω : Type*} (h : Ω × Ω → ℝ) (ω : Fin 0 → Ω) :
    iidCoupledSum 0 h ω = 0 := DGRHS.Decoupling.offDiagonalSum_subsingleton _
lemma iid_coupled_sum_one {Ω : Type*} (h : Ω × Ω → ℝ) (ω : Fin 1 → Ω) :
    iidCoupledSum 1 h ω = 0 := DGRHS.Decoupling.offDiagonalSum_subsingleton _

#print axioms DGRHS.Concentration.iid_even_four_scale_power
#print axioms DGRHS.Concentration.iid_real_four_scale
#print axioms DGRHS.Concentration.iid_four_scale_parameter_tail
#print axioms DGRHS.Concentration.iid_coupled_sum_one
#check @DGRHS.Concentration.iid_real_four_scale
#check @DGRHS.Concentration.iid_four_scale_parameter_tail
end DGRHS.Concentration
