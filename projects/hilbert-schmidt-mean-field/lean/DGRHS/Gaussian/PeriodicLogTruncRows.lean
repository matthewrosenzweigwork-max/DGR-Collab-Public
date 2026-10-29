import DGRHS.Gaussian.PeriodicLogTruncJensen
import DGRHS.Gaussian.PeriodicGreenExponentialIntegrability
import DGRHS.Gaussian.PeriodicGreenGlobalLower
import DGRHS.Gaussian.PeriodicPositiveMellinNearField
import DGRHS.Attractive.CenteredRowFactorial
import DGRHS.Attractive.RowMoments

/-!
Packet P11b, unit 2 (clause 2, step 2): uniform factorial row moments of the Hoeffding-centered
heat-shifted periodic LOG kernels `g_τ` on the torus, for every background density `ρ ≤ M`
(`periodicLogTruncCentered_rows`).  The Euclidean analogue is
`gaussianLogShort_centered_factorial_rows` / `gaussianLog_interpolated_factorial_rows`.

* `abs_centered_rowFactorial`: the signed version of `nonneg_centered_rowFactorial` (centering of a
  symmetric kernel with finite factorial row moments has finite factorial row moments);
* `periodicLogKernel_abs_pow_bound`: `∫ |g|^p ≤ Cg^p p!` from the exponential integrability
  `e^{γ g} ∈ L¹(Haar)`, `γ = d/2 < d`, and the global lower bound of `g`;
* `periodicLogTruncKernel_abs_pow_bound`: the same for `g_τ`, uniformly in `τ > 0`
  (`periodicLogTruncKernel_integral_pow_le`).
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Centering of a symmetric measurable kernel with factorial row moments (signed version of
`nonneg_centered_rowFactorial`). -/
lemma abs_centered_rowFactorial (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω × Ω → ℝ) (hW : Measurable W) (hs : ∀ x y, W (x,y) = W (y,x)) (C : ℝ)
    (hC : RowFactorialMoments μ W C) :
    RowFactorialMoments μ (DGRHS.Gaussian.hoeffdingCentered μ W) (16 * C) := by
  classical
  let P := fun y => ∫ x, W (x,y) ∂μ
  let K := ∫ z, W z ∂μ.prod μ
  have hrowm (y : Ω) : AEStronglyMeasurable (fun x => W (x,y)) μ :=
    (hW.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hrow1 (y : Ω) : Integrable (fun x => |W (x,y)|) μ := by
    simpa only [pow_one] using hC.proper 1 (by omega) y
  have hb1 (y : Ω) : (∫ x, |W (x,y)| ∂μ) ≤ C := by
    simpa only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one] using hC.bound 1 (by omega) y
  have hP (y : Ω) : |P y| ≤ C := by
    calc |P y| ≤ ∫ x, |W (x,y)| ∂μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (fun x => W (x,y))
      _ ≤ C := hb1 y
  have hi1 : Integrable (fun z => |W z|) (μ.prod μ) := by
    simpa only [pow_one] using joint_abs_power_integrable μ W hW C hC 1 (by omega)
  have hi : Integrable W (μ.prod μ) :=
    (integrable_norm_iff hW.aestronglyMeasurable).mp (by simpa only [Real.norm_eq_abs] using hi1)
  have hK : |K| ≤ C := by
    calc |K| ≤ ∫ z, |W z| ∂μ.prod μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ.prod μ) W
      _ = ∫ y, ∫ x, |W (x,y)| ∂μ ∂μ := integral_prod_symm _ hi1
      _ ≤ ∫ _ : Ω, C ∂μ := integral_mono_ae hi1.integral_prod_right (integrable_const C)
          (Filter.Eventually.of_forall fun y => hb1 y)
      _ = C := by simp
  have he (x y : Ω) : DGRHS.Gaussian.hoeffdingCentered μ W (x,y) = W (x,y) - P x - P y + K := by
    unfold DGRHS.Gaussian.hoeffdingCentered DGRHS.centeredKernel DGRHS.potential
      DGRHS.secondPotential P K
    have hswap : (∫ z, W (x,z) ∂μ) = ∫ z, W (z,x) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => hs x z)
    change W (x,y) - (∫ z, W (x,z) ∂μ) - (∫ z, W (z,y) ∂μ) +
      (∫ z, W z ∂μ.prod μ) = W (x,y) - (∫ z, W (z,x) ∂μ) -
      (∫ z, W (z,y) ∂μ) + (∫ z, W z ∂μ.prod μ)
    rw [hswap]
  have hC0 := hC.nonneg
  have hpoint (p : ℕ) (x y : Ω) :
      |DGRHS.Gaussian.hoeffdingCentered μ W (x,y)| ^ p ≤ 2 ^ p * (|W (x,y)| ^ p + (4 * C) ^ p) := by
    have ha : |DGRHS.Gaussian.hoeffdingCentered μ W (x,y)| ≤ |W (x,y)| + 4 * C := by
      rw [he]
      have h1 := hP x
      have h2 := hP y
      rw [abs_le] at h1 h2 hK ⊢
      have h3 := abs_nonneg (W (x,y))
      have h4 := neg_abs_le (W (x,y))
      have h5 := le_abs_self (W (x,y))
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, hK.1, hK.2]
    have hb := (pow_le_pow_left₀ (abs_nonneg _) ha p).trans
      (nonneg_sum_pow_le _ _ (abs_nonneg _) (by linarith) p)
    exact hb
  have hpint (p : ℕ) (hp : 1 ≤ p) (y : Ω) :
      Integrable (fun x => |DGRHS.Gaussian.hoeffdingCentered μ W (x,y)| ^ p) μ := by
    apply (((hC.proper p hp y).add (integrable_const ((4 * C) ^ p))).const_mul (2 ^ p)).mono'
      (by
        have hm := (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ W hW.stronglyMeasurable).measurable
        exact ((continuous_pow p).measurable.comp (continuous_abs.measurable.comp
          (hm.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      change ‖|DGRHS.Gaussian.hoeffdingCentered μ W (x,y)| ^ p‖ ≤
        2 ^ p * (|W (x,y)| ^ p + (4 * C) ^ p)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) p)]
      exact hpoint p x y
  refine ⟨by linarith, hpint, ?_⟩
  intro p hp y
  have hb := integral_mono_ae (hpint p hp y)
    (((hC.proper p hp y).add (integrable_const ((4 * C) ^ p))).const_mul (2 ^ p))
    (Filter.Eventually.of_forall fun x => hpoint p x y)
  change (∫ x, |DGRHS.Gaussian.hoeffdingCentered μ W (x,y)| ^ p ∂μ) ≤
    ∫ x, 2 ^ p * (|W (x,y)| ^ p + (4 * C) ^ p) ∂μ at hb
  rw [integral_const_mul, integral_add (hC.proper p hp y) (integrable_const ((4 * C) ^ p))] at hb
  simp only [integral_const, probReal_univ, one_smul] at hb
  have hfac : (1:ℝ) ≤ (p.factorial : ℝ) := by
    exact_mod_cast (show 1 ≤ p.factorial by have h := Nat.factorial_pos p; omega)
  have hCp : C ^ p ≤ (4 * C) ^ p := pow_le_pow_left₀ hC0 (by linarith) p
  have h2 : (2:ℝ) ≤ 2 ^ p := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hp
  calc
    _ ≤ 2 ^ p * ((∫ x, |W (x,y)| ^ p ∂μ) + (4 * C) ^ p) := hb
    _ ≤ 2 ^ p * (C ^ p * (p.factorial : ℝ) + (4 * C) ^ p) :=
      mul_le_mul_of_nonneg_left (add_le_add (hC.bound p hp y) le_rfl) (by positivity)
    _ ≤ 2 ^ p * (2 * (4 * C) ^ p * (p.factorial : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_right hCp (Nat.cast_nonneg (p.factorial))
      have h3 : (4 * C) ^ p ≤ (4 * C) ^ p * (p.factorial : ℝ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac
          (pow_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC0) p)
      exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    _ ≤ 2 ^ p * (2 ^ p * (4 * C) ^ p * (p.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (pow_nonneg (mul_nonneg (by norm_num) hC0) p))
          (Nat.cast_nonneg p.factorial)) (by positivity)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← mul_pow, ← mul_pow]
      congr 1
      congr 1
      ring

end DGRHS.Attractive

#print axioms DGRHS.Attractive.abs_centered_rowFactorial

namespace DGRHS.Periodic
open DGRHS.Attractive DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Factorial `L^p(Haar)` moments of the exact periodic LOG kernel: `∫ |g|^p ≤ Cg^p p!`. -/
theorem periodicLogKernel_abs_pow_bound :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ p : ℕ, 1 ≤ p →
      Integrable (fun x => |periodicLogKernel (ι := ι) x| ^ p) (periodicHaar ι) ∧
      ∫ x, |periodicLogKernel (ι := ι) x| ^ p ∂periodicHaar ι ≤ Cg ^ p * (p.factorial : ℝ) := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd_def
  have hd : 0 < d := by rw [hd_def]; exact_mod_cast Fintype.card_pos (α := ι)
  set γ : ℝ := d / 2 with hγ_def
  have hγ0 : 0 < γ := by positivity
  have hγd : γ < d := by rw [hγ_def]; linarith
  have hE := periodicLogKernel_exp_integrable (ι := ι) γ hγ0.le hγd
  set c : ℝ := max (periodicGreenLowerConstant ι) 0 with hc_def
  have hc0 : 0 ≤ c := le_max_right _ _
  set E : ℝ := ∫ x, Real.exp (γ * periodicLogKernel (ι := ι) x) ∂periodicHaar ι with hE_def
  have hE0 : 0 ≤ E := integral_nonneg fun x => (Real.exp_pos _).le
  set K : ℝ := max 1 (Real.exp (2 * γ * c) * E) with hK_def
  have hK1 : 1 ≤ K := le_max_left _ _
  refine ⟨K / γ, by positivity, fun p hp => ?_⟩
  have hlow := periodicLogKernel_lower_ae (ι := ι)
  set B : ℝ := (p.factorial : ℝ) / γ ^ p * Real.exp (2 * γ * c) with hB_def
  have hpt : ∀ᵐ x ∂periodicHaar ι, |periodicLogKernel (ι := ι) x| ^ p ≤
      B * Real.exp (γ * periodicLogKernel (ι := ι) x) := by
    filter_upwards [hlow] with x hx
    have hx' : -c ≤ periodicLogKernel (ι := ι) x :=
      le_trans (neg_le_neg (le_max_left _ _)) hx
    have habs : |periodicLogKernel (ι := ι) x| ≤ periodicLogKernel (ι := ι) x + 2 * c := by
      rcases le_total 0 (periodicLogKernel (ι := ι) x) with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    have h1 := Real.pow_div_factorial_le_exp (γ * |periodicLogKernel (ι := ι) x|)
      (by positivity) p
    have h2 : Real.exp (γ * |periodicLogKernel (ι := ι) x|) ≤
        Real.exp (2 * γ * c) * Real.exp (γ * periodicLogKernel (ι := ι) x) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hfac : (0:ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
    have hγp : 0 < γ ^ p := by positivity
    have h3 : |periodicLogKernel (ι := ι) x| ^ p ≤
        (p.factorial : ℝ) / γ ^ p * Real.exp (γ * |periodicLogKernel (ι := ι) x|) := by
      rw [mul_pow, div_le_iff₀ hfac] at h1
      rw [div_mul_eq_mul_div, le_div_iff₀ hγp]
      nlinarith [h1, mul_comm (|periodicLogKernel (ι := ι) x| ^ p) (γ ^ p)]
    calc |periodicLogKernel (ι := ι) x| ^ p
        ≤ (p.factorial : ℝ) / γ ^ p * Real.exp (γ * |periodicLogKernel (ι := ι) x|) := h3
      _ ≤ (p.factorial : ℝ) / γ ^ p *
          (Real.exp (2 * γ * c) * Real.exp (γ * periodicLogKernel (ι := ι) x)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by rw [hB_def]; ring
  have hmeas : AEStronglyMeasurable (fun x => |periodicLogKernel (ι := ι) x| ^ p) (periodicHaar ι) :=
    ((continuous_pow p).measurable.comp
      (continuous_abs.measurable.comp periodicLogKernel_measurable)).aestronglyMeasurable
  have hBi : Integrable (fun x => B * Real.exp (γ * periodicLogKernel (ι := ι) x)) (periodicHaar ι) :=
    hE.const_mul B
  have hint : Integrable (fun x => |periodicLogKernel (ι := ι) x| ^ p) (periodicHaar ι) :=
    hBi.mono' hmeas (hpt.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) p)]; exact hx)
  refine ⟨hint, ?_⟩
  calc ∫ x, |periodicLogKernel (ι := ι) x| ^ p ∂periodicHaar ι
      ≤ ∫ x, B * Real.exp (γ * periodicLogKernel (ι := ι) x) ∂periodicHaar ι :=
        integral_mono_ae hint hBi hpt
    _ = B * E := by rw [integral_const_mul]
    _ ≤ (K / γ) ^ p * (p.factorial : ℝ) := by
        have hfac : (0:ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
        have hγp : 0 < γ ^ p := by positivity
        have hEK : Real.exp (2 * γ * c) * E ≤ K ^ p :=
          (le_max_right _ _).trans (le_self_pow₀ hK1 (by omega))
        calc B * E = (p.factorial : ℝ) / γ ^ p * (Real.exp (2 * γ * c) * E) := by
              rw [hB_def]; ring
          _ ≤ (p.factorial : ℝ) / γ ^ p * K ^ p :=
              mul_le_mul_of_nonneg_left hEK (by positivity)
          _ = (K / γ) ^ p * (p.factorial : ℝ) := by
              have key : ∀ (a b q : ℝ) (n : ℕ), a / q ^ n * b ^ n = (b / q) ^ n * a := by
                intro a b q n
                rw [div_pow]
                ring
              exact key _ _ _ _

/-- Uniform factorial moments of the heat-shifted LOG kernels (Jensen against the heat kernel). -/
theorem periodicLogTruncKernel_abs_pow_bound :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ τ : ℝ, 0 < τ → ∀ p : ℕ, 1 ≤ p →
      ∫ x, |periodicLogTruncKernel (ι := ι) τ x| ^ p ∂periodicHaar ι ≤ Cg ^ p * (p.factorial : ℝ) := by
  obtain ⟨Cg, hCg, h⟩ := periodicLogKernel_abs_pow_bound (ι := ι)
  exact ⟨Cg, hCg, fun τ hτ p hp =>
    (periodicLogTruncKernel_integral_pow_le τ hτ p hp (h p hp).1).trans (h p hp).2⟩

lemma periodicLogTruncKernel_continuous (τ : ℝ) (hτ : 0 < τ) :
    Continuous (periodicLogTruncKernel (ι := ι) τ) :=
  periodicPositiveFourierKernel_continuous _ (periodicLogTruncCoeff_nonneg τ)
    (periodicLogTruncCoeff_summable τ hτ)

lemma periodicLogTruncKernel_pair_symm (τ : ℝ) (hτ : 0 < τ) (x y : PeriodicTorus ι) :
    periodicLogTruncKernel (ι := ι) τ (x - y) = periodicLogTruncKernel (ι := ι) τ (y - x) := by
  have ha := periodicLogTruncCoeff_nonneg (ι := ι) τ
  have hs := periodicLogTruncCoeff_summable (ι := ι) τ hτ
  have h1 := periodicPositiveFourierFeature_gram _ ha hs x y
  have h2 := periodicPositiveFourierFeature_gram _ ha hs y x
  rw [real_inner_comm] at h2
  exact h1.symm.trans h2

/-- Core of the row bound: given uniform factorial moments `Cg` of the truncated kernels. -/
theorem periodicLogTruncCentered_rows_core (Cg : ℝ) (hCg : 0 < Cg)
    (hbd : ∀ τ : ℝ, 0 < τ → ∀ p : ℕ, 1 ≤ p →
      ∫ x, |periodicLogTruncKernel (ι := ι) τ x| ^ p ∂periodicHaar ι ≤ Cg ^ p * (p.factorial : ℝ))
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ)
    (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (τ : ℝ) (hτ : 0 < τ) :
    RowFactorialMoments (periodicCappedDensityMeasure ρ)
      (periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ) (16 * (max 1 M * Cg)) := by
  set μ := periodicCappedDensityMeasure ρ with hμ
  set W : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun z => periodicLogTruncKernel τ (z.1 - z.2) with hW
  have hgc := periodicLogTruncKernel_continuous (ι := ι) τ hτ
  have hWc : Continuous W := hgc.comp (continuous_fst.sub continuous_snd)
  have hWs : ∀ x y, W (x,y) = W (y,x) := fun x y => periodicLogTruncKernel_pair_symm τ hτ x y
  have hrow : RowFactorialMoments μ W (max 1 M * Cg) := by
    refine rowFactorialMoments_of_proper_bound μ W _ (fun p hp y => ?_) (fun p hp y => ?_)
    · exact ((hgc.comp (continuous_id.sub continuous_const)).abs.pow p).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · have hI : Integrable (fun z => |periodicLogTruncKernel (ι := ι) τ z| ^ p) (periodicHaar ι) :=
        (hgc.abs.pow p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have h1 := periodicDensityColumn_nonnegative_bound ρ M hM hρ
        (fun z => |periodicLogTruncKernel (ι := ι) τ z| ^ p) hI
        (fun z => pow_nonneg (abs_nonneg _) p) y
      have h2 := hbd τ hτ p hp
      have hM1 : M ≤ max 1 M ^ p :=
        (le_max_right 1 M).trans (le_self_pow₀ (le_max_left 1 M) (by omega))
      calc ∫ x, |W (x,y)| ^ p ∂μ ≤ M * ∫ z, |periodicLogTruncKernel (ι := ι) τ z| ^ p ∂periodicHaar ι := h1
        _ ≤ M * (Cg ^ p * (p.factorial : ℝ)) := mul_le_mul_of_nonneg_left h2 hM
        _ ≤ max 1 M ^ p * (Cg ^ p * (p.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_right hM1 (by positivity)
        _ = (max 1 M * Cg) ^ p * (p.factorial : ℝ) := by rw [mul_pow]; ring
  exact abs_centered_rowFactorial μ W hWc.measurable hWs _ hrow

/-- Uniform factorial row moments of the Hoeffding-centered heat-shifted LOG kernels for every
bounded background density `ρ ≤ M`: the constant `R` depends only on the bound `M` (and the torus). -/
theorem periodicLogTruncCentered_rows_uniform (M : ℝ) (hM : 0 ≤ M) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ (ρ : PeriodicTorus ι → ℝ)
      [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
      (_ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (τ : ℝ), 0 < τ →
      RowFactorialMoments (periodicCappedDensityMeasure ρ)
        (periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ) R := by
  obtain ⟨Cg, hCg, hbd⟩ := periodicLogTruncKernel_abs_pow_bound (ι := ι)
  exact ⟨16 * (max 1 M * Cg), by positivity, fun ρ _ hρ τ hτ =>
    periodicLogTruncCentered_rows_core Cg hCg hbd ρ M hM hρ τ hτ⟩

/-- Uniform factorial row moments of the Hoeffding-centered heat-shifted LOG kernels for every
bounded background density `ρ ≤ M`. -/
theorem periodicLogTruncCentered_rows (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ τ : ℝ, 0 < τ →
      RowFactorialMoments (periodicCappedDensityMeasure ρ)
        (periodicLogTruncCentered (periodicCappedDensityMeasure ρ) τ) R := by
  obtain ⟨R, hR, h⟩ := periodicLogTruncCentered_rows_uniform (ι := ι) M hM
  exact ⟨R, hR, h ρ hρ⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogKernel_abs_pow_bound
#print axioms DGRHS.Periodic.periodicLogTruncKernel_abs_pow_bound
#print axioms DGRHS.Periodic.periodicLogTruncKernel_continuous
#print axioms DGRHS.Periodic.periodicLogTruncKernel_pair_symm
#print axioms DGRHS.Periodic.periodicLogTruncCentered_rows_core
#print axioms DGRHS.Periodic.periodicLogTruncCentered_rows_uniform
#print axioms DGRHS.Periodic.periodicLogTruncCentered_rows
