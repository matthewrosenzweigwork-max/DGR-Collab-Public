import SharpSymmetricLSI.Paper.AppAReg2

/-!
# The weak formulation (1): Fourier form

For a linear mild solution and a smooth periodic test function `φ`, for `0 ≤ s ≤ t ≤ T`:
`∫φρ_t - ∫φρ_s = ∫_{(s,t]} ∑ₙ conj(φ̂(n)) (-λₙ ρ̂_u(n) + bₙ(u)) du` (`LinMild.weak_form_fourier`).
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal ComplexConjugate

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The mode equation between two times. -/
theorem mode_ode_sub {lam : ℝ} (hlam : 0 ≤ lam) {b : ℝ → ℂ} (hbm : Measurable b) {B : ℝ}
    (hbB : ∀ v, ‖b v‖ ≤ B) (c : ℂ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ((Real.exp (-lam * t) : ℂ) * c + modeD lam b t) - ((Real.exp (-lam * s) : ℂ) * c + modeD lam b s) =
      ∫ u in Ioc s t, (-(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c + modeD lam b u) + b u) := by
  rw [mode_ode hlam hbm hbB c (hs.trans hst), mode_ode hlam hbm hbB c hs]
  set g : ℝ → ℂ := fun u => -(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c + modeD lam b u) + b u
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
  have hgm : Measurable g := by
    have := measurable_modeD hlam hbm hbB
    exact (measurable_const.mul (((Complex.measurable_ofReal.comp (by fun_prop)).mul
      measurable_const).add this)).add hbm
  have hgi : IntegrableOn g (Ioc 0 t) := by
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) t)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    refine (integrable_const (lam * (‖c‖ + B * t) + B)).mono' hgm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_))
    have hD := norm_modeD_le hlam hbm hbB hu.1.le
    have he : ‖(Real.exp (-lam * u) : ℂ) * c‖ ≤ ‖c‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (Real.exp_le_one_iff.2 (by nlinarith [hu.1]))
    calc ‖g u‖ ≤ ‖-(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c + modeD lam b u)‖ + ‖b u‖ :=
          norm_add_le _ _
      _ ≤ lam * (‖c‖ + B * t) + B := by
          refine add_le_add ?_ (hbB u)
          rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
          exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add he
            (hD.trans (mul_le_mul_of_nonneg_left hu.2 hB0)))) hlam
  have hsplit : Ioc 0 t = Ioc 0 s ∪ Ioc s t := (Ioc_union_Ioc_eq_Ioc hs hst).symm
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (hgi.mono_set (hsplit ▸ subset_union_left)) (hgi.mono_set (hsplit ▸ subset_union_right))]
  ring

/-- `∑ λₙ |φ̂(n)|²` and `∑ λₙ² |φ̂(n)|²` converge for smooth `φ`. -/
theorem summable_lam_sq_cf {φ : UnitAddTorus ι → ℝ} (hφ : IsSmoothT φ) :
    Summable (fun n => lamN n * ‖cf φ n‖ ^ 2) ∧ Summable (fun n => (lamN n) ^ 2 * ‖cf φ n‖ ^ 2) := by
  have hsj := fun j => isSmoothT_dpart hφ j
  have hsjj := fun j => isSmoothT_dpart (hsj j) j
  have hc : ∀ {v : UnitAddTorus ι → ℝ}, IsSmoothT v → Continuous v := fun hv => continuous_of_isSmoothT hv
  constructor
  · have hw := hasSum_wt_cf (isWeakGrad_of_contDiff (hφ.of_le (by simp)))
      (memLp_of_continuous (hc hφ) 2) (fun j => memLp_of_continuous (hc (hsj j)) 2)
    refine hw.summable.of_nonneg_of_le (fun n => mul_nonneg (lamN_nonneg n) (sq_nonneg _))
      fun n => ?_
    gcongr
    unfold wt lamN; linarith
  · set L : UnitAddTorus ι → ℝ := fun y => ∑ j, dpart_appA (dpart_appA φ j) j y
    have hL : Continuous L := continuous_finset_sum _ fun j _ => hc (hsjj j)
    have hP := (hasSum_sq_mFourierCoeff_real (memLp_of_continuous hL 2)).summable
    refine hP.congr fun n => ?_
    have hcf : cf L n = -(lamN n : ℂ) * cf φ n := by
      rw [cf_sum _ fun j _ => (memLp_of_continuous (hc (hsjj j)) 1).integrable le_rfl]
      simp_rw [cf_dpart_appA (hsj _), cf_dpart_appA hφ]
      rw [lamN]; push_cast
      set Y := cf φ n
      have hj : ∀ j, 2 * (π : ℂ) * I * n j * (2 * π * I * n j * Y) = -(4 * π ^ 2) * (n j : ℂ) ^ 2 * Y :=
        fun j => by ring_nf; rw [I_sq]; ring
      simp_rw [hj]
      rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
    simp only [cf] at hcf
    rw [hcf, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lamN_nonneg n),
      mul_pow]

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

/-- The mode equation for the coefficients of `ρ`. -/
theorem cf_sub_eq_integral {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    (n : ι → ℤ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    cf (ρ t) n - cf (ρ s) n =
      ∫ u in Ioc s t, (-(lamN n : ℂ) * cf (ρ u) n + modeB N T n u) := by
  rw [h.cf_eq_mode hK0 hK n ⟨hs.trans hst, htT⟩, h.cf_eq_mode hK0 hK n ⟨hs, hst.trans htT⟩,
    mode_ode_sub (lamN_nonneg n) (h.measurable_modeB T n) (h.norm_modeB_le hK0 hK n) _ hs hst]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  rw [h.cf_eq_mode hK0 hK n ⟨hs.trans hu.1.le, hu.2.trans htT⟩]

/-- Pointwise bound for the mode forcing. -/
theorem norm_modeB_le_sqrt (T : ℝ) (n : ι → ℤ) (v : ℝ) :
    ‖modeB N T n v‖ ≤ Real.sqrt (lamN n) * Real.sqrt (∑ k, ‖cf (fun z => N v z k) n‖ ^ 2) := by
  rw [← Real.sqrt_mul (lamN_nonneg n)]
  exact Real.le_sqrt_of_sq_le (h.norm_modeB_sq_le T n v)

/-- **The weak formulation, in Fourier form.** -/
theorem weak_form_fourier {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    {φ : UnitAddTorus ι → ℝ} (hφ : IsSmoothT φ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (htT : t ≤ T) :
    (((∫ x, φ x * ρ t x) - ∫ x, φ x * ρ s x : ℝ) : ℂ) =
      ∫ u in Ioc s t, ∑' n, conj (cf φ n) * (-(lamN n : ℂ) * cf (ρ u) n + modeB N T n u) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc s t)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hφ2 : MemLp φ 2 volume := memLp_of_continuous (continuous_of_isSmoothT hφ) 2
  have hP : ∀ u ∈ Icc 0 T, HasSum (fun n => conj (cf φ n) * cf (ρ u) n)
      ((∫ x, φ x * ρ u x : ℝ) : ℂ) := fun u hu =>
    hasSum_prod_cf_real hφ2 (h.memLp_two_section hK hu)
  have hts : ((∫ x, φ x * ρ t x : ℝ) : ℂ) - ((∫ x, φ x * ρ s x : ℝ) : ℂ) =
      ∑' n, conj (cf φ n) * (cf (ρ t) n - cf (ρ s) n) := by
    rw [((hP t ⟨hs.trans hst, htT⟩).sub (hP s ⟨hs, hst.trans htT⟩)).tsum_eq.symm]
    congr 1; funext n; ring
  push_cast
  rw [hts]
  simp_rw [h.cf_sub_eq_integral hK0 hK _ hs hst htT, ← integral_const_mul]
  set f : (ι → ℤ) → ℝ → ℂ := fun n u =>
    conj (cf φ n) * (-(lamN n : ℂ) * cf (ρ u) n + modeB N T n u) with hf
  have hfm : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Ioc s t)) := fun n =>
    (measurable_const.mul ((measurable_const.mul (h.measurable_cf_section n)).add
      (h.measurable_modeB T n))).aestronglyMeasurable
  -- the summable pointwise bound
  obtain ⟨hP1, hP2⟩ := summable_lam_sq_cf hφ
  set S : ℝ → (ι → ℤ) → ℝ := fun u n => ∑ k, ‖cf (fun z => N u z k) n‖ ^ 2
  have hSs : ∀ u ∈ Icc 0 T, HasSum (S u) (∑ k, ∫ z, (N u z k) ^ 2) := fun u hu =>
    hasSum_sum fun k _ => hasSum_sq_mFourierCoeff_real
      (memLp_of_abs_le (h.measurable_sectionN u k) (fun z => h.abs_N_le hK hu z k) 2)
  have hSb : ∀ u ∈ Icc 0 T, ∑ k, ∫ z, (N u z k) ^ 2 ≤ Fintype.card ι * (A * K) ^ 2 := fun u hu => by
    calc ∑ k, ∫ z, (N u z k) ^ 2 ≤ ∑ _k : ι, (A * K) ^ 2 := Finset.sum_le_sum fun k _ => by
          refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
            (integrable_const ((A * K) ^ 2)) (Eventually.of_forall fun z => ?_)).trans (by simp)
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h.abs_N_le hK hu z k) 2
      _ = _ := by simp
  have hab : ∀ u ∈ Icc 0 T, HasSum (fun n => ‖cf (ρ u) n‖ ^ 2) (∫ x, ρ u x ^ 2) := fun u hu =>
    hasSum_sq_mFourierCoeff_real (h.memLp_two_section hK hu)
  have habb : ∀ u ∈ Icc 0 T, ∫ x, ρ u x ^ 2 ≤ K ^ 2 := fun u hu => by
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
      (integrable_const (K ^ 2)) (Eventually.of_forall fun z => ?_)).trans (by simp)
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hK u hu z) 2
  set P2v : ℝ := ∑' n, (lamN n) ^ 2 * ‖cf φ n‖ ^ 2
  set P1v : ℝ := ∑' n, lamN n * ‖cf φ n‖ ^ 2
  set C : ℝ := (P2v + K ^ 2 + P1v + Fintype.card ι * (A * K) ^ 2) / 2
  have hpt : ∀ u ∈ Icc 0 T, ∀ n, ‖f n u‖ ≤
      ((lamN n) ^ 2 * ‖cf φ n‖ ^ 2 + ‖cf (ρ u) n‖ ^ 2 + lamN n * ‖cf φ n‖ ^ 2 + S u n) / 2 := by
    intro u hu n
    have hb := h.norm_modeB_le_sqrt T n u
    have hl := lamN_nonneg n
    simp only [hf]
    rw [norm_mul, Complex.norm_conj]
    calc ‖cf φ n‖ * ‖-(lamN n : ℂ) * cf (ρ u) n + modeB N T n u‖
        ≤ ‖cf φ n‖ * (lamN n * ‖cf (ρ u) n‖ + Real.sqrt (lamN n) * Real.sqrt (S u n)) := by
          gcongr
          refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) hb)
          rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
      _ ≤ _ := by
          have h1 := sq_nonneg (lamN n * ‖cf φ n‖ - ‖cf (ρ u) n‖)
          have h2 := sq_nonneg (Real.sqrt (lamN n) * ‖cf φ n‖ - Real.sqrt (S u n))
          have hs1 : Real.sqrt (lamN n) ^ 2 = lamN n := Real.sq_sqrt hl
          have hs2 : Real.sqrt (S u n) ^ 2 = S u n :=
            Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
          nlinarith
  have hsumb : ∀ u ∈ Icc 0 T, ∑' n, ‖f n u‖ₑ ≤ ENNReal.ofReal C := by
    intro u hu
    have hsum : HasSum (fun n => ((lamN n) ^ 2 * ‖cf φ n‖ ^ 2 + ‖cf (ρ u) n‖ ^ 2 +
        lamN n * ‖cf φ n‖ ^ 2 + S u n) / 2)
        ((P2v + (∫ x, ρ u x ^ 2) + P1v + ∑ k, ∫ z, (N u z k) ^ 2) / 2) :=
      ((((hP2.hasSum).add (hab u hu)).add hP1.hasSum).add (hSs u hu)).div_const 2
    calc ∑' n, ‖f n u‖ₑ ≤ ∑' n, ENNReal.ofReal (((lamN n) ^ 2 * ‖cf φ n‖ ^ 2 + ‖cf (ρ u) n‖ ^ 2 +
          lamN n * ‖cf φ n‖ ^ 2 + S u n) / 2) := ENNReal.tsum_le_tsum fun n => by
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hpt u hu n)
      _ = ENNReal.ofReal ((P2v + (∫ x, ρ u x ^ 2) + P1v + ∑ k, ∫ z, (N u z k) ^ 2) / 2) := by
            rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun n => by
              have := lamN_nonneg n
              have : 0 ≤ S u n := Finset.sum_nonneg fun k _ => sq_nonneg _
              positivity) hsum.summable]
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by
            simp only [C]; linarith [habb u hu, hSb u hu])
  have hlint : ∑' n, ∫⁻ u in Ioc s t, ‖f n u‖ₑ ≠ ⊤ := by
    rw [← lintegral_tsum fun n => (hfm n).enorm]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := C))
      (measure_ne_top (volume.restrict (Ioc s t)) univ)) ?_
    rw [← lintegral_const]
    exact setLIntegral_mono' measurableSet_Ioc fun u hu =>
      hsumb u ⟨hs.trans hu.1.le, hu.2.trans htT⟩
  rw [integral_tsum hfm hlint]

end LinMild

end SharpLSI
