import SharpSymmetricLSI.Paper.AppACont1

/-!
# Continuity in time of linear mild solutions (2): `L²` continuity

`s ↦ ρ_s` is continuous on `[0,T]` in `L²` (`LinMild.tendsto_L2`): by Parseval
`‖ρ_s - ρ_t‖₂² = ∑ₙ |a_n(s) - a_n(t)|²`, each mode is continuous, and
`|a_n(s)|² ≤ 2|ρ̂₀(n)|² + 2 wₙ` with `wₙ = ∫₀ᵀ ∑ₖ |N̂_{v,k}(n)|² dv` summable.
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The summable weight of the Duhamel modes. -/
noncomputable def modeW (N : ℝ → UnitAddTorus ι → ι → ℝ) (T : ℝ) (n : ι → ℤ) : ℝ :=
  ∫ v in Ioc 0 T, ∑ k, ‖cf (fun z => N v z k) n‖ ^ 2

namespace LinMild

variable {ρ₀ : UnitAddTorus ι → ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
  {N : ℝ → UnitAddTorus ι → ι → ℝ} {A : ℝ} (h : LinMild ρ₀ ρ N A)
include h

theorem norm_modeB_sq_le (T : ℝ) (n : ι → ℤ) (v : ℝ) :
    ‖modeB N T n v‖ ^ 2 ≤ lamN n * ∑ k, ‖cf (fun z => N v z k) n‖ ^ 2 := by
  unfold modeB
  split_ifs
  · have := norm_sum_mul_sq_le (fun k => (2 * π * I * n k : ℂ)) (fun k => cf (fun z => N v z k) n)
    rwa [sum_norm_two_pi_sq] at this
  · rw [norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg (lamN_nonneg n) (Finset.sum_nonneg fun k _ => sq_nonneg _)

theorem measurable_cf_sq (n : ι → ℤ) :
    Measurable fun v => ∑ k, ‖cf (fun z => N v z k) n‖ ^ 2 :=
  Finset.measurable_sum _ fun k _ => (h.measurable_cfN n k).norm.pow_const 2

theorem norm_modeD_sq_le_W {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    (n : ι → ℤ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ‖modeD (lamN n) (modeB N T n) s‖ ^ 2 ≤ modeW N T n := by
  have hbm := h.measurable_modeB T n
  have hbB := h.norm_modeB_le hK0 hK n
  have hW0 : 0 ≤ modeW N T n := setIntegral_nonneg measurableSet_Ioc fun v _ =>
    Finset.sum_nonneg fun k _ => sq_nonneg _
  rcases (lamN_nonneg n).eq_or_lt with h0 | hpos
  · -- `λ = 0`: no forcing
    have hb0 : ∀ v, modeB N T n v = 0 := fun v => by
      have := h.norm_modeB_sq_le T n v
      rw [← h0, zero_mul] at this
      exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm this (sq_nonneg _)))
    simp only [modeD, hb0, mul_zero, integral_zero, norm_zero]
    rw [zero_pow two_ne_zero]; exact hW0
  · refine (norm_modeD_sq_le hpos hbm hbB hs).trans ?_
    haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
      isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    set Cb := ∑ k : ι, 2 * π * |(n k : ℝ)| * (A * K)
    have h1 : ∫ v in Ioc 0 T, ‖modeB N T n v‖ ^ 2 ≤
        ∫ v in Ioc 0 T, lamN n * ∑ k, ‖cf (fun z => N v z k) n‖ ^ 2 := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) ?_
        (Eventually.of_forall fun v => h.norm_modeB_sq_le T n v)
      refine ((integrable_const (lamN n * (Fintype.card ι * (A * K) ^ 2))).mono'
        ((h.measurable_cf_sq n).const_mul _).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_)))
      have hv' : v ∈ Icc 0 T := ⟨hv.1.le, hv.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (lamN_nonneg n)
        (Finset.sum_nonneg fun k _ => sq_nonneg _))]
      refine mul_le_mul_of_nonneg_left ?_ (lamN_nonneg n)
      calc ∑ k, ‖cf (fun z => N v z k) n‖ ^ 2 ≤ ∑ _k : ι, (A * K) ^ 2 :=
            Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (norm_nonneg _)
              (h.norm_cf_le (h.measurable_sectionN v k) (fun z => h.abs_N_le hK hv' z k) n) 2
        _ = _ := by simp
    rw [integral_const_mul] at h1
    calc 1 / lamN n * ∫ v in Ioc 0 T, ‖modeB N T n v‖ ^ 2
        ≤ 1 / lamN n * (lamN n * modeW N T n) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = modeW N T n := by field_simp

theorem memLp_two_section {T K : ℝ} (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) {s : ℝ}
    (hs : s ∈ Icc 0 T) : MemLp (ρ s) 2 volume :=
  memLp_of_abs_le (h.measurable_section s) (hK s hs) 2

theorem summable_modeW {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K) :
    Summable (modeW N T) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) T)) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hpt : ∀ v ∈ Icc 0 T, ∀ k (S : Finset (ι → ℤ)),
      ∑ n ∈ S, ‖cf (fun z => N v z k) n‖ ^ 2 ≤ (A * K) ^ 2 := by
    intro v hv k S
    have hm : MemLp (fun z => N v z k) 2 volume :=
      memLp_of_abs_le (h.measurable_sectionN v k) (fun z => h.abs_N_le hK hv z k) 2
    have hs := hasSum_sq_mFourierCoeff_real hm
    refine (sum_le_hasSum S (fun n _ => sq_nonneg _) hs).trans ?_
    refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
      (integrable_const ((A * K) ^ 2)) (Eventually.of_forall fun z => ?_)).trans (by simp)
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h.abs_N_le hK hv z k) 2
  have hint : ∀ n, Integrable (fun v => ∑ k, ‖cf (fun z => N v z k) n‖ ^ 2)
      (volume.restrict (Ioc 0 T)) := fun n =>
    (integrable_const (Fintype.card ι * (A * K) ^ 2)).mono' (h.measurable_cf_sq n).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)]
        calc ∑ k, ‖cf (fun z => N v z k) n‖ ^ 2 ≤ ∑ _k : ι, (A * K) ^ 2 :=
              Finset.sum_le_sum fun k _ => by
                have := hpt v ⟨hv.1.le, hv.2⟩ k {n}
                simpa using this
          _ = _ := by simp))
  refine summable_of_sum_le (c := max T 0 * (Fintype.card ι * (A * K) ^ 2))
    (fun n => setIntegral_nonneg measurableSet_Ioc fun v _ =>
      Finset.sum_nonneg fun k _ => sq_nonneg _) fun S => ?_
  unfold modeW
  rw [← integral_finsetSum _ fun n _ => hint n]
  refine (integral_mono_of_nonneg (Eventually.of_forall fun v =>
    Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun k _ => sq_nonneg _)
    (integrable_const (Fintype.card ι * (A * K) ^ 2))
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_))).trans ?_
  · rw [Finset.sum_comm]
    calc ∑ k, ∑ n ∈ S, ‖cf (fun z => N v z k) n‖ ^ 2 ≤ ∑ _k : ι, (A * K) ^ 2 :=
          Finset.sum_le_sum fun k _ => hpt v ⟨hv.1.le, hv.2⟩ k S
      _ = _ := by simp
  · rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc, sub_zero]

theorem norm_cf_sq_le {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    (n : ι → ℤ) {s : ℝ} (hs : s ∈ Icc 0 T) :
    ‖cf (ρ s) n‖ ^ 2 ≤ 2 * ‖cf ρ₀ n‖ ^ 2 + 2 * modeW N T n := by
  rw [h.cf_eq_mode hK0 hK n hs]
  have hD := h.norm_modeD_sq_le_W hK0 hK n hs
  have he : ‖(Real.exp (-lamN n * s) : ℂ) * cf ρ₀ n‖ ≤ ‖cf ρ₀ n‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.2 (by nlinarith [lamN_nonneg n, hs.1]))
  calc ‖(Real.exp (-lamN n * s) : ℂ) * cf ρ₀ n + modeD (lamN n) (modeB N T n) s‖ ^ 2
      ≤ (‖(Real.exp (-lamN n * s) : ℂ) * cf ρ₀ n‖ + ‖modeD (lamN n) (modeB N T n) s‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
    _ ≤ 2 * ‖(Real.exp (-lamN n * s) : ℂ) * cf ρ₀ n‖ ^ 2 +
          2 * ‖modeD (lamN n) (modeB N T n) s‖ ^ 2 := by
        nlinarith [sq_nonneg (‖(Real.exp (-lamN n * s) : ℂ) * cf ρ₀ n‖ -
          ‖modeD (lamN n) (modeB N T n) s‖)]
    _ ≤ 2 * ‖cf ρ₀ n‖ ^ 2 + 2 * modeW N T n := by
        gcongr

theorem continuousOn_cf {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    (n : ι → ℤ) : ContinuousOn (fun s => cf (ρ s) n) (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [Icc_eq_empty (by linarith)]; exact continuousOn_empty _
  set lam := lamN n
  set c := cf ρ₀ n
  set b := modeB N T n
  have hbm := h.measurable_modeB T n
  have hbB := h.norm_modeB_le hK0 hK n
  set B := ∑ k : ι, 2 * π * |(n k : ℝ)| * (A * K)
  set g : ℝ → ℂ := fun u => -(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c + modeD lam b u) + b u
  have hgm : Measurable g := by
    have := measurable_modeD (lamN_nonneg n) hbm hbB
    exact (measurable_const.mul (((Complex.measurable_ofReal.comp (by fun_prop)).mul
      measurable_const).add this)).add hbm
  have hgi : IntegrableOn g (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) T)) :=
      isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne
    refine (integrable_const (lam * (‖c‖ + B * T) + B)).mono' hgm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun u hu => ?_))
    have hD := norm_modeD_le (lamN_nonneg n) hbm hbB hu.1
    have he : ‖(Real.exp (-lam * u) : ℂ) * c‖ ≤ ‖c‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (Real.exp_le_one_iff.2 (by nlinarith [lamN_nonneg n, hu.1]))
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbB 0)
    calc ‖g u‖ ≤ ‖-(lam : ℂ) * ((Real.exp (-lam * u) : ℂ) * c + modeD lam b u)‖ + ‖b u‖ :=
          norm_add_le _ _
      _ ≤ lam * (‖c‖ + B * T) + B := by
          refine add_le_add ?_ (hbB u)
          rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lamN_nonneg n)]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add he
            (hD.trans ?_))) (lamN_nonneg n)
          exact mul_le_mul_of_nonneg_left hu.2 hB0
  have hprim := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := T) hgi
  rw [uIcc_of_le hT] at hprim
  refine ((continuousOn_const (c := c)).add hprim).congr fun s hs => ?_
  rw [h.cf_eq_mode hK0 hK n hs, mode_ode (lamN_nonneg n) hbm hbB c hs.1]
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_of_le hs.1]

/-- **`L²` continuity in time.** -/
theorem tendsto_L2 {T K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ t ∈ Icc 0 T, ∀ x, |ρ t x| ≤ K)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => ∫ x, (ρ s x - ρ t x) ^ 2) (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hP : ∀ s ∈ Icc 0 T, ∫ x, (ρ s x - ρ t x) ^ 2 = ∑' n, ‖cf (ρ s) n - cf (ρ t) n‖ ^ 2 := by
    intro s hs
    have hm : MemLp (fun x => ρ s x - ρ t x) 2 volume :=
      (h.memLp_two_section hK hs).sub (h.memLp_two_section hK ht)
    have := (hasSum_sq_mFourierCoeff_real hm).tsum_eq
    rw [← this]
    congr 1; funext n
    have e := cf_sub ((h.memLp_two_section hK hs).integrable one_le_two)
      ((h.memLp_two_section hK ht).integrable one_le_two) n
    simp only [cf] at e
    rw [e]
  have hc := hasSum_sq_mFourierCoeff_real (h.memLp_two_section hK ⟨le_rfl, ht.1.trans ht.2⟩)
  rw [h.init] at hc
  set bound : (ι → ℤ) → ℝ := fun n => 8 * ‖cf ρ₀ n‖ ^ 2 + 8 * modeW N T n
  have hsum : Summable bound := (hc.summable.mul_left 8).add ((h.summable_modeW hK0 hK).mul_left 8)
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[Icc 0 T] t)
    (f := fun s n => ‖cf (ρ s) n - cf (ρ t) n‖ ^ 2) (g := fun _ => (0 : ℝ)) hsum
    (fun n => by
      have h1 := ((h.continuousOn_cf hK0 hK n) t ht).tendsto
      have := ((h1.sub_const (cf (ρ t) n)).norm).pow 2
      rwa [sub_self, norm_zero, zero_pow two_ne_zero] at this)
    (eventually_nhdsWithin_of_forall fun s hs n => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := h.norm_cf_sq_le hK0 hK n hs
      have h2 := h.norm_cf_sq_le hK0 hK n ht
      calc ‖cf (ρ s) n - cf (ρ t) n‖ ^ 2 ≤ (‖cf (ρ s) n‖ + ‖cf (ρ t) n‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
        _ ≤ 2 * ‖cf (ρ s) n‖ ^ 2 + 2 * ‖cf (ρ t) n‖ ^ 2 := by
            nlinarith [sq_nonneg (‖cf (ρ s) n‖ - ‖cf (ρ t) n‖)]
        _ ≤ bound n := by simp only [bound]; linarith)
  simp only [tsum_zero] at hlim
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun s hs => (hP s hs).symm)

end LinMild

end SharpLSI
