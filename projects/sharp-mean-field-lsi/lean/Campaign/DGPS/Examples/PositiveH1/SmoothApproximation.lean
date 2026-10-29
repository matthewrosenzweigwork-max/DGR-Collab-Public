import DGPS.Examples.PositiveH1.Dissipation
import DGPS.Analysis.PeriodicHeatKernel
import DGPS.Foundations.WeakContractions
import DGPS.Foundations.CompactSobolev

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Convolution
open DGPS.Examples.PositiveH1.Nonlinear

namespace DGPS.Examples.PositiveH1.SmoothApproximation

theorem h1015_integrable_box {f : Torus 1 → ℝ} (hf : Integrable f (haar 1)) :
    Integrable (fun s : Fin 1 → ℝ => (SharpLSI.unitBox (Fin 1)).indicator (fun s => f (torusLift s)) s) volume := by
  have h1 : Integrable f (((volume : Measure (Fin 1 → ℝ)).restrict (SharpLSI.unitBox (Fin 1))).map torusLift) := by
    rw [← haar_eq_map_unitBox]; exact hf
  have h2 := (integrable_map_measure (by rw [← haar_eq_map_unitBox]; exact hf.aestronglyMeasurable) SharpLSI.measurable_liftT.aemeasurable).mp h1
  have hm : MeasurableSet (SharpLSI.unitBox (Fin 1)) := by
    unfold SharpLSI.unitBox
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc
  exact (integrable_indicator_iff hm).mpr h2

theorem h1015_heatOp_smooth {t : ℝ} (ht : 0 < t) {f : Torus 1 → ℝ} (hf : Integrable f (haar 1)) :
    IsSmoothPeriodic (heatOp t f) := by
  unfold IsSmoothPeriodic
  set F : (Fin 1 → ℝ) → ℝ := (SharpLSI.unitBox (Fin 1)).indicator (fun s => f (torusLift s)) with hFdef
  have hF : Integrable F volume := h1015_integrable_box hf
  set k : (Fin 1 → ℝ) → ℝ := fun x => heatKernelT t (torusLift x) with hk
  have hkd : ContDiff ℝ ∞ k := isSmoothPeriodic_heatKernelT ht
  have heq : (heatOp t f ∘ torusLift) = fun x => (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] k) x := by
    funext x
    simp only [Function.comp, heatOp, torusConv, convolution_def, ContinuousLinearMap.mul_apply']
    have hKc : Continuous (heatKernelT (d := 1) t) := continuous_heatKernelT ht
    rw [integral_torus_eq_box' (integrable_conv_integrand hKc hf _).aestronglyMeasurable]
    have hm : MeasurableSet (SharpLSI.unitBox (Fin 1)) := by
      unfold SharpLSI.unitBox
      exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc
    rw [← integral_indicator hm]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hFdef, hk, indicator]
    by_cases hs : s ∈ SharpLSI.unitBox (Fin 1)
    · simp only [hs, ite_true, SharpLSI.liftT_sub]; ring
    · simp [hs]
  rw [heq, contDiff_iff_contDiffAt]
  intro x₀
  set M : ℝ := ‖x₀‖ + 2 with hM
  let χ : ContDiffBump (0 : Fin 1 → ℝ) := ⟨M, M + 1, by positivity, by linarith⟩
  have hk' : ContDiff ℝ ∞ (fun x => χ x • k x) := χ.contDiff.smul hkd
  have hcs : HasCompactSupport (fun x => χ x • k x) :=
    χ.hasCompactSupport.smul_right
  have hsm : ContDiff ℝ ∞ (F ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun x => χ x • k x)) :=
    hcs.contDiff_convolution_right _ hF.locallyIntegrable hk'
  refine hsm.contDiffAt.congr_of_eventuallyEq ?_
  have hball : Metric.ball x₀ 1 ∈ 𝓝 x₀ := Metric.ball_mem_nhds _ one_pos
  filter_upwards [hball] with x hx
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ SharpLSI.unitBox (Fin 1)
  · have hn : ‖x - s‖ ≤ M := by
      have h1 : ‖x‖ ≤ ‖x₀‖ + 1 := by
        have h2 : ‖x - x₀‖ < 1 := by simpa [dist_eq_norm] using hx
        calc ‖x‖ = ‖(x - x₀) + x₀‖ := by simp
          _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
          _ ≤ ‖x₀‖ + 1 := by linarith
      have h3 : ‖s‖ ≤ 1 := by
        refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
        have := hs i (mem_univ i)
        rw [Real.norm_eq_abs, abs_of_pos this.1]; exact this.2
      calc ‖x - s‖ ≤ ‖x‖ + ‖s‖ := norm_sub_le _ _
        _ ≤ M := by rw [hM]; linarith
    have : χ (x - s) = 1 := χ.one_of_mem_closedBall (by simpa using hn)
    simp [this]
  · simp [hFdef, hs]

theorem h1015_sup_real {w : Torus 1 → ℝ} {h : Torus 1 → Tangent 1} (hw : IsWeakGradient w h) :
    ∃ Ub : Torus 1 → ℝ, Ub =ᵐ[haar 1] w ∧ ∀ x, |Ub x| ≤
      (eLpNorm w 2 (haar 1)).toReal + (eLpNorm h 2 (haar 1)).toReal := by
  obtain ⟨Ub, hUc, hUae, hFTC⟩ := sobolev1 hw
  refine ⟨Ub, hUae, ?_⟩
  set q : ℝ → ℝ := fun t => h (lift1 t) 0 with hq
  have hqm : MemLp (fun x => h x 0) 2 (haar 1) := memLp_coord hw.memLp_grad 0
  have hqint : IntegrableOn q (Ioc (0:ℝ) 1) := by
    have := (integrable_haar1_iff (F := fun x => h x 0) hqm.aestronglyMeasurable).1
      (hqm.integrable (by norm_num))
    exact this
  have hq1 : ∫ t in (0:ℝ)..1, |q t| ≤ (eLpNorm h 2 (haar 1)).toReal := by
    have e := integral_haar1 (F := fun x => |h x 0|) hqm.aestronglyMeasurable.norm
    have e2 : ∫ t in (0:ℝ)..1, |q t| = ∫ x, |h x 0| ∂haar 1 := by
      rw [e]
    rw [e2]
    refine (integral_abs_le_eLpNorm hqm).trans ?_
    refine ENNReal.toReal_mono hw.memLp_grad.eLpNorm_ne_top (eLpNorm_mono hqm.aestronglyMeasurable fun x => ?_)
    simpa using PiLp.norm_apply_le (h x) 0
  have hUcc : Continuous fun t => Ub (lift1 t) := hUc.comp continuous_lift1
  have hosc : ∀ s ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) 1,
      |Ub (lift1 r) - Ub (lift1 s)| ≤ ∫ x in (0:ℝ)..1, |q x| := by
    intro s hs r hr
    rw [hFTC s r]
    have h2 := intervalIntegral.norm_integral_le_integral_norm_uIoc (a := s) (b := r)
      (f := q) (μ := volume)
    rw [Real.norm_eq_abs] at h2
    refine h2.trans ?_
    simp only [Real.norm_eq_abs]
    rw [intervalIntegral.integral_of_le zero_le_one]
    refine setIntegral_mono_set hqint.abs (Eventually.of_forall fun x => abs_nonneg _) ?_
    refine (LE.le.eventuallySubset ?_)
    intro x hx
    simp only [Set.uIoc, mem_Ioc] at hx ⊢
    exact ⟨lt_of_le_of_lt (le_min hs.1 hr.1) hx.1, hx.2.trans (max_le hs.2 hr.2)⟩
  have hB : ∫ s in (0:ℝ)..1, |Ub (lift1 s)| ≤ (eLpNorm w 2 (haar 1)).toReal := by
    have e := integral_haar1 (F := fun x => |Ub x|) hUc.aestronglyMeasurable.norm
    have e2 : ∫ s in (0:ℝ)..1, |Ub (lift1 s)| = ∫ x, |w x| ∂haar 1 := by
      rw [← e]
      exact integral_congr_ae (hUae.mono fun x hx => by simp [hx])
    rw [e2]
    exact integral_abs_le_eLpNorm hw.memLp
  intro x
  obtain ⟨t, rfl⟩ := lift1_exists x
  have ht : lift1 t = lift1 (Int.fract t) := by
    have := periodic_lift1.sub_int_mul_eq (x := t) ⌊t⌋
    rw [mul_one] at this
    rw [Int.fract]; exact this.symm
  rw [ht]
  set r := Int.fract t with hr
  have hr01 : r ∈ Icc (0:ℝ) 1 := ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hsplit : Ub (lift1 r) = (∫ s in (0:ℝ)..1, (Ub (lift1 r) - Ub (lift1 s))) +
      ∫ s in (0:ℝ)..1, Ub (lift1 s) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hUcc.intervalIntegrable _ _)]
    simp
  have hA : |∫ s in (0:ℝ)..1, (Ub (lift1 r) - Ub (lift1 s))| ≤ ∫ x in (0:ℝ)..1, |q x| := by
    refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
    refine (intervalIntegral.integral_mono_on zero_le_one
      ((continuous_const.sub hUcc).abs.intervalIntegrable _ _) intervalIntegrable_const
      (fun s hs => hosc s hs r hr01)).trans ?_
    simp
  have hB' : |∫ s in (0:ℝ)..1, Ub (lift1 s)| ≤ ∫ s in (0:ℝ)..1, |Ub (lift1 s)| :=
    intervalIntegral.abs_integral_le_integral_abs zero_le_one
  rw [hsplit]
  calc _ ≤ |∫ s in (0:ℝ)..1, (Ub (lift1 r) - Ub (lift1 s))| + |∫ s in (0:ℝ)..1, Ub (lift1 s)| :=
        abs_add_le _ _
    _ ≤ _ := by linarith

theorem h1015_eLpNorm_top_le {w : Torus 1 → ℝ} {h : Torus 1 → Tangent 1}
    (hw : IsWeakGradient w h) :
    eLpNorm w ⊤ (haar 1) ≤ eLpNorm w 2 (haar 1) + eLpNorm h 2 (haar 1) := by
  obtain ⟨Ub, hae, hb⟩ := h1015_sup_real hw
  rw [eLpNorm_exponent_top hw.memLp.aestronglyMeasurable, eLpNormEssSup_congr_ae hae.symm]
  refine (eLpNormEssSup_le_of_ae_bound (C := (eLpNorm w 2 (haar 1)).toReal + (eLpNorm h 2 (haar 1)).toReal)
    (Eventually.of_forall fun x => by simpa using hb x)).trans ?_
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hw.memLp.eLpNorm_ne_top, ENNReal.ofReal_toReal hw.memLp_grad.eLpNorm_ne_top]

theorem h1015_smul_tendsto {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    (hr : 1 ≤ r) (hq : 1 ≤ q)
    {φ : ℕ → α → ℝ} {φ₀ : α → ℝ} {f : ℕ → α → E} {f₀ : α → E}
    (hφ₀ : eLpNorm φ₀ p μ ≠ ⊤) (hf₀ : eLpNorm f₀ q μ ≠ ⊤)
    (hφ : Tendsto (fun j => eLpNorm (φ j - φ₀) p μ) atTop (𝓝 0))
    (hf : Tendsto (fun j => eLpNorm (f j - f₀) q μ) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (φ j • f j - φ₀ • f₀) r μ) atTop (𝓝 0) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbound : ∀ j, eLpNorm (φ j • f j - φ₀ • f₀) r μ ≤
      eLpNorm (φ j - φ₀) p μ * (eLpNorm f₀ q μ + eLpNorm (f j - f₀) q μ) +
        eLpNorm φ₀ p μ * eLpNorm (f j - f₀) q μ := by
    intro j
    have e : φ j • f j - φ₀ • f₀ = (φ j - φ₀) • f j + φ₀ • (f j - f₀) := by
      funext x; simp [sub_smul, smul_sub]
    rw [e]
    refine (eLpNorm_add_le hr).trans ?_
    refine add_le_add ?_ ?_
    · refine (eLpNorm_smul_le_mul_eLpNorm_of_pos (p := p) (q := q) hrpos).trans ?_
      refine mul_le_mul_right ?_ _
      have e2 : f j = f₀ + (f j - f₀) := by funext x; simp
      calc eLpNorm (f j) q μ = eLpNorm (f₀ + (f j - f₀)) q μ := by rw [← e2]
        _ ≤ _ := eLpNorm_add_le hq
    · exact eLpNorm_smul_le_mul_eLpNorm_of_pos (p := p) (q := q) hrpos
  have hlim : Tendsto (fun j => eLpNorm (φ j - φ₀) p μ * (eLpNorm f₀ q μ + eLpNorm (f j - f₀) q μ) +
        eLpNorm φ₀ p μ * eLpNorm (f j - f₀) q μ) atTop (𝓝 0) := by
    have h1 : Tendsto (fun j => eLpNorm f₀ q μ + eLpNorm (f j - f₀) q μ) atTop (𝓝 (eLpNorm f₀ q μ + 0)) :=
      tendsto_const_nhds.add hf
    have h2 := ENNReal.Tendsto.mul hφ (Or.inr (by simpa using hf₀)) h1 (Or.inr (by simp))
    have h3 := ENNReal.Tendsto.mul (tendsto_const_nhds (x := eLpNorm φ₀ p μ)) (Or.inr (by simp)) hf
      (Or.inr hφ₀)
    simpa using h2.add h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hbound

abbrev h1015_Cvg {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (p : ℝ≥0∞) (μ : Measure α) (a : ℕ → α → E) (b : α → E) : Prop :=
  Tendsto (fun j => eLpNorm (a j - b) p μ) atTop (𝓝 0)

theorem h1015_cvg_add {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α} {a a' : ℕ → α → E} {b b' : α → E}
    (h : h1015_Cvg p μ a b) (h' : h1015_Cvg p μ a' b') :
    h1015_Cvg p μ (fun j => a j + a' j) (b + b') := by
  have := h.add h'
  rw [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le) ?_
  intro j
  have e : (fun x => a j x + a' j x) - (b + b') = (a j - b) + (a' j - b') := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply]; abel
  show eLpNorm ((fun x => a j x + a' j x) - (b + b')) p μ ≤ _
  rw [e]; exact eLpNorm_add_le hp

theorem h1015_cvg_sub {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α} {a a' : ℕ → α → E} {b b' : α → E}
    (h : h1015_Cvg p μ a b) (h' : h1015_Cvg p μ a' b') :
    h1015_Cvg p μ (fun j => a j - a' j) (b - b') := by
  have := h.add h'
  rw [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le) ?_
  intro j
  have e : (fun x => a j x - a' j x) - (b - b') = (a j - b) - (a' j - b') := by
    funext x; simp only [Pi.sub_apply]; abel
  show eLpNorm ((fun x => a j x - a' j x) - (b - b')) p μ ≤ _
  rw [e]; exact eLpNorm_sub_le hp

theorem h1015_cvg_const_smul {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {c : ℕ → ℝ} {c₀ : ℝ} {a : ℕ → α → E} {b : α → E}
    (hb : eLpNorm b p μ ≠ ⊤) (hc : Tendsto c atTop (𝓝 c₀))
    (h : h1015_Cvg p μ a b) :
    h1015_Cvg p μ (fun j => c j • a j) (c₀ • b) := by
  have hbound : ∀ j, eLpNorm (c j • a j - c₀ • b) p μ ≤
      ‖c j‖ₑ * eLpNorm (a j - b) p μ + ‖c j - c₀‖ₑ * eLpNorm b p μ := by
    intro j
    have e : c j • a j - c₀ • b = c j • (a j - b) + (c j - c₀) • b := by
      funext x; simp [sub_smul, smul_sub]
    rw [e]
    refine (eLpNorm_add_le hp).trans ?_
    rw [eLpNorm_const_smul, eLpNorm_const_smul]
  have hc1 : Tendsto (fun j => ‖c j‖ₑ) atTop (𝓝 ‖c₀‖ₑ) := hc.enorm
  have hc2 : Tendsto (fun j => ‖c j - c₀‖ₑ) atTop (𝓝 0) := by
    have := (hc.sub_const c₀).enorm
    simpa using this
  have h1 := ENNReal.Tendsto.mul hc1 (Or.inr (by simp)) h (Or.inr (by simp))
  have h2 := ENNReal.Tendsto.mul hc2 (Or.inr hb) (tendsto_const_nhds (x := eLpNorm b p μ))
    (Or.inr (by simp))
  have := h1.add h2
  simp only [mul_zero, zero_mul, add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => bot_le) hbound

theorem h1015_cvg_congr_ae {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} {μ : Measure α} {a a' : ℕ → α → E} {b b' : α → E}
    (ha : ∀ j, a j =ᵐ[μ] a' j) (hb : b =ᵐ[μ] b')
    (h : h1015_Cvg p μ a b) : h1015_Cvg p μ a' b' := by
  refine h.congr (fun j => ?_)
  refine eLpNorm_congr_ae ?_
  filter_upwards [ha j, hb] with x h1 h2
  simp [h1, h2]

theorem h1015_cvg_mono {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p q : ℝ≥0∞} (hpq : p ≤ q) {μ : Measure α} [IsProbabilityMeasure μ]
    {a : ℕ → α → E} {b : α → E}
    (h : h1015_Cvg q μ a b) : h1015_Cvg p μ a b :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
    (fun _ => eLpNorm_le_eLpNorm_of_exponent_le hpq)

theorem h1015_cvg_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a : ℕ → α → ℝ} {b : α → ℝ} (hb : Integrable b μ) (ha : ∀ j, Integrable (a j) μ)
    (h : h1015_Cvg 1 μ a b) : Tendsto (fun j => ∫ x, a j x ∂μ) atTop (𝓝 (∫ x, b x ∂μ)) := by
  refine tendsto_integral_of_L1 b hb.aestronglyMeasurable (Eventually.of_forall ha) ?_
  refine h.congr (fun j => ?_)
  rw [eLpNorm_one_eq_lintegral_enorm (hf := (ha j).aestronglyMeasurable.sub hb.aestronglyMeasurable)]; rfl

theorem h1015_cvg_ae_tendsto {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {a : ℕ → α → E} {b : α → E}
    (ha : ∀ j, AEStronglyMeasurable (a j) μ) (hb : AEStronglyMeasurable b μ)
    (h : h1015_Cvg ⊤ μ a b) :
    ∀ᵐ x ∂μ, Tendsto (fun j => a j x) atTop (𝓝 (b x)) := by
  have hall : ∀ᵐ x ∂μ, ∀ j, ‖(a j - b) x‖ₑ ≤ eLpNorm (a j - b) ⊤ μ := by
    rw [ae_all_iff]
    intro j
    rw [eLpNorm_exponent_top ((ha j).sub hb)]; exact enorm_ae_le_eLpNormEssSup (a j - b) μ
  filter_upwards [hall] with x hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have : Tendsto (fun j => ‖a j x - b x‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le)
      (fun j => by simpa using hx j)
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this
  simpa [Function.comp_def, toReal_enorm] using h2

theorem h1015_cvg_norm {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α} {a : ℕ → α → E} {b : α → E}
    (hb : eLpNorm b p μ ≠ ⊤) (ha : ∀ j, eLpNorm (a j) p μ ≠ ⊤)
    (h : h1015_Cvg p μ a b) :
    Tendsto (fun j => (eLpNorm (a j) p μ).toReal) atTop (𝓝 (eLpNorm b p μ).toReal) := by
  have hz := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [Function.comp_def, ENNReal.toReal_zero] at hz
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) hz
  have hd : eLpNorm (a j - b) p μ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ha j, hb⟩) ?_
    have e : a j - b = a j + (-b) := sub_eq_add_neg _ _
    rw [e]
    refine (eLpNorm_add_le hp).trans ?_
    rw [eLpNorm_neg]
  rw [Real.dist_eq, abs_le]
  have h1 : eLpNorm (a j) p μ ≤ eLpNorm b p μ + eLpNorm (a j - b) p μ := by
    have e : a j = b + (a j - b) := by funext x; simp
    calc eLpNorm (a j) p μ = eLpNorm (b + (a j - b)) p μ := by rw [← e]
      _ ≤ _ := eLpNorm_add_le hp
  have h2 : eLpNorm b p μ ≤ eLpNorm (a j) p μ + eLpNorm (a j - b) p μ := by
    have e : b = a j - (a j - b) := by funext x; simp
    calc eLpNorm b p μ = eLpNorm (a j - (a j - b)) p μ := by rw [← e]
      _ ≤ eLpNorm (a j) p μ + eLpNorm (a j - b) p μ := eLpNorm_sub_le hp
  have hA := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hb, hd⟩) h1
  have hB := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ha j, hd⟩) h2
  rw [ENNReal.toReal_add hb hd] at hA
  rw [ENNReal.toReal_add (ha j) hd] at hB
  constructor <;> linarith

/-- Normalising constant `‖H_t u + δ‖₂`. -/
noncomputable def h1015_norm (u : Torus 1 → ℝ) (t δ : ℝ) : ℝ :=
  (eLpNorm (fun y => heatOp t u y + δ) 2 (haar 1)).toReal

/-- The normalised smoothed square root `(H_t u + δ) / ‖H_t u + δ‖₂`. -/
noncomputable def h1015_w (u : Torus 1 → ℝ) (t δ : ℝ) : Torus 1 → ℝ :=
  fun x => (heatOp t u x + δ) / h1015_norm u t δ

theorem h1015_isWeakGradient_sub {u v : Torus 1 → ℝ} {g k : Torus 1 → Tangent 1}
    (hu : IsWeakGradient u g) (hv : IsWeakGradient v k) :
    IsWeakGradient (u - v) (g - k) :=
  (hu.add (hv.smul (-1))).congr_ae (Eventually.of_forall fun x => by simp [sub_eq_add_neg])
    (Eventually.of_forall fun x => by simp [sub_eq_add_neg])

theorem h1015_memLp_v {u : Torus 1 → ℝ} (hu : MemLp u 2 (haar 1)) {t : ℝ} (ht : 0 < t) (δ : ℝ) :
    MemLp (fun y => heatOp t u y + δ) 2 (haar 1) :=
  (memLp_heatOp ht one_le_two (by simp) hu).add (memLp_const δ)

theorem h1015_heatOp_nonneg {u : Torus 1 → ℝ} (hu0 : 0 ≤ᵐ[haar 1] u) {t : ℝ} (ht : 0 < t)
    (x : Torus 1) : 0 ≤ heatOp t u x :=
  torusConv_nonneg (fun z => (heatKernelT_pos ht z).le) hu0 x

theorem h1015_norm_pos {u : Torus 1 → ℝ} (hu : MemLp u 2 (haar 1)) (hu0 : 0 ≤ᵐ[haar 1] u)
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) : 0 < h1015_norm u t δ := by
  unfold h1015_norm
  rw [DGPS.toReal_eLpNorm_two (h1015_memLp_v hu ht δ)]
  refine Real.sqrt_pos.2 ?_
  have hint : Integrable (fun x => ‖heatOp t u x + δ‖ ^ 2) (haar 1) :=
    (h1015_memLp_v hu ht δ).integrable_norm_pow (by norm_num)
  have : ∫ _x, δ ^ 2 ∂haar 1 ≤ ∫ x, ‖heatOp t u x + δ‖ ^ 2 ∂haar 1 := by
    refine integral_mono (integrable_const _) hint fun x => ?_
    have h0 := h1015_heatOp_nonneg hu0 ht x
    rw [Real.norm_eq_abs, sq_abs]
    exact pow_le_pow_left₀ hδ.le (by linarith) 2
  simp at this
  exact lt_of_lt_of_le (by positivity) this

theorem h1015_norm_sq {u : Torus 1 → ℝ} (hu : MemLp u 2 (haar 1)) {t : ℝ} (ht : 0 < t) (δ : ℝ) :
    h1015_norm u t δ ^ 2 = ∫ x, (heatOp t u x + δ) ^ 2 ∂haar 1 := by
  unfold h1015_norm
  rw [DGPS.toReal_eLpNorm_two (h1015_memLp_v hu ht δ)]
  rw [Real.sq_sqrt (integral_nonneg fun x => by positivity)]

theorem h1015_w_mass {u : Torus 1 → ℝ} (hu : MemLp u 2 (haar 1)) (hu0 : 0 ≤ᵐ[haar 1] u)
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) : ∫ x, h1015_w u t δ x ^ 2 ∂haar 1 = 1 := by
  have hN := h1015_norm_pos hu hu0 ht hδ
  unfold h1015_w
  simp_rw [div_pow]
  rw [integral_div, ← h1015_norm_sq hu ht δ]
  field_simp

theorem h1015_w_pos {u : Torus 1 → ℝ} (hu : MemLp u 2 (haar 1)) (hu0 : 0 ≤ᵐ[haar 1] u)
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (x : Torus 1) : 0 < h1015_w u t δ x :=
  div_pos (by linarith [h1015_heatOp_nonneg hu0 ht x]) (h1015_norm_pos hu hu0 ht hδ)

theorem h1015_w_grad {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1} (hg : IsWeakGradient u g)
    {t : ℝ} (ht : 0 < t) (δ : ℝ) :
    IsWeakGradient (h1015_w u t δ) (fun x => (h1015_norm u t δ)⁻¹ • heatGrad t g x) :=
  (((hg.heatOp ht).add (isWeakGradient_const δ)).smul (h1015_norm u t δ)⁻¹).congr_ae
    (Eventually.of_forall fun x => by simp [h1015_w, div_eq_inv_mul])
    (Eventually.of_forall fun x => by simp)

theorem h1015_w_smooth {u : Torus 1 → ℝ} (hu : MemLp u 2 (haar 1)) {t : ℝ} (ht : 0 < t) (δ : ℝ) :
    IsSmoothPeriodic (h1015_w u t δ) := by
  have h := h1015_heatOp_smooth ht (hu.integrable one_le_two)
  unfold IsSmoothPeriodic at h ⊢
  exact (h.add contDiff_const).div_const _

theorem h1015_cvg_const {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} (hp : p ≠ 0) {δ : ℕ → ℝ} {c₀ : ℝ} (h : Tendsto δ atTop (𝓝 c₀)) :
    h1015_Cvg p μ (fun j _ => δ j) (fun _ => c₀) := by
  have e : ∀ j, ((fun _ : α => δ j) - fun _ => c₀) = fun _ => δ j - c₀ := fun j => rfl
  show Tendsto (fun j => eLpNorm ((fun _ : α => δ j) - fun _ => c₀) p μ) atTop (𝓝 0)
  simp only [e]
  have : ∀ j, eLpNorm (fun _ : α => δ j - c₀) p μ = ‖δ j - c₀‖ₑ := fun j => by
    rw [eLpNorm_const _ hp (NeZero.ne μ)]; simp
  simp only [this]
  simpa using (h.sub_const c₀).enorm

theorem h1015_cvg_heatOp {u : Torus 1 → ℝ} (hu : MemLp u 2 (haar 1)) {t : ℕ → ℝ}
    (ht : ∀ j, 0 < t j) (ht0 : Tendsto t atTop (𝓝 0)) :
    h1015_Cvg 2 (haar 1) (fun j => heatOp (t j) u) u :=
  (tendsto_eLpNorm_two_heatOp_sub hu).comp (tendsto_nhdsWithin_iff.2 ⟨ht0, Eventually.of_forall ht⟩)

theorem h1015_eLpNorm_two_eq_ofReal_sqrt {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {F : α → E} (hF : MemLp F 2 μ) :
    eLpNorm F 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, ‖F x‖ ^ 2 ∂μ)) := by
  rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  norm_num

theorem h1015_heatGrad_tendsto {g : Torus 1 → Tangent 1} (hg : MemLp g 2 (haar 1)) :
    Tendsto (fun t : ℝ => eLpNorm (fun y => heatGrad t g y - g y) 2 (haar 1)) (𝓝[>] 0) (𝓝 0) := by
  have key := ENNReal.tendsto_ofReal (tendsto_integral_norm_sq_heatGrad_sub hg).sqrt
  rw [Real.sqrt_zero, ENNReal.ofReal_zero] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (h1015_eLpNorm_two_eq_ofReal_sqrt ((memLp_heatGrad ht hg).sub hg)).symm

theorem h1015_cvg_heatGrad {g : Torus 1 → Tangent 1} (hg : MemLp g 2 (haar 1)) {t : ℕ → ℝ}
    (ht : ∀ j, 0 < t j) (ht0 : Tendsto t atTop (𝓝 0)) :
    h1015_Cvg 2 (haar 1) (fun j => heatGrad (t j) g) g :=
  (h1015_heatGrad_tendsto hg).comp (tendsto_nhdsWithin_iff.2 ⟨ht0, Eventually.of_forall ht⟩)

theorem h1015_single_cvg {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1} (hg : IsWeakGradient u g)
    (hu1 : ∫ x, u x ^ 2 ∂haar 1 = 1) {t δ : ℕ → ℝ} (ht : ∀ j, 0 < t j) (ht0 : Tendsto t atTop (𝓝 0))
    (hδ0 : Tendsto δ atTop (𝓝 0)) :
    h1015_Cvg 2 (haar 1) (fun j => h1015_w u (t j) (δ j)) u ∧
    h1015_Cvg 2 (haar 1) (fun j x => (h1015_norm u (t j) (δ j))⁻¹ • heatGrad (t j) g x) g ∧
    h1015_Cvg ⊤ (haar 1) (fun j => h1015_w u (t j) (δ j)) u := by
  have hu := hg.memLp
  have hv : h1015_Cvg 2 (haar 1) (fun j y => heatOp (t j) u y + δ j) u := by
    have := h1015_cvg_add one_le_two (h1015_cvg_heatOp hu ht ht0)
      (h1015_cvg_const (μ := haar 1) (p := 2) (by norm_num) hδ0)
    refine h1015_cvg_congr_ae (fun j => Filter.EventuallyEq.rfl) (Eventually.of_forall fun x => ?_) this
    simp
  have hN : Tendsto (fun j => (h1015_norm u (t j) (δ j))⁻¹) atTop (𝓝 1) := by
    have h1 := h1015_cvg_norm one_le_two hu.eLpNorm_ne_top
      (fun j => (h1015_memLp_v hu (ht j) (δ j)).eLpNorm_ne_top) hv
    have h2 : (eLpNorm u 2 (haar 1)).toReal = 1 := by
      rw [DGPS.toReal_eLpNorm_two hu]; simp [hu1]
    rw [h2] at h1
    simpa [h1015_norm] using h1.inv₀ one_ne_zero
  have hw : h1015_Cvg 2 (haar 1) (fun j => h1015_w u (t j) (δ j)) u := by
    have := h1015_cvg_const_smul one_le_two hu.eLpNorm_ne_top hN hv
    refine h1015_cvg_congr_ae (fun j => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => by simp) this
    simp [h1015_w, div_eq_inv_mul]
  have hG : h1015_Cvg 2 (haar 1) (fun j x => (h1015_norm u (t j) (δ j))⁻¹ • heatGrad (t j) g x) g := by
    have := h1015_cvg_const_smul one_le_two hg.memLp_grad.eLpNorm_ne_top hN
      (h1015_cvg_heatGrad hg.memLp_grad ht ht0)
    refine h1015_cvg_congr_ae (fun j => Filter.EventuallyEq.rfl) (Eventually.of_forall fun x => by simp) this
  refine ⟨hw, hG, ?_⟩
  have hsum := hw.add hG
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => bot_le) fun j => ?_
  exact h1015_eLpNorm_top_le (h1015_isWeakGradient_sub (h1015_w_grad hg (ht j) (δ j)) hg)

theorem h1015_cvg_sum {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α} (s : Finset ι) {a : ι → ℕ → α → E} {b : ι → α → E}
    (h : ∀ i ∈ s, h1015_Cvg p μ (a i) (b i)) :
    h1015_Cvg p μ (fun j x => ∑ i ∈ s, a i j x) (fun x => ∑ i ∈ s, b i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : (fun _ : ℕ => eLpNorm ((fun _ : α => (0 : E)) - fun _ => 0) p μ) = fun _ => 0 := by
      funext j; simp
    show Tendsto (fun _ : ℕ => eLpNorm ((fun _ : α => (0 : E)) - fun _ => 0) p μ) atTop (𝓝 0)
    rw [this]; exact tendsto_const_nhds
  | insert i s hi ih =>
    have h1 := h1015_cvg_add hp (h i (Finset.mem_insert_self _ _))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
    refine h1015_cvg_congr_ae (fun j => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_) h1
    · simp [Finset.sum_insert hi]
    · simp [Finset.sum_insert hi]

theorem h1015_cvg_coord {μ : Measure (Torus 1)} {a : ℕ → Torus 1 → Tangent 1} {b : Torus 1 → Tangent 1}
    (ha : ∀ j, AEStronglyMeasurable (a j) μ) (hb : AEStronglyMeasurable b μ)
    (h : h1015_Cvg 2 μ a b) :
    h1015_Cvg 2 μ (fun j x => a j x 0) (fun x => b x 0) := by
  have hc : Continuous (fun v : Tangent 1 => v 0) := (EuclideanSpace.proj (0 : Fin 1)).continuous
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le) fun j => ?_
  refine eLpNorm_mono (((hc.comp_aestronglyMeasurable (ha j)).sub (hc.comp_aestronglyMeasurable hb))) fun x => ?_
  simp only [Pi.sub_apply]
  rw [← PiLp.sub_apply]
  exact PiLp.norm_apply_le _ _

theorem h1015_integral_norm_sq_eq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {F : α → E} (hF : MemLp F 2 μ) :
    ∫ x, ‖F x‖ ^ 2 ∂μ = (eLpNorm F 2 μ).toReal ^ 2 := by
  rw [h1015_eLpNorm_two_eq_ofReal_sqrt hF, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Real.sq_sqrt (integral_nonneg fun x => by positivity)]

theorem h1015_cvg_integral_norm_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {a : ℕ → α → E} {b : α → E} (ha : ∀ j, MemLp (a j) 2 μ) (hb : MemLp b 2 μ)
    (h : h1015_Cvg 2 μ a b) :
    Tendsto (fun j => ∫ x, ‖a j x‖ ^ 2 ∂μ) atTop (𝓝 (∫ x, ‖b x‖ ^ 2 ∂μ)) := by
  simp_rw [h1015_integral_norm_sq_eq (ha _), h1015_integral_norm_sq_eq hb]
  exact (h1015_cvg_norm one_le_two hb.eLpNorm_ne_top (fun j => (ha j).eLpNorm_ne_top) h).pow 2

theorem h1015_cvg_integral_comp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {Φ : ℝ → ℝ} (hΦ : Continuous Φ) {a : ℕ → α → ℝ} {b : α → ℝ}
    (ha : ∀ j, AEStronglyMeasurable (a j) μ) (hb : AEStronglyMeasurable b μ)
    (hbt : eLpNorm b ⊤ μ ≠ ⊤) (h : h1015_Cvg ⊤ μ a b) :
    Tendsto (fun j => ∫ x, Φ (a j x) ∂μ) atTop (𝓝 (∫ x, Φ (b x) ∂μ)) := by
  set B : ℝ≥0∞ := eLpNorm b ⊤ μ + 1 with hB
  have hBt : B ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hbt, ENNReal.one_ne_top⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ) B.toReal).exists_bound_of_continuousOn hΦ.continuousOn
  have hev : ∀ᶠ j in atTop, eLpNorm (a j - b) ⊤ μ ≤ 1 :=
    (h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))).mono fun j hj => hj.le
  have hlim := h1015_cvg_ae_tendsto ha hb h
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) (Eventually.of_forall fun j =>
    hΦ.comp_aestronglyMeasurable (ha j)) ?_ (integrable_const C) ?_
  · filter_upwards [hev] with j hj
    have h1 : ∀ᵐ x ∂μ, ‖b x‖ₑ ≤ eLpNorm b ⊤ μ := by
      rw [eLpNorm_exponent_top hb]; exact enorm_ae_le_eLpNormEssSup b μ
    have h2 : ∀ᵐ x ∂μ, ‖(a j - b) x‖ₑ ≤ eLpNorm (a j - b) ⊤ μ := by
      rw [eLpNorm_exponent_top ((ha j).sub hb)]; exact enorm_ae_le_eLpNormEssSup (a j - b) μ
    filter_upwards [h1, h2] with x hx1 hx2
    have h3 : ‖a j x‖ₑ ≤ B := by
      calc ‖a j x‖ₑ = ‖b x + (a j - b) x‖ₑ := by simp
        _ ≤ ‖b x‖ₑ + ‖(a j - b) x‖ₑ := enorm_add_le _ _
        _ ≤ eLpNorm b ⊤ μ + 1 := add_le_add hx1 (hx2.trans hj)
    have h4 : ‖a j x‖ ≤ B.toReal := by
      have := ENNReal.toReal_mono hBt h3
      simpa [toReal_enorm] using this
    exact hC _ (by simpa using h4)
  · filter_upwards [hlim] with x hx
    exact (hΦ.tendsto _).comp hx

/-- Convergence data for a sequence of densities: square roots in `L²` and `L^∞`, gradients in `L²`. -/
structure h1015_Conv (ρ : ℕ → AbsoluteDensity 1) (ρ0 : AbsoluteDensity 1) : Prop where
  sqrt2 : h1015_Cvg 2 (haar 1) (fun j => (ρ j).sqrt) ρ0.sqrt
  sqrtTop : h1015_Cvg ⊤ (haar 1) (fun j => (ρ j).sqrt) ρ0.sqrt
  grad2 : h1015_Cvg 2 (haar 1) (fun j => weakGradient (ρ j).sqrt (ρ j).sqrt_mem)
    (weakGradient ρ0.sqrt ρ0.sqrt_mem)

theorem h1015_sqrt_top_ne (ρ : AbsoluteDensity 1) : eLpNorm ρ.sqrt ⊤ (haar 1) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2
    ⟨(isWeakGradient_weakGradient ρ.sqrt_mem).memLp.eLpNorm_ne_top,
      (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad.eLpNorm_ne_top⟩)
    (h1015_eLpNorm_top_le (isWeakGradient_weakGradient ρ.sqrt_mem))

theorem h1015_memLp_sqrt_top (ρ : AbsoluteDensity 1) : MemLp ρ.sqrt ⊤ (haar 1) :=
  lt_top_iff_ne_top.2 (h1015_sqrt_top_ne ρ)

theorem h1015_density_top_ne (ρ : AbsoluteDensity 1) : eLpNorm ρ.density ⊤ (haar 1) ≠ ⊤ := by
  have h := MemLp.mul (p := ⊤) (q := ⊤) (r := ⊤) (h1015_memLp_sqrt_top ρ) (h1015_memLp_sqrt_top ρ)
  refine (h.ae_eq (Eventually.of_forall fun x => ?_)).eLpNorm_ne_top
  simp [AbsoluteDensity.density, sq]

theorem h1015_dens_top {ρ : ℕ → AbsoluteDensity 1} {ρ0 : AbsoluteDensity 1} (h : h1015_Conv ρ ρ0) :
    h1015_Cvg ⊤ (haar 1) (fun j => (ρ j).density) ρ0.density := by
  have := h1015_smul_tendsto (p := ⊤) (q := ⊤) (r := ⊤) le_top le_top (h1015_sqrt_top_ne ρ0)
    (h1015_sqrt_top_ne ρ0) h.sqrtTop h.sqrtTop
  refine h1015_cvg_congr_ae (fun j => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_) this
  · simp [AbsoluteDensity.density, sq]
  · simp [AbsoluteDensity.density, sq]

theorem h1015_dens_two {ρ : ℕ → AbsoluteDensity 1} {ρ0 : AbsoluteDensity 1} (h : h1015_Conv ρ ρ0) :
    h1015_Cvg 2 (haar 1) (fun j => (ρ j).density) ρ0.density := by
  have := h1015_smul_tendsto (p := ⊤) (q := 2) (r := 2) one_le_two one_le_two (h1015_sqrt_top_ne ρ0)
    ρ0.memLp_sqrt.eLpNorm_ne_top h.sqrtTop h.sqrt2
  refine h1015_cvg_congr_ae (fun j => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_) this
  · simp [AbsoluteDensity.density, sq]
  · simp [AbsoluteDensity.density, sq]

theorem h1015_deriv_two {ρ : ℕ → AbsoluteDensity 1} {ρ0 : AbsoluteDensity 1} (h : h1015_Conv ρ ρ0) :
    h1015_Cvg 2 (haar 1) (fun j => densityDeriv (ρ j)) (densityDeriv ρ0) := by
  have hφ := h1015_cvg_const_smul (c := fun _ : ℕ => (2 : ℝ)) (c₀ := 2) le_top
    (h1015_sqrt_top_ne ρ0) tendsto_const_nhds h.sqrtTop
  have hf := h1015_cvg_coord
    (fun j => (isWeakGradient_weakGradient (ρ j).sqrt_mem).memLp_grad.aestronglyMeasurable)
    (isWeakGradient_weakGradient ρ0.sqrt_mem).memLp_grad.aestronglyMeasurable h.grad2
  have h2 : eLpNorm ((2 : ℝ) • ρ0.sqrt) ⊤ (haar 1) ≠ ⊤ := by
    rw [eLpNorm_const_smul]
    exact ENNReal.mul_ne_top (by simp) (h1015_sqrt_top_ne ρ0)
  have hf0 : eLpNorm (fun x => weakGradient ρ0.sqrt ρ0.sqrt_mem x 0) 2 (haar 1) ≠ ⊤ :=
    (memLp_coord (isWeakGradient_weakGradient ρ0.sqrt_mem).memLp_grad 0).eLpNorm_ne_top
  have := h1015_smul_tendsto (p := ⊤) (q := 2) (r := 2) one_le_two one_le_two h2 hf0 hφ hf
  refine h1015_cvg_congr_ae (fun j => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_) this
  · simp [densityDeriv]
  · simp [densityDeriv]

theorem h1015_entropy_tendsto {ρ : ℕ → AbsoluteDensity 1} {ρ0 : AbsoluteDensity 1}
    (h : h1015_Conv ρ ρ0) :
    Tendsto (fun j => (relativeEntropy (densityMeasure (ρ j)) (haar 1)).toReal) atTop
      (𝓝 (relativeEntropy (densityMeasure ρ0) (haar 1)).toReal) := by
  simp_rw [(absoluteDensity_entropy_finite _).2.2.2]
  exact h1015_cvg_integral_comp (Φ := fun x => x * Real.log x) Real.continuous_mul_log
    (fun j => ((ρ j).memLp_sqrt.aestronglyMeasurable.pow 2)) (ρ0.memLp_sqrt.aestronglyMeasurable.pow 2)
    (h1015_density_top_ne ρ0) (h1015_dens_top h)

theorem h1015_gradnorm_tendsto {ρ : ℕ → AbsoluteDensity 1} {ρ0 : AbsoluteDensity 1}
    (h : h1015_Conv ρ ρ0) :
    Tendsto (fun j => ∫ x, ‖weakGradient (ρ j).sqrt (ρ j).sqrt_mem x‖ ^ 2 ∂haar 1) atTop
      (𝓝 (∫ x, ‖weakGradient ρ0.sqrt ρ0.sqrt_mem x‖ ^ 2 ∂haar 1)) :=
  h1015_cvg_integral_norm_sq (fun j => (isWeakGradient_weakGradient (ρ j).sqrt_mem).memLp_grad)
    (isWeakGradient_weakGradient ρ0.sqrt_mem).memLp_grad h.grad2

open DGPS DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model
  DGPS.Examples.PositiveH1.CrossTerm

theorem h1015_memLp_dens_two (σ : AbsoluteDensity 1) : MemLp σ.density 2 (haar 1) :=
  lt_top_iff_ne_top.2 (ne_top_of_le_ne_top (h1015_density_top_ne σ)
    (eLpNorm_le_eLpNorm_of_exponent_le le_top))

theorem h1015_fourier_tendsto {a : ℕ → Torus 1 → ℝ} {b : Torus 1 → ℝ}
    (ha : ∀ j, MemLp (a j) 2 (haar 1)) (hb : MemLp b 2 (haar 1))
    (h : h1015_Cvg 2 (haar 1) a b) (k : Fin 1 → ℤ) :
    Tendsto (fun j => fourierCoeff (a j) k) atTop (𝓝 (fourierCoeff b k)) := by
  have hz := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [Function.comp_def, ENNReal.toReal_zero] at hz
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hz
  have hm : MemLp (fun x => a j x - b x) 2 (haar 1) := (ha j).sub hb
  have h1 := DGPS.norm_sq_fourierCoeff_le hm k
  rw [DGPS.fourierCoeff_sub' (ha j) hb k] at h1
  have h2 : ∫ x, (a j x - b x) ^ 2 ∂haar 1 = (eLpNorm (a j - b) 2 (haar 1)).toReal ^ 2 := by
    rw [← h1015_integral_norm_sq_eq (F := a j - b) hm]
    simp [Real.norm_eq_abs, sq_abs]
  rw [h2] at h1
  exact le_of_sq_le_sq h1 ENNReal.toReal_nonneg


theorem h1015_P_tendsto {σ : ℕ → AbsoluteDensity 1} {σ0 : AbsoluteDensity 1}
    (h : h1015_Cvg 2 (haar 1) (fun j => (σ j).density) σ0.density) :
    Tendsto (fun j => P (σ j)) atTop (𝓝 (P σ0)) := by
  have hn := h1015_cvg_norm one_le_two (h1015_memLp_dens_two σ0).eLpNorm_ne_top
    (fun j => (h1015_memLp_dens_two (σ j)).eLpNorm_ne_top) h
  obtain ⟨K, hK⟩ := hn.bddAbove_range
  have hK' : ∀ j, (eLpNorm (σ j).density 2 (haar 1)).toReal ≤ K := fun j => hK ⟨j, rfl⟩
  unfold P
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => a n * K ^ 2)
    (a_summable.mul_right _) (fun n => ?_) (Eventually.of_forall fun j n => ?_)
  · have := h1015_fourier_tendsto (fun j => h1015_memLp_dens_two (σ j)) (h1015_memLp_dens_two σ0)
      h (freq n)
    exact (this.norm.pow 2).const_mul _
  · have h1 := DGPS.norm_sq_fourierCoeff_le (h1015_memLp_dens_two (σ j)) (freq n)
    have h2 : ∫ x, (σ j).density x ^ 2 ∂haar 1
        = (eLpNorm (σ j).density 2 (haar 1)).toReal ^ 2 := by
      rw [← h1015_integral_norm_sq_eq (h1015_memLp_dens_two (σ j))]
      simp [Real.norm_eq_abs, sq_abs]
    rw [h2] at h1
    have h3 : (eLpNorm (σ j).density 2 (haar 1)).toReal ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg (hK' j) 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (a_nonneg n) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (h1.trans h3) (a_nonneg n)

theorem h1015_conv_sub {f g : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1)) (hg : MemLp g 2 (haar 1))
    (x : Torus 1) : conv dR f x - conv dR g x = conv dR (fun y => f y - g y) x := by
  unfold conv
  rw [← integral_sub]
  · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [mul_sub]
  · exact memLp_dR.integrable_mul (memLp_sub_left hf x)
  · exact memLp_dR.integrable_mul (memLp_sub_left hg x)

theorem h1015_conv_top_ne (σ : AbsoluteDensity 1) : eLpNorm (conv dR σ.density) ⊤ (haar 1) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((eLpNorm_exponent_top (continuous_driftField σ).aestronglyMeasurable).symm ▸ eLpNormEssSup_le_of_ae_bound
      (C := Real.sqrt (∫ y, dR y ^ 2 ∂haar 1) * Real.sqrt (∫ y, σ.density y ^ 2 ∂haar 1))
      (Eventually.of_forall fun x => ?_))
  rw [Real.norm_eq_abs]
  exact conv_bound memLp_dR (h1015_memLp_dens_two σ) x

theorem h1015_conv_cvg {σ : ℕ → AbsoluteDensity 1} {σ0 : AbsoluteDensity 1}
    (h : h1015_Cvg 2 (haar 1) (fun j => (σ j).density) σ0.density) :
    h1015_Cvg ⊤ (haar 1) (fun j => conv dR (σ j).density) (conv dR σ0.density) := by
  set R := Real.sqrt (∫ y, dR y ^ 2 ∂haar 1)
  have hz := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [Function.comp_def, ENNReal.toReal_zero] at hz
  have hz2 : Tendsto (fun j => ENNReal.ofReal (R * (eLpNorm ((σ j).density - σ0.density) 2
      (haar 1)).toReal)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hz.const_mul R)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz2 (fun _ => bot_le)
    (fun j => ?_)
  show eLpNorm (conv dR (σ j).density - conv dR σ0.density) ⊤ (haar 1) ≤ _
  rw [eLpNorm_exponent_top ((continuous_driftField (σ j)).aestronglyMeasurable.sub
    (continuous_driftField σ0).aestronglyMeasurable)]
  refine eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => ?_)
  have hm : MemLp (fun y => (σ j).density y - σ0.density y) 2 (haar 1) :=
    (h1015_memLp_dens_two (σ j)).sub (h1015_memLp_dens_two σ0)
  have := conv_bound memLp_dR hm x
  have h2 : ∫ y, ((σ j).density y - σ0.density y) ^ 2 ∂haar 1
      = (eLpNorm ((σ j).density - σ0.density) 2 (haar 1)).toReal ^ 2 := by
    rw [← h1015_integral_norm_sq_eq (F := (σ j).density - σ0.density) hm]
    simp [Real.norm_eq_abs, sq_abs]
  rw [h2, Real.sqrt_sq ENNReal.toReal_nonneg] at this
  show ‖(conv dR (σ j).density - conv dR σ0.density) x‖ ≤ _
  rw [Pi.sub_apply, h1015_conv_sub (h1015_memLp_dens_two (σ j)) (h1015_memLp_dens_two σ0),
    Real.norm_eq_abs]
  exact this

theorem h1015_Q_tendsto {σ : ℕ → AbsoluteDensity 1} {σ0 : AbsoluteDensity 1}
    (hd : h1015_Cvg 2 (haar 1) (fun j => (σ j).density) σ0.density)
    (hdd : h1015_Cvg 2 (haar 1) (fun j => densityDeriv (σ j)) (densityDeriv σ0)) :
    Tendsto (fun j => Q (σ j)) atTop (𝓝 (Q σ0)) := by
  simp_rw [← (weak_fourier_cross_term _).2.2]
  have hc := h1015_conv_cvg hd
  have h1 : h1015_Cvg 1 (haar 1) (fun j => densityDeriv (σ j)) (densityDeriv σ0) :=
    h1015_cvg_mono one_le_two hdd
  have := h1015_smul_tendsto (p := ⊤) (q := 1) (r := 1) le_rfl le_rfl (h1015_conv_top_ne σ0)
    (memLp_one_iff_integrable.2 ((memLp_densityDeriv σ0).integrable one_le_two)).eLpNorm_ne_top hc h1
  refine h1015_cvg_integral
    (h1011_int_mul_cont ((memLp_densityDeriv σ0).integrable one_le_two)
      (continuous_driftField σ0))
    (fun j => h1011_int_mul_cont ((memLp_densityDeriv (σ j)).integrable one_le_two)
      (continuous_driftField (σ j))) ?_
  refine h1015_cvg_congr_ae (fun j => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_) this
  · simp [mul_comm]
  · simp [mul_comm]

theorem h1015_T3_tendsto {σ : ℕ → AbsoluteDensity 1} {σ0 : AbsoluteDensity 1}
    (hd : h1015_Cvg 2 (haar 1) (fun j => (σ j).density) σ0.density) :
    Tendsto (fun j => ∫ x, (σ j).density x * (conv dR (σ j).density x) ^ 2 ∂haar 1) atTop
      (𝓝 (∫ x, σ0.density x * (conv dR σ0.density x) ^ 2 ∂haar 1)) := by
  have hc := h1015_conv_cvg hd
  have hc2 := h1015_smul_tendsto (p := ⊤) (q := ⊤) (r := ⊤) le_top le_top
    (h1015_conv_top_ne σ0) (h1015_conv_top_ne σ0) hc hc
  have h1 : h1015_Cvg 1 (haar 1) (fun j => (σ j).density) σ0.density :=
    h1015_cvg_mono one_le_two hd
  have hsq : eLpNorm (fun x => conv dR σ0.density x • conv dR σ0.density x) ⊤ (haar 1) ≠ ⊤ := by
    have := MemLp.mul (p := ⊤) (q := ⊤) (r := ⊤) (lt_top_iff_ne_top.2 (h1015_conv_top_ne σ0) :
      MemLp (conv dR σ0.density) ⊤ (haar 1)) (lt_top_iff_ne_top.2 (h1015_conv_top_ne σ0))
    refine (this.ae_eq (Eventually.of_forall fun x => ?_)).eLpNorm_ne_top
    simp
  have := h1015_smul_tendsto (p := ⊤) (q := 1) (r := 1) le_rfl le_rfl hsq
    (memLp_one_iff_integrable.2 σ0.integrable_density).eLpNorm_ne_top hc2 h1
  refine h1015_cvg_integral
    (h1011_int_mul_cont σ0.integrable_density ((continuous_driftField σ0).pow 2))
    (fun j => h1011_int_mul_cont (σ j).integrable_density ((continuous_driftField (σ j)).pow 2)) ?_
  refine h1015_cvg_congr_ae (fun j => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_) this
  · simp [mul_comm, sq]
  · simp [mul_comm, sq]

open DGPS DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model
  DGPS.Examples.PositiveH1.CrossTerm

/-- The family `F` with its species densities replaced by `ρ`. -/
noncomputable def h1015_fam (F : SpeciesFamily 1) (ρ : Fin F.count → AbsoluteDensity 1) :
    SpeciesFamily 1 := { F with density := ρ }

theorem h1015_bary_dens {F : SpeciesFamily 1} {ρ : ℕ → Fin F.count → AbsoluteDensity 1}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hne : ∀ s, eLpNorm (F.density s).density p (haar 1) ≠ ⊤)
    (h : ∀ s, h1015_Cvg p (haar 1) (fun j => (ρ j s).density) (F.density s).density) :
    h1015_Cvg p (haar 1) (fun j => (barycenter (h1015_fam F (ρ j))).density)
      (barycenter F).density := by
  have key := h1015_cvg_sum hp (Finset.univ : Finset (Fin F.count))
    (a := fun s j x => F.weight s * (ρ j s).density x)
    (b := fun s x => F.weight s * (F.density s).density x) (fun s _ => by
      have := h1015_cvg_const_smul (c := fun _ : ℕ => F.weight s) (c₀ := F.weight s) hp
        (hne s) tendsto_const_nhds (h s)
      exact this)
  refine h1015_cvg_congr_ae (fun j => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_) key
  · exact (SpeciesFamily.barycenter_density_apply (h1015_fam F (ρ j)) x).symm
  · exact (SpeciesFamily.barycenter_density_apply F x).symm

theorem h1015_bary_deriv {F : SpeciesFamily 1} {ρ : ℕ → Fin F.count → AbsoluteDensity 1}
    (hc : ∀ s, h1015_Conv (fun j => ρ j s) (F.density s)) :
    h1015_Cvg 2 (haar 1) (fun j => densityDeriv (barycenter (h1015_fam F (ρ j))))
      (densityDeriv (barycenter F)) := by
  have key := h1015_cvg_sum one_le_two (Finset.univ : Finset (Fin F.count))
    (a := fun s j x => F.weight s * densityDeriv (ρ j s) x)
    (b := fun s x => F.weight s * densityDeriv (F.density s) x) (fun s _ => by
      have := h1015_cvg_const_smul (c := fun _ : ℕ => F.weight s) (c₀ := F.weight s) one_le_two
        (memLp_densityDeriv (F.density s)).eLpNorm_ne_top tendsto_const_nhds
        (h1015_deriv_two (hc s))
      exact this)
  refine h1015_cvg_congr_ae (fun j => ?_) ?_ key
  · filter_upwards [h1011_bary_deriv (h1015_fam F (ρ j))] with x hx
    exact hx.symm
  · filter_upwards [h1011_bary_deriv F] with x hx
    exact hx.symm


theorem h1015_bary_dens_two {F : SpeciesFamily 1} {ρ : ℕ → Fin F.count → AbsoluteDensity 1}
    (hc : ∀ s, h1015_Conv (fun j => ρ j s) (F.density s)) :
    h1015_Cvg 2 (haar 1) (fun j => (barycenter (h1015_fam F (ρ j))).density)
      (barycenter F).density :=
  h1015_bary_dens one_le_two (fun s => (h1015_memLp_dens_two (F.density s)).eLpNorm_ne_top)
    (fun s => h1015_dens_two (hc s))

theorem h1015_gap_tendsto {F : SpeciesFamily 1} {ρ : ℕ → Fin F.count → AbsoluteDensity 1}
    (hc : ∀ s, h1015_Conv (fun j => ρ j s) (F.density s)) :
    Tendsto (fun j => speciesGap positiveH1 (h1015_fam F (ρ j))) atTop
      (𝓝 (speciesGap positiveH1 F)) := by
  rw [← NNReal.tendsto_coe]
  simp_rw [h1011_gap_species]
  exact (tendsto_finsetSum Finset.univ (fun s _ => (h1015_entropy_tendsto (hc s)).const_mul _)).add
    ((h1015_P_tendsto (σ := fun j => barycenter (h1015_fam F (ρ j)))
      (h1015_bary_dens_two hc)).const_mul _)

theorem h1015_dissipation_tendsto {F : SpeciesFamily 1} {ρ : ℕ → Fin F.count → AbsoluteDensity 1}
    (hc : ∀ s, h1015_Conv (fun j => ρ j s) (F.density s)) (b : AbsoluteDrift positiveH1) :
    Tendsto (fun j => speciesDissipation positiveH1 b (h1015_fam F (ρ j))) atTop
      (𝓝 (speciesDissipation positiveH1 b F)) := by
  simp_rw [(exact_scalar_and_species_dissipation_expansion.2 b _).2.2]
  refine ENNReal.tendsto_ofReal ?_
  have hd := h1015_bary_dens_two hc
  have hdd := h1015_bary_deriv hc
  exact ((tendsto_finsetSum Finset.univ (fun s _ =>
    ((h1015_gradnorm_tendsto (hc s)).const_mul 4).const_mul _)).add
    ((h1015_Q_tendsto hd hdd).const_mul _)).add ((h1015_T3_tendsto hd).const_mul _)

theorem h1015_quotient_tendsto {F : SpeciesFamily 1} {ρ : ℕ → Fin F.count → AbsoluteDensity 1}
    (hc : ∀ s, h1015_Conv (fun j => ρ j s) (F.density s)) (b : AbsoluteDrift positiveH1)
    (hG : 0 < speciesGap positiveH1 F) :
    Tendsto (fun j => speciesQuotient positiveH1 b (h1015_fam F (ρ j))) atTop
      (𝓝 (speciesQuotient positiveH1 b F)) := by
  have hg : Tendsto (fun j => (2 : ℝ≥0∞) * (speciesGap positiveH1 (h1015_fam F (ρ j)) : ℝ≥0∞))
      atTop (𝓝 (2 * (speciesGap positiveH1 F : ℝ≥0∞))) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 (h1015_gap_tendsto hc)) (Or.inr (by simp))
  have hne : (2 : ℝ≥0∞) * (speciesGap positiveH1 F : ℝ≥0∞) ≠ 0 := by
    simpa using hG.ne'
  exact ENNReal.Tendsto.div (h1015_dissipation_tendsto hc b) (Or.inr hne) hg
    (Or.inl (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top))

open DGPS DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model
  DGPS.Examples.PositiveH1.CrossTerm

/-- The smooth positive mass-one square root `(H_t u + δ)/‖H_t u + δ‖₂` as an absolute density. -/
noncomputable def h1015_approx (ρ0 : AbsoluteDensity 1) {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) :
    AbsoluteDensity 1 where
  sqrt := h1015_w ρ0.sqrt t δ
  sqrt_mem := ⟨_, h1015_w_grad (isWeakGradient_weakGradient ρ0.sqrt_mem) ht δ⟩
  sqrt_nonneg := Eventually.of_forall fun x => (h1015_w_pos ρ0.memLp_sqrt ρ0.sqrt_nonneg ht hδ x).le
  mass_one := h1015_w_mass ρ0.memLp_sqrt ρ0.sqrt_nonneg ht hδ

theorem h1015_conv_approx (ρ0 : AbsoluteDensity 1) {t δ : ℕ → ℝ} (ht : ∀ j, 0 < t j)
    (hδ : ∀ j, 0 < δ j) (ht0 : Tendsto t atTop (𝓝 0)) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    h1015_Conv (fun j => h1015_approx ρ0 (ht j) (hδ j)) ρ0 := by
  obtain ⟨h1, h2, h3⟩ := h1015_single_cvg (isWeakGradient_weakGradient ρ0.sqrt_mem) ρ0.mass_one
    ht ht0 hδ0
  refine ⟨h1, h3, ?_⟩
  refine h1015_cvg_congr_ae (fun j => ?_) Filter.EventuallyEq.rfl h2
  exact (h1015_w_grad (isWeakGradient_weakGradient ρ0.sqrt_mem) (ht j) (δ j)).ae_eq
    (isWeakGradient_weakGradient (h1015_approx ρ0 (ht j) (hδ j)).sqrt_mem)

/-- **H1015.** Smooth positive density approximation at a fixed family. -/
theorem smooth_positive_density_approximation_at_fixed_family (F : SpeciesFamily 1)
    {t δ : ℕ → ℝ} (ht : ∀ j, 0 < t j) (hδ : ∀ j, 0 < δ j)
    (ht0 : Tendsto t atTop (𝓝 0)) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    ∃ ρ : ℕ → Fin F.count → AbsoluteDensity 1,
      (∀ j s, (ρ j s).sqrt = fun x =>
        (heatOp (t j) (F.density s).sqrt x + δ j) /
          (eLpNorm (fun y => heatOp (t j) (F.density s).sqrt y + δ j) 2 (haar 1)).toReal) ∧
      (∀ j s, IsSmoothPeriodic (ρ j s).sqrt ∧ ∀ x, 0 < (ρ j s).sqrt x) ∧
      (∀ j s, IsSmoothPeriodic (ρ j s).density ∧ ∀ x, 0 < (ρ j s).density x) ∧
      (∀ s,
        h1015_Cvg 2 (haar 1) (fun j => (ρ j s).sqrt) (F.density s).sqrt ∧
        h1015_Cvg ⊤ (haar 1) (fun j => (ρ j s).sqrt) (F.density s).sqrt ∧
        h1015_Cvg 2 (haar 1) (fun j => weakGradient (ρ j s).sqrt (ρ j s).sqrt_mem)
          (weakGradient (F.density s).sqrt (F.density s).sqrt_mem) ∧
        h1015_Cvg 2 (haar 1) (fun j => (ρ j s).density) (F.density s).density ∧
        h1015_Cvg ⊤ (haar 1) (fun j => (ρ j s).density) (F.density s).density ∧
        h1015_Cvg 2 (haar 1) (fun j => densityDeriv (ρ j s)) (densityDeriv (F.density s))) ∧
      Tendsto (fun j => speciesGap positiveH1 (h1015_fam F (ρ j))) atTop
        (𝓝 (speciesGap positiveH1 F)) ∧
      (∀ b : AbsoluteDrift positiveH1,
        Tendsto (fun j => speciesDissipation positiveH1 b (h1015_fam F (ρ j))) atTop
          (𝓝 (speciesDissipation positiveH1 b F))) ∧
      (0 < speciesGap positiveH1 F → ∀ b : AbsoluteDrift positiveH1,
        Tendsto (fun j => speciesQuotient positiveH1 b (h1015_fam F (ρ j))) atTop
          (𝓝 (speciesQuotient positiveH1 b F))) := by
  refine ⟨fun j s => h1015_approx (F.density s) (ht j) (hδ j), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j s
    rfl
  · intro j s
    exact ⟨h1015_w_smooth (F.density s).memLp_sqrt (ht j) (δ j),
      h1015_w_pos (F.density s).memLp_sqrt (F.density s).sqrt_nonneg (ht j) (hδ j)⟩
  · intro j s
    refine ⟨?_, fun x => pow_pos (h1015_w_pos (F.density s).memLp_sqrt
      (F.density s).sqrt_nonneg (ht j) (hδ j) x) 2⟩
    have := h1015_w_smooth (F.density s).memLp_sqrt (ht j) (δ j)
    unfold IsSmoothPeriodic at this ⊢
    exact this.pow 2
  · intro s
    have hc := h1015_conv_approx (F.density s) ht hδ ht0 hδ0
    exact ⟨hc.sqrt2, hc.sqrtTop, hc.grad2, h1015_dens_two hc, h1015_dens_top hc,
      h1015_deriv_two hc⟩
  · exact h1015_gap_tendsto (fun s => h1015_conv_approx (F.density s) ht hδ ht0 hδ0)
  · intro b
    exact h1015_dissipation_tendsto (fun s => h1015_conv_approx (F.density s) ht hδ ht0 hδ0) b
  · intro hG b
    exact h1015_quotient_tendsto (fun s => h1015_conv_approx (F.density s) ht hδ ht0 hδ0) b hG

end DGPS.Examples.PositiveH1.SmoothApproximation
