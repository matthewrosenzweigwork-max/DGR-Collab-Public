import DGPS.SingularCounterexample.BarrierBlock

open MeasureTheory Filter Topology

namespace DGPS.SingularCounterexample

private theorem c1_lt_one_off_zero (x : Circle) (hx : x ≠ 0) : c1 x < 1 := by
  by_contra h
  have heq : c1 x = 1 := le_antisymm (c1_le_one x) (le_of_not_gt h)
  obtain ⟨t, hxt⟩ := Examples.PositiveH1.Nonlinear.lift1_exists x
  change x = torusPoint t at hxt
  rw [hxt, c1_torusPoint] at heq
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).mp heq
  have hmul : (2 * Real.pi) * (m : ℝ) = (2 * Real.pi) * t := by
    simpa [mul_comm] using hm
  have ht : (m : ℝ) = t := mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) hmul
  apply hx
  rw [hxt]
  ext i
  change (t : AddCircle (1 : ℝ)) = 0
  exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).2
    ⟨m, by simpa [zsmul_eq_mul] using ht⟩

/-- The denominator has a positive limit at each point away from collision. -/
private theorem peak_eventually_le_width_sq {x : Circle} (hx : x ≠ 0)
    {u : ℕ → Circle} (hu : Tendsto u atTop (𝓝 x)) :
    ∀ᶠ n in atTop, poissonPeak (radius n) (u n) ≤ width n ^ 2 / (1 - c1 x) := by
  have hd : 0 < 1 - c1 x := sub_pos.mpr (c1_lt_one_off_zero x hx)
  have hc : Continuous c1 := SharpLSI.FL.Ex.LaneD.cm_cont 1
  have hcos : Tendsto (fun n => c1 (u n)) atTop (𝓝 (c1 x)) :=
    (hc.tendsto x).comp hu
  have hden : Tendsto (fun n => 1 - 2 * radius n * c1 (u n) + radius n ^ 2)
      atTop (𝓝 (2 * (1 - c1 x))) := by
    have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
      ((radius_tendsto_one.const_mul 2).mul hcos)).add (radius_tendsto_one.pow 2)
    have heq : (1 : ℝ) - 2 * 1 * c1 x + 1 ^ 2 = 2 * (1 - c1 x) := by ring
    rw [heq] at h
    exact h
  have hev := hden.eventually (Ioi_mem_nhds (by linarith :
    1 - c1 x < 2 * (1 - c1 x)))
  filter_upwards [hev] with n hn
  have hdenpos : 0 < 1 - 2 * radius n * c1 (u n) + radius n ^ 2 := hd.trans hn
  have hwidth : 1 - radius n = width n := by simp [radius]
  rw [poissonPeak, hwidth]
  exact (div_le_div_iff₀ hdenpos hd).2
    (mul_le_mul_of_nonneg_left hn.le (sq_nonneg (width n)))

/-- SLC-K007: all three peak centers converge to zero, leaving a summable quadratic-width
bound at every fixed noncollision point. -/
theorem barrierBlock_summable {x : Circle} (hx : x ≠ 0) :
    Summable (fun n : ℕ => barrierBlock n x) := by
  have hp : Continuous torusPoint := Examples.PositiveH1.Nonlinear.continuous_lift1
  have hp0 : torusPoint 0 = (0 : Circle) := by
    ext i
    simp [torusPoint, torusLift, SharpLSI.liftT]
  have ha : Tendsto (fun n => torusPoint (separation n)) atTop (𝓝 (0 : Circle)) := by
    have h := (hp.tendsto (0 : ℝ)).comp separation_tendsto_zero
    rw [hp0] at h
    exact h
  have hxconst : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
  have hcenter := peak_eventually_le_width_sq hx hxconst
  have hleft := peak_eventually_le_width_sq hx
    (u := fun n => x - torusPoint (separation n)) (by simpa using hxconst.sub ha)
  have hright := peak_eventually_le_width_sq hx
    (u := fun n => x + torusPoint (separation n)) (by simpa using hxconst.add ha)
  apply (height_width_sq_summable.mul_left (4 / (1 - c1 x))).of_norm_bounded_eventually_nat
  filter_upwards [hcenter, hleft, hright] with n hc hl hr
  rw [Real.norm_eq_abs, abs_of_nonneg (barrierBlock_nonneg n x)]
  have hsum :
      2 * poissonPeak (radius n) x +
        poissonPeak (radius n) (x - torusPoint (separation n)) +
        poissonPeak (radius n) (x + torusPoint (separation n)) ≤
          4 * (width n ^ 2 / (1 - c1 x)) := by linarith
  calc
    barrierBlock n x ≤ height n * (4 * (width n ^ 2 / (1 - c1 x))) :=
      mul_le_mul_of_nonneg_left hsum (height_pos n).le
    _ = 4 / (1 - c1 x) * (height n * width n ^ 2) := by ring

/-- The explicitly chosen zero value does not change the divergent punctured limit. -/
noncomputable def barrier (x : Circle) : ℝ := by
  classical
  exact if x = 0 then 0 else ∑' n : ℕ, barrierBlock n x

@[simp] theorem barrier_zero : barrier 0 = 0 := by
  simp [barrier]

theorem barrier_nonneg (x : Circle) : 0 ≤ barrier x := by
  classical
  by_cases hx : x = 0
  · simp [barrier, hx]
  · simp only [barrier, ite_eq_right hx]
    exact tsum_nonneg fun n => barrierBlock_nonneg n x

theorem barrier_even (x : Circle) : barrier (-x) = barrier x := by
  classical
  by_cases hx : x = 0
  · simp [hx]
  · simp only [barrier, ite_eq_right hx, ite_eq_right (neg_ne_zero.mpr hx)]
    exact tsum_congr fun n => barrierBlock_even n x

theorem barrier_measurable : Measurable barrier := by
  classical
  have hm (n : ℕ) : Measurable (barrierBlock n) :=
    (SharpLSI.continuous_of_liftT' (barrierBlock_smooth_periodic n).continuous).measurable
  exact Measurable.ite (measurableSet_singleton (0 : Circle)) measurable_const
    (Measurable.tsum hm)

theorem barrierBlock_continuous (n : ℕ) : Continuous (barrierBlock n) :=
  SharpLSI.continuous_of_liftT' (barrierBlock_smooth_periodic n).continuous

theorem barrierBlock_le_barrier {x : Circle} (hx : x ≠ 0) (n : ℕ) :
    barrierBlock n x ≤ barrier x := by
  classical
  rw [barrier, ite_eq_right hx]
  exact (barrierBlock_summable hx).le_tsum n fun j _ => barrierBlock_nonneg j x

/-- Central peaks of arbitrarily large height force divergence through nonzero points,
although the chosen collision value is zero. -/
theorem barrier_tendsto_collision : Tendsto barrier (𝓝[≠] (0 : Circle)) atTop := by
  refine tendsto_atTop.2 fun b => ?_
  have he : ∀ᶠ n : ℕ in atTop, b + 1 ≤ height n :=
    height_tendsto_atTop.eventually (eventually_ge_atTop (b + 1))
  obtain ⟨n, hn⟩ := he.exists
  have hr0 : 0 < radius n := by linarith [radius_ge_half n]
  have hr1 := radius_lt_one n
  have hleft := (poissonPeak_pos hr0 hr1 ((0 : Circle) - torusPoint (separation n))).le
  have hright := (poissonPeak_pos hr0 hr1 ((0 : Circle) + torusPoint (separation n))).le
  have hcentral : 2 * height n ≤ barrierBlock n 0 := by
    unfold barrierBlock
    rw [poissonPeak_zero hr1]
    nlinarith [mul_nonneg (height_pos n).le (add_nonneg hleft hright)]
  have hb : b < barrierBlock n 0 := by linarith [height_pos n]
  have hnear : ∀ᶠ x in 𝓝 (0 : Circle), b ≤ barrierBlock n x :=
    (barrierBlock_continuous n).tendsto 0 |>.eventually (Ici_mem_nhds hb)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hnear, self_mem_nhdsWithin] with x hx hx0
  exact hx.trans (barrierBlock_le_barrier (by simpa using hx0) n)

private theorem barrierBlock_integrable (n : ℕ) :
    Integrable (barrierBlock n) (DGPS.haar 1) := by
  apply Continuous.integrable_of_hasCompactSupport (barrierBlock_continuous n)
  exact HasCompactSupport.of_compactSpace _

private theorem barrierBlock_integral (n : ℕ) :
    ∫ x : Circle, barrierBlock n x ∂DGPS.haar 1 =
      4 * height n * poissonPeakScale (radius n) := by
  have hz : coeff1 (barrierBlock n) 0 =
      ((∫ x : Circle, barrierBlock n x ∂DGPS.haar 1 : ℝ) : ℂ) := by
    change DGPS.fourierCoeff (barrierBlock n) (0 : Fin 1 → ℤ) = _
    rw [DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
    simp only [neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_mul]
    exact integral_complex_ofReal
  apply Complex.ofReal_injective
  calc
    ((∫ x : Circle, barrierBlock n x ∂DGPS.haar 1 : ℝ) : ℂ) =
        coeff1 (barrierBlock n) 0 := hz.symm
    _ = ((4 * height n * poissonPeakScale (radius n) : ℝ) : ℂ) := by
      rw [coeff_barrierBlock]
      simp

private theorem barrierBlock_lintegral (n : ℕ) :
    ∫⁻ x : Circle, ENNReal.ofReal (barrierBlock n x) ∂DGPS.haar 1 =
      ENNReal.ofReal (4 * height n * poissonPeakScale (radius n)) := by
  have hnonneg : ∀ x, 0 ≤ barrierBlock n x := barrierBlock_nonneg n
  have hfinite := (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnonneg)).1
    (barrierBlock_integrable n).hasFiniteIntegral
  calc
    ∫⁻ x : Circle, ENNReal.ofReal (barrierBlock n x) ∂DGPS.haar 1 =
        ENNReal.ofReal
          ((∫⁻ x : Circle, ENNReal.ofReal (barrierBlock n x) ∂DGPS.haar 1).toReal) :=
      (ENNReal.ofReal_toReal (ne_of_lt hfinite)).symm
    _ = ENNReal.ofReal (∫ x : Circle, barrierBlock n x ∂DGPS.haar 1) := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnonneg)
        (barrierBlock_continuous n).aestronglyMeasurable]
    _ = ENNReal.ofReal (4 * height n * poissonPeakScale (radius n)) := by
      rw [barrierBlock_integral]

private theorem poissonPeakScale_le_width (n : ℕ) :
    poissonPeakScale (radius n) ≤ width n := by
  have hwidth : 1 - radius n = width n := by simp [width, radius]
  rw [poissonPeakScale, hwidth, div_le_iff₀ (by linarith [radius_ge_half n])]
  have hw := (width_pos n).le
  have hr : 0 ≤ radius n := by linarith [radius_ge_half n]
  nlinarith [mul_nonneg hw hr]

private theorem barrierBlock_mass_bound (n : ℕ) :
    0 ≤ 4 * height n * poissonPeakScale (radius n) ∧
      4 * height n * poissonPeakScale (radius n) ≤ 4 * height n * width n := by
  have hh := (height_pos n).le
  have hc : 0 < poissonPeakScale (radius n) := by
    unfold poissonPeakScale
    exact div_pos (sub_pos.mpr (radius_lt_one n)) (by linarith [radius_ge_half n])
  constructor
  · positivity
  · exact mul_le_mul_of_nonneg_left (poissonPeakScale_le_width n) (by positivity)

private theorem barrierBlock_fourier_lintegral (n : ℕ) (k : ℤ) :
    ∫⁻ x : Circle,
        ‖UnitAddTorus.mFourier (-freqZ k) x * (barrierBlock n x : ℂ)‖ₑ ∂DGPS.haar 1 ≤
      ENNReal.ofReal (4 * height n * poissonPeakScale (radius n)) := by
  rw [← barrierBlock_lintegral n]
  apply lintegral_mono
  intro x
  change ‖UnitAddTorus.mFourier (-freqZ k) x * (barrierBlock n x : ℂ)‖ₑ ≤
    ENNReal.ofReal (barrierBlock n x)
  have hnorm :
      ‖UnitAddTorus.mFourier (-freqZ k) x * (barrierBlock n x : ℂ)‖ = barrierBlock n x := by
    rw [norm_mul, DGPS.norm_mFourier_apply, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (barrierBlock_nonneg n x)]
  rw [← ofReal_norm, hnorm]

private noncomputable def barrierMassMajorant (n : ℕ) : ℝ := 4 * height n * width n

private theorem barrierMassMajorant_nonneg (n : ℕ) : 0 ≤ barrierMassMajorant n := by
  exact mul_nonneg (mul_nonneg (by norm_num) (height_pos n).le) (width_pos n).le

private theorem barrierMassMajorant_summable : Summable barrierMassMajorant := by
  change Summable (fun n : ℕ => 4 * height n * width n)
  simpa [mul_assoc] using height_width_summable.mul_left (4 : ℝ)

private theorem barrier_fourier_lintegral_tsum_ne_top (k : ℤ) :
    (∑' n : ℕ, ∫⁻ x : Circle,
      ‖UnitAddTorus.mFourier (-freqZ k) x * (barrierBlock n x : ℂ)‖ₑ ∂DGPS.haar 1) ≠ ⊤ := by
  have hbound :
      (∑' n : ℕ, ∫⁻ x : Circle,
        ‖UnitAddTorus.mFourier (-freqZ k) x * (barrierBlock n x : ℂ)‖ₑ ∂DGPS.haar 1) ≤
        ENNReal.ofReal (∑' n : ℕ, barrierMassMajorant n) := by
    calc
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (barrierMassMajorant n) :=
        ENNReal.tsum_le_tsum fun n =>
          (barrierBlock_fourier_lintegral n k).trans
            (ENNReal.ofReal_le_ofReal (barrierBlock_mass_bound n).2)
      _ = ENNReal.ofReal (∑' n : ℕ, barrierMassMajorant n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => barrierMassMajorant_nonneg n)
          barrierMassMajorant_summable).symm
  exact ne_of_lt (hbound.trans_lt ENNReal.ofReal_lt_top)

private theorem barrierBlock_mass_summable :
    Summable (fun n : ℕ => 4 * height n * poissonPeakScale (radius n)) := by
  refine Summable.of_nonneg_of_le (fun n => (barrierBlock_mass_bound n).1)
    (fun n => (barrierBlock_mass_bound n).2) barrierMassMajorant_summable

private noncomputable def barrierBlockSum (x : Circle) : ℝ := ∑' n : ℕ, barrierBlock n x

private theorem barrierBlockSum_measurable : Measurable barrierBlockSum := by
  apply Measurable.tsum
  intro n
  exact (barrierBlock_continuous n).measurable

private theorem barrierBlockSum_lintegral :
    ∫⁻ x : Circle, ENNReal.ofReal (barrierBlockSum x) ∂DGPS.haar 1 =
      ENNReal.ofReal (∑' n : ℕ, 4 * height n * poissonPeakScale (radius n)) := by
  have hzero : ∀ᵐ x : Circle ∂DGPS.haar 1, x ≠ 0 := by
    simpa using (measure_eq_zero_iff_ae_notMem.mp (haar_singleton_zero (0 : Circle)))
  have hAE : (fun x : Circle => ENNReal.ofReal (barrierBlockSum x)) =ᵐ[DGPS.haar 1]
      (fun x => ∑' n : ℕ, ENNReal.ofReal (barrierBlock n x)) := by
    filter_upwards [hzero] with x hx
    rw [barrierBlockSum]
    exact ENNReal.ofReal_tsum_of_nonneg (fun n => barrierBlock_nonneg n x)
      (barrierBlock_summable hx)
  calc
    ∫⁻ x : Circle, ENNReal.ofReal (barrierBlockSum x) ∂DGPS.haar 1 =
        ∫⁻ x : Circle, ∑' n : ℕ, ENNReal.ofReal (barrierBlock n x) ∂DGPS.haar 1 :=
      lintegral_congr_ae hAE
    _ = ∑' n : ℕ, ∫⁻ x : Circle, ENNReal.ofReal (barrierBlock n x) ∂DGPS.haar 1 := by
      rw [lintegral_tsum fun n =>
        (barrierBlock_continuous n).measurable.ennreal_ofReal.aemeasurable]
    _ = ∑' n : ℕ, ENNReal.ofReal (4 * height n * poissonPeakScale (radius n)) :=
      tsum_congr fun n => barrierBlock_lintegral n
    _ = ENNReal.ofReal (∑' n : ℕ, 4 * height n * poissonPeakScale (radius n)) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun n => (barrierBlock_mass_bound n).1)
        barrierBlock_mass_summable).symm

private theorem barrierBlockSum_integrable : Integrable barrierBlockSum (DGPS.haar 1) := by
  refine ⟨barrierBlockSum_measurable.aestronglyMeasurable, ?_⟩
  have hfinite :
      ∫⁻ x : Circle, ENNReal.ofReal (barrierBlockSum x) ∂DGPS.haar 1 < ⊤ := by
    rw [barrierBlockSum_lintegral]
    exact ENNReal.ofReal_lt_top
  exact (MeasureTheory.hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun x => tsum_nonneg fun n => barrierBlock_nonneg n x)).2 hfinite

private theorem barrier_ae_eq_barrierBlockSum : barrier =ᵐ[DGPS.haar 1] barrierBlockSum := by
  exact circle_ae_eq_of_eq_off_zero fun x hx => by simp [barrier, barrierBlockSum, hx]

/-- The barrier is Haar-integrable, and its integral is the sum of the block masses. -/
theorem barrier_integrable : Integrable barrier (DGPS.haar 1) :=
  barrierBlockSum_integrable.congr barrier_ae_eq_barrierBlockSum.symm

/-- L1 Tonelli interchange for the punctured barrier, including its null-set representative. -/
theorem integral_barrier_eq_tsum :
    ∫ x : Circle, barrier x ∂DGPS.haar 1 =
      ∑' n : ℕ, ∫ x : Circle, barrierBlock n x ∂DGPS.haar 1 := by
  have hnormsum : Summable (fun n : ℕ => ∫ x : Circle, ‖barrierBlock n x‖ ∂DGPS.haar 1) := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun x => norm_nonneg _)
      (fun n => ?_) (height_width_summable.mul_left (4 : ℝ))
    rw [integral_congr_ae (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (barrierBlock_nonneg n x)])]
    rw [barrierBlock_integral]
    simpa [barrierMassMajorant, mul_assoc] using (barrierBlock_mass_bound n).2
  calc
    ∫ x : Circle, barrier x ∂DGPS.haar 1 =
        ∫ x : Circle, barrierBlockSum x ∂DGPS.haar 1 :=
      integral_congr_ae barrier_ae_eq_barrierBlockSum
    _ = ∑' n : ℕ, ∫ x : Circle, barrierBlock n x ∂DGPS.haar 1 :=
      (integral_tsum_of_summable_integral_norm
        (fun n => barrierBlock_integrable n) hnormsum).symm

private theorem barrierBlock_coeff_norm_bound (n : ℕ) (k : ℤ) :
    ‖coeff1 (barrierBlock n) k‖ ≤ barrierMassMajorant n := by
  rw [coeff_barrierBlock, Complex.norm_real, Real.norm_eq_abs]
  have hscale : 0 < poissonPeakScale (radius n) := by
    unfold poissonPeakScale
    exact div_pos (sub_pos.mpr (radius_lt_one n)) (by linarith [radius_ge_half n])
  have hrad : 0 ≤ radius n := by linarith [radius_ge_half n]
  have hpow : radius n ^ Int.natAbs k ≤ 1 :=
    pow_le_one₀ hrad (radius_lt_one n).le
  have hcos : Real.cos (Real.pi * (k : ℝ) * separation n) ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (k : ℝ) * separation n),
      sq_nonneg (Real.sin (Real.pi * (k : ℝ) * separation n))]
  have h4h : 0 ≤ (4 : ℝ) * height n :=
    mul_nonneg (by norm_num) (height_pos n).le
  have h4hs : 0 ≤ (4 * height n) * poissonPeakScale (radius n) :=
    mul_nonneg h4h hscale.le
  have hpow0 : 0 ≤ radius n ^ Int.natAbs k := pow_nonneg hrad _
  have hcos0 : 0 ≤ Real.cos (Real.pi * (k : ℝ) * separation n) ^ 2 := sq_nonneg _
  have hnonneg :
      0 ≤ 4 * height n * poissonPeakScale (radius n) * radius n ^ Int.natAbs k *
        Real.cos (Real.pi * (k : ℝ) * separation n) ^ 2 :=
    mul_nonneg (mul_nonneg h4hs hpow0) hcos0
  rw [abs_of_nonneg hnonneg]
  let A : ℝ := 4 * height n * poissonPeakScale (radius n)
  have hA : 0 ≤ A := by
    change 0 ≤ (4 * height n) * poissonPeakScale (radius n)
    exact h4hs
  calc
    4 * height n * poissonPeakScale (radius n) * radius n ^ Int.natAbs k *
        Real.cos (Real.pi * (k : ℝ) * separation n) ^ 2 =
        A * radius n ^ Int.natAbs k * Real.cos (Real.pi * (k : ℝ) * separation n) ^ 2 := by
          simp [A, mul_assoc]
    _ ≤ A * radius n ^ Int.natAbs k := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hcos (mul_nonneg hA (pow_nonneg hrad (Int.natAbs k)))
    _ ≤ A := by
      simpa [mul_one] using mul_le_mul_of_nonneg_left hpow hA
    _ ≤ barrierMassMajorant n := by
      change (4 * height n) * poissonPeakScale (radius n) ≤
        (4 * height n) * width n
      exact mul_le_mul_of_nonneg_left (poissonPeakScale_le_width n) h4h

private theorem barrierBlock_coeff_summable (k : ℤ) :
    Summable (fun n : ℕ => coeff1 (barrierBlock n) k) :=
  Summable.of_norm_bounded barrierMassMajorant_summable
    (fun n => barrierBlock_coeff_norm_bound n k)

/-- The Fourier coefficient of the punctured barrier is the sum of its block coefficients. -/
theorem coeff1_barrier_eq_tsum (k : ℤ) :
    coeff1 barrier k = ∑' n : ℕ, coeff1 (barrierBlock n) k := by
  let F : ℕ → Circle → ℂ := fun n x =>
    UnitAddTorus.mFourier (-freqZ k) x * (barrierBlock n x : ℂ)
  have hFint (n : ℕ) : Integrable (F n) (DGPS.haar 1) := by
    simpa [F] using DGPS.integrable_mFourier_mul (barrierBlock_integrable n) (-freqZ k)
  have hFsm (n : ℕ) : AEStronglyMeasurable (F n) (DGPS.haar 1) :=
    (hFint n).aestronglyMeasurable
  have hfinite := barrier_fourier_lintegral_tsum_ne_top k
  have hsumInt := integral_tsum hFsm hfinite
  have hzero : ∀ᵐ x : Circle ∂DGPS.haar 1, x ≠ 0 := by
    simpa using (measure_eq_zero_iff_ae_notMem.mp (haar_singleton_zero (0 : Circle)))
  have hAE :
      (fun x : Circle => UnitAddTorus.mFourier (-freqZ k) x * (barrier x : ℂ)) =ᵐ[DGPS.haar 1]
        (fun x => ∑' n : ℕ, F n x) := by
    filter_upwards [hzero] with x hx
    have hs : Summable (fun n : ℕ => barrierBlock n x) := barrierBlock_summable hx
    calc
      UnitAddTorus.mFourier (-freqZ k) x * (barrier x : ℂ) =
          UnitAddTorus.mFourier (-freqZ k) x * ((∑' n : ℕ, barrierBlock n x : ℝ) : ℂ) := by
            simp [barrier, hx]
      _ = ∑' n : ℕ, F n x := by
        dsimp [F]
        rw [Complex.ofReal_tsum, tsum_mul_left]
  have hcoeff : coeff1 barrier k =
      ∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x * (barrier x : ℂ) ∂DGPS.haar 1 := by
    change DGPS.fourierCoeff barrier (freqZ k) = _
    rw [DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
  have hcoeffBlock (n : ℕ) : coeff1 (barrierBlock n) k =
      ∫ x : Circle, F n x ∂DGPS.haar 1 := by
    change DGPS.fourierCoeff (barrierBlock n) (freqZ k) = _
    rw [DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
  calc
    coeff1 barrier k =
        ∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x * (barrier x : ℂ) ∂DGPS.haar 1 :=
      hcoeff
    _ = ∫ x : Circle, ∑' n : ℕ, F n x ∂DGPS.haar 1 := integral_congr_ae hAE
    _ = ∑' n : ℕ, ∫ x : Circle, F n x ∂DGPS.haar 1 := hsumInt
    _ = ∑' n : ℕ, coeff1 (barrierBlock n) k :=
      tsum_congr fun n => (hcoeffBlock n).symm

/-- All integer Fourier modes of the barrier have a convergent block-coefficient series. -/
theorem hasSum_coeff_barrier (k : ℤ) :
    HasSum (fun n : ℕ => coeff1 (barrierBlock n) k) (coeff1 barrier k) := by
  rw [Summable.hasSum_iff (barrierBlock_coeff_summable k)]
  exact (coeff1_barrier_eq_tsum k).symm

private theorem barrierBlock_coeff_re_summable (k : ℤ) :
    Summable (fun n : ℕ => (coeff1 (barrierBlock n) k).re) := by
  apply Summable.of_norm_bounded barrierMassMajorant_summable
  intro n
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (barrierBlock_coeff_norm_bound n k)

private theorem barrierBlock_coeff_eq_ofReal_re (n : ℕ) (k : ℤ) :
    coeff1 (barrierBlock n) k = ((coeff1 (barrierBlock n) k).re : ℂ) := by
  apply Complex.ext
  · simp
  · exact (barrierBlock_coeff_nonneg n k).1

private theorem coeff1_barrier_eq_ofReal_tsum_re (k : ℤ) :
    coeff1 barrier k = ((∑' n : ℕ, (coeff1 (barrierBlock n) k).re : ℝ) : ℂ) := by
  rw [coeff1_barrier_eq_tsum]
  calc
    ∑' n : ℕ, coeff1 (barrierBlock n) k =
        ∑' n : ℕ, ((coeff1 (barrierBlock n) k).re : ℂ) :=
      tsum_congr fun n => barrierBlock_coeff_eq_ofReal_re n k
    _ = ((∑' n : ℕ, (coeff1 (barrierBlock n) k).re : ℝ) : ℂ) := by
      exact (Complex.ofReal_tsum (fun n : ℕ => (coeff1 (barrierBlock n) k).re)).symm

/-- The singular barrier has strictly positive real Fourier mass at every nonzero mode. -/
theorem barrier_has_pos_nonzero_fourier : HasPosNonzeroFourier barrier := by
  intro k hk
  have hcoeff_nonneg : ∀ n : ℕ, 0 ≤ (coeff1 (barrierBlock n) k).re :=
    fun n => (barrierBlock_coeff_nonneg n k).2
  obtain ⟨n, hn⟩ := barrierBlock_exists_pos_coefficient k
  have hsumpos : 0 < ∑' n : ℕ, (coeff1 (barrierBlock n) k).re :=
    (barrierBlock_coeff_re_summable k).tsum_pos hcoeff_nonneg n hn
  constructor
  · rw [coeff1_barrier_eq_ofReal_tsum_re]
    simp
  · rw [coeff1_barrier_eq_ofReal_tsum_re, Complex.ofReal_re]
    exact hsumpos

end DGPS.SingularCounterexample
