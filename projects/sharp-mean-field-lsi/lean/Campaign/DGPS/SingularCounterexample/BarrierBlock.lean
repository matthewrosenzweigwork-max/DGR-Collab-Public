import DGPS.SingularCounterexample.PoissonPeak
import DGPS.SingularCounterexample.Scales
import DGPS.Examples.PositiveH1.Nonlinear

open scoped ContDiff
open MeasureTheory Filter Topology

namespace DGPS.SingularCounterexample

/-- The `n`-th barrier block: a central Poisson peak and two equal translates. -/
noncomputable def barrierBlock (n : ℕ) (x : Circle) : ℝ :=
  height n *
    (2 * poissonPeak (radius n) x +
      poissonPeak (radius n) (x - torusPoint (separation n)) +
      poissonPeak (radius n) (x + torusPoint (separation n)))

theorem barrierBlock_nonneg (n : ℕ) (x : Circle) : 0 ≤ barrierBlock n x := by
  unfold barrierBlock
  have hr0 : 0 < radius n := by linarith [radius_ge_half n]
  have hr1 := radius_lt_one n
  have hcenter := poissonPeak_pos hr0 hr1 x
  have hleft := poissonPeak_pos hr0 hr1 (x - torusPoint (separation n))
  have hright := poissonPeak_pos hr0 hr1 (x + torusPoint (separation n))
  exact mul_nonneg (height_pos n).le (by positivity)

theorem barrierBlock_even (n : ℕ) (x : Circle) : barrierBlock n (-x) = barrierBlock n x := by
  let r := radius n
  let a := torusPoint (separation n)
  change height n * (2 * poissonPeak r (-x) + poissonPeak r (-x - a) +
      poissonPeak r (-x + a)) =
    height n * (2 * poissonPeak r x + poissonPeak r (x - a) + poissonPeak r (x + a))
  rw [poissonPeak_even r x]
  have h₁ : -x - a = -(x + a) := by abel
  rw [h₁, poissonPeak_even r (x + a)]
  have h₂ : -x + a = -(x - a) := by abel
  rw [h₂, poissonPeak_even r (x - a)]
  ring

theorem barrierBlock_smooth_periodic (n : ℕ) : IsSmoothPeriodic (barrierBlock n) := by
  have hr0 : 0 < radius n := by linarith [radius_ge_half n]
  have hr1 := radius_lt_one n
  have hbase : IsSmoothPeriodic (poissonPeak (radius n)) := poissonPeak_smooth_periodic hr0 hr1
  have hminus : IsSmoothPeriodic
      (fun x : Circle => poissonPeak (radius n) (x - torusPoint (separation n))) := by
    simpa only [sub_eq_add_neg] using
      DGPS.Examples.PositiveH1.Nonlinear.translate_smooth hbase
        (-torusPoint (separation n))
  have hplus : IsSmoothPeriodic
      (fun x : Circle => poissonPeak (radius n) (x + torusPoint (separation n))) :=
    DGPS.Examples.PositiveH1.Nonlinear.translate_smooth hbase (torusPoint (separation n))
  have hbase' : ContDiff ℝ ∞
      (fun v : Fin 1 → ℝ => poissonPeak (radius n) (DGPS.torusLift v)) := hbase
  have hminus' : ContDiff ℝ ∞ (fun v : Fin 1 → ℝ =>
      poissonPeak (radius n) (DGPS.torusLift v - torusPoint (separation n))) := hminus
  have hplus' : ContDiff ℝ ∞ (fun v : Fin 1 → ℝ =>
      poissonPeak (radius n) (DGPS.torusLift v + torusPoint (separation n))) := hplus
  change ContDiff ℝ ∞ (fun v : Fin 1 → ℝ =>
    height n *
      (2 * poissonPeak (radius n) (DGPS.torusLift v) +
        poissonPeak (radius n) (DGPS.torusLift v - torusPoint (separation n)) +
        poissonPeak (radius n) (DGPS.torusLift v + torusPoint (separation n))))
  exact contDiff_const.mul ((contDiff_const.mul hbase').add hminus' |>.add hplus')

theorem barrierBlock_le_four_height (n : ℕ) (x : Circle) : barrierBlock n x ≤ 4 * height n := by
  unfold barrierBlock
  have hr0 : 0 < radius n := by linarith [radius_ge_half n]
  have hr1 := radius_lt_one n
  have hcenter := poissonPeak_le_one hr0 hr1 x
  have hleft := poissonPeak_le_one hr0 hr1 (x - torusPoint (separation n))
  have hright := poissonPeak_le_one hr0 hr1 (x + torusPoint (separation n))
  have hsum :
      2 * poissonPeak (radius n) x +
        poissonPeak (radius n) (x - torusPoint (separation n)) +
        poissonPeak (radius n) (x + torusPoint (separation n)) ≤ 4 := by
    linarith
  calc
    height n * (2 * poissonPeak (radius n) x +
        poissonPeak (radius n) (x - torusPoint (separation n)) +
        poissonPeak (radius n) (x + torusPoint (separation n))) ≤ height n * 4 :=
      mul_le_mul_of_nonneg_left hsum (height_pos n).le
    _ = 4 * height n := by ring

private theorem coeff1_add_of_continuous {f g : Circle → ℝ}
    (hf : Continuous f) (hg : Continuous g) (k : ℤ) :
    coeff1 (fun x => f x + g x) k = coeff1 f k + coeff1 g k := by
  have hfint : Integrable
      (fun x : Circle => UnitAddTorus.mFourier (-freqZ k) x * (f x : ℂ)) (DGPS.haar 1) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (UnitAddTorus.mFourier (-freqZ k)).continuous.mul
        (Complex.continuous_ofReal.comp hf)
    · exact HasCompactSupport.of_compactSpace _
  have hgint : Integrable
      (fun x : Circle => UnitAddTorus.mFourier (-freqZ k) x * (g x : ℂ)) (DGPS.haar 1) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (UnitAddTorus.mFourier (-freqZ k)).continuous.mul
        (Complex.continuous_ofReal.comp hg)
    · exact HasCompactSupport.of_compactSpace _
  change DGPS.fourierCoeff (fun x => f x + g x) (freqZ k) =
    DGPS.fourierCoeff f (freqZ k) + DGPS.fourierCoeff g (freqZ k)
  simp only [DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
  calc
    (∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x * ((f x + g x : ℝ) : ℂ)
        ∂DGPS.haar 1) =
      ∫ x : Circle,
        (UnitAddTorus.mFourier (-freqZ k) x * (f x : ℂ)) +
          (UnitAddTorus.mFourier (-freqZ k) x * (g x : ℂ)) ∂DGPS.haar 1 := by
            congr 1
            funext x
            simp only [Complex.ofReal_add]
            ring
    _ = (∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x * (f x : ℂ)
          ∂DGPS.haar 1) +
        ∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x * (g x : ℂ) ∂DGPS.haar 1 :=
          integral_add hfint hgint

private theorem coeff1_real_smul (f : Circle → ℝ) (c : ℝ) (k : ℤ) :
    coeff1 (fun x => c * f x) k = (c : ℂ) * coeff1 f k := by
  change DGPS.fourierCoeff (fun x => c * f x) (freqZ k) =
    (c : ℂ) * DGPS.fourierCoeff f (freqZ k)
  simp only [DGPS.Examples.PositiveH1.Fourier.fourierCoeff_eq_integral]
  calc
    (∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x * ((c * f x : ℝ) : ℂ)
        ∂DGPS.haar 1) =
      ∫ x : Circle, (c : ℂ) *
        (UnitAddTorus.mFourier (-freqZ k) x * (f x : ℂ)) ∂DGPS.haar 1 := by
          congr 1
          funext x
          simp only [Complex.ofReal_mul]
          ring
    _ = (c : ℂ) *
        ∫ x : Circle, UnitAddTorus.mFourier (-freqZ k) x * (f x : ℂ) ∂DGPS.haar 1 :=
          integral_const_mul _ _

private theorem mFourier_negfreq_torusPoint_exp (k : ℤ) (t : ℝ) :
    UnitAddTorus.mFourier (-freqZ k) (torusPoint t) =
      Complex.exp (((-(2 * Real.pi * (k : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
  change UnitAddTorus.mFourier (-freqZ k) (SharpLSI.liftT (fun _ : Fin 1 => t)) = _
  rw [SharpLSI.mFourier_liftT]
  rw [Fin.sum_univ_one]
  have hk0 : (-freqZ k) 0 = -k := rfl
  rw [hk0]
  congr 1
  push_cast
  ring_nf

private theorem mFourier_negfreq_torusPoint_re (k : ℤ) (t : ℝ) :
    (UnitAddTorus.mFourier (-freqZ k) (torusPoint t)).re =
      Real.cos (2 * Real.pi * (k : ℝ) * t) := by
  rw [mFourier_negfreq_torusPoint_exp, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

private theorem mFourier_negfreq_torusPoint_im (k : ℤ) (t : ℝ) :
    (UnitAddTorus.mFourier (-freqZ k) (torusPoint t)).im =
      -Real.sin (2 * Real.pi * (k : ℝ) * t) := by
  rw [mFourier_negfreq_torusPoint_exp, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

private theorem mFourier_negfreq_torusPoint_pair (k : ℤ) (t : ℝ) :
    UnitAddTorus.mFourier (-freqZ k) (torusPoint t) +
      UnitAddTorus.mFourier (-freqZ k) (torusPoint (-t)) =
      ((2 * Real.cos (2 * Real.pi * (k : ℝ) * t) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re]
    rw [mFourier_negfreq_torusPoint_re, mFourier_negfreq_torusPoint_re]
    rw [show 2 * Real.pi * (k : ℝ) * (-t) =
      -(2 * Real.pi * (k : ℝ) * t) by ring]
    simp only [Real.cos_neg]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im]
    rw [mFourier_negfreq_torusPoint_im, mFourier_negfreq_torusPoint_im]
    rw [show 2 * Real.pi * (k : ℝ) * (-t) =
      -(2 * Real.pi * (k : ℝ) * t) by ring]
    simp only [Real.sin_neg]
    ring

/-- Exact Fourier coefficients of a two-point barrier block. -/
theorem coeff_barrierBlock (n : ℕ) (k : ℤ) :
    coeff1 (barrierBlock n) k =
      ((4 * height n * poissonPeakScale (radius n) * radius n ^ Int.natAbs k *
        Real.cos (Real.pi * (k : ℝ) * separation n) ^ 2 : ℝ) : ℂ) := by
  let r := radius n
  let a := torusPoint (separation n)
  have hr0 : 0 < r := by
    dsimp [r]
    linarith [radius_ge_half n]
  have hr1 : r < 1 := by simpa [r] using radius_lt_one n
  have hbase := poissonPeak_smooth_periodic hr0 hr1
  have hleft : IsSmoothPeriodic (fun x : Circle => poissonPeak r (x - a)) := by
    simpa only [sub_eq_add_neg] using
      DGPS.Examples.PositiveH1.Nonlinear.translate_smooth hbase (-a)
  have hright : IsSmoothPeriodic (fun x : Circle => poissonPeak r (x + a)) :=
    DGPS.Examples.PositiveH1.Nonlinear.translate_smooth hbase a
  have h2base : IsSmoothPeriodic (fun x : Circle => 2 * poissonPeak r x) := by
    change ContDiff ℝ ∞ (fun v : Fin 1 → ℝ => 2 * poissonPeak r (DGPS.torusLift v))
    exact contDiff_const.mul hbase
  have hsum : coeff1
      (fun x : Circle => 2 * poissonPeak r x +
        (poissonPeak r (x - a) + poissonPeak r (x + a))) k =
      (2 : ℂ) * coeff1 (poissonPeak r) k +
        coeff1 (fun x => poissonPeak r (x - a)) k +
        coeff1 (fun x => poissonPeak r (x + a)) k := by
    calc
      coeff1 (fun x : Circle => 2 * poissonPeak r x +
          (poissonPeak r (x - a) + poissonPeak r (x + a))) k =
        coeff1 (fun x : Circle => 2 * poissonPeak r x) k +
          coeff1 (fun x : Circle => poissonPeak r (x - a) + poissonPeak r (x + a)) k :=
            coeff1_add_of_continuous h2base.continuous_torus
              (hleft.continuous_torus.add hright.continuous_torus) k
      _ = (2 : ℂ) * coeff1 (poissonPeak r) k +
          coeff1 (fun x => poissonPeak r (x - a)) k +
          coeff1 (fun x => poissonPeak r (x + a)) k := by
            rw [coeff1_real_smul (poissonPeak r) 2 k,
              coeff1_add_of_continuous hleft.continuous_torus hright.continuous_torus k]
            push_cast
            ring_nf
  have hleftcoeff := coeff_poissonPeak_translate hr0 hr1 a k
  have hrightcoeff : coeff1 (fun x : Circle => poissonPeak r (x + a)) k =
      UnitAddTorus.mFourier (-freqZ k) (-a) * coeff1 (poissonPeak r) k := by
    convert coeff_poissonPeak_translate hr0 hr1 (-a) k using 1
    simp
  have hbasecoeff := coeff_poissonPeak hr0 hr1 k
  have hphase := mFourier_negfreq_torusPoint_pair k (separation n)
  have hnegpoint : torusPoint (-separation n) = -torusPoint (separation n) := by
    ext i
    simp [torusPoint, DGPS.torusLift, SharpLSI.liftT]
  have htrig :
      2 + 2 * Real.cos (2 * Real.pi * (k : ℝ) * separation n) =
        4 * Real.cos (Real.pi * (k : ℝ) * separation n) ^ 2 := by
    have harg : 2 * (Real.pi * (k : ℝ) * separation n) =
        2 * Real.pi * (k : ℝ) * separation n := by ring
    rw [← harg, Real.cos_two_mul]
    ring
  change coeff1 (fun x : Circle => height n *
      (2 * poissonPeak r x + poissonPeak r (x - a) + poissonPeak r (x + a))) k = _
  have hassoc :
      (fun x : Circle => 2 * poissonPeak r x + poissonPeak r (x - a) +
        poissonPeak r (x + a)) =
      (fun x : Circle => 2 * poissonPeak r x +
        (poissonPeak r (x - a) + poissonPeak r (x + a))) := by
    funext x
    ring
  have hassoc_coeff :
      coeff1 (fun x : Circle => 2 * poissonPeak r x + poissonPeak r (x - a) +
        poissonPeak r (x + a)) k =
      coeff1 (fun x : Circle => 2 * poissonPeak r x +
        (poissonPeak r (x - a) + poissonPeak r (x + a))) k :=
    congrArg (fun f : Circle → ℝ => coeff1 f k) hassoc
  rw [coeff1_real_smul _ (height n) k]
  rw [hassoc_coeff]
  rw [hsum, hleftcoeff, hrightcoeff, hbasecoeff]
  rw [show torusPoint (-separation n) = -a by simp [a, hnegpoint]] at hphase
  have hfactor :
      (2 : ℂ) * ((poissonPeakScale r * r ^ Int.natAbs k : ℝ) : ℂ) +
          UnitAddTorus.mFourier (-freqZ k) a *
            ((poissonPeakScale r * r ^ Int.natAbs k : ℝ) : ℂ) +
          UnitAddTorus.mFourier (-freqZ k) (-a) *
            ((poissonPeakScale r * r ^ Int.natAbs k : ℝ) : ℂ) =
        ((poissonPeakScale r * r ^ Int.natAbs k : ℝ) : ℂ) *
          (2 + (UnitAddTorus.mFourier (-freqZ k) a +
            UnitAddTorus.mFourier (-freqZ k) (-a))) := by ring
  have hphase' :
      UnitAddTorus.mFourier (-freqZ k) a + UnitAddTorus.mFourier (-freqZ k) (-a) =
        ((2 * Real.cos (2 * Real.pi * (k : ℝ) * separation n) : ℝ) : ℂ) := by
    simpa [a, hnegpoint] using hphase
  have htwo :
      (2 : ℂ) + ((2 * Real.cos (2 * Real.pi * (k : ℝ) * separation n) : ℝ) : ℂ) =
        ((2 + 2 * Real.cos (2 * Real.pi * (k : ℝ) * separation n) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hfactor, hphase']
  rw [htwo]
  rw [htrig]
  push_cast
  ring

/-- Every integer Fourier coefficient of a barrier block is a nonnegative real. -/
theorem barrierBlock_coeff_nonneg (n : ℕ) (k : ℤ) :
    (coeff1 (barrierBlock n) k).im = 0 ∧ 0 ≤ (coeff1 (barrierBlock n) k).re := by
  rw [coeff_barrierBlock]
  simp only [Complex.ofReal_im, Complex.ofReal_re]
  constructor
  · trivial
  · have hr0 : 0 < radius n := by linarith [radius_ge_half n]
    have hscale : 0 < poissonPeakScale (radius n) := by
      unfold poissonPeakScale
      exact div_pos (sub_pos.mpr (radius_lt_one n)) (by linarith)
    have hheight := height_pos n
    have hrpow : 0 < radius n ^ Int.natAbs k := pow_pos hr0 _
    positivity

/-- Barrier blocks have nonnegative nonzero Fourier coefficients in the frozen interface. -/
theorem barrierBlock_has_nonneg_nonzero_fourier (n : ℕ) :
    HasNonnegNonzeroFourier (barrierBlock n) := by
  intro k _
  exact barrierBlock_coeff_nonneg n k

/-- Every fixed integer mode is strictly positive for some sufficiently late barrier block. -/
theorem barrierBlock_exists_pos_coefficient (k : ℤ) :
    ∃ n : ℕ, 0 < (coeff1 (barrierBlock n) k).re := by
  have harg : Tendsto (fun n : ℕ => Real.pi * (k : ℝ) * separation n)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul separation_tendsto_zero)
  have hcos : Tendsto (fun n : ℕ =>
      Real.cos (Real.pi * (k : ℝ) * separation n)) atTop (𝓝 1) := by
    rw [show (fun n : ℕ => Real.cos (Real.pi * (k : ℝ) * separation n)) =
        Real.cos ∘ (fun n : ℕ => Real.pi * (k : ℝ) * separation n) by rfl]
    rw [← Real.cos_zero]
    exact (Real.continuous_cos.tendsto 0).comp harg
  have heventually : ∀ᶠ n : ℕ in atTop,
      0 < Real.cos (Real.pi * (k : ℝ) * separation n) := by
    filter_upwards [hcos.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with n hn
    exact hn
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 heventually
  have hncos : 0 < Real.cos (Real.pi * (k : ℝ) * separation n) := hn n le_rfl
  refine ⟨n, ?_⟩
  rw [coeff_barrierBlock]
  simp only [Complex.ofReal_re]
  have hr0 : 0 < radius n := by linarith [radius_ge_half n]
  have hscale : 0 < poissonPeakScale (radius n) := by
    unfold poissonPeakScale
    exact div_pos (sub_pos.mpr (radius_lt_one n)) (by linarith)
  have hrpow : 0 < radius n ^ Int.natAbs k := pow_pos hr0 _
  have hcos2 : 0 < Real.cos (Real.pi * (k : ℝ) * separation n) ^ 2 :=
    sq_pos_of_ne_zero (ne_of_gt hncos)
  exact mul_pos
    (mul_pos
      (mul_pos
        (mul_pos (by norm_num : (0 : ℝ) < 4) (height_pos n)) hscale)
      hrpow)
    hcos2

end DGPS.SingularCounterexample
