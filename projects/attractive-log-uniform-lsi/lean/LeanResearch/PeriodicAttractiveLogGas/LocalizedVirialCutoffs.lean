import LeanResearch.PeriodicAttractiveLogGas.TorusDistance
import LeanResearch.PeriodicAttractiveLogGas.LogHessian
import LeanResearch.PeriodicAttractiveLogGas.LaplacianGeometry
import LeanResearch.PeriodicAttractiveLogGas.TorusLocalGradient
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The fixed cutoff from `eq:cutoff-profile` and the radial functions from
`eq:virial-cutoffs`.  The antiderivative is defined by its exact elementary
formula and identified with the integral over `(-∞, r]`.  All derivatives below
are ordinary derivatives of these actual functions. -/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace Laplacian

namespace PeriodicAttractiveLogGas.LocalizedVirialCutoffs

private def join (c : ℝ) (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ c then f x else g x

private theorem continuous_join {c : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hc : f c = g c) :
    Continuous (join c f g) := by
  apply hf.if_le hg continuous_id continuous_const
  intro x hx
  change x = c at hx
  simpa only [hx] using hc

private theorem hasDerivAt_join {c : ℝ} {f g df dg : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (df x) x) (hg : ∀ x, HasDerivAt g (dg x) x)
    (hc : f c = g c) (hd : df c = dg c) (x : ℝ) :
    HasDerivAt (join c f g) (join c df dg x) x := by
  rcases lt_trichotomy x c with hxc | heq | hcx
  · have heq : join c f g =ᶠ[𝓝 x] f := by
      filter_upwards [Iio_mem_nhds hxc] with y hy
      change y < c at hy
      simp only [join, ite_eq_left hy.le]
    simpa only [join, ite_eq_left hxc.le] using (hf x).congr_of_eventuallyEq heq
  · subst x
    have hl : HasDerivWithinAt (join c f g) (df c) (Iic c) c := by
      apply (hf c).hasDerivWithinAt.congr
      · intro y hy
        change y ≤ c at hy
        simp only [join, ite_eq_left hy]
      · simp only [join, le_refl, ite_true]
    have hr : HasDerivWithinAt (join c f g) (df c) (Ici c) c := by
      apply ((hg c).congr_deriv hd.symm).hasDerivWithinAt.congr
      · intro y hy
        change c ≤ y at hy
        by_cases h : y ≤ c
        · have he : y = c := le_antisymm h hy
          simpa only [he, join, le_refl, ite_true] using hc
        · simp only [join, ite_eq_right h]
      · simpa only [join, le_refl, ite_true] using hc
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ, join, le_refl, ite_true]
      using hl.union hr
  · have heq : join c f g =ᶠ[𝓝 x] g := by
      filter_upwards [Ioi_mem_nhds hcx] with y hy
      change c < y at hy
      simp only [join, ite_eq_right (not_le.mpr hy)]
    simpa only [join, ite_eq_right (not_le.mpr hcx)] using
      (hg x).congr_of_eventuallyEq heq

private def primitive (r : ℝ) : ℝ := r - Real.sin (2 * Real.pi * r) / (2 * Real.pi)
private def rawB (r : ℝ) : ℝ := 2 * Real.sin (Real.pi * r) ^ 2
private def rawB' (r : ℝ) : ℝ := 2 * Real.pi * Real.sin (2 * Real.pi * r)

/-- The zero extension of the specified profile `2 sin²(π r)`. -/
def b : ℝ → ℝ := join 1 (join 0 (fun _ ↦ 0) rawB) (fun _ ↦ 0)

/-- The derivative of the zero-extended profile, including both joining points. -/
def b' : ℝ → ℝ := join 1 (join 0 (fun _ ↦ 0) rawB') (fun _ ↦ 0)

/-- The elementary primitive; `H_eq_integral` identifies the exact source integral. -/
def H : ℝ → ℝ := join 1 (join 0 (fun _ ↦ 0) primitive) (fun _ ↦ 1)

private theorem hasDerivAt_primitive (r : ℝ) : HasDerivAt primitive (rawB r) r := by
  have h := (hasDerivAt_id r).sub
    (((hasDerivAt_id r).const_mul (2 * Real.pi)).sin.div_const (2 * Real.pi))
  convert! h using 1
  dsimp [rawB, id]
  rw [show 2 * Real.pi * r = 2 * (Real.pi * r) by ring, Real.cos_two_mul]
  field_simp [Real.pi_ne_zero]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * r)]

private theorem hasDerivAt_rawB (r : ℝ) : HasDerivAt rawB (rawB' r) r := by
  have h := ((((hasDerivAt_id r).const_mul Real.pi).sin).pow 2).const_mul 2
  convert! h using 1
  dsimp [rawB', id]
  rw [show 2 * Real.pi * r = 2 * (Real.pi * r) by ring, Real.sin_two_mul]
  ring

@[simp] theorem b_zero : b 0 = 0 := by simp [b, join]
@[simp] theorem b_one : b 1 = 0 := by simp [b, join, rawB]
@[simp] theorem b'_zero : b' 0 = 0 := by simp [b', join]
@[simp] theorem b'_one : b' 1 = 0 := by simp [b', join, rawB', Real.sin_two_mul]
@[simp] theorem H_zero : H 0 = 0 := by simp [H, join]
@[simp] theorem H_one : H 1 = 1 := by simp [H, join, primitive, Real.sin_two_mul]

theorem b_eq (r : ℝ) : b r = if r ∈ Icc (0 : ℝ) 1 then
    2 * Real.sin (Real.pi * r) ^ 2 else 0 := by
  by_cases hl : r ≤ 0
  · by_cases he : r = 0
    · simp [he]
    · have hlt : r < 0 := lt_of_le_of_ne hl he
      simp [b, join, hl, show r ≤ 1 by linarith, not_le.mpr hlt]
  · by_cases hu : r ≤ 1 <;> simp [b, join, hl, hu, rawB, le_of_lt (not_le.mp hl)]

theorem b_eq_zero_of_le {r : ℝ} (hr : r ≤ 0) : b r = 0 := by
  simp [b, join, hr, show r ≤ 1 by linarith]

theorem b_eq_zero_of_one_le {r : ℝ} (hr : 1 ≤ r) : b r = 0 := by
  rcases hr.eq_or_lt with h | h
  · simpa only [← h] using b_one
  · simp [b, join, not_le.mpr h]

theorem b'_eq_zero_of_le {r : ℝ} (hr : r ≤ 0) : b' r = 0 := by
  simp [b', join, hr, show r ≤ 1 by linarith]

theorem b'_eq_zero_of_one_le {r : ℝ} (hr : 1 ≤ r) : b' r = 0 := by
  rcases hr.eq_or_lt with h | h
  · simpa only [← h] using b'_one
  · simp [b', join, not_le.mpr h]

theorem H_eq_zero_of_le {r : ℝ} (hr : r ≤ 0) : H r = 0 := by
  simp [H, join, hr, show r ≤ 1 by linarith]

theorem H_eq_one_of_one_le {r : ℝ} (hr : 1 ≤ r) : H r = 1 := by
  rcases hr.eq_or_lt with h | h
  · simpa only [← h] using H_one
  · simp [H, join, not_le.mpr h]

theorem hasDerivAt_H (r : ℝ) : HasDerivAt H (b r) r := by
  apply hasDerivAt_join
    (hasDerivAt_join (fun x ↦ hasDerivAt_const x 0) hasDerivAt_primitive
      (by simp [primitive]) (by simp [rawB]))
    (fun x ↦ hasDerivAt_const x 1)
  · simp [join, primitive, Real.sin_two_mul]
  · simp [join, rawB]

theorem hasDerivAt_b (r : ℝ) : HasDerivAt b (b' r) r := by
  apply hasDerivAt_join
    (hasDerivAt_join (fun x ↦ hasDerivAt_const x 0) hasDerivAt_rawB
      (by simp [rawB]) (by simp [rawB']))
    (fun x ↦ hasDerivAt_const x 0)
  · simp [join, rawB]
  · simp [join, rawB', Real.sin_two_mul]

@[simp] theorem deriv_H : deriv H = b := funext fun r ↦ (hasDerivAt_H r).deriv
@[simp] theorem deriv_b : deriv b = b' := funext fun r ↦ (hasDerivAt_b r).deriv
@[simp] theorem second_deriv_H : deriv (deriv H) = b' := by rw [deriv_H, deriv_b]

theorem continuous_b' : Continuous b' := by
  apply continuous_join
    (continuous_join continuous_const (by unfold rawB'; fun_prop) (by simp [rawB']))
    continuous_const
  simp [join, rawB', Real.sin_two_mul]

theorem contDiff_b : ContDiff ℝ 1 b := by
  rw [contDiff_one_iff_deriv, deriv_b]
  exact ⟨fun r ↦ (hasDerivAt_b r).differentiableAt, continuous_b'⟩

theorem contDiff_H : ContDiff ℝ 2 H := by
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv, deriv_H]
  refine ⟨fun r ↦ (hasDerivAt_H r).differentiableAt, ?_, contDiff_b⟩
  norm_num

theorem b_nonneg (r : ℝ) : 0 ≤ b r := by
  rw [b_eq]
  split_ifs <;> positivity

theorem b_le_two (r : ℝ) : b r ≤ 2 := by
  rw [b_eq]
  split_ifs
  · nlinarith [Real.sin_sq_add_cos_sq (Real.pi * r), sq_nonneg (Real.cos (Real.pi * r))]
  · norm_num

theorem abs_b'_le (r : ℝ) : |b' r| ≤ 2 * Real.pi := by
  have hraw : |rawB' r| ≤ 2 * Real.pi := by
    dsimp [rawB']
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  dsimp [b', join]
  split_ifs
  all_goals first | exact hraw | simpa using (show 0 ≤ 2 * Real.pi by positivity)

theorem monotone_H : Monotone H :=
  monotone_of_deriv_nonneg (fun r ↦ (hasDerivAt_H r).differentiableAt)
    (by intro r; rw [deriv_H]; exact b_nonneg r)

theorem H_nonneg (r : ℝ) : 0 ≤ H r := by
  by_cases hr : r ≤ 0
  · rw [H_eq_zero_of_le hr]
  · simpa using monotone_H (le_of_not_ge hr)

theorem H_le_one (r : ℝ) : H r ≤ 1 := by
  by_cases hr : 1 ≤ r
  · rw [H_eq_one_of_one_le hr]
  · simpa using monotone_H (le_of_not_ge hr)

theorem H_mem_Icc (r : ℝ) : H r ∈ Icc (0 : ℝ) 1 := ⟨H_nonneg r, H_le_one r⟩

theorem hasCompactSupport_b : HasCompactSupport b := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  intro r hr
  rw [b_eq, ite_eq_right hr]

theorem integrable_b : Integrable b :=
  contDiff_b.continuous.integrable_of_hasCompactSupport hasCompactSupport_b

/-- Exact identification with the source's integral from minus infinity. -/
theorem H_eq_integral (r : ℝ) : H r = ∫ t in Iic r, b t := by
  have ht : Tendsto H atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Iic_mem_atBot (0 : ℝ)] with t ht
    exact (H_eq_zero_of_le ht).symm
  simpa only [sub_zero] using
    (integral_Iic_of_hasDerivAt_of_tendsto' (fun t _ ↦ hasDerivAt_H t)
      integrable_b.integrableOn ht).symm

theorem profile_derivative_bounds (r : ℝ) :
    0 ≤ deriv H r ∧ deriv H r ≤ 2 ∧ |deriv (deriv H) r| ≤ 2 * Real.pi := by
  simpa only [deriv_H, deriv_b] using ⟨b_nonneg r, b_le_two r, abs_b'_le r⟩

theorem profile_endpoint_derivatives :
    deriv H 0 = 0 ∧ deriv H 1 = 0 ∧ deriv (deriv H) 0 = 0 ∧
      deriv (deriv H) 1 = 0 := by simp

/-- Radial profile of the inner cutoff. -/
def phiProfile (s r : ℝ) : ℝ := H ((4 * s - r) / (2 * s))

/-- Product representation of the exact piecewise annulus cutoff.  Its factors
have disjoint transition regions when `2 ≤ K`. -/
def omegaProfile (s K r : ℝ) : ℝ :=
  H ((r - s) / s) * H ((2 * K * s - r) / (K * s))

theorem contDiff_phiProfile (s : ℝ) : ContDiff ℝ 2 (phiProfile s) := by
  exact contDiff_H.comp (by fun_prop)

theorem contDiff_omegaProfile (s K : ℝ) : ContDiff ℝ 2 (omegaProfile s K) := by
  exact (contDiff_H.comp (by fun_prop)).mul (contDiff_H.comp (by fun_prop))

theorem phiProfile_eq_one {s r : ℝ} (hs : 0 < s) (hr : r ≤ 2 * s) :
    phiProfile s r = 1 := by
  apply H_eq_one_of_one_le
  apply (le_div_iff₀ (by positivity : 0 < 2 * s)).2
  linarith

theorem phiProfile_eq_zero {s r : ℝ} (hs : 0 < s) (hr : 4 * s ≤ r) :
    phiProfile s r = 0 := by
  apply H_eq_zero_of_le
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem omegaProfile_eq_inner {s K r : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (hr : r ≤ 2 * s) : omegaProfile s K r = H ((r - s) / s) := by
  have hKs : 0 < K * s := mul_pos (by linarith) hs
  have h2Ks : 2 * s ≤ K * s := mul_le_mul_of_nonneg_right hK hs.le
  have ho : H ((2 * K * s - r) / (K * s)) = 1 := by
    apply H_eq_one_of_one_le
    apply (le_div_iff₀ hKs).2
    nlinarith
  simp only [omegaProfile, ho, mul_one]

theorem omegaProfile_eq_one {s K r : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (hl : 2 * s ≤ r) (hu : r ≤ K * s) : omegaProfile s K r = 1 := by
  have hi : H ((r - s) / s) = 1 := H_eq_one_of_one_le
    ((le_div_iff₀ hs).2 (by linarith))
  have ho : H ((2 * K * s - r) / (K * s)) = 1 := H_eq_one_of_one_le
    ((le_div_iff₀ (mul_pos (by linarith : 0 < K) hs)).2 (by nlinarith))
  simp [omegaProfile, hi, ho]

theorem omegaProfile_eq_outer {s K r : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (hr : K * s ≤ r) : omegaProfile s K r = H ((2 * K * s - r) / (K * s)) := by
  have h2Ks : 2 * s ≤ K * s := mul_le_mul_of_nonneg_right hK hs.le
  have hi : H ((r - s) / s) = 1 := H_eq_one_of_one_le
    ((le_div_iff₀ hs).2 (by linarith))
  simp [omegaProfile, hi]

theorem omegaProfile_eq_zero_inner {s K r : ℝ} (hs : 0 < s) (hr : r ≤ s) :
    omegaProfile s K r = 0 := by
  have hi : H ((r - s) / s) = 0 := H_eq_zero_of_le
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hs.le)
  simp [omegaProfile, hi]

theorem omegaProfile_eq_zero_outer {s K r : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hr : 2 * K * s ≤ r) : omegaProfile s K r = 0 := by
  have ho : H ((2 * K * s - r) / (K * s)) = 0 := H_eq_zero_of_le
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) (mul_nonneg hK.le hs.le))
  simp [omegaProfile, ho]

theorem phiProfile_mem_Icc (s r : ℝ) : phiProfile s r ∈ Icc (0 : ℝ) 1 := H_mem_Icc _

theorem omegaProfile_mem_Icc (s K r : ℝ) : omegaProfile s K r ∈ Icc (0 : ℝ) 1 := by
  exact ⟨mul_nonneg (H_nonneg _) (H_nonneg _),
    (mul_le_mul_of_nonneg_right (H_le_one _) (H_nonneg _)).trans (by simpa using H_le_one _)⟩

theorem hasDerivAt_phiProfile (s r : ℝ) :
    HasDerivAt (phiProfile s) (-b ((4 * s - r) / (2 * s)) / (2 * s)) r := by
  convert! (hasDerivAt_H _).comp r
    (((hasDerivAt_id r).const_sub (4 * s)).div_const (2 * s)) using 1
  dsimp [id]
  ring

theorem deriv_phiProfile (s r : ℝ) :
    deriv (phiProfile s) r = -b ((4 * s - r) / (2 * s)) / (2 * s) :=
  (hasDerivAt_phiProfile s r).deriv

theorem hasDerivAt_deriv_phiProfile (s r : ℝ) :
    HasDerivAt (deriv (phiProfile s))
      (b' ((4 * s - r) / (2 * s)) / (4 * s ^ 2)) r := by
  have h := (((hasDerivAt_b _).comp r
    (((hasDerivAt_id r).const_sub (4 * s)).div_const (2 * s))).neg).div_const (2 * s)
  have he : deriv (phiProfile s) = fun t ↦ -b ((4 * s - t) / (2 * s)) / (2 * s) :=
    funext (deriv_phiProfile s)
  rw [he]
  convert! h using 1
  dsimp [id]
  ring

theorem second_deriv_phiProfile (s r : ℝ) :
    deriv (deriv (phiProfile s)) r = b' ((4 * s - r) / (2 * s)) / (4 * s ^ 2) :=
  (hasDerivAt_deriv_phiProfile s r).deriv

theorem abs_deriv_phiProfile_le {s : ℝ} (hs : 0 < s) (r : ℝ) :
    |deriv (phiProfile s) r| ≤ 1 / s := by
  rw [deriv_phiProfile, abs_div, abs_neg, abs_of_nonneg (b_nonneg _),
    abs_of_pos (mul_pos (by norm_num) hs)]
  calc
    b ((4 * s - r) / (2 * s)) / (2 * s) ≤ 2 / (2 * s) :=
      div_le_div_of_nonneg_right (b_le_two _) (by positivity)
    _ = 1 / s := by ring

theorem abs_second_deriv_phiProfile_le {s : ℝ} (hs : 0 < s) (r : ℝ) :
    |deriv (deriv (phiProfile s)) r| ≤ Real.pi / (2 * s ^ 2) := by
  rw [second_deriv_phiProfile, abs_div, abs_of_pos (by positivity : 0 < 4 * s ^ 2)]
  calc
    |b' ((4 * s - r) / (2 * s))| / (4 * s ^ 2) ≤
        (2 * Real.pi) / (4 * s ^ 2) :=
      div_le_div_of_nonneg_right (abs_b'_le _) (by positivity)
    _ = Real.pi / (2 * s ^ 2) := by ring

theorem deriv_phiProfile_eq_zero_inner {s r : ℝ} (hs : 0 < s) (hr : r ≤ 2 * s) :
    deriv (phiProfile s) r = 0 := by
  rw [deriv_phiProfile, b_eq_zero_of_one_le, neg_zero, zero_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * s)).2
  linarith

theorem second_deriv_phiProfile_eq_zero_inner {s r : ℝ} (hs : 0 < s)
    (hr : r ≤ 2 * s) : deriv (deriv (phiProfile s)) r = 0 := by
  rw [second_deriv_phiProfile, b'_eq_zero_of_one_le, zero_div]
  apply (le_div_iff₀ (by positivity : 0 < 2 * s)).2
  linarith

theorem deriv_phiProfile_eq_zero_outer {s r : ℝ} (hs : 0 < s) (hr : 4 * s ≤ r) :
    deriv (phiProfile s) r = 0 := by
  rw [deriv_phiProfile, b_eq_zero_of_le, neg_zero, zero_div]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem second_deriv_phiProfile_eq_zero_outer {s r : ℝ} (hs : 0 < s)
    (hr : 4 * s ≤ r) : deriv (deriv (phiProfile s)) r = 0 := by
  rw [second_deriv_phiProfile, b'_eq_zero_of_le, zero_div]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

theorem hasDerivAt_omegaProfile (s K r : ℝ) :
    HasDerivAt (omegaProfile s K)
      (b ((r - s) / s) / s * H ((2 * K * s - r) / (K * s)) -
        H ((r - s) / s) * (b ((2 * K * s - r) / (K * s)) / (K * s))) r := by
  have hi := (hasDerivAt_H _).comp r (((hasDerivAt_id r).sub_const s).div_const s)
  have ho := (hasDerivAt_H _).comp r
    (((hasDerivAt_id r).const_sub (2 * K * s)).div_const (K * s))
  convert! hi.mul ho using 1
  dsimp [id, Function.comp_def]
  ring

theorem deriv_omegaProfile_inner {s K r : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (hr : r ≤ 2 * s) : deriv (omegaProfile s K) r = b ((r - s) / s) / s := by
  have hKs : 0 < K * s := mul_pos (by linarith) hs
  have h2Ks : 2 * s ≤ K * s := mul_le_mul_of_nonneg_right hK hs.le
  have ha : 1 ≤ (2 * K * s - r) / (K * s) := (le_div_iff₀ hKs).2 (by nlinarith)
  rw [(hasDerivAt_omegaProfile s K r).deriv, H_eq_one_of_one_le ha,
    b_eq_zero_of_one_le ha]
  ring

theorem deriv_omegaProfile_outer {s K r : ℝ} (hs : 0 < s) (hr : 2 * s ≤ r) :
    deriv (omegaProfile s K) r = -b ((2 * K * s - r) / (K * s)) / (K * s) := by
  have ha : 1 ≤ (r - s) / s := (le_div_iff₀ hs).2 (by linarith)
  rw [(hasDerivAt_omegaProfile s K r).deriv, H_eq_one_of_one_le ha,
    b_eq_zero_of_one_le ha]
  ring

theorem abs_deriv_omegaProfile_le {s K : ℝ} (hs : 0 < s) (hK : 2 ≤ K) (r : ℝ) :
    |deriv (omegaProfile s K) r| ≤ 2 / s := by
  by_cases hr : r ≤ 2 * s
  · rw [deriv_omegaProfile_inner hs hK hr, abs_div, abs_of_nonneg (b_nonneg _),
      abs_of_pos hs]
    exact div_le_div_of_nonneg_right (b_le_two _) hs.le
  · have hKs : 0 < K * s := mul_pos (by linarith) hs
    rw [deriv_omegaProfile_outer hs (le_of_not_ge hr), abs_div, abs_neg,
      abs_of_nonneg (b_nonneg _), abs_of_pos hKs]
    calc
      b ((2 * K * s - r) / (K * s)) / (K * s) ≤ 2 / (K * s) :=
        div_le_div_of_nonneg_right (b_le_two _) hKs.le
      _ ≤ 2 / s := div_le_div_of_nonneg_left (by norm_num) hs
        (by nlinarith [mul_nonneg (show 0 ≤ K - 1 by linarith) hs.le])

/-- Actual Euclidean radial lifts. -/
def phiEuclidean (s : ℝ) (x : PlanarSpace) : ℝ := phiProfile s ‖x‖
def omegaEuclidean (s K : ℝ) (x : PlanarSpace) : ℝ := omegaProfile s K ‖x‖

private theorem contDiff_radial {R : ℝ → ℝ} (hR : ContDiff ℝ 2 R)
    {ε c : ℝ} (hε : 0 < ε) (hc : ∀ r, 0 ≤ r → r < ε → R r = c) :
    ContDiff ℝ 2 (fun x : PlanarSpace ↦ R ‖x‖) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : PlanarSpace) hε] with y hy
    exact hc _ (norm_nonneg _) (by simpa only [mem_ball, dist_zero_right] using hy)
  · exact hR.contDiffAt.comp x (contDiffAt_norm ℝ hx)

theorem contDiff_phiEuclidean {s : ℝ} (hs : 0 < s) : ContDiff ℝ 2 (phiEuclidean s) := by
  apply contDiff_radial (contDiff_phiProfile s) (show 0 < 2 * s by positivity)
  intro r _ hr
  exact phiProfile_eq_one hs hr.le

theorem contDiff_omegaEuclidean {s K : ℝ} (hs : 0 < s) :
    ContDiff ℝ 2 (omegaEuclidean s K) := by
  apply contDiff_radial (contDiff_omegaProfile s K) hs
  intro r _ hr
  exact omegaProfile_eq_zero_inner hs hr.le

private theorem radial_tsupport {R : ℝ → ℝ} {ρ : ℝ}
    (hR : ∀ r, ρ ≤ r → R r = 0) :
    tsupport (fun x : PlanarSpace ↦ R ‖x‖) ⊆ closedBall 0 ρ := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  apply mem_closedBall_zero_iff.mpr
  by_contra h
  exact hx (hR _ (le_of_not_ge h))

theorem tsupport_phiEuclidean {s : ℝ} (hs : 0 < s) :
    tsupport (phiEuclidean s) ⊆ closedBall 0 (4 * s) :=
  radial_tsupport (fun _ hr ↦ phiProfile_eq_zero hs hr)

theorem tsupport_omegaEuclidean {s K : ℝ} (hs : 0 < s) (hK : 0 < K) :
    tsupport (omegaEuclidean s K) ⊆ closedBall 0 (2 * K * s) :=
  radial_tsupport (fun _ hr ↦ omegaProfile_eq_zero_outer hs hK hr)

theorem hasCompactSupport_phiEuclidean {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (phiEuclidean s) :=
  (isCompact_closedBall (0 : PlanarSpace) (4 * s)).of_isClosed_subset
    isClosed_closure (tsupport_phiEuclidean hs)

theorem hasCompactSupport_omegaEuclidean {s K : ℝ} (hs : 0 < s) (hK : 0 < K) :
    HasCompactSupport (omegaEuclidean s K) :=
  (isCompact_closedBall (0 : PlanarSpace) (2 * K * s)).of_isClosed_subset
    isClosed_closure (tsupport_omegaEuclidean hs hK)

/-- The actual periodic functions use the manuscript's Euclidean quotient distance. -/
def phi (ξ : Torus) (s : ℝ) (z : Torus) : ℝ := phiProfile s (torusEuclideanDist z ξ)
def omega (ξ : Torus) (s K : ℝ) (z : Torus) : ℝ := omegaProfile s K (torusEuclideanDist z ξ)

theorem phi_eq_one {ξ z : Torus} {s : ℝ} (hs : 0 < s)
    (hz : torusEuclideanDist z ξ ≤ 2 * s) : phi ξ s z = 1 := phiProfile_eq_one hs hz

theorem phi_eq_zero {ξ z : Torus} {s : ℝ} (hs : 0 < s)
    (hz : 4 * s ≤ torusEuclideanDist z ξ) : phi ξ s z = 0 := phiProfile_eq_zero hs hz

theorem omega_eq_inner {ξ z : Torus} {s K : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (hz : torusEuclideanDist z ξ ≤ 2 * s) :
    omega ξ s K z = H ((torusEuclideanDist z ξ - s) / s) :=
  omegaProfile_eq_inner hs hK hz

theorem omega_eq_one {ξ z : Torus} {s K : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (hl : 2 * s ≤ torusEuclideanDist z ξ) (hu : torusEuclideanDist z ξ ≤ K * s) :
    omega ξ s K z = 1 := omegaProfile_eq_one hs hK hl hu

theorem omega_eq_outer {ξ z : Torus} {s K : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (hz : K * s ≤ torusEuclideanDist z ξ) :
    omega ξ s K z = H ((2 * K * s - torusEuclideanDist z ξ) / (K * s)) :=
  omegaProfile_eq_outer hs hK hz

theorem omega_eq_zero_inner {ξ z : Torus} {s K : ℝ} (hs : 0 < s)
    (hz : torusEuclideanDist z ξ ≤ s) : omega ξ s K z = 0 :=
  omegaProfile_eq_zero_inner hs hz

theorem omega_eq_zero_outer {ξ z : Torus} {s K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hz : 2 * K * s ≤ torusEuclideanDist z ξ) : omega ξ s K z = 0 :=
  omegaProfile_eq_zero_outer hs hK hz

theorem phi_mem_Icc (ξ : Torus) (s : ℝ) (z : Torus) : phi ξ s z ∈ Icc (0 : ℝ) 1 :=
  phiProfile_mem_Icc _ _

theorem omega_mem_Icc (ξ : Torus) (s K : ℝ) (z : Torus) : omega ξ s K z ∈ Icc (0 : ℝ) 1 :=
  omegaProfile_mem_Icc _ _ _

private theorem contDiff_periodicSum_two {f : PlanarSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) : ContDiff ℝ 2 (periodicSum f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨S, hS⟩ := finsum_eventually_eq_sum (locallyFinite_integer_translates hc) x
  have hsum : ContDiff ℝ 2 (fun y : PlanarSpace ↦ ∑ k ∈ S, f (y + frequencyVector k)) :=
    ContDiff.sum (fun k _ ↦ hf.comp (contDiff_id.add contDiff_const))
  exact hsum.contDiffAt.congr_of_eventuallyEq hS

private theorem radial_periodization_eq {R : ℝ → ℝ} {ρ : ℝ}
    (hR : ∀ r, ρ ≤ r → R r = 0) (hρ : ρ < 1 / 2) (z : Torus) :
    torusPeriodization (fun x : PlanarSpace ↦ R ‖x‖) z = R (torusEuclideanNorm z) := by
  have hsupp : tsupport (fun x : PlanarSpace ↦ R ‖x‖) ⊆
      euclideanFundamentalBox (centeredBoxAnchor 0) := by
    intro x hx
    apply euclideanOpenBox_subset_fundamentalBox
    apply mem_centeredOpenBox_of_norm_lt_half
    exact lt_of_le_of_lt (mem_closedBall_zero_iff.mp (radial_tsupport hR hx)) hρ
  rw [← torusQuotient_centeredLift z, torusPeriodization_lift,
    periodicSum_eq_on_box hsupp (centeredLift_mem_fundamentalBox z),
    torusQuotient_centeredLift, norm_centeredLift]

theorem phi_lift_eq_periodicSum {s : ℝ} (hs : 0 < s) (hsize : s ≤ 1 / 64)
    (ξ : Torus) (x : PlanarSpace) :
    phi ξ s (torusQuotient x) = periodicSum (phiEuclidean s) (x - centeredLift ξ) := by
  unfold phiEuclidean
  rw [← torusPeriodization_lift, radial_periodization_eq
    (fun _ hr ↦ phiProfile_eq_zero hs hr) (by linarith : 4 * s < 1 / 2)]
  simp only [phi, torusEuclideanDist, torusQuotient_sub, torusQuotient_centeredLift]

theorem omega_lift_eq_periodicSum {s K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hsize : 2 * K * s ≤ 1 / 4) (ξ : Torus) (x : PlanarSpace) :
    omega ξ s K (torusQuotient x) = periodicSum (omegaEuclidean s K) (x - centeredLift ξ) := by
  unfold omegaEuclidean
  rw [← torusPeriodization_lift, radial_periodization_eq
    (fun _ hr ↦ omegaProfile_eq_zero_outer hs hK hr) (by linarith : 2 * K * s < 1 / 2)]
  simp only [omega, torusEuclideanDist, torusQuotient_sub, torusQuotient_centeredLift]

/-- C2 across the center, both radial joins, and every fundamental-domain seam. -/
theorem contDiff_phi_lift {s : ℝ} (hs : 0 < s) (hsize : s ≤ 1 / 64) (ξ : Torus) :
    ContDiff ℝ 2 (fun x : PlanarSpace ↦ phi ξ s (torusQuotient x)) := by
  simp_rw [phi_lift_eq_periodicSum hs hsize]
  exact (contDiff_periodicSum_two (contDiff_phiEuclidean hs)
    (hasCompactSupport_phiEuclidean hs)).comp (contDiff_id.sub contDiff_const)

/-- The product representation matches both transition regions at second order. -/
theorem contDiff_omega_lift {s K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hsize : 2 * K * s ≤ 1 / 4) (ξ : Torus) :
    ContDiff ℝ 2 (fun x : PlanarSpace ↦ omega ξ s K (torusQuotient x)) := by
  simp_rw [omega_lift_eq_periodicSum hs hK hsize]
  exact (contDiff_periodicSum_two (contDiff_omegaEuclidean hs)
    (hasCompactSupport_omegaEuclidean hs hK)).comp (contDiff_id.sub contDiff_const)

private theorem hasFDerivAt_norm {x : PlanarSpace} (hx : x ≠ 0) :
    HasFDerivAt (fun y : PlanarSpace ↦ ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  convert! h using 1
  · funext y
    simp only [Real.sqrt_sq (norm_nonneg y)]
  · ext u
    simp only [Real.sqrt_sq (norm_nonneg x), smul_apply,
      innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    field_simp

private theorem hasFDerivAt_radial {R : ℝ → ℝ} {d : ℝ} {x : PlanarSpace}
    (hR : HasDerivAt R d ‖x‖) (hx : x ≠ 0) :
    HasFDerivAt (fun y : PlanarSpace ↦ R ‖y‖) ((d / ‖x‖) • innerSL ℝ x) x := by
  simpa only [Function.comp_def, smul_smul, div_eq_mul_inv] using
    hR.comp_hasFDerivAt x (hasFDerivAt_norm hx)

private theorem radial_fderiv {R dR : ℝ → ℝ}
    (hR : ∀ r, HasDerivAt R (dR r) r) {x : PlanarSpace} (hx : x ≠ 0) :
    fderiv ℝ (fun y : PlanarSpace ↦ R ‖y‖) x = (dR ‖x‖ / ‖x‖) • innerSL ℝ x :=
  (hasFDerivAt_radial (hR _) hx).fderiv

/-- The genuine second derivative of a radial lift away from the center. -/
private theorem radial_second_fderiv {R dR : ℝ → ℝ} {dd : ℝ}
    (hR : ∀ r, HasDerivAt R (dR r) r) {x : PlanarSpace} (hx : x ≠ 0)
    (hdR : HasDerivAt dR dd ‖x‖) (u v : PlanarSpace) :
    fderiv ℝ (fderiv ℝ (fun y : PlanarSpace ↦ R ‖y‖)) x u v =
      (dd / ‖x‖ ^ 2 - dR ‖x‖ / ‖x‖ ^ 3) * ⟪x, u⟫ * ⟪x, v⟫ +
        (dR ‖x‖ / ‖x‖) * ⟪u, v⟫ := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hc := (hdR.div (hasDerivAt_id ‖x‖) hn).comp_hasFDerivAt x (hasFDerivAt_norm hx)
  have hd := hc.smul (innerSL ℝ (E := PlanarSpace)).hasFDerivAt
  simp only [Pi.div_apply, Function.comp_def, id_eq, mul_one] at hd
  change HasFDerivAt (fun y : PlanarSpace ↦ (dR ‖y‖ / ‖y‖) • innerSL ℝ y) _ x at hd
  have heq : fderiv ℝ (fun y : PlanarSpace ↦ R ‖y‖) =ᶠ[𝓝 x]
      (fun y : PlanarSpace ↦ (dR ‖y‖ / ‖y‖) • innerSL ℝ y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact radial_fderiv hR hy
  rw [heq.fderiv_eq, hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_eq_mul]
  field_simp
  ring_nf
  rfl

theorem fderiv_phiEuclidean {s : ℝ} {x : PlanarSpace} (hx : x ≠ 0) :
    fderiv ℝ (phiEuclidean s) x =
      (deriv (phiProfile s) ‖x‖ / ‖x‖) • innerSL ℝ x := by
  exact radial_fderiv (fun r ↦ ((contDiff_phiProfile s).differentiable
    (by norm_num) r).hasDerivAt) hx

theorem second_fderiv_phiEuclidean {s : ℝ} {x : PlanarSpace} (hx : x ≠ 0)
    (u v : PlanarSpace) :
    fderiv ℝ (fderiv ℝ (phiEuclidean s)) x u v =
      (deriv (deriv (phiProfile s)) ‖x‖ / ‖x‖ ^ 2 -
        deriv (phiProfile s) ‖x‖ / ‖x‖ ^ 3) * ⟪x, u⟫ * ⟪x, v⟫ +
        (deriv (phiProfile s) ‖x‖ / ‖x‖) * ⟪u, v⟫ := by
  apply radial_second_fderiv
    (fun r ↦ ((contDiff_phiProfile s).differentiable (by norm_num) r).hasDerivAt) hx
  exact ((contDiff_phiProfile s).differentiable_deriv_two _).hasDerivAt

theorem fderiv_omegaEuclidean {s K : ℝ} {x : PlanarSpace} (hx : x ≠ 0) :
    fderiv ℝ (omegaEuclidean s K) x =
      (deriv (omegaProfile s K) ‖x‖ / ‖x‖) • innerSL ℝ x := by
  exact radial_fderiv (fun r ↦ ((contDiff_omegaProfile s K).differentiable
    (by norm_num) r).hasDerivAt) hx

private theorem phiEuclidean_eventually_one {s : ℝ} (hs : 0 < s) :
    phiEuclidean s =ᶠ[𝓝 (0 : PlanarSpace)] (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [ball_mem_nhds (0 : PlanarSpace) (show 0 < 2 * s by positivity)] with y hy
  apply phiProfile_eq_one hs
  exact (show ‖y‖ < 2 * s by simpa only [mem_ball, dist_zero_right] using hy).le

private theorem omegaEuclidean_eventually_zero {s K : ℝ} (hs : 0 < s) :
    omegaEuclidean s K =ᶠ[𝓝 (0 : PlanarSpace)] (fun _ ↦ (0 : ℝ)) := by
  filter_upwards [ball_mem_nhds (0 : PlanarSpace) hs] with y hy
  apply omegaProfile_eq_zero_inner hs
  exact (show ‖y‖ < s by simpa only [mem_ball, dist_zero_right] using hy).le

@[simp] theorem fderiv_phiEuclidean_zero {s : ℝ} (hs : 0 < s) :
    fderiv ℝ (phiEuclidean s) 0 = 0 := by
  rw [(phiEuclidean_eventually_one hs).fderiv_eq]
  simp

@[simp] theorem second_fderiv_phiEuclidean_zero {s : ℝ} (hs : 0 < s) :
    fderiv ℝ (fderiv ℝ (phiEuclidean s)) 0 = 0 := by
  rw [(phiEuclidean_eventually_one hs).fderiv.fderiv_eq]
  simp

@[simp] theorem fderiv_omegaEuclidean_zero {s K : ℝ} (hs : 0 < s) :
    fderiv ℝ (omegaEuclidean s K) 0 = 0 := by
  rw [(omegaEuclidean_eventually_zero hs).fderiv_eq]
  simp

private theorem norm_radial_covector {d : ℝ} {x : PlanarSpace} (hx : x ≠ 0) :
    ‖(d / ‖x‖) • innerSL ℝ x‖ = |d| := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_div,
    abs_of_nonneg (norm_nonneg _)]
  exact div_mul_cancel₀ _ hn

theorem norm_fderiv_phiEuclidean_le {s : ℝ} (hs : 0 < s) (x : PlanarSpace) :
    ‖fderiv ℝ (phiEuclidean s) x‖ ≤ 1 / s := by
  by_cases hx : x = 0
  · subst x
    rw [fderiv_phiEuclidean_zero hs, norm_zero]
    positivity
  · rw [fderiv_phiEuclidean hx, norm_radial_covector hx]
    exact abs_deriv_phiProfile_le hs _

theorem norm_fderiv_omegaEuclidean_le {s K : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (x : PlanarSpace) : ‖fderiv ℝ (omegaEuclidean s K) x‖ ≤ 2 / s := by
  by_cases hx : x = 0
  · subst x
    rw [fderiv_omegaEuclidean_zero hs, norm_zero]
    positivity
  · rw [fderiv_omegaEuclidean hx, norm_radial_covector hx]
    exact abs_deriv_omegaProfile_le hs hK _

/-- Tangential eigenvalue bound, with the inner plateau used at small radii. -/
theorem abs_tangential_phiProfile_le {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    |deriv (phiProfile s) r / r| ≤ 1 / (2 * s ^ 2) := by
  by_cases hsmall : r ≤ 2 * s
  · rw [deriv_phiProfile_eq_zero_inner hs hsmall, zero_div, abs_zero]
    positivity
  · rw [abs_div, abs_of_pos hr]
    calc
      |deriv (phiProfile s) r| / r ≤ (1 / s) / r :=
        div_le_div_of_nonneg_right (abs_deriv_phiProfile_le hs r) hr.le
      _ ≤ (1 / s) / (2 * s) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (le_of_not_ge hsmall)
      _ = 1 / (2 * s ^ 2) := by ring

/-- An orthogonal radial/tangential split controls the operator norm by the
larger eigenvalue, without adding the two bounds. -/
private theorem radial_bilinear_bound {e u v : PlanarSpace} (he : ‖e‖ = 1)
    {a b M : ℝ} (hM : 0 ≤ M) (ha : |a| ≤ M) (hb : |b| ≤ M) :
    |a * ⟪e, u⟫ * ⟪e, v⟫ + b * (⟪u, v⟫ - ⟪e, u⟫ * ⟪e, v⟫)| ≤
      M * ‖u‖ * ‖v‖ := by
  let α : ℝ := ⟪e, u⟫
  let w : PlanarSpace := u - α • e
  let z : PlanarSpace := (a * α) • e + b • w
  have hew : ⟪e, w⟫ = 0 := by
    simp [w, α, inner_sub_right, real_inner_smul_right, he]
  have hu : u = α • e + w := by dsimp [w]; abel
  have hu2 : ‖u‖ ^ 2 = α ^ 2 + ‖w‖ ^ 2 := by
    conv_lhs => rw [hu, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs,
      real_inner_smul_left, hew, mul_zero, add_zero]
  have hz2 : ‖z‖ ^ 2 = a ^ 2 * α ^ 2 + b ^ 2 * ‖w‖ ^ 2 := by
    dsimp [z]
    rw [norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, he, mul_one, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right, hew, mul_zero, add_zero]
  have ha2 : a ^ 2 ≤ M ^ 2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg a) ha
  have hb2 : b ^ 2 ≤ M ^ 2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg b) hb
  have hz : ‖z‖ ≤ M * ‖u‖ := by
    have hsq : ‖z‖ ^ 2 ≤ (M * ‖u‖) ^ 2 := by
      rw [hz2, mul_pow, hu2, mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right ha2 (sq_nonneg α))
        (mul_le_mul_of_nonneg_right hb2 (sq_nonneg ‖w‖))
    nlinarith [norm_nonneg z, mul_nonneg hM (norm_nonneg u)]
  have heq : ⟪z, v⟫ = a * ⟪e, u⟫ * ⟪e, v⟫ +
      b * (⟪u, v⟫ - ⟪e, u⟫ * ⟪e, v⟫) := by
    simp only [z, w, α, inner_add_left, inner_sub_left, real_inner_smul_left]
  rw [← heq]
  exact (abs_real_inner_le_norm z v).trans (mul_le_mul_of_nonneg_right hz (norm_nonneg v))

theorem norm_second_fderiv_phiEuclidean_le {s : ℝ} (hs : 0 < s) (x : PlanarSpace) :
    ‖fderiv ℝ (fderiv ℝ (phiEuclidean s)) x‖ ≤ 2 / s ^ 2 := by
  by_cases hx : x = 0
  · subst x
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have he : fderiv ℝ (fderiv ℝ (phiEuclidean s)) 0 u v = 0 := by
      rw [second_fderiv_phiEuclidean_zero hs]
      rfl
    rw [he, norm_zero]
    positivity
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let e : PlanarSpace := ‖x‖⁻¹ • x
  have he : ‖e‖ = 1 := by
    simp only [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]
    exact inv_mul_cancel₀ hr.ne'
  have ha : |deriv (deriv (phiProfile s)) ‖x‖| ≤ 2 / s ^ 2 := by
    calc
      _ ≤ Real.pi / (2 * s ^ 2) := abs_second_deriv_phiProfile_le hs _
      _ ≤ 2 / s ^ 2 := by
        apply (div_le_div_iff₀ (by positivity : 0 < 2 * s ^ 2) (by positivity : 0 < s ^ 2)).2
        nlinarith [mul_le_mul_of_nonneg_right Real.pi_le_four (sq_nonneg s)]
  have hb : |deriv (phiProfile s) ‖x‖ / ‖x‖| ≤ 2 / s ^ 2 := by
    calc
      _ ≤ 1 / (2 * s ^ 2) := abs_tangential_phiProfile_le hs hr
      _ ≤ 2 / s ^ 2 := by
        apply (div_le_div_iff₀ (by positivity : 0 < 2 * s ^ 2) (by positivity : 0 < s ^ 2)).2
        nlinarith [sq_nonneg s]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [Real.norm_eq_abs, second_fderiv_phiEuclidean hx]
  have heq :
      (deriv (deriv (phiProfile s)) ‖x‖ / ‖x‖ ^ 2 -
        deriv (phiProfile s) ‖x‖ / ‖x‖ ^ 3) * ⟪x, u⟫ * ⟪x, v⟫ +
        (deriv (phiProfile s) ‖x‖ / ‖x‖) * ⟪u, v⟫ =
      deriv (deriv (phiProfile s)) ‖x‖ * ⟪e, u⟫ * ⟪e, v⟫ +
        (deriv (phiProfile s) ‖x‖ / ‖x‖) * (⟪u, v⟫ - ⟪e, u⟫ * ⟪e, v⟫) := by
    simp only [e, real_inner_smul_left]
    field_simp
    ring
  rw [heq]
  exact radial_bilinear_bound he (by positivity) ha hb

theorem laplacian_phiEuclidean {s : ℝ} {x : PlanarSpace} (hx : x ≠ 0) :
    Δ (phiEuclidean s) x = deriv (deriv (phiProfile s)) ‖x‖ +
      deriv (phiProfile s) ‖x‖ / ‖x‖ := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (phiEuclidean s)
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    second_fderiv_phiEuclidean hx, EuclideanSpace.inner_basisFun_real]
  simp only [EuclideanSpace.basisFun_apply, PiLp.single_apply, ite_true, mul_assoc, ← sq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← EuclideanSpace.real_norm_sq_eq x]
  field_simp
  ring

theorem abs_laplacian_phiEuclidean_le {s : ℝ} (hs : 0 < s) (x : PlanarSpace) :
    |Δ (phiEuclidean s) x| ≤ 3 / s ^ 2 := by
  by_cases hx : x = 0
  · subst x
    have heq := (laplacian_congr_nhds (phiEuclidean_eventually_one hs)).eq_of_nhds
    rw [heq]
    simp only [laplacian_const, Pi.zero_apply, abs_zero]
    positivity
  · rw [laplacian_phiEuclidean hx]
    calc
      _ ≤ |deriv (deriv (phiProfile s)) ‖x‖| + |deriv (phiProfile s) ‖x‖ / ‖x‖| :=
        abs_add_le _ _
      _ ≤ Real.pi / (2 * s ^ 2) + 1 / (2 * s ^ 2) :=
        add_le_add (abs_second_deriv_phiProfile_le hs _)
          (abs_tangential_phiProfile_le hs (norm_pos_iff.mpr hx))
      _ ≤ 3 / s ^ 2 := by
        apply (le_div_iff₀ (by positivity : 0 < s ^ 2)).2
        field_simp
        nlinarith [Real.pi_le_four]

private theorem radial_lift_germ {R : ℝ → ℝ} {ρ : ℝ}
    (hR : ∀ r, ρ ≤ r → R r = 0) (hρ : ρ < 1 / 2) (ξ : Torus) (x : PlanarSpace) :
    (fun y : PlanarSpace ↦ R (torusEuclideanDist (torusQuotient y) ξ)) =ᶠ[𝓝 x]
      (fun y ↦ R ‖y + (centeredLift (torusQuotient x - ξ) - x)‖) := by
  let w : PlanarSpace := centeredLift (torusQuotient x - ξ)
  let a : PlanarSpace := w - x
  have hxw : x + a = w := by dsimp [a]; abel
  have hw : ‖w‖ = torusEuclideanDist (torusQuotient x) ξ := norm_centeredLift _
  have hq (y : PlanarSpace) : torusQuotient (y + a) = torusQuotient y - ξ := by
    dsimp [a, w]
    rw [torusQuotient_add, torusQuotient_sub, torusQuotient_centeredLift]
    abel
  have hn : Continuous (fun y : PlanarSpace ↦ ‖y + a‖) := by fun_prop
  have ht : Continuous (fun y : PlanarSpace ↦ torusEuclideanDist (torusQuotient y) ξ) :=
    continuous_torusEuclideanNorm.comp
      (isOpenQuotientMap_torusQuotient.continuous.sub continuous_const)
  change (fun y : PlanarSpace ↦ R (torusEuclideanDist (torusQuotient y) ξ)) =ᶠ[𝓝 x]
    (fun y ↦ R ‖y + a‖)
  by_cases hr : torusEuclideanDist (torusQuotient x) ξ < 1 / 2
  · have hxn : ‖x + a‖ < 1 / 2 := by rw [hxw, hw]; exact hr
    filter_upwards [hn.continuousAt (Iio_mem_nhds hxn)] with y hy
    have he : torusEuclideanDist (torusQuotient y) ξ = ‖y + a‖ := by
      rw [torusEuclideanDist, ← hq y]
      exact torusEuclideanNorm_quotient_eq_of_norm_lt_half hy
    rw [he]
  · have hrt : ρ < torusEuclideanDist (torusQuotient x) ξ :=
      lt_of_lt_of_le hρ (le_of_not_gt hr)
    have hrn : ρ < ‖x + a‖ := by rw [hxw, hw]; exact hrt
    filter_upwards [ht.continuousAt (Ioi_mem_nhds hrt),
      hn.continuousAt (Ioi_mem_nhds hrn)] with y hyt hyn
    rw [hR _ hyt.le, hR _ hyn.le]

private theorem radial_lift_fderiv {R : ℝ → ℝ} {ρ : ℝ}
    (hR : ∀ r, ρ ≤ r → R r = 0) (hρ : ρ < 1 / 2) (ξ : Torus) (x : PlanarSpace) :
    fderiv ℝ (fun y : PlanarSpace ↦ R (torusEuclideanDist (torusQuotient y) ξ)) x =
      fderiv ℝ (fun y : PlanarSpace ↦ R ‖y‖) (centeredLift (torusQuotient x - ξ)) := by
  rw [(radial_lift_germ hR hρ ξ x).fderiv_eq,
    fderiv_comp_add_right (f := fun y : PlanarSpace ↦ R ‖y‖)]
  congr 1
  abel

private theorem radial_lift_second_fderiv {R : ℝ → ℝ} {ρ : ℝ}
    (hR : ∀ r, ρ ≤ r → R r = 0) (hρ : ρ < 1 / 2) (ξ : Torus) (x : PlanarSpace) :
    fderiv ℝ (fderiv ℝ (fun y : PlanarSpace ↦ R (torusEuclideanDist (torusQuotient y) ξ))) x =
      fderiv ℝ (fderiv ℝ (fun y : PlanarSpace ↦ R ‖y‖))
        (centeredLift (torusQuotient x - ξ)) := by
  let a : PlanarSpace := centeredLift (torusQuotient x - ξ) - x
  let F : PlanarSpace → ℝ := fun y ↦ R ‖y‖
  have ht : fderiv ℝ (fun y : PlanarSpace ↦ F (y + a)) =
      fun y ↦ fderiv ℝ F (y + a) := by
    funext y
    exact fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := y) a
  rw [(radial_lift_germ hR hρ ξ x).fderiv.fderiv_eq]
  change fderiv ℝ (fderiv ℝ (fun y : PlanarSpace ↦ F (y + a))) x = _
  rw [ht, fderiv_comp_add_right (f := fderiv ℝ F) a]
  congr 1
  dsimp [a]
  abel

private theorem radial_lift_laplacian {R : ℝ → ℝ} {ρ : ℝ}
    (hR : ∀ r, ρ ≤ r → R r = 0) (hρ : ρ < 1 / 2) (ξ : Torus) (x : PlanarSpace) :
    Δ (fun y : PlanarSpace ↦ R (torusEuclideanDist (torusQuotient y) ξ)) x =
      Δ (fun y : PlanarSpace ↦ R ‖y‖) (centeredLift (torusQuotient x - ξ)) := by
  let a : PlanarSpace := centeredLift (torusQuotient x - ξ) - x
  let F : PlanarSpace → ℝ := fun y ↦ R ‖y‖
  calc
    _ = Δ (fun y : PlanarSpace ↦ F (y + a)) x :=
      (laplacian_congr_nhds (radial_lift_germ hR hρ ξ x)).eq_of_nhds
    _ = Δ F (x + a) := congrFun (laplacian_comp_add_right F a) x
    _ = _ := congrArg (Δ F) (show x + a = centeredLift (torusQuotient x - ξ) by
      dsimp [a]
      abel)

/-- Actual ordinary derivatives at every lift, including points on chart seams. -/
theorem fderiv_phi_lift {s : ℝ} (hs : 0 < s) (hsize : s ≤ 1 / 64)
    (ξ : Torus) (x : PlanarSpace) :
    fderiv ℝ (fun y : PlanarSpace ↦ phi ξ s (torusQuotient y)) x =
      fderiv ℝ (phiEuclidean s) (centeredLift (torusQuotient x - ξ)) :=
  radial_lift_fderiv (fun _ hr ↦ phiProfile_eq_zero hs hr) (by linarith) ξ x

theorem second_fderiv_phi_lift {s : ℝ} (hs : 0 < s) (hsize : s ≤ 1 / 64)
    (ξ : Torus) (x : PlanarSpace) :
    fderiv ℝ (fderiv ℝ (fun y : PlanarSpace ↦ phi ξ s (torusQuotient y))) x =
      fderiv ℝ (fderiv ℝ (phiEuclidean s)) (centeredLift (torusQuotient x - ξ)) :=
  radial_lift_second_fderiv (fun _ hr ↦ phiProfile_eq_zero hs hr) (by linarith) ξ x

theorem laplacian_phi_lift {s : ℝ} (hs : 0 < s) (hsize : s ≤ 1 / 64)
    (ξ : Torus) (x : PlanarSpace) :
    Δ (fun y : PlanarSpace ↦ phi ξ s (torusQuotient y)) x =
      Δ (phiEuclidean s) (centeredLift (torusQuotient x - ξ)) :=
  radial_lift_laplacian (fun _ hr ↦ phiProfile_eq_zero hs hr) (by linarith) ξ x

theorem fderiv_omega_lift {s K : ℝ} (hs : 0 < s) (hK : 0 < K)
    (hsize : 2 * K * s ≤ 1 / 4) (ξ : Torus) (x : PlanarSpace) :
    fderiv ℝ (fun y : PlanarSpace ↦ omega ξ s K (torusQuotient y)) x =
      fderiv ℝ (omegaEuclidean s K) (centeredLift (torusQuotient x - ξ)) :=
  radial_lift_fderiv (fun _ hr ↦ omegaProfile_eq_zero_outer hs hK hr) (by linarith) ξ x

theorem norm_fderiv_phi_lift_le {s : ℝ} (hs : 0 < s) (hsize : s ≤ 1 / 64)
    (ξ : Torus) (x : PlanarSpace) :
    ‖fderiv ℝ (fun y : PlanarSpace ↦ phi ξ s (torusQuotient y)) x‖ ≤ 1 / s := by
  rw [fderiv_phi_lift hs hsize]
  exact norm_fderiv_phiEuclidean_le hs _

theorem norm_hessian_phi_lift_le {s : ℝ} (hs : 0 < s) (hsize : s ≤ 1 / 64)
    (ξ : Torus) (x : PlanarSpace) :
    ‖fderiv ℝ (fderiv ℝ (fun y : PlanarSpace ↦ phi ξ s (torusQuotient y))) x‖ ≤
      2 / s ^ 2 := by
  rw [second_fderiv_phi_lift hs hsize]
  exact norm_second_fderiv_phiEuclidean_le hs _

theorem abs_laplacian_phi_lift_le {s : ℝ} (hs : 0 < s) (hsize : s ≤ 1 / 64)
    (ξ : Torus) (x : PlanarSpace) :
    |Δ (fun y : PlanarSpace ↦ phi ξ s (torusQuotient y)) x| ≤ 3 / s ^ 2 := by
  rw [laplacian_phi_lift hs hsize]
  exact abs_laplacian_phiEuclidean_le hs _

theorem norm_fderiv_omega_lift_le {s K : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (hsize : 2 * K * s ≤ 1 / 4) (ξ : Torus) (x : PlanarSpace) :
    ‖fderiv ℝ (fun y : PlanarSpace ↦ omega ξ s K (torusQuotient y)) x‖ ≤ 2 / s := by
  rw [fderiv_omega_lift hs (by linarith) hsize]
  exact norm_fderiv_omegaEuclidean_le hs hK _

theorem norm_gradient_phi_le {s : ℝ} (hs : 0 < s) (hsize : s ≤ 1 / 64)
    (ξ z : Torus) : ‖torusOrdinaryGradient (phi ξ s) z‖ ≤ 1 / s := by
  rw [← torusQuotient_centeredLift z, norm_torusOrdinaryGradient_lift]
  exact norm_fderiv_phi_lift_le hs hsize ξ _

theorem norm_gradient_omega_le {s K : ℝ} (hs : 0 < s) (hK : 2 ≤ K)
    (hsize : 2 * K * s ≤ 1 / 4) (ξ z : Torus) :
    ‖torusOrdinaryGradient (omega ξ s K) z‖ ≤ 2 / s := by
  rw [← torusQuotient_centeredLift z, norm_torusOrdinaryGradient_lift]
  exact norm_fderiv_omega_lift_le hs hK hsize ξ _

theorem continuous_phi (ξ : Torus) (s : ℝ) : Continuous (phi ξ s) :=
  (contDiff_phiProfile s).continuous.comp
    (continuous_torusEuclideanNorm.comp (continuous_id.sub continuous_const))

theorem continuous_omega (ξ : Torus) (s K : ℝ) : Continuous (omega ξ s K) :=
  (contDiff_omegaProfile s K).continuous.comp
    (continuous_torusEuclideanNorm.comp (continuous_id.sub continuous_const))

theorem support_phi_subset {s : ℝ} (hs : 0 < s) (ξ : Torus) :
    Function.support (phi ξ s) ⊆ {z | torusEuclideanDist z ξ < 4 * s} := by
  intro z hz
  by_contra h
  exact hz (phi_eq_zero hs (le_of_not_gt h))

theorem support_omega_subset {s K : ℝ} (hs : 0 < s) (hK : 0 < K) (ξ : Torus) :
    Function.support (omega ξ s K) ⊆
      {z | s < torusEuclideanDist z ξ ∧ torusEuclideanDist z ξ < 2 * K * s} := by
  intro z hz
  constructor
  · by_contra h
    exact hz (omega_eq_zero_inner hs (le_of_not_gt h))
  · by_contra h
    exact hz (omega_eq_zero_outer hs hK (le_of_not_gt h))

/-- All four constants in `eq:virial-cutoff-bounds`, for the exact manuscript
parameters and the actual ordinary torus gradient and ordinary lift Hessian. -/
theorem virial_cutoff_bounds {s K : ℝ} (hs : 0 < s) (hsmall : s ≤ 1 / 64)
    (hK : 8 ≤ K) (houter : 2 * K * s ≤ 1 / 4) (ξ z : Torus) :
    ‖torusOrdinaryGradient (phi ξ s) z‖ ≤ 1 / s ∧
    ‖fderiv ℝ (fderiv ℝ (fun y : PlanarSpace ↦ phi ξ s (torusQuotient y)))
      (centeredLift z)‖ ≤ 2 / s ^ 2 ∧
    |Δ (fun y : PlanarSpace ↦ phi ξ s (torusQuotient y)) (centeredLift z)| ≤ 3 / s ^ 2 ∧
    ‖torusOrdinaryGradient (omega ξ s K) z‖ ≤ 2 / s :=
  ⟨norm_gradient_phi_le hs hsmall ξ z, norm_hessian_phi_lift_le hs hsmall ξ _,
    abs_laplacian_phi_lift_le hs hsmall ξ _,
    norm_gradient_omega_le hs (by linarith) houter ξ z⟩

end PeriodicAttractiveLogGas.LocalizedVirialCutoffs
