import DGPS.Circle.BesselMoments
/-!
# Strict Bessel ratio inequalities (EX003)

With `g = I₁/I₀` (`besselRatio`), the theorem `DGPS.Examples.strict_bessel_ratio_inequalities`
shows for `t > 0`: `0 < g'(t) < g(t)/t < 1/2`, `I₀(t) < exp(t²/4)`, `g(t)/t` is strictly decreasing,
`0 < g(t) < 1`, and `g(t)/t → 0` as `t → ∞`.

The monotonicity of `g/t = B/A` (`A = I₀`, `B = I₁/t`, both power series in `u = t²/4` with
coefficient ratio `1/(2(j+1))`) is obtained from the cross inequality
`B(s) A(t) - B(t) A(s) = ½ ∑_{i,j} a_i a_j (c_i - c_j)(u^i v^j - u^j v^i) ≥ 0`
(pairing `(i,j)` with `(j,i)`), which also yields the strict derivative bound.
-/

open MeasureTheory Real Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Circle.BesselMonotonicity

theorem pow_cross_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) {i j : ℕ} (hij : i ≤ j) :
    u ^ j * v ^ i ≤ u ^ i * v ^ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  have hv : 0 ≤ v := hu.trans huv
  have hk : u ^ k ≤ v ^ k := pow_le_pow_left₀ hu huv k
  have h0 : 0 ≤ u ^ i * v ^ i := by positivity
  calc u ^ (i + k) * v ^ i = (u ^ i * v ^ i) * u ^ k := by ring
    _ ≤ (u ^ i * v ^ i) * v ^ k := mul_le_mul_of_nonneg_left hk h0
    _ = u ^ i * v ^ (i + k) := by ring

/-- the cross inequality for two power series with monotone coefficient ratio -/
theorem cross_sum_lower (a c : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hc : ∀ i j, i ≤ j → c j ≤ c i)
    {u v Au Av Bu Bv : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hAu : HasSum (fun j => a j * u ^ j) Au) (hAv : HasSum (fun j => a j * v ^ j) Av)
    (hBu : HasSum (fun j => a j * c j * u ^ j) Bu) (hBv : HasSum (fun j => a j * c j * v ^ j) Bv) :
    a 0 * a 1 * (c 0 - c 1) * (v - u) ≤ Bu * Av - Au * Bv := by
  have hv : 0 ≤ v := hu.trans huv
  have nAu : Summable fun j => ‖a j * u ^ j‖ := hAu.summable.norm
  have nAv : Summable fun j => ‖a j * v ^ j‖ := hAv.summable.norm
  have nBu : Summable fun j => ‖a j * c j * u ^ j‖ := hBu.summable.norm
  have nBv : Summable fun j => ‖a j * c j * v ^ j‖ := hBv.summable.norm
  have S1 := summable_mul_of_summable_norm (f := fun j => a j * c j * u ^ j)
    (g := fun j => a j * v ^ j) nBu nAv
  have P1 := HasSum.mul (f := fun j => a j * c j * u ^ j) (g := fun j => a j * v ^ j) hBu hAv S1
  have S2 := summable_mul_of_summable_norm (f := fun j => a j * u ^ j)
    (g := fun j => a j * c j * v ^ j) nAu nBv
  have P2 := HasSum.mul (f := fun j => a j * u ^ j) (g := fun j => a j * c j * v ^ j) hAu hBv S2
  have D := P1.sub P2
  obtain ⟨G, hG⟩ : ∃ G : ℕ × ℕ → ℝ, G = fun p => a p.1 * c p.1 * u ^ p.1 * (a p.2 * v ^ p.2)
      - a p.1 * u ^ p.1 * (a p.2 * c p.2 * v ^ p.2) := ⟨_, rfl⟩
  have D' : HasSum G (Bu * Av - Au * Bv) := by rw [hG]; exact D
  have Dsw : HasSum (fun p : ℕ × ℕ => G p.swap) (Bu * Av - Au * Bv) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr D'
  have DK := D'.add Dsw
  have hK : ∀ p : ℕ × ℕ, 0 ≤ G p + G p.swap := by
    rintro ⟨i, j⟩
    have e : G (i, j) + G (j, i) =
        a i * a j * ((c i - c j) * (u ^ i * v ^ j - u ^ j * v ^ i)) := by
      rw [hG]; simp only; ring
    show 0 ≤ G (i, j) + G (j, i)
    rw [e]
    have hai := ha i
    have haj := ha j
    refine mul_nonneg (mul_nonneg hai haj) ?_
    rcases le_total i j with h | h
    · exact mul_nonneg (sub_nonneg.mpr (hc i j h)) (sub_nonneg.mpr (pow_cross_le hu huv h))
    · have h1 : c i - c j ≤ 0 := sub_nonpos.mpr (hc j i h)
      have h2 : u ^ i * v ^ j - u ^ j * v ^ i ≤ 0 := sub_nonpos.mpr (pow_cross_le hu huv h)
      exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  have hfin := sum_le_hasSum ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) (fun p _ => hK p) DK
  have h01 : ((0 : ℕ), (1 : ℕ)) ≠ (1, 0) := by simp
  rw [Finset.sum_pair h01] at hfin
  have e01 : G (0, 1) + G (0, 1).swap = a 0 * a 1 * (c 0 - c 1) * (v - u) := by
    rw [hG]; simp only [Prod.swap]; ring
  have e10 : G (1, 0) + G (1, 0).swap = a 0 * a 1 * (c 0 - c 1) * (v - u) := by
    rw [hG]; simp only [Prod.swap]; ring
  rw [e01, e10] at hfin
  linarith

theorem hasSum_coefA (t : ℝ) :
    HasSum (fun j : ℕ => 1 / (j.factorial : ℝ) ^ 2 * (t ^ 2 / 4) ^ j) (besselI 0 t) := by
  convert hasSum_besselI_zero t using 1
  funext j
  ring

theorem hasSum_coefB (t : ℝ) :
    HasSum (fun j : ℕ => 1 / (j.factorial : ℝ) ^ 2 * (1 / (2 * ((j : ℝ) + 1))) * (t ^ 2 / 4) ^ j)
      (besselI1Over t) := by
  convert hasSum_besselI1Over t using 1
  funext j
  rw [Nat.factorial_succ]
  push_cast
  have : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem ratio_cross {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    (t ^ 2 - s ^ 2) / 16 ≤ besselI1Over s * besselI 0 t - besselI1Over t * besselI 0 s := by
  have h := cross_sum_lower (fun j : ℕ => 1 / (j.factorial : ℝ) ^ 2)
    (fun j : ℕ => 1 / (2 * ((j : ℝ) + 1))) (fun j => by positivity)
    (fun i j hij => by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      apply one_div_le_one_div_of_le (by positivity)
      linarith)
    (u := s ^ 2 / 4) (v := t ^ 2 / 4) (by positivity) (by nlinarith)
    (hasSum_coefA s) (hasSum_coefA t) (hasSum_coefB s) (hasSum_coefB t)
  norm_num [Nat.factorial] at h
  nlinarith [h]

theorem besselI1Over_pos (t : ℝ) : 0 < besselI1Over t := by
  have h := sum_le_hasSum (Finset.range 1) (fun j _ => by positivity) (hasSum_besselI1Over t)
  simp at h
  linarith

/-- `B/A` equals `g/t` for `t ≠ 0` -/
theorem ratio_eq (t : ℝ) (ht : t ≠ 0) :
    besselRatio t / t = besselI1Over t / besselI 0 t := by
  rw [besselI1Over_of_ne t ht]
  unfold besselRatio
  field_simp

theorem strictAntiOn_ratio : StrictAntiOn (fun t => besselRatio t / t) (Set.Ioi 0) := by
  intro s hs t ht hst
  have hs' : (0 : ℝ) < s := hs
  have ht' : (0 : ℝ) < t := ht
  simp only
  rw [ratio_eq s hs'.ne', ratio_eq t ht'.ne']
  have hAs := besselI_zero_pos s
  have hAt := besselI_zero_pos t
  have hc := ratio_cross hs'.le hst
  rw [div_lt_div_iff₀ hAt hAs]
  have : 0 < t ^ 2 - s ^ 2 := by nlinarith
  nlinarith

theorem ratio_lt_half (t : ℝ) (ht : 0 < t) : besselRatio t / t < 1 / 2 := by
  rw [ratio_eq t ht.ne']
  have hA := besselI_zero_pos t
  rw [div_lt_iff₀ hA]
  have hA' := hasSum_coefA t
  have hB' := hasSum_coefB t
  have hlt : besselI1Over t < besselI 0 t / 2 := by
    have hA2 := hA'.div_const 2
    refine hasSum_lt (f := fun j : ℕ => 1 / (j.factorial : ℝ) ^ 2 * (1 / (2 * ((j : ℝ) + 1))) *
      (t ^ 2 / 4) ^ j) (g := fun j : ℕ => 1 / (j.factorial : ℝ) ^ 2 * (t ^ 2 / 4) ^ j / 2)
      (i := 1) (fun j => ?_) ?_ hB' hA2
    · have : (1 : ℝ) / (2 * ((j : ℝ) + 1)) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      have h0 : 0 ≤ 1 / (j.factorial : ℝ) ^ 2 * (t ^ 2 / 4) ^ j := by positivity
      calc 1 / (j.factorial : ℝ) ^ 2 * (1 / (2 * ((j : ℝ) + 1))) * (t ^ 2 / 4) ^ j
          = (1 / (j.factorial : ℝ) ^ 2 * (t ^ 2 / 4) ^ j) * (1 / (2 * ((j : ℝ) + 1))) := by ring
        _ ≤ (1 / (j.factorial : ℝ) ^ 2 * (t ^ 2 / 4) ^ j) * (1 / 2) :=
            mul_le_mul_of_nonneg_left this h0
        _ = _ := by ring
    · have : 0 < t ^ 2 := by positivity
      norm_num [Nat.factorial]
      nlinarith
  linarith

theorem besselI_zero_lt_exp (t : ℝ) (ht : 0 < t) : besselI 0 t < Real.exp (t ^ 2 / 4) := by
  have h1 := hasSum_besselI_zero t
  have h2 := hasSum_exp_series (t ^ 2 / 4)
  refine hasSum_lt (i := 2) (fun j => ?_) ?_ h1 h2
  · have hf : (1 : ℝ) ≤ j.factorial := by exact_mod_cast Nat.factorial_pos j
    have hu : 0 ≤ (t ^ 2 / 4) ^ j := by positivity
    have hf0 : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    have hsq : (j.factorial : ℝ) ≤ (j.factorial : ℝ) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_left hu hf0 hsq
  · norm_num [Nat.factorial]
    have : 0 < (t ^ 2 / 4) ^ 2 := by positivity
    nlinarith

theorem besselRatio_pos (t : ℝ) (ht : 0 < t) : 0 < besselRatio t := by
  have h : besselRatio t = t * (besselRatio t / t) := by field_simp
  rw [h, ratio_eq t ht.ne']
  have := besselI1Over_pos t
  have := besselI_zero_pos t
  positivity

theorem besselI_one_lt (t : ℝ) : besselI 1 t < besselI 0 t := by
  have hc : Continuous angCos := continuous_angMode 1
  have hcb : ∀ θ, |angCos θ| ≤ 1 := abs_angMode_le 1
  have i0 := integrable_cexp t (fun _ => 1) continuous_const (fun _ => by simp)
  have i1 := integrable_cexp t angCos hc hcb
  have hnn : 0 ≤ᵐ[angHaar] fun θ => Real.exp (t * angCos θ) * (1 - angCos θ) :=
    Filter.Eventually.of_forall fun θ => by
      have := (abs_le.mp (hcb θ)).2
      have h := Real.exp_pos (t * angCos θ)
      show 0 ≤ Real.exp (t * angCos θ) * (1 - angCos θ)
      exact mul_nonneg h.le (by linarith)
  have hint : Integrable (fun θ => Real.exp (t * angCos θ) * (1 - angCos θ)) angHaar := by
    have := i0.sub i1
    refine this.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only [Pi.sub_apply]; ring
  have hpos : 0 < ∫ θ, Real.exp (t * angCos θ) * (1 - angCos θ) ∂angHaar := by
    rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
    have hU : IsOpen {θ : AngCircle | angCos θ ≠ 1} := isOpen_ne_fun hc continuous_const
    have hne : {θ : AngCircle | angCos θ ≠ 1}.Nonempty := by
      refine ⟨((π : ℝ) : AngCircle), ?_⟩
      have := angMode_coe 1 π
      show angCos ((π : ℝ) : AngCircle) ≠ 1
      have h1 : angCos ((π : ℝ) : AngCircle) = -1 := by simpa using this
      rw [h1]; norm_num
    refine lt_of_lt_of_le (hU.measure_pos angHaar hne) (measure_mono ?_)
    intro θ hθ
    simp only [Function.mem_support]
    have : 1 - angCos θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
    have h := Real.exp_pos (t * angCos θ)
    positivity
  have e0 : ∫ θ, Real.exp (t * angCos θ) * 1 ∂angHaar = besselI 0 t := by
    rw [besselI_zero]; simp
  have e1 : ∫ θ, Real.exp (t * angCos θ) * angCos θ ∂angHaar = besselI 1 t := by
    rw [besselI_one]; simp
  have hsplit : ∫ θ, Real.exp (t * angCos θ) * (1 - angCos θ) ∂angHaar
      = besselI 0 t - besselI 1 t := by
    rw [← e0, ← e1, ← integral_sub i0 i1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only; ring
  linarith

theorem besselRatio_lt_one (t : ℝ) : besselRatio t < 1 := by
  unfold besselRatio
  rw [div_lt_one (besselI_zero_pos t)]
  exact besselI_one_lt t

theorem tendsto_ratio : Tendsto (fun t => besselRatio t / t) atTop (𝓝 0) := by
  have hup : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    exact (div_pos (besselRatio_pos t ht) ht).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [div_eq_mul_inv]
    have := besselRatio_lt_one t
    have : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht
    nlinarith

/-- strict derivative bound `g'(t) < g(t)/t` -/
theorem besselVariance_lt (s : ℝ) (hs : 0 < s) : besselVariance s < besselRatio s / s := by
  have hg : HasDerivAt besselRatio (besselVariance s) s :=
    (besselVariance_eq s) ▸ hasDerivAt_besselRatio s
  have hh : HasDerivAt (fun t => besselRatio t / t)
      ((besselVariance s * s - besselRatio s * 1) / s ^ 2) s :=
    hg.div (hasDerivAt_id s) hs.ne'
  set h' := (besselVariance s * s - besselRatio s * 1) / s ^ 2 with hh'
  have hA : ContinuousAt (besselI 0) s := (hasDerivAt_besselI_zero s).continuousAt
  have hAs := besselI_zero_pos s
  -- slope bound
  have hslope : Tendsto (fun t => (t - s)⁻¹ • ((fun t => besselRatio t / t) t
      - (fun t => besselRatio t / t) s)) (𝓝[>] s) (𝓝 h') :=
    (hasDerivAt_iff_tendsto_slope.mp hh).mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))
  have hrhs : Tendsto (fun t => -((t + s) / (16 * besselI 0 s * besselI 0 t))) (𝓝[>] s)
      (𝓝 (-((s + s) / (16 * besselI 0 s * besselI 0 s)))) := by
    refine Tendsto.neg (Tendsto.div (tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_id.add continuous_const).tendsto s)) ?_ ?_)
    · exact tendsto_nhdsWithin_of_tendsto_nhds
        ((tendsto_const_nhds.mul hA.tendsto : Tendsto _ (𝓝 s) _))
    · positivity
  have hle : h' ≤ -((s + s) / (16 * besselI 0 s * besselI 0 s)) := by
    refine le_of_tendsto_of_tendsto hslope hrhs ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hts : s < t := ht
    have ht0 : 0 < t := hs.trans hts
    have hAt := besselI_zero_pos t
    have hc := ratio_cross hs.le hts
    simp only [smul_eq_mul]
    rw [ratio_eq s hs.ne', ratio_eq t ht0.ne']
    have hpos : 0 < 16 * besselI 0 s * besselI 0 t := by positivity
    have key : besselI1Over t / besselI 0 t - besselI1Over s / besselI 0 s
        ≤ -((t ^ 2 - s ^ 2) / 16 / (besselI 0 s * besselI 0 t)) := by
      have e : besselI1Over t / besselI 0 t - besselI1Over s / besselI 0 s
          = -((besselI1Over s * besselI 0 t - besselI1Over t * besselI 0 s)
              / (besselI 0 s * besselI 0 t)) := by
        field_simp
        ring
      rw [e, neg_le_neg_iff]
      exact div_le_div_of_nonneg_right hc (by positivity)
    have hts' : 0 < t - s := sub_pos.mpr hts
    have e2 : (t - s)⁻¹ * (besselI1Over t / besselI 0 t - besselI1Over s / besselI 0 s)
        ≤ (t - s)⁻¹ * (-((t ^ 2 - s ^ 2) / 16 / (besselI 0 s * besselI 0 t))) :=
      mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hts'.le)
    refine e2.trans (le_of_eq ?_)
    field_simp
    ring
  have hneg : -((s + s) / (16 * besselI 0 s * besselI 0 s)) < 0 := by
    have : 0 < (s + s) / (16 * besselI 0 s * besselI 0 s) := by positivity
    linarith
  have hh0 : h' < 0 := lt_of_le_of_lt hle hneg
  have : besselVariance s * s - besselRatio s * 1 < 0 := by
    by_contra hcon
    have : 0 ≤ h' := div_nonneg (not_lt.mp hcon) (by positivity)
    linarith
  rw [lt_div_iff₀ hs]
  linarith

end DGPS.Circle.BesselMonotonicity

namespace DGPS.Examples

open DGPS.Circle.BesselMoments DGPS.Circle.BesselMonotonicity

/-- EX003: strict Bessel ratio inequalities.  For `t > 0`: `0 < g'(t) < g(t)/t < 1/2` and
`I₀(t) < exp(t²/4)`; `t ↦ g(t)/t` is strictly decreasing on `(0, ∞)`; `0 < g(t) < 1`; and
`g(t)/t → 0` as `t → ∞`.  Here `g = I₁/I₀` is `besselRatio`. -/
theorem strict_bessel_ratio_inequalities :
    (∀ t : ℝ, 0 < t →
      0 < deriv besselRatio t ∧ deriv besselRatio t < besselRatio t / t ∧
        besselRatio t / t < 1 / 2) ∧
    (∀ t : ℝ, 0 < t → besselI 0 t < Real.exp (t ^ 2 / 4)) ∧
    StrictAntiOn (fun t : ℝ => besselRatio t / t) (Set.Ioi 0) ∧
    (∀ t : ℝ, 0 < t → 0 < besselRatio t ∧ besselRatio t < 1) ∧
    Filter.Tendsto (fun t : ℝ => besselRatio t / t) Filter.atTop (nhds 0) := by
  refine ⟨fun t ht => ?_, besselI_zero_lt_exp, strictAntiOn_ratio,
    fun t ht => ⟨besselRatio_pos t ht, besselRatio_lt_one t⟩, tendsto_ratio⟩
  have hg : HasDerivAt besselRatio (besselVariance t) t :=
    (besselVariance_eq t) ▸ hasDerivAt_besselRatio t
  rw [hg.deriv]
  exact ⟨besselVariance_pos t, besselVariance_lt t ht, ratio_lt_half t ht⟩

end DGPS.Examples
