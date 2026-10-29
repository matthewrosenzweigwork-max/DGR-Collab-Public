import SharpSymmetricLSI.Infra.HeatCircle
import SharpSymmetricLSI.Paper.CircleSobolev
import SharpSymmetricLSI.Paper.FourierPoincare
import SharpSymmetricLSI.Infra.Pinsker

/-!
# Lemma 3.2: the quantitative circle inequality via the heat flow (Phase 3, lane C; R10 (b)–(e))

For a probability density `ρ` on `ℝ/ℤ` and `p_t = e^{t∂²}ρ` (`t > 0`):
* (b) `H(t) = ∫ klFun(p_t)` and `I(t) = ∫ (p_t')²/p_t` satisfy `H' = -I` and
  `I' ≤ -2aI - I²/6` (`hasDerivAt_entropyH`, `hasDerivAt_fisherI`, `fisherI_deriv_le`).
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI

/-! ### Calculus helpers -/

theorem hasDerivAt_klFun {x : ℝ} (hx : 0 < x) : HasDerivAt klFun (Real.log x) x := by
  have := ((Real.hasDerivAt_mul_log hx.ne').add_const 1).sub (hasDerivAt_id x)
  convert this using 1
  · funext s; simp [klFun_apply]
  · simp

/-- The integral of the derivative of a `1`-periodic function over a period vanishes. -/
theorem integral_deriv_periodic {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (hc : Continuous F') (hp : F 1 = F 0) : ∫ x in (0 : ℝ)..1, F' x = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hc.intervalIntegrable _ _),
    hp, sub_self]

/-! ### Wirtinger and Cauchy–Schwarz on one period -/

theorem periodic_int {w : ℝ → ℝ} (hper : ∀ x, w (x + 1) = w x) (n : ℤ) (x : ℝ) :
    w (x + n) = w x := by
  have hp : Function.Periodic w 1 := hper
  simpa using (hp.int_mul n) x

theorem exists_bound_periodic {w : ℝ → ℝ} (hc : Continuous w) :
    ∃ C, ∀ y : Torus 1, |w (secT y 0)| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨C, fun y => ?_⟩
  have := (AddCircle.measurableEquivIoc 1 0 (y 0)).2
  have h2 : ((AddCircle.measurableEquivIoc 1 0 (y 0) : ℝ)) ≤ 1 := by simpa using this.2
  have := hC (secT y 0) ⟨this.1.le, h2⟩
  rwa [Real.norm_eq_abs] at this

/-- Wirtinger: `4π² ∫₀¹ w² ≤ ∫₀¹ w'²` for `C¹` `1`-periodic `w` with mean zero. -/
theorem wirtinger {w w' : ℝ → ℝ} (hw : ∀ x, HasDerivAt w (w' x) x) (hw' : Continuous w')
    (hper : ∀ x, w (x + 1) = w x) (hmean : ∫ x in (0 : ℝ)..1, w x = 0) :
    4 * π ^ 2 * ∫ x in (0 : ℝ)..1, w x ^ 2 ≤ ∫ x in (0 : ℝ)..1, w' x ^ 2 := by
  have hwc : Continuous w := continuous_iff_continuousAt.mpr fun x => (hw x).continuousAt
  set f : Torus 1 → ℝ := fun y => w (secT y 0) with hf
  have hfl : f ∘ liftT = fun z : Fin 1 → ℝ => w (z 0) := by
    funext z
    obtain ⟨m, hm⟩ := secT_liftT_eq z
    simp only [Function.comp_apply, hf, hm, Pi.add_apply, intVec]
    exact periodic_int hper (m 0) (z 0)
  have hfd : ∀ z : Fin 1 → ℝ, HasFDerivAt (fun z : Fin 1 → ℝ => w (z 0))
      ((w' (z 0)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) z := fun z =>
    (hw (z 0)).comp_hasFDerivAt z (hasFDerivAt_apply 0 z)
  have hcd : ContDiff ℝ 1 (fun z : Fin 1 → ℝ => w (z 0)) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun z => (hfd z).differentiableAt, ?_⟩
    have : fderiv ℝ (fun z : Fin 1 → ℝ => w (z 0)) =
        fun z => (w' (z 0)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0 :=
      funext fun z => (hfd z).fderiv
    rw [this]
    exact (hw'.comp (continuous_apply 0)).smul continuous_const
  have hfc : ContDiff ℝ 1 (f ∘ liftT) := by rw [hfl]; exact hcd
  have hwg := isWeakGrad_of_contDiff hfc
  have hgy : ∀ y : Torus 1, ∀ k : Fin 1,
      fderiv ℝ (f ∘ liftT) (secT y) (Pi.single k 1) = w' (secT y 0) := by
    intro y k
    rw [Subsingleton.elim k 0, hfl, (hfd (secT y)).fderiv]
    simp
  obtain ⟨C, hC⟩ := exists_bound_periodic hwc
  obtain ⟨C', hC'⟩ := exists_bound_periodic hw'
  have hfm : MemLp f 2 volume :=
    MemLp.of_bound (hwc.comp_aestronglyMeasurable
      ((continuous_apply 0).comp_aestronglyMeasurable measurable_secT.aestronglyMeasurable)) C
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)
  have hgm : ∀ j, MemLp (fun y => fderiv ℝ (f ∘ liftT) (secT y) (Pi.single j 1)) 2 volume := by
    intro j
    simp_rw [hgy]
    exact MemLp.of_bound (hw'.comp_aestronglyMeasurable
      ((continuous_apply 0).comp_aestronglyMeasurable measurable_secT.aestronglyMeasurable)) C'
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC' y)
  have hP := poincare_torus hwg hfm hgm
  simp_rw [hgy] at hP
  rw [Fintype.sum_unique, ProbabilityTheory.variance_eq_sub hfm] at hP
  have h1 : ∫ y : Torus 1, (f ^ 2) y = ∫ x in (0 : ℝ)..1, w x ^ 2 := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_torus1_secT]; rfl
  have h2 : ∫ y : Torus 1, f y = 0 := by
    rw [hf, integral_torus1_secT (fun s => w s), ← intervalIntegral.integral_of_le zero_le_one,
      hmean]
  have h3 : ∫ y : Torus 1, w' (secT y 0) ^ 2 = ∫ x in (0 : ℝ)..1, w' x ^ 2 := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_torus1_secT (fun s => w' s ^ 2)]
  rw [h1, h2, h3] at hP
  simpa using hP

/-- `(∫ A)² ≤ (∫ A²/B)(∫ B)` for `A ≥ 0`, `B > 0` continuous. -/
theorem sq_integral_le {A B : ℝ → ℝ} (hA : Continuous A) (hB : Continuous B)
    (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ x, 0 < B x) :
    (∫ x in (0 : ℝ)..1, A x) ^ 2 ≤
      (∫ x in (0 : ℝ)..1, A x ^ 2 / B x) * ∫ x in (0 : ℝ)..1, B x := by
  set X := ∫ x in (0 : ℝ)..1, A x ^ 2 / B x
  set Y := ∫ x in (0 : ℝ)..1, B x
  set Z := ∫ x in (0 : ℝ)..1, A x
  have hZ0 : 0 ≤ Z := intervalIntegral.integral_nonneg zero_le_one fun x _ => hA0 x
  have hX0 : 0 ≤ X := intervalIntegral.integral_nonneg zero_le_one fun x _ =>
    div_nonneg (sq_nonneg _) (hB0 x).le
  have hc1 : Continuous fun x => A x ^ 2 / B x := (hA.pow 2).div hB fun x => (hB0 x).ne'
  have key : ∀ l : ℝ, 0 < l → Z ≤ l / 2 * X + 1 / (2 * l) * Y := by
    intro l hl
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add ((hc1.const_mul _).intervalIntegrable _ _)
        ((hB.const_mul _).intervalIntegrable _ _)]
    refine intervalIntegral.integral_mono_on zero_le_one (hA.intervalIntegrable _ _)
      (((hc1.const_mul _).add (hB.const_mul _)).intervalIntegrable _ _) fun x _ => ?_
    have hb := hB0 x
    have : l / 2 * (A x ^ 2 / B x) + 1 / (2 * l) * B x - A x =
        (l * A x - B x) ^ 2 / (2 * l * B x) := by field_simp; ring
    have : 0 ≤ (l * A x - B x) ^ 2 / (2 * l * B x) := by positivity
    linarith
  rcases hX0.eq_or_lt with hX | hX
  · have hZ : Z ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hY0 : 0 ≤ Y := intervalIntegral.integral_nonneg zero_le_one fun x _ => (hB0 x).le
      have := key (Y / (2 * ε) + 1) (by positivity)
      rw [← hX, mul_zero, zero_add] at this
      refine this.trans ?_
      rw [zero_add, show 1 / (2 * (Y / (2 * ε) + 1)) * Y = Y * ε / (Y + 2 * ε) by
        field_simp, div_le_iff₀ (by positivity)]
      nlinarith
    have : Z = 0 := le_antisymm hZ hZ0
    rw [this, sq, zero_mul]
    exact mul_nonneg hX0 (intervalIntegral.integral_nonneg zero_le_one fun x _ => (hB0 x).le)
  · rcases hZ0.eq_or_lt with hZ | hZ
    · have hY0 : 0 ≤ Y := intervalIntegral.integral_nonneg zero_le_one fun x _ => (hB0 x).le
      rw [← hZ]; nlinarith
    · have h := key (Z / X) (by positivity)
      have : Z / X / 2 * X = Z / 2 := by field_simp
      rw [this] at h
      have h2 : 1 / (2 * (Z / X)) * Y = X * Y / (2 * Z) := by field_simp
      rw [h2] at h
      have h3 : Z / 2 ≤ X * Y / (2 * Z) := by linarith
      rw [le_div_iff₀ (by positivity)] at h3
      nlinarith

/-! ### The heat flow of a probability density -/

section Flow

variable {ρ : ℝ → ℝ}

/-- Uniform bound for `|∂ₓʲ p_s|`, `s ≥ t/2`. -/
noncomputable def heatB (ρ : ℝ → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ∑' n, heatBound (∫ y in (0 : ℝ)..1, |ρ y|) j (t / 2) n

theorem abs_heatD_le_heatB (ρ : ℝ → ℝ) (j : ℕ) {t s : ℝ} (ht : 0 < t) (hs : t / 2 ≤ s) (x : ℝ) :
    |heatD ρ j s x| ≤ heatB ρ j t :=
  abs_heatD_le ρ j (by positivity) hs x

theorem heat_lower_one (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) :
    ∃ m > 0, ∀ s ∈ Icc (t / 2) (2 * t), ∀ x, m ≤ heat ρ s x := by
  obtain ⟨m, hm, h⟩ := heat_lower (t₁ := t / 2) (t₂ := 2 * t) hρ hρ0 (by positivity)
    (by linarith)
  exact ⟨m, hm, fun s hs x => by simpa [hρ1] using h s hs x⟩

theorem heat_pos (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heat ρ t x := by
  obtain ⟨m, hm, h⟩ := heat_lower_one hρ hρ0 hρ1 ht
  exact lt_of_lt_of_le hm (h t ⟨by linarith, by linarith⟩ x)

/-- The entropy `H(t) = ∫ klFun(p_t)`. -/
noncomputable def entropyH (ρ : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, klFun (heat ρ t x)

/-- The Fisher information `I(t) = ∫ (p_t')²/p_t`. -/
noncomputable def fisherI (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, heatD ρ 1 t x ^ 2 / heat ρ t x

theorem nhds_Ioo_half {t : ℝ} (ht : 0 < t) : Ioo (t / 2) (2 * t) ∈ 𝓝 t :=
  Ioo_mem_nhds (by linarith) (by linarith)

theorem abs_log_le {m M y : ℝ} (hm : 0 < m) (hy : m ≤ y) (hyM : y ≤ M) :
    |Real.log y| ≤ |Real.log m| + |Real.log M| := by
  have h1 : Real.log m ≤ Real.log y := Real.log_le_log hm hy
  have h2 : Real.log y ≤ Real.log M := Real.log_le_log (lt_of_lt_of_le hm hy) hyM
  rw [abs_le]; constructor
  · linarith [neg_abs_le (Real.log m), abs_nonneg (Real.log M)]
  · linarith [le_abs_self (Real.log M), abs_nonneg (Real.log m)]

/-- `H'(t) = ∫ log(p_t) p_t''`. -/
theorem hasDerivAt_entropyH_aux (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (entropyH ρ) (∫ x in (0 : ℝ)..1, Real.log (heat ρ t x) * heatD ρ 2 t x) t := by
  obtain ⟨m, hm, hml⟩ := heat_lower_one hρ hρ0 hρ1 ht
  have hpos : ∀ s, 0 < s → ∀ x, 0 < heat ρ s x := fun s hs x => heat_pos hρ hρ0 hρ1 hs x
  set M := heatB ρ 0 t
  have hb : ∀ s ∈ Ioo (t / 2) (2 * t), ∀ x,
      ‖Real.log (heat ρ s x) * heatD ρ 2 s x‖ ≤ (|Real.log m| + |Real.log M|) * heatB ρ 2 t := by
    intro s hs x
    have hs' : s ∈ Icc (t / 2) (2 * t) := ⟨hs.1.le, hs.2.le⟩
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (abs_log_le hm (hml s hs' x) ?_) (abs_heatD_le_heatB ρ 2 ht hs.1.le x)
      (abs_nonneg _) (by positivity)
    exact (le_abs_self _).trans (abs_heatD_le_heatB ρ 0 ht hs.1.le x)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 1) (F := fun s x => klFun (heat ρ s x))
    (F' := fun s x => Real.log (heat ρ s x) * heatD ρ 2 s x)
    (bound := fun _ => (|Real.log m| + |Real.log M|) * heatB ρ 2 t) (nhds_Ioo_half ht)
    (by filter_upwards [Ioi_mem_nhds ht] with s hs
        exact (continuous_klFun.comp (continuous_heatD ρ 0 hs)).aestronglyMeasurable)
    ((continuous_klFun.comp (continuous_heatD ρ 0 ht)).intervalIntegrable _ _)
    (((continuous_heatD ρ 0 ht).log fun x => (hpos t ht x).ne').mul
      (continuous_heatD ρ 2 ht)).aestronglyMeasurable
    (Eventually.of_forall fun x _ s hs => hb s hs x) intervalIntegrable_const
    (Eventually.of_forall fun x _ s hs => by
      have hs0 : 0 < s := by linarith [hs.1]
      exact (hasDerivAt_klFun (hpos s hs0 x)).comp s (hasDerivAt_heatD_t ρ 0 hs0 x))
  exact h.2

/-- `H' = -I`. -/
theorem hasDerivAt_entropyH (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (entropyH ρ) (-fisherI ρ t) t := by
  have h := hasDerivAt_entropyH_aux hρ hρ0 hρ1 ht
  have hpos : ∀ x, 0 < heat ρ t x := fun x => heat_pos hρ hρ0 hρ1 ht x
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := fun x => Real.log (heat ρ t x)) (u' := fun x => heatD ρ 1 t x / heat ρ t x)
    (v := fun x => heatD ρ 1 t x) (v' := fun x => heatD ρ 2 t x)
    (fun x _ => (hasDerivAt_heatD_x ρ 0 ht x).log (hpos x).ne')
    (fun x _ => hasDerivAt_heatD_x ρ 1 ht x)
    (((continuous_heatD ρ 1 ht).div (continuous_heatD ρ 0 ht) fun x =>
      (hpos x).ne').intervalIntegrable _ _)
    ((continuous_heatD ρ 2 ht).intervalIntegrable _ _)
  have hp1 : heat ρ t 1 = heat ρ t 0 := by simpa using heatD_add_one ρ 0 t 0
  have hq1 : heatD ρ 1 t 1 = heatD ρ 1 t 0 := by simpa using heatD_add_one ρ 1 t 0
  convert h using 1
  rw [hibp, hp1, hq1]
  unfold fisherI
  rw [sub_self, zero_sub]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  ring

/-- `I'(t) = ∫ (2 p₁ p₃ / p - p₁² p₂ / p²)` (`pⱼ = ∂ₓʲ p_t`). -/
theorem hasDerivAt_fisherI (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fisherI ρ) (∫ x in (0 : ℝ)..1, (2 * heatD ρ 1 t x * heatD ρ 3 t x / heat ρ t x -
      heatD ρ 1 t x ^ 2 * heatD ρ 2 t x / heat ρ t x ^ 2)) t := by
  obtain ⟨m, hm, hml⟩ := heat_lower_one hρ hρ0 hρ1 ht
  have hpos : ∀ s, 0 < s → ∀ x, 0 < heat ρ s x := fun s hs x => heat_pos hρ hρ0 hρ1 hs x
  set B1 := heatB ρ 1 t
  set B2 := heatB ρ 2 t
  set B3 := heatB ρ 3 t
  have hB : ∀ j, 0 ≤ heatB ρ j t := fun j =>
    le_trans (abs_nonneg _) (abs_heatD_le_heatB ρ j ht (by linarith : t / 2 ≤ t) 0)
  have hb : ∀ s ∈ Ioo (t / 2) (2 * t), ∀ x,
      ‖2 * heatD ρ 1 s x * heatD ρ 3 s x / heat ρ s x -
        heatD ρ 1 s x ^ 2 * heatD ρ 2 s x / heat ρ s x ^ 2‖ ≤
        2 * B1 * B3 / m + B1 ^ 2 * B2 / m ^ 2 := by
    intro s hs x
    have hs' : s ∈ Icc (t / 2) (2 * t) := ⟨hs.1.le, hs.2.le⟩
    have hp := hml s hs' x
    have h1 := abs_heatD_le_heatB ρ 1 ht hs.1.le x
    have h2 := abs_heatD_le_heatB ρ 2 ht hs.1.le x
    have h3 := abs_heatD_le_heatB ρ 3 ht hs.1.le x
    have hp0 : 0 < heat ρ s x := lt_of_lt_of_le hm hp
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_mul, abs_mul, abs_of_pos hp0, abs_two]
      calc 2 * |heatD ρ 1 s x| * |heatD ρ 3 s x| / heat ρ s x ≤ 2 * B1 * B3 / heat ρ s x := by
            gcongr
            exact mul_nonneg zero_le_two (hB 1)
        _ ≤ 2 * B1 * B3 / m := by
            gcongr; exact mul_nonneg (mul_nonneg zero_le_two (hB 1)) (hB 3)
    · rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos hp0]
      calc |heatD ρ 1 s x| ^ 2 * |heatD ρ 2 s x| / heat ρ s x ^ 2 ≤
            B1 ^ 2 * B2 / heat ρ s x ^ 2 := by gcongr
        _ ≤ B1 ^ 2 * B2 / m ^ 2 := by gcongr; exact mul_nonneg (sq_nonneg _) (hB 2)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 1) (F := fun s x => heatD ρ 1 s x ^ 2 / heat ρ s x)
    (F' := fun s x => 2 * heatD ρ 1 s x * heatD ρ 3 s x / heat ρ s x -
      heatD ρ 1 s x ^ 2 * heatD ρ 2 s x / heat ρ s x ^ 2)
    (bound := fun _ => 2 * B1 * B3 / m + B1 ^ 2 * B2 / m ^ 2) (nhds_Ioo_half ht)
    (by filter_upwards [Ioi_mem_nhds ht] with s hs
        exact (((continuous_heatD ρ 1 hs).pow 2).div (continuous_heatD ρ 0 hs) fun x =>
          (hpos s hs x).ne').aestronglyMeasurable)
    ((((continuous_heatD ρ 1 ht).pow 2).div (continuous_heatD ρ 0 ht) fun x =>
      (hpos t ht x).ne').intervalIntegrable _ _)
    (((((continuous_const.mul (continuous_heatD ρ 1 ht)).mul (continuous_heatD ρ 3 ht)).div
      (continuous_heatD ρ 0 ht) fun x => (hpos t ht x).ne').sub
      ((((continuous_heatD ρ 1 ht).pow 2).mul (continuous_heatD ρ 2 ht)).div
        ((continuous_heatD ρ 0 ht).pow 2) fun x =>
          pow_ne_zero 2 (hpos t ht x).ne')).aestronglyMeasurable)
    (Eventually.of_forall fun x _ s hs => hb s hs x) intervalIntegrable_const
    (Eventually.of_forall fun x _ s hs => by
      have hs0 : 0 < s := by linarith [hs.1]
      have := ((hasDerivAt_heatD_t ρ 1 hs0 x).pow 2).div (hasDerivAt_heatD_t ρ 0 hs0 x)
        (hpos s hs0 x).ne'
      convert this using 1
      have hp := (hpos s hs0 x).ne'
      simp only [Pi.pow_apply]
      field_simp
      push_cast
      ring)
  exact h.2

theorem integral_lin3 {f g h : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    (a b c : ℝ) : ∫ x in (0 : ℝ)..1, (a * f x + b * g x + c * h x) =
      a * (∫ x in (0 : ℝ)..1, f x) + b * (∫ x in (0 : ℝ)..1, g x) +
        c * ∫ x in (0 : ℝ)..1, h x := by
  rw [intervalIntegral.integral_add (f := fun x => a * f x + b * g x) (g := fun x => c * h x)
    (((hf.const_mul a).add (hg.const_mul b)).intervalIntegrable _ _)
    ((hh.const_mul c).intervalIntegrable _ _), intervalIntegral.integral_add
    (f := fun x => a * f x) (g := fun x => b * g x)
    ((hf.const_mul a).intervalIntegrable _ _) ((hg.const_mul b).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- `I' ≤ -2aI - I²/6`. -/
theorem fisherI_deriv_le (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) :
    ∫ x in (0 : ℝ)..1, (2 * heatD ρ 1 t x * heatD ρ 3 t x / heat ρ t x -
      heatD ρ 1 t x ^ 2 * heatD ρ 2 t x / heat ρ t x ^ 2) ≤
      -2 * (4 * π ^ 2) * fisherI ρ t - fisherI ρ t ^ 2 / 6 := by
  set P := fun x => heat ρ t x with hP
  set P1 := fun x => heatD ρ 1 t x with hP1
  set P2 := fun x => heatD ρ 2 t x with hP2
  set P3 := fun x => heatD ρ 3 t x with hP3
  have hpos : ∀ x, 0 < P x := fun x => heat_pos hρ hρ0 hρ1 ht x
  have hne : ∀ x, P x ≠ 0 := fun x => (hpos x).ne'
  have dP : ∀ x, HasDerivAt P (P1 x) x := fun x => hasDerivAt_heatD_x ρ 0 ht x
  have dP1 : ∀ x, HasDerivAt P1 (P2 x) x := fun x => hasDerivAt_heatD_x ρ 1 ht x
  have dP2 : ∀ x, HasDerivAt P2 (P3 x) x := fun x => hasDerivAt_heatD_x ρ 2 ht x
  have cP : Continuous P := continuous_heatD ρ 0 ht
  have cP1 : Continuous P1 := continuous_heatD ρ 1 ht
  have cP2 : Continuous P2 := continuous_heatD ρ 2 ht
  have cP3 : Continuous P3 := continuous_heatD ρ 3 ht
  have per : ∀ j, heatD ρ j t 1 = heatD ρ j t 0 := fun j => by
    simpa using heatD_add_one ρ j t 0
  have perH : heat ρ t 1 = heat ρ t 0 := per 0
  -- the integrals
  set A := ∫ x in (0 : ℝ)..1, P2 x ^ 2 / P x
  set Bq := ∫ x in (0 : ℝ)..1, P1 x ^ 2 * P2 x / P x ^ 2
  set Cq := ∫ x in (0 : ℝ)..1, P1 x ^ 4 / P x ^ 3
  set D := ∫ x in (0 : ℝ)..1, 2 * P1 x * P3 x / P x
  set I := fisherI ρ t with hI
  have cA : Continuous fun x => P2 x ^ 2 / P x := (cP2.pow 2).div cP hne
  have cB : Continuous fun x => P1 x ^ 2 * P2 x / P x ^ 2 :=
    ((cP1.pow 2).mul cP2).div (cP.pow 2) fun x => pow_ne_zero 2 (hne x)
  have cC : Continuous fun x => P1 x ^ 4 / P x ^ 3 :=
    (cP1.pow 4).div (cP.pow 3) fun x => pow_ne_zero 3 (hne x)
  have cD : Continuous fun x => 2 * P1 x * P3 x / P x :=
    ((continuous_const.mul cP1).mul cP3).div cP hne
  -- (i) `∫ (2P₁P₂/P)' = 0`
  have ibp1 : 2 * A + D - 2 * Bq = 0 := by
    have h := integral_deriv_periodic (F := fun x => 2 * P1 x * P2 x / P x)
      (F' := fun x => 2 * (P2 x ^ 2 / P x) + 1 * (2 * P1 x * P3 x / P x) +
        (-2) * (P1 x ^ 2 * P2 x / P x ^ 2))
      (fun x => by
        have := (((dP1 x).const_mul 2).mul (dP2 x)).div (dP x) (hne x)
        convert this using 1
        have := hne x
        simp only [Pi.mul_apply]
        field_simp
        ring)
      (((cA.const_mul 2).add (cD.const_mul 1)).add (cB.const_mul _))
      (by simp only [hP, hP1, hP2]; rw [perH, per 1, per 2])
    rw [integral_lin3 cA cD cB] at h
    simp only [one_mul] at h
    linarith
  -- (ii) `∫ (P₁³/P²)' = 0`
  have ibp2 : 3 * Bq - 2 * Cq = 0 := by
    have h := integral_deriv_periodic (F := fun x => P1 x ^ 3 / P x ^ 2)
      (F' := fun x => 3 * (P1 x ^ 2 * P2 x / P x ^ 2) + (-2) * (P1 x ^ 4 / P x ^ 3) +
        0 * (P1 x ^ 4 / P x ^ 3))
      (fun x => by
        have := ((dP1 x).pow 3).div ((dP x).pow 2) (pow_ne_zero 2 (hne x))
        convert this using 1
        have := hne x
        simp only [Pi.pow_apply]
        norm_num
        field_simp
        ring)
      (((cB.const_mul 3).add (cC.const_mul _)).add (cC.const_mul _))
      (by simp only [hP, hP1]; rw [perH, per 1])
    rw [integral_lin3 cB cC cC] at h
    linarith
  -- `w = (√P)'`
  set w := fun x => P1 x / (2 * Real.sqrt (P x)) with hw
  set w' := fun x => P2 x / (2 * Real.sqrt (P x)) - P1 x ^ 2 / (4 * P x * Real.sqrt (P x))
    with hw'
  have hsq : ∀ x, Real.sqrt (P x) ^ 2 = P x := fun x => Real.sq_sqrt (hpos x).le
  have hsqpos : ∀ x, 0 < Real.sqrt (P x) := fun x => Real.sqrt_pos.mpr (hpos x)
  have dw : ∀ x, HasDerivAt w (w' x) x := by
    intro x
    have hs := ((dP x).sqrt (hne x)).const_mul 2
    have := (dP1 x).div hs (by have := hsqpos x; positivity)
    convert this using 1
    have h1 := hsqpos x
    have h2 := hsq x
    have h3 := hne x
    simp only [hw']
    field_simp
    simp only [h2]
    field_simp
    ring
  have cw : Continuous w := cP1.div (continuous_const.mul (Real.continuous_sqrt.comp cP))
    fun x => by have := hsqpos x; positivity
  have cw' : Continuous w' := (cP2.div (continuous_const.mul (Real.continuous_sqrt.comp cP))
    fun x => (mul_pos two_pos (hsqpos x)).ne').sub ((cP1.pow 2).div
      ((continuous_const.mul cP).mul (Real.continuous_sqrt.comp cP)) fun x =>
        (mul_pos (mul_pos four_pos (hpos x)) (hsqpos x)).ne')
  have hmean : ∫ x in (0 : ℝ)..1, w x = 0 :=
    integral_deriv_periodic (F := fun x => Real.sqrt (P x)) (fun x => by
      have := (dP x).sqrt (hne x)
      convert this using 1) cw (by simp only [hP]; rw [perH])
  have hW := wirtinger dw cw' (fun x => by
    simp only [hw, hP, hP1]
    rw [heatD_add_one ρ 1 t x, show heat ρ t (x + 1) = heat ρ t x from heatD_add_one ρ 0 t x])
    hmean
  have hw2 : ∫ x in (0 : ℝ)..1, w x ^ 2 = I / 4 := by
    rw [hI, fisherI, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hw, hP, hP1]
    have := hsq x
    rw [div_pow, mul_pow, this]
    ring
  have hw'2 : ∫ x in (0 : ℝ)..1, w' x ^ 2 = A / 4 + (-1 / 4) * Bq + (1 / 16) * Cq := by
    have : ∫ x in (0 : ℝ)..1, w' x ^ 2 = ∫ x in (0 : ℝ)..1, ((1 / 4) * (P2 x ^ 2 / P x) +
        (-1 / 4) * (P1 x ^ 2 * P2 x / P x ^ 2) + (1 / 16) * (P1 x ^ 4 / P x ^ 3)) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hw']
      have h1 := hsqpos x
      have h2 := hsq x
      have h3 := hpos x
      field_simp
      simp only [h2]
      ring
    rw [this, integral_lin3 cA cB cC]
    ring
  -- Cauchy–Schwarz
  have hCS := sq_integral_le (A := fun x => P1 x ^ 2 / (4 * P x)) (B := P)
    ((cP1.pow 2).div (continuous_const.mul cP) fun x => (mul_pos four_pos (hpos x)).ne') cP
    (fun x => by have := hpos x; positivity) hpos
  have hmass : ∫ x in (0 : ℝ)..1, P x = 1 := by rw [hP, integral_heat ρ ht, hρ1]
  have h4 : ∫ x in (0 : ℝ)..1, P1 x ^ 2 / (4 * P x) = I / 4 := by
    rw [hI, fisherI, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hP, hP1]; ring
  have h5 : ∫ x in (0 : ℝ)..1, (P1 x ^ 2 / (4 * P x)) ^ 2 / P x = Cq / 16 := by
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun x _ => ?_
    have := hne x
    field_simp
    ring
  rw [h4, h5, hmass, mul_one] at hCS
  -- assemble
  have hI' : ∫ x in (0 : ℝ)..1, (2 * P1 x * P3 x / P x - P1 x ^ 2 * P2 x / P x ^ 2) = D - Bq :=
    intervalIntegral.integral_sub (cD.intervalIntegrable _ _) (cB.intervalIntegrable _ _)
  show ∫ x in (0 : ℝ)..1, (2 * P1 x * P3 x / P x - P1 x ^ 2 * P2 x / P x ^ 2) ≤ _
  rw [hI']
  have hpi : 0 ≤ 4 * π ^ 2 := by positivity
  rw [hw2, hw'2] at hW
  nlinarith

theorem fisherI_nonneg (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) : 0 ≤ fisherI ρ t :=
  intervalIntegral.integral_nonneg zero_le_one fun x _ =>
    div_nonneg (sq_nonneg _) (heat_pos hρ hρ0 hρ1 ht x).le

theorem klFun_le_sq {x : ℝ} (hx : 0 < x) : klFun x ≤ (x - 1) ^ 2 := by
  rw [klFun_apply]
  have := Real.log_le_sub_one_of_pos hx
  nlinarith [mul_le_mul_of_nonneg_left this hx.le]

/-- The Lyapunov functional `ψ(t) = H(t) - 6 log(1 + I(t)/(12a))`, `a = 4π²`. -/
noncomputable def psiH (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  entropyH ρ t - 6 * Real.log (1 + fisherI ρ t / (12 * (4 * π ^ 2)))

theorem psiH_monotoneOn (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) : MonotoneOn (psiH ρ) (Ioi 0) := by
  set a : ℝ := 4 * π ^ 2 with ha_def
  have ha : 0 < a := by positivity
  have hd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (psiH ρ)
      (-fisherI ρ t - 6 * ((∫ x in (0 : ℝ)..1, (2 * heatD ρ 1 t x * heatD ρ 3 t x / heat ρ t x -
        heatD ρ 1 t x ^ 2 * heatD ρ 2 t x / heat ρ t x ^ 2)) / (12 * a) /
          (1 + fisherI ρ t / (12 * a)))) t := by
    intro t ht
    have hI := fisherI_nonneg hρ hρ0 hρ1 ht
    have hpos : 1 + fisherI ρ t / (12 * a) ≠ 0 := by positivity
    exact (hasDerivAt_entropyH hρ hρ0 hρ1 ht).sub (HasDerivAt.const_mul 6
      ((((hasDerivAt_fisherI hρ hρ0 hρ1 ht).div_const (12 * a)).const_add 1).log hpos))
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0) (f' := fun t =>
      -fisherI ρ t - 6 * ((∫ x in (0 : ℝ)..1, (2 * heatD ρ 1 t x * heatD ρ 3 t x / heat ρ t x -
        heatD ρ 1 t x ^ 2 * heatD ρ 2 t x / heat ρ t x ^ 2)) / (12 * a) /
          (1 + fisherI ρ t / (12 * a))))
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Ioi] at ht
    exact (hd t ht).hasDerivWithinAt
  · rw [interior_Ioi] at ht
    have hI := fisherI_nonneg hρ hρ0 hρ1 ht
    have hJ := fisherI_deriv_le hρ hρ0 hρ1 ht
    set I := fisherI ρ t
    set J := ∫ x in (0 : ℝ)..1, (2 * heatD ρ 1 t x * heatD ρ 3 t x / heat ρ t x -
        heatD ρ 1 t x ^ 2 * heatD ρ 2 t x / heat ρ t x ^ 2)
    have hden : 0 < 12 * a + I := by positivity
    have heq : J / (12 * a) / (1 + I / (12 * a)) = J / (12 * a + I) := by
      field_simp
    rw [heq, mul_div_assoc', show -I - 6 * J / (12 * a + I) = (-6 * J - I * (12 * a + I)) /
      (12 * a + I) by field_simp; ring]
    apply div_nonneg _ hden.le
    nlinarith

theorem entropyH_le_sq_decay (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {T : ℝ} (hT : 1 ≤ T)
    (hpos : ∀ x, 0 < heat ρ T x) :
    entropyH ρ T ≤ (Real.exp (-(4 * π ^ 2) * (T - 1)) *
      ∑' n, heatBound (∫ y in (0 : ℝ)..1, |ρ y|) 0 1 n) ^ 2 := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun x => klFun (heat ρ T x))
    (C := (Real.exp (-(4 * π ^ 2) * (T - 1)) *
      ∑' n, heatBound (∫ y in (0 : ℝ)..1, |ρ y|) 0 1 n) ^ 2) (fun x _ => by
      have hd := abs_heatD_sub_le ρ 0 hT x
      simp only [↓reduceIte, hρ1] at hd
      rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg (hpos x).le)]
      refine (klFun_le_sq (hpos x)).trans ?_
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hd 2)
  simp only [sub_zero, abs_one, mul_one] at h
  exact (le_abs_self _).trans h

/-- Sub-milestone (c): `H(p_t) ≤ 6 log(1 + I(p_t)/(12·4π²))` for `t > 0`. -/
theorem entropyH_le_log_fisher (hρ : IntervalIntegrable ρ volume 0 1) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y in (0 : ℝ)..1, ρ y = 1) {t : ℝ} (ht : 0 < t) :
    entropyH ρ t ≤ 6 * Real.log (1 + fisherI ρ t / (12 * (4 * π ^ 2))) := by
  set K := ∑' n, heatBound (∫ y in (0 : ℝ)..1, |ρ y|) 0 1 n
  have hmono := psiH_monotoneOn hρ hρ0 hρ1
  have hbound : ∀ᶠ T in atTop, psiH ρ t ≤ (Real.exp (-(4 * π ^ 2) * (T - 1)) * K) ^ 2 := by
    filter_upwards [eventually_ge_atTop (max t 1)] with T hT
    have hT0 : 0 < T := lt_of_lt_of_le ht ((le_max_left _ _).trans hT)
    have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
    refine (hmono ht hT0 ((le_max_left _ _).trans hT)).trans ?_
    have hlog : 0 ≤ Real.log (1 + fisherI ρ T / (12 * (4 * π ^ 2))) :=
      Real.log_nonneg (by have := fisherI_nonneg hρ hρ0 hρ1 hT0; simp only [le_add_iff_nonneg_right]; positivity)
    have := entropyH_le_sq_decay (ρ := ρ) hρ1 hT1 (heat_pos hρ hρ0 hρ1 hT0)
    unfold psiH
    linarith
  have hlim : Tendsto (fun T : ℝ => (Real.exp (-(4 * π ^ 2) * (T - 1)) * K) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => -(4 * π ^ 2) * (T - 1)) atTop atBot := by
      have : Tendsto (fun T : ℝ => (4 * π ^ 2) * (T + -1)) atTop atTop :=
        (tendsto_atTop_add_const_right _ _ tendsto_id).const_mul_atTop (by positivity)
      convert tendsto_neg_atTop_atBot.comp this using 1
      funext T; simp only [Function.comp_apply]; ring
    have h2 := ((Real.tendsto_exp_atBot.comp h1).mul_const K).pow 2
    simpa using h2
  have h0 : psiH ρ t ≤ 0 := ge_of_tendsto hlim hbound
  unfold psiH at h0
  linarith

end Flow

end SharpLSI
