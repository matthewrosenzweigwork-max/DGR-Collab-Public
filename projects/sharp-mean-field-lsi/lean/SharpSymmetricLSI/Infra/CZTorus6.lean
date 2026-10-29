import SharpSymmetricLSI.Infra.CZTorus5

/-!
# Morrey's inequality on cubes and on `𝕋^ι` (R23 lane, CZ part 6)

For `F ∈ C¹(ℝ^ι)` with `G = ∑ᵢ |∂ᵢF|`, a cube `Q` of side `r` and `x ∈ Q`:
`∫_Q |F(z) - F(x)| dz ≤ r ∫₀¹ ∫_Q G(x + t(z-x)) dz dt` (fundamental theorem on segments), and
the substitution `w = x + t(z-x)` (Jacobian `t^d`, image a subcube of volume `(tr)^d`) with Hölder
gives `≤ r^{1+d-d/N} ‖G‖_{L^N(Q)} N/(N-d)` for `N > d`. Averaging over `Q ∋ x, y`:
`|F(x) - F(y)| ≤ 2N/(N-d) r^{1-d/N} ‖G‖_{L^N(Q)}`. On the torus (`r ≤ 1/2`, close lifts) the
cube integral is bounded by the torus integral (`morrey_torus`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `∑ᵢ |∂ᵢ F|`. -/
noncomputable def gradSum (F : (ι → ℝ) → ℝ) (w : ι → ℝ) : ℝ :=
  ∑ i, |fderiv ℝ F w (Pi.single i 1)|

theorem fderiv_apply_eq_sum (F : (ι → ℝ) → ℝ) (w h : ι → ℝ) :
    fderiv ℝ F w h = ∑ i, h i * fderiv ℝ F w (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Pi.single i (h i) = h i • (Pi.single i 1 : ι → ℝ) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem abs_fderiv_le (F : (ι → ℝ) → ℝ) (w h : ι → ℝ) {r : ℝ} (hh : ∀ i, |h i| ≤ r) :
    |fderiv ℝ F w h| ≤ r * gradSum F w := by
  rw [fderiv_apply_eq_sum, gradSum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hh i) (abs_nonneg _)

theorem continuous_gradSum {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) : Continuous (gradSum F) :=
  continuous_finset_sum _ fun i _ =>
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).abs

/-- **Segment bound**: `|F(z) - F(x)| ≤ r ∫₀¹ G(x + t(z-x)) dt` if `|zᵢ - xᵢ| ≤ r`. -/
theorem enorm_sub_le_segment {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) (x z : ι → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hzx : ∀ i, |z i - x i| ≤ r) :
    ‖F z - F x‖ₑ ≤ ENNReal.ofReal r *
      ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (gradSum F (x + t • (z - x))) := by
  set φ : ℝ → ℝ := fun t => F (x + t • (z - x))
  have hFd : Differentiable ℝ F := hF.differentiable one_ne_zero
  have hφd : ∀ t, HasDerivAt φ (fderiv ℝ F (x + t • (z - x)) (z - x)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • (z - x)) (z - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (z - x)).const_add x
    exact (hFd _).hasFDerivAt.comp_hasDerivAt t h1
  have hcl : Continuous fun t : ℝ => x + t • (z - x) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hcont : Continuous fun t => fderiv ℝ F (x + t • (z - x)) (z - x) :=
    ((hF.continuous_fderiv one_ne_zero).comp hcl).clm_apply continuous_const
  have hFTC : F z - F x = ∫ t in (0 : ℝ)..1, fderiv ℝ F (x + t • (z - x)) (z - x) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hφd t)
      (hcont.intervalIntegrable _ _)]
    simp [φ]
  rw [hFTC, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun t => ?_
  rw [← ENNReal.ofReal_mul hr, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
  refine ENNReal.ofReal_le_ofReal (abs_fderiv_le F _ _ fun i => ?_)
  simpa using hzx i

/-! ### The substitution `w = x + t(z - x)` -/

theorem lintegral_comp_affine {H : (ι → ℝ) → ℝ≥0∞} (hH : Measurable H) (x : ι → ℝ) {t : ℝ}
    (ht : 0 < t) :
    ∫⁻ z, H (x + t • (z - x)) = ENNReal.ofReal ((t ^ Fintype.card ι)⁻¹) * ∫⁻ w, H w := by
  set c : ι → ℝ := x - t • x
  have e : ∀ z : ι → ℝ, x + t • (z - x) = t • z + c := fun z => by
    simp only [c, smul_sub]; abel
  simp_rw [e]
  have hmap := Measure.map_addHaar_smul (volume : Measure (ι → ℝ)) ht.ne'
  have hm : Measurable fun w : ι → ℝ => H (w + c) := hH.comp (measurable_add_const c)
  calc ∫⁻ z, H (t • z + c) = ∫⁻ w, H (w + c) ∂(Measure.map (t • ·) volume) :=
        (lintegral_map hm (measurable_const_smul t)).symm
    _ = ENNReal.ofReal ((t ^ Fintype.card ι)⁻¹) * ∫⁻ w, H (w + c) := by
        rw [hmap, lintegral_smul_measure, Module.finrank_fintype_fun_eq_card,
          abs_of_pos (by positivity)]
        rfl
    _ = _ := by rw [lintegral_add_right_eq_self (fun w => H w) c]

/-- The preimage of `S` under the inverse substitution. -/
def scaledSet (x : ι → ℝ) (t : ℝ) (S : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {w | x + t⁻¹ • (w - x) ∈ S}

theorem measurableSet_scaledSet (x : ι → ℝ) (t : ℝ) {S : Set (ι → ℝ)} (hS : MeasurableSet S) :
    MeasurableSet (scaledSet x t S) :=
  (by fun_prop : Measurable fun w : ι → ℝ => x + t⁻¹ • (w - x)) hS

theorem setLIntegral_comp_affine {H : (ι → ℝ) → ℝ≥0∞} (hH : Measurable H) (x : ι → ℝ) {t : ℝ}
    (ht : 0 < t) {S : Set (ι → ℝ)} (hS : MeasurableSet S) :
    ∫⁻ z in S, H (x + t • (z - x)) =
      ENNReal.ofReal ((t ^ Fintype.card ι)⁻¹) * ∫⁻ w in scaledSet x t S, H w := by
  rw [← lintegral_indicator hS, ← lintegral_indicator (measurableSet_scaledSet x t hS)]
  have e : ∀ z, S.indicator (fun z => H (x + t • (z - x))) z =
      (scaledSet x t S).indicator H (x + t • (z - x)) := by
    intro z
    have hz : x + t⁻¹ • (x + t • (z - x) - x) = z := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
    have hmem : (x + t • (z - x) ∈ scaledSet x t S) ↔ z ∈ S := by
      show x + t⁻¹ • (x + t • (z - x) - x) ∈ S ↔ _
      rw [hz]
    by_cases hzS : z ∈ S
    · rw [Set.indicator_of_mem hzS, Set.indicator_of_mem (hmem.mpr hzS)]
    · rw [Set.indicator_of_notMem hzS, Set.indicator_of_notMem (mt hmem.mp hzS)]
  simp_rw [e]
  exact lintegral_comp_affine (hH.indicator (measurableSet_scaledSet x t hS)) x ht

/-- The cube `∏ [aᵢ, aᵢ + r]`. -/
def cubeAt (a : ι → ℝ) (r : ℝ) : Set (ι → ℝ) := Set.pi univ fun i => Icc (a i) (a i + r)

theorem measurableSet_cubeAt (a : ι → ℝ) (r : ℝ) : MeasurableSet (cubeAt a r) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem volume_cubeAt (a : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (cubeAt a r) = ENNReal.ofReal (r ^ Fintype.card ι) := by
  rw [cubeAt, Set.pi_univ_Icc, Real.volume_Icc_pi]
  simp only [Pi.add_apply, add_sub_cancel_left, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.ofReal_pow hr]

theorem scaledSet_cube_subset {a x : ι → ℝ} {r t : ℝ} (hx : x ∈ cubeAt a r) (ht0 : 0 < t)
    (ht1 : t ≤ 1) : scaledSet x t (cubeAt a r) ⊆ cubeAt a r := by
  intro w hw
  simp only [scaledSet, cubeAt, Set.mem_setOf_eq, Set.mem_pi, mem_univ, true_implies,
    mem_Icc, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hw hx ⊢
  intro i
  obtain ⟨h1, h2⟩ := hw i
  obtain ⟨h3, h4⟩ := hx i
  have hw' : w i = (1 - t) * x i + t * (x i + t⁻¹ * (w i - x i)) := by
    field_simp; ring
  constructor
  · rw [hw']; nlinarith
  · rw [hw']; nlinarith

theorem volume_scaledSet_cube {a x : ι → ℝ} {r t : ℝ} (hr : 0 ≤ r) (ht : 0 < t) :
    volume (scaledSet x t (cubeAt a r)) = ENNReal.ofReal ((t * r) ^ Fintype.card ι) := by
  have h := setLIntegral_comp_affine (H := fun _ => (1 : ℝ≥0∞)) measurable_const x ht
    (measurableSet_cubeAt a r)
  simp only [setLIntegral_const, one_mul] at h
  rw [volume_cubeAt a hr] at h
  have hpos : (0 : ℝ) < t ^ Fintype.card ι := by positivity
  calc volume (scaledSet x t (cubeAt a r))
      = ENNReal.ofReal (t ^ Fintype.card ι) * (ENNReal.ofReal ((t ^ Fintype.card ι)⁻¹) *
          volume (scaledSet x t (cubeAt a r))) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hpos.le, mul_inv_cancel₀ hpos.ne',
          ENNReal.ofReal_one, one_mul]
    _ = ENNReal.ofReal (t ^ Fintype.card ι) * ENNReal.ofReal (r ^ Fintype.card ι) := by rw [← h]
    _ = ENNReal.ofReal ((t * r) ^ Fintype.card ι) := by rw [← ENNReal.ofReal_mul hpos.le, mul_pow]

/-! ### The cube estimate -/

/-- Hölder on a set: `∫_A g ≤ |A|^{1/q} (∫_A g^N)^{1/N}`. -/
theorem setLIntegral_le_holder {A : Set (ι → ℝ)} {g : (ι → ℝ) → ℝ≥0∞} (hg : AEMeasurable g)
    {N : ℝ} (hN : 1 < N) :
    ∫⁻ w in A, g w ≤ volume A ^ (1 / Real.conjExponent N) * (∫⁻ w in A, g w ^ N) ^ (1 / N) := by
  have hpq : (Real.conjExponent N).HolderConjugate N :=
    (Real.HolderConjugate.conjExponent hN).symm
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict A) hpq (f := fun _ => 1) (g := g)
    aemeasurable_const hg.restrict
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, setLIntegral_const, one_mul] at h
  simpa [Measure.restrict_apply MeasurableSet.univ] using h

theorem integral_rpow_Ioc {s : ℝ} (hs : -1 < s) :
    ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ s) = ENNReal.ofReal (1 / (s + 1)) := by
  have hii : IntegrableOn (fun t : ℝ => t ^ s) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' hs).1
  rw [← ofReal_integral_eq_lintegral_ofReal hii
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht =>
      Real.rpow_nonneg ht.1.le s)), ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl hs)]
  rw [Real.one_rpow, Real.zero_rpow (by linarith), sub_zero]

/-- **The cube estimate**: for `x ∈ Q` (side `r`), `∫_Q |F - F(x)| ≤ r^{1+d-d/N} N/(N-d) ‖G‖_{L^N(Q)}`. -/
theorem lintegral_cube_sub_le {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) {a x : ι → ℝ} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ cubeAt a r) {N : ℕ} (hN : (Fintype.card ι : ℝ) < N) (hN2 : 2 ≤ N) :
    ∫⁻ z in cubeAt a r, ‖F z - F x‖ₑ ≤
      ENNReal.ofReal (r ^ (1 + (Fintype.card ι : ℝ) - Fintype.card ι / N) *
        (N / (N - Fintype.card ι))) *
      (∫⁻ w in cubeAt a r, ENNReal.ofReal (gradSum F w) ^ (N : ℝ)) ^ (1 / (N : ℝ)) := by
  set d : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hd
  set Q := cubeAt a r with hQ
  set M := (∫⁻ w in Q, ENNReal.ofReal (gradSum F w) ^ (N : ℝ)) ^ (1 / (N : ℝ)) with hM
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt hd0 hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hGc : Continuous (gradSum F) := continuous_gradSum hF
  set Gf : (ι → ℝ) → ℝ≥0∞ := fun w => ENNReal.ofReal (gradSum F w)
  have hGm : Measurable Gf := ENNReal.measurable_ofReal.comp hGc.measurable
  have hQm := measurableSet_cubeAt a r
  -- step 1: segments
  have hseg : ∀ z ∈ Q, ‖F z - F x‖ₑ ≤
      ENNReal.ofReal r * ∫⁻ t in Ioc (0 : ℝ) 1, Gf (x + t • (z - x)) := by
    intro z hz
    refine enorm_sub_le_segment hF x z hr.le fun i => ?_
    have h1 := hz i (mem_univ i)
    have h2 := hx i (mem_univ i)
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- step 2: inner integrals
  have hinner : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ z in Q, Gf (x + t • (z - x)) ≤
      ENNReal.ofReal (t ^ (-(d / N)) * r ^ (d - d / N)) * M := by
    intro t ht
    rw [setLIntegral_comp_affine hGm x ht.1 hQm]
    have hsub := scaledSet_cube_subset hx ht.1 ht.2
    have hvol := volume_scaledSet_cube (a := a) (x := x) hr.le ht.1
    have hH := setLIntegral_le_holder (A := scaledSet x t Q) hGm.aemeasurable hN1
    have hmono : (∫⁻ w in scaledSet x t Q, Gf w ^ (N : ℝ)) ≤ ∫⁻ w in Q, Gf w ^ (N : ℝ) :=
      lintegral_mono_set hsub
    have hq : 1 / Real.conjExponent (N : ℝ) = 1 - 1 / N := by
      rw [Real.conjExponent]
      have : (N : ℝ) - 1 ≠ 0 := by linarith
      field_simp
    calc ENNReal.ofReal ((t ^ Fintype.card ι)⁻¹) * ∫⁻ w in scaledSet x t Q, Gf w
        ≤ ENNReal.ofReal ((t ^ Fintype.card ι)⁻¹) *
            (volume (scaledSet x t Q) ^ (1 / Real.conjExponent (N : ℝ)) * M) := by
          gcongr
          exact hH.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hmono (by positivity)))
      _ = ENNReal.ofReal ((t ^ Fintype.card ι)⁻¹) *
            ENNReal.ofReal (((t * r) ^ Fintype.card ι) ^ (1 - 1 / (N : ℝ))) * M := by
          rw [hvol, hq, ENNReal.ofReal_rpow_of_nonneg (pow_nonneg (mul_pos ht.1 hr).le _) (by
            have : (1 : ℝ) / N ≤ 1 := by rw [div_le_one hN0]; exact hN1.le
            linarith), mul_assoc]
      _ = ENNReal.ofReal (t ^ (-(d / N)) * r ^ (d - d / N)) * M := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg ht.1.le _))]
          congr 2
          rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg ht.1.le,
            ← Real.rpow_mul (mul_pos ht.1 hr).le, Real.mul_rpow ht.1.le hr.le, ← hd,
            ← mul_assoc, ← Real.rpow_add ht.1]
          congr 2
          · field_simp; ring
          · field_simp
  -- assembly
  have hdN : -(d / N) > -1 := by
    have : d / N < 1 := by rw [div_lt_one hN0]; exact hN
    linarith
  have hmeas : Measurable (Function.uncurry fun (z : ι → ℝ) (t : ℝ) => Gf (x + t • (z - x))) :=
    hGm.comp (continuous_const.add (continuous_snd.smul (continuous_fst.sub continuous_const))).measurable
  calc ∫⁻ z in Q, ‖F z - F x‖ₑ
      ≤ ∫⁻ z in Q, ENNReal.ofReal r * ∫⁻ t in Ioc (0 : ℝ) 1, Gf (x + t • (z - x)) :=
        setLIntegral_mono' hQm hseg
    _ = ENNReal.ofReal r * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ z in Q, Gf (x + t • (z - x)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap
          hmeas.aemeasurable]
    _ ≤ ENNReal.ofReal r * ∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (t ^ (-(d / N)) * r ^ (d - d / N)) * M := by
        exact mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioc hinner)
    _ = ENNReal.ofReal r * (ENNReal.ofReal (r ^ (d - d / N)) *
          ENNReal.ofReal (1 / (-(d / N) + 1)) * M) := by
        congr 1
        have e : ∀ t ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-(d / N)) * r ^ (d - d / N)) * M =
            ENNReal.ofReal (t ^ (-(d / N))) * (ENNReal.ofReal (r ^ (d - d / N)) * M) := by
          intro t ht
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg ht.1.le _), mul_assoc]
        rw [setLIntegral_congr_fun measurableSet_Ioc e, lintegral_mul_const _
          ((measurable_id'.pow_const _).ennreal_ofReal : Measurable fun t : ℝ =>
            ENNReal.ofReal (t ^ (-(d / N)))), integral_rpow_Ioc hdN]
        ring
    _ = _ := by
        have hNd : (N : ℝ) - d ≠ 0 := by linarith
        have hden : 0 < -(d / N) + 1 := by linarith
        rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hr.le,
          ← ENNReal.ofReal_mul (mul_nonneg hr.le (Real.rpow_nonneg hr.le _))]
        congr 2
        rw [show (1 : ℝ) + d - d / N = 1 + (d - d / N) by ring, Real.rpow_add hr, Real.rpow_one]
        field_simp
        rw [show -d + (N : ℝ) = N - d by ring]
        exact div_self hNd

/-- **Morrey on a cube**: `|F(x) - F(y)| ≤ 2 r^{1-d/N} N/(N-d) ‖G‖_{L^N(Q)}` for `x, y ∈ Q`. -/
theorem enorm_sub_le_cube {F : (ι → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) {a x y : ι → ℝ} {r : ℝ}
    (hr : 0 < r) (hx : x ∈ cubeAt a r) (hy : y ∈ cubeAt a r) {N : ℕ}
    (hN : (Fintype.card ι : ℝ) < N) (hN2 : 2 ≤ N) :
    ‖F x - F y‖ₑ ≤
      ENNReal.ofReal (2 * r ^ (1 - (Fintype.card ι : ℝ) / N) * (N / (N - Fintype.card ι))) *
      (∫⁻ w in cubeAt a r, ENNReal.ofReal (gradSum F w) ^ (N : ℝ)) ^ (1 / (N : ℝ)) := by
  have h1 := lintegral_cube_sub_le hF hr hx hN hN2
  have h2 := lintegral_cube_sub_le hF hr hy hN hN2
  set d : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hd
  set Q := cubeAt a r
  set M := (∫⁻ w in Q, ENNReal.ofReal (gradSum F w) ^ (N : ℝ)) ^ (1 / (N : ℝ))
  set c : ℝ := N / (N - d)
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hFc : Continuous F := hF.continuous
  have hQm := measurableSet_cubeAt a r
  have hsum : ENNReal.ofReal (r ^ Fintype.card ι) * ‖F x - F y‖ₑ ≤
      2 * (ENNReal.ofReal (r ^ (1 + d - d / N) * c) * M) := by
    calc ENNReal.ofReal (r ^ Fintype.card ι) * ‖F x - F y‖ₑ = ∫⁻ z in Q, ‖F x - F y‖ₑ := by
          rw [setLIntegral_const, volume_cubeAt a hr.le, mul_comm]
      _ ≤ ∫⁻ z in Q, (‖F z - F x‖ₑ + ‖F z - F y‖ₑ) := by
          refine lintegral_mono fun z => ?_
          calc ‖F x - F y‖ₑ = ‖(F z - F y) - (F z - F x)‖ₑ := by congr 1; ring
            _ ≤ ‖F z - F y‖ₑ + ‖F z - F x‖ₑ := enorm_sub_le
            _ = _ := add_comm _ _
      _ = (∫⁻ z in Q, ‖F z - F x‖ₑ) + ∫⁻ z in Q, ‖F z - F y‖ₑ :=
          lintegral_add_left (f := fun z => ‖F z - F x‖ₑ)
            ((hFc.sub continuous_const).measurable.enorm) _
      _ ≤ ENNReal.ofReal (r ^ (1 + d - d / N) * c) * M +
            ENNReal.ofReal (r ^ (1 + d - d / N) * c) * M := add_le_add h1 h2
      _ = 2 * (ENNReal.ofReal (r ^ (1 + d - d / N) * c) * M) := by rw [two_mul]
  have hr0 : ENNReal.ofReal (r ^ Fintype.card ι) ≠ 0 := by
    simpa using pow_pos hr (Fintype.card ι)
  have hrt : ENNReal.ofReal (r ^ Fintype.card ι) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hre : 2 * (ENNReal.ofReal (r ^ (1 + d - d / N) * c) * M) =
      ENNReal.ofReal (r ^ Fintype.card ι) *
        (ENNReal.ofReal (2 * r ^ (1 - d / N) * c) * M) := by
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    congr 1
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [← Real.rpow_natCast, ← hd, show (1 : ℝ) + d - d / N = d + (1 - d / N) by ring,
      Real.rpow_add hr]
    ring
  rw [hre] at hsum
  exact (ENNReal.mul_le_mul_iff_right hr0 hrt).mp hsum

theorem dist_torus_le_half (x y : UnitAddTorus ι) : dist x y ≤ 1 / 2 := by
  refine (dist_pi_le_iff (by norm_num)).mpr fun i => ?_
  rw [dist_eq_norm]
  have := AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := x i - y i) one_ne_zero
  simpa using this

/-- **Morrey on the torus.** -/
theorem morrey_torus {f : UnitAddTorus ι → ℝ} (hf : ContDiff ℝ 1 (f ∘ liftT)) {N : ℕ}
    (hN : (Fintype.card ι : ℝ) < N) (hN2 : 2 ≤ N) (x y : UnitAddTorus ι) :
    ‖f x - f y‖ₑ ≤
      ENNReal.ofReal (2 * dist x y ^ (1 - (Fintype.card ι : ℝ) / N) *
        (N / (N - Fintype.card ι))) *
      (∫⁻ z, ENNReal.ofReal (∑ i, |dpart f i z|) ^ (N : ℝ)) ^ (1 / (N : ℝ)) := by
  rcases eq_or_ne x y with rfl | hxy
  · simp
  set r := dist x y with hrdef
  have hr : 0 < r := dist_pos.mpr hxy
  obtain ⟨a, b, ha, hb, hab⟩ := exists_close_lifts x y
  set c : ι → ℝ := fun i => min (a i) (b i)
  have habi : ∀ i, |a i - b i| ≤ r := fun i =>
    (norm_le_pi_norm (a - b) i).trans hab |>.trans_eq' (by simp [Real.norm_eq_abs])
  have hac : a ∈ cubeAt c r := fun i _ => by
    have := habi i
    rw [abs_le] at this
    constructor
    · exact min_le_left _ _
    · simp only [c]; rcases le_total (a i) (b i) with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
  have hbc : b ∈ cubeAt c r := fun i _ => by
    have := habi i
    rw [abs_le] at this
    constructor
    · exact min_le_right _ _
    · simp only [c]; rcases le_total (a i) (b i) with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; linarith
  have hcube := enorm_sub_le_cube hf hr hac hbc hN hN2
  simp only [Function.comp, ha, hb] at hcube
  refine hcube.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow ?_ (by positivity)))
  -- the cube integral is at most the torus integral
  set H : UnitAddTorus ι → ℝ≥0∞ := fun z => ENNReal.ofReal (∑ i, |dpart f i z|) ^ (N : ℝ)
  have hgs : ∀ w, ENNReal.ofReal (gradSum (f ∘ liftT) w) ^ (N : ℝ) = H (liftT w) := by
    intro w
    simp only [H, gradSum, dpart_liftT]
  simp_rw [hgs]
  have hHm : Measurable H := by
    have : Continuous fun z => ∑ i, |dpart f i z| := continuous_finset_sum _ fun i _ =>
      (continuous_of_contDiff_lift (contDiff_dpart (n := 0) hf i)).abs
    exact (ENNReal.measurable_ofReal.comp this.measurable).pow_const _
  set s : ι → ℝ := fun i => c i - 1 / 2
  have hr2 : r ≤ 1 / 2 := dist_torus_le_half x y
  have hsub : ∀ w ∈ cubeAt c r, w - s ∈ unitBox ι := by
    intro w hw i _
    have := hw i (mem_univ i)
    simp only [s, Pi.sub_apply, mem_Ioc]
    constructor <;> linarith [this.1, this.2]
  rw [← lintegral_unitBox_sub hHm (-s)]
  calc ∫⁻ w in cubeAt c r, H (liftT w)
      = ∫⁻ w, (cubeAt c r).indicator (fun w => H (liftT w)) w :=
        (lintegral_indicator (measurableSet_cubeAt c r) _).symm
    _ = ∫⁻ v, (cubeAt c r).indicator (fun w => H (liftT w)) (v + s) :=
        (lintegral_add_right_eq_self _ s).symm
    _ ≤ ∫⁻ v, (unitBox ι).indicator (fun v => H (liftT (v - -s))) v := by
        refine lintegral_mono fun v => ?_
        by_cases hv : v + s ∈ cubeAt c r
        · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (by simpa using hsub _ hv), sub_neg_eq_add]
        · rw [Set.indicator_of_notMem hv]; exact zero_le
    _ = ∫⁻ v in unitBox ι, H (liftT (v - -s)) :=
        lintegral_indicator (MeasurableSet.univ_pi fun _ => measurableSet_Ioc) _

end SharpLSI
