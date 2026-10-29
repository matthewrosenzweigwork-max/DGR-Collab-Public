import FullLabeledLSI.Examples.Paper.Sec9RegularityA
import SharpSymmetricLSI.Paper.Rothaus
import SharpSymmetricLSI.Paper.DensMeasure

/-!
# Section 9 regularity, module C: bounded-function toolkit and the first variation of `S_{r,A}`

Lane C of the Section 9 formalization (H8), Steps 2-3 of `Audit/FLX/laneC/PLAN_C.md`.

COPIED (namespace changed from `SharpLSI.FL.Prop82` to `SharpLSI.FL.Ex.Reg`, otherwise unmodified;
source branch `claude/prop82-lane-c-s8pz05`, commit `ce7043d`):
* from `FullLabeledLSI/Nonvacuity/Prop82/CBdd.lean`: `BM` and its algebra, `BM.of_isSmoothT`,
  `integral_quad`, `memH1_of_isWeakGrad`;
* from `CCalc.lean`: `hasDerivAt_sq_mul_log_sq`, `abs_mul_log_sq_le`, `hasDerivAt_integral_sq_log_sq`;
* from `CProfile.lean`/`CVariation.lean`: `BM.mul_log_sq`, `BM.memLp`, `BM.w`,
  `isWeakGrad_smooth_zero`, `memH1_w`, and the pattern of `Wd_hasDerivAt_zero`.

NEW: the competitor `|u + tφ| / √N(t)`, the profile `Fbar` bounding `S_{r,A}` of the competitor, and
`weak_euler`: if `u ≥ 0` is bounded, in `H¹`, `∫ u² = 1` and minimizes `S_{r,A}`, then for every smooth `φ`
`4∫u'φ' + ∫Auφ - 2r∫uφ log u² = S(u) ∫uφ`.  No finite-dimensional multipliers are needed.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Ex.Reg

open SharpLSI

/-! ### Bounded measurable functions (copy of `CBdd`) -/

structure BM (f : Torus 1 → ℝ) : Prop where
  meas : Measurable f
  bdd : ∃ C, ∀ x, |f x| ≤ C

namespace BM

theorem integrable {f : Torus 1 → ℝ} (h : BM f) : Integrable f (haar 1) := by
  obtain ⟨C, hC⟩ := h.bdd
  exact Integrable.of_bound h.meas.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem const (c : ℝ) : BM (fun _ => c) := ⟨measurable_const, ⟨|c|, fun _ => le_rfl⟩⟩

theorem add {f g : Torus 1 → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x + g x) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  exact ⟨hf.meas.add hg.meas, ⟨C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩⟩

theorem sub {f g : Torus 1 → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x - g x) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  exact ⟨hf.meas.sub hg.meas, ⟨C + D, fun x => (abs_sub _ _).trans (add_le_add (hC x) (hD x))⟩⟩

theorem mul {f g : Torus 1 → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x * g x) := by
  obtain ⟨C, hC⟩ := hf.bdd
  obtain ⟨D, hD⟩ := hg.bdd
  refine ⟨hf.meas.mul hg.meas, ⟨C * D, fun x => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))

theorem const_mul {f : Torus 1 → ℝ} (hf : BM f) (c : ℝ) : BM (fun x => c * f x) :=
  (BM.const c).mul hf

theorem sq {f : Torus 1 → ℝ} (hf : BM f) : BM (fun x => f x ^ 2) := by
  simpa [pow_two] using hf.mul hf

theorem of_continuous {f : Torus 1 → ℝ} (hf : Continuous f) : BM f := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨hf.measurable, ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩⟩

end BM

theorem BM.of_isSmoothT {φ : Torus 1 → ℝ} (h : IsSmoothT φ) : BM φ :=
  BM.of_continuous (continuous_of_isSmoothT h)

/-- Quadratic expansion of `∫ e (a + t b)²`. -/
theorem integral_quad {e a b : Torus 1 → ℝ} (he : BM e) (ha : BM a) (hb : BM b) (t : ℝ) :
    ∫ x, e x * (a x + t * b x) ^ 2 ∂haar 1 =
      (∫ x, e x * a x ^ 2 ∂haar 1) + 2 * t * (∫ x, e x * (a x * b x) ∂haar 1) +
        t ^ 2 * (∫ x, e x * b x ^ 2 ∂haar 1) := by
  have h1 := (he.mul ha.sq).integrable
  have h2 := (he.mul (ha.mul hb)).integrable
  have h3 := (he.mul hb.sq).integrable
  have : ∀ x, e x * (a x + t * b x) ^ 2 =
      e x * a x ^ 2 + (2 * t) * (e x * (a x * b x)) + t ^ 2 * (e x * b x ^ 2) := fun x => by ring
  simp_rw [this]
  have h12 : Integrable (fun x => e x * a x ^ 2 + (2 * t) * (e x * (a x * b x))) (haar 1) :=
    h1.add (h2.const_mul _)
  rw [integral_add h12 (h3.const_mul _), integral_add h1 (h2.const_mul _),
    integral_const_mul, integral_const_mul]

/-- A function with weak derivative in `L²` and itself in `L²` is in `H¹`. -/
theorem memH1_of_isWeakGrad {w G : Torus 1 → ℝ} (hw : IsWeakGrad w (fun y _ => G y))
    (hw2 : MemLp w 2 (haar 1)) (hG2 : MemLp G 2 (haar 1)) :
    MemH1 (haar 1) w ∧ (fun x => weakGrad w x 0) =ᵐ[haar 1] G := by
  have hae : weakGrad w =ᵐ[haar 1] fun y _ => G y := weakGrad_ae_eq hw
  have hae0 : (fun x => weakGrad w x 0) =ᵐ[haar 1] G := by
    filter_upwards [hae] with x hx
    exact congrFun hx 0
  refine ⟨⟨⟨_, hw⟩, hw2, ?_⟩, hae0⟩
  refine hG2.norm.ae_eq ?_
  filter_upwards [hae] with x hx
  rw [hx]
  simp [sqNorm, Real.sqrt_sq_eq_abs]

/-! ### Calculus of `s ↦ s² log s²` (copy of `CCalc`) -/

/-- Derivative of `s ↦ s² log s²` (with the convention `log 0 = 0`). -/
theorem hasDerivAt_sq_mul_log_sq (r : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 2 * Real.log (s ^ 2)) (2 * r * (Real.log (r ^ 2) + 1)) r := by
  by_cases hr : r = 0
  · subst hr
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hc : Continuous fun t : ℝ => |2 * (|t| * Real.log |t|)| :=
      (continuous_abs.comp (continuous_const.mul
        (Real.continuous_mul_log.comp continuous_abs)))
    have h0 : Tendsto (fun t : ℝ => |2 * (|t| * Real.log |t|)|) (𝓝 0) (𝓝 0) := by
      have := hc.tendsto 0
      simpa using this
    have h1 : Tendsto (fun t : ℝ => |2 * (|t| * Real.log |t|)|) (𝓝[≠] 0) (𝓝 0) :=
      h0.mono_left nhdsWithin_le_nhds
    have h2 := squeeze_zero_norm (f := fun t : ℝ => t⁻¹ • (((0 + t) ^ 2 * Real.log ((0 + t) ^ 2)) -
        (0 ^ 2 * Real.log (0 ^ 2)))) (a := fun t : ℝ => |2 * (|t| * Real.log |t|)|) ?_ h1
    · simpa using h2
    · intro t
      by_cases ht : t = 0
      · subst ht; simp
      · have hl : Real.log (t ^ 2) = 2 * Real.log |t| := by
          rw [← sq_abs, Real.log_pow]; norm_num
        have : t⁻¹ • (((0 + t) ^ 2 * Real.log ((0 + t) ^ 2)) - (0 ^ 2 * Real.log (0 ^ 2))) =
            t * Real.log (t ^ 2) := by
          simp only [smul_eq_mul, zero_add]
          field_simp
          simp
        rw [this, Real.norm_eq_abs, hl]
        apply le_of_eq
        simp only [abs_mul, abs_abs]
        ring
  · have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h2 : HasDerivAt (fun s : ℝ => Real.log (s ^ 2)) (2 * r / r ^ 2) r :=
      h1.log hr2
    have h3 := h1.mul h2
    convert h3 using 1
    field_simp

/-- A bound on `|w log w²|` for `|w| ≤ W`. -/
theorem abs_mul_log_sq_le {w W : ℝ} (hw : |w| ≤ W) (hW : 1 ≤ W) :
    |w * Real.log (w ^ 2)| ≤ 2 + W ^ 2 * Real.log (W ^ 2) := by
  have hM2 : 0 ≤ W ^ 2 * Real.log (W ^ 2) :=
    mul_nonneg (sq_nonneg _) (Real.log_nonneg (by nlinarith))
  rcases le_or_gt |w| 1 with h | h
  · rcases (abs_nonneg w).eq_or_lt with h0 | h0
    · have : w = 0 := abs_eq_zero.mp h0.symm
      subst this; rw [zero_mul, abs_zero]; linarith
    · have hl : Real.log (w ^ 2) = 2 * Real.log |w| := by
        rw [← sq_abs, Real.log_pow]; norm_num
      have := Real.abs_log_mul_self_lt |w| h0 h
      rw [hl, abs_mul, abs_mul, abs_two]
      rw [abs_mul, abs_abs, mul_comm] at this
      nlinarith
  · have h1 := abs_sq_log_sq_le (abs_nonneg w) hw hW
    rw [sq_abs] at h1
    have h2 : |w * Real.log (w ^ 2)| ≤ |w ^ 2 * Real.log (w ^ 2)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg w), ← sq_abs]
      have : |w| ≤ |w| ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    linarith

/-- Differentiation under the integral of `(u + tφ)² log (u + tφ)²`. -/
theorem hasDerivAt_integral_sq_log_sq {u φ : Torus 1 → ℝ} (hu : Measurable u) (hφ : Measurable φ)
    {K L : ℝ} (hK : ∀ x, |u x| ≤ K) (hL : ∀ x, |φ x| ≤ L) (t0 : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, (u x + t * φ x) ^ 2 * Real.log ((u x + t * φ x) ^ 2) ∂haar 1)
      (∫ x, 2 * (u x + t0 * φ x) * φ x * (Real.log ((u x + t0 * φ x) ^ 2) + 1) ∂haar 1) t0 := by
  have : IsProbabilityMeasure (haar 1) := haar_isProbabilityMeasure 1
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL (0 : Torus 1))
  set W : ℝ := max 1 (K + (|t0| + 1) * L) with hWdef
  have hW1 : 1 ≤ W := le_max_left _ _
  have hbd : ∀ t ∈ Set.Icc (t0 - 1) (t0 + 1), ∀ x, |u x + t * φ x| ≤ W := by
    intro t ht x
    have ht' : |t| ≤ |t0| + 1 := by
      rw [abs_le]; constructor <;> cases abs_cases t0 <;> linarith [ht.1, ht.2]
    calc |u x + t * φ x| ≤ |u x| + |t| * |φ x| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ K + (|t0| + 1) * L :=
        add_le_add (hK x) (mul_le_mul ht' (hL x) (abs_nonneg _) (by positivity))
      _ ≤ W := le_max_right _ _
  refine hasDerivAt_integral_bdd (P := haar 1)
    (F := fun t x => (u x + t * φ x) ^ 2 * Real.log ((u x + t * φ x) ^ 2))
    (F' := fun t x => 2 * (u x + t * φ x) * φ x * (Real.log ((u x + t * φ x) ^ 2) + 1))
    (s := Set.Icc (t0 - 1) (t0 + 1)) (Icc_mem_nhds (by linarith) (by linarith))
    ?_ ?_ (L0 := 1 + W ^ 2 * Real.log (W ^ 2)) (L1 := 2 * L * ((2 + W ^ 2 * Real.log (W ^ 2)) + W))
    ?_ ?_ ?_
  · intro t
    have hm : Measurable fun x => u x + t * φ x := hu.add (measurable_const.mul hφ)
    exact (hm.pow_const 2).mul (Real.measurable_log.comp (hm.pow_const 2))
  · intro t
    have hm : Measurable fun x => u x + t * φ x := hu.add (measurable_const.mul hφ)
    exact (((measurable_const.mul hm).mul hφ)).mul
      ((Real.measurable_log.comp (hm.pow_const 2)).add measurable_const)
  · intro t ht x
    have := abs_sq_log_sq_le (abs_nonneg (u x + t * φ x)) (hbd t ht x) hW1
    rwa [sq_abs] at this
  · intro t ht x
    have hb := hbd t ht x
    have h1 := abs_mul_log_sq_le hb hW1
    have hlog : |(u x + t * φ x) * Real.log ((u x + t * φ x) ^ 2)| ≤ 2 + W ^ 2 * Real.log (W ^ 2) := h1
    have : 2 * (u x + t * φ x) * φ x * (Real.log ((u x + t * φ x) ^ 2) + 1) =
        2 * φ x * ((u x + t * φ x) * Real.log ((u x + t * φ x) ^ 2) + (u x + t * φ x)) := by ring
    rw [this, abs_mul, abs_mul, abs_two]
    have h3 : |(u x + t * φ x) * Real.log ((u x + t * φ x) ^ 2) + (u x + t * φ x)| ≤
        (2 + W ^ 2 * Real.log (W ^ 2)) + W :=
      (abs_add_le _ _).trans (add_le_add hlog hb)
    have hnn : 0 ≤ |(u x + t * φ x) * Real.log ((u x + t * φ x) ^ 2) + (u x + t * φ x)| :=
      abs_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hL x) (by norm_num)) h3 hnn (by positivity)
  · intro x t ht
    have h := hasDerivAt_sq_mul_log_sq (u x + t * φ x)
    have hl : HasDerivAt (fun s : ℝ => u x + s * φ x) (φ x) t := by
      simpa using ((hasDerivAt_id t).mul_const (φ x)).const_add (u x)
    refine (h.comp t hl).congr_deriv ?_
    ring


/-! ### Small copies from `CProfile` / `CVariation` -/

theorem BM.mul_log_sq {f : Torus 1 → ℝ} (hf : BM f) : BM (fun x => f x * Real.log (f x ^ 2)) := by
  obtain ⟨C, hC⟩ := hf.bdd
  refine ⟨hf.meas.mul (Real.measurable_log.comp (hf.meas.pow_const 2)), ⟨2 + (max 1 C) ^ 2 * Real.log ((max 1 C) ^ 2), fun x => ?_⟩⟩
  exact abs_mul_log_sq_le ((hC x).trans (le_max_right _ _)) (le_max_left _ _)

theorem BM.memLp {f : Torus 1 → ℝ} (h : BM f) : MemLp f 2 (haar 1) := by
  obtain ⟨C, hC⟩ := h.bdd
  exact MemLp.of_bound h.meas.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

theorem BM.w {u φ : Torus 1 → ℝ} (hu : BM u) (hφ : BM φ) (t : ℝ) : BM (fun x => u x + t * φ x) :=
  hu.add (hφ.const_mul t)

theorem isWeakGrad_smooth_zero {φ : Torus 1 → ℝ} (hφ : IsSmoothT φ) :
    IsWeakGrad φ (fun y _ => dpart_appA φ 0 y) := by
  have h := isWeakGrad_of_contDiff (f := φ) (hφ.of_le (by simp))
  have e : (fun (y : Torus 1) (_ : Fin 1) => dpart_appA φ 0 y) =
      fun y k => fderiv ℝ (φ ∘ liftT) (secT y) (Pi.single k 1) := by
    funext y k; rw [Subsingleton.elim k 0]; rfl
  rw [e]; exact h

theorem memH1_w {u φ : Torus 1 → ℝ} (hH : MemH1 (haar 1) u) (hu : BM u) (hφ : IsSmoothT φ)
    (t : ℝ) :
    MemH1 (haar 1) (fun x => u x + t * φ x) ∧
      (fun x => weakGrad (fun x => u x + t * φ x) x 0) =ᵐ[haar 1]
        fun x => weakGrad u x 0 + t * dpart_appA φ 0 x := by
  have hφb := BM.of_isSmoothT hφ
  have hφ'b := BM.of_isSmoothT (isSmoothT_dpart hφ 0)
  have hw : IsWeakGrad (fun x => u x + t * φ x)
      (fun y _ => weakGrad u y 0 + t * dpart_appA φ 0 y) := by
    have := (isWeakGrad_zero_of_memH1 hH).add ((isWeakGrad_smooth_zero hφ).cmul t)
    exact this
  exact memH1_of_isWeakGrad hw (BM.w hu hφb t).memLp
    ((memLp_weakGrad_zero hH).add (hφ'b.memLp.const_mul t))

/-! ### The functional and the profile -/

/-- `S_{r,A}(f) = 4∫|f'|² + ∫ A f² - 2r H(f²|m)`; definitionally `FL.Ex.sFunctional` of E01. -/
noncomputable def Sfun (r : ℝ) (A f : Torus 1 → ℝ) : ℝ :=
  4 * ∫ x, weakGrad f x 0 ^ 2 ∂haar 1 + ∫ x, A x * f x ^ 2 ∂haar 1 -
    2 * r * (klDiv (densMeasure (fun x => f x ^ 2)) (haar 1)).toReal

noncomputable def MM (u φ e : Torus 1 → ℝ) (t : ℝ) : ℝ := ∫ x, e x * (u x + t * φ x) ^ 2 ∂haar 1

noncomputable abbrev NN (u φ : Torus 1 → ℝ) (t : ℝ) : ℝ := MM u φ (fun _ => 1) t

noncomputable def WW (u φ : Torus 1 → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (weakGrad u x 0 + t * dpart_appA φ 0 x) ^ 2 ∂haar 1

noncomputable def EE (u φ : Torus 1 → ℝ) (t : ℝ) : ℝ :=
  ∫ x, (u x + t * φ x) ^ 2 * Real.log ((u x + t * φ x) ^ 2) ∂haar 1

/-- The upper bound for `S_{r,A}` of the competitor `|u + tφ| / √N(t)`. -/
noncomputable def Fbar (r : ℝ) (A u φ : Torus 1 → ℝ) (t : ℝ) : ℝ :=
  4 * (WW u φ t / NN u φ t) + MM u φ A t / NN u φ t -
    2 * r * (EE u φ t / NN u φ t - Real.log (NN u φ t))

theorem NN_eq (u φ : Torus 1 → ℝ) (t : ℝ) : NN u φ t = ∫ x, (u x + t * φ x) ^ 2 ∂haar 1 := by
  unfold NN MM; simp

theorem MM_hasDerivAt {e u φ : Torus 1 → ℝ} (he : BM e) (hu : BM u) (hφ : BM φ) :
    HasDerivAt (MM u φ e) (2 * ∫ x, e x * (u x * φ x) ∂haar 1) 0 ∧
      MM u φ e 0 = ∫ x, e x * u x ^ 2 ∂haar 1 := by
  have hfun : MM u φ e = fun t => (∫ x, e x * u x ^ 2 ∂haar 1) +
      2 * t * (∫ x, e x * (u x * φ x) ∂haar 1) + t ^ 2 * (∫ x, e x * φ x ^ 2 ∂haar 1) := by
    funext t
    unfold MM
    rw [integral_quad he hu hφ t]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    have h1 := ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
      (∫ x, e x * (u x * φ x) ∂haar 1)
    have h2 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const (∫ x, e x * φ x ^ 2 ∂haar 1)
    have := (h1.const_add (∫ x, e x * u x ^ 2 ∂haar 1)).add h2
    convert this using 1
    · funext t; simp
    · simp
  · rw [hfun]; simp

theorem WW_hasDerivAt {u φ : Torus 1 → ℝ} (hg : MemLp (fun x => weakGrad u x 0) 2 (haar 1))
    (hφ' : BM (dpart_appA φ 0)) :
    HasDerivAt (WW u φ) (2 * ∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1) 0 ∧
      WW u φ 0 = ∫ x, weakGrad u x 0 ^ 2 ∂haar 1 := by
  have i1 : Integrable (fun x => weakGrad u x 0 ^ 2) (haar 1) := hg.integrable_sq
  have i2 : Integrable (fun x => weakGrad u x 0 * dpart_appA φ 0 x) (haar 1) := by
    obtain ⟨C, hC⟩ := hφ'.bdd
    exact (hg.integrable one_le_two).mul_bdd hφ'.meas.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have i3 : Integrable (fun x => dpart_appA φ 0 x ^ 2) (haar 1) := hφ'.sq.integrable
  have hfun : WW u φ = fun t => (∫ x, weakGrad u x 0 ^ 2 ∂haar 1) +
      2 * t * (∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1) +
        t ^ 2 * (∫ x, dpart_appA φ 0 x ^ 2 ∂haar 1) := by
    funext t
    unfold WW
    have : ∀ x, (weakGrad u x 0 + t * dpart_appA φ 0 x) ^ 2 =
        weakGrad u x 0 ^ 2 + (2 * t) * (weakGrad u x 0 * dpart_appA φ 0 x) +
          t ^ 2 * dpart_appA φ 0 x ^ 2 := fun x => by ring
    simp_rw [this]
    have h12 : Integrable (fun x => weakGrad u x 0 ^ 2 +
        (2 * t) * (weakGrad u x 0 * dpart_appA φ 0 x)) (haar 1) := i1.add (i2.const_mul _)
    rw [integral_add h12 (i3.const_mul _), integral_add i1 (i2.const_mul _),
      integral_const_mul, integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    have h1 := ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
      (∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1)
    have h2 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const (∫ x, dpart_appA φ 0 x ^ 2 ∂haar 1)
    have := (h1.const_add (∫ x, weakGrad u x 0 ^ 2 ∂haar 1)).add h2
    convert this using 1
    · funext t; simp
    · simp
  · rw [hfun]; simp

theorem EE_hasDerivAt {u φ : Torus 1 → ℝ} (hu : BM u) (hφ : BM φ) :
    HasDerivAt (EE u φ)
      (2 * (∫ x, u x * φ x * Real.log (u x ^ 2) ∂haar 1) + 2 * ∫ x, u x * φ x ∂haar 1) 0 ∧
      EE u φ 0 = ∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂haar 1 := by
  obtain ⟨K, hK⟩ := hu.bdd
  obtain ⟨L, hL⟩ := hφ.bdd
  refine ⟨?_, by simp [EE]⟩
  have h := hasDerivAt_integral_sq_log_sq hu.meas hφ.meas hK hL 0
  have e : ∫ x, 2 * (u x + 0 * φ x) * φ x * (Real.log ((u x + 0 * φ x) ^ 2) + 1) ∂haar 1 =
      2 * (∫ x, u x * φ x * Real.log (u x ^ 2) ∂haar 1) + 2 * ∫ x, u x * φ x ∂haar 1 := by
    have i1 : Integrable (fun x => u x * φ x * Real.log (u x ^ 2)) (haar 1) := by
      have := (hφ.mul hu.mul_log_sq).integrable
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only; ring
    have i2 : Integrable (fun x => u x * φ x) (haar 1) := (hu.mul hφ).integrable
    have : ∀ x, 2 * (u x + 0 * φ x) * φ x * (Real.log ((u x + 0 * φ x) ^ 2) + 1) =
        2 * (u x * φ x * Real.log (u x ^ 2)) + 2 * (u x * φ x) := fun x => by ring_nf
    simp_rw [this]
    rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
  rw [e] at h
  exact h

/-- `H(w²/N | m)` for a bounded `w` with `∫ w² = N`. -/
theorem klDiv_toReal_sq {w : Torus 1 → ℝ} (hw : BM w) {N : ℝ} (hN : 0 < N)
    (hNw : ∫ x, w x ^ 2 ∂haar 1 = N) :
    (klDiv (densMeasure (fun x => w x ^ 2 / N)) (haar 1)).toReal =
      (∫ x, w x ^ 2 * Real.log (w x ^ 2) ∂haar 1) / N - Real.log N := by
  obtain ⟨K, hK⟩ := hw.bdd
  have hN0 : N ≠ 0 := hN.ne'
  have hρm : Measurable (fun x => w x ^ 2 / N) := (hw.meas.pow_const 2).div_const N
  have hρ0 : ∀ x, 0 ≤ w x ^ 2 / N := fun x => div_nonneg (sq_nonneg _) hN.le
  have hρ1 : ∫ x, w x ^ 2 / N ∂haar 1 = 1 := by
    rw [integral_div, hNw]; exact div_self hN0
  have hB : ∀ x, w x ^ 2 / N ≤ K ^ 2 / N := fun x => by
    apply div_le_div_of_nonneg_right _ hN.le
    have := hK x
    rw [abs_le] at this
    nlinarith [this.1, this.2]
  obtain ⟨_, hkl⟩ := klDiv_densMeasure_bdd hρm hρ0 hρ1 hB
  rw [hkl]
  have i1 : Integrable (fun x => w x ^ 2 * Real.log (w x ^ 2)) (haar 1) := by
    have := (hw.mul hw.mul_log_sq).integrable
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only; ring
  have i2 : Integrable (fun x => w x ^ 2) (haar 1) := hw.sq.integrable
  have hpt : ∀ x, klFun (w x ^ 2 / N) =
      N⁻¹ * (w x ^ 2 * Real.log (w x ^ 2)) + (-(N⁻¹ * Real.log N) - N⁻¹) * w x ^ 2 + 1 := by
    intro x
    rw [klFun_apply]
    by_cases h0 : w x = 0
    · simp [h0]
    · rw [Real.log_div (pow_ne_zero 2 h0) hN0]
      field_simp
      ring
  simp_rw [hpt]
  have j1 : Integrable (fun x => N⁻¹ * (w x ^ 2 * Real.log (w x ^ 2)) +
      (-(N⁻¹ * Real.log N) - N⁻¹) * w x ^ 2) (haar 1) :=
    (i1.const_mul N⁻¹).add (i2.const_mul (-(N⁻¹ * Real.log N) - N⁻¹))
  rw [integral_add j1 (integrable_const (1 : ℝ)),
    integral_add (i1.const_mul N⁻¹) (i2.const_mul (-(N⁻¹ * Real.log N) - N⁻¹)),
    integral_const_mul, integral_const_mul, hNw]
  simp
  field_simp
  ring_nf

/-! ### The competitor and the first variation -/

/-- The competitor `|u + tφ| / √N(t)` (a unit `L²`-vector). -/
noncomputable def comp (u φ : Torus 1 → ℝ) (t : ℝ) (x : Torus 1) : ℝ :=
  |u x + t * φ x| / Real.sqrt (NN u φ t)

theorem comp_sq {u φ : Torus 1 → ℝ} {t : ℝ} (hN : 0 < NN u φ t) (x : Torus 1) :
    comp u φ t x ^ 2 = (u x + t * φ x) ^ 2 / NN u φ t := by
  unfold comp
  rw [div_pow, sq_abs, Real.sq_sqrt hN.le]

/-- `comp ∈ H¹` and its gradient energy is at most `WW(t)/N(t)`. -/
theorem comp_facts {u φ : Torus 1 → ℝ} (hH : MemH1 (haar 1) u) (hu : BM u) (hφ : IsSmoothT φ)
    {t : ℝ} (hN : 0 < NN u φ t) :
    MemH1 (haar 1) (comp u φ t) ∧
      ∫ x, weakGrad (comp u φ t) x 0 ^ 2 ∂haar 1 ≤ WW u φ t / NN u φ t := by
  obtain ⟨hw, hwg⟩ := memH1_w hH hu hφ t
  have hc : 0 < Real.sqrt (NN u φ t) := Real.sqrt_pos.2 hN
  obtain ⟨hA, hB⟩ := memH1_abs_div hw hc
  have e : comp u φ t = fun x => |u x + t * φ x| / Real.sqrt (NN u φ t) := rfl
  rw [e]
  refine ⟨hA, ?_⟩
  have hφ'b := BM.of_isSmoothT (isSmoothT_dpart hφ 0)
  have hG2 : MemLp (fun x => weakGrad u x 0 + t * dpart_appA φ 0 x) 2 (haar 1) :=
    (memLp_weakGrad_zero hH).add (hφ'b.memLp.const_mul t)
  have hsq : Real.sqrt (NN u φ t) ^ 2 = NN u φ t := Real.sq_sqrt hN.le
  unfold WW
  rw [← integral_div]
  refine integral_mono_ae (memLp_weakGrad_zero hA).integrable_sq (hG2.integrable_sq.div_const _) ?_
  filter_upwards [hB, hwg] with x h1 h2
  rw [hsq, h2] at h1
  exact h1

theorem Sfun_comp_le {r : ℝ} {A u φ : Torus 1 → ℝ}
    (hH : MemH1 (haar 1) u) (hu : BM u) (hφ : IsSmoothT φ) {t : ℝ} (hN : 0 < NN u φ t) :
    Sfun r A (comp u φ t) ≤ Fbar r A u φ t := by
  have hφb := BM.of_isSmoothT hφ
  have hw := BM.w hu hφb t
  have hNw : ∫ x, (u x + t * φ x) ^ 2 ∂haar 1 = NN u φ t := (NN_eq u φ t).symm
  obtain ⟨_, hE⟩ := comp_facts hH hu hφ hN
  have hfun : (fun x => comp u φ t x ^ 2) = fun x => (u x + t * φ x) ^ 2 / NN u φ t :=
    funext (comp_sq hN)
  have hkl : (klDiv (densMeasure (fun x => (u x + t * φ x) ^ 2 / NN u φ t)) (haar 1)).toReal =
      EE u φ t / NN u φ t - Real.log (NN u φ t) := klDiv_toReal_sq hw hN hNw
  have hAint : ∫ x, A x * comp u φ t x ^ 2 ∂haar 1 = MM u φ A t / NN u φ t := by
    simp_rw [comp_sq hN]
    unfold MM
    rw [← integral_div]
    congr 1; funext x; ring
  unfold Sfun Fbar
  rw [hAint, hfun, hkl]
  linarith

theorem Fbar_zero {r : ℝ} {A u φ : Torus 1 → ℝ} (hu : BM u)
    (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1) : Fbar r A u φ 0 = Sfun r A u := by
  have hN0 : NN u φ 0 = 1 := by rw [NN_eq]; simpa using hmass
  have e1 : WW u φ 0 = ∫ x, weakGrad u x 0 ^ 2 ∂haar 1 := by simp [WW]
  have e2 : MM u φ A 0 = ∫ x, A x * u x ^ 2 ∂haar 1 := by simp [MM]
  have e3 : EE u φ 0 = ∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂haar 1 := by simp [EE]
  have hkl : (klDiv (densMeasure (fun x => u x ^ 2)) (haar 1)).toReal =
      ∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂haar 1 := by
    have := klDiv_toReal_sq hu one_pos (by simpa using hmass)
    simpa using this
  unfold Fbar Sfun
  rw [e1, e2, e3, hN0, hkl]
  simp

theorem Fbar_hasDerivAt {r : ℝ} {A u φ : Torus 1 → ℝ} (hA : BM A) (hu : BM u)
    (hφ : IsSmoothT φ) (hH : MemH1 (haar 1) u) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1) :
    HasDerivAt (Fbar r A u φ)
      (8 * (∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1) +
        2 * (∫ x, A x * (u x * φ x) ∂haar 1) -
        4 * r * (∫ x, u x * φ x * Real.log (u x ^ 2) ∂haar 1) -
        2 * (∫ x, u x * φ x ∂haar 1) * Sfun r A u) 0 := by
  have hφb := BM.of_isSmoothT hφ
  have hφ'b := BM.of_isSmoothT (isSmoothT_dpart hφ 0)
  obtain ⟨hN, hN0'⟩ := MM_hasDerivAt (BM.const 1) hu hφb
  obtain ⟨hMA, hMA0⟩ := MM_hasDerivAt hA hu hφb
  obtain ⟨hW, hW0⟩ := WW_hasDerivAt (memLp_weakGrad_zero hH) hφ'b
  obtain ⟨hE, hE0⟩ := EE_hasDerivAt hu hφb
  have hN0 : NN u φ 0 = 1 := by rw [NN_eq]; simpa using hmass
  have hN1 : NN u φ 0 ≠ 0 := by rw [hN0]; exact one_ne_zero
  have hNd : HasDerivAt (NN u φ) (2 * ∫ x, u x * φ x ∂haar 1) 0 := by simpa using hN
  have hkl : (klDiv (densMeasure (fun x => u x ^ 2)) (haar 1)).toReal =
      ∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂haar 1 := by
    have := klDiv_toReal_sq hu one_pos (by simpa using hmass)
    simpa using this
  have hT1 := (hW.div hNd hN1).const_mul 4
  have hT2 := hMA.div hNd hN1
  have hT3 := ((hE.div hNd hN1).sub (hNd.log hN1)).const_mul (2 * r)
  have hF := (hT1.add hT2).sub hT3
  have hfun : Fbar r A u φ = fun y => 4 * (WW u φ y / NN u φ y) + MM u φ A y / NN u φ y -
      2 * r * (EE u φ y / NN u φ y - Real.log (NN u φ y)) := rfl
  rw [hfun]
  refine hF.congr_deriv ?_
  unfold Sfun
  rw [hkl, hN0, hW0, hMA0, hE0]
  ring

theorem Fbar_isLocalMin {r : ℝ} {A u φ : Torus 1 → ℝ} (hu : BM u)
    (hH : MemH1 (haar 1) u) (hφ : IsSmoothT φ) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1)
    (hmin : ∀ g : Torus 1 → ℝ, (∀ x, 0 ≤ g x) → MemH1 (haar 1) g → ∫ x, g x ^ 2 ∂haar 1 = 1 →
      Sfun r A u ≤ Sfun r A g) :
    IsLocalMin (Fbar r A u φ) 0 := by
  have hφb := BM.of_isSmoothT hφ
  obtain ⟨hN, hN0'⟩ := MM_hasDerivAt (BM.const 1) hu hφb
  have hN0 : NN u φ 0 = 1 := by rw [NN_eq]; simpa using hmass
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < NN u φ t :=
    hN.continuousAt.eventually (lt_mem_nhds (by show 0 < NN u φ 0; rw [hN0]; exact one_pos))
  filter_upwards [hev] with t ht
  obtain ⟨hmem, _⟩ := comp_facts hH hu hφ ht
  have hnn : ∀ x, 0 ≤ comp u φ t x := fun x => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hmass_t : ∫ x, comp u φ t x ^ 2 ∂haar 1 = 1 := by
    simp_rw [comp_sq ht]
    rw [integral_div, ← NN_eq]
    exact div_self ht.ne'
  rw [Fbar_zero hu hmass]
  exact (hmin _ hnn hmem hmass_t).trans (Sfun_comp_le hH hu hφ ht)

/-- **Weak Euler--Lagrange equation** for a bounded minimizer `u` of `S_{r,A}`. -/
theorem weak_euler {r : ℝ} {A u : Torus 1 → ℝ} (hA : BM A) (hu : BM u)
    (hH : MemH1 (haar 1) u) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1)
    (hmin : ∀ g : Torus 1 → ℝ, (∀ x, 0 ≤ g x) → MemH1 (haar 1) g → ∫ x, g x ^ 2 ∂haar 1 = 1 →
      Sfun r A u ≤ Sfun r A g)
    {φ : Torus 1 → ℝ} (hφ : IsSmoothT φ) :
    4 * (∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1) +
        (∫ x, A x * (u x * φ x) ∂haar 1) -
        2 * r * (∫ x, u x * φ x * Real.log (u x ^ 2) ∂haar 1) =
      Sfun r A u * ∫ x, u x * φ x ∂haar 1 := by
  have h := (Fbar_isLocalMin hu hH hφ hmass hmin).hasDerivAt_eq_zero
    (Fbar_hasDerivAt hA hu hφ hH hmass)
  linarith

end SharpLSI.FL.Ex.Reg
