import DGPS.Examples.RoughBoundary.NonlinearDissipation

/-!
# Remote Gibbs states fail the absolute domain (RUF034)

For the rough product model (`L > 0`, `ε ≠ 0`) and every nonzero `t ∈ ℝ²`, the Gibbs density
`q_t = exp (t·U - Λ(t))` (`Λ(t) = log ∫ exp (t·U) dm`) satisfies
`exp (-2‖t‖) ≤ q_t ≤ exp (2‖t‖)` and `|Λ(t)| ≤ ‖t‖`.  The chain rule gives
`√q_t = exp ((t·U - Λ)/2) ∈ W^{1,p}` with weak gradient `(1/2) √q_t (t·U')` for every `1 ≤ p < 2`,
but `√q_t ∉ H¹` (also not locally on any nonempty open subset of the line lift), by RUF007 and the
positive lower bound.  If `t = κ M(q_t)` the formal score cancels pointwise, yet `q_t` is not an
absolute-admissible density, and no sequence of absolute-admissible densities with finite scalar
dissipation converges to `q_t` in `L¹` (finite dissipation forces zero feature mean, RUF032, while
the mean is `L¹`-continuous and `M(q_t) = t/κ ≠ 0`).

Design notes (R5):
* a new module is used because `Nonlinear.lean` already holds RUF031;
* hypotheses `0 < L`, `ε ≠ 0`, `t ≠ 0` (needed by RUF007);
* "locally on any nonempty interval" is formalised on the `ℝ`-lift `s ↦ √q_t (pt s)` by
  `LocalH1OnRUF034 J u` (an `L²_loc` weak derivative against `C_c^∞(J)` test functions), for every
  nonempty open `J ⊆ ℝ`, which is stronger than the version with `L²(J)`;
* the self-consistent remote `t_*` is a hypothesis `t = κ M(q_t)` (existence of such `t_*` is not
  part of this packet; "remote" is not required, the conclusions hold for every such nonzero `t`);
* `L¹` convergence is `∫⁻ ‖ρ_n - q_t‖ₑ → 0` in `ℝ≥0∞`, for every drift provider `b`; non-vacuity
  of the provider quantifier is `driftProviderRUF034`;
* RUF027 is not needed in this route.
-/

open MeasureTheory Filter Set
open scoped ENNReal Real ContDiff Topology

namespace DGPS.Examples.RoughBoundary.Nonlinear

open DGPS.Examples.RoughBoundary.Feature DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Spikes (pt measurable_pt integral_haar_eq)

lemma ac_theta_ab_RUF034 (L ε a b : ℝ) : AbsolutelyContinuousOnInterval (theta L ε) a b := by
  have h := (dtheta_ii L ε a b).absolutelyContinuousOnInterval_intervalIntegral (c := a)
    left_mem_uIcc
  have e : theta L ε = fun x => theta L ε a + ∫ s in a..x, dtheta L ε s := by
    funext x
    rw [theta_eq_integral L ε x, theta_eq_integral L ε a]
    have := intervalIntegral.integral_add_adjacent_intervals (dtheta_ii L ε 0 a) (dtheta_ii L ε a x)
    linarith
  rw [e]
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => theta L ε a) a b :=
    (contDiffOn_const (c := theta L ε a) (n := 1) (s := uIcc a b)).absolutelyContinuousOnInterval
  exact hc.add h

lemma ac_Ureal_ab_RUF034 (L ε a b : ℝ) (j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t => Ureal L ε t j) a b := by
  have h := (ac_theta_ab_RUF034 L ε a b).const_mul (2 * π)
  fin_cases j
  · have := Real.lipschitzWith_cos.comp_absolutelyContinuousOnInterval h
    simpa [Function.comp_def] using this
  · have := Real.lipschitzWith_sin.comp_absolutelyContinuousOnInterval h
    simpa [Function.comp_def] using this

lemma ac_gibbsLift_RUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (c a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun s => Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2)) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c / 2) a b :=
    (contDiffOn_const (c := c / 2) (n := 1) (s := uIcc a b)).absolutelyContinuousOnInterval
  have h2 : AbsolutelyContinuousOnInterval (fun s => (inner ℝ t (Ureal L ε s) - c) / 2) a b := by
    have e : (fun s => (inner ℝ t (Ureal L ε s) - c) / 2) =
        fun s => ((t 0 / 2) * Ureal L ε s 0 + (t 1 / 2) * Ureal L ε s 1) - c / 2 := by
      funext s; rw [inner_two]; ring
    rw [e]
    exact (((ac_Ureal_ab_RUF034 L ε a b 0).const_mul _).add
      ((ac_Ureal_ab_RUF034 L ε a b 1).const_mul _)).sub hc
  obtain ⟨K, hK⟩ := (Real.contDiff_exp.contDiffOn (s := Icc (-(‖t‖ + |c|)) (‖t‖ + |c|))).exists_lipschitzOnWith
    one_ne_zero (convex_Icc _ _) isCompact_Icc
  refine hK.comp_absolutelyContinuousOnInterval (g := fun s => (inner ℝ t (Ureal L ε s) - c) / 2)
    (fun s _ => ?_) h2
  have h1 := abs_real_inner_le_norm t (Ureal L ε s)
  rw [norm_Ureal, mul_one] at h1
  have h3 := abs_le.1 h1
  have h4 := neg_abs_le c
  have h5 := le_abs_self c
  have h6 := abs_nonneg c
  have h7 := norm_nonneg t
  constructor <;> linarith [h3.1, h3.2]


lemma ae_hasDerivAt_gibbsLift_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2))
    (c : ℝ) : ∀ᵐ s : ℝ, HasDerivAt (fun s => Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2))
      (1 / 2 * Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2) * inner ℝ t (Uprime L ε (pt s))) s := by
  filter_upwards [ae_hasDerivAt_Ureal_comp hL ε 0, ae_hasDerivAt_Ureal_comp hL ε 1] with s h0 h1
  have h := (((h0.const_mul (t 0 / 2)).add (h1.const_mul (t 1 / 2))).sub_const (c / 2)).exp
  have e : (fun s => Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2)) =
      fun s => Real.exp (((t 0 / 2) * Ureal L ε s 0 + (t 1 / 2) * Ureal L ε s 1) - c / 2) := by
    funext s; rw [inner_two]; congr 1; ring
  rw [e]
  convert h using 1
  rw [inner_two, inner_two]
  simp only [Pi.add_apply]
  have : (t 0 / 2 * Ureal L ε s 0 + t 1 / 2 * Ureal L ε s 1 - c / 2) =
      (t 0 * Ureal L ε s 0 + t 1 * Ureal L ε s 1 - c) / 2 := by ring
  rw [this]
  ring

lemma exists_Ioo_supset_RUF034 {φ : ℝ → ℝ} (hc : HasCompactSupport φ) :
    ∃ a b : ℝ, a < b ∧ tsupport φ ⊆ Ioo a b := by
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨-(|r| + 1), |r| + 1, by linarith [abs_nonneg r], fun x hx => ?_⟩
  have := hr hx
  rw [Real.closedBall_eq_Icc] at this
  simp only [zero_sub, zero_add, mem_Icc] at this
  constructor <;> linarith [le_abs_self r, this.1, this.2]

lemma ibp_gibbsLift_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (c : ℝ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ s, Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2) * deriv φ s =
      -∫ s, (1 / 2 * Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2) *
        inner ℝ t (Uprime L ε (pt s))) * φ s := by
  obtain ⟨a, b, hab, hsub⟩ := exists_Ioo_supset_RUF034 hc
  set F : ℝ → ℝ := fun s => Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2) with hF
  set f : ℝ → ℝ := fun s => 1 / 2 * Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2) *
        inner ℝ t (Uprime L ε (pt s)) with hf
  have hFac := ac_gibbsLift_RUF034 L ε t c a b
  have hψac : AbsolutelyContinuousOnInterval φ a b :=
    ((hφ.of_le (mod_cast le_top)).contDiffOn (s := uIcc a b)).absolutelyContinuousOnInterval
  have key := hFac.integral_mul_deriv_eq_deriv_mul hψac
  have ha : φ a = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hsub h).1.false)
  have hb : φ b = 0 := image_eq_zero_of_notMem_tsupport (fun h => (hsub h).2.false)
  have hae : ∫ x in a..b, deriv F x * φ x = ∫ x in a..b, f x * φ x :=
    intervalIntegral.integral_congr_ae (by
      filter_upwards [ae_hasDerivAt_gibbsLift_RUF034 hL ε t c] with s hs _
      rw [hs.deriv])
  have hz1 : ∀ x ∉ Ioc a b, F x * deriv φ x = 0 := by
    intro x hx
    have : deriv φ x = 0 := by
      by_contra h
      have := hsub (support_deriv_subset (show x ∈ Function.support (deriv φ) from h))
      exact hx ⟨this.1, this.2.le⟩
    rw [this, mul_zero]
  have hz2 : ∀ x ∉ Ioc a b, f x * φ x = 0 := by
    intro x hx
    have : φ x = 0 := by
      by_contra h
      have := hsub (subset_tsupport _ (show x ∈ Function.support φ from h))
      exact hx ⟨this.1, this.2.le⟩
    rw [this, mul_zero]
  have e1 : ∫ s, F s * deriv φ s = ∫ x in a..b, F x * deriv φ x := by
    rw [intervalIntegral.integral_of_le hab.le, setIntegral_eq_integral_of_forall_compl_eq_zero hz1]
  have e2 : ∫ s, f s * φ s = ∫ x in a..b, f x * φ x := by
    rw [intervalIntegral.integral_of_le hab.le, setIntegral_eq_integral_of_forall_compl_eq_zero hz2]
  rw [e1, e2, key, hae, ha, hb]
  ring


/-- Local `H¹` membership on an open set `J ⊆ ℝ`: a weak derivative `g`, square integrable on every
compact subset of `J`, tested against all smooth compactly supported `φ` with `tsupport φ ⊆ J`. -/
def LocalH1OnRUF034 (J : Set ℝ) (u : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, (∀ K : Set ℝ, IsCompact K → K ⊆ J → MemLp g 2 (volume.restrict K)) ∧
    ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ J →
      ∫ s, u s * deriv φ s = -∫ s, g s * φ s

lemma exists_Icc_subset_RUF034 {J : Set ℝ} (hJ : IsOpen J) {x : ℝ} (hx : x ∈ J) :
    ∃ r : ℝ, 0 < r ∧ Icc (x - r) (x + r) ⊆ J := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hJ x hx
  refine ⟨r / 2, by linarith, fun y hy => hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

lemma locallyIntegrableOn_of_local_RUF034 {J : Set ℝ} (hJ : IsOpen J) {g : ℝ → ℝ}
    (hK : ∀ K : Set ℝ, IsCompact K → K ⊆ J → MemLp g 2 (volume.restrict K)) :
    LocallyIntegrableOn g J volume := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ := exists_Icc_subset_RUF034 hJ hx
  refine ⟨Icc (x - r) (x + r), ?_, ?_⟩
  · rw [hJ.nhdsWithin_eq hx]
    exact Icc_mem_nhds (by linarith) (by linarith)
  · have h := hK _ isCompact_Icc hsub
    have : IsFiniteMeasure (volume.restrict (Icc (x - r) (x + r))) := ⟨by simp⟩
    exact h.integrable one_le_two


lemma integrable_mul_test_RUF034 {J : Set ℝ} {g : ℝ → ℝ}
    (hK : ∀ K : Set ℝ, IsCompact K → K ⊆ J → MemLp g 2 (volume.restrict K))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ J) :
    Integrable (fun s => g s * φ s) := by
  have h := hK _ hc hs
  have : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hc.measure_lt_top⟩
  have hint : Integrable g (volume.restrict (tsupport φ)) := h.integrable one_le_two
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hc
  have h2 : Integrable (fun s => g s * φ s) (volume.restrict (tsupport φ)) := by
    refine Integrable.mono' (hint.norm.mul_const C) (hint.aestronglyMeasurable.mul
      hφ.continuous.aestronglyMeasurable) (Eventually.of_forall fun s => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _)
  refine (integrableOn_iff_integrable_of_support_subset (s := tsupport φ) ?_).1 h2
  intro x hx
  exact subset_tsupport _ (fun h0 => hx (by simp [h0]))

lemma locallyIntegrable_gibbsDeriv_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (t : EuclideanSpace ℝ (Fin 2)) (c : ℝ) :
    LocallyIntegrable (fun s => 1 / 2 * Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2) *
      inner ℝ t (Uprime L ε (pt s))) volume := by
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  have hFac := ac_gibbsLift_RUF034 L ε t c (x - 1) (x + 1)
  have hI := hFac.intervalIntegrable_deriv
  rw [intervalIntegrable_iff] at hI ⊢
  refine hI.congr ?_
  refine (ae_restrict_iff' (measurableSet_uIoc (a := x - 1) (b := x + 1))).2 ?_
  filter_upwards [ae_hasDerivAt_gibbsLift_RUF034 hL ε t c] with s hs _
  rw [hs.deriv]

lemma ae_eq_of_weak_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (c : ℝ)
    {J : Set ℝ} (hJ : IsOpen J) {g : ℝ → ℝ}
    (hK : ∀ K : Set ℝ, IsCompact K → K ⊆ J → MemLp g 2 (volume.restrict K))
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ J →
      ∫ s, Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2) * deriv φ s = -∫ s, g s * φ s) :
    ∀ᵐ s, s ∈ J → g s = 1 / 2 * Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2) *
      inner ℝ t (Uprime L ε (pt s)) := by
  set f : ℝ → ℝ := fun s => 1 / 2 * Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2) *
      inner ℝ t (Uprime L ε (pt s)) with hf
  have hfl := locallyIntegrable_gibbsDeriv_RUF034 hL ε t c
  have hgl := locallyIntegrableOn_of_local_RUF034 hJ hK
  have hloc : LocallyIntegrableOn (fun s => g s - f s) J volume :=
    hgl.sub (hfl.locallyIntegrableOn J)
  have := hJ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun φ hφ hc hs => by
    have h1 := integrable_mul_test_RUF034 hK hφ hc hs
    have h2 : Integrable (fun s => f s * φ s) := by
      have := hfl.integrable_smul_left_of_hasCompactSupport hφ.continuous hc
      have e2 : (fun s => f s * φ s) = fun s => φ s • f s := by
        funext s; simp only [smul_eq_mul]; ring
      rw [e2]; exact this
    have e : (fun s => φ s • (g s - f s)) = fun s => g s * φ s - f s * φ s := by
      funext s; simp only [smul_eq_mul]; ring
    have hw := hweak φ hφ hc hs
    have hib := ibp_gibbsLift_RUF034 hL ε t c hφ hc
    rw [e, integral_sub h1 h2]
    have hib' : ∫ s, Real.exp ((inner ℝ t (Ureal L ε s) - c) / 2) * deriv φ s =
        -∫ s, f s * φ s := hib
    linarith)
  filter_upwards [this] with s hs hsJ
  exact sub_eq_zero.1 (hs hsJ)

/-- The log-partition function `Λ(t) = log ∫ e^{t·U} dm`. -/
noncomputable def gibbsLogPartitionRUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Real.log (∫ x, Real.exp (inner ℝ t (Ufeat L ε x)) ∂haar 1)

/-- The Gibbs density `q_t = exp (t·U - Λ(t))` (with respect to Haar measure). -/
noncomputable def gibbsDensityRUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) : ℝ :=
  Real.exp (inner ℝ t (Ufeat L ε x) - gibbsLogPartitionRUF034 L ε t)

/-- The square root `√q_t`. -/
noncomputable def gibbsSqrtRUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) : ℝ :=
  Real.sqrt (gibbsDensityRUF034 L ε t x)

/-- The formal derivative field `(1/2) √q_t (t·U')`. -/
noncomputable def gibbsSqrtGradRUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    Torus 1 → Tangent 1 :=
  fun x => !₂[1 / 2 * gibbsSqrtRUF034 L ε t x * inner ℝ t (Uprime L ε x)]

/-- The feature mean `M(q_t) = ∫ q_t U dm`. -/
noncomputable def gibbsMeanRUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  ∫ x, gibbsDensityRUF034 L ε t x • Ufeat L ε x ∂haar 1

lemma abs_inner_Ufeat_le_RUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) :
    |inner ℝ t (Ufeat L ε x)| ≤ ‖t‖ := by
  have := abs_real_inner_le_norm t (Ufeat L ε x)
  rwa [norm_Ufeat, mul_one] at this

lemma continuous_expInner_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    Continuous fun x => Real.exp (inner ℝ t (Ufeat L ε x)) :=
  Real.continuous_exp.comp (continuous_const.inner (continuous_Ufeat hL ε))

lemma partition_bounds_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    Real.exp (-‖t‖) ≤ ∫ x, Real.exp (inner ℝ t (Ufeat L ε x)) ∂haar 1 ∧
      ∫ x, Real.exp (inner ℝ t (Ufeat L ε x)) ∂haar 1 ≤ Real.exp ‖t‖ := by
  have hint : Integrable (fun x => Real.exp (inner ℝ t (Ufeat L ε x))) (haar 1) :=
    (continuous_expInner_RUF034 hL ε t).integrable_of_hasCompactSupport (by
      exact HasCompactSupport.of_compactSpace _) |>.mono_measure le_rfl
  constructor
  · calc Real.exp (-‖t‖) = ∫ _x, Real.exp (-‖t‖) ∂haar 1 := by simp
      _ ≤ _ := integral_mono (integrable_const _) hint (fun x => Real.exp_le_exp.2
          (by linarith [(abs_le.1 (abs_inner_Ufeat_le_RUF034 L ε t x)).1]))
  · calc _ ≤ ∫ _x, Real.exp ‖t‖ ∂haar 1 := integral_mono hint (integrable_const _)
          (fun x => Real.exp_le_exp.2
            (by linarith [(abs_le.1 (abs_inner_Ufeat_le_RUF034 L ε t x)).2]))
      _ = Real.exp ‖t‖ := by simp

lemma partition_pos_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    0 < ∫ x, Real.exp (inner ℝ t (Ufeat L ε x)) ∂haar 1 :=
  lt_of_lt_of_le (Real.exp_pos _) (partition_bounds_RUF034 hL ε t).1

lemma abs_logPartition_le_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    |gibbsLogPartitionRUF034 L ε t| ≤ ‖t‖ := by
  obtain ⟨h1, h2⟩ := partition_bounds_RUF034 hL ε t
  have hpos := partition_pos_RUF034 hL ε t
  unfold gibbsLogPartitionRUF034
  rw [abs_le]
  constructor
  · have := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at this; linarith
  · have := Real.log_le_log hpos h2
    rw [Real.log_exp] at this; linarith

lemma gibbsDensity_bounds_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2))
    (x : Torus 1) :
    Real.exp (-(2 * ‖t‖)) ≤ gibbsDensityRUF034 L ε t x ∧
      gibbsDensityRUF034 L ε t x ≤ Real.exp (2 * ‖t‖) := by
  have h1 := abs_le.1 (abs_inner_Ufeat_le_RUF034 L ε t x)
  have h2 := abs_le.1 (abs_logPartition_le_RUF034 hL ε t)
  unfold gibbsDensityRUF034
  exact ⟨Real.exp_le_exp.2 (by linarith), Real.exp_le_exp.2 (by linarith)⟩

lemma gibbsDensity_pos_RUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) :
    0 < gibbsDensityRUF034 L ε t x := Real.exp_pos _

lemma gibbsSqrt_eq_RUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) :
    gibbsSqrtRUF034 L ε t x =
      Real.exp ((inner ℝ t (Ufeat L ε x) - gibbsLogPartitionRUF034 L ε t) / 2) := by
  unfold gibbsSqrtRUF034 gibbsDensityRUF034
  exact (Real.exp_half _).symm

lemma gibbsSqrt_sq_RUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) :
    gibbsSqrtRUF034 L ε t x ^ 2 = gibbsDensityRUF034 L ε t x := by
  unfold gibbsSqrtRUF034
  exact Real.sq_sqrt (gibbsDensity_pos_RUF034 L ε t x).le

lemma gibbsSqrt_pos_RUF034 (L ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) (x : Torus 1) :
    0 < gibbsSqrtRUF034 L ε t x := by
  rw [gibbsSqrt_eq_RUF034]; exact Real.exp_pos _

lemma continuous_gibbsSqrt_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    Continuous (gibbsSqrtRUF034 L ε t) := by
  have : gibbsSqrtRUF034 L ε t = fun x => Real.exp ((inner ℝ t (Ufeat L ε x) -
      gibbsLogPartitionRUF034 L ε t) / 2) := funext (gibbsSqrt_eq_RUF034 L ε t)
  rw [this]
  exact Real.continuous_exp.comp (((continuous_const.inner (continuous_Ufeat hL ε)).sub
    continuous_const).div_const 2)

lemma gibbsSqrt_le_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2))
    (x : Torus 1) : gibbsSqrtRUF034 L ε t x ≤ Real.exp ‖t‖ := by
  rw [gibbsSqrt_eq_RUF034]
  have h1 := abs_le.1 (abs_inner_Ufeat_le_RUF034 L ε t x)
  have h2 := abs_le.1 (abs_logPartition_le_RUF034 hL ε t)
  exact Real.exp_le_exp.2 (by linarith)

lemma integral_gibbsDensity_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    ∫ x, gibbsDensityRUF034 L ε t x ∂haar 1 = 1 := by
  have hpos := partition_pos_RUF034 hL ε t
  have e : ∀ x, gibbsDensityRUF034 L ε t x = Real.exp (inner ℝ t (Ufeat L ε x)) *
      (∫ y, Real.exp (inner ℝ t (Ufeat L ε y)) ∂haar 1)⁻¹ := by
    intro x
    unfold gibbsDensityRUF034 gibbsLogPartitionRUF034
    rw [Real.exp_sub, Real.exp_log hpos, div_eq_mul_inv]
  simp_rw [e]
  rw [integral_mul_const]
  exact mul_inv_cancel₀ hpos.ne'

lemma integral_gibbsSqrt_sq_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (t : EuclideanSpace ℝ (Fin 2)) :
    ∫ x, gibbsSqrtRUF034 L ε t x ^ 2 ∂haar 1 = 1 := by
  simp_rw [gibbsSqrt_sq_RUF034]
  exact integral_gibbsDensity_RUF034 hL ε t

lemma measurable_gibbsSqrtGrad0_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (t : EuclideanSpace ℝ (Fin 2)) :
    Measurable fun y => 1 / 2 * gibbsSqrtRUF034 L ε t y * inner ℝ t (Uprime L ε y) :=
  (measurable_const.mul (continuous_gibbsSqrt_RUF034 hL ε t).measurable).mul
    (measurable_const.inner (measurable_Uprime_vec hL ε))

lemma measurable_gibbsSqrtGrad_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (t : EuclideanSpace ℝ (Fin 2)) : Measurable (gibbsSqrtGradRUF034 L ε t) := by
  unfold gibbsSqrtGradRUF034
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable.comp
    (measurable_pi_iff.2 fun i => by fin_cases i; simpa using measurable_gibbsSqrtGrad0_RUF034 hL ε t)

lemma isWeakGradientLp_gibbsSqrt_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (t : EuclideanSpace ℝ (Fin 2)) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    IsWeakGradientLp (ENNReal.ofReal p) (gibbsSqrtRUF034 L ε t) (gibbsSqrtGradRUF034 L ε t) := by
  set Λ := gibbsLogPartitionRUF034 L ε t with hΛ
  have hSc := continuous_gibbsSqrt_RUF034 hL ε t
  refine ⟨?_, ?_, ?_⟩
  · refine MemLp.of_bound hSc.aestronglyMeasurable (Real.exp ‖t‖)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (gibbsSqrt_pos_RUF034 L ε t y)]
    exact gibbsSqrt_le_RUF034 hL ε t y
  · set C : ℝ := Real.exp ‖t‖ * ‖t‖ * (2 * π) with hC
    refine MemLp.mono ((memLp_dthetaT hL ε hp hp2).const_mul C)
      (measurable_gibbsSqrtGrad_RUF034 hL ε t).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    have h1 : ‖gibbsSqrtGradRUF034 L ε t y‖ =
        |1 / 2 * gibbsSqrtRUF034 L ε t y * inner ℝ t (Uprime L ε y)| := by
      simp [gibbsSqrtGradRUF034, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
    rw [h1, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have hS : |gibbsSqrtRUF034 L ε t y| ≤ Real.exp ‖t‖ := by
      rw [abs_of_pos (gibbsSqrt_pos_RUF034 L ε t y)]; exact gibbsSqrt_le_RUF034 hL ε t y
    have hI : |inner ℝ t (Uprime L ε y)| ≤ ‖t‖ * (2 * π * |dthetaT L ε y|) := by
      have := abs_real_inner_le_norm t (Uprime L ε y)
      rwa [norm_Uprime] at this
    have hπ : |C| = C := abs_of_nonneg (by positivity)
    have h0 : (0 : ℝ) ≤ |dthetaT L ε y| := abs_nonneg _
    have hSn : 0 ≤ |gibbsSqrtRUF034 L ε t y| := abs_nonneg _
    rw [hπ]
    have : |1 / 2| * |gibbsSqrtRUF034 L ε t y| * |inner ℝ t (Uprime L ε y)| ≤
        1 / 2 * Real.exp ‖t‖ * (‖t‖ * (2 * π * |dthetaT L ε y|)) := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hS (by norm_num)) hI (abs_nonneg _)
        (by positivity)
    refine this.trans ?_
    have hk : 0 ≤ Real.exp ‖t‖ * ‖t‖ * (2 * π * |dthetaT L ε y|) := by positivity
    have : C * |dthetaT L ε y| = Real.exp ‖t‖ * ‖t‖ * (2 * π * |dthetaT L ε y|) := by
      rw [hC]; ring
    rw [this]; nlinarith
  · intro φ hφ j'
    have hj : j' = 0 := Subsingleton.elim _ _
    subst hj
    have hU : ∀ s, gibbsSqrtRUF034 L ε t (pt s) =
        Real.exp ((inner ℝ t (Ureal L ε s) - Λ) / 2) := fun s => by
      rw [gibbsSqrt_eq_RUF034, Ufeat_pt hL]
    have := weak_ibp_of_ac (F := fun s => Real.exp ((inner ℝ t (Ureal L ε s) - Λ) / 2))
      (f := fun s => 1 / 2 * Real.exp ((inner ℝ t (Ureal L ε s) - Λ) / 2) *
        inner ℝ t (Uprime L ε (pt s)))
      (fun x => by
        show Real.exp ((inner ℝ t (Ureal L ε (x + 1)) - Λ) / 2) =
          Real.exp ((inner ℝ t (Ureal L ε x) - Λ) / 2)
        rw [Ureal_periodic hL ε x])
      (ac_gibbsLift_RUF034 L ε t Λ 0 1) (ae_hasDerivAt_gibbsLift_RUF034 hL ε t Λ)
      (U := gibbsSqrtRUF034 L ε t) (c := fun y => gibbsSqrtGradRUF034 L ε t y 0) hU
      (fun s => by simp only [gibbsSqrtGradRUF034, hU]; simp)
      hSc.aestronglyMeasurable
      (by simpa [gibbsSqrtGradRUF034] using
        (measurable_gibbsSqrtGrad0_RUF034 hL ε t).aestronglyMeasurable) hφ
    exact this

lemma not_memH1_gibbsSqrt_RUF034 {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    {t : EuclideanSpace ℝ (Fin 2)} (ht : t ≠ 0) {u : Torus 1 → ℝ}
    (hu : u =ᵐ[haar 1] gibbsSqrtRUF034 L ε t) : ¬ MemH1 u := by
  rintro ⟨g, hg⟩
  have hg' : IsWeakGradient (gibbsSqrtRUF034 L ε t) g :=
    hg.congr_ae hu (Filter.EventuallyEq.refl _ _)
  have h1 := isWeakGradientLp_gibbsSqrt_RUF034 hL ε t le_rfl one_lt_two
  rw [ENNReal.ofReal_one] at h1
  have hae := (isWeakGradientLp_one_of hg').ae_eq_of_one h1
  have hg0 : MemLp (fun x => g x 0) 2 (haar 1) := memLp_coord_of_memLp hg'.memLp_grad 0
  refine false_of_finite_weighted_directional hL hε (continuous_gibbsSqrt_RUF034 hL ε t)
    (integral_gibbsSqrt_sq_RUF034 hL ε t) ht ?_
  have hlt := lintegral_lt_top_of_memLp_two (hg0.const_mul 2)
  refine lt_of_le_of_lt (le_of_eq ?_) hlt
  refine lintegral_congr_ae (hae.mono fun x hx => ?_)
  have h0 : g x 0 = 1 / 2 * gibbsSqrtRUF034 L ε t x * inner ℝ t (Uprime L ε x) := by
    rw [hx]; rfl
  have e : gibbsSqrtRUF034 L ε t x * inner ℝ t (Uprime L ε x) = 2 * g x 0 := by
    rw [h0]; ring
  simp only [e]

lemma not_absolute_gibbs_RUF034 {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    {t : EuclideanSpace ℝ (Fin 2)} (ht : t ≠ 0) :
    ¬ ∃ ρ : AbsoluteDensity 1, ρ.density =ᵐ[haar 1] gibbsDensityRUF034 L ε t := by
  rintro ⟨ρ, hρ⟩
  refine not_memH1_gibbsSqrt_RUF034 hL hε ht (u := ρ.sqrt) ?_ ρ.sqrt_mem
  filter_upwards [hρ, ρ.sqrt_nonneg] with x hx h0
  have : ρ.sqrt x = Real.sqrt (ρ.density x) := (Real.sqrt_sq h0).symm
  rw [this, hx]
  rfl

lemma not_localH1_gibbsSqrt_RUF034 {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    {t : EuclideanSpace ℝ (Fin 2)} (ht : t ≠ 0) {J : Set ℝ} (hJ : IsOpen J) (hne : J.Nonempty) :
    ¬ LocalH1OnRUF034 J (fun s => gibbsSqrtRUF034 L ε t (pt s)) := by
  rintro ⟨g, hK, hweak⟩
  set Λ := gibbsLogPartitionRUF034 L ε t with hΛ
  have hU : ∀ s, gibbsSqrtRUF034 L ε t (pt s) =
      Real.exp ((inner ℝ t (Ureal L ε s) - Λ) / 2) := fun s => by
    rw [gibbsSqrt_eq_RUF034, Ufeat_pt hL]
  have hae := ae_eq_of_weak_RUF034 hL ε t Λ hJ hK (fun φ hφ hc hs => by
    have := hweak φ hφ hc hs
    simpa only [hU] using this)
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨r, hr, hsub⟩ := exists_Icc_subset_RUF034 hJ hx0
  have hgK : MemLp g 2 (volume.restrict (Icc (x0 - r) (x0 + r))) := hK _ isCompact_Icc hsub
  have hJ' : Ioo (x0 - r) (x0 + r) ⊆ J := Ioo_subset_Icc_self.trans hsub
  have hgJ' : MemLp g 2 (volume.restrict (Ioo (x0 - r) (x0 + r))) :=
    hgK.mono_measure (Measure.restrict_mono Ioo_subset_Icc_self le_rfl)
  have hfJ' : ∀ᵐ s ∂(volume.restrict (Ioo (x0 - r) (x0 + r))), g s =
      1 / 2 * Real.exp ((inner ℝ t (Ureal L ε s) - Λ) / 2) * inner ℝ t (Uprime L ε (pt s)) := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    filter_upwards [hae] with s hs hsJ using hs (hJ' hsJ)
  have hfmem := hgJ'.ae_eq hfJ'
  refine (every_nonzero_direction_is_rough hL hε (isOpen_Ioo (a := x0 - r) (b := x0 + r))
    ⟨x0, by constructor <;> linarith⟩ ht).2.2 ?_
  have hh : (fun x => inner ℝ t ((2 * π * dtheta L ε x) • Jrot (Ureal L ε x))) =
      fun s => inner ℝ t (Uprime L ε (pt s)) := funext fun s => by rw [Uprime_pt hL]
  rw [hh]
  refine hfmem.of_le_mul (c := 2 * Real.exp ‖t‖) ?_ (ae_of_all _ fun s => ?_)
  · exact ((measurable_const.inner (measurable_Uprime_vec hL ε)).comp
      measurable_pt).aestronglyMeasurable
  · have h1 := abs_le.1 (abs_inner_Ufeat_le_RUF034 L ε t (pt s))
    rw [Ufeat_pt hL] at h1
    have h2 := abs_le.1 (abs_logPartition_le_RUF034 hL ε t)
    have hFge : 1 ≤ Real.exp ‖t‖ * Real.exp ((inner ℝ t (Ureal L ε s) - Λ) / 2) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have hFpos := Real.exp_pos ((inner ℝ t (Ureal L ε s) - Λ) / 2)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have e : 2 * Real.exp ‖t‖ * |1 / 2 * Real.exp ((inner ℝ t (Ureal L ε s) - Λ) / 2) *
        inner ℝ t (Uprime L ε (pt s))| =
        (Real.exp ‖t‖ * Real.exp ((inner ℝ t (Ureal L ε s) - Λ) / 2)) *
          |inner ℝ t (Uprime L ε (pt s))| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos hFpos]
      ring
    rw [e]
    exact le_mul_of_one_le_left (abs_nonneg _) hFge

lemma measurable_forceVec_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) (M : EuclideanSpace ℝ (Fin 2)) :
    Measurable (forceVec L ε M) := by
  unfold forceVec
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable.comp
    (measurable_pi_iff.2 fun i => ?_)
  fin_cases i
  exact ((measurable_const.inner (measurable_Uprime_vec hL ε)).const_mul _).neg

/-- The explicit force `-κ (M·U')` is an absolute-domain drift provider. -/
noncomputable def driftProviderRUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ) :
    AbsoluteDrift (modelData hL ε) where
  force ρ := forceVec L ε (featureMean L ε ρ)
  measurable_force ρ := measurable_forceVec_RUF034 hL ε _
  weak_gradient ρ := by
    have h := isWeakGradientLp_potential hL ε ρ (p := 1) le_rfl one_lt_two
    rwa [ENNReal.ofReal_one] at h

lemma continuous_gibbsDensity_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (t : EuclideanSpace ℝ (Fin 2)) : Continuous (gibbsDensityRUF034 L ε t) := by
  have : gibbsDensityRUF034 L ε t = fun x => gibbsSqrtRUF034 L ε t x ^ 2 :=
    funext fun x => (gibbsSqrt_sq_RUF034 L ε t x).symm
  rw [this]
  exact (continuous_gibbsSqrt_RUF034 hL ε t).pow 2

lemma integrable_gibbsDensity_smul_RUF034 {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (t : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun x => gibbsDensityRUF034 L ε t x • Ufeat L ε x) (haar 1) :=
  ((continuous_gibbsDensity_RUF034 hL ε t).smul (continuous_Ufeat hL ε)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma gibbsMean_ne_zero_RUF034 (L ε : ℝ) {t : EuclideanSpace ℝ (Fin 2)} (ht : t ≠ 0)
    (hstar : t = kappa • gibbsMeanRUF034 L ε t) : gibbsMeanRUF034 L ε t ≠ 0 := by
  intro h0
  apply ht
  rw [hstar, h0, smul_zero]

lemma score_cancel_RUF034 (L ε : ℝ) {t : EuclideanSpace ℝ (Fin 2)}
    (hstar : t = kappa • gibbsMeanRUF034 L ε t) (x : Torus 1) :
    2 * gibbsSqrtGradRUF034 L ε t x 0 - kappa * gibbsSqrtRUF034 L ε t x *
      inner ℝ (gibbsMeanRUF034 L ε t) (Uprime L ε x) = 0 := by
  have h : inner ℝ t (Uprime L ε x) = kappa * inner ℝ (gibbsMeanRUF034 L ε t) (Uprime L ε x) := by
    conv_lhs => rw [hstar]
    rw [real_inner_smul_left]
  simp only [gibbsSqrtGradRUF034]
  simp only [Matrix.cons_val_zero]
  rw [h]; ring

lemma no_L1_approx_RUF034 {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    {t : EuclideanSpace ℝ (Fin 2)} (ht : t ≠ 0) (hstar : t = kappa • gibbsMeanRUF034 L ε t)
    (b : AbsoluteDrift (modelData hL ε)) (ρ : ℕ → AbsoluteDensity 1)
    (hfin : ∀ n, scalarDissipation (modelData hL ε) b (ρ n) < ⊤) :
    ¬ Tendsto (fun n => ∫⁻ x, ‖(ρ n).density x - gibbsDensityRUF034 L ε t x‖ₑ ∂haar 1)
      atTop (𝓝 0) := by
  intro hconv
  have hM0 : ∀ n, ‖gibbsMeanRUF034 L ε t‖ₑ ≤
      ∫⁻ x, ‖(ρ n).density x - gibbsDensityRUF034 L ε t x‖ₑ ∂haar 1 := fun n => by
    have h0 := featureMean_eq_zero_of_finite hL hε b (ρ n) (hfin n)
    have hq := integrable_gibbsDensity_smul_RUF034 hL ε t
    have hr := integrable_density_smul_Ufeat hL ε (ρ n)
    have e : gibbsMeanRUF034 L ε t =
        ∫ x, (gibbsDensityRUF034 L ε t x - (ρ n).density x) • Ufeat L ε x ∂haar 1 := by
      simp_rw [sub_smul]
      rw [integral_sub hq hr]
      unfold featureMean at h0
      rw [h0, sub_zero]
      rfl
    rw [e]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun x => ?_
    have hU : ‖Ufeat L ε x‖ₑ = 1 := by
      rw [← ofReal_norm, norm_Ufeat]; simp
    rw [enorm_smul, hU, mul_one, enorm_sub_rev]
  have hle := ge_of_tendsto' hconv hM0
  have hz : gibbsMeanRUF034 L ε t = 0 := by
    have := nonpos_iff_eq_zero.1 hle
    exact enorm_eq_zero.1 this
  exact gibbsMean_ne_zero_RUF034 L ε ht hstar hz

/-- **Remote Gibbs states fail the absolute domain** (RUF034). -/
theorem remote_gibbs_states_fail_the_absolute_domain {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    {t : EuclideanSpace ℝ (Fin 2)} (ht : t ≠ 0) :
    (|gibbsLogPartitionRUF034 L ε t| ≤ ‖t‖ ∧
      (∀ x, Real.exp (-(2 * ‖t‖)) ≤ gibbsDensityRUF034 L ε t x ∧
        gibbsDensityRUF034 L ε t x ≤ Real.exp (2 * ‖t‖)) ∧
      ∫ x, gibbsDensityRUF034 L ε t x ∂haar 1 = 1) ∧
    (∀ p : ℝ, 1 ≤ p → p < 2 →
      IsWeakGradientLp (ENNReal.ofReal p) (gibbsSqrtRUF034 L ε t) (gibbsSqrtGradRUF034 L ε t)) ∧
    (∀ J : Set ℝ, IsOpen J → J.Nonempty →
      ¬ LocalH1OnRUF034 J (fun s => gibbsSqrtRUF034 L ε t (pt s))) ∧
    (¬ MemH1 (gibbsSqrtRUF034 L ε t) ∧
      ¬ ∃ ρ : AbsoluteDensity 1, ρ.density =ᵐ[haar 1] gibbsDensityRUF034 L ε t) ∧
    (t = kappa • gibbsMeanRUF034 L ε t →
      (∀ x, 2 * gibbsSqrtGradRUF034 L ε t x 0 - kappa * gibbsSqrtRUF034 L ε t x *
        inner ℝ (gibbsMeanRUF034 L ε t) (Uprime L ε x) = 0) ∧
      gibbsMeanRUF034 L ε t ≠ 0 ∧
      ∀ (b : AbsoluteDrift (modelData hL ε)) (ρ : ℕ → AbsoluteDensity 1),
        (∀ n, scalarDissipation (modelData hL ε) b (ρ n) < ⊤) →
        ¬ Tendsto (fun n => ∫⁻ x, ‖(ρ n).density x - gibbsDensityRUF034 L ε t x‖ₑ ∂haar 1)
          atTop (𝓝 0)) ∧
    Nonempty (AbsoluteDrift (modelData hL ε)) :=
  ⟨⟨abs_logPartition_le_RUF034 hL ε t, gibbsDensity_bounds_RUF034 hL ε t,
      integral_gibbsDensity_RUF034 hL ε t⟩,
    fun _ hp hp2 => isWeakGradientLp_gibbsSqrt_RUF034 hL ε t hp hp2,
    fun _ hJ hne => not_localH1_gibbsSqrt_RUF034 hL hε ht hJ hne,
    ⟨not_memH1_gibbsSqrt_RUF034 hL hε ht (Filter.EventuallyEq.refl _ _),
      not_absolute_gibbs_RUF034 hL hε ht⟩,
    fun hstar => ⟨score_cancel_RUF034 L ε hstar, gibbsMean_ne_zero_RUF034 L ε ht hstar,
      fun b ρ hfin => no_L1_approx_RUF034 hL hε ht hstar b ρ hfin⟩,
    ⟨driftProviderRUF034 hL ε⟩⟩

end DGPS.Examples.RoughBoundary.Nonlinear

