import DGPS.FiniteN.Tools.StrongConvexityLSI
import Mathlib

/-!
# Extension of `HasLSIRate` to bounded `C¹` functions with bounded gradient (FIN015b)

If a probability measure `μ` on `ℝ^k` satisfies `HasLSIRate μ lam`, then
`Ent_μ(f²) ≤ (2/lam) ∫ |∇f|² dμ` for every `C¹` function `f` with bounded values and bounded
gradient.  The proof cuts `f` off (`cutFn`), mollifies with a normalized `ContDiffBump`
(`mollFn`), applies the inequality to the resulting test functions and passes to the limit:
the gradient side by dominated convergence, the entropy side by continuity of the
homogeneous entropy under uniformly bounded pointwise convergence
(`tendsto_homogeneousEntropy`).  The result holds for every probability measure and needs no
positivity of `lam`.
-/

open MeasureTheory Filter Topology Metric Set Function
open scoped ENNReal ContDiff Convolution

namespace DGPS.FiniteN.Tools.LSIExtension

variable {k : ℕ}

/-- Convolution against a nonnegative probability density preserves sup-bounds. -/
theorem norm_convolution_le_of_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : EuclideanSpace ℝ (Fin k) → ℝ} {g : EuclideanSpace ℝ (Fin k) → F}
    (hφ0 : ∀ x, 0 ≤ φ x) (hφ1 : ∫ x, φ x = 1) {B : ℝ} (hg : ∀ x, ‖g x‖ ≤ B)
    (x : EuclideanSpace ℝ (Fin k)) :
    ‖(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ B := by
  have hi : Integrable φ := integrable_of_integral_eq_one hφ1
  rw [convolution_def]
  calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (φ t) (g (x - t))‖
      ≤ ∫ t, φ t * B := by
        refine norm_integral_le_of_norm_le (hi.mul_const B) (Eventually.of_forall fun t => ?_)
        simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_of_nonneg (hφ0 t)]
        exact mul_le_mul_of_nonneg_left (hg _) (hφ0 t)
    _ = B := by rw [integral_mul_const, hφ1, one_mul]


/-- The fixed cutoff bump: equal to `1` on the unit ball, supported in the ball of radius `2`. -/
noncomputable def cutBump : ContDiffBump (0 : EuclideanSpace ℝ (Fin k)) :=
  ⟨1, 2, one_pos, one_lt_two⟩

/-- The `n`-th dilated cutoff. -/
noncomputable def cut (n : ℕ) (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  cutBump (((n : ℝ) + 1)⁻¹ • x)

theorem cut_contDiff (n : ℕ) : ContDiff ℝ ∞ (cut (k := k) n) :=
  cutBump.contDiff.comp (contDiff_const_smul _)

theorem cut_compactSupport (n : ℕ) : HasCompactSupport (cut (k := k) n) :=
  cutBump.hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (((n : ℝ) + 1)⁻¹) (by positivity))

theorem cut_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin k)) : 0 ≤ cut n x := cutBump.nonneg

theorem cut_le_one (n : ℕ) (x : EuclideanSpace ℝ (Fin k)) : cut n x ≤ 1 := cutBump.le_one

theorem cut_eq_one {n : ℕ} {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ ≤ (n : ℝ) + 1) :
    cut n x = 1 := by
  apply cutBump.one_of_mem_closedBall
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  show ‖(((n : ℝ) + 1)⁻¹ • x) - 0‖ ≤ 1
  rw [sub_zero, norm_smul, norm_inv, Real.norm_of_nonneg hn.le]
  have : ((n : ℝ) + 1)⁻¹ * ‖x‖ ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hn.le)
  rwa [inv_mul_cancel₀ hn.ne'] at this

theorem exists_cut_fderiv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin k)), ‖fderiv ℝ (cut n) x‖ ≤ C := by
  have hc : Continuous (fderiv ℝ (cutBump : EuclideanSpace ℝ (Fin k) → ℝ)) :=
    (cutBump.contDiff (n := 1)).continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (cutBump.hasCompactSupport.fderiv ℝ)
  refine ⟨max C 0, le_max_right _ _, fun n x => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin k) => (((n : ℝ) + 1)⁻¹) • y)
      ((((n : ℝ) + 1)⁻¹) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))) x :=
    (hasFDerivAt_id x).const_smul (((n : ℝ) + 1)⁻¹)
  have hcb : DifferentiableAt ℝ (cutBump : EuclideanSpace ℝ (Fin k) → ℝ)
      ((((n : ℝ) + 1)⁻¹) • x) :=
    ((cutBump.contDiff (n := 1)).differentiable (by norm_num)) _
  have hcomp := hcb.hasFDerivAt.comp x hd
  have : fderiv ℝ (cut n) x = (fderiv ℝ cutBump ((((n : ℝ) + 1)⁻¹) • x)).comp
      ((((n : ℝ) + 1)⁻¹) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))) :=
    hcomp.fderiv
  rw [this]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have h1 : ‖(((n : ℝ) + 1)⁻¹) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k))‖ ≤ 1 := by
    refine (norm_smul_le (((n : ℝ) + 1)⁻¹) (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin k)))).trans ?_
    have h2 : ‖(((n : ℝ) + 1)⁻¹)‖ ≤ 1 := by
      rw [norm_inv, Real.norm_of_nonneg hn.le]
      exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    calc _ ≤ ‖(((n : ℝ) + 1)⁻¹)‖ * 1 := by
          gcongr; exact ContinuousLinearMap.norm_id_le
      _ ≤ 1 := by simpa using h2
  calc _ ≤ ‖fderiv ℝ cutBump ((((n : ℝ) + 1)⁻¹) • x)‖ * 1 := by gcongr
    _ ≤ max C 0 := by rw [mul_one]; exact (hC _).trans (le_max_left _ _)


section Approx

variable {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- The `n`-th cut-off of `f`. -/
noncomputable def cutFn (f : EuclideanSpace ℝ (Fin k) → ℝ) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin k)) : ℝ := cut n x * f x

theorem cutFn_contDiff (hf : ContDiff ℝ 1 f) (n : ℕ) : ContDiff ℝ 1 (cutFn f n) :=
  ((cut_contDiff n).of_le (by exact_mod_cast le_top)).mul hf

theorem cutFn_compactSupport (n : ℕ) : HasCompactSupport (cutFn f n) :=
  (cut_compactSupport n).mul_right

theorem cutFn_eventuallyEq {n : ℕ} {x : EuclideanSpace ℝ (Fin k)} (hx : ‖x‖ < (n : ℝ) + 1) :
    cutFn f n =ᶠ[𝓝 x] f := by
  have : ∀ᶠ y in 𝓝 x, ‖y‖ < (n : ℝ) + 1 := by
    have : Continuous (fun y : EuclideanSpace ℝ (Fin k) => ‖y‖) := continuous_norm
    exact this.continuousAt.eventually (gt_mem_nhds hx)
  filter_upwards [this] with y hy
  simp [cutFn, cut_eq_one hy.le]

theorem cutFn_abs_le {M : ℝ} (hM : ∀ x, |f x| ≤ M) (n : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    |cutFn f n x| ≤ M := by
  rw [cutFn, abs_mul, abs_of_nonneg (cut_nonneg n x)]
  calc cut n x * |f x| ≤ 1 * M :=
        mul_le_mul (cut_le_one n x) (hM x) (abs_nonneg _) zero_le_one
    _ = M := one_mul M

theorem cutFn_fderiv_le (hf : ContDiff ℝ 1 f) {M G C : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hG : ∀ x, ‖fderiv ℝ f x‖ ≤ G) (hC : ∀ (n : ℕ) x, ‖fderiv ℝ (cut (k := k) n) x‖ ≤ C)
    (n : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    ‖fderiv ℝ (cutFn f n) x‖ ≤ G + M * C := by
  have h1 : DifferentiableAt ℝ (cut (k := k) n) x :=
    ((cut_contDiff n).differentiable (by simp)) x
  have h2 : DifferentiableAt ℝ f x := hf.differentiable (by norm_num) x
  have : fderiv ℝ (cutFn f n) x = cut n x • fderiv ℝ f x + f x • fderiv ℝ (cut n) x :=
    fderiv_mul h1 h2
  rw [this]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_of_nonneg (cut_nonneg n x)]
    calc cut n x * ‖fderiv ℝ f x‖ ≤ 1 * G :=
          mul_le_mul (cut_le_one n x) (hG x) (norm_nonneg _) zero_le_one
      _ = G := one_mul G
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hM x) (hC n x) (norm_nonneg _) ((abs_nonneg _).trans (hM x))

end Approx


section Mollify

/-- The `n`-th mollifier radius bump. -/
noncomputable def moll (n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin k)) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity,
    by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]
      nlinarith⟩

theorem tendsto_moll_rOut :
    Tendsto (fun n : ℕ => (moll (k := k) n).rOut) atTop (𝓝 0) := by
  show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The mollification of the `n`-th cut-off. -/
noncomputable def mollFn (f : EuclideanSpace ℝ (Fin k) → ℝ) (n : ℕ) :
    EuclideanSpace ℝ (Fin k) → ℝ :=
  ((moll n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] cutFn f n

variable {f : EuclideanSpace ℝ (Fin k) → ℝ}

theorem mollFn_testFn (hf : ContDiff ℝ 1 f) (n : ℕ) :
    DGPS.FiniteN.Tools.StrongConvexityLSI.TestFn (mollFn f n) := by
  refine ⟨?_, ?_⟩
  · exact (moll n).hasCompactSupport_normed.contDiff_convolution_left _
      (moll n).contDiff_normed (cutFn_contDiff hf n).continuous.locallyIntegrable
  · exact (moll n).hasCompactSupport_normed.convolution _ (cutFn_compactSupport n)

theorem fderiv_mollFn (hf : ContDiff ℝ 1 f) (n : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    fderiv ℝ (mollFn f n) x =
      (((moll n).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fderiv ℝ (cutFn f n)) x := by
  have h := (cutFn_compactSupport (f := f) n).hasFDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (f := (moll n).normed volume) (moll n).integrable_normed.locallyIntegrable
    (cutFn_contDiff hf n) x
  rw [mollFn, h.fderiv]
  simp only [convolution_def]
  rfl

end Mollify


section Convergence

variable {f : EuclideanSpace ℝ (Fin k) → ℝ}

theorem tendsto_mollFn (hf : ContDiff ℝ 1 f) (x : EuclideanSpace ℝ (Fin k)) :
    Tendsto (fun n => mollFn f n x) atTop (𝓝 (f x)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ + 1)
  have hev : ∀ᶠ p : ℕ × EuclideanSpace ℝ (Fin k) in atTop ×ˢ 𝓝 x,
      N ≤ p.1 ∧ p.2 ∈ ball x 1 :=
    (eventually_ge_atTop N).prod_mk (ball_mem_nhds x one_pos)
  have hcg : Tendsto (uncurry (cutFn f)) (atTop ×ˢ 𝓝 x) (𝓝 (f x)) := by
    refine ((hf.continuous.tendsto x).comp tendsto_snd).congr' ?_
    filter_upwards [hev] with p hp
    obtain ⟨hn, hy⟩ := hp
    have hy' : ‖p.2‖ < (p.1 : ℝ) + 1 := by
      have h1 : ‖p.2‖ ≤ ‖x‖ + ‖p.2 - x‖ := by
        have := norm_le_norm_add_norm_sub' p.2 x
        linarith
      have h2 : ‖p.2 - x‖ < 1 := by simpa [dist_eq_norm] using hy
      have h3 : (N : ℝ) ≤ p.1 := by exact_mod_cast hn
      linarith
    exact (cutFn_eventuallyEq (f := f) hy').self_of_nhds.symm
  exact ContDiffBump.convolution_tendsto_right (μ := volume) (φ := moll) (g := cutFn f)
    (k := fun _ => x) tendsto_moll_rOut
    (Eventually.of_forall fun n => (cutFn_contDiff hf n).continuous.aestronglyMeasurable)
    hcg tendsto_const_nhds

theorem tendsto_fderiv_mollFn (hf : ContDiff ℝ 1 f) (x : EuclideanSpace ℝ (Fin k)) :
    Tendsto (fun n => fderiv ℝ (mollFn f n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (‖x‖ + 1)
  have hev : ∀ᶠ p : ℕ × EuclideanSpace ℝ (Fin k) in atTop ×ˢ 𝓝 x,
      N ≤ p.1 ∧ p.2 ∈ ball x 1 :=
    (eventually_ge_atTop N).prod_mk (ball_mem_nhds x one_pos)
  have hcg : Tendsto (uncurry (fun n => fderiv ℝ (cutFn f n))) (atTop ×ˢ 𝓝 x)
      (𝓝 (fderiv ℝ f x)) := by
    refine (((hf.continuous_fderiv one_ne_zero).tendsto x).comp tendsto_snd).congr' ?_
    filter_upwards [hev] with p hp
    obtain ⟨hn, hy⟩ := hp
    have hy' : ‖p.2‖ < (p.1 : ℝ) + 1 := by
      have h1 : ‖p.2‖ ≤ ‖x‖ + ‖p.2 - x‖ := by
        have := norm_le_norm_add_norm_sub' p.2 x
        linarith
      have h2 : ‖p.2 - x‖ < 1 := by simpa [dist_eq_norm] using hy
      have h3 : (N : ℝ) ≤ p.1 := by exact_mod_cast hn
      linarith
    exact (cutFn_eventuallyEq (f := f) hy').fderiv_eq.symm
  have hcont : ∀ n, Continuous (fderiv ℝ (cutFn f n)) := fun n =>
    (cutFn_contDiff hf n).continuous_fderiv one_ne_zero
  have := ContDiffBump.convolution_tendsto_right (μ := volume) (φ := moll)
    (g := fun n => fderiv ℝ (cutFn f n)) (k := fun _ => x) tendsto_moll_rOut
    (Eventually.of_forall fun n => (hcont n).aestronglyMeasurable) hcg tendsto_const_nhds
  simpa only [fderiv_mollFn hf] using this

end Convergence


section EntropyLimit

variable {α : Type*} [MeasurableSpace α]

theorem exists_mul_log_bound (K : ℝ) :
    ∃ B : ℝ, ∀ t ∈ Icc (0 : ℝ) K, ‖t * Real.log t‖ ≤ B :=
  isCompact_Icc.exists_bound_of_continuousOn Real.continuous_mul_log.continuousOn

/-- Continuity of homogeneous entropy under uniformly bounded pointwise convergence. -/
theorem tendsto_homogeneousEntropy {μ : Measure α} [IsProbabilityMeasure μ]
    {h : ℕ → α → ℝ} {h' : α → ℝ} {K : ℝ} (hmeas : ∀ n, Measurable (h n))
    (hmeas' : Measurable h') (h0 : ∀ n x, 0 ≤ h n x) (h0' : ∀ x, 0 ≤ h' x)
    (hK : ∀ n x, h n x ≤ K) (hK' : ∀ x, h' x ≤ K)
    (hlim : ∀ x, Tendsto (fun n => h n x) atTop (𝓝 (h' x))) :
    Tendsto (fun n => DGPS.homogeneousEntropy μ (h n)) atTop
      (𝓝 (DGPS.homogeneousEntropy μ h')) := by
  obtain ⟨B, hB⟩ := exists_mul_log_bound K
  have hint : ∀ v : α → ℝ, Measurable v → (∀ x, 0 ≤ v x) → (∀ x, v x ≤ K) →
      Integrable v μ := fun v hv h0 hK =>
    Integrable.of_bound hv.aestronglyMeasurable K
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (h0 x)]; exact hK x)
  have hintlog : ∀ v : α → ℝ, Measurable v → (∀ x, 0 ≤ v x) → (∀ x, v x ≤ K) →
      Integrable (fun x => v x * Real.log (v x)) μ := fun v hv h0 hK =>
    Integrable.of_bound (Real.continuous_mul_log.measurable.comp hv).aestronglyMeasurable B
      (Eventually.of_forall fun x => hB _ ⟨h0 x, hK x⟩)
  have hform : ∀ v : α → ℝ, Measurable v → (∀ x, 0 ≤ v x) → (∀ x, v x ≤ K) →
      DGPS.homogeneousEntropy μ v = ENNReal.ofReal (∫ x, v x * Real.log (v x) ∂μ
        - (∫ x, v x ∂μ) * Real.log (∫ x, v x ∂μ)) := fun v hv h0 hK =>
    DGPS.homogeneousEntropy_eq_formula (Eventually.of_forall h0) (hint v hv h0 hK)
      (hintlog v hv h0 hK)
  simp_rw [hform _ (hmeas _) (h0 _) (hK _), hform _ hmeas' h0' hK']
  refine ENNReal.tendsto_ofReal (Tendsto.sub ?_ ?_)
  · refine tendsto_integral_of_dominated_convergence (fun _ => B) ?_ (integrable_const B) ?_ ?_
    · intro n
      exact (Real.continuous_mul_log.measurable.comp (hmeas n)).aestronglyMeasurable
    · intro n
      exact Eventually.of_forall fun x => hB _ ⟨h0 n x, hK n x⟩
    · exact Eventually.of_forall fun x => (Real.continuous_mul_log.tendsto _).comp (hlim x)
  · have ha : Tendsto (fun n => ∫ x, h n x ∂μ) atTop (𝓝 (∫ x, h' x ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => K) ?_ (integrable_const K) ?_ ?_
      · intro n
        exact (hmeas n).aestronglyMeasurable
      · intro n
        exact Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (h0 n x)]; exact hK n x
      · exact Eventually.of_forall hlim
    exact (Real.continuous_mul_log.tendsto _).comp ha

end EntropyLimit


section Main

variable {f : EuclideanSpace ℝ (Fin k) → ℝ}

theorem abs_mollFn_le {M : ℝ} (hM : ∀ x, |f x| ≤ M) (n : ℕ)
    (x : EuclideanSpace ℝ (Fin k)) : |mollFn f n x| ≤ M := by
  have := norm_convolution_le_of_bound (φ := (moll n).normed volume) (g := cutFn f n)
    (moll n).nonneg_normed (moll n).integral_normed (B := M)
    (fun y => by rw [Real.norm_eq_abs]; exact cutFn_abs_le hM n y) x
  rwa [Real.norm_eq_abs] at this

theorem norm_fderiv_mollFn_le (hf : ContDiff ℝ 1 f) {M G : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hG : ∀ x, ‖fderiv ℝ f x‖ ≤ G) :
    ∃ B : ℝ, ∀ (n : ℕ) (x : EuclideanSpace ℝ (Fin k)), ‖fderiv ℝ (mollFn f n) x‖ ≤ B := by
  obtain ⟨C, -, hC⟩ := exists_cut_fderiv_bound (k := k)
  refine ⟨G + M * C, fun n x => ?_⟩
  rw [fderiv_mollFn hf]
  exact norm_convolution_le_of_bound (φ := (moll n).normed volume) (moll n).nonneg_normed
    (moll n).integral_normed (fun y => cutFn_fderiv_le hf hM hG hC n y) x

/-- FIN015b: the log-Sobolev inequality of `HasLSIRate` extends from smooth compactly supported
functions to `C¹` functions with bounded values and bounded gradient. -/
theorem hasLSIRate_of_C1_bounded {μ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure μ] {lam : ℝ}
    (hμ : DGPS.FiniteN.Tools.StrongConvexityLSI.HasLSIRate μ lam)
    (hf : ContDiff ℝ 1 f) {M G : ℝ} (hM : ∀ x, |f x| ≤ M) (hG : ∀ x, ‖fderiv ℝ f x‖ ≤ G) :
    DGPS.homogeneousEntropy μ (fun x => f x ^ 2) ≤
      ENNReal.ofReal (2 / lam) * ∫⁻ x, DGPS.FiniteN.Tools.StrongConvexityLSI.gradSq f x ∂μ := by
  obtain ⟨B, hB⟩ := norm_fderiv_mollFn_le hf hM hG
  have hgc : ∀ n, ContDiff ℝ ∞ (mollFn f n) := fun n => (mollFn_testFn hf n).1
  have hgm : ∀ n, Measurable (fun x => mollFn f n x ^ 2) := fun n =>
    ((hgc n).continuous.pow 2).measurable
  have hent : Tendsto (fun n => DGPS.homogeneousEntropy μ (fun x => mollFn f n x ^ 2)) atTop
      (𝓝 (DGPS.homogeneousEntropy μ (fun x => f x ^ 2))) := by
    refine tendsto_homogeneousEntropy (K := M ^ 2) hgm (hf.continuous.pow 2).measurable
      (fun n x => sq_nonneg _) (fun x => sq_nonneg _) (fun n x => ?_) (fun x => ?_)
      (fun x => (tendsto_mollFn hf x).pow 2)
    · have := abs_mollFn_le hM n x
      calc mollFn f n x ^ 2 = |mollFn f n x| ^ 2 := (sq_abs _).symm
        _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    · calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
        _ ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hM x) 2
  have hgrad : Tendsto (fun n => ∫⁻ x, DGPS.FiniteN.Tools.StrongConvexityLSI.gradSq
      (mollFn f n) x ∂μ) atTop
      (𝓝 (∫⁻ x, DGPS.FiniteN.Tools.StrongConvexityLSI.gradSq f x ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal B ^ 2) ?_ ?_ ?_ ?_
    · intro n
      have : Continuous (fderiv ℝ (mollFn f n)) :=
        (hgc n).continuous_fderiv (by simp)
      exact this.enorm.measurable.pow_const 2
    · intro n
      refine Eventually.of_forall fun x => ?_
      unfold DGPS.FiniteN.Tools.StrongConvexityLSI.gradSq
      show ‖fderiv ℝ (mollFn f n) x‖ₑ ^ 2 ≤ ENNReal.ofReal B ^ 2
      gcongr
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB n x)
    · simp
    · refine Eventually.of_forall fun x => ?_
      unfold DGPS.FiniteN.Tools.StrongConvexityLSI.gradSq
      exact ((ENNReal.continuous_pow 2).tendsto _).comp
        ((continuous_enorm.tendsto _).comp (tendsto_fderiv_mollFn hf x))
  refine le_of_tendsto_of_tendsto hent
    (ENNReal.Tendsto.const_mul hgrad (Or.inr ENNReal.ofReal_ne_top)) ?_
  exact Eventually.of_forall fun n => hμ _ (mollFn_testFn hf n)

/-- Variant with the boundedness hypotheses stated via `Bornology.IsBounded`. -/
theorem hasLSIRate_of_C1_isBounded {μ : Measure (EuclideanSpace ℝ (Fin k))}
    [IsProbabilityMeasure μ] {lam : ℝ}
    (hμ : DGPS.FiniteN.Tools.StrongConvexityLSI.HasLSIRate μ lam)
    (hf : ContDiff ℝ 1 f) (hb : Bornology.IsBounded (Set.range f))
    (hd : Bornology.IsBounded (Set.range (fderiv ℝ f))) :
    DGPS.homogeneousEntropy μ (fun x => f x ^ 2) ≤
      ENNReal.ofReal (2 / lam) * ∫⁻ x, DGPS.FiniteN.Tools.StrongConvexityLSI.gradSq f x ∂μ := by
  obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le).1 hb
  obtain ⟨G, hG⟩ := (isBounded_iff_forall_norm_le).1 hd
  exact hasLSIRate_of_C1_bounded hμ hf (M := M) (G := G)
    (fun x => by simpa using hM (f x) ⟨x, rfl⟩) (fun x => hG _ ⟨x, rfl⟩)

end Main

end DGPS.FiniteN.Tools.LSIExtension
