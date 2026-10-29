import LeanResearch.PeriodicAttractiveLogGas.GreenMollifierConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Full local smooth convergence for the prescribed radial Green
regularization. We use the actual harmonic quadratic residual and the proved
radial mean-value formula. On every pole-free mollifier neighborhood, the
regularized lift differs from the Green lift by one scalar quadratic moment.
Compactness supplies a uniform neighborhood margin. Thus every derivative of
positive order is eventually exactly equal, while order zero converges
uniformly by the actual second-moment estimate.

This is an adaptation of the source's radial harmonic averaging argument to
the smooth-convergence assertion. It does not assume high-order derivative
commutation or infer it from a classical derivative of a singular function.
-/

noncomputable section
open MeasureTheory Set Metric Filter InnerProductSpace
open scoped Topology ContDiff Convolution

namespace PeriodicAttractiveLogGas

/-- The actual regular representative minus the source quadratic is harmonic
off the lattice. Identification uses continuous a.e. uniqueness on this open
set, so the arbitrary choice of smooth representative causes no gap. -/
theorem harmonicOnNhd_regularGreenLift_sub_quadratic :
    HarmonicOnNhd (fun x : PlanarSpace ↦ regularGreenLift x - planarGreenQuadratic x)
      offIntegerLattice := by
  obtain ⟨h, hsm, hhar, hae⟩ := exists_greenQuadraticRemainder
  have hcont : ContinuousOn
      (fun x : PlanarSpace ↦ regularGreenLift x - planarGreenQuadratic x) offIntegerLattice :=
    contDiffOn_regularGreenLift.continuousOn.sub
      contDiff_planarGreenQuadratic.continuous.continuousOn
  have hsame : (fun x : PlanarSpace ↦ regularGreenLift x - planarGreenQuadratic x)
      =ᵐ[volume.restrict offIntegerLattice] h := by
    filter_upwards [regularGreenLift_ae_greenLift.restrict, hae] with x hx hh
    rw [hx]
    exact hh
  have heq := Measure.eqOn_open_of_ae_eq hsame isOpen_offIntegerLattice
    hcont hsm.continuousOn
  intro x hx
  have hlocal : (fun y : PlanarSpace ↦ regularGreenLift y - planarGreenQuadratic y)
      =ᶠ[𝓝 x] h := by
    filter_upwards [isOpen_offIntegerLattice.mem_nhds hx] with y hy
    exact heq hy
  exact (harmonicAt_congr_nhds hlocal).mpr (hhar x hx)

/-- A continuous global extension is used only to make the global harmonic
convolution literal. Equality and harmonicity are proved on the local ball. -/
theorem exists_continuous_greenQuadraticResidual_extension
    {x : PlanarSpace} {R : ℝ} (hball : closedBall x R ⊆ offIntegerLattice) :
    ∃ H : PlanarSpace → ℝ, Continuous H ∧
      EqOn H (fun y ↦ regularGreenLift y - planarGreenQuadratic y) (closedBall x R) ∧
      HarmonicOnNhd H (ball x R) := by
  let K := closedBall x R
  have hc : ContinuousOn
      (fun y : PlanarSpace ↦ regularGreenLift y - planarGreenQuadratic y) K :=
    (contDiffOn_regularGreenLift.continuousOn.sub
      contDiff_planarGreenQuadratic.continuous.continuousOn).mono hball
  let f : C(K, ℝ) := ⟨fun y ↦ regularGreenLift y - planarGreenQuadratic y, hc.domRestrict⟩
  obtain ⟨H, hH⟩ := f.exists_restrict_eq isClosed_closedBall
  have heq : EqOn H (fun y ↦ regularGreenLift y - planarGreenQuadratic y) K := by
    intro y hy
    exact congrArg (fun g : C(K, ℝ) ↦ g ⟨y, hy⟩) hH
  refine ⟨H, H.continuous, heq, ?_⟩
  intro y hy
  have hlocal : (fun w : PlanarSpace ↦ regularGreenLift w - planarGreenQuadratic w)
      =ᶠ[𝓝 y] H := by
    filter_upwards [isOpen_ball.mem_nhds hy] with w hw
    exact (heq (ball_subset_closedBall hw)).symm
  exact (harmonicAt_congr_nhds hlocal).mp
    (harmonicOnNhd_regularGreenLift_sub_quadratic y (hball (ball_subset_closedBall hy)))

def greenMollifierQuadraticShift (ε : ℝ) : ℝ :=
  (Real.pi / 2) * (∫ y : PlanarSpace, scaledRadialMollifier ε y * ‖y‖ ^ 2)

theorem greenMollifierQuadraticShift_nonneg (ε : ℝ) :
    0 ≤ greenMollifierQuadraticShift ε := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun y ↦ mul_nonneg (scaledRadialMollifier_nonneg ε y) (sq_nonneg _))

theorem greenMollifierQuadraticShift_le (ε : ℝ) (hε : 0 < ε) :
    greenMollifierQuadraticShift ε ≤ (Real.pi / 2) * ε ^ 2 :=
  mul_le_mul_of_nonneg_left (integral_scaledRadialMollifier_mul_norm_sq_le ε hε) (by positivity)

theorem tendsto_greenMollifierQuadraticShift {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (ht : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i ↦ greenMollifierQuadraticShift (ε i)) l (𝓝 0) := by
  apply squeeze_zero (fun i ↦ greenMollifierQuadraticShift_nonneg (ε i))
    (fun i ↦ greenMollifierQuadraticShift_le (ε i) (hε i))
  simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using
    (tendsto_const_nhds.mul (ht.pow 2) :
      Tendsto (fun i ↦ (Real.pi / 2) * ε i ^ 2) l (𝓝 ((Real.pi / 2) * (0 : ℝ) ^ 2)))

/-- Exact spatially constant correction whenever the full localization ball
avoids every lattice pole. Both terms in the localized convolution are
integrable before linearity and radial reproduction are applied. -/
theorem regularizedGreen_lift_eq_add_quadraticShift_on_ball
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ (1 / 16 : ℝ)) {x : PlanarSpace}
    (hball : closedBall x (2 * ε) ⊆ offIntegerLattice) :
    regularizedGreen ε hε (torusQuotient x) =
      regularGreenLift x + greenMollifierQuadraticShift ε := by
  obtain ⟨H, hHcont, hHeq, hHharm⟩ :=
    exists_continuous_greenQuadraticResidual_extension hball
  have hHlocal : HarmonicOnNhd H (closedBall x ε) := by
    intro y hy
    apply hHharm
    have hd : dist y x ≤ ε := hy
    exact show dist y x < 2 * ε from by linarith
  have hQ : Integrable (fun y ↦ scaledRadialMollifier ε y * planarGreenQuadratic (x - y)) volume :=
    integrable_scaledRadialMollifier_mul_continuous ε hε
      (contDiff_planarGreenQuadratic.continuous.comp (continuous_const.sub continuous_id))
  have hH : Integrable (fun y ↦ scaledRadialMollifier ε y * H (x - y)) volume :=
    integrable_scaledRadialMollifier_mul_continuous ε hε
      (hHcont.comp (continuous_const.sub continuous_id))
  have heq : (fun y ↦ regularGreenLift (x - y) * scaledRadialMollifier ε y) =ᵐ[volume]
      (fun y ↦ scaledRadialMollifier ε y * planarGreenQuadratic (x - y) +
        scaledRadialMollifier ε y * H (x - y)) := by
    filter_upwards with y
    by_cases hzero : scaledRadialMollifier ε y = 0
    · simp only [hzero, mul_zero, zero_mul, add_zero]
    · have hy := mem_ball_zero_iff.mp (support_scaledRadialMollifier_subset ε hε hzero)
      have hxy : x - y ∈ closedBall x (2 * ε) := by
        rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
        linarith
      rw [hHeq hxy]
      ring
  rw [regularizedGreen_lift_eq_convolution ε hε hεsmall, convolution_mul_swap,
    integral_congr_ae heq, integral_add hQ hH,
    integral_scaledRadialMollifier_mul_quadratic ε hε x,
    integral_scaledRadialMollifier_mul_sub_harmonic ε hε hHcont hHlocal,
    hHeq (mem_closedBall_self (by positivity : 0 ≤ 2 * ε))]
  unfold greenMollifierQuadraticShift
  ring

/-- Compactness gives a uniform support margin and an equality on a genuine
neighborhood of every point of the compact set. This neighborhood equality
precedes, and justifies, every use of iterated-derivative locality below. -/
theorem exists_regularizedGreen_lift_local_identity_on_compact
    {K : Set PlanarSpace} (hK : IsCompact K) (hKU : K ⊆ offIntegerLattice) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) → ε < δ →
      ∀ x ∈ K, (fun y : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient y))
        =ᶠ[𝓝 x] (fun y ↦ regularGreenLift y + greenMollifierQuadraticShift ε) := by
  obtain ⟨R, hR, hRU⟩ := hK.exists_cthickening_subset_open isOpen_offIntegerLattice hKU
  refine ⟨R / 8, by positivity, ?_⟩
  intro ε hε hsmall hεR x hx
  filter_upwards [ball_mem_nhds x (by positivity : 0 < R / 4)] with y hy
  apply regularizedGreen_lift_eq_add_quadraticShift_on_ball ε hε hsmall
  intro w hw
  apply hRU
  apply mem_cthickening_of_dist_le w x R K hx
  have hwy : dist w y ≤ 2 * ε := hw
  have hyx : dist y x < R / 4 := hy
  have ht := dist_triangle w y x
  linarith

/-- Every positive-order ordinary iterated derivative is eventually exactly
equal on the compact set; no derivative of the singularity is integrated. -/
theorem eventually_iteratedFDeriv_regularizedGreen_lift_eq
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hsmall : ∀ i, ε i ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε l (𝓝 0)) {K : Set PlanarSpace}
    (hK : IsCompact K) (hKU : K ⊆ offIntegerLattice) {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ i in l, ∀ x ∈ K,
      iteratedFDeriv ℝ n (fun y : PlanarSpace ↦ regularizedGreen (ε i) (hε i) (torusQuotient y)) x =
        iteratedFDeriv ℝ n regularGreenLift x := by
  obtain ⟨δ, hδ, hlocal⟩ := exists_regularizedGreen_lift_local_identity_on_compact hK hKU
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with i hi
  intro x hx
  have heq := ((hlocal (ε i) (hε i) (hsmall i) hi x hx).iteratedFDeriv ℝ n).eq_of_nhds
  rw [heq]
  have hG : ContDiffAt ℝ n regularGreenLift x :=
    (contDiffOn_regularGreenLift.contDiffAt
      (isOpen_offIntegerLattice.mem_nhds (hKU hx))).of_le (by simp)
  change iteratedFDeriv ℝ n (regularGreenLift + (fun _ : PlanarSpace ↦
    greenMollifierQuadraticShift (ε i))) x = _
  rw [iteratedFDeriv_add_apply hG contDiffAt_const,
    iteratedFDeriv_const_of_ne hn]
  simp

/-- Zeroth-order convergence is uniform on each compact set avoiding the
lattice, with the same scalar correction at every point of that set. -/
theorem tendstoUniformlyOn_regularizedGreen_lift
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hsmall : ∀ i, ε i ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε l (𝓝 0)) {K : Set PlanarSpace}
    (hK : IsCompact K) (hKU : K ⊆ offIntegerLattice) :
    TendstoUniformlyOn
      (fun i (y : PlanarSpace) ↦ regularizedGreen (ε i) (hε i) (torusQuotient y))
      regularGreenLift l K := by
  obtain ⟨δ, hδ, hlocal⟩ := exists_regularizedGreen_lift_local_identity_on_compact hK hKU
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have hshift := (tendsto_greenMollifierQuadraticShift hε ht).eventually (gt_mem_nhds hη)
  filter_upwards [ht.eventually (gt_mem_nhds hδ), hshift] with i hi hsi
  intro x hx
  have heq := (hlocal (ε i) (hε i) (hsmall i) hi x hx).eq_of_nhds
  rw [heq, Real.dist_eq]
  have halg : regularGreenLift x - (regularGreenLift x + greenMollifierQuadraticShift (ε i)) =
      -greenMollifierQuadraticShift (ε i) := by ring
  rw [halg, abs_neg, abs_of_nonneg (greenMollifierQuadraticShift_nonneg (ε i))]
  exact hsi

/-- Full local C-infinity convergence of source Lemma 2.2, expressed using
the actual ordinary iterated Fréchet derivatives and their operator norms.
The statement includes order zero and allows an arbitrary index filter. -/
theorem tendstoUniformlyOn_iteratedFDeriv_regularizedGreen_lift
    {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hsmall : ∀ i, ε i ≤ (1 / 16 : ℝ))
    (ht : Tendsto ε l (𝓝 0)) {K : Set PlanarSpace}
    (hK : IsCompact K) (hKU : K ⊆ offIntegerLattice) (n : ℕ) :
    TendstoUniformlyOn
      (fun i ↦ iteratedFDeriv ℝ n
        (fun y : PlanarSpace ↦ regularizedGreen (ε i) (hε i) (torusQuotient y)))
      (iteratedFDeriv ℝ n regularGreenLift) l K := by
  by_cases hn : n = 0
  · subst n
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    have hu := Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_regularizedGreen_lift hε hsmall ht hK hKU) η hη
    filter_upwards [hu] with i hi
    intro x hx
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
      LinearIsometryEquiv.dist_map] using hi x hx
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro η hη
    filter_upwards [eventually_iteratedFDeriv_regularizedGreen_lift_eq
      hε hsmall ht hK hKU hn] with i hi
    intro x hx
    rw [hi x hx, dist_self]
    exact hη

end PeriodicAttractiveLogGas
