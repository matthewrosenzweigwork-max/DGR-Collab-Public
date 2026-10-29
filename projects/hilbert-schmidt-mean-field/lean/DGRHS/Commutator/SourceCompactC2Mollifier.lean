import DGRHS.Commutator.SourceBoundedC2Spatial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Topology.UniformSpace.HeineCantor

/-! RECORDS-ONLY / UNCOMPILED Claude candidate (remaining-original-results
return, 2026-10-03). No compiler has evaluated this file.

Compact smoothing of a fixed compactly supported C2 test. The approximate
identity is the native normalized smooth bump `sourceMollifier n` with outer
radius `2*(n+2)⁻¹ ≤ 1`: nonnegative, unit Lebesgue mass, compact support in
the closed unit ball. Convolution on the LEFT with this smooth bump gives a
smooth function (native `contDiff_convolution_left`); differentiation falls
on the C2 test (native `hasFDerivAt_convolution_right`, twice), so

  `fderiv (η ⋆ ψ) = η ⋆ fderiv ψ`,  `fderiv (fderiv (η ⋆ ψ)) = η ⋆ fderiv (fderiv ψ)`.

Uniform continuity of the three continuous compactly supported functions
`ψ, Dψ, D²ψ` and the native unit-mass distance estimate then give UNIFORM
convergence of value, first and second derivative; the same estimate with
centre zero gives one bound, uniform in `n`, on all derivatives through order
two. Every approximant is supported in the one compact set
`closedBall 0 1 + tsupport ψ`. No measure on the time axis, no law, no weak
equation and no desired conclusion is involved. -/
noncomputable section
open MeasureTheory Set Filter Metric Laplacian ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise
namespace DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Mollifier radii: inner `(n+2)⁻¹`, outer `2*(n+2)⁻¹`. -/
def sourceMollifierBump (n : ℕ) : ContDiffBump (0 : E) where
  rIn := ((n : ℝ) + 2)⁻¹
  rOut := 2 * ((n : ℝ) + 2)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < ((n : ℝ) + 2)⁻¹ := by positivity
    linarith

/-- The nonnegative unit-mass compactly supported smooth approximate identity. -/
abbrev sourceMollifier (n : ℕ) : E → ℝ :=
  (sourceMollifierBump (ι := ι) n).normed volume

/-- The mollification of a test, convolution on the left by the smooth bump. -/
abbrev sourceMollify (n : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : E → F) : E → F :=
  sourceMollifier (ι := ι) n ⋆[lsmul ℝ ℝ, volume] h

lemma sourceMollifierBump_rOut_tendsto :
    Tendsto (fun n => (sourceMollifierBump (ι := ι) n).rOut) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have h2 := (tendsto_inv_atTop_zero.comp h1).const_mul (2 : ℝ)
  simpa only [sourceMollifierBump, mul_zero, Function.comp_def] using h2

lemma sourceMollifierBump_rOut_le_one (n : ℕ) :
    (sourceMollifierBump (ι := ι) n).rOut ≤ 1 := by
  show 2 * ((n : ℝ) + 2)⁻¹ ≤ 1
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  rw [← div_eq_mul_inv, div_le_one hpos]
  exact h2

/-- Pointwise scalar multiplication applied after a linear map is again pointwise
scalar multiplication; this identifies the native `precompR` convolution with
the ordinary scalar convolution. -/
lemma source_lsmul_precompR (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).precompR E =
      (lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] F) →L[ℝ] (E →L[ℝ] F)) := by
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun g =>
    ContinuousLinearMap.ext fun v => ?_
  simp only [precompR_apply, compL_apply, ContinuousLinearMap.comp_apply, lsmul_apply,
    ContinuousLinearMap.smul_apply]

/-- Unit mass and nonnegativity give the norm bound of the mollification by a
global bound of the mollified function, uniformly in `n` and the point. -/
lemma source_mollify_norm_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (h : E → F) (hh : Continuous h) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ y, ‖h y‖ ≤ C) (n : ℕ) (x : E) :
    ‖sourceMollify (ι := ι) n h x‖ ≤ C := by
  have hd := dist_convolution_le (μ := volume) (x₀ := x) (z₀ := (0 : F)) hC
    (sourceMollifierBump (ι := ι) n).support_normed_eq.subset
    (fun y => (sourceMollifierBump (ι := ι) n).nonneg_normed (μ := volume) y)
    (sourceMollifierBump (ι := ι) n).integral_normed hh.aestronglyMeasurable
    (fun y _ => by simpa only [dist_zero_right] using hb y)
  simpa only [dist_zero_right] using hd

/-- Uniform convergence of the mollification of a continuous compactly
supported function. -/
lemma source_mollify_tendstoUniformly {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (h : E → F) (hh : Continuous h)
    (hc : HasCompactSupport h) :
    TendstoUniformly (fun n => sourceMollify (ι := ι) n h) h atTop := by
  have hu : UniformContinuous h := hc.uniformContinuous_of_continuous hh
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuous_iff.mp hu (ε / 2) (by positivity)
  filter_upwards [(sourceMollifierBump_rOut_tendsto (ι := ι)).eventually
    (eventually_lt_nhds hδ)] with n hn x
  have hle : dist (sourceMollify (ι := ι) n h x) (h x) ≤ ε / 2 :=
    ContDiffBump.dist_normed_convolution_le hh.aestronglyMeasurable
      (fun y hy => (hδh (lt_trans (mem_ball.mp hy) hn)).le)
  rw [dist_comm]
  linarith

/-- The second iterated derivative has the norm of the second Fréchet
derivative. -/
lemma source_norm_iteratedFDeriv_two_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : E → F) (x : E) :
    ‖iteratedFDeriv ℝ 2 f x‖ = ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ f), norm_iteratedFDeriv_fderiv]

/-- A compactly supported C2 function is a bounded C2 test. -/
lemma sourceBoundedC2Test_of_compact (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) : SourceBoundedC2Test ψ := by
  have hb (j : ℕ) (hj : j ≤ 2) : ∃ A : ℝ, ∀ y, ‖iteratedFDeriv ℝ j ψ y‖ ≤ A :=
    (hψ.continuous_iteratedFDeriv (by exact_mod_cast hj)).bounded_above_of_compact_support
      (hc.iteratedFDeriv j)
  obtain ⟨A0, hA0⟩ := hb 0 (by norm_num)
  obtain ⟨A1, hA1⟩ := hb 1 (by norm_num)
  obtain ⟨A2, hA2⟩ := hb 2 le_rfl
  refine ⟨hψ, max 0 (max A0 (max A1 A2)), le_max_left _ _, ?_⟩
  intro j hj y
  interval_cases j
  · exact (hA0 y).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hA1 y).trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  · exact (hA2 y).trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))

section Fixed

lemma sourceMollify_contDiff {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (n : ℕ) : ContDiff ℝ ∞ (sourceMollify (ι := κ) n ψ) :=
  (sourceMollifierBump (ι := κ) n).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) ((sourceMollifierBump (ι := κ) n).contDiff_normed (n := ⊤))
    hψ.continuous.locallyIntegrable

lemma sourceMollify_hasCompactSupport {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (n : ℕ) :
    HasCompactSupport (sourceMollify (ι := κ) n ψ) :=
  (sourceMollifierBump (ι := κ) n).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hc

/-- All approximants are supported in one fixed compact set. -/
lemma sourceMollify_tsupport_subset {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (n : ℕ) :
    tsupport (sourceMollify (ι := κ) n ψ) ⊆ closedBall (0 : EuclideanSpace ℝ κ) 1 + tsupport ψ := by
  have hK : IsCompact (closedBall (0 : EuclideanSpace ℝ κ) 1 + tsupport ψ) :=
    (isCompact_closedBall 0 1).add hc
  refine closure_minimal ?_ hK.isClosed
  refine (support_convolution_subset (lsmul ℝ ℝ)).trans (add_subset_add ?_ (subset_tsupport ψ))
  rw [(sourceMollifierBump (ι := κ) n).support_normed_eq]
  exact ball_subset_closedBall.trans
    (closedBall_subset_closedBall (sourceMollifierBump_rOut_le_one (ι := κ) n))

lemma sourceMollify_fderiv {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (n : ℕ) :
    fderiv ℝ (sourceMollify (ι := κ) n ψ) = sourceMollify (ι := κ) n (fderiv ℝ ψ) := by
  funext x
  have hd := hc.hasFDerivAt_convolution_right
    (μ := (volume : Measure (EuclideanSpace ℝ κ))) (lsmul ℝ ℝ)
    ((sourceMollifierBump (ι := κ) n).continuous_normed
      (μ := (volume : Measure (EuclideanSpace ℝ κ)))).locallyIntegrable
    (hψ.of_le one_le_two) x
  rw [source_lsmul_precompR] at hd
  exact hd.fderiv

lemma sourceMollify_fderiv_fderiv {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (n : ℕ) :
    fderiv ℝ (fderiv ℝ (sourceMollify (ι := κ) n ψ)) =
      sourceMollify (ι := κ) n (fderiv ℝ (fderiv ℝ ψ)) := by
  rw [sourceMollify_fderiv ψ hψ hc n]
  funext x
  have hψ1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (m := 1) (by norm_num)
  have hd := (hc.fderiv (𝕜 := ℝ)).hasFDerivAt_convolution_right
    (μ := (volume : Measure (EuclideanSpace ℝ κ))) (lsmul ℝ ℝ)
    ((sourceMollifierBump (ι := κ) n).continuous_normed
      (μ := (volume : Measure (EuclideanSpace ℝ κ)))).locallyIntegrable hψ1 x
  rw [source_lsmul_precompR] at hd
  exact hd.fderiv

/-- One derivative bound through order two, uniform in the mollification index. -/
lemma sourceMollify_deriv_bound {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n j, j ≤ 2 → ∀ x,
      ‖iteratedFDeriv ℝ j (sourceMollify (ι := κ) n ψ) x‖ ≤ C := by
  obtain ⟨_, C, hC, hb⟩ := sourceBoundedC2Test_of_compact ψ hψ hc
  refine ⟨C, hC, ?_⟩
  intro n j hj x
  interval_cases j
  · rw [norm_iteratedFDeriv_zero]
    exact source_mollify_norm_le ψ hψ.continuous C hC
      (fun y => by simpa only [norm_iteratedFDeriv_zero] using hb 0 (by norm_num) y) n x
  · rw [norm_iteratedFDeriv_one, sourceMollify_fderiv ψ hψ hc n]
    exact source_mollify_norm_le (fderiv ℝ ψ) (hψ.continuous_fderiv (by norm_num)) C hC
      (fun y => by simpa only [norm_iteratedFDeriv_one] using hb 1 (by norm_num) y) n x
  · rw [source_norm_iteratedFDeriv_two_eq, sourceMollify_fderiv_fderiv ψ hψ hc n]
    have hcont : Continuous (fderiv ℝ (fderiv ℝ ψ)) :=
      (hψ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    exact source_mollify_norm_le (fderiv ℝ (fderiv ℝ ψ)) hcont C hC
      (fun y => by rw [← source_norm_iteratedFDeriv_two_eq]; exact hb 2 le_rfl y) n x

lemma sourceMollify_tendstoUniformly_value {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) :
    TendstoUniformly (fun n => sourceMollify (ι := κ) n ψ) ψ atTop :=
  source_mollify_tendstoUniformly ψ hψ.continuous hc

lemma sourceMollify_tendstoUniformly_fderiv {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) :
    TendstoUniformly (fun n => fderiv ℝ (sourceMollify (ι := κ) n ψ)) (fderiv ℝ ψ) atTop := by
  simp_rw [sourceMollify_fderiv ψ hψ hc]
  exact source_mollify_tendstoUniformly (fderiv ℝ ψ) (hψ.continuous_fderiv (by norm_num))
    (hc.fderiv (𝕜 := ℝ))

lemma sourceMollify_tendstoUniformly_hessian {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) :
    TendstoUniformly (fun n => fderiv ℝ (fderiv ℝ (sourceMollify (ι := κ) n ψ)))
      (fderiv ℝ (fderiv ℝ ψ)) atTop := by
  simp_rw [sourceMollify_fderiv_fderiv ψ hψ hc]
  exact source_mollify_tendstoUniformly (fderiv ℝ (fderiv ℝ ψ))
    ((hψ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero)
    ((hc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))

/-- Uniform convergence of the second iterated derivatives in operator norm. -/
lemma sourceMollify_tendstoUniformly_iteratedFDeriv_two {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) :
    TendstoUniformly (fun n => iteratedFDeriv ℝ 2 (sourceMollify (ι := κ) n ψ))
      (iteratedFDeriv ℝ 2 ψ) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformly_iff
    (F := fun n => fderiv ℝ (fderiv ℝ (sourceMollify (ι := κ) n ψ)))
    (f := fderiv ℝ (fderiv ℝ ψ))).mp
    (sourceMollify_tendstoUniformly_hessian ψ hψ hc) ε hε] with n hn x
  refine lt_of_le_of_lt ?_ (hn x)
  simp only [dist_eq_norm]
  have hdist (H Hn : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ →L[ℝ] ℝ) :
      dist H Hn = ‖H - Hn‖ := dist_eq_norm H Hn
  rw [hdist]
  refine ContinuousMultilinearMap.opNorm_le_bound
    (ContinuousLinearMap.opNorm_nonneg
      (fderiv ℝ (fderiv ℝ ψ) x -
        fderiv ℝ (fderiv ℝ (sourceMollify (ι := κ) n ψ)) x)) (fun m => ?_)
  rw [ContinuousMultilinearMap.sub_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply,
    Fin.prod_univ_two, ← ContinuousLinearMap.sub_apply, ← ContinuousLinearMap.sub_apply]
  calc
    _ ≤ ‖(fderiv ℝ (fderiv ℝ ψ) x - fderiv ℝ (fderiv ℝ (sourceMollify (ι := κ) n ψ)) x)
          (m 0)‖ * ‖m 1‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by
      have h0 := ContinuousLinearMap.le_opNorm
        (fderiv ℝ (fderiv ℝ ψ) x - fderiv ℝ (fderiv ℝ (sourceMollify (ι := κ) n ψ)) x) (m 0)
      have := mul_le_mul_of_nonneg_right h0 (norm_nonneg (m 1))
      simpa only [mul_assoc] using this

lemma sourceMollify_tendsto_gradient {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (x : EuclideanSpace ℝ κ) :
    Tendsto (fun n => gradient (sourceMollify (ι := κ) n ψ) x) atTop (𝓝 (gradient ψ x)) := by
  have hg (f : EuclideanSpace ℝ κ → ℝ) : gradient f x = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ κ)).symm (fderiv ℝ f x) := rfl
  simp_rw [hg]
  exact ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ κ)).symm.continuous.tendsto _).comp
    ((sourceMollify_tendstoUniformly_fderiv ψ hψ hc).tendsto_at x)

lemma sourceMollify_tendsto_laplacian {κ : Type*} [Fintype κ]
    (ψ : EuclideanSpace ℝ κ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) (x : EuclideanSpace ℝ κ) :
    Tendsto (fun n => laplacian (sourceMollify (ι := κ) n ψ) x) atTop (𝓝 (laplacian ψ x)) := by
  let b := EuclideanSpace.basisFun κ ℝ
  have hl (f : EuclideanSpace ℝ κ → ℝ) : laplacian f x = ∑ i, iteratedFDeriv ℝ 2 f x ![b i, b i] :=
    congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b) x
  simp_rw [hl]
  apply tendsto_finsetSum
  intro i _
  have hc2 : Continuous fun A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => EuclideanSpace ℝ κ) ℝ =>
      A ![b i, b i] :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => EuclideanSpace ℝ κ) ℝ ![b i, b i]).continuous
  exact (hc2.tendsto _).comp ((sourceMollify_tendstoUniformly_iteratedFDeriv_two ψ hψ hc).tendsto_at x)

end Fixed

/-- Packaged compact-smooth approximation of a compact C2 test: smooth,
compactly supported in one common compact set, one derivative bound through
order two, uniform convergence of value, first and second derivative, and
pointwise convergence of the gradient and Laplacian. -/
theorem exists_source_compactC2_mollification (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hc : HasCompactSupport ψ) :
    ∃ ψs : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ ∞ (ψs n)) ∧ (∀ n, HasCompactSupport (ψs n)) ∧
      (∃ K : Set E, IsCompact K ∧ ∀ n, tsupport (ψs n) ⊆ K) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ n j, j ≤ 2 → ∀ x, ‖iteratedFDeriv ℝ j (ψs n) x‖ ≤ C) ∧
      TendstoUniformly ψs ψ atTop ∧
      TendstoUniformly (fun n => fderiv ℝ (ψs n)) (fderiv ℝ ψ) atTop ∧
      TendstoUniformly (fun n => iteratedFDeriv ℝ 2 (ψs n)) (iteratedFDeriv ℝ 2 ψ) atTop ∧
      (∀ x, Tendsto (fun n => gradient (ψs n) x) atTop (𝓝 (gradient ψ x))) ∧
      (∀ x, Tendsto (fun n => laplacian (ψs n) x) atTop (𝓝 (laplacian ψ x))) :=
  ⟨fun n => sourceMollify (ι := ι) n ψ, sourceMollify_contDiff ψ hψ hc,
    sourceMollify_hasCompactSupport ψ hψ hc,
    ⟨_, (isCompact_closedBall 0 1).add hc, sourceMollify_tsupport_subset ψ hψ hc⟩,
    sourceMollify_deriv_bound ψ hψ hc, sourceMollify_tendstoUniformly_value ψ hψ hc,
    sourceMollify_tendstoUniformly_fderiv ψ hψ hc,
    sourceMollify_tendstoUniformly_iteratedFDeriv_two ψ hψ hc,
    sourceMollify_tendsto_gradient ψ hψ hc, sourceMollify_tendsto_laplacian ψ hψ hc⟩

end DGRHS.Commutator
