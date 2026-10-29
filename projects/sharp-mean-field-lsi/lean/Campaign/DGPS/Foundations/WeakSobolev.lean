import DGPS.Foundations.Torus
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The periodic weak Sobolev graph (FOU001)

INTERFACES/common_lemmas.md FOU001. On the Euclidean unit torus with Haar probability `m`, a
weak gradient (DEF001, `IsWeakGradient`) is unique a.e.; the graph
`{(u, g) | g is the weak gradient of u}` in `L²(m) × L²(m; ℝ^d)` with the norm
`‖(u, g)‖² = ‖u‖₂² + ‖g‖₂²` is a closed subspace, hence a Hilbert space; the weak-gradient
operator is closed.

Route (05_LEMMA_LEVEL_DAG FOU001): density of trigonometric polynomials. A real `L²` function
orthogonal to every smooth periodic test has zero Fourier coefficients (the real and imaginary
parts of `mFourier n` are smooth periodic tests), so it vanishes by the `L²` Fourier Hilbert basis
`UnitAddTorus.mFourierBasis`. Each test identity is continuous in `L²` (tests and their
partials are bounded), giving closedness.

Main results:
* `DGPS.ae_eq_zero_of_forall_integral_mul_eq_zero`: uniqueness of distributions in `L²`.
* `DGPS.IsWeakGradient.ae_eq`: weak gradients are unique a.e.
* `DGPS.h1Graph`: the graph as a closed submodule of `WithLp 2 (L² × L²(ℝ^d))`.
* `DGPS.Analysis.periodic_weak_sobolev_graph`: the FOU001 bundle.
-/

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace DGPS

variable {d : ℕ}

/-! ### Bounded measurable tests -/

theorem secT_mem_Icc (x : Torus d) : SharpLSI.secT x ∈ Icc (0 : Fin d → ℝ) 1 := by
  have h : ∀ i, SharpLSI.secT x i ∈ Ioc (0 : ℝ) (0 + 1) := fun i =>
    ((AddCircle.measurableEquivIoc 1 0) (x i)).2
  refine ⟨fun i => (h i).1.le, fun i => ?_⟩
  simpa using (h i).2

/-- A continuous function on `ℝ^d` evaluated at the section `secT` is bounded and measurable. -/
theorem memLp_top_comp_secT {G : (Fin d → ℝ) → ℝ} (hG : Continuous G) :
    MemLp (fun x : Torus d => G (SharpLSI.secT x)) ∞ (haar d) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : Fin d → ℝ)) (b := 1)).exists_bound_of_continuousOn
    hG.continuousOn
  exact memLp_top_of_bound (hG.measurable.comp SharpLSI.measurable_secT).aestronglyMeasurable C
    (Eventually.of_forall fun x => hC _ (secT_mem_Icc x))

theorem IsSmoothPeriodic.memLp_top {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    MemLp φ ∞ (haar d) := by
  have h := memLp_top_comp_secT (d := d) hφ.continuous
  simpa [Function.comp_def, torusLift, SharpLSI.liftT_secT] using h

theorem IsSmoothPeriodic.memLp_top_coordPartial {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ)
    (j : Fin d) : MemLp (coordPartial j φ) ∞ (haar d) :=
  memLp_top_comp_secT ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- Products of an `L²` function with a bounded measurable function are integrable. -/
theorem integrable_mul_of_memLp_two {u φ : Torus d → ℝ} (hu : MemLp u 2 (haar d))
    (hφ : MemLp φ ∞ (haar d)) : Integrable (fun x => u x * φ x) (haar d) :=
  (hu.integrable one_le_two).mul_of_top_left hφ

/-! ### Fourier uniqueness -/

theorem mFourier_torusLift (n : Fin d → ℤ) (y : Fin d → ℝ) :
    UnitAddTorus.mFourier n (torusLift y)
      = ∏ i, Complex.exp (2 * Real.pi * Complex.I * (n i) * (y i) / (1 : ℝ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusLift, SharpLSI.liftT]
  exact Finset.prod_congr rfl fun i _ => fourier_coe_apply

theorem contDiff_mFourier_torusLift (n : Fin d → ℤ) :
    ContDiff ℝ ∞ (fun y => UnitAddTorus.mFourier n (torusLift y)) := by
  simp_rw [mFourier_torusLift]
  refine contDiff_prod fun i _ => Complex.contDiff_exp.comp ?_
  have : ContDiff ℝ ∞ (fun y : Fin d → ℝ => ((y i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ i)
  exact (contDiff_const.mul this).div_const _

theorem isSmoothPeriodic_re_mFourier (n : Fin d → ℤ) :
    IsSmoothPeriodic (fun x => (UnitAddTorus.mFourier n x).re) :=
  Complex.reCLM.contDiff.comp (contDiff_mFourier_torusLift n)

theorem isSmoothPeriodic_im_mFourier (n : Fin d → ℤ) :
    IsSmoothPeriodic (fun x => (UnitAddTorus.mFourier n x).im) :=
  Complex.imCLM.contDiff.comp (contDiff_mFourier_torusLift n)

/-- Mathlib's Fourier API on `UnitAddTorus` uses the product of `AddCircle.haarAddCircle`
(declared locally in that file); it equals `haar d` (not definitionally). -/
theorem haar_eq_pi_haarAddCircle (d : ℕ) :
    haar d = Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  show Measure.pi _ = _
  congr 1
  funext i
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

/-- A real `L²` function orthogonal to every smooth periodic test vanishes a.e. -/
theorem ae_eq_zero_of_forall_integral_mul_eq_zero {h : Torus d → ℝ} (hh : MemLp h 2 (haar d))
    (H : ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ → ∫ x, h x * φ x ∂haar d = 0) :
    h =ᵐ[haar d] 0 := by
  set ν : Measure (Torus d) :=
    Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle) with hνdef
  have hν : haar d = ν := haar_eq_pi_haarAddCircle d
  rw [hν] at hh H ⊢
  have hint : Integrable h ν := hh.integrable one_le_two
  have hcoef : ∀ n : Fin d → ℤ,
      UnitAddTorus.mFourierCoeff (d := Fin d) (fun x => (h x : ℂ)) n = 0 := by
    intro n
    set e := UnitAddTorus.mFourier (-n)
    have hI : Integrable (fun t => e t • (h t : ℂ)) ν := by
      simp only [smul_eq_mul]
      refine hint.ofReal.bdd_mul (c := 1) e.continuous.aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      calc ‖e t‖ ≤ ‖e‖ := e.norm_coe_le_norm t
        _ = 1 := UnitAddTorus.mFourier_norm
    have hre : ∫ t, h t * (e t).re ∂ν = 0 := H _ (isSmoothPeriodic_re_mFourier (-n))
    have him : ∫ t, h t * (e t).im ∂ν = 0 := H _ (isSmoothPeriodic_im_mFourier (-n))
    have h1 := Complex.reCLM.integral_comp_comm hI
    have h2 := Complex.imCLM.integral_comp_comm hI
    simp only [Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h1 h2
    have hdef : UnitAddTorus.mFourierCoeff (d := Fin d) (fun x => (h x : ℂ)) n
        = ∫ x, e x * (h x : ℂ) ∂ν := by
      simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]
      rfl
    rw [hdef]
    apply Complex.ext
    · rw [← h1, Complex.zero_re]
      simpa [mul_comm] using hre
    · rw [← h2, Complex.zero_im]
      simpa [mul_comm] using him
  have hc : MemLp (fun x => (h x : ℂ)) 2 ν := hh.ofReal
  have hf0 : hc.toLp _ = 0 := by
    rw [← LinearIsometryEquiv.map_eq_zero_iff UnitAddTorus.mFourierBasis.repr]
    ext n
    rw [UnitAddTorus.mFourierBasis_repr]
    calc UnitAddTorus.mFourierCoeff (d := Fin d) (hc.toLp _) n
        = UnitAddTorus.mFourierCoeff (d := Fin d) (fun x => (h x : ℂ)) n := by
          unfold UnitAddTorus.mFourierCoeff
          refine integral_congr_ae ?_
          filter_upwards [hc.coeFn_toLp] with x hx
          rw [hx]
      _ = 0 := hcoef n
      _ = _ := by simp
  have h2 : (fun x => (h x : ℂ)) =ᵐ[ν] 0 :=
    hc.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hf0)
  filter_upwards [h2] with x hx
  simpa using hx

/-! ### Uniqueness of weak gradients -/

theorem memLp_coord {g : Torus d → Tangent d} (hg : MemLp g 2 (haar d)) (j : Fin d) :
    MemLp (fun x => g x j) 2 (haar d) :=
  (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).comp_memLp' hg

/-- FOU001 uniqueness: two weak gradients of the same function agree a.e. -/
theorem IsWeakGradient.ae_eq {u : Torus d → ℝ} {g g' : Torus d → Tangent d}
    (hg : IsWeakGradient u g) (hg' : IsWeakGradient u g') : g =ᵐ[haar d] g' := by
  have hj : ∀ j : Fin d, (fun x => g x j - g' x j) =ᵐ[haar d] 0 := by
    intro j
    refine ae_eq_zero_of_forall_integral_mul_eq_zero
      ((memLp_coord hg.memLp_grad j).sub (memLp_coord hg'.memLp_grad j)) fun φ hφ => ?_
    have e1 := hg.ibp φ hφ j
    have e2 := hg'.ibp φ hφ j
    simp_rw [sub_mul]
    rw [integral_sub (integrable_mul_of_memLp_two (memLp_coord hg.memLp_grad j) hφ.memLp_top)
      (integrable_mul_of_memLp_two (memLp_coord hg'.memLp_grad j) hφ.memLp_top)]
    linarith
  filter_upwards [ae_all_iff.mpr hj] with x hx
  ext j
  simpa [sub_eq_zero] using hx j

/-- The chosen weak gradient agrees a.e. with every weak gradient. -/
theorem weakGradient_ae_eq {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradient u g) : weakGradient u ⟨g, hg⟩ =ᵐ[haar d] g :=
  (isWeakGradient_weakGradient ⟨g, hg⟩).ae_eq hg

/-! ### Linearity and a.e. invariance -/

theorem IsWeakGradient.integrable_left {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (j : Fin d) :
    Integrable (fun x => u x * coordPartial j φ x) (haar d) :=
  integrable_mul_of_memLp_two h.memLp (hφ.memLp_top_coordPartial j)

theorem IsWeakGradient.integrable_right {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (j : Fin d) :
    Integrable (fun x => g x j * φ x) (haar d) :=
  integrable_mul_of_memLp_two (memLp_coord h.memLp_grad j) hφ.memLp_top

theorem IsWeakGradient.congr_ae {u u' : Torus d → ℝ} {g g' : Torus d → Tangent d}
    (h : IsWeakGradient u g) (hu : u =ᵐ[haar d] u') (hg : g =ᵐ[haar d] g') :
    IsWeakGradient u' g' where
  memLp := h.memLp.ae_eq hu
  memLp_grad := h.memLp_grad.ae_eq hg
  ibp φ hφ j := by
    calc ∫ x, u' x * coordPartial j φ x ∂haar d = ∫ x, u x * coordPartial j φ x ∂haar d :=
          integral_congr_ae (hu.mono fun x hx => by simp only [hx])
      _ = -∫ x, g x j * φ x ∂haar d := h.ibp φ hφ j
      _ = -∫ x, g' x j * φ x ∂haar d := by
          congr 1
          exact integral_congr_ae (hg.mono fun x hx => by simp only [hx])

theorem isWeakGradient_zero : IsWeakGradient (fun _ : Torus d => (0 : ℝ)) (fun _ => 0) where
  memLp := memLp_const 0
  memLp_grad := memLp_const 0
  ibp φ _ j := by simp

theorem IsWeakGradient.add {u v : Torus d → ℝ} {g k : Torus d → Tangent d}
    (hg : IsWeakGradient u g) (hk : IsWeakGradient v k) :
    IsWeakGradient (fun x => u x + v x) (fun x => g x + k x) where
  memLp := hg.memLp.add hk.memLp
  memLp_grad := hg.memLp_grad.add hk.memLp_grad
  ibp φ hφ j := by
    have e1 := hg.ibp φ hφ j
    have e2 := hk.ibp φ hφ j
    simp only [PiLp.add_apply, add_mul]
    rw [integral_add (hg.integrable_left hφ j) (hk.integrable_left hφ j),
      integral_add (hg.integrable_right hφ j) (hk.integrable_right hφ j)]
    linarith

theorem IsWeakGradient.smul {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradient u g) (c : ℝ) :
    IsWeakGradient (fun x => c * u x) (fun x => c • g x) where
  memLp := hg.memLp.const_mul c
  memLp_grad := hg.memLp_grad.const_smul c
  ibp φ hφ j := by
    have e := hg.ibp φ hφ j
    simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, integral_const_mul, e]
    ring

/-! ### The graph as a closed subspace -/

/-- The ambient Hilbert space `L²(m) × L²(m; ℝ^d)` with `‖(u, g)‖² = ‖u‖₂² + ‖g‖₂²`. -/
abbrev H1Ambient (d : ℕ) := WithLp 2 (Lp ℝ 2 (haar d) × Lp (Tangent d) 2 (haar d))

/-- The weak-gradient graph `{(u, g) | g is a weak gradient of u}` (FOU001). -/
noncomputable def h1Graph (d : ℕ) : Submodule ℝ (H1Ambient d) where
  carrier := {p | IsWeakGradient (p.ofLp.1 : Torus d → ℝ) (p.ofLp.2 : Torus d → Tangent d)}
  zero_mem' := isWeakGradient_zero.congr_ae (Lp.coeFn_zero _ _ _).symm (Lp.coeFn_zero _ _ _).symm
  add_mem' {a b} ha hb :=
    (IsWeakGradient.add ha hb).congr_ae (Lp.coeFn_add _ _).symm (Lp.coeFn_add _ _).symm
  smul_mem' c p hp := by
    exact (hp.smul c).congr_ae (Lp.coeFn_smul c p.ofLp.1).symm (Lp.coeFn_smul c p.ofLp.2).symm

theorem mem_h1Graph {p : H1Ambient d} :
    p ∈ h1Graph d ↔ IsWeakGradient (p.ofLp.1 : Torus d → ℝ) (p.ofLp.2 : Torus d → Tangent d) := by
  rfl

/-- Pairing an `L²` class with a bounded test is continuous. -/
theorem continuous_integral_mul {ψ : Torus d → ℝ} (hψ : MemLp ψ ∞ (haar d)) :
    Continuous fun U : Lp ℝ 2 (haar d) => ∫ x, U x * ψ x ∂haar d := by
  have hψ2 : MemLp ψ 2 (haar d) := hψ.mono_exponent le_top
  have : (fun U : Lp ℝ 2 (haar d) => ∫ x, U x * ψ x ∂haar d)
      = fun U => inner ℝ (hψ2.toLp ψ) U := by
    funext U
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψ2.coeFn_toLp] with x hx
    simp [hx, mul_comm]
  rw [this]
  exact continuous_const.inner continuous_id

theorem isClosed_h1Graph : IsClosed (h1Graph d : Set (H1Ambient d)) := by
  have hset : (h1Graph d : Set (H1Ambient d)) =
      ⋂ φ : {φ : Torus d → ℝ // IsSmoothPeriodic φ}, ⋂ j : Fin d,
        {p : H1Ambient d | ∫ x, (p.ofLp.1 : Torus d → ℝ) x * coordPartial j φ.1 x ∂haar d
          + ∫ x, ((EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).compLp p.ofLp.2 : Torus d → ℝ) x
              * φ.1 x ∂haar d = 0} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe, mem_h1Graph]
    have hc : ∀ (φ : Torus d → ℝ) (j : Fin d),
        ∫ x, ((EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).compLp p.ofLp.2 : Torus d → ℝ) x
          * φ x ∂haar d = ∫ x, (p.ofLp.2 : Torus d → Tangent d) x j * φ x ∂haar d :=
      fun φ j => integral_congr_ae <|
        ((EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).coeFn_compLp p.ofLp.2).mono
          fun x hx => by beta_reduce; rw [hx]; rfl
    constructor
    · intro hp φ j
      rw [hc, hp.ibp φ.1 φ.2 j]
      ring
    · intro hp
      refine ⟨Lp.memLp _, Lp.memLp _, fun φ hφ j => ?_⟩
      have := hp ⟨φ, hφ⟩ j
      rw [hc] at this
      linarith
  rw [hset]
  refine isClosed_iInter fun φ => isClosed_iInter fun j => isClosed_eq ?_ continuous_const
  have h1 : Continuous fun p : H1Ambient d => p.ofLp.1 :=
    continuous_fst.comp (WithLp.prod_continuous_ofLp _ _ _)
  have h2 : Continuous fun p : H1Ambient d =>
      (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).compLp p.ofLp.2 :=
    ((EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).compLpL 2 (haar d)).continuous.comp
      (continuous_snd.comp (WithLp.prod_continuous_ofLp _ _ _))
  exact ((continuous_integral_mul (φ.2.memLp_top_coordPartial j)).comp h1).add
    ((continuous_integral_mul φ.2.memLp_top).comp h2)

instance : CompleteSpace (h1Graph d) := isClosed_h1Graph.completeSpace_coe

/-- The `H¹` norm on the graph: `‖(u, g)‖² = ‖u‖₂² + ‖g‖₂²`. -/
theorem h1Ambient_norm_sq (p : H1Ambient d) :
    ‖p‖ ^ 2 = ‖p.ofLp.1‖ ^ 2 + ‖p.ofLp.2‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 p

/-- The weak-gradient operator is closed: `L²` limits of graph points are graph points. -/
theorem IsWeakGradient.of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : ι → Lp ℝ 2 (haar d)} {G : ι → Lp (Tangent d) 2 (haar d)}
    {u : Lp ℝ 2 (haar d)} {g : Lp (Tangent d) 2 (haar d)}
    (hU : Tendsto U l (𝓝 u)) (hG : Tendsto G l (𝓝 g))
    (h : ∀ᶠ n in l, IsWeakGradient (U n : Torus d → ℝ) (G n : Torus d → Tangent d)) :
    IsWeakGradient (u : Torus d → ℝ) (g : Torus d → Tangent d) := by
  have ht : Tendsto (fun n => WithLp.toLp 2 (U n, G n)) l (𝓝 (WithLp.toLp 2 (u, g))) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.tendsto _).comp
      (hU.prodMk_nhds hG)
  exact (mem_h1Graph (p := WithLp.toLp 2 (u, g))).mp
    (isClosed_h1Graph.mem_of_tendsto ht (h.mono fun n hn => mem_h1Graph.mpr hn))

end DGPS

namespace DGPS.Analysis

open DGPS

/-- FOU001: on the unit torus, weak gradients are unique a.e.; the weak-gradient graph in
`L²(m) × L²(m; ℝ^d)` is a closed subspace, complete (a Hilbert space) for
`‖(u, g)‖² = ‖u‖₂² + ‖g‖₂²`; and the weak-gradient operator is closed. -/
theorem periodic_weak_sobolev_graph (d : ℕ) :
    (∀ {u : Torus d → ℝ} {g g' : Torus d → Tangent d},
      IsWeakGradient u g → IsWeakGradient u g' → g =ᵐ[haar d] g') ∧
    IsClosed (h1Graph d : Set (H1Ambient d)) ∧
    CompleteSpace (h1Graph d) ∧
    (∀ p : H1Ambient d, ‖p‖ ^ 2 = ‖p.ofLp.1‖ ^ 2 + ‖p.ofLp.2‖ ^ 2) ∧
    (∀ (U : ℕ → Lp ℝ 2 (haar d)) (G : ℕ → Lp (Tangent d) 2 (haar d))
      (u : Lp ℝ 2 (haar d)) (g : Lp (Tangent d) 2 (haar d)),
      Tendsto U atTop (𝓝 u) → Tendsto G atTop (𝓝 g) →
      (∀ n, IsWeakGradient (U n : Torus d → ℝ) (G n : Torus d → Tangent d)) →
      IsWeakGradient (u : Torus d → ℝ) (g : Torus d → Tangent d)) :=
  ⟨fun hg hg' => hg.ae_eq hg', isClosed_h1Graph, inferInstance, h1Ambient_norm_sq,
    fun _ _ _ _ hU hG h => IsWeakGradient.of_tendsto hU hG (Eventually.of_forall h)⟩

end DGPS.Analysis
