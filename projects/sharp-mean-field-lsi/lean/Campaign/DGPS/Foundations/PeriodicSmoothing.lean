import DGPS.Foundations.SmoothingLp
import DGPS.Foundations.WeakSobolev
import SharpSymmetricLSI.Paper.FourierPoincare

/-!
# Periodic smoothing and Sobolev density (FOU002)

INTERFACES/common_lemmas.md FOU002. The periodic smoothing operators are the legacy torus
mollifiers `SharpLSI.moll n` (`DGPS/Foundations/SmoothingLp.lean`): convolution through the
periodic lift with `φₙ = SharpLSI.phiSeq n`, a nonnegative `C^∞` bump of integral one supported in
the sup-norm ball of radius `εₙ = 2/(n+2)` of `ℝ^d` (route deviation RD-004: the family is indexed
by `n`, `εₙ → 0`).

* kernel facts: `phiSeq_support`, nonnegativity, unit mass, smoothness;
* `isSmoothPeriodic_moll`: `moll n f` is smooth periodic for integrable `f`;
* `integral_mul_coordPartial_of_smooth`: integration by parts for smooth periodic functions;
* `mFourierCoeff_moll`: the Fourier coefficients of `moll n f` are those of `f` times the
  kernel's;
* `IsWeakGradientLp.coordPartial_moll`: for a weak gradient `g` of `u` in `Lᵖ`, `∂ⱼ (moll n u) = moll n gⱼ`;
* `IsWeakGradientLp p u g`: weak gradient in `Lᵖ` (for `p = 2` it is `IsWeakGradient`);
* `tendsto_moll_W1p`: `moll n u → u` in `W^{1,p}`, `1 ≤ p < ∞`;
* `exists_smooth_tendsto_H1`: smooth periodic functions are dense in `H¹`;
* `DGPS.Analysis.periodic_smoothing_and_sobolev_density`: the FOU002 bundle.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace DGPS

variable {d : ℕ}

/-! ### The smoothing kernel -/

theorem phiSeq_support (n : ℕ) :
    Function.support (SharpLSI.phiSeq (ι := Fin d) n) = Metric.ball 0 (2 / ((n : ℝ) + 2)) :=
  ContDiffBump.support_normed_eq _

theorem phiSeq_nonneg (n : ℕ) (s : Fin d → ℝ) : 0 ≤ SharpLSI.phiSeq n s :=
  SharpLSI.phiSeq_nonneg n s

theorem integral_phiSeq (n : ℕ) : ∫ s : Fin d → ℝ, SharpLSI.phiSeq n s = 1 :=
  SharpLSI.integral_phiSeq n

theorem contDiff_phiSeq (n : ℕ) : ContDiff ℝ ∞ (SharpLSI.phiSeq (ι := Fin d) n) :=
  SharpLSI.contDiff_phiSeq n

theorem integrable_phiSeq (n : ℕ) : Integrable (SharpLSI.phiSeq (ι := Fin d) n) :=
  (contDiff_phiSeq n).continuous.integrable_of_hasCompactSupport
    (SharpLSI.hasCompactSupport_phiSeq n)

/-! ### Smooth periodic functions -/

theorem continuous_of_comp_torusLift {X : Type*} [TopologicalSpace X] {f : Torus d → X}
    (h : Continuous (f ∘ torusLift)) : Continuous f :=
  (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff.mp h

theorem IsSmoothPeriodic.continuous_torus {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    Continuous φ :=
  continuous_of_comp_torusLift hφ.continuous

theorem IsSmoothPeriodic.mul {v φ : Torus d → ℝ} (hv : IsSmoothPeriodic v)
    (hφ : IsSmoothPeriodic φ) : IsSmoothPeriodic (fun x => v x * φ x) :=
  ContDiff.mul hv hφ

theorem coordPartial_comp_torusLift (j : Fin d) (φ : Torus d → ℝ) :
    coordPartial j φ ∘ torusLift = fun x => fderiv ℝ (φ ∘ torusLift) x (Pi.single j 1) := by
  funext x
  show fderiv ℝ (φ ∘ SharpLSI.liftT) (SharpLSI.secT (SharpLSI.liftT x)) (Pi.single j 1) =
    fderiv ℝ (φ ∘ SharpLSI.liftT) x (Pi.single j 1)
  rw [SharpLSI.fderiv_lift_secT]

theorem IsSmoothPeriodic.isSmoothPeriodic_coordPartial {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) (j : Fin d) :
    IsSmoothPeriodic (coordPartial j φ) := by
  unfold IsSmoothPeriodic
  rw [coordPartial_comp_torusLift]
  exact (hφ.fderiv_right (by norm_cast)).clm_apply contDiff_const

theorem IsSmoothPeriodic.continuous_coordPartial {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ)
    (j : Fin d) : Continuous (coordPartial j φ) :=
  (hφ.isSmoothPeriodic_coordPartial j).continuous_torus

/-- Integration by parts for smooth periodic functions. -/
theorem integral_mul_coordPartial_of_smooth {v φ : Torus d → ℝ} (hv : IsSmoothPeriodic v)
    (hφ : IsSmoothPeriodic φ) (j : Fin d) :
    ∫ x, v x * coordPartial j φ x ∂haar d = -∫ x, coordPartial j v x * φ x ∂haar d := by
  have hW : ContDiff ℝ 1 ((fun x => v x * φ x) ∘ SharpLSI.liftT) :=
    (hv.mul hφ).of_le (by exact_mod_cast le_top)
  have h0 := SharpLSI.integral_fderiv_torus_eq_zero hW (Pi.single j 1)
  have hpt : ∀ y : Torus d,
      fderiv ℝ ((fun x => v x * φ x) ∘ SharpLSI.liftT) (SharpLSI.secT y) (Pi.single j 1)
        = v y * coordPartial j φ y + coordPartial j v y * φ y := by
    intro y
    have hv1 : DifferentiableAt ℝ (v ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
      (hv.differentiable (by simp)) _
    have hφ1 : DifferentiableAt ℝ (φ ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
      (hφ.differentiable (by simp)) _
    have : ((fun x => v x * φ x) ∘ SharpLSI.liftT) =
        fun x => (v ∘ SharpLSI.liftT) x * (φ ∘ SharpLSI.liftT) x := rfl
    rw [this, fderiv_fun_mul hv1 hφ1]
    simp only [add_apply, smul_apply, smul_eq_mul,
      Function.comp_apply, SharpLSI.liftT_secT, DGPS.coordPartial]
    ring
  simp_rw [hpt] at h0
  have i1 : Integrable (fun x => v x * coordPartial j φ x) (haar d) :=
    integrable_mul_of_memLp_two (hv.memLp_top.mono_exponent le_top)
      (hφ.memLp_top_coordPartial j)
  have i2 : Integrable (fun x => coordPartial j v x * φ x) (haar d) :=
    integrable_mul_of_memLp_two ((hv.memLp_top_coordPartial j).mono_exponent le_top)
      hφ.memLp_top
  have h3 := integral_add i1 i2
  have h4 : ∫ x, (v x * coordPartial j φ x + coordPartial j v x * φ x) ∂haar d = 0 := h0
  linarith

/-! ### The mollifier as an integral, and characters -/

theorem moll_apply_eq (n : ℕ) (f : Torus d → ℝ) (y : Torus d) :
    SharpLSI.moll n f y = ∫ s, SharpLSI.phiSeq n s * f (y - torusLift s) := by
  simp only [SharpLSI.moll, SharpLSI.mollL_apply', Function.comp_apply, SharpLSI.liftT_sub,
    SharpLSI.liftT_secT, torusLift]

theorem mFourier_add_pt (k : Fin d → ℤ) (a b : Torus d) :
    UnitAddTorus.mFourier k (a + b) = UnitAddTorus.mFourier k a * UnitAddTorus.mFourier k b := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem norm_mFourier_apply (k : Fin d → ℤ) (t : Torus d) : ‖UnitAddTorus.mFourier k t‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod]
  exact Finset.prod_eq_one fun i _ => by simp [fourier_apply]


/-! ### Fourier coefficients of weak derivatives and of mollifications -/

theorem coordPartial_re_mFourier (k : Fin d → ℤ) (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => (UnitAddTorus.mFourier k y).re) x =
      (2 * π * Complex.I * (k j : ℂ) * UnitAddTorus.mFourier k x).re := by
  have hF := (contDiff_mFourier_torusLift (d := d) k).differentiable (by simp) (SharpLSI.secT x)
  show fderiv ℝ (Complex.reCLM ∘ fun y => UnitAddTorus.mFourier k (SharpLSI.liftT y))
    (SharpLSI.secT x) (Pi.single j 1) = _
  rw [(Complex.reCLM.hasFDerivAt.comp _ hF.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [SharpLSI.fderiv_mFourier_liftT, SharpLSI.liftT_secT]
  rfl

theorem coordPartial_im_mFourier (k : Fin d → ℤ) (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => (UnitAddTorus.mFourier k y).im) x =
      (2 * π * Complex.I * (k j : ℂ) * UnitAddTorus.mFourier k x).im := by
  have hF := (contDiff_mFourier_torusLift (d := d) k).differentiable (by simp) (SharpLSI.secT x)
  show fderiv ℝ (Complex.imCLM ∘ fun y => UnitAddTorus.mFourier k (SharpLSI.liftT y))
    (SharpLSI.secT x) (Pi.single j 1) = _
  rw [(Complex.imCLM.hasFDerivAt.comp _ hF.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [SharpLSI.fderiv_mFourier_liftT, SharpLSI.liftT_secT]
  rfl

theorem integrable_mFourier_mul {u : Torus d → ℝ} (hu : Integrable u (haar d)) (k : Fin d → ℤ) :
    Integrable (fun x => UnitAddTorus.mFourier k x * (u x : ℂ)) (haar d) :=
  Integrable.mono' hu.norm
    ((UnitAddTorus.mFourier k).continuous.aestronglyMeasurable.mul
      hu.ofReal.aestronglyMeasurable)
    (Eventually.of_forall fun x => by simp [norm_mFourier_apply])

/-- The weak-derivative identity, tested on characters, is the Fourier relation
`ĝ(k) = 2πi kⱼ û(k)`. -/
theorem mFourierCoeff_of_ibp {u g : Torus d → ℝ} (hu : Integrable u (haar d))
    (hg : Integrable g (haar d)) (j : Fin d)
    (H : ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ →
      ∫ x, u x * coordPartial j φ x ∂haar d = -∫ x, g x * φ x ∂haar d) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun y => (g y : ℂ)) k =
      2 * π * Complex.I * (k j : ℂ) * UnitAddTorus.mFourierCoeff (fun y => (u y : ℂ)) k := by
  set c : ℂ := 2 * π * Complex.I * (((-k) j : ℤ) : ℂ) with hc
  have hA : UnitAddTorus.mFourierCoeff (fun y => (u y : ℂ)) k = ∫ x, UnitAddTorus.mFourier (-k) x * (u x : ℂ) ∂haar d := by
    rw [haar_eq_pi_haarAddCircle]; simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]; rfl
  have hB : UnitAddTorus.mFourierCoeff (fun y => (g y : ℂ)) k = ∫ x, UnitAddTorus.mFourier (-k) x * (g x : ℂ) ∂haar d := by
    rw [haar_eq_pi_haarAddCircle]; simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]; rfl
  have iu := integrable_mFourier_mul hu (-k)
  have ig := integrable_mFourier_mul hg (-k)
  have hre := H _ (isSmoothPeriodic_re_mFourier (-k))
  have him := H _ (isSmoothPeriodic_im_mFourier (-k))
  simp_rw [coordPartial_re_mFourier, coordPartial_im_mFourier] at hre him
  have key : c * ∫ x, UnitAddTorus.mFourier (-k) x * (u x : ℂ) ∂haar d = -∫ x, UnitAddTorus.mFourier (-k) x * (g x : ℂ) ∂haar d := by
    rw [← integral_const_mul]
    have r1 : ∀ f : Torus d → ℂ, Integrable f (haar d) →
        (∫ x, f x ∂haar d).re = ∫ x, (f x).re ∂haar d := fun f hf => by
      have := integral_re hf; simp only [RCLike.re_to_complex] at this; exact this.symm
    have i1 : ∀ f : Torus d → ℂ, Integrable f (haar d) →
        (∫ x, f x ∂haar d).im = ∫ x, (f x).im ∂haar d := fun f hf => by
      have := integral_im hf; simp only [RCLike.im_to_complex] at this; exact this.symm
    apply Complex.ext
    · rw [Complex.neg_re, r1 _ (iu.const_mul c), r1 _ ig]
      have e1 : ∀ x, (c * (UnitAddTorus.mFourier (-k) x * (u x : ℂ))).re = u x * (c * UnitAddTorus.mFourier (-k) x).re := fun x => by
        rw [show c * (UnitAddTorus.mFourier (-k) x * (u x : ℂ)) = (u x : ℂ) * (c * UnitAddTorus.mFourier (-k) x) by ring, Complex.re_ofReal_mul]
      have e2 : ∀ x, (UnitAddTorus.mFourier (-k) x * (g x : ℂ)).re = g x * (UnitAddTorus.mFourier (-k) x).re := fun x => by
        rw [mul_comm, Complex.re_ofReal_mul]
      rw [integral_congr_ae (Eventually.of_forall e1), integral_congr_ae (Eventually.of_forall e2)]
      exact hre
    · rw [Complex.neg_im, i1 _ (iu.const_mul c), i1 _ ig]
      have e1 : ∀ x, (c * (UnitAddTorus.mFourier (-k) x * (u x : ℂ))).im = u x * (c * UnitAddTorus.mFourier (-k) x).im := fun x => by
        rw [show c * (UnitAddTorus.mFourier (-k) x * (u x : ℂ)) = (u x : ℂ) * (c * UnitAddTorus.mFourier (-k) x) by ring, Complex.im_ofReal_mul]
      have e2 : ∀ x, (UnitAddTorus.mFourier (-k) x * (g x : ℂ)).im = g x * (UnitAddTorus.mFourier (-k) x).im := fun x => by
        rw [mul_comm, Complex.im_ofReal_mul]
      rw [integral_congr_ae (Eventually.of_forall e1), integral_congr_ae (Eventually.of_forall e2)]
      exact him
  rw [hA, hB]
  have : c = -(2 * π * Complex.I * (k j : ℂ)) := by
    rw [hc]; simp only [Pi.neg_apply, Int.cast_neg]; ring
  rw [this] at key
  linear_combination key


theorem mFourierCoeff_ofReal_eq (f : Torus d → ℝ) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) k =
      ∫ x, UnitAddTorus.mFourier (-k) x * (f x : ℂ) ∂haar d := by
  rw [haar_eq_pi_haarAddCircle]; simp only [UnitAddTorus.mFourierCoeff, smul_eq_mul]; rfl

/-- The Fourier coefficients of the smoothing kernel, `∫ φₙ(s) e^{-2πi k·s} ds`. -/
noncomputable def kernelCoeff (n : ℕ) (k : Fin d → ℤ) : ℂ :=
  ∫ s : Fin d → ℝ, (SharpLSI.phiSeq n s : ℂ) * UnitAddTorus.mFourier (-k) (torusLift s)

theorem mFourierCoeff_moll_of_stronglyMeasurable (n : ℕ) {f : Torus d → ℝ}
    (hf : Integrable f (haar d)) (hfm : StronglyMeasurable f) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun y => (SharpLSI.moll n f y : ℂ)) k =
      kernelCoeff n k * UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) k := by
  rw [mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq]
  set e := UnitAddTorus.mFourier (-k)
  set φ := SharpLSI.phiSeq (ι := Fin d) n
  set F : Torus d → (Fin d → ℝ) → ℂ := fun y s => (φ s : ℂ) * (e y * (f (y - torusLift s) : ℂ))
  have hcont : Continuous fun p : Torus d × (Fin d → ℝ) => p.1 - torusLift p.2 :=
    continuous_fst.sub (SharpLSI.continuous_liftT.comp continuous_snd)
  have hFm : AEStronglyMeasurable (Function.uncurry F) ((haar d).prod volume) := by
    have h1 : StronglyMeasurable fun p : Torus d × (Fin d → ℝ) => f (p.1 - torusLift p.2) :=
      hfm.comp_measurable hcont.measurable
    have h2 : Continuous fun p : Torus d × (Fin d → ℝ) => ((φ p.2 : ℂ) * e p.1) :=
      (Complex.continuous_ofReal.comp ((contDiff_phiSeq n).continuous.comp continuous_snd)).mul
        (e.continuous.comp continuous_fst)
    have := (h2.aestronglyMeasurable (μ := (haar d).prod volume)).mul (Complex.continuous_ofReal.comp_stronglyMeasurable h1).aestronglyMeasurable
    refine this.congr (Eventually.of_forall fun p => ?_)
    obtain ⟨y, s⟩ := p
    simp only [Pi.mul_apply, Function.uncurry_apply_pair, F]
    ring
  have hslice : ∀ s, Integrable (fun y => e y * (f (y - torusLift s) : ℂ)) (haar d) := fun s =>
    integrable_mFourier_mul (hf.comp_sub_right (torusLift s)) (-k)
  have hnorm : ∀ s, ∫ y, ‖F y s‖ ∂haar d = φ s * ∫ y, |f y| ∂haar d := fun s => by
    have : ∀ y, ‖F y s‖ = φ s * |f (y - torusLift s)| := fun y => by
      have he : ‖e y‖ = 1 := norm_mFourier_apply _ y
      simp [F, he, abs_of_nonneg (phiSeq_nonneg n s), φ]
    simp_rw [this]
    rw [integral_const_mul, integral_sub_right_eq_self (fun y => |f y|)]
  have hF : Integrable (Function.uncurry F) ((haar d).prod volume) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨Eventually.of_forall fun s => (show Integrable (fun y => F y s) (haar d) from (hslice s).const_mul _), ?_⟩
    simp only [Function.uncurry_apply_pair]
    simp_rw [hnorm]
    exact (integrable_phiSeq n).mul_const _
  have hinner : ∀ s, ∫ y, e y * (f (y - torusLift s) : ℂ) ∂haar d =
      e (torusLift s) * ∫ y, e y * (f y : ℂ) ∂haar d := fun s => by
    have := integral_sub_right_eq_self
      (μ := haar d) (fun y => e (y + torusLift s) * (f y : ℂ)) (torusLift s)
    simp only [sub_add_cancel] at this
    rw [this, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [e, mFourier_add_pt]; ring
  calc ∫ y, e y * (SharpLSI.moll n f y : ℂ) ∂haar d
      = ∫ y, (∫ s, F y s) ∂haar d := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [moll_apply_eq, F]
        rw [← integral_complex_ofReal, ← integral_const_mul]
        congr 1; funext s; push_cast; ring
    _ = ∫ s, ∫ y, F y s ∂haar d := integral_integral_swap hF
    _ = ∫ s, (φ s : ℂ) * e (torusLift s) * ∫ y, e y * (f y : ℂ) ∂haar d := by
        congr 1; funext s
        simp only [F]
        rw [integral_const_mul, hinner, mul_assoc]
    _ = kernelCoeff n k * ∫ y, e y * (f y : ℂ) ∂haar d := by
        rw [integral_mul_const]; rfl

theorem mFourierCoeff_moll (n : ℕ) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff (fun y => (SharpLSI.moll n f y : ℂ)) k =
      kernelCoeff n k * UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) k := by
  have hae := hf.1.ae_eq_mk
  have h1 : SharpLSI.moll n f = SharpLSI.moll n (hf.1.mk f) := SharpLSI.moll_congr_ae n hae
  have h2 := mFourierCoeff_moll_of_stronglyMeasurable n (hf.congr hae) hf.1.stronglyMeasurable_mk k
  rw [h1, h2, mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq f]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

/-! ### Smoothness, derivative commutation, `W^{1,p}` convergence, `H¹` density -/

theorem isSmoothPeriodic_moll (n : ℕ) {f : Torus d → ℝ} (hf : Integrable f (haar d)) :
    IsSmoothPeriodic (SharpLSI.moll n f) :=
  SharpLSI.moll_comp_liftT_contDiff n hf

/-- An `L²` function whose Fourier coefficients all vanish is zero a.e. -/
theorem ae_eq_zero_of_mFourierCoeff_eq_zero {h : Torus d → ℝ} (hh : MemLp h 2 (haar d))
    (hcoef : ∀ k : Fin d → ℤ, UnitAddTorus.mFourierCoeff (fun x => (h x : ℂ)) k = 0) :
    h =ᵐ[haar d] 0 := by
  set ν : Measure (Torus d) :=
    Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle) with hνdef
  have hν : haar d = ν := haar_eq_pi_haarAddCircle d
  rw [hν] at hh ⊢
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

theorem memLp_two_of_continuous {h : Torus d → ℝ} (hc : Continuous h) : MemLp h 2 (haar d) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact (memLp_top_of_bound hc.aestronglyMeasurable C
    (Eventually.of_forall fun x => hC x (mem_univ x))).mono_exponent le_top

/-- `∂ⱼ (moll n u) = moll n gⱼ` whenever `gⱼ` is an integrable weak `j`-th derivative of the
integrable function `u` (tested against smooth periodic functions). -/
theorem coordPartial_moll_of_ibp {u gj : Torus d → ℝ} (hu1 : Integrable u (haar d))
    (hg1 : Integrable gj (haar d)) (j : Fin d)
    (H : ∀ φ, IsSmoothPeriodic φ →
      ∫ x, u x * coordPartial j φ x ∂haar d = -∫ x, gj x * φ x ∂haar d) (n : ℕ) :
    coordPartial j (SharpLSI.moll n u) = SharpLSI.moll n gj := by
  have hS := isSmoothPeriodic_moll n hu1
  have hT := isSmoothPeriodic_moll n hg1
  have hc1 := hS.continuous_coordPartial j
  have hc2 := hT.continuous_torus
  have hi1 : Integrable (coordPartial j (SharpLSI.moll n u)) (haar d) :=
    hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (SharpLSI.moll n gj) (haar d) :=
    hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcoef : ∀ k, UnitAddTorus.mFourierCoeff (fun x =>
      ((coordPartial j (SharpLSI.moll n u) x - SharpLSI.moll n gj x : ℝ) : ℂ)) k = 0 := by
    intro k
    have e1 := mFourierCoeff_of_ibp (hS.continuous_torus.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) hi1 j
      (fun φ hφ => integral_mul_coordPartial_of_smooth hS hφ j) k
    have e2 := mFourierCoeff_of_ibp hu1 hg1 j H k
    rw [mFourierCoeff_moll n hu1] at e1
    have e3 := mFourierCoeff_moll n hg1 k
    have hsplit : UnitAddTorus.mFourierCoeff (fun x =>
        ((coordPartial j (SharpLSI.moll n u) x - SharpLSI.moll n gj x : ℝ) : ℂ)) k
        = UnitAddTorus.mFourierCoeff (fun x => (coordPartial j (SharpLSI.moll n u) x : ℂ)) k -
          UnitAddTorus.mFourierCoeff (fun x => (SharpLSI.moll n gj x : ℂ)) k := by
      rw [mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq,
        ← integral_sub (integrable_mFourier_mul hi1 _) (integrable_mFourier_mul hi2 _)]
      congr 1; funext x; push_cast; ring
    rw [hsplit, e1, e3, e2]
    ring
  have hae := ae_eq_zero_of_mFourierCoeff_eq_zero (memLp_two_of_continuous (hc1.sub hc2)) hcoef
  have := (hc1.sub hc2).ae_eq_iff_eq (μ := haar d) continuous_const |>.mp hae
  funext x
  exact sub_eq_zero.mp (congrFun this x)

/-- A weak gradient in `Lᵖ`: `u ∈ Lᵖ`, `g ∈ Lᵖ(m; ℝ^d)` and `∫ u ∂ⱼφ = -∫ gⱼ φ` for every smooth
periodic `φ`. For `p = 2` this is `IsWeakGradient` (`isWeakGradient_iff_isWeakGradientLp`). -/
structure IsWeakGradientLp (p : ℝ≥0∞) (u : Torus d → ℝ) (g : Torus d → Tangent d) : Prop where
  memLp : MemLp u p (haar d)
  memLp_grad : MemLp g p (haar d)
  ibp : ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ → ∀ j : Fin d,
    ∫ x, u x * coordPartial j φ x ∂haar d = -∫ x, g x j * φ x ∂haar d

theorem isWeakGradient_iff_isWeakGradientLp {u : Torus d → ℝ} {g : Torus d → Tangent d} :
    IsWeakGradient u g ↔ IsWeakGradientLp 2 u g :=
  ⟨fun h => ⟨h.memLp, h.memLp_grad, h.ibp⟩, fun h => ⟨h.memLp, h.memLp_grad, h.ibp⟩⟩

theorem memLp_coord_of_memLp {p : ℝ≥0∞} {g : Torus d → Tangent d} (hg : MemLp g p (haar d))
    (j : Fin d) : MemLp (fun x => g x j) p (haar d) :=
  (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).comp_memLp' hg

/-- Derivatives commute with the smoothing: `∂ⱼ (moll n u) = moll n gⱼ`. -/
theorem IsWeakGradientLp.coordPartial_moll {p : ℝ≥0∞} (hp : 1 ≤ p) {u : Torus d → ℝ}
    {g : Torus d → Tangent d} (hg : IsWeakGradientLp p u g) (n : ℕ) (j : Fin d) :
    coordPartial j (SharpLSI.moll n u) = SharpLSI.moll n (fun x => g x j) :=
  coordPartial_moll_of_ibp (hg.memLp.integrable hp)
    ((memLp_coord_of_memLp hg.memLp_grad j).integrable hp) j (fun φ hφ => hg.ibp φ hφ j) n

theorem coordPartial_moll {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradient u g) (n : ℕ) (j : Fin d) :
    coordPartial j (SharpLSI.moll n u) = SharpLSI.moll n (fun x => g x j) :=
  (isWeakGradient_iff_isWeakGradientLp.mp hg).coordPartial_moll one_le_two n j

/-- `W^{1,p}` convergence of the smoothing, `1 ≤ p < ∞`. -/
theorem tendsto_moll_W1p {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ (∞ : ℝ≥0∞)) {u : Torus d → ℝ}
    {g : Torus d → Tangent d} (hg : IsWeakGradientLp p u g) :
    Tendsto (fun n => eLpNorm (fun x => SharpLSI.moll n u x - u x) p (haar d)) atTop (𝓝 0) ∧
      ∀ j : Fin d, Tendsto (fun n => eLpNorm
        (fun x => coordPartial j (SharpLSI.moll n u) x - g x j) p (haar d)) atTop (𝓝 0) := by
  refine ⟨tendsto_eLpNorm_moll_sub hp hp' hg.memLp, fun j => ?_⟩
  simp_rw [hg.coordPartial_moll hp]
  exact tendsto_eLpNorm_moll_sub hp hp' (memLp_coord_of_memLp hg.memLp_grad j)

/-- The classical gradient of a smooth periodic function, as a tangent vector. -/
noncomputable def smoothGrad (φ : Torus d → ℝ) (x : Torus d) : Tangent d :=
  WithLp.toLp 2 fun j => coordPartial j φ x

@[simp] theorem smoothGrad_apply (φ : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    smoothGrad φ x j = coordPartial j φ x := rfl

theorem IsSmoothPeriodic.continuous_smoothGrad {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    Continuous (smoothGrad φ) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => hφ.continuous_coordPartial j)

/-- A smooth periodic function is in `H¹` with its classical gradient. -/
theorem IsSmoothPeriodic.isWeakGradient {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    IsWeakGradient φ (smoothGrad φ) where
  memLp := hφ.memLp_top.mono_exponent le_top
  memLp_grad := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      hφ.continuous_smoothGrad.continuousOn
    exact (memLp_top_of_bound hφ.continuous_smoothGrad.aestronglyMeasurable C
      (Eventually.of_forall fun x => hC x (mem_univ x))).mono_exponent le_top
  ibp ψ hψ j := integral_mul_coordPartial_of_smooth hφ hψ j

/-- Smooth periodic functions are dense in `H¹`. -/
theorem exists_smooth_tendsto_H1 {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (hg : IsWeakGradient u g) :
    ∃ v : ℕ → Torus d → ℝ, (∀ n, IsSmoothPeriodic (v n)) ∧
      (∀ n, IsWeakGradient (v n) (smoothGrad (v n))) ∧
      Tendsto (fun n => eLpNorm (fun x => v n x - u x) 2 (haar d)) atTop (𝓝 0) ∧
      ∀ j : Fin d, Tendsto (fun n => eLpNorm
        (fun x => smoothGrad (v n) x j - g x j) 2 (haar d)) atTop (𝓝 0) := by
  have hu1 : Integrable u (haar d) := hg.memLp.integrable one_le_two
  have hT := tendsto_moll_W1p one_le_two ENNReal.ofNat_ne_top (isWeakGradient_iff_isWeakGradientLp.mp hg)
  exact ⟨fun n => SharpLSI.moll n u, fun n => isSmoothPeriodic_moll n hu1,
    fun n => (isSmoothPeriodic_moll n hu1).isWeakGradient, hT.1, hT.2⟩

end DGPS

namespace DGPS.Analysis

/-- FOU002 bundle: the periodic smoothing kernels `φₙ` are nonnegative, smooth, of unit mass,
supported in balls of radius `εₙ = 2/(n+2) → 0`; for `1 ≤ p < ∞`, `moll n f → f` in `Lᵖ`;
derivatives commute with smoothing and `moll n u → u` in `W^{1,p}`; each `moll n f` is smooth
periodic; and smooth periodic functions are dense in `H¹`. -/
theorem periodic_smoothing_and_sobolev_density (d : ℕ) :
    (∀ n (s : Fin d → ℝ), 0 ≤ SharpLSI.phiSeq n s) ∧
    (∀ n, ∫ s : Fin d → ℝ, SharpLSI.phiSeq n s = 1) ∧
    (∀ n, ContDiff ℝ ∞ (SharpLSI.phiSeq (ι := Fin d) n)) ∧
    (∀ n, Function.support (SharpLSI.phiSeq (ι := Fin d) n) =
      Metric.ball 0 (2 / ((n : ℝ) + 2))) ∧
    Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → p ≠ (∞ : ℝ≥0∞) → ∀ f : Torus d → ℝ, MemLp f p (haar d) →
      Tendsto (fun n => eLpNorm (fun x => SharpLSI.moll n f x - f x) p (haar d)) atTop (𝓝 0)) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → ∀ (u : Torus d → ℝ) (g : Torus d → Tangent d),
      IsWeakGradientLp p u g → ∀ n (j : Fin d),
        coordPartial j (SharpLSI.moll n u) = SharpLSI.moll n (fun x => g x j)) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → p ≠ (∞ : ℝ≥0∞) → ∀ (u : Torus d → ℝ) (g : Torus d → Tangent d),
      IsWeakGradientLp p u g →
        Tendsto (fun n => eLpNorm (fun x => SharpLSI.moll n u x - u x) p (haar d))
          atTop (𝓝 0) ∧
        ∀ j : Fin d, Tendsto (fun n => eLpNorm
          (fun x => coordPartial j (SharpLSI.moll n u) x - g x j) p (haar d)) atTop (𝓝 0)) ∧
    (∀ f : Torus d → ℝ, Integrable f (haar d) → ∀ n, IsSmoothPeriodic (SharpLSI.moll n f)) ∧
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      ∃ v : ℕ → Torus d → ℝ, (∀ n, IsSmoothPeriodic (v n)) ∧
        (∀ n, IsWeakGradient (v n) (smoothGrad (v n))) ∧
        Tendsto (fun n => eLpNorm (fun x => v n x - u x) 2 (haar d)) atTop (𝓝 0) ∧
        ∀ j : Fin d, Tendsto (fun n => eLpNorm
          (fun x => smoothGrad (v n) x j - g x j) 2 (haar d)) atTop (𝓝 0)) :=
  ⟨phiSeq_nonneg, integral_phiSeq, contDiff_phiSeq, phiSeq_support,
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop),
    fun _ hp hp' _ hf => tendsto_eLpNorm_moll_sub hp hp' hf,
    fun _ hp _ _ hg n j => hg.coordPartial_moll hp n j,
    fun _ hp hp' _ _ hg => tendsto_moll_W1p hp hp' hg,
    fun _ hf n => isSmoothPeriodic_moll n hf,
    fun _ _ hg => exists_smooth_tendsto_H1 hg⟩

end DGPS.Analysis
