import DGPS.Foundations.SobolevFourier

/-!
# FOU010: Periodic Laplacian `H²` regularity

On the unit torus `𝕋^d` with Haar probability `m`.

* `IsWeakLaplacian u g`: `u, g ∈ L²` and `∫ u Δφ = ∫ g φ` for every smooth periodic `φ`
  (the distributional Laplacian of `u` is `g`).
* `IsWeakHessian u G H`: `G` is the weak gradient of `u` and `Hᵢⱼ = ∂ᵢ Gⱼ` is the `L²` weak
  derivative of the `j`-th component of `G`.  `MemH2 u` says such `G, H` exist.
* `h2NormSq u G H = ‖u‖₂² + ‖G‖₂² + ∑ᵢⱼ ‖Hᵢⱼ‖₂²`.

Main result `DGPS.Analysis.periodic_laplacian_h2_regularity`:
1. if `u ∈ H¹` has distributional Laplacian `g ∈ L²`, then `u ∈ H²`, with
   `ĝ(k) = -4π²|k|² û(k)` for every `k` (including the zero mode, where both sides vanish),
   `Ĥᵢⱼ(k) = -4π² kᵢ kⱼ û(k)` and `‖u‖_{H²} ≤ C (‖u‖₂ + ‖g‖₂)`;
2. conversely, for `u ∈ H²` the trace `∑ᵢ Hᵢᵢ` of the Hessian is the weak Laplacian, it has Fourier
   coefficients `-4π²|k|² û(k)` (so `∑ 16π⁴|k|⁴|û(k)|² = ‖Δu‖₂² < ∞`) and integration by parts
   `∫ Δu φ = -∑ⱼ ∫ ∂ⱼu ∂ⱼφ` holds for smooth periodic `φ`.
-/

open MeasureTheory Filter Topology
open scoped Real ComplexConjugate ENNReal

namespace DGPS.Analysis

open DGPS

variable {d : ℕ}

/-- The Laplacian `Δφ = ∑ⱼ ∂ⱼ∂ⱼ φ` of a smooth periodic function. -/
noncomputable def periodicLaplacian (φ : Torus d → ℝ) (x : Torus d) : ℝ :=
  ∑ j, coordPartial j (coordPartial j φ) x

/-- `g` is the distributional Laplacian of `u`, both in `L²`. -/
structure IsWeakLaplacian (u g : Torus d → ℝ) : Prop where
  memLp : MemLp u 2 (haar d)
  memLp_lap : MemLp g 2 (haar d)
  ibp : ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ →
    ∫ x, u x * periodicLaplacian φ x ∂haar d = ∫ x, g x * φ x ∂haar d

/-- `G` is the weak gradient of `u` and `H i j = ∂ᵢ Gⱼ` weakly, all in `L²`. -/
structure IsWeakHessian (u : Torus d → ℝ) (G : Torus d → Tangent d)
    (H : Fin d → Fin d → Torus d → ℝ) : Prop where
  grad : IsWeakGradient u G
  memLp_hess : ∀ i j, MemLp (H i j) 2 (haar d)
  ibp : ∀ i j (φ : Torus d → ℝ), IsSmoothPeriodic φ →
    ∫ x, G x j * coordPartial i φ x ∂haar d = -∫ x, H i j x * φ x ∂haar d

/-- `u ∈ H²(m)`. -/
def MemH2 (u : Torus d → ℝ) : Prop := ∃ G H, IsWeakHessian u G H

/-- The squared `H²` norm `‖u‖₂² + ‖∇u‖₂² + ∑ᵢⱼ ‖∂ᵢ∂ⱼu‖₂²`. -/
noncomputable def h2NormSq (u : Torus d → ℝ) (G : Torus d → Tangent d)
    (H : Fin d → Fin d → Torus d → ℝ) : ℝ :=
  ∫ x, u x ^ 2 ∂haar d + ∫ x, ‖G x‖ ^ 2 ∂haar d + ∑ i, ∑ j, ∫ x, H i j x ^ 2 ∂haar d

/-! ### Derivatives of characters -/

theorem coordPartial_clm_mFourier (L : ℂ →L[ℝ] ℝ) (k : Fin d → ℤ) (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => L (UnitAddTorus.mFourier k y)) x =
      L (2 * π * Complex.I * (k j : ℂ) * UnitAddTorus.mFourier k x) := by
  have hF := (contDiff_mFourier_torusLift (d := d) k).differentiable (by simp) (SharpLSI.secT x)
  show fderiv ℝ (L ∘ fun y => UnitAddTorus.mFourier k (SharpLSI.liftT y))
    (SharpLSI.secT x) (Pi.single j 1) = _
  rw [(L.hasFDerivAt.comp _ hF.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [SharpLSI.fderiv_mFourier_liftT, SharpLSI.liftT_secT]

theorem isSmoothPeriodic_clm_mFourier (L : ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) :
    IsSmoothPeriodic (fun y => L (UnitAddTorus.mFourier n y)) :=
  L.contDiff.comp (contDiff_mFourier_torusLift n)

theorem periodicLaplacian_clm_mFourier (L : ℂ →L[ℝ] ℝ) (n : Fin d → ℤ) (x : Torus d) :
    periodicLaplacian (fun y => L (UnitAddTorus.mFourier n y)) x =
      L (((-gradWeight n : ℝ) : ℂ) * UnitAddTorus.mFourier n x) := by
  unfold periodicLaplacian
  have h1 : ∀ j : Fin d, coordPartial j (coordPartial j (fun y => L (UnitAddTorus.mFourier n y))) x
      = L (2 * π * Complex.I * (n j : ℂ) * (2 * π * Complex.I * (n j : ℂ) *
          UnitAddTorus.mFourier n x)) := by
    intro j
    have : coordPartial j (fun y => L (UnitAddTorus.mFourier n y)) =
        fun y => (L.comp (ContinuousLinearMap.mul ℝ ℂ (2 * π * Complex.I * (n j : ℂ))))
          (UnitAddTorus.mFourier n y) := by
      funext y
      rw [coordPartial_clm_mFourier]
      rfl
    rw [this, coordPartial_clm_mFourier]
    rfl
  simp_rw [h1]
  rw [← map_sum]
  congr 1
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  unfold gradWeight
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  linear_combination (4 * (π : ℂ) ^ 2 * ((n j : ℤ) : ℂ) ^ 2) * Complex.I_sq

/-! ### Fourier coefficients as integrals against real and imaginary parts of characters -/

theorem fourierCoeff_re {f : Torus d → ℝ} (hf : Integrable f (haar d)) (k : Fin d → ℤ) :
    (fourierCoeff f k).re = ∫ x, f x * (UnitAddTorus.mFourier (-k) x).re ∂haar d := by
  have h := mFourierCoeff_ofReal_eq f k
  have hi := integrable_mFourier_mul hf (-k)
  have h2 := integral_re hi
  simp only [RCLike.re_to_complex] at h2
  show (UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) k).re = _
  rw [h, ← h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [Complex.mul_re]
  ring

theorem fourierCoeff_im {f : Torus d → ℝ} (hf : Integrable f (haar d)) (k : Fin d → ℤ) :
    (fourierCoeff f k).im = ∫ x, f x * (UnitAddTorus.mFourier (-k) x).im ∂haar d := by
  have h := mFourierCoeff_ofReal_eq f k
  have hi := integrable_mFourier_mul hf (-k)
  have h2 := integral_im hi
  simp only [RCLike.im_to_complex] at h2
  show (UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) k).im = _
  rw [h, ← h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [Complex.mul_im]
  ring

/-- The Fourier symbol of the Laplacian, including the zero mode: `ĝ(k) = -4π²|k|² û(k)`. -/
theorem IsWeakLaplacian.fourierCoeff_eq {u g : Torus d → ℝ} (h : IsWeakLaplacian u g)
    (k : Fin d → ℤ) :
    fourierCoeff g k = -(gradWeight k : ℂ) * fourierCoeff u k := by
  have hu1 := h.memLp.integrable one_le_two
  have hg1 := h.memLp_lap.integrable one_le_two
  have key : ∀ L : ℂ →L[ℝ] ℝ, ∫ x, g x * L (UnitAddTorus.mFourier (-k) x) ∂haar d =
      -gradWeight k * ∫ x, u x * L (UnitAddTorus.mFourier (-k) x) ∂haar d := by
    intro L
    have := h.ibp _ (isSmoothPeriodic_clm_mFourier L (-k))
    simp_rw [periodicLaplacian_clm_mFourier] at this
    rw [← this, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have e : (((-gradWeight (-k) : ℝ) : ℂ)) * UnitAddTorus.mFourier (-k) x =
        (-gradWeight k) • UnitAddTorus.mFourier (-k) x := by
      have : gradWeight (-k) = gradWeight k := by simp [gradWeight]
      rw [this, Complex.real_smul]
    simp only []
    rw [e, map_smul, smul_eq_mul]
    ring
  apply Complex.ext
  · have hr : (-(gradWeight k : ℂ) * fourierCoeff u k).re = -gradWeight k * (fourierCoeff u k).re := by
      simp
    rw [hr, fourierCoeff_re hg1, fourierCoeff_re hu1]
    simpa using key Complex.reCLM
  · have hr : (-(gradWeight k : ℂ) * fourierCoeff u k).im = -gradWeight k * (fourierCoeff u k).im := by
      simp
    rw [hr, fourierCoeff_im hg1, fourierCoeff_im hu1]
    simpa using key Complex.imCLM

/-! ### Algebra of the symbols -/

theorem sum_sq_hess_symbol (k : Fin d → ℤ) (c : ℂ) :
    ∑ i, ∑ j, ‖2 * π * Complex.I * (k i : ℂ) * (2 * π * Complex.I * (k j : ℂ) * c)‖ ^ 2 =
      gradWeight k ^ 2 * ‖c‖ ^ 2 := by
  have h : ∀ i j : Fin d, ‖2 * π * Complex.I * (k i : ℂ) * (2 * π * Complex.I * (k j : ℂ) * c)‖ ^ 2
      = (4 * π ^ 2 * ((k i : ℤ) : ℝ) ^ 2) * (4 * π ^ 2 * ((k j : ℤ) : ℝ) ^ 2) * ‖c‖ ^ 2 := by
    intro i j
    rw [SharpLSI.norm_grad_coeff_sq, SharpLSI.norm_grad_coeff_sq]
    ring
  simp_rw [h, ← Finset.sum_mul, ← Finset.sum_mul_sum]
  unfold gradWeight
  rw [← Finset.mul_sum]
  ring

theorem sq_grad_symbol (k : Fin d → ℤ) (c : ℂ) :
    ‖-(gradWeight k : ℂ) * c‖ ^ 2 = gradWeight k ^ 2 * ‖c‖ ^ 2 := by
  rw [norm_mul, mul_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem hess_symbol_eq (k : Fin d → ℤ) (i j : Fin d) (c : ℂ) :
    2 * π * Complex.I * (k i : ℂ) * (2 * π * Complex.I * (k j : ℂ) * c) =
      -(4 * π ^ 2 * (k i : ℂ) * (k j : ℂ)) * c := by
  linear_combination (4 * (π : ℂ) ^ 2 * (k i : ℂ) * (k j : ℂ) * c) * Complex.I_sq

/-! ### Forward direction: `Δu ∈ L²` gives `u ∈ H²` -/

theorem exists_hessian_of_weakLaplacian {u g : Torus d → ℝ} (hu : MemH1 u)
    (hg : IsWeakLaplacian u g) :
    ∃ (G : Torus d → Tangent d) (H : Fin d → Fin d → Torus d → ℝ), IsWeakHessian u G H ∧
      (∀ i j k, fourierCoeff (H i j) k = -(4 * π ^ 2 * (k i : ℂ) * (k j : ℂ)) * fourierCoeff u k) ∧
      h2NormSq u G H ≤ 3 / 2 * (∫ x, u x ^ 2 ∂haar d + ∫ x, g x ^ 2 ∂haar d) := by
  obtain ⟨G, hG⟩ := hu
  have hGc : ∀ j k, fourierCoeff (fun y => G y j) k = 2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k :=
    fun j k => fourierCoeff_weakGradient hG j k
  have hgc := hg.fourierCoeff_eq
  have hgsum : HasSum (fun k => ‖fourierCoeff g k‖ ^ 2) (∫ x, g x ^ 2 ∂haar d) :=
    hasSum_sq_fourierCoeff hg.memLp_lap
  have hgsum' : HasSum (fun k => gradWeight k ^ 2 * ‖fourierCoeff u k‖ ^ 2)
      (∫ x, g x ^ 2 ∂haar d) := by
    convert hgsum using 1
    funext k
    rw [hgc k, sq_grad_symbol]
  have hex : ∀ i j : Fin d, ∃ f : Torus d → ℝ, MemLp f 2 (haar d) ∧ ∀ k,
      fourierCoeff f k = 2 * π * Complex.I * (k i : ℂ) * (2 * π * Complex.I * (k j : ℂ) *
        fourierCoeff u k) := by
    intro i j
    refine SharpLSI.exists_of_cf (c := fun k => 2 * π * Complex.I * (k i : ℂ) *
      (2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k)) ?_ ?_
    · refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hgsum'.summable
      calc ‖2 * π * Complex.I * (k i : ℂ) * (2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k)‖ ^ 2
          ≤ gradWeight k * ‖2 * π * Complex.I * (k j : ℂ) * fourierCoeff u k‖ ^ 2 :=
            norm_sq_gradCoeff_le k i _
        _ ≤ gradWeight k * (gradWeight k * ‖fourierCoeff u k‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (norm_sq_gradCoeff_le k j _) (by
              unfold gradWeight; positivity)
        _ = _ := by ring
    · intro k
      have : fourierCoeff u (-k) = conj (fourierCoeff u k) := fourierCoeff_neg u k
      simp only [this, Pi.neg_apply, Int.cast_neg, map_mul, Complex.conj_ofReal,
        Complex.conj_I, Complex.conj_ofNat, map_intCast]
      ring
  choose H hHmem hHc using hex
  have hHc' : ∀ i j k, fourierCoeff (H i j) k = 2 * π * Complex.I * (k i : ℂ) *
      fourierCoeff (fun y => G y j) k := fun i j k => by rw [hHc, hGc]
  have hW : IsWeakHessian u G H :=
    { grad := hG
      memLp_hess := hHmem
      ibp := fun i j φ hφ => ibp_of_fourierCoeff (memLp_coord hG.memLp_grad j) (hHmem i j) i
        (hHc' i j) hφ }
  refine ⟨G, H, hW, fun i j k => by rw [hHc, hess_symbol_eq], ?_⟩
  have h0 := hasSum_sq_fourierCoeff hG.memLp
  have h1 := hasSum_gradWeight_weakGradient hG
  have h2 : HasSum (fun k => ∑ i, ∑ j, ‖fourierCoeff (H i j) k‖ ^ 2)
      (∑ i, ∑ j, ∫ x, H i j x ^ 2 ∂haar d) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ => hasSum_sq_fourierCoeff (hHmem i j)
  have hall := (h0.add h1).add h2
  have hbound := (hgsum'.add h0).mul_left (3 / 2)
  have hle := hasSum_le (fun k => ?_) hall hbound
  · unfold h2NormSq
    linarith
  · have e : ∑ i, ∑ j, ‖fourierCoeff (H i j) k‖ ^ 2 = gradWeight k ^ 2 * ‖fourierCoeff u k‖ ^ 2 := by
      rw [← sum_sq_hess_symbol]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hHc]
    rw [e]
    have hw : 0 ≤ gradWeight k := by unfold gradWeight; positivity
    nlinarith [sq_nonneg (gradWeight k - 1), sq_nonneg ‖fourierCoeff u k‖,
      mul_nonneg (sq_nonneg ‖fourierCoeff u k‖) (sq_nonneg (gradWeight k - 1))]

theorem h2_bound_of_weakLaplacian {u g : Torus d → ℝ} (hu : MemH1 u) (hg : IsWeakLaplacian u g) :
    ∃ (G : Torus d → Tangent d) (H : Fin d → Fin d → Torus d → ℝ), IsWeakHessian u G H ∧
      Real.sqrt (h2NormSq u G H) ≤
        2 * (Real.sqrt (∫ x, u x ^ 2 ∂haar d) + Real.sqrt (∫ x, g x ^ 2 ∂haar d)) := by
  obtain ⟨G, H, hW, -, hb⟩ := exists_hessian_of_weakLaplacian hu hg
  refine ⟨G, H, hW, ?_⟩
  have hA : 0 ≤ ∫ x, u x ^ 2 ∂haar d := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, g x ^ 2 ∂haar d := integral_nonneg fun x => sq_nonneg _
  rw [Real.sqrt_le_left (by positivity)]
  have ha := Real.sq_sqrt hA
  have hb' := Real.sq_sqrt hB
  have := Real.sqrt_nonneg (∫ x, u x ^ 2 ∂haar d)
  have := Real.sqrt_nonneg (∫ x, g x ^ 2 ∂haar d)
  nlinarith [mul_nonneg (Real.sqrt_nonneg (∫ x, u x ^ 2 ∂haar d))
    (Real.sqrt_nonneg (∫ x, g x ^ 2 ∂haar d))]

/-! ### Converse: `u ∈ H²` has `L²` Fourier Laplacian and weak integration by parts -/

theorem fourierCoeff_hessian {u : Torus d → ℝ} {G : Torus d → Tangent d}
    {H : Fin d → Fin d → Torus d → ℝ} (h : IsWeakHessian u G H) (i j : Fin d) (k : Fin d → ℤ) :
    fourierCoeff (H i j) k = -(4 * π ^ 2 * (k i : ℂ) * (k j : ℂ)) * fourierCoeff u k := by
  have h1 : fourierCoeff (H i j) k = 2 * π * Complex.I * (k i : ℂ) *
      fourierCoeff (fun y => G y j) k :=
    mFourierCoeff_of_ibp ((memLp_coord h.grad.memLp_grad j).integrable one_le_two)
      ((h.memLp_hess i j).integrable one_le_two) i (fun φ hφ => h.ibp i j φ hφ) k
  rw [h1, fourierCoeff_weakGradient h.grad j k, hess_symbol_eq]

theorem fourierCoeff_trace_hessian {u : Torus d → ℝ} {G : Torus d → Tangent d}
    {H : Fin d → Fin d → Torus d → ℝ} (h : IsWeakHessian u G H) (k : Fin d → ℤ) :
    fourierCoeff (fun x => ∑ i, H i i x) k = -(gradWeight k : ℂ) * fourierCoeff u k := by
  have hsum : fourierCoeff (fun x => ∑ i, H i i x) k = ∑ i, fourierCoeff (H i i) k := by
    rw [fourierCoeff, mFourierCoeff_ofReal_eq]
    push_cast
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ =>
      integrable_mFourier_mul ((h.memLp_hess i i).integrable one_le_two) (-k)]
    exact Finset.sum_congr rfl fun i _ => (mFourierCoeff_ofReal_eq _ k).symm
  rw [hsum]
  simp_rw [fourierCoeff_hessian h]
  rw [← Finset.sum_mul]
  congr 1
  unfold gradWeight
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem integral_trace_hessian_mul {u : Torus d → ℝ} {G : Torus d → Tangent d}
    {H : Fin d → Fin d → Torus d → ℝ} (h : IsWeakHessian u G H) {φ : Torus d → ℝ}
    (hφ : IsSmoothPeriodic φ) :
    ∫ x, (∑ i, H i i x) * φ x ∂haar d = -∑ j, ∫ x, G x j * coordPartial j φ x ∂haar d := by
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ =>
    integrable_mul_of_memLp_two (h.memLp_hess i i) hφ.memLp_top, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h.ibp j j φ hφ, neg_neg]

theorem isWeakLaplacian_trace_hessian {u : Torus d → ℝ} {G : Torus d → Tangent d}
    {H : Fin d → Fin d → Torus d → ℝ} (h : IsWeakHessian u G H) :
    IsWeakLaplacian u (fun x => ∑ i, H i i x) where
  memLp := h.grad.memLp
  memLp_lap := by
    have := memLp_finsetSum' Finset.univ fun i _ => h.memLp_hess i i
    convert this using 1
    funext x
    simp [Finset.sum_apply]
  ibp φ hφ := by
    rw [integral_trace_hessian_mul h hφ]
    unfold periodicLaplacian
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun j _ => integrable_mul_of_memLp_two h.grad.memLp
      ((hφ.isSmoothPeriodic_coordPartial j).isSmoothPeriodic_coordPartial j).memLp_top,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h.grad.ibp (coordPartial j φ) (hφ.isSmoothPeriodic_coordPartial j) j]

theorem hasSum_trace_hessian {u : Torus d → ℝ} {G : Torus d → Tangent d}
    {H : Fin d → Fin d → Torus d → ℝ} (h : IsWeakHessian u G H) :
    HasSum (fun k => gradWeight k ^ 2 * ‖fourierCoeff u k‖ ^ 2)
      (∫ x, (∑ i, H i i x) ^ 2 ∂haar d) := by
  have := hasSum_sq_fourierCoeff (isWeakLaplacian_trace_hessian h).memLp_lap
  convert this using 1
  funext k
  rw [fourierCoeff_trace_hessian h, sq_grad_symbol]

/-- **FOU010** (periodic Laplacian `H²` regularity on `𝕋^d`).

(1) There is a constant `C` such that if `u ∈ H¹` has distributional Laplacian `g ∈ L²`
then `u ∈ H²` with Hessian `H`, the Fourier identities `ĝ(k) = -4π²|k|² û(k)` (for every `k`,
including the zero mode) and `Ĥᵢⱼ(k) = -4π² kᵢ kⱼ û(k)` hold, and
`‖u‖_{H²} ≤ C (‖u‖₂ + ‖g‖₂)`.

(2) Conversely, if `u ∈ H²` with weak gradient `G` and Hessian `H`, then the trace `∑ᵢ Hᵢᵢ` is
the weak Laplacian of `u`, has Fourier coefficients `-4π²|k|² û(k)` with
`∑ₖ (4π²|k|²)² |û(k)|² = ‖Δu‖₂²`, and satisfies the weak integration by parts
`∫ Δu φ = -∑ⱼ ∫ ∂ⱼu ∂ⱼφ` for every smooth periodic `φ`. -/
theorem periodic_laplacian_h2_regularity (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ (u g : Torus d → ℝ), MemH1 u → IsWeakLaplacian u g →
        (∀ k, fourierCoeff g k = -(gradWeight k : ℂ) * fourierCoeff u k) ∧
        ∃ (G : Torus d → Tangent d) (H : Fin d → Fin d → Torus d → ℝ),
          IsWeakHessian u G H ∧
          (∀ i j k, fourierCoeff (H i j) k =
            -(4 * π ^ 2 * (k i : ℂ) * (k j : ℂ)) * fourierCoeff u k) ∧
          Real.sqrt (h2NormSq u G H) ≤
            C * (Real.sqrt (∫ x, u x ^ 2 ∂haar d) + Real.sqrt (∫ x, g x ^ 2 ∂haar d))) ∧
      (∀ (u : Torus d → ℝ) (G : Torus d → Tangent d) (H : Fin d → Fin d → Torus d → ℝ),
        IsWeakHessian u G H →
        IsWeakLaplacian u (fun x => ∑ i, H i i x) ∧
        (∀ k, fourierCoeff (fun x => ∑ i, H i i x) k =
          -(gradWeight k : ℂ) * fourierCoeff u k) ∧
        HasSum (fun k => gradWeight k ^ 2 * ‖fourierCoeff u k‖ ^ 2)
          (∫ x, (∑ i, H i i x) ^ 2 ∂haar d) ∧
        (∀ φ : Torus d → ℝ, IsSmoothPeriodic φ →
          ∫ x, (∑ i, H i i x) * φ x ∂haar d =
            -∑ j, ∫ x, G x j * coordPartial j φ x ∂haar d)) := by
  refine ⟨2, two_pos, fun u g hu hg => ⟨hg.fourierCoeff_eq, ?_⟩, fun u G H h => ?_⟩
  · obtain ⟨G, H, hW, hb⟩ := h2_bound_of_weakLaplacian hu hg
    exact ⟨G, H, hW, fun i j k => fourierCoeff_hessian hW i j k, hb⟩
  · exact ⟨isWeakLaplacian_trace_hessian h, fourierCoeff_trace_hessian h, hasSum_trace_hessian h,
      fun φ hφ => integral_trace_hessian_mul h hφ⟩

end DGPS.Analysis
