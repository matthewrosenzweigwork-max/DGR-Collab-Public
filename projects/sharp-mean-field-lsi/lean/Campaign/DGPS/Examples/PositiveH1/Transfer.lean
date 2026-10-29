import Mathlib
import DGPS.Examples.PositiveH1.Particle
import DGPS.Particle.Sobolev
import DGPS.Foundations.PeriodicSmoothing
import DGPS.Analysis.ForceMultiplier


/-!
# Particle Fourier coordinate multiplier (H1031)

For `n ≠ 0`, `N ≥ 1` and `ψ ∈ H¹(m^N)` (real valued, with weak gradient `g` on `(𝕋¹)^N`),
`‖Z_{N,n} ψ‖₂ ≤ ‖ψ‖₂ + 2 (2π n)⁻¹ ‖∇ψ‖₂`
(`particle_fourier_coordinate_multiplier`).

Proof: for smooth `v` on `𝕋^N`, integrate by parts against the real and imaginary parts of the
mode sums, `∂ⱼ R = -k Sⱼ`, `∂ⱼ I = k Cⱼ`, giving `k ∫ v² (R²+I²) = 2 ∫ v T + N k ∫ v²`; then
pointwise and Cauchy-Schwarz bounds give `B ≤ A + (2/k) √B √G` and the scalar quadratic lemma
`quad_aux` yields `√B ≤ √A + (2/k) √G`.  The extension to `H¹` is by density of smooth periodic
functions (`exists_smooth_tendsto_H1`), and `(𝕋¹)^N ≃ 𝕋^N` transports the particle statement.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS
open DGPS.Analysis.ForceMultiplier

namespace DGPS.Examples.PositiveH1.Transfer

section torus
variable {d : ℕ}

theorem coordPartial_add {f g : Torus d → ℝ} (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g)
    (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => f y + g y) x = coordPartial j f x + coordPartial j g x := by
  have hf1 : DifferentiableAt ℝ (f ∘ SharpLSI.liftT) (SharpLSI.secT x) :=
    (hf.differentiable (by simp)) _
  have hg1 : DifferentiableAt ℝ (g ∘ SharpLSI.liftT) (SharpLSI.secT x) :=
    (hg.differentiable (by simp)) _
  show fderiv ℝ ((fun y => f y + g y) ∘ SharpLSI.liftT) (SharpLSI.secT x) (Pi.single j 1) = _
  have : ((fun y => f y + g y) ∘ SharpLSI.liftT) =
      fun z => (f ∘ SharpLSI.liftT) z + (g ∘ SharpLSI.liftT) z := rfl
  rw [this, fderiv_fun_add hf1 hg1]
  rfl

theorem coordPartial_mul {f g : Torus d → ℝ} (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g)
    (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => f y * g y) x = f x * coordPartial j g x + coordPartial j f x * g x := by
  have hf1 : DifferentiableAt ℝ (f ∘ SharpLSI.liftT) (SharpLSI.secT x) :=
    (hf.differentiable (by simp)) _
  have hg1 : DifferentiableAt ℝ (g ∘ SharpLSI.liftT) (SharpLSI.secT x) :=
    (hg.differentiable (by simp)) _
  show fderiv ℝ ((fun y => f y * g y) ∘ SharpLSI.liftT) (SharpLSI.secT x) (Pi.single j 1) = _
  have : ((fun y => f y * g y) ∘ SharpLSI.liftT) =
      fun z => (f ∘ SharpLSI.liftT) z * (g ∘ SharpLSI.liftT) z := rfl
  rw [this, fderiv_fun_mul hf1 hg1]
  simp only [add_apply, smul_apply, smul_eq_mul,
    Function.comp_apply, SharpLSI.liftT_secT, DGPS.coordPartial]
  ring

theorem coordPartial_const_mul {f : Torus d → ℝ} (hf : IsSmoothPeriodic f) (c : ℝ)
    (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => c * f y) x = c * coordPartial j f x := by
  have hf1 : DifferentiableAt ℝ (f ∘ SharpLSI.liftT) (SharpLSI.secT x) :=
    (hf.differentiable (by simp)) _
  show fderiv ℝ ((fun y => c * f y) ∘ SharpLSI.liftT) (SharpLSI.secT x) (Pi.single j 1) = _
  have : ((fun y => c * f y) ∘ SharpLSI.liftT) = fun z => c * (f ∘ SharpLSI.liftT) z := rfl
  rw [this, fderiv_const_mul hf1]
  rfl

theorem isSmoothPeriodic_sum {ι : Type*} (s : Finset ι) {f : ι → Torus d → ℝ}
    (hf : ∀ i ∈ s, IsSmoothPeriodic (f i)) : IsSmoothPeriodic (fun y => ∑ i ∈ s, f i y) :=
  ContDiff.sum hf

theorem coordPartial_sum {ι : Type*} (s : Finset ι) {f : ι → Torus d → ℝ}
    (hf : ∀ i ∈ s, IsSmoothPeriodic (f i)) (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, coordPartial j (f i) x := by
  have hf1 : ∀ i ∈ s, DifferentiableAt ℝ (f i ∘ SharpLSI.liftT) (SharpLSI.secT x) :=
    fun i hi => ((hf i hi).differentiable (by simp)) _
  show fderiv ℝ ((fun y => ∑ i ∈ s, f i y) ∘ SharpLSI.liftT) (SharpLSI.secT x) (Pi.single j 1) = _
  have : ((fun y => ∑ i ∈ s, f i y) ∘ SharpLSI.liftT) =
      fun z => ∑ i ∈ s, (f i ∘ SharpLSI.liftT) z := rfl
  rw [this, fderiv_fun_sum hf1]
  simp
  rfl

theorem integrable_of_smooth {f : Torus d → ℝ} (hf : IsSmoothPeriodic f) :
    Integrable f (haar d) :=
  (memLp_two_of_continuous hf.continuous_torus).integrable one_le_two

end torus

section modes
variable {M : ℕ}

noncomputable def mF (n : ℕ) (i : Fin M) : Torus M → ℂ :=
  UnitAddTorus.mFourier (Pi.single i (n : ℤ))

noncomputable def Cc (n : ℕ) (i : Fin M) (y : Torus M) : ℝ := (mF n i y).re
noncomputable def Ss (n : ℕ) (i : Fin M) (y : Torus M) : ℝ := (mF n i y).im
noncomputable def Rr (n : ℕ) (y : Torus M) : ℝ := ∑ i, Cc n i y
noncomputable def Ii (n : ℕ) (y : Torus M) : ℝ := ∑ i, Ss n i y
noncomputable def kk (n : ℕ) : ℝ := 2 * Real.pi * n

theorem isSmooth_Cc (n : ℕ) (i : Fin M) : IsSmoothPeriodic (Cc n i) :=
  isSmoothPeriodic_re_mFourier _

theorem isSmooth_Ss (n : ℕ) (i : Fin M) : IsSmoothPeriodic (Ss n i) :=
  isSmoothPeriodic_im_mFourier _

theorem isSmooth_Rr (n : ℕ) : IsSmoothPeriodic (Rr (M := M) n) :=
  isSmoothPeriodic_sum _ fun i _ => isSmooth_Cc n i

theorem isSmooth_Ii (n : ℕ) : IsSmoothPeriodic (Ii (M := M) n) :=
  isSmoothPeriodic_sum _ fun i _ => isSmooth_Ss n i

theorem Cc_sq_add_Ss_sq (n : ℕ) (i : Fin M) (y : Torus M) :
    Cc n i y ^ 2 + Ss n i y ^ 2 = 1 := by
  have h := norm_mFourier_apply (Pi.single i (n : ℤ)) y
  have h2 : Complex.normSq (mF n i y) = 1 := by
    rw [Complex.normSq_eq_norm_sq]; unfold mF; rw [h]; norm_num
  rw [Complex.normSq_apply] at h2
  unfold Cc Ss; nlinarith

theorem coordPartial_Cc (n : ℕ) (i j : Fin M) (x : Torus M) :
    coordPartial j (Cc n i) x = if i = j then -(kk n) * Ss n i x else 0 := by
  have h := coordPartial_re_mFourier (Pi.single i (n : ℤ)) j x
  show coordPartial j (fun y => (mF n i y).re) x = _
  unfold mF at *
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [Ss, mF, kk, Complex.mul_re, Complex.mul_im]
  · simp [hij, Ne.symm hij]

theorem coordPartial_Ss (n : ℕ) (i j : Fin M) (x : Torus M) :
    coordPartial j (Ss n i) x = if i = j then (kk n) * Cc n i x else 0 := by
  have h := coordPartial_im_mFourier (Pi.single i (n : ℤ)) j x
  show coordPartial j (fun y => (mF n i y).im) x = _
  unfold mF at *
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp [Cc, mF, kk, Complex.mul_re, Complex.mul_im]
  · simp [hij, Ne.symm hij]

theorem coordPartial_Rr (n : ℕ) (j : Fin M) (x : Torus M) :
    coordPartial j (Rr n) x = -(kk n) * Ss n j x := by
  unfold Rr
  rw [coordPartial_sum _ (fun i _ => isSmooth_Cc n i)]
  simp [coordPartial_Cc]

theorem coordPartial_Ii (n : ℕ) (j : Fin M) (x : Torus M) :
    coordPartial j (Ii n) x = (kk n) * Cc n j x := by
  unfold Ii
  rw [coordPartial_sum _ (fun i _ => isSmooth_Ss n i)]
  simp [coordPartial_Ss]


theorem isSmooth_add {f g : Torus M → ℝ} (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    IsSmoothPeriodic (fun y => f y + g y) := ContDiff.add hf hg

theorem isSmooth_sub {f g : Torus M → ℝ} (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    IsSmoothPeriodic (fun y => f y - g y) := ContDiff.sub hf hg

theorem isSmooth_const_mul {f : Torus M → ℝ} (hf : IsSmoothPeriodic f) (c : ℝ) :
    IsSmoothPeriodic (fun y => c * f y) := ContDiff.mul contDiff_const hf

theorem perj (n : ℕ) {v : Torus M → ℝ} (hv : IsSmoothPeriodic v) (j : Fin M) :
    ∫ x, ((v x * v x * Rr n x) * (kk n * Cc n j x) + (v x * v x * Ii n x) * (kk n * Ss n j x))
        ∂haar M
      = ∫ x, (2 * v x * coordPartial j v x * (Ii n x * Cc n j x - Rr n x * Ss n j x)
          + kk n * v x * v x) ∂haar M := by
  have hvv : IsSmoothPeriodic (fun y => v y * v y) := hv.mul hv
  have hFR : IsSmoothPeriodic (fun y => v y * v y * Rr n y) := hvv.mul (isSmooth_Rr n)
  have hFI : IsSmoothPeriodic (fun y => v y * v y * Ii n y) := hvv.mul (isSmooth_Ii n)
  have e1 := integral_mul_coordPartial_of_smooth hFR (isSmooth_Ss n j) j
  have e2 := integral_mul_coordPartial_of_smooth hFI (isSmooth_Cc n j) j
  have dR : ∀ x, coordPartial j (fun y => v y * v y * Rr n y) x
      = (v x * v x) * (-(kk n) * Ss n j x) + (v x * coordPartial j v x + coordPartial j v x * v x) * Rr n x := by
    intro x
    rw [coordPartial_mul hvv (isSmooth_Rr n), coordPartial_Rr, coordPartial_mul hv hv]
  have dI : ∀ x, coordPartial j (fun y => v y * v y * Ii n y) x
      = (v x * v x) * ((kk n) * Cc n j x) + (v x * coordPartial j v x + coordPartial j v x * v x) * Ii n x := by
    intro x
    rw [coordPartial_mul hvv (isSmooth_Ii n), coordPartial_Ii, coordPartial_mul hv hv]
  have i1 : Integrable (fun x => (v x * v x * Rr n x) * coordPartial j (Ss n j) x) (haar M) :=
    integrable_of_smooth (hFR.mul ((isSmooth_Ss n j).isSmoothPeriodic_coordPartial j))
  have i2 : Integrable (fun x => (v x * v x * Ii n x) * coordPartial j (Cc n j) x) (haar M) :=
    integrable_of_smooth (hFI.mul ((isSmooth_Cc n j).isSmoothPeriodic_coordPartial j))
  have i3 : Integrable (fun x => coordPartial j (fun y => v y * v y * Rr n y) x * Ss n j x) (haar M) :=
    integrable_of_smooth ((hFR.isSmoothPeriodic_coordPartial j).mul (isSmooth_Ss n j))
  have i4 : Integrable (fun x => coordPartial j (fun y => v y * v y * Ii n y) x * Cc n j x) (haar M) :=
    integrable_of_smooth ((hFI.isSmoothPeriodic_coordPartial j).mul (isSmooth_Cc n j))
  have hL : (fun x => ((v x * v x * Rr n x) * (kk n * Cc n j x) + (v x * v x * Ii n x) * (kk n * Ss n j x)))
      = fun x => (v x * v x * Rr n x) * coordPartial j (Ss n j) x
          - (v x * v x * Ii n x) * coordPartial j (Cc n j) x := by
    funext x
    rw [coordPartial_Ss, coordPartial_Cc]
    simp only [ite_true]
    ring
  have hR : (fun x => (2 * v x * coordPartial j v x * (Ii n x * Cc n j x - Rr n x * Ss n j x)
          + kk n * v x * v x))
      = fun x => -(coordPartial j (fun y => v y * v y * Rr n y) x * Ss n j x)
          + coordPartial j (fun y => v y * v y * Ii n y) x * Cc n j x := by
    funext x
    rw [dR, dI]
    have h := Cc_sq_add_Ss_sq n j x
    linear_combination (-(kk n) * v x * v x) * h
  have i3' : Integrable (fun x => -(coordPartial j (fun y => v y * v y * Rr n y) x * Ss n j x))
      (haar M) := i3.neg
  rw [hL, hR, integral_sub i1 i2, integral_add i3' i4, integral_neg, e1, e2]
  ring


theorem integrable_of_continuous {d : ℕ} {f : Torus d → ℝ} (hf : Continuous f) :
    Integrable f (haar d) :=
  (memLp_two_of_continuous hf).integrable one_le_two

noncomputable def Tt (n : ℕ) (v : Torus M → ℝ) (x : Torus M) : ℝ :=
  ∑ j, coordPartial j v x * (Ii n x * Cc n j x - Rr n x * Ss n j x)

theorem ibp_sum (n : ℕ) {v : Torus M → ℝ} (hv : IsSmoothPeriodic v) :
    kk n * ∫ x, (v x * v x) * (Rr n x ^ 2 + Ii n x ^ 2) ∂haar M =
      2 * ∫ x, v x * Tt n v x ∂haar M + (M : ℝ) * kk n * ∫ x, v x * v x ∂haar M := by
  have hcv : Continuous v := hv.continuous_torus
  have hcR : Continuous (Rr (M := M) n) := (isSmooth_Rr n).continuous_torus
  have hcI : Continuous (Ii (M := M) n) := (isSmooth_Ii n).continuous_torus
  have hcC : ∀ j, Continuous (Cc (M := M) n j) := fun j => (isSmooth_Cc n j).continuous_torus
  have hcS : ∀ j, Continuous (Ss (M := M) n j) := fun j => (isSmooth_Ss n j).continuous_torus
  have hcp : ∀ j, Continuous (coordPartial j v) := fun j => hv.continuous_coordPartial j
  have hcT : Continuous (Tt n v) := by
    unfold Tt
    exact continuous_finsetSum _ fun j _ => by
      have := hcC j; have := hcS j; have := hcp j; fun_prop
  have h := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => perj n hv j)
  rw [← integral_finsetSum _ (fun j _ => integrable_of_continuous (by
        have := hcC j; have := hcS j; fun_prop)),
    ← integral_finsetSum _ (fun j _ => integrable_of_continuous (by
        have := hcC j; have := hcS j; have := hcp j; fun_prop))] at h
  have hL : ∀ x, ∑ j, ((v x * v x * Rr n x) * (kk n * Cc n j x) + (v x * v x * Ii n x) * (kk n * Ss n j x))
      = kk n * ((v x * v x) * (Rr n x ^ 2 + Ii n x ^ 2)) := by
    intro x
    calc _ = (v x * v x * Rr n x * kk n) * ∑ j, Cc n j x
          + (v x * v x * Ii n x * kk n) * ∑ j, Ss n j x := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = _ := by simp only [Rr, Ii]; ring
  have hR : ∀ x, ∑ j, (2 * v x * coordPartial j v x * (Ii n x * Cc n j x - Rr n x * Ss n j x)
          + kk n * v x * v x) = 2 * (v x * Tt n v x) + (M : ℝ) * kk n * (v x * v x) := by
    intro x
    rw [Finset.sum_add_distrib, Tt, Finset.mul_sum, Finset.mul_sum]
    have h1 : ∑ j, 2 * v x * coordPartial j v x * (Ii n x * Cc n j x - Rr n x * Ss n j x)
        = ∑ j, 2 * (v x * (coordPartial j v x * (Ii n x * Cc n j x - Rr n x * Ss n j x))) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    rw [h1]
    simp [Finset.sum_const, Finset.card_univ]
    ring
  simp only [hL, hR] at h
  rw [integral_const_mul, integral_add, integral_const_mul, integral_const_mul] at h
  · exact h
  · exact integrable_of_continuous (by have := hcT; fun_prop)
  · exact integrable_of_continuous (by fun_prop)


end modes

theorem integral_mul_le_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ∫ x, a x * b x ∂μ ≤ Real.sqrt (∫ x, a x ^ 2 ∂μ) * Real.sqrt (∫ x, b x ^ 2 ∂μ) := by
  have iA : Integrable (fun x => a x ^ 2) μ := ha.integrable_sq
  have iB : Integrable (fun x => b x ^ 2) μ := hb.integrable_sq
  have iAB : Integrable (fun x => a x * b x) μ := ha.integrable_mul hb
  have key : ∀ t : ℝ, 0 ≤ (∫ x, a x ^ 2 ∂μ) * (t * t) + (-2 * ∫ x, a x * b x ∂μ) * t
      + ∫ x, b x ^ 2 ∂μ := by
    intro t
    have e : (fun x => (t * a x - b x) ^ 2)
        = fun x => t * t * a x ^ 2 + (-2 * t) * (a x * b x) + b x ^ 2 := by
      funext x; ring
    have h0 : 0 ≤ ∫ x, (t * a x - b x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have I1 : Integrable (fun x => t * t * a x ^ 2 + (-2 * t) * (a x * b x)) μ :=
      (iA.const_mul _).add (iAB.const_mul _)
    rw [e, integral_add I1 iB, integral_add (iA.const_mul (t * t)) (iAB.const_mul (-2 * t)),
      integral_const_mul, integral_const_mul] at h0
    linarith
  have hd := discrim_le_zero key
  unfold discrim at hd
  have hA : 0 ≤ ∫ x, a x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have h2 : (∫ x, a x * b x ∂μ) ^ 2 ≤ (∫ x, a x ^ 2 ∂μ) * ∫ x, b x ^ 2 ∂μ := by nlinarith
  rw [← Real.sqrt_mul hA]
  exact (le_abs_self _).trans (Real.abs_le_sqrt h2)

theorem quad_aux {A B G k : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hk : 0 < k)
    (h : B ≤ A + 2 / k * (Real.sqrt B * Real.sqrt G)) :
    Real.sqrt B ≤ Real.sqrt A + 2 / k * Real.sqrt G := by
  have ha := Real.sqrt_nonneg A
  have hb := Real.sqrt_nonneg B
  have hg := Real.sqrt_nonneg G
  have hA' := Real.sq_sqrt hA
  have hB' := Real.sq_sqrt hB
  set a := Real.sqrt A
  set b := Real.sqrt B
  set g := Real.sqrt G
  have hc : 0 ≤ g / k := div_nonneg hg hk.le
  have h1 : (b - g / k) ^ 2 ≤ (a + g / k) ^ 2 := by
    have e : 2 / k * (b * g) = 2 * (g / k) * b := by ring
    rw [e] at h
    nlinarith [mul_nonneg ha hc]
  have h3 := abs_le_of_sq_le_sq h1 (by positivity)
  have h4 := (abs_le.mp h3).2
  have e2 : 2 / k * g = 2 * (g / k) := by ring
  rw [e2]; linarith

section pt
variable {M : ℕ}

theorem pt_bound (hM : 0 < M) (n : ℕ) (v : Torus M → ℝ) (x : Torus M) :
    (v x * Tt n v x / M) ^ 2 ≤
      (v x ^ 2 * ((Rr n x ^ 2 + Ii n x ^ 2) / M)) * ∑ j, (coordPartial j v x) ^ 2 := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hW : ∀ j, (Ii n x * Cc n j x - Rr n x * Ss n j x) ^ 2 ≤ Rr n x ^ 2 + Ii n x ^ 2 := by
    intro j
    have h := Cc_sq_add_Ss_sq n j x
    have e : (Ii n x * Cc n j x - Rr n x * Ss n j x) ^ 2 + (Ii n x * Ss n j x + Rr n x * Cc n j x) ^ 2
        = (Rr n x ^ 2 + Ii n x ^ 2) * (Cc n j x ^ 2 + Ss n j x ^ 2) := by ring
    rw [h] at e
    nlinarith [sq_nonneg (Ii n x * Ss n j x + Rr n x * Cc n j x)]
  have hT : Tt n v x ^ 2 ≤ (∑ j, (coordPartial j v x) ^ 2) * (M * (Rr n x ^ 2 + Ii n x ^ 2)) := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => coordPartial j v x)
      (fun j => Ii n x * Cc n j x - Rr n x * Ss n j x)
    have h2 : ∑ j, (Ii n x * Cc n j x - Rr n x * Ss n j x) ^ 2 ≤ M * (Rr n x ^ 2 + Ii n x ^ 2) := by
      calc _ ≤ ∑ _j : Fin M, (Rr n x ^ 2 + Ii n x ^ 2) := Finset.sum_le_sum fun j _ => hW j
        _ = _ := by simp; ring
    have hG : 0 ≤ ∑ j, (coordPartial j v x) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    unfold Tt
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hG)
  calc (v x * Tt n v x / M) ^ 2 = v x ^ 2 * Tt n v x ^ 2 / (M : ℝ) ^ 2 := by
        rw [div_pow, mul_pow]
    _ ≤ v x ^ 2 * ((∑ j, (coordPartial j v x) ^ 2) * (M * (Rr n x ^ 2 + Ii n x ^ 2)))
          / (M : ℝ) ^ 2 := by gcongr
    _ = _ := by field_simp


theorem smooth_case (hM : 0 < M) (n : ℕ) (hn : n ≠ 0) {v : Torus M → ℝ} (hv : IsSmoothPeriodic v) :
    Real.sqrt (∫ x, v x ^ 2 * ((Rr n x ^ 2 + Ii n x ^ 2) / M) ∂haar M) ≤
      Real.sqrt (∫ x, v x ^ 2 ∂haar M) +
        2 / kk n * Real.sqrt (∫ x, ∑ j, (coordPartial j v x) ^ 2 ∂haar M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hk : 0 < kk n := by
    unfold kk
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  have hcv : Continuous v := hv.continuous_torus
  have hcR : Continuous (Rr (M := M) n) := (isSmooth_Rr n).continuous_torus
  have hcI : Continuous (Ii (M := M) n) := (isSmooth_Ii n).continuous_torus
  have hcp : ∀ j, Continuous (coordPartial j v) := fun j => hv.continuous_coordPartial j
  have hcT : Continuous (Tt n v) := by
    unfold Tt
    exact continuous_finsetSum _ fun j _ => by
      have := (isSmooth_Cc (M := M) n j).continuous_torus
      have := (isSmooth_Ss (M := M) n j).continuous_torus
      have := hcp j; fun_prop
  have hcG : Continuous (fun x => ∑ j, (coordPartial j v x) ^ 2) :=
    continuous_finsetSum _ fun j _ => by have := hcp j; fun_prop
  set Qd : Torus M → ℝ := fun x => (Rr n x ^ 2 + Ii n x ^ 2) / M with hQd
  have hQ0 : ∀ x, 0 ≤ Qd x := fun x => by positivity
  have hcQ : Continuous Qd := by simp only [hQd]; fun_prop
  set B := ∫ x, v x ^ 2 * Qd x ∂haar M with hB
  set A := ∫ x, v x ^ 2 ∂haar M with hA
  set G := ∫ x, ∑ j, (coordPartial j v x) ^ 2 ∂haar M with hG
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hQ0 x)
  -- the identity from integration by parts
  have hib := ibp_sum n hv
  have hBeq : B = (∫ x, (v x * v x) * (Rr n x ^ 2 + Ii n x ^ 2) ∂haar M) / M := by
    rw [← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hQd]; ring
  have hAeq : A = ∫ x, v x * v x ∂haar M := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  simp only [← sq] at hib hBeq hAeq
  -- pointwise bound and Cauchy-Schwarz
  set a : Torus M → ℝ := fun x => Real.sqrt (v x ^ 2 * Qd x) with ha
  set b : Torus M → ℝ := fun x => Real.sqrt (∑ j, (coordPartial j v x) ^ 2) with hb
  have hca : Continuous a := by simp only [ha]; fun_prop
  have hcb : Continuous b := by simp only [hb]; fun_prop
  have ha2 : ∀ x, a x ^ 2 = v x ^ 2 * Qd x := fun x =>
    Real.sq_sqrt (mul_nonneg (sq_nonneg _) (hQ0 x))
  have hb2 : ∀ x, b x ^ 2 = ∑ j, (coordPartial j v x) ^ 2 := fun x =>
    Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hpt : ∀ x, v x * Tt n v x / M ≤ a x * b x := by
    intro x
    have h := pt_bound hM n v x
    rw [← Real.sqrt_mul (mul_nonneg (sq_nonneg _) (hQ0 x))]
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by simpa [hQd] using h))
  have hJ : (∫ x, v x * Tt n v x ∂haar M) / M ≤ ∫ x, a x * b x ∂haar M := by
    rw [← integral_div]
    exact integral_mono (integrable_of_continuous (by fun_prop)) (integrable_of_continuous (by fun_prop)) hpt
  have hCS := integral_mul_le_sqrt (memLp_two_of_continuous hca) (memLp_two_of_continuous hcb)
  simp_rw [ha2, hb2] at hCS
  have hmain : B ≤ A + 2 / kk n * (Real.sqrt B * Real.sqrt G) := by
    have h1 : B = A + 2 / kk n * ((∫ x, v x * Tt n v x ∂haar M) / M) := by
      rw [hBeq, hAeq]
      field_simp
      linarith
    have h2 : (∫ x, v x * Tt n v x ∂haar M) / M ≤ Real.sqrt B * Real.sqrt G := hJ.trans hCS
    have : 2 / kk n * ((∫ x, v x * Tt n v x ∂haar M) / M) ≤ 2 / kk n * (Real.sqrt B * Real.sqrt G) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  exact quad_aux hA0 hB0 hk hmain

theorem weak_case (hM : 0 < M) (n : ℕ) (hn : n ≠ 0) {u : Torus M → ℝ} {g : Torus M → Tangent M}
    (hg : IsWeakGradient u g) :
    Real.sqrt (∫ x, u x ^ 2 * ((Rr n x ^ 2 + Ii n x ^ 2) / M) ∂haar M) ≤
      Real.sqrt (∫ x, u x ^ 2 ∂haar M) +
        2 / kk n * Real.sqrt (∫ x, ∑ j, (g x j) ^ 2 ∂haar M) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  obtain ⟨v, hs, -, h0, h1⟩ := exists_smooth_tendsto_H1 hg
  have hcR : Continuous (Rr n) := (isSmooth_Rr (M := M) n).continuous_torus
  have hcI : Continuous (Ii n) := (isSmooth_Ii (M := M) n).continuous_torus
  set s : Torus M → ℝ := fun x => Real.sqrt ((Rr n x ^ 2 + Ii n x ^ 2) / M) with hsdef
  have hcs : Continuous s := by simp only [hsdef]; fun_prop
  have hs2 : ∀ x, s x ^ 2 = (Rr n x ^ 2 + Ii n x ^ 2) / M := fun x =>
    Real.sq_sqrt (by positivity)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcs.continuousOn
  have hC' : ∀ x, ‖s x‖ ≤ C := fun x => hC x (Set.mem_univ x)
  -- A
  have TA : Tendsto (fun k => ∫ x, v k x ^ 2 ∂haar M) atTop (𝓝 (∫ x, u x ^ 2 ∂haar M)) :=
    tendsto_integral_sq_of_eLpNorm (fun k => memLp_two_of_smooth (hs k)) hg.memLp h0
  -- G
  have TG : Tendsto (fun k => ∫ x, ∑ j, (coordPartial j (v k) x) ^ 2 ∂haar M) atTop
      (𝓝 (∫ x, ∑ j, (g x j) ^ 2 ∂haar M)) := by
    have hj : ∀ j : Fin M, Tendsto (fun k => ∫ x, (coordPartial j (v k) x) ^ 2 ∂haar M) atTop
        (𝓝 (∫ x, (g x j) ^ 2 ∂haar M)) := fun j =>
      tendsto_integral_sq_of_eLpNorm (fun k => memLp_two_coordPartial (hs k) j)
        (memLp_coord_of_memLp hg.memLp_grad j) (h1 j)
    have hsum := tendsto_finsetSum Finset.univ fun j _ => hj j
    have e1 : ∀ k, ∫ x, ∑ j, (coordPartial j (v k) x) ^ 2 ∂haar M =
        ∑ j, ∫ x, (coordPartial j (v k) x) ^ 2 ∂haar M := fun k =>
      integral_finsetSum _ fun j _ => (memLp_two_coordPartial (hs k) j).integrable_sq
    have e2 : ∫ x, ∑ j, (g x j) ^ 2 ∂haar M = ∑ j, ∫ x, (g x j) ^ 2 ∂haar M :=
      integral_finsetSum _ fun j _ => (memLp_coord_of_memLp hg.memLp_grad j).integrable_sq
    simp_rw [e1, e2]
    exact hsum
  -- B
  have hW : MemLp (fun x => u x * s x) 2 (haar M) :=
    hg.memLp.of_le_mul (c := C) (hg.memLp.aestronglyMeasurable.mul hcs.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul]
        nlinarith [norm_nonneg (u x), norm_nonneg (s x), hC' x])
  have hnorm : Tendsto (fun k => eLpNorm ((fun x => v k x * s x) - fun x => u x * s x) 2 (haar M))
      atTop (𝓝 0) := by
    have hup : Tendsto (fun k => ENNReal.ofReal C * eLpNorm (fun x => v k x - u x) 2 (haar M))
        atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal C) h0 (Or.inr ENNReal.ofReal_ne_top)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => bot_le) ?_
    intro k
    have hwk : Continuous (fun x => v k x * s x) :=
      ((hs k).continuous_torus).mul hcs
    have hmeas : AEStronglyMeasurable ((fun x => v k x * s x) - fun x => u x * s x) (haar M) :=
      hwk.aestronglyMeasurable.sub hW.aestronglyMeasurable
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas (Eventually.of_forall fun x => ?_) 2
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    rw [← sub_mul, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa using hC' x) (abs_nonneg _)
  have TB0 := tendsto_integral_sq_of_eLpNorm
    (fun k => memLp_two_of_continuous (((hs k).continuous_torus).mul hcs)) hW hnorm
  have eB : ∀ f : Torus M → ℝ, ∫ x, (f x * s x) ^ 2 ∂haar M =
      ∫ x, f x ^ 2 * ((Rr n x ^ 2 + Ii n x ^ 2) / M) ∂haar M := fun f =>
    integral_congr_ae (Eventually.of_forall fun x => by simp only; rw [mul_pow, hs2])
  beta_reduce at TB0
  have TB := TB0.congr (fun k => eB (v k))
  rw [eB u] at TB
  have hle : ∀ k, Real.sqrt (∫ x, v k x ^ 2 * ((Rr n x ^ 2 + Ii n x ^ 2) / M) ∂haar M) ≤
      Real.sqrt (∫ x, v k x ^ 2 ∂haar M) +
        2 / kk n * Real.sqrt (∫ x, ∑ j, (coordPartial j (v k) x) ^ 2 ∂haar M) :=
    fun k => smooth_case hM n hn (hs k)
  exact le_of_tendsto_of_tendsto' TB.sqrt (TA.sqrt.add (TG.sqrt.const_mul _)) hle

end pt
/-- The identification `(𝕋¹)^N ≃ 𝕋^N`. -/
noncomputable def EE (N : ℕ+) : ParticleSpace 1 N ≃ᵐ Torus (N : ℕ) :=
  MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.funUnique (Fin 1) (AddCircle (1 : ℝ))

theorem EE_apply (N : ℕ+) (x : ParticleSpace 1 N) (i : Fin N) : EE N x i = x i 0 := rfl

theorem mp_EE (N : ℕ+) : MeasurePreserving (EE N) (particleHaar 1 N) (haar (N : ℕ)) := by
  have h := measurePreserving_pi (fun _ : Fin N => haar 1) (fun _ : Fin N => (volume : Measure (AddCircle (1:ℝ))))
    (f := fun _ => MeasurableEquiv.funUnique (Fin 1) (AddCircle (1 : ℝ)))
    (fun _ => measurePreserving_funUnique (volume : Measure (AddCircle (1:ℝ))) (Fin 1))
  exact h

noncomputable def LL (N : ℕ+) : (Fin N → Fin 1 → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) (0 : Fin 1)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin 1 → ℝ) i)

theorem EE_particleLift (N : ℕ+) (y : Fin N → Fin 1 → ℝ) :
    EE N (particleLift y) = torusLift (LL N y) := rfl

theorem secT_EE (N : ℕ+) (x : ParticleSpace 1 N) :
    SharpLSI.secT (EE N x) = LL N (fun k => SharpLSI.secT (x k)) := rfl

theorem isSmooth_comp_EE (N : ℕ+) {φ : Torus (N : ℕ) → ℝ} (hφ : IsSmoothPeriodic φ) :
    IsSmoothPeriodicParticle (fun x => φ (EE N x)) := by
  have : ((fun x => φ (EE N x)) ∘ particleLift) = (φ ∘ torusLift) ∘ LL N := rfl
  unfold IsSmoothPeriodicParticle
  rw [this]
  exact hφ.comp (LL N).contDiff

theorem particlePartial_comp_EE (N : ℕ+) {φ : Torus (N : ℕ) → ℝ} (hφ : IsSmoothPeriodic φ)
    (j : Fin N) (x : ParticleSpace 1 N) :
    particlePartial j 0 (fun x => φ (EE N x)) x = coordPartial j φ (EE N x) := by
  have h1 : ((fun x => φ (EE N x)) ∘ particleLift) = (φ ∘ torusLift) ∘ LL N := rfl
  unfold particlePartial coordPartial
  rw [h1, secT_EE]
  have hd : DifferentiableAt ℝ (φ ∘ torusLift) (LL N (fun k => SharpLSI.secT (x k))) :=
    (hφ.differentiable (by simp)) _
  rw [fderiv_comp _ hd (LL N).differentiableAt, (LL N).fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  funext i
  by_cases h : i = j <;> simp [LL, h]


section transport

variable (N : ℕ+)

/-- The weak gradient on `𝕋^N` obtained from a particle weak gradient (coordinate `(j,0)`). -/
noncomputable def gTorus (g : ParticleSpace 1 N → Fin N → Tangent 1) :
    Torus (N : ℕ) → Tangent (N : ℕ) :=
  fun y => WithLp.toLp 2 fun j => g ((EE N).symm y) j 0

theorem transport_weak {ψ : ParticleSpace 1 N → ℝ} {g : ParticleSpace 1 N → Fin N → Tangent 1}
    (hg : IsParticleHaarWeakGradient N ψ g) :
    IsWeakGradient (fun y => ψ ((EE N).symm y)) (gTorus N g) := by
  have hmp : MeasurePreserving (EE N).symm (haar (N : ℕ)) (particleHaar 1 N) := (mp_EE N).symm _
  refine ⟨hg.memLp.comp_measurePreserving hmp, ?_, ?_⟩
  · refine memLp_piLp_iff.2 fun j => ?_
    exact (memLp_particleCoord hg.memLp_grad j 0).comp_measurePreserving hmp
  · intro φ hφ j
    have hI := (mp_EE N).integral_comp' (fun y => ψ ((EE N).symm y) * coordPartial j φ y)
    have hJ := (mp_EE N).integral_comp' (fun y => gTorus N g y j * φ y)
    simp only [MeasurableEquiv.symm_apply_apply] at hI hJ
    rw [← hI, ← hJ]
    have := hg.ibp (fun x => φ (EE N x)) (isSmooth_comp_EE N hφ) j 0
    simp_rw [particlePartial_comp_EE N hφ] at this
    simpa [gTorus] using this

end transport


theorem mode_eq_mF (N : ℕ+) (n : ℕ) (x : ParticleSpace 1 N) (i : Fin N) :
    Particle.mode n (x i) = mF n i (EE N x) := by
  unfold Particle.mode mF UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk, Finset.univ_unique, Finset.prod_singleton]
  rw [Finset.prod_eq_single i]
  · simp [Fin.default_eq_zero, EE_apply]
  · intro k _ hk
    simp [hk]
  · simp

theorem normSq_S_eq (N : ℕ+) (n : ℕ) (x : ParticleSpace 1 N) :
    ‖Particle.S N n x‖ ^ 2 = Rr n (EE N x) ^ 2 + Ii n (EE N x) ^ 2 := by
  have hre : (Particle.S N n x).re = Rr n (EE N x) := by
    simp [Particle.S, Complex.re_sum, Rr, Cc, mode_eq_mF]
  have him : (Particle.S N n x).im = Ii n (EE N x) := by
    simp [Particle.S, Complex.im_sum, Ii, Ss, mode_eq_mF]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring

/-- **H1031.** Fourier coordinate multiplier: for `n ≠ 0`, `N ≥ 1` and `ψ ∈ H¹(Q_N)` (real valued,
with weak gradient `g`), `‖Z_{N,n} ψ‖₂ ≤ ‖ψ‖₂ + 2 (2π n)⁻¹ ‖∇ψ‖₂`. -/
theorem particle_fourier_coordinate_multiplier (N : ℕ+) (n : ℕ) (hn : n ≠ 0)
    {ψ : ParticleSpace 1 N → ℝ} {g : ParticleSpace 1 N → Fin N → Tangent 1}
    (hg : IsParticleHaarWeakGradient N ψ g) :
    Real.sqrt (∫ x, ‖Particle.Z N n x * (ψ x : ℂ)‖ ^ 2 ∂particleHaar 1 N) ≤
      Real.sqrt (∫ x, ψ x ^ 2 ∂particleHaar 1 N) +
        2 / (2 * Real.pi * n) *
          Real.sqrt (∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N) := by
  have hN : 0 < (N : ℕ) := N.pos
  have hw := weak_case hN n hn (transport_weak N hg)
  have e1 := (mp_EE N).integral_comp' (fun y => ψ ((EE N).symm y) ^ 2 *
    ((Rr n y ^ 2 + Ii n y ^ 2) / (N : ℕ)))
  have e2 := (mp_EE N).integral_comp' (fun y => ψ ((EE N).symm y) ^ 2)
  have e3 := (mp_EE N).integral_comp' (fun y => ∑ j, (gTorus N g y j) ^ 2)
  simp only [MeasurableEquiv.symm_apply_apply] at e1 e2 e3
  rw [← e1, ← e2, ← e3] at hw
  have hZ : ∀ x : ParticleSpace 1 N, ‖Particle.Z N n x * (ψ x : ℂ)‖ ^ 2 =
      ψ x ^ 2 * ((Rr n (EE N x) ^ 2 + Ii n (EE N x) ^ 2) / (N : ℕ)) := by
    intro x
    rw [norm_mul, mul_pow, Particle.norm_Z_sq, normSq_S_eq, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
    ring
  have hG : ∀ x : ParticleSpace 1 N, ∑ j, (gTorus N g (EE N x) j) ^ 2 =
      particleTangentNormSq (g x) := by
    intro x
    rw [particleTangentNormSq_eq]
    simp [gTorus]
  simp_rw [hG] at hw
  simp_rw [hZ]
  exact hw

end DGPS.Examples.PositiveH1.Transfer
