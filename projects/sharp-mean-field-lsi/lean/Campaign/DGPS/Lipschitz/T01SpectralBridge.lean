import DGPS.Lipschitz.KernelApproximation
import DGPS.Lipschitz.HessianKernel
import DGPS.Particle.DiagonalForce

/-!
# Centered kernel data for the direct-Lipschitz lower-bound argument

The spectral approximation lemmas take a `KData` provider. This adapter constructs it for the
actual centered interaction kernel, keeping its pointwise diagonal and bounded weak gradients.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace DGPS.Lipschitz

open KernelApproximation ParabolicChainRule

variable {d : ℕ}

theorem centeredKernel_lipschitz (A : InteractionData d) (hA : LipschitzData A)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y x' y',
      |centeredKernel A μ x y - centeredKernel A μ x' y'| ≤
        L * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) := by
  obtain ⟨LW, hLW⟩ := hA.W_lipschitz
  have hx : ∀ y, TorusLipschitzWith |LW| fun x => A.W x y := by
    intro y x x'
    have h := hLW x y x' y
    have h0 : 0 ≤ torusDist x x' := Real.sqrt_nonneg _
    simp only [torusDist_metric.1 y, zero_pow (by decide : 2 ≠ 0), add_zero,
      Real.sqrt_sq h0] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self LW) h0)
  have hc := lipschitz_integral_of_lipschitz A.W_continuous hx μ
  have hk : ∀ x x' y, |centeredKernel A μ x y - centeredKernel A μ x' y| ≤
      2 * |LW| * torusDist x x' := by
    intro x x' y
    have he : centeredKernel A μ x y - centeredKernel A μ x' y =
        (A.W x y - A.W x' y) -
          (interactionConvolution A μ x - interactionConvolution A μ x') := by
      unfold centeredKernel
      ring
    rw [he]
    have hW : |A.W x y - A.W x' y| ≤ |LW| * torusDist x x' := hx y x x'
    have hconv : |interactionConvolution A μ x - interactionConvolution A μ x'| ≤
        |LW| * torusDist x x' := hc x x'
    calc _ ≤ |A.W x y - A.W x' y| +
          |interactionConvolution A μ x - interactionConvolution A μ x'| := abs_sub _ _
      _ ≤ |LW| * torusDist x x' + |LW| * torusDist x x' := add_le_add hW hconv
      _ = _ := by ring
  refine ⟨4 * |LW|, by positivity, fun x y x' y' => ?_⟩
  have hfirst := hk x x' y
  have hsecond : |centeredKernel A μ x' y - centeredKernel A μ x' y'| ≤
      2 * |LW| * torusDist y y' := by
    rw [centeredKernel_symm A μ x' y, centeredKernel_symm A μ x' y']
    exact hk y y' x'
  have hdx : torusDist x x' ≤ Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) := by
    calc torusDist x x' = Real.sqrt (torusDist x x' ^ 2) :=
          (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
  have hdy : torusDist y y' ≤ Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) := by
    calc torusDist y y' = Real.sqrt (torusDist y y' ^ 2) :=
          (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _))
  calc |centeredKernel A μ x y - centeredKernel A μ x' y'|
      ≤ |centeredKernel A μ x y - centeredKernel A μ x' y| +
          |centeredKernel A μ x' y - centeredKernel A μ x' y'| := abs_sub_le _ _ _
    _ ≤ 2 * |LW| * torusDist x x' + 2 * |LW| * torusDist y y' :=
      add_le_add hfirst hsecond
    _ ≤ 2 * |LW| * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) +
        2 * |LW| * Real.sqrt (torusDist x x' ^ 2 + torusDist y y' ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hdx (by positivity))
        (mul_le_mul_of_nonneg_left hdy (by positivity))
    _ = _ := by ring

/-- The actual centered kernel admits the input data required by the bounded-drift spectral
approximation. No regularity stronger than direct Lipschitz regularity is assumed. -/
theorem exists_centeredKernel_data (A : InteractionData d) (hA : LipschitzData A)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∃ D : KData d, D.K = centeredKernel A μ := by
  obtain ⟨L, hL, hK⟩ := centeredKernel_lipschitz A hA μ
  obtain ⟨B, hBm, hBb, hBg⟩ := df_exists_B hL hK
  refine ⟨{
    K := centeredKernel A μ
    G1 := B
    G2 := fun x y => B y x
    Kc := centeredKernel_continuous A μ
    G1m := hBm
    G2m := hBm.comp measurable_swap
    B := L
    G1b := hBb
    G2b := fun x y => hBb y x
    g1 := hBg
    g2 := fun x => ?_
  }, rfl⟩
  have he : (fun y => centeredKernel A μ x y) = fun y => centeredKernel A μ y x :=
    funext fun y => centeredKernel_symm A μ x y
  rw [he]
  exact hBg x

/-- The diagonal is differentiated as a Lipschitz function in its own right. Values of ambient
slice gradients on the diagonal are not used. -/
theorem exists_centeredKernel_diagonal_gradient (A : InteractionData d) (hA : LipschitzData A)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∃ g : Torus d → Tangent d, Measurable g ∧
      (∃ M : ℝ, ∀ x, ‖g x‖ ≤ M) ∧ IsWeakGradient (fun x => centeredKernel A μ x x) g := by
  obtain ⟨L, hL, hK⟩ := centeredKernel_lipschitz A hA μ
  have hδ : TorusLipschitzWith (Real.sqrt 2 * L) (fun x => centeredKernel A μ x x) :=
    df_diag_lipschitz hK
  have hM : 0 ≤ Real.sqrt 2 * L := mul_nonneg (Real.sqrt_nonneg _) hL
  obtain ⟨hw, hb⟩ := exists_weak_gradient hM hδ
  let g : Torus d → Tangent d := fun x =>
    if ‖smoothGrad (fun y => centeredKernel A μ y y) x‖ ≤ Real.sqrt 2 * L then
      smoothGrad (fun y => centeredKernel A μ y y) x else 0
  refine ⟨g, ?_, ⟨Real.sqrt 2 * L, fun x => ?_⟩, ?_⟩
  · exact Measurable.ite (measurableSet_le measurable_smoothGrad.norm measurable_const)
      measurable_smoothGrad measurable_const
  · dsimp only [g]
    split_ifs with h
    · exact h
    · simpa using hM
  · have hw2 : IsWeakGradient (fun x => centeredKernel A μ x x)
        (smoothGrad (fun x => centeredKernel A μ x x)) :=
      isWeakGradient_iff_isWeakGradientLp.mpr
        ⟨hw.memLp.mono_exponent (by simp), hw.memLp_grad.mono_exponent (by simp), hw.ibp⟩
    refine hw2.congr_ae (Filter.EventuallyEq.refl _ _) ?_
    filter_upwards [hb] with x hx
    simp only [g, if_pos hx]

/-- A direct-Lipschitz equilibrium has one common spectral basis for its actual measure and
the centered kernel data, rather than independent existential spectral witnesses. -/
theorem exists_equilibrium_spectral_data (A : InteractionData d) (hA : LipschitzData A)
    (hd : 0 < d) (μ : ProbabilityMeasure (Torus d))
    (hμ : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    ∃ (S : Spec d) (aux : Aux S) (D : KData d),
      S.mu = (μ : Measure (Torus d)) ∧ Monotone S.lam ∧ S.lam 0 = 0 ∧
      S.lam 0 < S.lam 1 ∧ (∀ j, IsC1Periodic (S.v j)) ∧
      (∀ j (f : DGPS.Analysis.CompactResolvent.Hw d S.w) (Y : Torus d → Tangent d),
        IsWeakGradient (f : Torus d → ℝ) Y →
        weightedForm S.w (aux.g j) Y = S.lam j * inner ℝ (S.e j) f) ∧
      D.K = centeredKernel A S.mu := by
  obtain ⟨L, hL, hΦ⟩ := lipschitz_equilibriumPotential A hA
  have hgrad := weak_gradient_log_gibbsDensity A (μ : Measure (Torus d))
    (exists_weak_gradient hL (hΦ (μ : Measure (Torus d)))).1
  have hlog : IsWeakGradient
      (fun x => Real.log (WeightedGenerator.gibbsW (equilibriumPotential A μ) x))
      (fun x => -smoothGrad (equilibriumPotential A μ) x) := by
    apply isWeakGradient_iff_isWeakGradientLp.mpr
    simpa only [WeightedGenerator.gibbsW, gibbsDensity, gibbsPartition] using
      (show IsWeakGradientLp 2 (fun x => Real.log (gibbsDensity A μ x))
        (fun x => -smoothGrad (equilibriumPotential A μ) x) from
        ⟨hgrad.memLp.mono_exponent (by simp), hgrad.memLp_grad.mono_exponent (by simp), hgrad.ibp⟩)
  obtain ⟨S, aux, hw, hmono, hl0, hl01, hC1, hE⟩ :=
    exists_spec_aux_eigen hd hL (hΦ (μ : Measure (Torus d))) hlog
  have hS : S.mu = (μ : Measure (Torus d)) := by
    rw [minimizer_eq_gibbs A μ hμ, gibbsMeasure_eq_withDensity]
    change DGPS.Analysis.CompactResolvent.wMeasure d S.w = _
    rw [hw]
    rfl
  obtain ⟨D, hD⟩ := exists_centeredKernel_data A hA (μ : Measure (Torus d))
  refine ⟨S, aux, D, hS, hmono, hl0, hl01, hC1, hE, ?_⟩
  rw [hS]
  exact hD

end DGPS.Lipschitz
