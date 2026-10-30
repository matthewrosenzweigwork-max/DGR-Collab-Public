import DGPS.Frontier.STR029.T24

/-! Exact amplitude-Hessian scaling from the actual reduced extension. The optimal-rate
parameter is frozen; the identity uses the local T20 value formula, not an IFT Jacobian. -/

noncomputable section
open Filter Set
open scoped ContDiff Topology
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem hessian_const_smul (F : (ℝ × ℝ) → ℝ) (c : ℝ) (hc : c ≠ 0)
    (x v z : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => c • F y)) x v z =
      c * fderiv ℝ (fderiv ℝ F) x v z := by
  letI : Invertible c := invertibleOfNonzero hc
  have hd : fderiv ℝ (fun y => c • F y) = c • fderiv ℝ F := by
    funext y
    exact fderiv_const_smul_of_invertible c
  rw [hd, fderiv_const_smul_of_invertible (𝕜 := ℝ) (f := fderiv ℝ F) (x := x) c]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

private theorem hessian_comp_smul (F : (ℝ × ℝ) → ℝ) (h : ℝ) (hh : h ≠ 0)
    (x v z : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => F (h • y))) x v z =
      h ^ 2 * fderiv ℝ (fderiv ℝ F) (h • x) v z := by
  letI : Invertible h := invertibleOfNonzero hh
  have hd : fderiv ℝ (fun y => F (h • y)) =
      h • (fun y => fderiv ℝ F (h • y)) := by
    funext y
    exact fderiv_comp_smul h
  rw [hd, fderiv_const_smul_of_invertible (𝕜 := ℝ)
    (f := fun y => fderiv ℝ F (h • y)) (x := x) h,
    fderiv_comp_smul (𝕜 := ℝ) (f := fderiv ℝ F) (x := x) h]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, pow_two]
  ring

/-- The actual unscaled-amplitude Hessian has exactly h² times the scaled-amplitude
Hessian. Both h and the optimal-rate parameter s are fixed during differentiation. -/
theorem ordinaryReduced_hessian_scale
    (ψ : Par_STR02916 → E_STR02969) (E : ℝ × (Fin 3 → ℝ) → ℝ)
    {O : Set (ℝ × (Fin 3 → ℝ))} (hO : IsOpen O)
    (hval : ∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
      E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4)
    (h s : ℝ) (hh : h ≠ 0) (x v z : ℝ × ℝ)
    (hx : (h, ![x.1, x.2, s]) ∈ O) :
    fderiv ℝ (fderiv ℝ (fun y => Fred_STR02956 ψ y (h, h ^ 2 * s)))
        (h • x) v z =
      h ^ 2 * fderiv ℝ (fderiv ℝ (fun y : ℝ × ℝ => E (h, ![y.1, y.2, s]))) x v z := by
  let F : (ℝ × ℝ) → ℝ := fun y => Fred_STR02956 ψ y (h, h ^ 2 * s)
  let A : (ℝ × ℝ) → ℝ := fun y => E (h, ![y.1, y.2, s])
  have hmap : Continuous (fun y : ℝ × ℝ => (h, ![y.1, y.2, s])) := by fun_prop
  have heq : A =ᶠ[𝓝 x] fun y => (h ^ 4)⁻¹ • F (h • y) := by
    filter_upwards [hmap.continuousAt.tendsto.eventually (hO.mem_nhds hx)] with y hy
    dsimp only [A, F]
    rw [hval h ![y.1, y.2, s] hy hh]
    change Fred_STR02956 ψ (h * y.1, h * y.2) (h, h ^ 2 * s) / h ^ 4 =
      (h ^ 4)⁻¹ * Fred_STR02956 ψ (h * y.1, h * y.2) (h, h ^ 2 * s)
    rw [div_eq_mul_inv]
    ring
  have hsec : fderiv ℝ (fderiv ℝ A) x =
      fderiv ℝ (fderiv ℝ (fun y => (h ^ 4)⁻¹ • F (h • y))) x :=
    heq.fderiv.fderiv_eq
  have hvz := congrArg (fun H => H v z) hsec
  rw [hessian_const_smul (fun y => F (h • y)) _ (inv_ne_zero (pow_ne_zero 4 hh)),
    hessian_comp_smul F h hh] at hvz
  change fderiv ℝ (fderiv ℝ F) (h • x) v z =
    h ^ 2 * fderiv ℝ (fderiv ℝ A) x v z
  symm
  calc
    _ = h ^ 2 * ((h ^ 4)⁻¹ * (h ^ 2 * fderiv ℝ (fderiv ℝ F) (h • x) v z)) := by rw [hvz]
    _ = _ := by field_simp [hh]

end DGPS.Examples.ThreeSpeciesCircle
