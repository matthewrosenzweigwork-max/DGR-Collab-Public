import DGPS.FiniteN.AnisotropicQuarticRareTestSupport

/-! Exact native derivatives of the actual empirical field. -/

open DGPS.Models DGPS.FiniteN.ScalarFoldFIN064
open scoped ContDiff

namespace DGPS.FiniteN

theorem quartic_empirical_cos_partial (N : ℕ+) (i : Fin N) (x : ParticleSpace 1 N) :
    particlePartial i 0 (quarticEmpiricalCos N) x =
      -(2 * Real.pi * quarticKappa / (N : ℝ)) * scalarSin (x i) := by
  let a : Fin N → Fin 1 → ℝ := fun k => SharpLSI.secT (x k)
  let e : Fin N → (Fin N → Fin 1 → ℝ) →L[ℝ] ℝ := fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin 1 → ℝ) k)
  have hc : ∀ k : Fin N, HasFDerivAt (fun z : Fin N → Fin 1 → ℝ =>
      Real.cos (2 * Real.pi * z k 0))
      (-Real.sin (2 * Real.pi * a k 0) • ((2 * Real.pi) • e k)) a := by
    intro k
    have heval : HasFDerivAt (fun z : Fin N → Fin 1 → ℝ => z k 0) (e k) a := by
      change HasFDerivAt (e k) (e k) a
      exact (e k).hasFDerivAt
    exact (heval.const_mul (2 * Real.pi)).cos
  have hd := (((HasFDerivAt.fun_sum fun k (_ : k ∈ (Finset.univ : Finset (Fin N))) => hc k).const_mul
    quarticKappa).mul_const (N : ℝ)⁻¹).const_add 1
  have he : quarticEmpiricalCos N ∘ particleLift = fun z : Fin N → Fin 1 → ℝ =>
      1 + quarticKappa * (∑ k, Real.cos (2 * Real.pi * z k 0)) * (N : ℝ)⁻¹ := by
    funext z
    simp only [Function.comp_apply, quarticEmpiricalCos, particleLift, scalarCos_lift, div_eq_mul_inv]
  have hs : Real.sin (2 * Real.pi * a i 0) = scalarSin (x i) := by
    rw [← scalarSin_lift]
    congr 1
    simp only [a, torusLift, SharpLSI.liftT_secT]
  unfold particlePartial
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.single_apply, e]
  have hb : ∀ k : Fin N,
      (if k = i then (Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ) else (0 : Fin 1 → ℝ)) (0 : Fin 1) =
        if k = i then 1 else 0 := by
    intro k
    by_cases h : k = i <;> simp [h]
  simp_rw [hb]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hs]
  ring

theorem quartic_empirical_sin_partial (N : ℕ+) (i : Fin N) (x : ParticleSpace 1 N) :
    particlePartial i 0 (quarticEmpiricalSin N) x =
      (2 * Real.pi * (quarticKappa * quarticEta) / (N : ℝ)) * scalarCos (x i) := by
  let a : Fin N → Fin 1 → ℝ := fun k => SharpLSI.secT (x k)
  let e : Fin N → (Fin N → Fin 1 → ℝ) →L[ℝ] ℝ := fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Fin 1 → ℝ) k)
  have hc : ∀ k : Fin N, HasFDerivAt (fun z : Fin N → Fin 1 → ℝ =>
      Real.sin (2 * Real.pi * z k 0))
      (Real.cos (2 * Real.pi * a k 0) • ((2 * Real.pi) • e k)) a := by
    intro k
    have heval : HasFDerivAt (fun z : Fin N → Fin 1 → ℝ => z k 0) (e k) a := by
      change HasFDerivAt (e k) (e k) a
      exact (e k).hasFDerivAt
    exact (heval.const_mul (2 * Real.pi)).sin
  have hd := ((HasFDerivAt.fun_sum fun k (_ : k ∈ (Finset.univ : Finset (Fin N))) => hc k).const_mul
    (quarticKappa * quarticEta)).mul_const (N : ℝ)⁻¹
  have he : quarticEmpiricalSin N ∘ particleLift = fun z : Fin N → Fin 1 → ℝ =>
      (quarticKappa * quarticEta) * (∑ k, Real.sin (2 * Real.pi * z k 0)) * (N : ℝ)⁻¹ := by
    funext z
    simp only [Function.comp_apply, quarticEmpiricalSin, particleLift, scalarSin_lift, div_eq_mul_inv]
  have hs : Real.cos (2 * Real.pi * a i 0) = scalarCos (x i) := by
    rw [← scalarCos_lift]
    congr 1
    simp only [a, torusLift, SharpLSI.liftT_secT]
  unfold particlePartial
  rw [he, hd.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Pi.single_apply, e]
  have hb : ∀ k : Fin N,
      (if k = i then (Pi.single (0 : Fin 1) (1 : ℝ) : Fin 1 → ℝ) else (0 : Fin 1 → ℝ)) (0 : Fin 1) =
        if k = i then 1 else 0 := by
    intro k
    by_cases h : k = i <;> simp [h]
  simp_rw [hb]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [hs]
  ring

end DGPS.FiniteN
