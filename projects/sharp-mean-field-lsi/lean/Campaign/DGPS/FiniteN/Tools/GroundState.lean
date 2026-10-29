import DGPS.Foundations.PeriodicSmoothing
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory Real
open scoped ContDiff

/-!
# FIN016: ground state weighted energy identity

For smooth `ψ` and smooth compactly supported `F` on `ℝ^k` (`EuclideanSpace ℝ (Fin k)`), with
`G = F e^{-Nψ/2}`,
`∫ |∇F|² e^{-Nψ} = ∫ [|∇G|² + (N²|∇ψ|²/4 - NΔψ/2) G²]`; the same identity holds for the
derivative `∂_v` in one fixed direction `v`; and on the torus `𝕋^d` (Haar probability measure),
for `g = f e^{-H/2}`, `∫ |∇g|² = ∫ [|∇f|² + (ΔH/2 - |∇H|²/4) f²] e^{-H}`.

Conventions: `|∇F|² = ‖fderiv ℝ F x‖²` and `Δ` is Mathlib's `Laplacian.laplacian` on `ℝ^k`;
on the torus `|∇f|² = ∑ⱼ (∂ⱼ f)²`, `ΔH = ∑ⱼ ∂ⱼ ∂ⱼ H` with `coordPartial`. `N` is any real.
The core is the pointwise identity `groundState_pointwise_identity` plus integration by parts.
-/

namespace DGPS.FiniteN

theorem groundState_pointwise_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℝ) (F ψ : E → ℝ) (hF : ContDiff ℝ 2 F) (hψ : ContDiff ℝ 2 ψ) (v x : E) :
    (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x)) =
      (fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x v) ^ 2
        + (N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4 - N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2)
          * (F x * exp (-(N * ψ x) / 2)) ^ 2
        + N / 2 * fderiv ℝ (fun y => F y * F y * fderiv ℝ ψ y v * exp (-(N * ψ y))) x v := by
  have hF1 : HasFDerivAt F (fderiv ℝ F x) x :=
    ((hF.differentiable (by norm_num)) x).hasFDerivAt
  have hψ1 : HasFDerivAt ψ (fderiv ℝ ψ x) x :=
    ((hψ.differentiable (by norm_num)) x).hasFDerivAt
  have hP : ContDiff ℝ 1 (fun y => fderiv ℝ ψ y v) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hP1 : HasFDerivAt (fun y => fderiv ℝ ψ y v) (fderiv ℝ (fun y => fderiv ℝ ψ y v) x) x :=
    ((hP.differentiable (by norm_num)) x).hasFDerivAt
  have hw0 : HasFDerivAt (fun y => exp ((-(N / 2)) * ψ y))
      (exp ((-(N / 2)) * ψ x) • ((-(N / 2)) • fderiv ℝ ψ x)) x :=
    (hψ1.const_mul (-(N / 2))).exp
  have hw : HasFDerivAt (fun y => exp (-(N * ψ y) / 2))
      (exp (-(N * ψ x) / 2) • ((-(N / 2)) • fderiv ℝ ψ x)) x := by
    have h1 : (fun y => exp (-(N * ψ y) / 2)) = fun y => exp ((-(N / 2)) * ψ y) := by
      funext y; congr 1; ring
    have h2 : exp (-(N * ψ x) / 2) = exp ((-(N / 2)) * ψ x) := by congr 1; ring
    rw [h1, h2]; exact hw0
  have hE0 : HasFDerivAt (fun y => exp ((-N) * ψ y))
      (exp ((-N) * ψ x) • ((-N) • fderiv ℝ ψ x)) x :=
    (hψ1.const_mul (-N)).exp
  have hE : HasFDerivAt (fun y => exp (-(N * ψ y)))
      (exp (-(N * ψ x)) • ((-N) • fderiv ℝ ψ x)) x := by
    have h1 : (fun y => exp (-(N * ψ y))) = fun y => exp ((-N) * ψ y) := by
      funext y; congr 1; ring
    have h2 : exp (-(N * ψ x)) = exp ((-N) * ψ x) := by congr 1; ring
    rw [h1, h2]; exact hE0
  have hG := hF1.fun_mul hw
  have hH := (((hF1.fun_mul hF1).fun_mul hP1).fun_mul hE)
  have e1 : fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x v
      = fderiv ℝ F x v * exp (-(N * ψ x) / 2) + F x * (exp (-(N * ψ x) / 2) * (-(N / 2) * fderiv ℝ ψ x v)) := by
    rw [hG.fderiv]; simp; ring
  have e2 : fderiv ℝ (fun y => F y * F y * fderiv ℝ ψ y v * exp (-(N * ψ y))) x v
      = ((fderiv ℝ F x v * F x + F x * fderiv ℝ F x v) * fderiv ℝ ψ x v + F x * F x * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v) * exp (-(N * ψ x))
        + F x * F x * fderiv ℝ ψ x v * (exp (-(N * ψ x)) * (-N * fderiv ℝ ψ x v)) := by
    rw [hH.fderiv]; simp; ring
  have hww : exp (-(N * ψ x) / 2) ^ 2 = exp (-(N * ψ x)) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e1, e2, ← hww]
  ring


/-- Directional identity with integrability data (auxiliary). -/
theorem groundState_direction_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
    (N : ℝ) (ψ F : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (v : E) :
    Integrable (fun x => (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x))) μ ∧
    Integrable (fun x => (fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x v) ^ 2
        + (N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4 - N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2)
          * (F x * exp (-(N * ψ x) / 2)) ^ 2) μ ∧
    ∫ x, (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x)) ∂μ =
      ∫ x, ((fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x v) ^ 2
        + (N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4 - N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2)
          * (F x * exp (-(N * ψ x) / 2)) ^ 2) ∂μ := by
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  have hP : ContDiff ℝ ∞ (fun y => fderiv ℝ ψ y v) :=
    (hψ.fderiv_right (m := ∞) (by norm_num)).clm_apply contDiff_const
  have hEc : ContDiff ℝ ∞ (fun y => exp (-(N * ψ y))) :=
    (contDiff_exp.comp (contDiff_const.mul hψ).neg)
  set h : E → ℝ := fun y => F y * F y * fderiv ℝ ψ y v * exp (-(N * ψ y)) with hh
  have hhs : ContDiff ℝ ∞ h := ((hF.mul hF).mul hP).mul hEc
  have hhc : HasCompactSupport h := by
    have : h = ((F * F) * (fun y => fderiv ℝ ψ y v)) * (fun y => exp (-(N * ψ y))) := rfl
    rw [this]
    exact (hFc.mul_right.mul_right).mul_right
  have hDh_int : Integrable (fun x => fderiv ℝ h x v) μ :=
    ((hhs.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hhc.fderiv_apply ℝ v)
  have hDh0 : ∫ x, fderiv ℝ h x v ∂μ = 0 := by
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := h)
      (g := fun _ : E => (1 : ℝ)) (v := v) (by simpa using hDh_int) (by simp)
      (by simpa using hhs.continuous.integrable_of_hasCompactSupport hhc)
      (fun x _ => (hhs.differentiable (by simp)) x) (fun x _ => differentiableAt_const _)
    simpa using this
  have hLc : HasCompactSupport (fun x => (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x))) := by
    have : (fun x => (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x))) =
        (((fun x => fderiv ℝ F x v) * (fun x => fderiv ℝ F x v)) * (fun y => exp (-(N * ψ y)))) := by
      funext x; simp [sq]
    rw [this]
    exact ((hFc.fderiv_apply ℝ v).mul_right).mul_right
  have hLint : Integrable (fun x => (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x))) μ := by
    refine Continuous.integrable_of_hasCompactSupport ?_ hLc
    exact (((hF.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2).mul
      hEc.continuous
  have hpt : (fun x => (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x))) = fun x =>
      ((fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x v) ^ 2
        + (N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4 - N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2)
          * (F x * exp (-(N * ψ x) / 2)) ^ 2) + N / 2 * fderiv ℝ h x v := by
    funext x
    exact groundState_pointwise_identity N F ψ hF2 hψ2 v x
  have hRint : Integrable (fun x =>
      ((fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x v) ^ 2
        + (N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4 - N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2)
          * (F x * exp (-(N * ψ x) / 2)) ^ 2)) μ := by
    have := hLint.sub (hDh_int.const_mul (N / 2))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    have := congrFun hpt x
    simp only [Pi.sub_apply] at this ⊢
    linarith
  refine ⟨hLint, hRint, ?_⟩
  rw [hpt]
  rw [integral_add hRint (hDh_int.const_mul (N / 2)), integral_const_mul, hDh0]
  simp


/-! ### Euclidean space -/

section Euclid

variable {k : ℕ}

theorem groundState_norm_sq_eq_sum_basis (l : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) :
    ‖l‖ ^ 2 = ∑ i, (l (EuclideanSpace.basisFun (Fin k) ℝ i)) ^ 2 := by
  set b := EuclideanSpace.basisFun (Fin k) ℝ
  set w := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm l with hw
  have h1 : ‖l‖ = ‖w‖ := by
    rw [hw, LinearIsometryEquiv.norm_map]
  have h2 := b.sum_sq_norm_inner_right w
  rw [h1, ← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : inner ℝ (b i) w = l (b i) := by
    rw [real_inner_comm, hw, InnerProductSpace.toDual_symm_apply]
  rw [this, Real.norm_eq_abs, sq_abs]

theorem groundState_laplacian_eq_sum_basis (ψ : EuclideanSpace ℝ (Fin k) → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (x : EuclideanSpace ℝ (Fin k)) :
    Laplacian.laplacian ψ x = ∑ i, fderiv ℝ (fun y => fderiv ℝ ψ y
      (EuclideanSpace.basisFun (Fin k) ℝ i)) x (EuclideanSpace.basisFun (Fin k) ℝ i) := by
  have := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ψ
    (EuclideanSpace.basisFun (Fin k) ℝ)) x
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  set e := EuclideanSpace.basisFun (Fin k) ℝ i
  rw [iteratedFDeriv_two_apply]
  have hd : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  have : fderiv ℝ (fun y => fderiv ℝ ψ y e) x = (fderiv ℝ (fderiv ℝ ψ) x).flip e := by
    rw [fderiv_clm_apply (hd x) (differentiableAt_const e)]
    simp
  simp [this]


/-- FIN016, Euclidean full-gradient form: for smooth `ψ` and smooth compactly supported `F` on
`ℝ^k`, with `G = F e^{-Nψ/2}`,
`∫ |∇F|² e^{-Nψ} = ∫ [|∇G|² + (N²|∇ψ|²/4 - NΔψ/2) G²]`. -/
theorem ground_state_weighted_energy_identity_euclidean (N : ℝ)
    (ψ F : EuclideanSpace ℝ (Fin k) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) :
    ∫ x, ‖fderiv ℝ F x‖ ^ 2 * exp (-(N * ψ x)) =
      ∫ x, (‖fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x‖ ^ 2
        + (N ^ 2 * ‖fderiv ℝ ψ x‖ ^ 2 / 4 - N * Laplacian.laplacian ψ x / 2)
          * (F x * exp (-(N * ψ x) / 2)) ^ 2) := by
  set b := EuclideanSpace.basisFun (Fin k) ℝ
  have hd := fun i => groundState_direction_aux (μ := (volume : Measure (EuclideanSpace ℝ (Fin k))))
    N ψ F hψ hF hFc (b i)
  have hL : ∀ x, ‖fderiv ℝ F x‖ ^ 2 * exp (-(N * ψ x)) =
      ∑ i, (fderiv ℝ F x (b i)) ^ 2 * exp (-(N * ψ x)) := by
    intro x; rw [groundState_norm_sq_eq_sum_basis, Finset.sum_mul]
  have hR : ∀ x, (‖fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x‖ ^ 2
        + (N ^ 2 * ‖fderiv ℝ ψ x‖ ^ 2 / 4 - N * Laplacian.laplacian ψ x / 2)
          * (F x * exp (-(N * ψ x) / 2)) ^ 2) =
      ∑ i, ((fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x (b i)) ^ 2
        + (N ^ 2 * (fderiv ℝ ψ x (b i)) ^ 2 / 4
            - N * fderiv ℝ (fun y => fderiv ℝ ψ y (b i)) x (b i) / 2)
          * (F x * exp (-(N * ψ x) / 2)) ^ 2) := by
    intro x
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, groundState_norm_sq_eq_sum_basis,
      groundState_laplacian_eq_sum_basis ψ hψ x]
    congr 1
    congr 1
    simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_div]
    rw [groundState_norm_sq_eq_sum_basis]
  simp_rw [hL, hR]
  rw [integral_finsetSum _ (fun i _ => (hd i).1), integral_finsetSum _ (fun i _ => (hd i).2.1)]
  exact Finset.sum_congr rfl fun i _ => (hd i).2.2

end Euclid

section DirectionPart

variable {k : ℕ}

/-- FIN016, fixed direction on `ℝ^k`. -/
theorem ground_state_weighted_energy_identity_direction (N : ℝ)
    (ψ F : EuclideanSpace ℝ (Fin k) → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (v : EuclideanSpace ℝ (Fin k)) :
    ∫ x, (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x)) =
      ∫ x, ((fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x v) ^ 2
        + (N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4 - N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2)
          * (F x * exp (-(N * ψ x) / 2)) ^ 2) :=
  (groundState_direction_aux N ψ F hψ hF hFc v).2.2

end DirectionPart

/-! ### The torus -/

section TorusPart

variable {d : ℕ}

theorem groundState_integrable_torus_of_continuous {u : Torus d → ℝ} (hu : Continuous u) :
    Integrable u (haar d) :=
  hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace u)

theorem groundState_isSmoothPeriodic_exp_neg_half {H : Torus d → ℝ} (hH : IsSmoothPeriodic H) :
    IsSmoothPeriodic (fun y => exp (-H y / 2)) := by
  unfold IsSmoothPeriodic at *
  exact contDiff_exp.comp ((hH.neg).div_const 2)

theorem groundState_isSmoothPeriodic_exp_neg {H : Torus d → ℝ} (hH : IsSmoothPeriodic H) :
    IsSmoothPeriodic (fun y => exp (-H y)) := by
  unfold IsSmoothPeriodic at *
  exact contDiff_exp.comp hH.neg


/-- Pointwise form of the torus identity in the coordinate direction `j`. -/
theorem groundState_torus_pointwise (H f : Torus d → ℝ) (hH : IsSmoothPeriodic H) (hf : IsSmoothPeriodic f)
    (j : Fin d) (y : Torus d) :
    (coordPartial j f y) ^ 2 * exp (-H y) =
      (coordPartial j (fun z => f z * exp (-H z / 2)) y) ^ 2
        + ((coordPartial j H y) ^ 2 / 4 - coordPartial j (coordPartial j H) y / 2)
          * (f y * exp (-H y / 2)) ^ 2
        + 1 / 2 * fderiv ℝ ((fun z => f z * f z * coordPartial j H z * exp (-H z)) ∘ torusLift)
            (SharpLSI.secT y) (Pi.single j 1) := by
  have hf2 : ContDiff ℝ 2 (f ∘ torusLift) := hf.of_le (by simp)
  have hH2 : ContDiff ℝ 2 (H ∘ torusLift) := hH.of_le (by simp)
  have key := groundState_pointwise_identity 1 (f ∘ torusLift) (H ∘ torusLift) hf2 hH2 (Pi.single j 1)
    (SharpLSI.secT y)
  have hg : (fun z => (f ∘ torusLift) z * exp (-(1 * (H ∘ torusLift) z) / 2)) =
      (fun z => f z * exp (-H z / 2)) ∘ torusLift := by
    funext z; simp
  have hW : (fun z => (f ∘ torusLift) z * (f ∘ torusLift) z * fderiv ℝ (H ∘ torusLift) z
      (Pi.single j 1) * exp (-(1 * (H ∘ torusLift) z))) =
      (fun z => f z * f z * coordPartial j H z * exp (-H z)) ∘ torusLift := by
    funext z
    have := congrFun (coordPartial_comp_torusLift j H) z
    simp only [Function.comp_apply] at this ⊢
    rw [← this]; simp
  have hD2 : (fun z => fderiv ℝ (H ∘ torusLift) z (Pi.single j 1)) =
      coordPartial j H ∘ torusLift := (coordPartial_comp_torusLift j H).symm
  rw [hg, hW, hD2] at key
  have e1 : fderiv ℝ (f ∘ torusLift) (SharpLSI.secT y) (Pi.single j 1) = coordPartial j f y := rfl
  have e2 : fderiv ℝ ((fun z => f z * exp (-H z / 2)) ∘ torusLift) (SharpLSI.secT y)
      (Pi.single j 1) = coordPartial j (fun z => f z * exp (-H z / 2)) y := rfl
  have e3 : fderiv ℝ (coordPartial j H ∘ torusLift) (SharpLSI.secT y) (Pi.single j 1) =
      coordPartial j (coordPartial j H) y := rfl
  simp only [e1, e2, e3] at key
  simp only [Function.comp_apply, SharpLSI.liftT_secT, one_mul, one_pow] at key
  have e5 : fderiv ℝ (H ∘ torusLift) (SharpLSI.secT y) (Pi.single j 1) = coordPartial j H y := rfl
  rw [e5] at key
  exact key

/-- The auxiliary periodic function whose coordinate derivative integrates to zero. -/
noncomputable def groundStateBoundary (H f : Torus d → ℝ) (j : Fin d) : Torus d → ℝ :=
  fun z => f z * f z * coordPartial j H z * exp (-H z)

theorem isSmoothPeriodic_groundStateBoundary {H f : Torus d → ℝ} (hH : IsSmoothPeriodic H)
    (hf : IsSmoothPeriodic f) (j : Fin d) : IsSmoothPeriodic (groundStateBoundary H f j) :=
  ((hf.mul hf).mul (hH.isSmoothPeriodic_coordPartial j)).mul (groundState_isSmoothPeriodic_exp_neg hH)

/-- FIN016, torus form in the coordinate direction `j`. -/
theorem ground_state_weighted_energy_identity_torus_coord (H f : Torus d → ℝ)
    (hH : IsSmoothPeriodic H) (hf : IsSmoothPeriodic f) (j : Fin d) :
    Integrable (fun y => (coordPartial j f y) ^ 2 * exp (-H y)) (haar d) ∧
    Integrable (fun y => (coordPartial j (fun z => f z * exp (-H z / 2)) y) ^ 2) (haar d) ∧
    Integrable (fun y => (coordPartial j (fun z => f z * exp (-H z / 2)) y) ^ 2
        + ((coordPartial j H y) ^ 2 / 4 - coordPartial j (coordPartial j H) y / 2)
          * (f y * exp (-H y / 2)) ^ 2) (haar d) ∧
    ∫ y, (coordPartial j f y) ^ 2 * exp (-H y) ∂haar d =
      ∫ y, ((coordPartial j (fun z => f z * exp (-H z / 2)) y) ^ 2
        + ((coordPartial j H y) ^ 2 / 4 - coordPartial j (coordPartial j H) y / 2)
          * (f y * exp (-H y / 2)) ^ 2) ∂haar d := by
  have hg : IsSmoothPeriodic (fun z => f z * exp (-H z / 2)) :=
    hf.mul (groundState_isSmoothPeriodic_exp_neg_half hH)
  have hHj := hH.isSmoothPeriodic_coordPartial j
  have c1 : Continuous (fun y => (coordPartial j f y) ^ 2 * exp (-H y)) :=
    ((hf.continuous_coordPartial j).pow 2).mul (groundState_isSmoothPeriodic_exp_neg hH).continuous_torus
  have c2 : Continuous (fun y => (coordPartial j (fun z => f z * exp (-H z / 2)) y) ^ 2
        + ((coordPartial j H y) ^ 2 / 4 - coordPartial j (coordPartial j H) y / 2)
          * (f y * exp (-H y / 2)) ^ 2) := by
    refine ((hg.continuous_coordPartial j).pow 2).add ?_
    refine ((((hH.continuous_coordPartial j).pow 2).div_const 4).sub
      ((hHj.continuous_coordPartial j).div_const 2)).mul ?_
    exact (hf.continuous_torus.mul (groundState_isSmoothPeriodic_exp_neg_half hH).continuous_torus).pow 2
  have hW := isSmoothPeriodic_groundStateBoundary hH hf j
  have hD0 := SharpLSI.integral_fderiv_torus_eq_zero
    (W := groundStateBoundary H f j) (hW.of_le (by simp)) (Pi.single j 1)
  have hpt := groundState_torus_pointwise H f hH hf j
  have hDint : Integrable (fun y => fderiv ℝ (groundStateBoundary H f j ∘ torusLift)
      (SharpLSI.secT y) (Pi.single j 1)) (haar d) := by
    have := (groundState_integrable_torus_of_continuous c1).sub (groundState_integrable_torus_of_continuous c2)
    refine (this.const_mul 2).congr (Filter.Eventually.of_forall fun y => ?_)
    have h1 := hpt y
    simp only [Pi.sub_apply]
    unfold groundStateBoundary at h1 ⊢
    linarith
  refine ⟨groundState_integrable_torus_of_continuous c1,
    groundState_integrable_torus_of_continuous ((hg.continuous_coordPartial j).pow 2),
    groundState_integrable_torus_of_continuous c2, ?_⟩
  have : (fun y => (coordPartial j f y) ^ 2 * exp (-H y)) = fun y =>
      ((coordPartial j (fun z => f z * exp (-H z / 2)) y) ^ 2
        + ((coordPartial j H y) ^ 2 / 4 - coordPartial j (coordPartial j H) y / 2)
          * (f y * exp (-H y / 2)) ^ 2) + 1 / 2 * fderiv ℝ (groundStateBoundary H f j ∘ torusLift)
            (SharpLSI.secT y) (Pi.single j 1) := funext (groundState_torus_pointwise H f hH hf j)
  rw [this, integral_add (groundState_integrable_torus_of_continuous c2) (hDint.const_mul _),
    integral_const_mul, hD0]
  simp

/-- FIN016, torus form: with `g = f e^{-H/2}`,
`∫ |∇g|² = ∫ [|∇f|² + (ΔH/2 - |∇H|²/4) f²] e^{-H}` (Haar probability measure). -/
theorem ground_state_weighted_energy_identity_torus (H f : Torus d → ℝ)
    (hH : IsSmoothPeriodic H) (hf : IsSmoothPeriodic f) :
    ∫ y, ∑ j, (coordPartial j (fun z => f z * exp (-H z / 2)) y) ^ 2 ∂haar d =
      ∫ y, (∑ j, (coordPartial j f y) ^ 2
        + (∑ j, coordPartial j (coordPartial j H) y / 2 - ∑ j, (coordPartial j H y) ^ 2 / 4)
          * (f y) ^ 2) * exp (-H y) ∂haar d := by
  set A : Fin d → Torus d → ℝ := fun j y =>
    (coordPartial j (fun z => f z * exp (-H z / 2)) y) ^ 2 with hA
  set B : Fin d → Torus d → ℝ := fun j y =>
    ((coordPartial j H y) ^ 2 / 4 - coordPartial j (coordPartial j H) y / 2)
      * (f y * exp (-H y / 2)) ^ 2 with hB
  set L : Fin d → Torus d → ℝ := fun j y => (coordPartial j f y) ^ 2 * exp (-H y) with hL
  have key : ∀ j, Integrable (L j) (haar d) ∧ Integrable (A j) (haar d) ∧
      Integrable (B j) (haar d) ∧ ∫ y, L j y ∂haar d = ∫ y, A j y ∂haar d + ∫ y, B j y ∂haar d := by
    intro j
    obtain ⟨h1, h2, h3, h4⟩ := ground_state_weighted_energy_identity_torus_coord H f hH hf j
    have hBi : Integrable (B j) (haar d) := by
      have := h3.sub h2
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp [hB]
    refine ⟨h1, h2, hBi, ?_⟩
    rw [← integral_add h2 hBi]
    exact h4
  have hexp : ∀ y, (f y * exp (-H y / 2)) ^ 2 = f y ^ 2 * exp (-H y) := by
    intro y
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hT : ∀ y, (∑ j, (coordPartial j f y) ^ 2
        + (∑ j, coordPartial j (coordPartial j H) y / 2 - ∑ j, (coordPartial j H y) ^ 2 / 4)
          * (f y) ^ 2) * exp (-H y) = ∑ j, L j y - ∑ j, B j y := by
    intro y
    have hB' : ∑ j, B j y = (∑ j, (coordPartial j H y) ^ 2 / 4
        - ∑ j, coordPartial j (coordPartial j H) y / 2) * (f y ^ 2 * exp (-H y)) := by
      simp only [hB, hexp]
      rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    have hL' : ∑ j, L j y = (∑ j, (coordPartial j f y) ^ 2) * exp (-H y) := by
      simp only [hL, Finset.sum_mul]
    rw [hB', hL', ← Finset.sum_div, ← Finset.sum_div]
    ring
  simp_rw [hT]
  rw [integral_sub (integrable_finsetSum _ fun j _ => (key j).1)
    (integrable_finsetSum _ fun j _ => (key j).2.2.1),
    integral_finsetSum _ fun j _ => (key j).1, integral_finsetSum _ fun j _ => (key j).2.2.1,
    integral_finsetSum _ fun j _ => (key j).2.1]
  have : ∀ j ∈ Finset.univ, ∫ y, L j y ∂haar d = ∫ y, A j y ∂haar d + ∫ y, B j y ∂haar d :=
    fun j _ => (key j).2.2.2
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  ring

/-- FIN016 (`DGPS.FiniteN.ground_state_weighted_energy_identity`): the weighted energy identity
on `ℝ^k` (full gradient and fixed direction `v`) and on the torus. -/
theorem ground_state_weighted_energy_identity :
    (∀ (k : ℕ) (N : ℝ) (ψ F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ F →
      HasCompactSupport F →
      ∫ x, ‖fderiv ℝ F x‖ ^ 2 * exp (-(N * ψ x)) =
        ∫ x, (‖fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x‖ ^ 2
          + (N ^ 2 * ‖fderiv ℝ ψ x‖ ^ 2 / 4 - N * Laplacian.laplacian ψ x / 2)
            * (F x * exp (-(N * ψ x) / 2)) ^ 2)) ∧
    (∀ (k : ℕ) (N : ℝ) (ψ F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ ∞ ψ → ContDiff ℝ ∞ F →
      HasCompactSupport F → ∀ v : EuclideanSpace ℝ (Fin k),
      ∫ x, (fderiv ℝ F x v) ^ 2 * exp (-(N * ψ x)) =
        ∫ x, ((fderiv ℝ (fun y => F y * exp (-(N * ψ y) / 2)) x v) ^ 2
          + (N ^ 2 * (fderiv ℝ ψ x v) ^ 2 / 4
              - N * fderiv ℝ (fun y => fderiv ℝ ψ y v) x v / 2)
            * (F x * exp (-(N * ψ x) / 2)) ^ 2)) ∧
    (∀ (d : ℕ) (H f : Torus d → ℝ), IsSmoothPeriodic H → IsSmoothPeriodic f →
      ∫ y, ∑ j, (coordPartial j (fun z => f z * exp (-H z / 2)) y) ^ 2 ∂haar d =
        ∫ y, (∑ j, (coordPartial j f y) ^ 2
          + (∑ j, coordPartial j (coordPartial j H) y / 2 - ∑ j, (coordPartial j H y) ^ 2 / 4)
            * (f y) ^ 2) * exp (-H y) ∂haar d) :=
  ⟨fun _ N ψ F hψ hF hFc => ground_state_weighted_energy_identity_euclidean N ψ F hψ hF hFc,
   fun _ N ψ F hψ hF hFc v => ground_state_weighted_energy_identity_direction N ψ F hψ hF hFc v,
   fun _ H f hH hf => ground_state_weighted_energy_identity_torus H f hH hf⟩

end TorusPart

end DGPS.FiniteN
