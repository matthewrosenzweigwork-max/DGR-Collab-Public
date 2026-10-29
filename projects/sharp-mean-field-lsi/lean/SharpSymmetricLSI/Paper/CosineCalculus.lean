import SharpSymmetricLSI.Paper.FourierPoincare
import SharpSymmetricLSI.Defs.D12_Cosine

/-!
# Calculus for `U_N` of the cosine model: (3.30), (3.35), (3.36) (Phase 3, lane C)

On the lift `x : Fin N × Fin 1 → ℝ`, with `θⱼ = 2π x_{(j,0)}`, `C = ∑ cos θⱼ`, `S = ∑ sin θⱼ`:
`U_N = (κ/2N)(C² + S²)`, `∂_p U = 4πc (S cos θ_p - C sin θ_p)` (`c = κ/2N`) and
`∂_q ∂_p U = 8π²c (cos θ_q cos θ_p + sin θ_q sin θ_p - δ_{pq}(C cos θ_p + S sin θ_p))`.
-/

open MeasureTheory Set Filter Complex
open scoped Real

namespace SharpLSI

/-! ### Generic tools -/

theorem liftT_repTorus {ι : Type*} [Fintype ι] [DecidableEq ι] (y : UnitAddTorus ι) :
    liftT (repTorus y) = y := by
  funext i
  exact AddCircle.coe_equivIco

/-- The directional derivative as the derivative along a line. -/
theorem fderiv_apply_of_line {ι : Type*} [Fintype ι] {F : (ι → ℝ) → ℝ} {x e : ι → ℝ}
    (hF : DifferentiableAt ℝ F x) {d : ℝ} (h : HasDerivAt (fun t : ℝ => F (x + t • e)) d 0) :
    fderiv ℝ F x e = d := by
  have h2 : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  exact (hF.hasFDerivAt.comp_hasDerivAt_of_eq 0 h2 (by simp)).unique h

/-! ### The lift of `U_N` -/

variable {N : ℕ}

/-- `θⱼ = 2π x_{(j,0)}`. -/
noncomputable def thetaC (x : Fin N × Fin 1 → ℝ) (j : Fin N) : ℝ := 2 * π * x (j, 0)

/-- `C = ∑ⱼ cos θⱼ`. -/
noncomputable def sumCos (x : Fin N × Fin 1 → ℝ) : ℝ := ∑ j, Real.cos (thetaC x j)

/-- `S = ∑ⱼ sin θⱼ`. -/
noncomputable def sumSin (x : Fin N × Fin 1 → ℝ) : ℝ := ∑ j, Real.sin (thetaC x j)

theorem expT_unflat_liftT (x : Fin N × Fin 1 → ℝ) (j : Fin N) :
    expT (unflat (liftT x) j) = cexp ((thetaC x j : ℂ) * I) := by
  simp only [expT, unflat, liftT, fourier_coe_apply, thetaC]
  push_cast
  ring_nf

theorem cosU_lift (κ : ℝ) (x : Fin N × Fin 1 → ℝ) :
    cosU κ N (unflat (liftT x)) = κ / (2 * N) * (sumCos x ^ 2 + sumSin x ^ 2) := by
  simp only [cosU, expT_unflat_liftT, Complex.normSq_apply, Complex.re_sum, Complex.im_sum,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sumCos, sumSin]
  ring

theorem cosU_comp_lift (κ : ℝ) :
    (cosU κ N ∘ unflat) ∘ liftT = fun x => κ / (2 * N) * (sumCos x ^ 2 + sumSin x ^ 2) := by
  funext x; exact cosU_lift κ x

theorem contDiff_cos_coord (j : Fin N) :
    ContDiff ℝ ⊤ (fun x : Fin N × Fin 1 → ℝ => Real.cos (thetaC x j)) :=
  Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ (j, 0)))

theorem contDiff_sin_coord (j : Fin N) :
    ContDiff ℝ ⊤ (fun x : Fin N × Fin 1 → ℝ => Real.sin (thetaC x j)) :=
  Real.contDiff_sin.comp (contDiff_const.mul (contDiff_apply ℝ ℝ (j, 0)))

theorem contDiff_sumCos : ContDiff ℝ ⊤ (sumCos (N := N)) :=
  ContDiff.sum fun j _ => contDiff_cos_coord j

theorem contDiff_sumSin : ContDiff ℝ ⊤ (sumSin (N := N)) :=
  ContDiff.sum fun j _ => contDiff_sin_coord j

/-- The coordinate line `t ↦ x + t e_p`. -/
theorem thetaC_line (x : Fin N × Fin 1 → ℝ) (p j : Fin N) (t : ℝ) :
    thetaC (x + t • Pi.single (p, 0) 1) j = thetaC x j + 2 * π * t * (if j = p then 1 else 0) := by
  simp only [thetaC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Prod.mk.injEq,
    and_true]
  split_ifs <;> ring

theorem hasDerivAt_cos_line (x : Fin N × Fin 1 → ℝ) (p j : Fin N) :
    HasDerivAt (fun t : ℝ => Real.cos (thetaC (x + t • Pi.single (p, 0) 1) j))
      (-Real.sin (thetaC x j) * (2 * π * (if j = p then 1 else 0))) 0 := by
  simp_rw [thetaC_line]
  have := (((hasDerivAt_id (0 : ℝ)).const_mul (2 * π)).mul_const
    (if j = p then (1 : ℝ) else 0)).const_add (thetaC x j)
  simpa using this.cos

theorem hasDerivAt_sin_line (x : Fin N × Fin 1 → ℝ) (p j : Fin N) :
    HasDerivAt (fun t : ℝ => Real.sin (thetaC (x + t • Pi.single (p, 0) 1) j))
      (Real.cos (thetaC x j) * (2 * π * (if j = p then 1 else 0))) 0 := by
  simp_rw [thetaC_line]
  have := (((hasDerivAt_id (0 : ℝ)).const_mul (2 * π)).mul_const
    (if j = p then (1 : ℝ) else 0)).const_add (thetaC x j)
  simpa using this.sin

theorem hasDerivAt_sumCos_line (x : Fin N × Fin 1 → ℝ) (p : Fin N) :
    HasDerivAt (fun t : ℝ => sumCos (x + t • Pi.single (p, 0) 1))
      (-2 * π * Real.sin (thetaC x p)) 0 := by
  have := HasDerivAt.sum (u := Finset.univ) fun j _ => hasDerivAt_cos_line x p j
  convert this using 1
  · funext t; simp [sumCos]
  · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring

theorem hasDerivAt_sumSin_line (x : Fin N × Fin 1 → ℝ) (p : Fin N) :
    HasDerivAt (fun t : ℝ => sumSin (x + t • Pi.single (p, 0) 1))
      (2 * π * Real.cos (thetaC x p)) 0 := by
  have := HasDerivAt.sum (u := Finset.univ) fun j _ => hasDerivAt_sin_line x p j
  convert this using 1
  · funext t; simp [sumSin]
  · simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring

/-! ### First and second derivatives -/

/-- `U_N` on the lift. -/
noncomputable def UL (κ : ℝ) (N : ℕ) (x : Fin N × Fin 1 → ℝ) : ℝ :=
  κ / (2 * N) * (sumCos x ^ 2 + sumSin x ^ 2)

/-- `∂_p U_N` on the lift. -/
noncomputable def dUL (κ : ℝ) (p : Fin N) (x : Fin N × Fin 1 → ℝ) : ℝ :=
  κ / (2 * N) * (4 * π) * (sumSin x * Real.cos (thetaC x p) - sumCos x * Real.sin (thetaC x p))

theorem contDiff_UL (κ : ℝ) : ContDiff ℝ ⊤ (UL κ N) :=
  contDiff_const.mul ((contDiff_sumCos.pow 2).add (contDiff_sumSin.pow 2))

theorem contDiff_dUL (κ : ℝ) (p : Fin N) : ContDiff ℝ ⊤ (dUL κ p) :=
  contDiff_const.mul ((contDiff_sumSin.mul (contDiff_cos_coord p)).sub
    (contDiff_sumCos.mul (contDiff_sin_coord p)))

theorem fderiv_UL (κ : ℝ) (p : Fin N) (x : Fin N × Fin 1 → ℝ) :
    fderiv ℝ (UL κ N) x (Pi.single (p, 0) 1) = dUL κ p x := by
  refine fderiv_apply_of_line ((contDiff_UL κ).differentiable (by simp) x) ?_
  have := (((hasDerivAt_sumCos_line x p).pow 2).add
    ((hasDerivAt_sumSin_line x p).pow 2)).const_mul (κ / (2 * N))
  convert this using 1
  · funext t; simp [UL]
  · simp only [dUL, zero_smul, add_zero]
    push_cast
    ring

theorem fderiv_dUL (κ : ℝ) (p q : Fin N) (x : Fin N × Fin 1 → ℝ) :
    fderiv ℝ (dUL κ p) x (Pi.single (q, 0) 1) =
      κ / (2 * N) * (8 * π ^ 2) *
        (Real.cos (thetaC x q) * Real.cos (thetaC x p) +
          Real.sin (thetaC x q) * Real.sin (thetaC x p) -
          (if p = q then 1 else 0) *
            (sumCos x * Real.cos (thetaC x p) + sumSin x * Real.sin (thetaC x p))) := by
  refine fderiv_apply_of_line ((contDiff_dUL κ p).differentiable (by simp) x) ?_
  have := (((hasDerivAt_sumSin_line x q).mul (hasDerivAt_cos_line x q p)).sub
    ((hasDerivAt_sumCos_line x q).mul (hasDerivAt_sin_line x q p))).const_mul
      (κ / (2 * N) * (4 * π))
  convert this using 1
  · funext t; simp [dUL]
  · simp only [zero_smul, add_zero]
    split_ifs <;> ring

/-! ### Values at a configuration -/

theorem flat_eq_liftT (X : Config N 1) : X = unflat (liftT (repTorus (flat X))) := by
  rw [liftT_repTorus]; rfl

theorem gCos_sub_lift (x : Fin N × Fin 1 → ℝ) (j k : Fin N) :
    gCos (unflat (liftT x) j - unflat (liftT x) k) =
      Real.cos (thetaC x j) * Real.cos (thetaC x k) +
        Real.sin (thetaC x j) * Real.sin (thetaC x k) := by
  have h : (unflat (liftT x) j - unflat (liftT x) k) 0 =
      ((x (j, 0) - x (k, 0) : ℝ) : UnitAddCircle) := by
    simp [unflat, liftT]
  rw [← Real.cos_sub]
  simp only [gCos, expT, h, fourier_coe_apply, thetaC]
  rw [show (2 * (π : ℂ) * I * ((1 : ℤ) : ℂ) * ((x (j, 0) - x (k, 0) : ℝ) : ℂ) / ((1 : ℝ) : ℂ)) =
      ((2 * π * x (j, 0) - 2 * π * x (k, 0) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

theorem re_mul_conj_sub (a : ℝ) (b : Fin N → ℝ) :
    (cexp ((a : ℂ) * I) * (starRingEnd ℂ) ((∑ l, cexp ((b l : ℂ) * I)) - cexp ((a : ℂ) * I))).re =
      Real.cos a * ∑ l, Real.cos (b l) + Real.sin a * ∑ l, Real.sin (b l) - 1 := by
  simp only [map_sub, map_sum, mul_sub, Finset.mul_sum, Complex.sub_re, Complex.re_sum,
    Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rw [← Finset.sum_add_distrib]
  have := Real.sin_sq_add_cos_sq a
  simp only [mul_neg, sub_neg_eq_add]
  linear_combination (-1 : ℝ) * this

theorem cpartial2C_cosU (κ : ℝ) (j k : Fin N) (X : Config N 1) :
    cpartial2C (cosU κ N) j 0 k 0 X =
      κ / (2 * N) * (8 * π ^ 2) *
        (Real.cos (thetaC (repTorus (flat X)) k) * Real.cos (thetaC (repTorus (flat X)) j) +
          Real.sin (thetaC (repTorus (flat X)) k) * Real.sin (thetaC (repTorus (flat X)) j) -
          (if j = k then 1 else 0) *
            (sumCos (repTorus (flat X)) * Real.cos (thetaC (repTorus (flat X)) j) +
              sumSin (repTorus (flat X)) * Real.sin (thetaC (repTorus (flat X)) j))) := by
  have h1 : (fun x => fderiv ℝ ((cosU κ N ∘ unflat) ∘ liftT) x (Pi.single (j, 0) 1)) =
      dUL κ j := by
    funext x
    rw [cosU_comp_lift]
    exact fderiv_UL κ j x
  simp only [cpartial2C, cpartial2]
  rw [h1, fderiv_dUL]

theorem expT_X (X : Config N 1) (j : Fin N) :
    expT (X j) = cexp ((thetaC (repTorus (flat X)) j : ℂ) * I) := by
  conv_lhs => rw [flat_eq_liftT X]
  exact expT_unflat_liftT _ j

theorem gCos_X (X : Config N 1) (j k : Fin N) :
    gCos (X j - X k) =
      Real.cos (thetaC (repTorus (flat X)) j) * Real.cos (thetaC (repTorus (flat X)) k) +
        Real.sin (thetaC (repTorus (flat X)) j) * Real.sin (thetaC (repTorus (flat X)) k) := by
  conv_lhs => rw [flat_eq_liftT X]
  exact gCos_sub_lift _ j k

theorem cosU_X (κ : ℝ) (X : Config N 1) :
    cosU κ N X = κ / (2 * N) * (sumCos (repTorus (flat X)) ^ 2 + sumSin (repTorus (flat X)) ^ 2) := by
  conv_lhs => rw [flat_eq_liftT X]
  exact cosU_lift κ _

/-- (3.35). -/
theorem cosine_hessian_aux (κ : ℝ) (X : Config N 1) :
    (∀ j k : Fin N, j ≠ k →
      cpartial2C (cosU κ N) j 0 k 0 X = aCos * κ / N * gCos (X j - X k)) ∧
    ∀ j : Fin N, cpartial2C (cosU κ N) j 0 j 0 X =
      -(aCos * κ / N) * (expT (X j) * (starRingEnd ℂ) ((∑ l, expT (X l)) - expT (X j))).re := by
  refine ⟨fun j k hjk => ?_, fun j => ?_⟩
  · rw [cpartial2C_cosU, if_neg hjk, gCos_X]
    unfold aCos
    ring
  · rw [cpartial2C_cosU, if_pos rfl]
    simp_rw [expT_X]
    rw [re_mul_conj_sub]
    have := Real.sin_sq_add_cos_sq (thetaC (repTorus (flat X)) j)
    simp only [sumCos, sumSin]
    unfold aCos
    linear_combination (κ / (2 * N) * (8 * π ^ 2)) * this

/-- (3.30). -/
theorem cosine_U_laplacian_aux (κ : ℝ) (hN : 1 ≤ N) (X : Config N 1) :
    laplacianC (cosU κ N) X = aCos * κ - 2 * aCos * cosU κ N X := by
  simp only [laplacianC, Fin.sum_univ_one]
  simp_rw [cpartial2C_cosU]
  simp only [↓reduceIte, one_mul]
  rw [cosU_X]
  set x := repTorus (flat X)
  have hsum : ∑ j : Fin N, (Real.cos (thetaC x j) * Real.cos (thetaC x j) +
      Real.sin (thetaC x j) * Real.sin (thetaC x j) -
      (sumCos x * Real.cos (thetaC x j) + sumSin x * Real.sin (thetaC x j))) =
      N - (sumCos x ^ 2 + sumSin x ^ 2) := by
    have h1 : ∀ j : Fin N, Real.cos (thetaC x j) * Real.cos (thetaC x j) +
        Real.sin (thetaC x j) * Real.sin (thetaC x j) = 1 := fun j => by
      rw [← sq, ← sq, add_comm]; exact Real.sin_sq_add_cos_sq _
    simp only [Finset.sum_sub_distrib, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [sumCos, sumSin]
    ring
  rw [← Finset.mul_sum, hsum]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  unfold aCos
  field_simp
  ring

/-- (3.36). -/
theorem cosine_offdiagonal_aux (κ : ℝ) (hκ : 0 < κ) (X : Config N 1) (v : Fin N → ℝ) :
    -(aCos * κ / N) * ∑ j, v j ^ 2 ≤
      ∑ j, ∑ k, (if j ≠ k then cpartial2C (cosU κ N) j 0 k 0 X * v j * v k else 0) := by
  set x := repTorus (flat X) with hx
  set c := aCos * κ / N with hc
  set O : Fin N → Fin N → ℝ := fun j k =>
    c * (Real.cos (thetaC x k) * Real.cos (thetaC x j) +
      Real.sin (thetaC x k) * Real.sin (thetaC x j)) with hO
  have hrw : ∀ j k, (if j ≠ k then cpartial2C (cosU κ N) j 0 k 0 X * v j * v k else 0) =
      O j k * v j * v k - (if j = k then O j k * v j * v k else 0) := by
    intro j k
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [if_pos hjk, if_neg hjk, cpartial2C_cosU, if_neg hjk, hO, hc]
      unfold aCos
      ring
  simp_rw [hrw, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h1 : ∑ j, ∑ k, O j k * v j * v k =
      c * ((∑ j, v j * Real.cos (thetaC x j)) ^ 2 + (∑ j, v j * Real.sin (thetaC x j)) ^ 2) := by
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hO]
    ring
  have h2 : ∑ j, O j j * v j * v j = c * ∑ j, v j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := Real.sin_sq_add_cos_sq (thetaC x j)
    simp only [hO]
    linear_combination (c * v j ^ 2) * this
  rw [h1, h2]
  have hc0 : 0 ≤ c := by rw [hc]; unfold aCos; positivity
  have : 0 ≤ c * ((∑ j, v j * Real.cos (thetaC x j)) ^ 2 +
      (∑ j, v j * Real.sin (thetaC x j)) ^ 2) := by positivity
  linarith

end SharpLSI
