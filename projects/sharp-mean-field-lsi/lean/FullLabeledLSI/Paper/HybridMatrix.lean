import FullLabeledLSI.Paper.HybridRLS
import FullLabeledLSI.Defs.F05_FiniteRank
import SharpSymmetricLSI.Paper.GaussPoincare3
import SharpSymmetricLSI.Paper.GaussLaw2

/-!
# Finite-rank matrix facts for the hybrid inequality (plan, section 1.2)

For `A : FiniteRankApprox W μ e`, a rank `R` and `J` with `∀ i ∈ A.s R, i < J` put
`Tm = (A.a R i j)_{i,j<J}` and `CJ = (C i j)_{i,j<J}` (the restriction of the infinite matrix `C`
with `IsInverseOfIPlus (A.a R) C`).
* `hCJ`: `(1 + Tm) * CJ = 1`; `CJ_mul`: `CJ * (1 + Tm) = 1`.
* `PosTm`: the positivity `σ/2 |v|² ≤ |v|² + vᵀ Tm v`; under it `CJ` is positive semidefinite.
* `rho_le_sq`, `rho_le_quad`: `ρ |s|² ≤ ∑ λ_{m+1} s_m²`, `ρ sᵀ CJ s ≤ ∑ λ_{m+1} s_m²`
  with `ρ = (bRate μ lam C).toReal`.
* `kappa_eq`: `κ_R = ∫ exp(-u_R(ext g)) dγ_J`; `uJ_eq`: `u_R(ext g) = ½ gᵀ Tm g`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

/-- `Tm = (A.a R i j)_{i,j<J}`. -/
def Tm (A : FiniteRankApprox W μ e) (R J : ℕ) : Matrix (Fin J) (Fin J) ℝ :=
  Matrix.of fun i j => A.a R i j

/-- `CJ = (C i j)_{i,j<J}`. -/
def CJ (C : ℕ → ℕ → ℝ) (J : ℕ) : Matrix (Fin J) (Fin J) ℝ :=
  Matrix.of fun i j => C i j

theorem Tm_apply (A : FiniteRankApprox W μ e) (R J : ℕ) (i j : Fin J) :
    Tm A R J i j = A.a R i j := rfl

theorem CJ_apply (C : ℕ → ℕ → ℝ) (J : ℕ) (i j : Fin J) : CJ C J i j = C i j := rfl

theorem Tm_transpose (A : FiniteRankApprox W μ e) (R J : ℕ) : (Tm A R J)ᵀ = Tm A R J := by
  ext i j
  simp [Tm, A.symm R i j]

theorem Tm_isSymm (A : FiniteRankApprox W μ e) (R J : ℕ) : (Tm A R J).IsSymm :=
  Tm_transpose A R J

section inverse
variable (A : FiniteRankApprox W μ e) {R J : ℕ} (hJ : ∀ i ∈ A.s R, i < J) {C : ℕ → ℕ → ℝ}
  (hC : IsInverseOfIPlus (A.a R) C)
include hJ hC

/-- `(1 + Tm) * CJ = 1`. -/
theorem hCJ : (1 + Tm A R J) * CJ C J = 1 := by
  ext i j
  have h := (hC j).2 i
  have h2 := h.2
  have hz : ∀ k ∉ Finset.range J,
      ((if (i : ℕ) = k then (1 : ℝ) else 0) + A.a R i k) * C k j = 0 := by
    intro k hk
    have hkJ : J ≤ k := by simpa using hk
    have hik : (i : ℕ) ≠ k := by have := i.2; omega
    have hks : k ∉ A.s R := fun hks => by have := hJ k hks; omega
    rw [A.supp R i k (Or.inr hks)]
    simp [hik]
  rw [tsum_eq_sum hz, Finset.sum_range] at h2
  rw [Matrix.mul_apply]
  simp only [Matrix.add_apply, Matrix.one_apply, CJ_apply, Tm_apply]
  convert h2 using 2 with k
  · simp [Fin.ext_iff]
  · simp [Fin.ext_iff]

/-- `CJ * (1 + Tm) = 1`. -/
theorem CJ_mul : CJ C J * (1 + Tm A R J) = 1 :=
  mul_eq_one_comm.mp (hCJ A hJ hC)

theorem CJ_transpose : (CJ C J)ᵀ = CJ C J := by
  have h1 := hCJ A hJ hC
  have h2 := CJ_mul A hJ hC
  have hT : (1 + Tm A R J)ᵀ = 1 + Tm A R J := by
    rw [Matrix.transpose_add, Matrix.transpose_one, Tm_transpose]
  have h3 : (CJ C J)ᵀ * (1 + Tm A R J) = 1 := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, hT, Matrix.transpose_one] at this
  calc (CJ C J)ᵀ = (CJ C J)ᵀ * ((1 + Tm A R J) * CJ C J) := by rw [h1, Matrix.mul_one]
    _ = ((CJ C J)ᵀ * (1 + Tm A R J)) * CJ C J := by rw [Matrix.mul_assoc]
    _ = CJ C J := by rw [h3, Matrix.one_mul]

theorem CJ_isHermitian : (CJ C J).IsHermitian := by
  have h := CJ_transpose A hJ hC
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact h

end inverse

/-- Positivity of `1 + Tm`: `σ/2 |v|² ≤ |v|² + vᵀ Tm v` for all `v : Fin J → ℝ`. -/
def PosTm (A : FiniteRankApprox W μ e) (R J : ℕ) (σ : ℝ) : Prop :=
  ∀ v : Fin J → ℝ, σ / 2 * (v ⬝ᵥ v) ≤ v ⬝ᵥ v + v ⬝ᵥ (Tm A R J *ᵥ v)

section pos
variable (A : FiniteRankApprox W μ e) {R J : ℕ} (hJ : ∀ i ∈ A.s R, i < J) {C : ℕ → ℕ → ℝ}
  (hC : IsInverseOfIPlus (A.a R) C) {σ : ℝ} (hσ : 0 < σ) (hpos : PosTm A R J σ)
include hJ hC hσ hpos

/-- `CJ` is positive semidefinite. -/
theorem CJ_quad_nonneg (v : Fin J → ℝ) : 0 ≤ v ⬝ᵥ (CJ C J *ᵥ v) := by
  set w := CJ C J *ᵥ v with hw
  have hv : (1 + Tm A R J) *ᵥ w = v := by
    rw [hw, Matrix.mulVec_mulVec, hCJ A hJ hC, Matrix.one_mulVec]
  have h1 : v ⬝ᵥ w = w ⬝ᵥ w + w ⬝ᵥ (Tm A R J *ᵥ w) := by
    calc v ⬝ᵥ w = ((1 + Tm A R J) *ᵥ w) ⬝ᵥ w := by rw [hv]
      _ = w ⬝ᵥ w + w ⬝ᵥ (Tm A R J *ᵥ w) := by
        rw [Matrix.add_mulVec, Matrix.one_mulVec, add_dotProduct, dotProduct_comm (Tm A R J *ᵥ w) w]
  have h2 := hpos w
  have h3 : 0 ≤ w ⬝ᵥ w := dotProduct_self_star_nonneg w
  nlinarith

theorem CJ_posSemidef : (CJ C J).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨CJ_isHermitian A hJ hC, fun x => ?_⟩
  simpa using CJ_quad_nonneg A hJ hC hσ hpos x

end pos


section rho
variable {lam : ℕ → ℝ} {C : ℕ → ℕ → ℝ}

/-- `bRate` is finite when `rLS ≤ λ₁`. -/
theorem bRate_ne_top (hrl : rLS μ ≤ ENNReal.ofReal (lam 1)) : bRate μ lam C ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((min_le_left _ _).trans hrl)

theorem bRate_toReal_nonneg : 0 ≤ (bRate μ lam C).toReal := ENNReal.toReal_nonneg

variable [IsProbabilityMeasure μ] (he : IsRefEigenbasis μ e lam)
  (hrl : rLS μ ≤ ENNReal.ofReal (lam 1))
include he

theorem lam_one_nonneg : 0 ≤ lam 1 := by
  rw [← integral_sqNorm_weakGrad_eigen he 1]
  exact integral_nonneg fun x => sqNorm_nonneg _

include hrl

omit hrl in
theorem lam_succ_nonneg (m : ℕ) : 0 ≤ lam (m + 1) :=
  (lam_one_nonneg he).trans (he.mono (by omega))

/-- `ρ = (bRate μ lam C).toReal ≤ λ₁`. -/
theorem rho_le_lam_one : (bRate μ lam C).toReal ≤ lam 1 := by
  have hb : bRate μ lam C ≤ rLS μ := min_le_left _ _
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb.trans hrl)
  rwa [ENNReal.toReal_ofReal (lam_one_nonneg he)] at h

/-- (i): `ρ |s|² ≤ ∑ λ_{m+1} s_m²`. -/
theorem rho_le_sq {J : ℕ} (s : Fin J → ℝ) :
    (bRate μ lam C).toReal * ∑ m, s m ^ 2 ≤ ∑ m : Fin J, lam (m + 1) * s m ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have h1 : (bRate μ lam C).toReal ≤ lam (m + 1) :=
    (rho_le_lam_one he hrl).trans (he.mono (by omega))
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _) |>.trans_eq (mul_comm _ _) |> fun h => by
    nlinarith [sq_nonneg (s m)]

omit hrl in
/-- (ii): `ρ sᵀ CJ s ≤ ∑ λ_{k+1} s_k²`. -/
theorem rho_le_quad {J : ℕ} (s : Fin J → ℝ) :
    (bRate μ lam C).toReal * ∑ k : Fin J, ∑ l : Fin J, C k l * s k * s l ≤
      ∑ k : Fin J, lam (k + 1) * s k ^ 2 := by
  set Q := ∑ k : Fin J, ∑ l : Fin J, C k l * s k * s l with hQ
  set L := ∑ k : Fin J, lam (k + 1) * s k ^ 2 with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun k _ =>
    mul_nonneg (lam_succ_nonneg he k) (sq_nonneg _)
  have hr0 := bRate_toReal_nonneg (μ := μ) (lam := lam) (C := C)
  rcases le_or_gt Q 0 with hQ0 | hQ0
  · nlinarith
  have h1 := quad_mul_lamG_le (lam' := lamShift lam) (C := C) s
  have h2 : ENNReal.ofReal Q * bRate μ lam C ≤ ENNReal.ofReal L := by
    refine le_trans ?_ h1
    exact mul_le_mul_right (min_le_right _ _) _
  have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hQ0.le, ENNReal.toReal_ofReal hL0] at h3
  linarith

end rho

/-! ### The quadratic form `u_R` on `Fin J → ℝ` and `κ_R` -/

/-- `u_R` of the zero extension of `g : Fin J → ℝ`. -/
def uJ (A : FiniteRankApprox W μ e) (R J : ℕ) (g : Fin J → ℝ) : ℝ := uR A R (extFin g)

theorem uJ_eq (A : FiniteRankApprox W μ e) {R J : ℕ} (hJ : ∀ i ∈ A.s R, i < J) (g : Fin J → ℝ) :
    uJ A R J g = (1 / 2) * (g ⬝ᵥ (Tm A R J *ᵥ g)) := by
  unfold uJ uR
  congr 1
  have hsub : A.s R ⊆ Finset.range J := fun i hi => Finset.mem_range.2 (hJ i hi)
  have h1 : ∀ i : ℕ, ∑ j ∈ A.s R, A.a R i j * extFin g i * extFin g j =
      ∑ j ∈ Finset.range J, A.a R i j * extFin g i * extFin g j := by
    intro i
    refine Finset.sum_subset hsub fun j _ hj => ?_
    rw [A.supp R i j (Or.inr hj)]; ring
  have h2 : ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * extFin g i * extFin g j =
      ∑ i ∈ Finset.range J, ∑ j ∈ Finset.range J, A.a R i j * extFin g i * extFin g j := by
    simp_rw [h1]
    refine Finset.sum_subset hsub fun i _ hi => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [A.supp R i j (Or.inl hi)]; ring
  rw [h2, Finset.sum_range]
  simp only [dotProduct, mulVec, Tm_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [extFin_coe, extFin_coe]; ring

theorem continuous_uJ (A : FiniteRankApprox W μ e) (R J : ℕ) : Continuous (uJ A R J) := by
  unfold uJ uR
  have hc : ∀ i : ℕ, Continuous fun g : Fin J → ℝ => extFin g i := by
    intro i
    by_cases h : i < J
    · simp only [extFin, h, dite_true]; exact continuous_apply _
    · simp only [extFin, h, dite_false]; exact continuous_const
  fun_prop

/-- `κ_R = ∫ exp(-u_R(ext g)) dγ_J`. -/
theorem kappa_eq (A : FiniteRankApprox W μ e) {R J : ℕ} (hJ : ∀ i ∈ A.s R, i < J) :
    kappaR A R = ∫ g, Real.exp (-uJ A R J g) ∂gpi J := by
  unfold kappaR
  have h := integral_map (μ := gammaRef) (φ := fun z (a : Fin J) => z a)
    (f := fun g : Fin J → ℝ => Real.exp (-uJ A R J g))
    (measurable_zBlock J).aemeasurable ((continuous_uJ A R J).neg.rexp.aestronglyMeasurable)
  rw [gammaRef_map_fin] at h
  refine Eq.trans ?_ h.symm
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have this : ∀ i ∈ A.s R, extFin (fun a : Fin J => z a) i = z i := by
    intro i hi
    simp [extFin, hJ i hi]
  have hu : uR A R z = uR A R (extFin (fun a : Fin J => z a)) := by
    unfold uR
    congr 1
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [this i hi, this j hj]
  show Real.exp (-uR A R z) = Real.exp (-uR A R (extFin (fun a : Fin J => z a)))
  rw [hu]

/-! ### Positivity of the eigenvalues and of `κ_R` -/

/-- Eigenvalue lower bound from a quadratic-form lower bound. -/
theorem secEig_ge {B : ℕ → ℕ → ℝ} (hB : ∀ i j, B i j = B j i) {n : ℕ} {c : ℝ}
    (h : ∀ y : EuclideanSpace ℝ (Fin n),
      c * inner ℝ y y ≤ inner ℝ y y + inner ℝ y (secOp B n y)) (k : Fin n) :
    c ≤ 1 + secEig hB n k := by
  have h1 := h (secVec hB n k)
  have h2 : inner ℝ (secVec hB n k) (secVec hB n k) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, (secVec hB n).orthonormal.1 k]; norm_num
  have h3 := inner_secVec_secOp hB k (secVec hB n k)
  rw [h2] at h1 h3
  simp only [mul_one] at h1 h3
  linarith

theorem inner_secOp_Tm (A : FiniteRankApprox W μ e) (R J : ℕ) (y : EuclideanSpace ℝ (Fin J)) :
    inner ℝ y (secOp (A.a R) J y) = (WithLp.ofLp y) ⬝ᵥ (Tm A R J *ᵥ WithLp.ofLp y) := by
  rw [inner_secOp_self]
  simp only [dotProduct, mulVec, Tm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem inner_self_euclid {J : ℕ} (y : EuclideanSpace ℝ (Fin J)) :
    inner ℝ y y = (WithLp.ofLp y) ⬝ᵥ (WithLp.ofLp y) := by
  rw [inner_euclid]; rfl

theorem one_add_secEig_ge (A : FiniteRankApprox W μ e) {R J : ℕ} {σ : ℝ}
    (hpos : PosTm A R J σ) (k : Fin J) : σ / 2 ≤ 1 + secEig (A.symm R) J k := by
  refine secEig_ge (A.symm R) (fun y => ?_) k
  rw [inner_secOp_Tm, inner_self_euclid]
  exact hpos _

theorem quadFin_eq_inner (B : ℕ → ℕ → ℝ) {J : ℕ} (y : EuclideanSpace ℝ (Fin J)) :
    quadFin B J y = inner ℝ y (secOp B J y) - ∑ i : Fin J, B i i := by
  rw [inner_secOp_self]
  unfold quadFin
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- `κ_R > 0` under the positivity of `1 + Tm`. -/
theorem kappa_pos (A : FiniteRankApprox W μ e) {R J : ℕ} (hJ : ∀ i ∈ A.s R, i < J) {σ : ℝ}
    (hσ : 0 < σ) (hpos : PosTm A R J σ) : 0 < kappaR A R := by
  rw [kappa_eq A hJ]
  have hE : ∀ k, 0 < 1 + (1 : ℝ) * secEig (A.symm R) J k := fun k => by
    have := one_add_secEig_ge A hpos k
    linarith
  have h1 := integral_exp_quadFin (A.symm R) (n := J) 1 0 hE
  have hmap := map_pi_eq_stdGaussian (ι := Fin J)
  have h2 : ∫ g, Real.exp (-uJ A R J g) ∂gpi J =
      Real.exp (-(∑ i : Fin J, A.a R i i) / 2) *
        ∫ y, Real.exp (inner ℝ (0 : EuclideanSpace ℝ (Fin J)) y - 1 * quadFin (A.a R) J y / 2)
          ∂stdGaussian (EuclideanSpace ℝ (Fin J)) := by
    rw [← hmap, integral_map (WithLp.measurable_toLp 2 _).aemeasurable]
    · rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only
      rw [← Real.exp_add, uJ_eq A hJ, quadFin_eq_inner, inner_secOp_Tm]
      congr 1
      simp only [inner_zero_left]
      ring
    · refine Continuous.aestronglyMeasurable ?_
      unfold quadFin
      fun_prop
  rw [h2, h1]
  exact mul_pos (Real.exp_pos _) (prod_exp_quadFin_pos (A.symm R) 1 0 hE)

end SharpLSI.FL
