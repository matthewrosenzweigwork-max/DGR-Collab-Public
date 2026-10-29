import FullLabeledLSI.Paper.Prop23ReplaceA

/-!
# Proposition 2.3, WP-E: the Schrödinger identity and the limit of `V_{N,R}` (SKELETON)

Manuscript (eq:schrodinger), (eq:VNR), (eq:v-limit) (lines 1012-1041).  `N`-indexed, `N ≥ 1`,
reference measure `QN μ N = μ^{⊗N}`, `Z_N = fluct`, `U_{N,R} = URN A R N`.

## Contents

* Definitions `ANmat` (`A_{N,ij}`) and `VNR` (`V_{N,R}`, formula (VNR)); `TR`, `gradURN` are in
  `Prop23ReplaceSkel.lean`.
* **E1** (Schrödinger identity) `schrodinger_identity`, split into
  `shEn_expand` (expansion of the square, any `U` with bounded weak gradient),
  `sum_gradURN_sq` (`|∇U_{N,R}|² = (T Z)ᵀ A_N (T Z)`, pure algebra),
  `sum_integral_cgrad_eC` (one-particle Dirichlet matrix `∫ ∇e_a·∇e_b dμ = λ_a δ_ab` for the `C¹`
  representatives), `eigen_slice_sq_mul` (the eigen-slice identity for `Φ = Ψ² (T Z)_i`),
  `cross_term_URN` (`∫ Ψ ∇Ψ·∇U_{N,R} = ½ ∫ Ψ² (Zᵀ Λ T Z - tr(T A_N))`).
* **E2** (eq:v-limit) `VNR_tendsto_vR`, split into `VNR_sub_vR_eq` (pure algebra),
  `ANmat_moment` (law of large numbers, via lane 3's `sum_moment_bound`),
  `fluct_moment_eC` (via `fluct_moment_bound`), and the ready-to-use consumer
  `integral_VNR_sub_vR_small`.

## Conventions / design decisions (read before proving)

* **Which representatives.** `VNR`, `ANmat`, `gradURN` are defined with the `C¹` representatives
  `eC` (classical gradient `cgrad`, bounded, measurable) of the eigenfunctions `e`
  (`exists_c1_reps`, ForceApprox4:26: `ContDiff ℝ 1 (eC j ∘ liftT)`, `eC j =ᵐ[haar d] e j`);
  `URN`, `vR`, `fluct e` are built from `e` (as in F05/F06, the statement of S23, `Jexpr`).
  Since `μ ≪ Haar` (`minimizer_ac`) all these agree `Q_N`-a.e.; the only places where this matters
  are `schrodinger_identity` (via `weakGradC_URN_ae`) and `VNR_tendsto_vR` (`fluct eC =ᵐ fluct e`).
* **No approximation argument is needed.**  The manuscript says "the identity holds for every
  `H¹(Q_N)` function by approximation".  Our route applies `eigen_slice` (FormLiminf4:21, which
  holds for `Φ ∈ W^{1,1}`) directly to `Φ = Ψ² (T Z)_i`, so the identity is proved for every
  `Ψ ∈ H¹(Q_N)` without density arguments.
* **Transfer between `Q_N` and Haar.**  `eigen_slice`, `isWeakGrad_sq`, `IsWeakGrad.mul_lip` are
  stated w.r.t. `volume`.  For `Ψ ∈ H¹(Q_N)` get `Ψ ∈ L²(volume)`, `∂Ψ ∈ L²(volume)` from
  `minimizer_pi_comparison` (NBody3:52: `volume ≤ a • (Q_N).map flat`), `memLp_vol`, `memLp_grad_vol`
  (as in `eigen_tensor_H1`, NBody3:~105-130, which is the model proof: copy its set-up).
* The identity is stated with `toReal`; `shEn ≠ ⊤` is part of the conclusion.
* `lam` is the manuscript-indexed eigenvalue sequence (`lam 0 = 0`), so `λ_{i+1} = lam (i+1)` is the
  eigenvalue of `e (i+1)`, exactly as in `vR`.

## Doubts

* (VNR) of the plan is correct (verified by hand: `∇_l Z_i = N^{-1/2} ∇e_{i+1}(X_l)`,
  `|∇U|² = (TZ)ᵀ A (TZ)`, `L⁰(Z_iZ_j) = -(λ_i+λ_j) Z_i Z_j + 2 A_{ij}`, whence
  `-½ L⁰U = ½ ZᵀΛTZ - ½ tr(T A)`), but note: our proof never forms `L⁰ U_{N,R}`.
* The statement `schrodinger_identity` holds for *every* `Ψ` with `MemH1C (QN μ N) Ψ`; no
  boundedness of `Ψ` is needed because `∇U_{N,R}` and `V_{N,R}` are bounded for fixed `N`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

section Defs

variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

/-- `A_{N,ij}(X) = N⁻¹ ∑_l ∇e_{i+1}(X_l)·∇e_{j+1}(X_l)` (classical gradients of the `C¹`
representatives `eC`; Lean index `i` = manuscript mode `i+1`). -/
noncomputable def ANmat (eC : ℕ → Torus d → ℝ) (N : ℕ) (X : Config N d) (i j : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ l : Fin N, ∑ k : Fin d, cgrad (eC (i + 1)) (X l) k * cgrad (eC (j + 1)) (X l) k

/-- `V_{N,R} = ¼ (T_R Z_N)ᵀ A_N (T_R Z_N) - ½ tr(T_R A_N) + ½ Z_Nᵀ Λ_R T_R Z_N` (eq:VNR), with
`Z_N = fluct eC N`, `Λ_R = diag(lam (i+1))`, `tr(T_R A_N) = ∑_{ij} (T_R)_{ij} A_{N,ji}`
(`A_N` is symmetric). -/
noncomputable def VNR (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (eC : ℕ → Torus d → ℝ)
    (R N : ℕ) (X : Config N d) : ℝ :=
  (1 / 4) * ∑ i ∈ A.s R, ∑ j ∈ A.s R,
      TR A R (fun n => fluct eC N n X) i * ANmat eC N X i j * TR A R (fun n => fluct eC N n X) j
    - (1 / 2) * ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j
    + (1 / 2) * ∑ i ∈ A.s R, lam (i + 1) * fluct eC N i X * TR A R (fun n => fluct eC N n X) i

/-- **`|∇U_{N,R}|² = (T_R Z_N)ᵀ A_N (T_R Z_N)`** (pointwise algebra, true for all `N`, `R`, `X`).

Proof (PROVED below): unfold `gradURN`; square the product `N^{-1/2} * ∑_i …`
(`(N:ℝ)^(-1/2) ^ 2 = N⁻¹` for `N ≥ 1`, and both sides are `0` for `N = 0` since `Fin 0` is empty);
`Finset.sum_mul_sum`, `Finset.sum_comm` to exchange `∑_l ∑_k` with `∑_i ∑_j`. -/
theorem sum_gradURN_sq (A : FiniteRankApprox W μ e) (eC : ℕ → Torus d → ℝ) (R N : ℕ)
    (X : Config N d) :
    ∑ l : Fin N, ∑ k : Fin d, gradURN A eC R N X l k ^ 2 =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R,
        TR A R (fun n => fluct eC N n X) i * ANmat eC N X i j *
          TR A R (fun n => fluct eC N n X) j := by
  have hN := prop23_rpow_half_mul_self N
  have h1 : ∀ (l : Fin N) (k : Fin d), gradURN A eC R N X l k ^ 2 =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, (N : ℝ)⁻¹ * (TR A R (fun n => fluct eC N n X) i *
        TR A R (fun n => fluct eC N n X) j * (cgrad (eC (i + 1)) (X l) k * cgrad (eC (j + 1)) (X l) k)) := by
    intro l k
    unfold gradURN
    rw [mul_pow, sq ((N : ℝ) ^ (-(1 / 2 : ℝ))), hN, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [h1]
  rw [prop23_sum4_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold ANmat
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

/-- **`V_{N,R} - v_R(Z_N) = ¼ ∑ (TZ)_i D_ij (TZ)_j - ½ ∑ a_ij D_ij`**, `D_ij = A_{N,ij} - λ_{i+1}δ_ij`
(pointwise algebra; `vR` evaluated at the *same* vector `Z = fluct eC N X`).

Proof (PROVED below): unfold `VNR, vR, TR`; `Finset.sum_ite_eq` for the `δ_ij` terms
(`∑_i ∑_j T_i (if i = j then λ_i else 0) T_j = ∑_i λ_i T_i²`, `∑_i ∑_j a_ij (if i = j …) = ∑_i a_ii λ_i`,
using `i ∈ s_R` membership, `Finset.sum_ite_eq'`), `Finset.sum_sub_distrib`, `ring`. -/
theorem VNR_sub_vR_eq (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (eC : ℕ → Torus d → ℝ)
    (R N : ℕ) (X : Config N d) :
    VNR A lam eC R N X - vR A lam R (fun n => fluct eC N n X) =
      (1 / 4) * ∑ i ∈ A.s R, ∑ j ∈ A.s R, TR A R (fun n => fluct eC N n X) i *
          (ANmat eC N X i j - if i = j then lam (i + 1) else 0) *
            TR A R (fun n => fluct eC N n X) j
        - (1 / 2) * ∑ i ∈ A.s R, ∑ j ∈ A.s R,
          A.a R i j * (ANmat eC N X i j - if i = j then lam (i + 1) else 0) := by
  set T := TR A R (fun n => fluct eC N n X) with hT
  set z : ℕ → ℝ := fun n => fluct eC N n X with hz
  have hA : ∑ i ∈ A.s R, ∑ j ∈ A.s R, T i * (if i = j then lam (i + 1) else 0) * T j =
      ∑ m ∈ A.s R, lam (m + 1) * T m ^ 2 := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single_of_mem i hi (fun j _ hj => by simp [Ne.symm hj])]
    simp; ring
  have hB : ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * (if i = j then lam (i + 1) else 0) =
      ∑ m ∈ A.s R, A.a R m m * lam (m + 1) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single_of_mem i hi (fun j _ hj => by simp [Ne.symm hj])]
    simp
  have hC : ∑ i ∈ A.s R, lam (i + 1) * z i * T i =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, z i * lam (i + 1) * A.a R i j * z j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hT, TR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e1 : ∑ i ∈ A.s R, ∑ j ∈ A.s R, T i * (ANmat eC N X i j - if i = j then lam (i + 1) else 0) * T j =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, T i * ANmat eC N X i j * T j - ∑ m ∈ A.s R, lam (m + 1) * T m ^ 2 := by
    rw [← hA, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * (ANmat eC N X i j - if i = j then lam (i + 1) else 0) =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * ANmat eC N X i j - ∑ m ∈ A.s R, A.a R m m * lam (m + 1) := by
    rw [← hB, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1, e2]
  unfold VNR vR
  rw [← hz, ← hT]
  rw [hC]
  have hT' : ∀ m, ∑ j ∈ A.s R, A.a R m j * z j = T m := fun m => rfl
  simp only [hT']
  ring

end Defs

/-! ### E1: the Schrödinger identity -/

section Expand

variable {μ : Measure (Torus d)}

/-- **Expansion of the square** (E1, step 1).  For `Ψ ∈ H¹(Q_N)` and `U` with a weak gradient
bounded `Q_N`-a.e. by `L`:
`∫|∇Ψ + ½Ψ∇U|² = ∫|∇Ψ|² + ∫ Ψ ∇Ψ·∇U + ¼ ∫ Ψ² |∇U|²`, all three terms finite (so `shEn ≠ ⊤`).

Only `μ ≪ Haar` is needed (for a.e.-measurability of the chosen weak gradients on `Q_N`:
`aestronglyMeasurable_comp_flat` GroundT6:46 / `pi_ac_volume` ForceExp:22 — their proofs use only
`hac`).

Proof (about 60-80 lines): `MemLp Ψ 2 Q` (`memLp_of_memH1C_pi`, GroundT11:14), `MemLp (weakGradC Ψ · i k) 2 Q`
(from `hΨ.2.2` and `abs_le_sqrt_sqNorm`, cf. `memLp_weakGradC` NBody4:86 which needs `hyp hμ` but
whose proof only uses a.e.-measurability); pointwise a.e. `(a + ½Ψb)² = a² + Ψ a b + ¼Ψ² b²`
summed over `(i,k)`; `integral_add`, `ofReal_integral_eq_lintegral_ofReal`; integrability of
`Ψ·a·b` from `|b| ≤ L`, `Ψ ∈ L²`, `a ∈ L²` (`MemLp.integrable_mul`), of `Ψ² b²` from `Ψ² ∈ L¹`. -/
theorem shEn_expand [IsProbabilityMeasure μ] (hac : μ ≪ haar d) {N : ℕ} {Ψ U : Config N d → ℝ}
    (hΨ : MemH1C (QN μ N) Ψ) (hU : HasWeakGrad (U ∘ unflat)) {L : ℝ}
    (hL : ∀ᵐ X ∂QN μ N, ∀ (i : Fin N) (k : Fin d), |weakGradC U X i k| ≤ L) :
    shEn μ Ψ U ≠ ⊤ ∧
      (shEn μ Ψ U).toReal =
        (refEnergy μ Ψ).toReal +
          ∫ X, Ψ X * ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC U X i k ∂QN μ N +
          (1 / 4) * ∫ X, Ψ X ^ 2 * gradSqC U X ∂QN μ N := by
  classical
  set P := QN μ N with hP
  have hsm : ∀ (f : Config N d → ℝ), HasWeakGrad (f ∘ unflat) → ∀ (i : Fin N) (k : Fin d),
      AEStronglyMeasurable (fun X => weakGradC f X i k) P := by
    intro f hf i k
    have hG := (isWeakGrad_weakGrad hf).aestronglyMeasurable_grad (i, k)
    have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
      ⟨measurable_flat, map_flat_volume N⟩
    exact (hG.comp_measurePreserving hmp).mono_ac (pi_ac_volume hac N)
  have hΨ2 : MemLp Ψ 2 P := measurableEmbedding_flat.memLp_map_measure_iff.mp hΨ.2.1
  have hgrad2 : MemLp (fun X => Real.sqrt (sqNorm (weakGrad (Ψ ∘ unflat) (flat X)))) 2 P :=
    measurableEmbedding_flat.memLp_map_measure_iff.mp hΨ.2.2
  have ha : ∀ (i : Fin N) (k : Fin d), MemLp (fun X => weakGradC Ψ X i k) 2 P := by
    intro i k
    refine hgrad2.mono (hsm Ψ hΨ.1 i k) (ae_of_all _ fun X => ?_)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_eq_abs]
    exact abs_le_sqrt_sqNorm (weakGrad (Ψ ∘ unflat) (flat X)) (i, k)
  have hΨsq : Integrable (fun X => Ψ X ^ 2) P := hΨ2.integrable_sq
  have hF1 : Integrable (fun X => gradSqC Ψ X) P := by
    unfold gradSqC
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => (ha i k).integrable_sq
  have hF2 : Integrable (fun X => Ψ X * ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC U X i k) P := by
    simp_rw [Finset.mul_sum]
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => ?_
    have h1 : Integrable (fun X => Ψ X * weakGradC Ψ X i k) P := hΨ2.integrable_mul (ha i k)
    refine Integrable.mono' (h1.norm.mul_const |L|) ?_ ?_
    · exact hΨ2.aestronglyMeasurable.mul ((ha i k).aestronglyMeasurable.mul (hsm U hU i k))
    · filter_upwards [hL] with X hX
      have hb := (hX i k).trans (le_abs_self L)
      calc ‖Ψ X * (weakGradC Ψ X i k * weakGradC U X i k)‖
          = ‖Ψ X * weakGradC Ψ X i k‖ * |weakGradC U X i k| := by
            rw [← mul_assoc, norm_mul, Real.norm_eq_abs (weakGradC U X i k)]
        _ ≤ ‖Ψ X * weakGradC Ψ X i k‖ * |L| := by gcongr
  have hF3 : Integrable (fun X => Ψ X ^ 2 * gradSqC U X) P := by
    have : (fun X => Ψ X ^ 2 * gradSqC U X) =
        fun X => ∑ i, ∑ k, Ψ X ^ 2 * (weakGradC U X i k) ^ 2 := by
      funext X; simp [gradSqC, Finset.mul_sum]
    rw [this]
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => ?_
    refine Integrable.mono' (hΨsq.mul_const (L ^ 2)) ?_ ?_
    · exact hΨ2.aestronglyMeasurable.pow 2 |>.mul ((hsm U hU i k).pow 2)
    · filter_upwards [hL] with X hX
      have hb : (weakGradC U X i k) ^ 2 ≤ L ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hX i k) 2
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
  have hpt : ∀ X : Config N d,
      ∑ i, ∑ k, (weakGradC Ψ X i k + (1 / 2) * Ψ X * weakGradC U X i k) ^ 2 =
        gradSqC Ψ X + Ψ X * ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC U X i k +
          (1 / 4) * (Ψ X ^ 2 * gradSqC U X) := by
    intro X
    simp only [gradSqC, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hG : Integrable (fun X => ∑ i, ∑ k,
      (weakGradC Ψ X i k + (1 / 2) * Ψ X * weakGradC U X i k) ^ 2) P := by
    simp_rw [hpt]
    exact (hF1.add hF2).add (hF3.const_mul _)
  have hG0 : ∀ X : Config N d, 0 ≤ ∑ i, ∑ k,
      (weakGradC Ψ X i k + (1 / 2) * Ψ X * weakGradC U X i k) ^ 2 :=
    fun X => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsh : shEn μ Ψ U = ENNReal.ofReal (∫ X, ∑ i, ∑ k,
      (weakGradC Ψ X i k + (1 / 2) * Ψ X * weakGradC U X i k) ^ 2 ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hG (ae_of_all _ hG0)]
    rfl
  have href : refEnergy μ Ψ = ENNReal.ofReal (∫ X, gradSqC Ψ X ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hF1
      (ae_of_all _ fun X => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    rfl
  refine ⟨by rw [hsh]; exact ENNReal.ofReal_ne_top, ?_⟩
  have hF1nn : 0 ≤ ∫ X, gradSqC Ψ X ∂P :=
    integral_nonneg fun X => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hsh, href, ENNReal.toReal_ofReal (integral_nonneg hG0), ENNReal.toReal_ofReal hF1nn]
  simp_rw [hpt]
  have h12 : ∫ X, (gradSqC Ψ X + Ψ X * ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC U X i k) ∂P =
      ∫ X, gradSqC Ψ X ∂P +
        ∫ X, Ψ X * ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC U X i k ∂P := integral_add hF1 hF2
  have h123 : ∫ X, (gradSqC Ψ X + Ψ X * ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC U X i k +
      (1 / 4) * (Ψ X ^ 2 * gradSqC U X)) ∂P =
      ∫ X, (gradSqC Ψ X + Ψ X * ∑ i, ∑ k, weakGradC Ψ X i k * weakGradC U X i k) ∂P +
        ∫ X, (1 / 4) * (Ψ X ^ 2 * gradSqC U X) ∂P :=
    integral_add (hF1.add hF2) (hF3.const_mul _)
  rw [h123, h12, integral_const_mul]

end Expand

end SharpLSI.FL
