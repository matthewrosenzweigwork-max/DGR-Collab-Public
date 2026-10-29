import DGPS.Frontier.LIP051.T03

/-!
# LIP051.21: Exact empirical energy decomposition

Task id `LIP051.21`, title "Exact empirical energy decomposition" (node LIP051,
"Joint Gaussian and quadratic fluctuation limit", leaf formalization, verification V1,
dispatch tier 4).

Let `μ` be a probability measure on the torus and `K` a symmetric kernel; in the campaign `K` is the
centered kernel `centeredKernelOf_LIP05103 μ W` of `LIP051.03`. For real functions `e j` put
`T i j = ∬ K(x,y) e i(x) e j(y) dμ(x) dμ(y)`, `K_R(x,y) = ∑_{i,j=1}^R T i j e i(x) e j(y)`,
`F_R = K - K_R`, `d_K = ∫ K(x,x) dμ(x)` and `tr T_R = ∑_{i=1}^R T i i`. For `N` points
`x : Fin N → Torus d` put `Z_j = N^{-1/2} ∑_l e j (x l)`, `U_N = (2N)⁻¹ ∑_{l,k} K(x l, x k)`,
`A_N(F) = N⁻¹ ∑_{i<j} F(x i, x j)` and `D_{N,R} = (2N)⁻¹ ∑_l F_R(x l, x l) - (d_K - tr T_R)/2`.
With `V_{N,R} = (1/2) [∑_{i,j=1}^R T i j (Z_i Z_j - δ_ij) + d_K]` (the formula of `LIP051.20`),
the main declaration proves the exact identity `U_N = V_{N,R} + A_N(F_R) + D_{N,R}`.

## Provides

* `DGPS.Frontier.LIP051.lip051_21_exact_empirical_energy_decomposition`: for the centered kernel
  `centeredKernelOf_LIP05103 μ W` of a symmetric `W` (probability `μ`), every `R`, every `N` and
  every sample `x : Fin N → Torus d` satisfy `U_N = V_{N,R} + A_N(F_R) + D_{N,R}`.
* `DGPS.Frontier.LIP051.lip051_21_exact_empirical_energy_decomposition_symmetric_kernel`: the same
  identity for an arbitrary symmetric kernel `K` and an arbitrary family `e` of real functions;
  the main declaration is its specialization.
* Helpers (all suffixed `_LIP05121`): the coefficients `tIJ_LIP05121`, the finite-rank section
  `kSecLIP05121`, the tail `tailLIP05121` (`F_R`), the trace `traceLIP05121`, the diagonal integral
  `dKLIP05121`, the normalized sum `zLIP05121` (`Z_{N,j}`), the energy `energyLIP05121` (`U_N`),
  the pair sum `pairSumLIP05121` (`A_N`), the diagonal remainder `diagRemLIP05121` (`D_{N,R}`),
  the fixed-rank polynomial `fixedRankLIP05121` (`V_{N,R}`), and the lemmas used in the proof.

## R5 notes

1. Kernel and hypotheses. The main declaration assumes exactly the symmetry `W x y = W y x` of the
   source function `W`, through `kernel_symm_LIP05103`. The continuity, the uniform bound and the
   bound `0 ≤ M` of `LIP051.03` are not assumed, because the identity is algebraic and uses none of
   them. The statement is therefore stronger than the one with those hypotheses. The measure is a
   probability measure, as in the campaign setup.
2. Sample points. The specification says "every sample point outside the representative-null
   sets". The identity is proved for every `x : Fin N → Torus d`. The functions `e j` and `K` are
   used pointwise, so no representative choice enters and no null set is excluded.
3. Basis data. The identity does not use `L²`, orthonormality, `e 0 = 1` or measurability of
   the feature functions; the family `e : ℕ → Torus d → ℝ` is arbitrary. Consequently `LIP051.06`
   and `LIP051.07` are not needed as inputs, and this file does not depend on them. The
   measurable-representative facts of those units apply to the specialization only.
4. Index convention. Positive indices only: `T i j`, the section `K_R`, the trace `tr T_R` and the
   sums in `V_{N,R}` run over `i, j ∈ {1,…,R}` (`Finset.Icc 1 R`). Index zero is never used, so
   the Gaussian zero-mode issue (defect FD-002) does not arise. `R = 0` gives empty sums.
5. Normalization. `N^{-1/2}` is written `(Real.sqrt N)⁻¹`. `U_N` is `(2N)⁻¹` times the full double
   sum, and `A_N` is `N⁻¹` times the strict-pair double sum `∑_{i<j}` over `Fin N`.
6. Diagonal. `d_K` is `∫ y, K y y ∂μ` for the pointwise kernel. The diagonal is never replaced by an
   almost-everywhere representative, so the original diagonal is retained in `F_R(x l, x l)`.
7. Specification of `V_{N,R}`. The specification says it is "given by the same formula as
   LIP051.20". That formula is the displayed one in the node document, and it is defined here
   with the suffix `_LIP05121`, since the `LIP051.20` file is not part of this unit's inputs.
8. No `N ≥ 1` hypothesis. The identity is stated for every `N`. For `N = 0` both sides are the
   same expression under Lean's conventions, so the requirement `N ≥ 1` of the specification is
   weakened, not changed in content.
9. Interchange. All sums are finite sums over `Fin N` or `Finset.Icc 1 R`. No infinite series are
   involved, so no interchange with a limit is made.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP051

variable {d : ℕ}

/-- The coefficient `T i j = ∬ K(x,y) e i(x) e j(y) dμ(x) dμ(y)`, as an integral over `μ.prod μ`. -/
noncomputable def tIJ_LIP05121 (μ : Measure (DGPS.Torus d))
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (e : ℕ → DGPS.Torus d → ℝ) (i j : ℕ) : ℝ :=
  ∫ p, K p.1 p.2 * e i p.1 * e j p.2 ∂(μ.prod μ)

/-- The finite-rank section `K_R(x,y) = ∑_{i,j=1}^R T i j e i(x) e j(y)`, indices `1..R`. -/
noncomputable def kSecLIP05121 (μ : Measure (DGPS.Torus d))
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (e : ℕ → DGPS.Torus d → ℝ) (R : ℕ)
    (x y : DGPS.Torus d) : ℝ :=
  ∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R, tIJ_LIP05121 μ K e i j * e i x * e j y

/-- The tail `F_R = K - K_R`. -/
noncomputable def tailLIP05121 (μ : Measure (DGPS.Torus d))
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (e : ℕ → DGPS.Torus d → ℝ) (R : ℕ)
    (x y : DGPS.Torus d) : ℝ :=
  K x y - kSecLIP05121 μ K e R x y

/-- The trace `tr T_R = ∑_{i=1}^R T i i`. -/
noncomputable def traceLIP05121 (μ : Measure (DGPS.Torus d))
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (e : ℕ → DGPS.Torus d → ℝ) (R : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 R, tIJ_LIP05121 μ K e i i

/-- The diagonal integral `d_K = ∫ K(x,x) dμ(x)` of the pointwise kernel. -/
noncomputable def dKLIP05121 (μ : Measure (DGPS.Torus d))
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) : ℝ :=
  ∫ y, K y y ∂μ

/-- The normalized sum `Z_{N,j} = N^{-1/2} ∑_{l} e j (x l)` on `N` points. -/
noncomputable def zLIP05121 (N : ℕ) (e : ℕ → DGPS.Torus d → ℝ) (j : ℕ)
    (x : Fin N → DGPS.Torus d) : ℝ :=
  (Real.sqrt (N : ℝ))⁻¹ * (∑ l : Fin N, e j (x l))

/-- The empirical energy `U_N = (2N)⁻¹ ∑_{l,k} K(x l, x k)`. -/
noncomputable def energyLIP05121 (K : DGPS.Torus d → DGPS.Torus d → ℝ) (N : ℕ)
    (x : Fin N → DGPS.Torus d) : ℝ :=
  (2 * (N : ℝ))⁻¹ * (∑ l : Fin N, ∑ k : Fin N, K (x l) (x k))

/-- The pair sum `A_N(F) = N⁻¹ ∑_{i<j} F(x i, x j)`. -/
noncomputable def pairSumLIP05121 (N : ℕ) (F : DGPS.Torus d → DGPS.Torus d → ℝ)
    (x : Fin N → DGPS.Torus d) : ℝ :=
  (N : ℝ)⁻¹ * (∑ i : Fin N, ∑ j : Fin N, if i < j then F (x i) (x j) else 0)

/-- The diagonal remainder `D_{N,R} = (2N)⁻¹ ∑_l F_R(x l, x l) - (d_K - tr T_R)/2`. -/
noncomputable def diagRemLIP05121 (μ : Measure (DGPS.Torus d))
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (e : ℕ → DGPS.Torus d → ℝ) (R N : ℕ)
    (x : Fin N → DGPS.Torus d) : ℝ :=
  (2 * (N : ℝ))⁻¹ * (∑ l : Fin N, tailLIP05121 μ K e R (x l) (x l))
    - (1 / 2 : ℝ) * (dKLIP05121 μ K - traceLIP05121 μ K e R)

/-- The fixed-rank polynomial `V_{N,R} = (1/2) [∑_{i,j=1}^R T i j (Z_i Z_j - δ_ij) + d_K]`. -/
noncomputable def fixedRankLIP05121 (μ : Measure (DGPS.Torus d))
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (e : ℕ → DGPS.Torus d → ℝ) (R N : ℕ)
    (x : Fin N → DGPS.Torus d) : ℝ :=
  (1 / 2 : ℝ) * ((∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R,
    tIJ_LIP05121 μ K e i j * (zLIP05121 N e i x * zLIP05121 N e j x - (if i = j then (1 : ℝ) else 0)))
    + dKLIP05121 μ K)

/-- Symmetric double sums over `Fin N`: splitting a symmetric double sum into twice the strict
upper-triangular part plus the diagonal. -/
theorem sum_fin_symm_LIP05121 {N : ℕ} (G : Fin N → Fin N → ℝ) (hG : ∀ i j, G i j = G j i) :
    ∑ i, ∑ j, G i j = 2 * (∑ i, ∑ j, if i < j then G i j else 0) + ∑ i, G i i := by
  have hsplit : ∀ i j, G i j = (if i < j then G i j else 0) + (if j < i then G i j else 0)
      + (if i = j then G i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, h.not_gt]
    · subst h
      simp
    · simp [h, h.ne', h.not_gt]
  have hswap : ∑ i, ∑ j, (if j < i then G i j else 0)
      = ∑ i, ∑ j, (if i < j then G i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hG j i]
  have hdiag : ∑ i, ∑ j, (if i = j then G i j else 0) = ∑ i, G i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  calc ∑ i, ∑ j, G i j
      = ∑ i, ∑ j, ((if i < j then G i j else 0) + (if j < i then G i j else 0)
          + (if i = j then G i j else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = 2 * (∑ i, ∑ j, if i < j then G i j else 0) + ∑ i, G i i := by
        simp only [Finset.sum_add_distrib]
        rw [hswap, hdiag]
        ring

/-- Symmetry of the coefficients `T i j` under a symmetric kernel. -/
theorem tIJ_symm_LIP05121 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (K : DGPS.Torus d → DGPS.Torus d → ℝ)
    (hK : ∀ x y, K x y = K y x) (e : ℕ → DGPS.Torus d → ℝ) (i j : ℕ) :
    tIJ_LIP05121 μ K e i j = tIJ_LIP05121 μ K e j i := by
  unfold tIJ_LIP05121
  rw [← integral_prod_swap (f := fun p => K p.1 p.2 * e j p.1 * e i p.2)]
  congr 1
  funext p
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [hK p.2 p.1]
  ring

/-- Symmetry of the section `K_R` under a symmetric kernel. -/
theorem kSec_symm_LIP05121 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (K : DGPS.Torus d → DGPS.Torus d → ℝ)
    (hK : ∀ x y, K x y = K y x) (e : ℕ → DGPS.Torus d → ℝ) (R : ℕ)
    (x y : DGPS.Torus d) :
    kSecLIP05121 μ K e R x y = kSecLIP05121 μ K e R y x := by
  unfold kSecLIP05121
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [tIJ_symm_LIP05121 (μ := μ) K hK e j i]
  ring

/-- Symmetry of the tail `F_R = K - K_R` under a symmetric kernel. -/
theorem tail_symm_LIP05121 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (K : DGPS.Torus d → DGPS.Torus d → ℝ)
    (hK : ∀ x y, K x y = K y x) (e : ℕ → DGPS.Torus d → ℝ) (R : ℕ)
    (x y : DGPS.Torus d) :
    tailLIP05121 μ K e R x y = tailLIP05121 μ K e R y x := by
  unfold tailLIP05121
  rw [hK x y, kSec_symm_LIP05121 (μ := μ) K hK e R x y]

/-- Four-fold exchange of finite sums: the two sample indices are moved inside the two basis
indices, the second sample index outside the first. -/
theorem sum_comm4_LIP05121 {ι κ : Type*} (s t : Finset ι) (u v : Finset κ)
    (F : κ → κ → ι → ι → ℝ) :
    ∑ l ∈ u, ∑ k ∈ v, ∑ i ∈ s, ∑ j ∈ t, F l k i j
      = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ v, ∑ l ∈ u, F l k i j := by
  calc ∑ l ∈ u, ∑ k ∈ v, ∑ i ∈ s, ∑ j ∈ t, F l k i j
      = ∑ l ∈ u, ∑ i ∈ s, ∑ k ∈ v, ∑ j ∈ t, F l k i j :=
        Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ l ∈ u, ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ v, F l k i j :=
        Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ l ∈ u, ∑ j ∈ t, ∑ k ∈ v, F l k i j := Finset.sum_comm
    _ = ∑ i ∈ s, ∑ j ∈ t, ∑ l ∈ u, ∑ k ∈ v, F l k i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ s, ∑ j ∈ t, ∑ k ∈ v, ∑ l ∈ u, F l k i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm

/-- The double sum of the section, rewritten through the coefficients: the sum over all sample
pairs of `K_R(x l, x k)` equals `∑_{i,j} T i j (∑_l e i(x l)) (∑_k e j(x k))`. -/
theorem sum_kSec_LIP05121 (μ : Measure (DGPS.Torus d)) (K : DGPS.Torus d → DGPS.Torus d → ℝ)
    (e : ℕ → DGPS.Torus d → ℝ) (R N : ℕ) (x : Fin N → DGPS.Torus d) :
    (∑ l : Fin N, ∑ k : Fin N, kSecLIP05121 μ K e R (x l) (x k))
      = ∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R,
          tIJ_LIP05121 μ K e i j * ((∑ l : Fin N, e i (x l)) * (∑ k : Fin N, e j (x k))) := by
  unfold kSecLIP05121
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact sum_comm4_LIP05121 _ _ _ _ _

/-- The normalized products: `Z_i Z_j = N⁻¹ (∑_l e i(x l)) (∑_k e j(x k))`. -/
theorem zsq_LIP05121 (N : ℕ) (e : ℕ → DGPS.Torus d → ℝ) (i j : ℕ)
    (x : Fin N → DGPS.Torus d) :
    zLIP05121 N e i x * zLIP05121 N e j x
      = (N : ℝ)⁻¹ * ((∑ l : Fin N, e i (x l)) * (∑ k : Fin N, e j (x k))) := by
  unfold zLIP05121
  have hs : (Real.sqrt (N : ℝ))⁻¹ * (Real.sqrt (N : ℝ))⁻¹ = (N : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  rw [← hs]
  ring

/-- The energy of the section in coefficient form: `(2N)⁻¹ ∑_{l,k} K_R(x l, x k)
= (1/2) ∑_{i,j=1}^R T i j Z_i Z_j`. -/
theorem half_energy_kSec_LIP05121 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (e : ℕ → DGPS.Torus d → ℝ) (R N : ℕ)
    (x : Fin N → DGPS.Torus d) :
    (2 * (N : ℝ))⁻¹ * (∑ l : Fin N, ∑ k : Fin N, kSecLIP05121 μ K e R (x l) (x k))
      = (1 / 2 : ℝ) * ∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R,
          tIJ_LIP05121 μ K e i j * (zLIP05121 N e i x * zLIP05121 N e j x) := by
  rw [sum_kSec_LIP05121]
  simp only [zsq_LIP05121, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring_nf

/-- The fixed-rank polynomial in coefficient form, with the trace removed:
`V_{N,R} = (1/2) (∑_{i,j} T i j Z_i Z_j - tr T_R + d_K)`. -/
theorem fixedRank_eq_LIP05121 {μ : Measure (DGPS.Torus d)}
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (e : ℕ → DGPS.Torus d → ℝ) (R N : ℕ)
    (x : Fin N → DGPS.Torus d) :
    fixedRankLIP05121 μ K e R N x
      = (1 / 2 : ℝ) * ((∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R,
            tIJ_LIP05121 μ K e i j * (zLIP05121 N e i x * zLIP05121 N e j x))
          - traceLIP05121 μ K e R + dKLIP05121 μ K) := by
  have hdiag : (∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R,
      tIJ_LIP05121 μ K e i j * (if i = j then (1 : ℝ) else 0)) = traceLIP05121 μ K e R := by
    unfold traceLIP05121
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [hi]
  have hsub : (∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R,
      tIJ_LIP05121 μ K e i j * (zLIP05121 N e i x * zLIP05121 N e j x
        - (if i = j then (1 : ℝ) else 0)))
      = (∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R,
            tIJ_LIP05121 μ K e i j * (zLIP05121 N e i x * zLIP05121 N e j x))
        - (∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R,
            tIJ_LIP05121 μ K e i j * (if i = j then (1 : ℝ) else 0)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  unfold fixedRankLIP05121
  rw [hsub, hdiag]

/-- Splitting the symmetric double sum of the tail: `(2N)⁻¹ ∑_{l,k} F_R(x l, x k)
= A_N(F_R) + (2N)⁻¹ ∑_l F_R(x l, x l)`. -/
theorem tail_energy_LIP05121 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (hK : ∀ x y, K x y = K y x)
    (e : ℕ → DGPS.Torus d → ℝ) (R N : ℕ) (x : Fin N → DGPS.Torus d) :
    (2 * (N : ℝ))⁻¹ * (∑ l : Fin N, ∑ k : Fin N, tailLIP05121 μ K e R (x l) (x k))
      = pairSumLIP05121 N (tailLIP05121 μ K e R) x
        + (2 * (N : ℝ))⁻¹ * (∑ l : Fin N, tailLIP05121 μ K e R (x l) (x l)) := by
  have h := sum_fin_symm_LIP05121 (N := N)
    (fun i j => tailLIP05121 μ K e R (x i) (x j))
    (fun i j => tail_symm_LIP05121 (μ := μ) K hK e R (x i) (x j))
  rw [h]
  unfold pairSumLIP05121
  ring

/-- The diagonal remainder, rewritten with the full diagonal sum of the tail. -/
theorem diag_split_LIP05121 {μ : Measure (DGPS.Torus d)}
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (e : ℕ → DGPS.Torus d → ℝ) (R N : ℕ)
    (x : Fin N → DGPS.Torus d) :
    (2 * (N : ℝ))⁻¹ * (∑ l : Fin N, tailLIP05121 μ K e R (x l) (x l))
      = diagRemLIP05121 μ K e R N x + (1 / 2 : ℝ) * (dKLIP05121 μ K - traceLIP05121 μ K e R) := by
  unfold diagRemLIP05121
  ring

/-- **LIP051.21 (symmetric kernel form).** For an arbitrary symmetric kernel `K` of a probability
measure `μ` on the torus, an arbitrary family `e` of real functions, every `R`, every `N` and every
sample `x : Fin N → Torus d`: `U_N = V_{N,R} + A_N(F_R) + D_{N,R}`. -/
theorem lip051_21_exact_empirical_energy_decomposition_symmetric_kernel
    {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (K : DGPS.Torus d → DGPS.Torus d → ℝ) (hK : ∀ x y, K x y = K y x)
    (e : ℕ → DGPS.Torus d → ℝ) (R N : ℕ) (x : Fin N → DGPS.Torus d) :
    energyLIP05121 K N x
      = fixedRankLIP05121 μ K e R N x + pairSumLIP05121 N (tailLIP05121 μ K e R) x
        + diagRemLIP05121 μ K e R N x := by
  have hK' : ∀ l k : Fin N, K (x l) (x k)
      = kSecLIP05121 μ K e R (x l) (x k) + tailLIP05121 μ K e R (x l) (x k) := fun l k => by
    unfold tailLIP05121
    ring
  have hU : energyLIP05121 K N x
      = (2 * (N : ℝ))⁻¹ * (∑ l : Fin N, ∑ k : Fin N, kSecLIP05121 μ K e R (x l) (x k))
        + (2 * (N : ℝ))⁻¹ * (∑ l : Fin N, ∑ k : Fin N, tailLIP05121 μ K e R (x l) (x k)) := by
    unfold energyLIP05121
    simp only [hK', Finset.sum_add_distrib, mul_add]
  rw [hU, half_energy_kSec_LIP05121 K e R N x, tail_energy_LIP05121 K hK e R N x,
    fixedRank_eq_LIP05121 K e R N x, diag_split_LIP05121 K e R N x]
  ring

/-- **LIP051.21.** Exact empirical energy decomposition for the centered kernel
`centeredKernelOf_LIP05103 μ W` of a symmetric function `W` and a probability measure `μ` on the
torus: for every `R`, every `N` and every sample `x : Fin N → Torus d`,
`U_N = V_{N,R} + A_N(F_R) + D_{N,R}`. -/
theorem lip051_21_exact_empirical_energy_decomposition
    {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    {W : DGPS.Torus d → DGPS.Torus d → ℝ} (hs : ∀ x y, W x y = W y x)
    (e : ℕ → DGPS.Torus d → ℝ) (R N : ℕ) (x : Fin N → DGPS.Torus d) :
    energyLIP05121 (centeredKernelOf_LIP05103 μ W) N x
      = fixedRankLIP05121 μ (centeredKernelOf_LIP05103 μ W) e R N x
        + pairSumLIP05121 N (tailLIP05121 μ (centeredKernelOf_LIP05103 μ W) e R) x
        + diagRemLIP05121 μ (centeredKernelOf_LIP05103 μ W) e R N x :=
  lip051_21_exact_empirical_energy_decomposition_symmetric_kernel
    (centeredKernelOf_LIP05103 μ W) (fun a b => kernel_symm_LIP05103 (μ := μ) hs a b) e R N x

end DGPS.Frontier.LIP051
