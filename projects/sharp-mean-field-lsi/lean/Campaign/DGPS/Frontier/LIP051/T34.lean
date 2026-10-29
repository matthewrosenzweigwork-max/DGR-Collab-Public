import DGPS.Frontier.LIP051.T32
import DGPS.Frontier.LIP051.T33

/-!
# LIP051.34: Positive spectral sections and tails

Task id `LIP051.34`, title "Positive spectral sections and tails" (node LIP051, "Joint Gaussian and
quadratic fluctuation limit", category leaf formalization, verification V1). Proved inputs:
`LIP051.03` (`DGPS.Frontier.LIP051.T03`), `LIP051.25` (`DGPS.Frontier.LIP051.T25`),
`LIP051.32` (`DGPS.Frontier.LIP051.T32`) and `LIP051.33` (`DGPS.Frontier.LIP051.T33`).

Let `K` be the centered kernel of `LIP051.03` for a bounded continuous symmetric `W` on the torus,
let `e` be a real Hilbert basis of `L²(μ)` with `e 0 = 1`, and let `f j` be measurable
representatives of `e j`. With the coefficients `T i j = ∬ K(x,y) f i(x) f j(y) dμ(x) dμ(y)`, the
positive section `K_R = ∑_{i,j=1}^R T_ij f_i ⊗ f_j` and the tail `F_R = K - K_R`, the main theorem
states: `‖F_R‖₂ → 0`; the positive-pair Parseval identity `∑_{i,j ≥ 1} T_ij² = ‖K‖₂²`; the tail
identity `‖F_R‖₂² = ∑_{(i,j) ∉ {1..R}²} T_ij²` over positive pairs, for every `R`; and that `K_R`
and `F_R` are symmetric, `L²`, and centered in either variable almost everywhere.

## Provides

* `DGPS.Frontier.LIP051.coefT_LIP05134`: the coefficient `T i j`, the integral of
  `K(p.1,p.2) f i p.1 f j p.2` over `μ ⊗ μ`.
* `DGPS.Frontier.LIP051.sectionKR_LIP05134`: the positive section `K_R(x,y)`, the finite sum over
  `i, j ∈ {1,…,R}` of `T i j f i(x) f j(y)`.
* `DGPS.Frontier.LIP051.tailKR_LIP05134`: the tail `F_R = K - K_R`.
* `DGPS.Frontier.LIP051.lip051_34_positive_spectral_sections_tails`: the main theorem. Its conjuncts
  are the convergence `‖F_R‖₂ → 0`, the positive Parseval identity, the positive tail identity for
  every `R`, the membership in `L²` of `K_R` and `F_R`, their pointwise symmetry, and their a.e.
  centering in each variable.
* Helpers, all with suffix `_LIP05134`:
  `integral_rep_mul_LIP05134` (the representatives have the orthonormality integrals),
  `integral_rep_eq_zero_LIP05134` (`∫ f i = 0` for `i ≠ 0`),
  `ae_sum_LIP05134` (a.e. pointwise form of a finite sum in `L²`),
  `inner_coef_LIP05134` (the inner product with a product class is the kernel integral),
  `sum_range_eq_Icc_LIP05134` (removal of the zero row and column from a double sum),
  `hasSum_pos_LIP05134` and `hasSum_pos_full_LIP05134` (transfer of a `HasSum` over `ℕ × ℕ` to
  positive pairs), `sec_decomp_LIP05134`, `sec_symm_LIP05134`, `sec_integrable_first_LIP05134`,
  `sec_center_first_LIP05134`, `tail_symm_LIP05134`, `tail_center_first_LIP05134` (decomposition,
  symmetry, integrability and centering of the sections and the tails).

## R5 notes

1. Kernel. `K` is `centeredKernelOf_LIP05103 μ W`, under exactly the hypotheses of `LIP051.03`
   and `LIP051.33`: `Continuous (Function.uncurry W)`, symmetry of `W`, `0 ≤ M` and `|W| ≤ M`. No
   `Spec`, `KData`, `Hw` or Gaussian object occurs. The identification of `S.mu` and `D.K` with `μ`
   and `K` belongs to `LIP051.01` and is not used here.
2. Basis. `e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)` with `he0 : e 0 = Lp.const 2 μ 1`, as in `LIP051.25`,
   `LIP051.32` and `LIP051.33`. The normalization `e 0 = 1` is a hypothesis, because the
   specification lists it as data; it is not derived.
3. Representatives. The sections are functions, so the theorem quantifies over every family `f` of
   measurable functions with `f j =ᵐ[μ] e j`, as in `LIP051.33`. Every conclusion holds for every
   such family, so none depends on a selected representative.
4. Positive indices (defect FD-002). The sections and tails use the indices `i, j ∈ {1,…,R}` and
   the positive pairs, as the specification writes them. The rectangle `{0,…,R}²` of `LIP051.32`
   is reduced to `{1,…,R}²` only by removing terms whose coefficient is zero by `LIP051.33`
   (`T 0 j = 0` and `T i 0 = 0`). No index restriction is added to the hypotheses.
5. Parseval and tails. The positive-pair sums are `HasSum` (not `tsum`), so summability is part of
   the claim. The complement of `{1,…,R}²` is taken among positive pairs, written as the subtype
   `{q // (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)}`.
6. Norms. `‖F‖₂` is written `(eLpNorm F 2 (μ.prod μ)).toReal`, and `‖K‖₂²` as the square of it.
   `K` is the pointwise continuous-representative function, not an arbitrary class representative.
7. Centering. The specification says "centered almost everywhere". The proof gives the identities
   for every `y` (respectively every `x`), and the statement records them in the `∀ᵐ` form that the
   specification uses. Symmetry of `K_R` and `F_R` is stated pointwise.
8. Lean-exposed specification defects: none found.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP051

variable {d : ℕ}

/-- The coefficient `T i j = ∬ K(x,y) f i(x) f j(y) dμ(x) dμ(y)` of the centered kernel. -/
noncomputable def coefT_LIP05134 (μ : Measure (DGPS.Torus d))
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (i j : ℕ) : ℝ :=
  ∫ p, centeredKernelOf_LIP05103 μ W p.1 p.2 * f i p.1 * f j p.2 ∂(μ.prod μ)

/-- The positive section `K_R(x,y) = ∑_{i,j=1}^R T_ij f_i(x) f_j(y)`. -/
noncomputable def sectionKR_LIP05134 (μ : Measure (DGPS.Torus d))
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R : ℕ)
    (p : DGPS.Torus d × DGPS.Torus d) : ℝ :=
  ∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R, coefT_LIP05134 μ W f i j * f i p.1 * f j p.2

/-- The tail `F_R = K - K_R`. -/
noncomputable def tailKR_LIP05134 (μ : Measure (DGPS.Torus d))
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ) (R : ℕ)
    (p : DGPS.Torus d × DGPS.Torus d) : ℝ :=
  centeredKernelOf_LIP05103 μ W p.1 p.2 - sectionKR_LIP05134 μ W f R p

section Helpers

variable {α : Type*} [MeasurableSpace α]

/-- The representatives have the orthonormality integrals `∫ f a f b = δ_ab`. -/
lemma integral_rep_mul_LIP05134 {μ : Measure α} [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) {f : ℕ → α → ℝ} (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (a b : ℕ) : ∫ x, f a x * f b x ∂μ = if a = b then 1 else 0 := by
  rw [← orthonormal_iff_ite.mp e.orthonormal a b, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hfe a, hfe b] with x h1 h2
  simp only [← h1, ← h2, RCLike.inner_apply, conj_trivial]
  ring

/-- For `i ≠ 0` and representatives with `f 0 = 1` a.e., the integral of `f i` vanishes. -/
lemma integral_rep_eq_zero_LIP05134 {μ : Measure α} [IsProbabilityMeasure μ]
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) {f : ℕ → α → ℝ} (hfe : ∀ j, f j =ᵐ[μ] (e j : α → ℝ))
    (hf0 : f 0 =ᵐ[μ] fun _ => (1 : ℝ)) {i : ℕ} (hi : i ≠ 0) : ∫ x, f i x ∂μ = 0 := by
  have h1 : ∫ x, f i x * f 0 x ∂μ = ∫ x, f i x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf0] with x hx
    simp only [hx, mul_one]
  rw [← h1, integral_rep_mul_LIP05134 e hfe]
  simp [hi]

/-- A finite sum of `L²` classes has, almost everywhere, the pointwise value of the sum. -/
lemma ae_sum_LIP05134 {ν : Measure α} {ι : Type*} (s : Finset ι) (g : ι → Lp ℝ 2 ν)
    (φ : ι → α → ℝ) (h : ∀ i, ∀ᵐ p ∂ν, ⇑(g i) p = φ i p) :
    ∀ᵐ p ∂ν, ⇑(∑ i ∈ s, g i) p = ∑ i ∈ s, φ i p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 ν] with p hp
    rw [Finset.sum_empty, Finset.sum_empty]
    exact hp
  | insert a s ha ih =>
    filter_upwards [Lp.coeFn_add (g a) (∑ i ∈ s, g i), h a, ih] with p h1 h2 h3
    rw [Finset.sum_insert ha, Finset.sum_insert ha, h1, Pi.add_apply, h2, h3]

/-- The inner product of an `L²` class with a product class is the kernel integral. -/
lemma inner_coef_LIP05134 {μ : Measure α} [IsProbabilityMeasure μ] {K : α × α → ℝ}
    {Kl Q : Lp ℝ 2 (μ.prod μ)} {a b : α → ℝ}
    (hKl : ⇑Kl =ᵐ[μ.prod μ] K) (hQ : ⇑Q =ᵐ[μ.prod μ] fun p => a p.1 * b p.2) :
    inner ℝ Kl Q = ∫ p, K p * a p.1 * b p.2 ∂(μ.prod μ) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hKl, hQ] with p h1 h2
  simp only [RCLike.inner_apply, conj_trivial, h1, h2]
  ring

/-- Removal of the zero row and zero column from a double sum over `{0,…,R}²`. -/
lemma sum_range_eq_Icc_LIP05134 (G : ℕ → ℕ → ℝ) (R : ℕ) (h0 : ∀ j, G 0 j = 0)
    (h0' : ∀ i, G i 0 = 0) :
    ∑ i ∈ Finset.range (R + 1), ∑ j ∈ Finset.range (R + 1), G i j =
      ∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R, G i j := by
  have hsub : Finset.Icc 1 R ⊆ Finset.range (R + 1) := by
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    omega
  have hzero : ∀ x ∈ Finset.range (R + 1), x ∉ Finset.Icc 1 R → x = 0 := by
    intro x hx hnx
    rw [Finset.mem_range] at hx
    rw [Finset.mem_Icc] at hnx
    omega
  calc ∑ i ∈ Finset.range (R + 1), ∑ j ∈ Finset.range (R + 1), G i j
      = ∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.range (R + 1), G i j := by
        symm
        apply Finset.sum_subset hsub
        intro i hi hni
        obtain rfl := hzero i hi hni
        exact Finset.sum_eq_zero fun j _ => h0 j
    _ = ∑ i ∈ Finset.Icc 1 R, ∑ j ∈ Finset.Icc 1 R, G i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        symm
        apply Finset.sum_subset hsub
        intro j hj hnj
        obtain rfl := hzero j hj hnj
        exact h0' i

/-- Transfer of a `HasSum` over `ℕ × ℕ` to the positive pairs, for a set `t` of pairs. -/
lemma hasSum_pos_LIP05134 {g : ℕ × ℕ → ℝ} (hg : ∀ q : ℕ × ℕ, (q.1 = 0 ∨ q.2 = 0) → g q = 0)
    (t : Set (ℕ × ℕ)) {a : ℝ} (h : HasSum (fun q : t => g q) a) :
    HasSum (fun q : ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2} ∩ t : Set (ℕ × ℕ)) => g q) a := by
  have key : ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2} ∩ t : Set (ℕ × ℕ)).indicator g = t.indicator g := by
    funext q
    by_cases hqt : q ∈ t
    · by_cases hpos : q ∈ ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2} : Set (ℕ × ℕ))
      · rw [Set.indicator_of_mem (Set.mem_inter hpos hqt), Set.indicator_of_mem hqt]
      · have hn : q ∉ ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2} ∩ t : Set (ℕ × ℕ)) :=
          fun h' => hpos h'.1
        have hpos' : ¬(1 ≤ q.1 ∧ 1 ≤ q.2) := hpos
        rw [Set.indicator_of_notMem hn, Set.indicator_of_mem hqt]
        exact (hg q (by omega)).symm
    · have hn : q ∉ ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2} ∩ t : Set (ℕ × ℕ)) :=
        fun h' => hqt h'.2
      rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hqt]
  have h' : HasSum (t.indicator g) a := (hasSum_subtype_iff_indicator (f := g) (s := t)).1 h
  rw [← key] at h'
  exact (hasSum_subtype_iff_indicator (f := g)).2 h'

/-- Transfer of a `HasSum` over `ℕ × ℕ` to the positive pairs, when the summand vanishes off them. -/
lemma hasSum_pos_full_LIP05134 {g : ℕ × ℕ → ℝ}
    (hg : ∀ q : ℕ × ℕ, (q.1 = 0 ∨ q.2 = 0) → g q = 0) {a : ℝ} (h : HasSum g a) :
    HasSum (fun q : {q : ℕ × ℕ // 1 ≤ q.1 ∧ 1 ≤ q.2} => g q.1) a := by
  have hind : ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2} : Set (ℕ × ℕ)).indicator g = g := by
    funext q
    by_cases hpos : q ∈ ({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2} : Set (ℕ × ℕ))
    · exact Set.indicator_of_mem hpos g
    · rw [Set.indicator_of_notMem hpos]
      have hpos' : ¬(1 ≤ q.1 ∧ 1 ≤ q.2) := hpos
      exact (hg q (by omega)).symm
  have h' : HasSum (({q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2} : Set (ℕ × ℕ)).indicator g) a := by
    rw [hind]
    exact h
  exact (hasSum_subtype_iff_indicator (f := g) (s := {q : ℕ × ℕ | 1 ≤ q.1 ∧ 1 ≤ q.2})).2 h'

/-- Pointwise decomposition of the positive section as a sum over the first index. -/
lemma sec_decomp_LIP05134 (μ : Measure (DGPS.Torus d)) (W : DGPS.Torus d → DGPS.Torus d → ℝ)
    (f : ℕ → DGPS.Torus d → ℝ) (R : ℕ) (x y : DGPS.Torus d) :
    sectionKR_LIP05134 μ W f R (x, y) = ∑ i ∈ Finset.Icc 1 R,
      f i x * ∑ j ∈ Finset.Icc 1 R, coefT_LIP05134 μ W f i j * f j y := by
  unfold sectionKR_LIP05134
  dsimp only
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The positive section is symmetric as a function of its two variables. -/
lemma sec_symm_LIP05134 (μ : Measure (DGPS.Torus d)) (W : DGPS.Torus d → DGPS.Torus d → ℝ)
    (f : ℕ → DGPS.Torus d → ℝ)
    (hT : ∀ i j, coefT_LIP05134 μ W f i j = coefT_LIP05134 μ W f j i) (R : ℕ)
    (x y : DGPS.Torus d) :
    sectionKR_LIP05134 μ W f R (x, y) = sectionKR_LIP05134 μ W f R (y, x) := by
  unfold sectionKR_LIP05134
  dsimp only
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hT i j]
  ring

/-- Integrability of the positive section in its first variable. -/
lemma sec_integrable_first_LIP05134 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ)
    (hint : ∀ j, Integrable (f j) μ) (R : ℕ) (y : DGPS.Torus d) :
    Integrable (fun x => sectionKR_LIP05134 μ W f R (x, y)) μ := by
  simp only [sec_decomp_LIP05134]
  exact integrable_finsetSum _ fun i _ => (hint i).mul_const _

/-- The positive section is centered in its first variable, for every second variable. -/
lemma sec_center_first_LIP05134 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ)
    (hint : ∀ j, Integrable (f j) μ) (hmean : ∀ j, j ≠ 0 → ∫ x, f j x ∂μ = 0)
    (R : ℕ) (y : DGPS.Torus d) : ∫ x, sectionKR_LIP05134 μ W f R (x, y) ∂μ = 0 := by
  simp only [sec_decomp_LIP05134]
  rw [integral_finsetSum (Finset.Icc 1 R) fun i _ =>
    (hint i).mul_const (∑ j ∈ Finset.Icc 1 R, coefT_LIP05134 μ W f i j * f j y)]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [integral_mul_const, hmean i (by have := (Finset.mem_Icc.mp hi).1; omega), zero_mul]

/-- The tail is symmetric as a function of its two variables. -/
lemma tail_symm_LIP05134 (μ : Measure (DGPS.Torus d)) (W : DGPS.Torus d → DGPS.Torus d → ℝ)
    (f : ℕ → DGPS.Torus d → ℝ)
    (hKs : ∀ x y, centeredKernelOf_LIP05103 μ W x y = centeredKernelOf_LIP05103 μ W y x)
    (hT : ∀ i j, coefT_LIP05134 μ W f i j = coefT_LIP05134 μ W f j i) (R : ℕ)
    (x y : DGPS.Torus d) :
    tailKR_LIP05134 μ W f R (x, y) = tailKR_LIP05134 μ W f R (y, x) := by
  simp only [tailKR_LIP05134]
  rw [hKs x y, sec_symm_LIP05134 μ W f hT R x y]

/-- The tail is centered in its first variable, for every second variable. -/
lemma tail_center_first_LIP05134 {μ : Measure (DGPS.Torus d)} [IsProbabilityMeasure μ]
    (W : DGPS.Torus d → DGPS.Torus d → ℝ) (f : ℕ → DGPS.Torus d → ℝ)
    (hint : ∀ j, Integrable (f j) μ) (hmean : ∀ j, j ≠ 0 → ∫ x, f j x ∂μ = 0)
    (hKc : ∀ y, ∫ x, centeredKernelOf_LIP05103 μ W x y ∂μ = 0)
    (hKint : ∀ y, Integrable (fun x => centeredKernelOf_LIP05103 μ W x y) μ)
    (R : ℕ) (y : DGPS.Torus d) : ∫ x, tailKR_LIP05134 μ W f R (x, y) ∂μ = 0 := by
  simp only [tailKR_LIP05134]
  rw [integral_sub (hKint y) (sec_integrable_first_LIP05134 W f hint R y), hKc y,
    sec_center_first_LIP05134 W f hint hmean R y, sub_zero]

end Helpers

/-- LIP051.34: positive spectral sections and tails. For a probability measure `μ` on the torus,
a bounded continuous symmetric `W`, a real Hilbert basis `e` of `L²(μ)` with `e 0 = 1`, and
measurable representatives `f j` of the classes `e j`, with `K` the centered kernel of `LIP051.03`
and `T i j` the coefficients: the `L²` norms of the tails `F_R = K - K_R` tend to zero; the positive
Parseval identity and the positive tail identity hold; and `K_R`, `F_R` are `L²`, symmetric, and
centered in either variable almost everywhere. See the module docstring, R5 notes. -/
theorem lip051_34_positive_spectral_sections_tails {μ : Measure (DGPS.Torus d)}
    [IsProbabilityMeasure μ] {W : DGPS.Torus d → DGPS.Torus d → ℝ} {M : ℝ}
    (hWc : Continuous (Function.uncurry W)) (hs : ∀ x y, W x y = W y x)
    (hM : 0 ≤ M) (hb : ∀ x y, |W x y| ≤ M)
    (e : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (he0 : e 0 = Lp.const 2 μ (1 : ℝ))
    (f : ℕ → DGPS.Torus d → ℝ) (hfm : ∀ j, Measurable (f j))
    (hfe : ∀ j, f j =ᵐ[μ] (e j : DGPS.Torus d → ℝ)) :
    Tendsto (fun R : ℕ => (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal) atTop
        (𝓝 0) ∧
    HasSum (fun q : {q : ℕ × ℕ // 1 ≤ q.1 ∧ 1 ≤ q.2} => coefT_LIP05134 μ W f q.1.1 q.1.2 ^ 2)
      ((eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d => centeredKernelOf_LIP05103 μ W p.1 p.2)
        2 (μ.prod μ)).toReal ^ 2) ∧
    (∀ R : ℕ, HasSum (fun q : {q : ℕ × ℕ // (1 ≤ q.1 ∧ 1 ≤ q.2) ∧ ¬(q.1 ≤ R ∧ q.2 ≤ R)} =>
        coefT_LIP05134 μ W f q.1.1 q.1.2 ^ 2)
      ((eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal ^ 2)) ∧
    (∀ R : ℕ, MemLp (sectionKR_LIP05134 μ W f R) 2 (μ.prod μ)) ∧
    (∀ R : ℕ, MemLp (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)) ∧
    (∀ R : ℕ, ∀ x y : DGPS.Torus d, sectionKR_LIP05134 μ W f R (x, y) =
        sectionKR_LIP05134 μ W f R (y, x)) ∧
    (∀ R : ℕ, ∀ x y : DGPS.Torus d, tailKR_LIP05134 μ W f R (x, y) =
        tailKR_LIP05134 μ W f R (y, x)) ∧
    (∀ R : ℕ, (∀ᵐ y ∂μ, ∫ x, sectionKR_LIP05134 μ W f R (x, y) ∂μ = 0) ∧
        ∀ᵐ x ∂μ, ∫ y, sectionKR_LIP05134 μ W f R (x, y) ∂μ = 0) ∧
    (∀ R : ℕ, (∀ᵐ y ∂μ, ∫ x, tailKR_LIP05134 μ W f R (x, y) ∂μ = 0) ∧
        ∀ᵐ x ∂μ, ∫ y, tailKR_LIP05134 μ W f R (x, y) ∂μ = 0) := by
  obtain ⟨hKm, hKs, hKb, hKc, -, -, hKL, -⟩ :=
    lip051_03_centering_integrability_original_kernel (μ := μ) hWc hs hM hb
  obtain ⟨hsymT, hrow0, hcol0⟩ := lip051_33_symmetry_constant_row hWc hs hM hb e he0 f hfm hfe
  have hT0 : ∀ j, coefT_LIP05134 μ W f 0 j = 0 := hrow0
  have hTc0 : ∀ i, coefT_LIP05134 μ W f i 0 = 0 := hcol0
  have hTs : ∀ i j, coefT_LIP05134 μ W f i j = coefT_LIP05134 μ W f j i := hsymT
  have hKL' : MemLp (fun p : DGPS.Torus d × DGPS.Torus d => centeredKernelOf_LIP05103 μ W p.1 p.2)
      2 (μ.prod μ) := hKL
  have hmem : ∀ j, MemLp (f j) 2 μ := fun j => (Lp.memLp (e j)).ae_eq (hfe j).symm
  have hint : ∀ j, Integrable (f j) μ := fun j => (hmem j).integrable one_le_two
  have hf0 : f 0 =ᵐ[μ] fun _ => (1 : ℝ) := by
    refine (hfe 0).trans ?_
    rw [he0]
    exact Lp.coeFn_const _ _ _
  have hmean : ∀ j, j ≠ 0 → ∫ x, f j x ∂μ = 0 := fun j hj =>
    integral_rep_eq_zero_LIP05134 e hfe hf0 hj
  have hKint : ∀ y, Integrable (fun x => centeredKernelOf_LIP05103 μ W x y) μ := fun y =>
    Integrable.mono' (integrable_const (4 * M))
      (hKm.comp (measurable_id.prodMk (measurable_const (a := y)))).aestronglyMeasurable
      (ae_of_all _ fun x => by simp only [Real.norm_eq_abs]; exact hKb x y)
  obtain ⟨Kl, hKl⟩ : ∃ Kl : Lp ℝ 2 (μ.prod μ),
      ⇑Kl =ᵐ[μ.prod μ] fun p : DGPS.Torus d × DGPS.Torus d =>
        centeredKernelOf_LIP05103 μ W p.1 p.2 :=
    ⟨hKL'.toLp _, hKL'.coeFn_toLp⟩
  have hmemP : ∀ i j, MemLp (fun p : DGPS.Torus d × DGPS.Torus d => f i p.1 * f j p.2) 2
      (μ.prod μ) := fun i j => memLp_product_LIP05130 μ hfm hmem i j
  obtain ⟨P, hP⟩ : ∃ P : ℕ → ℕ → Lp ℝ 2 (μ.prod μ), ∀ i j,
      ⇑(P i j) =ᵐ[μ.prod μ] fun p : DGPS.Torus d × DGPS.Torus d => f i p.1 * f j p.2 :=
    ⟨fun i j => (hmemP i j).toLp _, fun i j => (hmemP i j).coeFn_toLp⟩
  have hcoef : ∀ i j, inner ℝ Kl (P i j) = coefT_LIP05134 μ W f i j := fun i j =>
    inner_coef_LIP05134 (a := f i) (b := f j) hKl (hP i j)
  obtain ⟨hconv, hpar, htail⟩ :=
    lip051_32_exhaustive_rectangular_projections μ e f hfe P hP Kl
  -- The rectangular projections of `Kl` are the positive sections almost everywhere.
  have hS : ∀ R : ℕ, ⇑(rectProj_LIP05132 P R Kl) =ᵐ[μ.prod μ]
      fun p => sectionKR_LIP05134 μ W f R p := by
    intro R
    have hsum : rectProj_LIP05132 P R Kl =
        ∑ q ∈ rectIdx_LIP05132 R, inner ℝ Kl (P q.1 q.2) • P q.1 q.2 := by
      unfold rectProj_LIP05132 rectIdx_LIP05132
      simp only [Finset.sum_product]
    have hq : ∀ q : ℕ × ℕ, ∀ᵐ p ∂(μ.prod μ),
        ⇑(inner ℝ Kl (P q.1 q.2) • P q.1 q.2) p =
          coefT_LIP05134 μ W f q.1 q.2 * f q.1 p.1 * f q.2 p.2 := by
      intro q
      filter_upwards [Lp.coeFn_smul (inner ℝ Kl (P q.1 q.2)) (P q.1 q.2),
        hP q.1 q.2] with p h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul, hcoef q.1 q.2, mul_assoc]
    have hrect : ∀ p : DGPS.Torus d × DGPS.Torus d,
        ∑ q ∈ rectIdx_LIP05132 R, coefT_LIP05134 μ W f q.1 q.2 * f q.1 p.1 * f q.2 p.2 =
          sectionKR_LIP05134 μ W f R p := by
      intro p
      unfold rectIdx_LIP05132 sectionKR_LIP05134
      rw [Finset.sum_product]
      exact sum_range_eq_Icc_LIP05134 (fun i j => coefT_LIP05134 μ W f i j * f i p.1 * f j p.2) R
        (fun j => by simp only [hT0 j, zero_mul])
        (fun i => by simp only [hTc0 i, zero_mul])
    rw [hsum]
    filter_upwards [ae_sum_LIP05134 (rectIdx_LIP05132 R)
      (fun q : ℕ × ℕ => inner ℝ Kl (P q.1 q.2) • P q.1 q.2)
      (fun q p => coefT_LIP05134 μ W f q.1 q.2 * f q.1 p.1 * f q.2 p.2) hq] with p hp
    exact hp.trans (hrect p)
  -- The norm of the tail is the `L²` norm of `Kl` minus its rectangular projection.
  have hnorm : ∀ R : ℕ, (eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal =
      ‖Kl - rectProj_LIP05132 P R Kl‖ := by
    intro R
    have hT : tailKR_LIP05134 μ W f R =ᵐ[μ.prod μ] ⇑(Kl - rectProj_LIP05132 P R Kl) := by
      filter_upwards [Lp.coeFn_sub Kl (rectProj_LIP05132 P R Kl), hKl, hS R] with p h1 h2 h3
      simp only [tailKR_LIP05134, h1, Pi.sub_apply, h2, h3]
    rw [Lp.norm_def, eLpNorm_congr_ae hT]
  -- Coefficients with a zero index vanish, as functions on the pairs.
  have hg0 : ∀ q : ℕ × ℕ, (q.1 = 0 ∨ q.2 = 0) → coefT_LIP05134 μ W f q.1 q.2 ^ 2 = 0 := by
    rintro ⟨i, j⟩ h
    rcases h with h | h
    · dsimp only at h
      subst h
      simp [hT0 j]
    · dsimp only at h
      subst h
      simp [hTc0 i]
  have hnK : ‖Kl‖ = (eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d =>
      centeredKernelOf_LIP05103 μ W p.1 p.2) 2 (μ.prod μ)).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae hKl]
  -- Parseval over the positive pairs.
  have hsq : HasSum (fun q : ℕ × ℕ => coefT_LIP05134 μ W f q.1 q.2 ^ 2)
      ((eLpNorm (fun p : DGPS.Torus d × DGPS.Torus d => centeredKernelOf_LIP05103 μ W p.1 p.2)
        2 (μ.prod μ)).toReal ^ 2) := by
    have hfun : (fun q : ℕ × ℕ => inner ℝ Kl (P q.1 q.2) ^ 2) =
        fun q : ℕ × ℕ => coefT_LIP05134 μ W f q.1 q.2 ^ 2 :=
      funext fun q => by rw [hcoef q.1 q.2]
    rw [hfun, hnK] at hpar
    exact hpar
  have hpos := hasSum_pos_full_LIP05134 (g := fun q : ℕ × ℕ => coefT_LIP05134 μ W f q.1 q.2 ^ 2)
    hg0 hsq
  -- Tail identities over the positive pairs outside `{1,…,R}²`.
  have htailSum : ∀ R : ℕ, HasSum (fun q : {q : ℕ × ℕ // (1 ≤ q.1 ∧ 1 ≤ q.2) ∧
      ¬(q.1 ≤ R ∧ q.2 ≤ R)} => coefT_LIP05134 μ W f q.1.1 q.1.2 ^ 2)
      ((eLpNorm (tailKR_LIP05134 μ W f R) 2 (μ.prod μ)).toReal ^ 2) := by
    intro R
    have hfun : (fun q : {q : ℕ × ℕ // ¬(q.1 ≤ R ∧ q.2 ≤ R)} =>
        inner ℝ Kl (P q.1.1 q.1.2) ^ 2) =
        fun q : {q : ℕ × ℕ // ¬(q.1 ≤ R ∧ q.2 ≤ R)} => coefT_LIP05134 μ W f q.1.1 q.1.2 ^ 2 :=
      funext fun q => by rw [hcoef q.1.1 q.1.2]
    have h1 := htail R
    rw [hfun, ← hnorm R] at h1
    exact hasSum_pos_LIP05134 (g := fun q : ℕ × ℕ => coefT_LIP05134 μ W f q.1 q.2 ^ 2) hg0
      {q : ℕ × ℕ | ¬(q.1 ≤ R ∧ q.2 ≤ R)} h1
  -- Membership, symmetry and centering of the sections and tails.
  have hsecMem : ∀ R : ℕ, MemLp (sectionKR_LIP05134 μ W f R) 2 (μ.prod μ) := fun R =>
    (Lp.memLp (rectProj_LIP05132 P R Kl)).ae_eq (hS R)
  have htailMem : ∀ R : ℕ, MemLp (tailKR_LIP05134 μ W f R) 2 (μ.prod μ) := fun R =>
    hKL'.sub (hsecMem R)
  have hsecC : ∀ R : ℕ, (∀ᵐ y ∂μ, ∫ x, sectionKR_LIP05134 μ W f R (x, y) ∂μ = 0) ∧
      ∀ᵐ x ∂μ, ∫ y, sectionKR_LIP05134 μ W f R (x, y) ∂μ = 0 := fun R =>
    ⟨ae_of_all _ fun y => sec_center_first_LIP05134 W f hint hmean R y,
     ae_of_all _ fun x => by
       have h1 : ∫ y, sectionKR_LIP05134 μ W f R (x, y) ∂μ =
           ∫ y, sectionKR_LIP05134 μ W f R (y, x) ∂μ :=
         integral_congr_ae (ae_of_all _ fun y => sec_symm_LIP05134 μ W f hTs R x y)
       rw [h1]
       exact sec_center_first_LIP05134 W f hint hmean R x⟩
  have htailC : ∀ R : ℕ, (∀ᵐ y ∂μ, ∫ x, tailKR_LIP05134 μ W f R (x, y) ∂μ = 0) ∧
      ∀ᵐ x ∂μ, ∫ y, tailKR_LIP05134 μ W f R (x, y) ∂μ = 0 := fun R =>
    ⟨ae_of_all _ fun y => tail_center_first_LIP05134 W f hint hmean hKc hKint R y,
     ae_of_all _ fun x => by
       have h1 : ∫ y, tailKR_LIP05134 μ W f R (x, y) ∂μ =
           ∫ y, tailKR_LIP05134 μ W f R (y, x) ∂μ :=
         integral_congr_ae (ae_of_all _ fun y => tail_symm_LIP05134 μ W f hKs hTs R x y)
       rw [h1]
       exact tail_center_first_LIP05134 W f hint hmean hKc hKint R x⟩
  refine ⟨?_, hpos, htailSum, hsecMem, htailMem,
    fun R x y => sec_symm_LIP05134 μ W f hTs R x y,
    fun R x y => tail_symm_LIP05134 μ W f hKs hTs R x y, hsecC, htailC⟩
  exact Filter.Tendsto.congr (fun R => (hnorm R).symm) hconv

end DGPS.Frontier.LIP051
