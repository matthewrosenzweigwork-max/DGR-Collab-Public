import DGPS.Frontier.LIP051.T15

/-!
# LIP051.16: Finite Wick isometry

Task id `LIP051.16`, title "Finite Wick isometry" (node LIP051, "Joint Gaussian and quadratic
fluctuation limit", category leaf formalization, verification V1).

## Provides

* `DGPS.Frontier.LIP051.wickQuad_LIP05116`: the finite Wick quadratic
  `Q_A(z) = ∑ i ∈ s, ∑ j ∈ s, A i j * (z i * z j - δ_ij)` for a finite index set `s : Finset ℕ`, a
  coefficient array `A : ℕ → ℕ → ℝ` and a point `z : ℕ → ℝ` (Kronecker symbol as
  `if i = j then 1 else 0`). It is a definition kept public so that the main statement is readable;
  it carries the helper suffix by the campaign naming rule.
* `DGPS.Frontier.LIP051.lip051_16_finite_wick_isometry`: for `s` and `A B` symmetric on `s × s`,
  under the reference law `γ₀ = Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)` on `ℕ → ℝ`, the
  conjunction of (1)-(2) `Q_A` and `Q_B` lie in `L²(γ₀)` (`MemLp … 2`); (3)-(4) both have mean zero;
  (5) `E (Q_A Q_B) = 2 ∑ i ∈ s, ∑ j ∈ s, A i j * B i j`; (6) `∫ (Q_A - Q_B)² = 2 ∑ ∑ (A i j - B i j)²`;
  (7) the same identity for the `L²` norm: `lpNorm (Q_A - Q_B) 2 γ₀ ^ 2 = 2 ∑ ∑ (A i j - B i j)²`;
  (8) zero extension: for every `t ⊇ s`, the array equal to `A` on `s × s` and `0` elsewhere gives the
  same Wick polynomial over `t` as `A` over `s`, at every point `z`.
* Helpers (suffix `_LIP05116`, private except `wickQuad_LIP05116`): total-degree and monomial
  computations for exponent vectors, integrability of the products `z i * z j` and
  `z i * z j * z k * z l`, the pair mean `E (z i * z j) = δ_ij`, the entrywise covariance
  `E [(z i z j - δ_ij)(z k z l - δ_kl)] = δ_ik δ_jl + δ_il δ_jk`, measurability, the expansion of
  `Q_A Q_B` over `(s × s) × (s × s)`, the contraction of the Kronecker sums, and the passage from
  `∫ f²` to the `L²` norm.

## R5 notes

1. Mode index (FD-002). The specification speaks of matrices "indexed by the same finite
   positive-coordinate set". The formalization indexes by an arbitrary finite set `s : Finset ℕ` of
   coordinate indices of `γ₀`, with the positive modes `1, 2, ...` of the node being the intended use,
   and adds no positivity hypothesis. The result therefore holds in particular when every element of
   `s` is at least one. It is also valid for `s` containing `0`: under `γ₀` every coordinate, the
   zeroth included, is a standard Gaussian, so the zero-mode obstruction (which concerns the
   empirical variables `Z_{N,0} = sqrt N`) plays no role here. A matrix `(A_ij)` with `i, j ∈ Fin m`
   indexing positive modes `1..m` is the case `s = Finset.Icc 1 m`, entries read at the source
   coordinate index.
2. Matrices. "Real symmetric finite matrices" are read as arrays `A B : ℕ → ℕ → ℝ`; only their values
   on `s × s` matter and the hypothesis is symmetry on `s × s`:
   `∀ i ∈ s, ∀ j ∈ s, A i j = A j i`. Values off `s × s` are irrelevant to every conclusion.
3. Reference law. `γ₀` is `Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)`, the same measure as in
   LIP051.15, .42 and .43. Coordinates are the evaluations `z ↦ z i`.
4. "Q_A is L2" is stated as `MemLp (Q_A) 2 γ₀`. "Mean zero" is the Bochner integral; it is not a
   vacuous default value since `Q_A` is integrable (a `MemLp … 2` function on a probability space,
   and the integrability of each summand is proved from LIP051.15).
5. The squared norm `‖Q_A - Q_B‖_2^2` is given in two forms: as `∫ (Q_A - Q_B)^2` and as
   `lpNorm (Q_A - Q_B) 2 γ₀ ^ 2`, where `lpNorm … 2` is the `L²(γ₀)` norm of the function.
6. Zero extension of "two differently sized matrices to a common index set" is read as: for finite
   index sets `s ⊆ t`, the array equal to `A` on `s × s` and zero on the rest of `t × t` (written
   `fun i j => if i ∈ s ∧ j ∈ s then A i j else 0`) has the same Wick polynomial over `t` as `A` over
   `s`, pointwise in `z`. Two matrices on `s` and `s'` are extended to `t = s ∪ s'` by applying this
   to each, after which the isometry applies over `t`. Symmetry of the extension on `t × t` follows
   from symmetry of the original on `s × s`.
7. Proof route. Integrability of the monomials `z i * z j` and `z i * z j * z k * z l` comes from the
   integrability conjunct of LIP051.15 (exponent vectors `single i 1 + single j 1 + ...` of total degree
   at most four). `E (z i * z j) = δ_ij` uses the one-coordinate second moment (LIP051.15) for `i = j`
   and the monomial factorization of LIP051.42 for `i ≠ j`. The four-index pairing identity of
   LIP051.15 then gives the entrywise covariance. The file adds no hypotheses beyond the symmetry
   of the two matrices on `s × s` and contains no unproved placeholders.
-/

open MeasureTheory ProbabilityTheory

namespace DGPS.Frontier.LIP051

private noncomputable abbrev gam0_LIP05116 : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)

private lemma sum_add_LIP05116 (f g : ℕ →₀ ℕ) :
    (f + g).sum (fun _ n => n) = f.sum (fun _ n => n) + g.sum (fun _ n => n) :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private lemma sum_single_LIP05116 (a p : ℕ) : (Finsupp.single a p).sum (fun _ n => n) = p :=
  Finsupp.sum_single_index rfl

private lemma prod_add_LIP05116 (f g : ℕ →₀ ℕ) (z : ℕ → ℝ) :
    (f + g).prod (fun i n => z i ^ n) = f.prod (fun i n => z i ^ n) * g.prod (fun i n => z i ^ n) :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

private lemma prod_single_LIP05116 (a p : ℕ) (z : ℕ → ℝ) :
    (Finsupp.single a p).prod (fun i n => z i ^ n) = z a ^ p :=
  Finsupp.prod_single_index (pow_zero _)

private lemma int_mul2_LIP05116 (i j : ℕ) :
    Integrable (fun z : ℕ → ℝ => z i * z j) gam0_LIP05116 := by
  have h := (lip051_15_gaussian_fourth_moments.2.2.2.2 (Finsupp.single i 1 + Finsupp.single j 1)
    (by rw [sum_add_LIP05116, sum_single_LIP05116, sum_single_LIP05116]; norm_num))
  simpa only [prod_add_LIP05116, prod_single_LIP05116, pow_one] using h

private lemma int_mul4_LIP05116 (i j k l : ℕ) :
    Integrable (fun z : ℕ → ℝ => z i * z j * z k * z l) gam0_LIP05116 := by
  have h := (lip051_15_gaussian_fourth_moments.2.2.2.2
    (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 + Finsupp.single l 1)
    (by simp only [sum_add_LIP05116, sum_single_LIP05116]; norm_num))
  simpa only [prod_add_LIP05116, prod_single_LIP05116, pow_one] using h

private lemma mean2_LIP05116 (i j : ℕ) :
    ∫ z : ℕ → ℝ, z i * z j ∂gam0_LIP05116 = if i = j then (1 : ℝ) else 0 := by
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    have := lip051_15_gaussian_fourth_moments.2.1 i
    simpa only [sq] using this
  · simp only [hij, ↓reduceIte]
    have h := (lip051_42_gaussian_monomial_factorization
      (Finsupp.single i 1 + Finsupp.single j 1)
      (by rw [sum_add_LIP05116, sum_single_LIP05116, sum_single_LIP05116]; norm_num)).2.2
    have hd : Disjoint (Finsupp.single i 1).support (Finsupp.single j 1).support := by
      simp [Finsupp.support_single, hij]
    rw [Finsupp.prod_add_index_of_disjoint hd] at h
    simp only [prod_add_LIP05116, prod_single_LIP05116, pow_one] at h
    rw [h]
    simp only [Finsupp.prod_single_index (h := fun _ n => ∫ x : ℝ, x ^ n ∂(gaussianReal 0 1)) (by simp), pow_one]
    simp


/-- The finite Wick quadratic `Q_A(z) = ∑ i ∈ s, ∑ j ∈ s, A i j * (z i * z j - δ_ij)`. -/
noncomputable def wickQuad_LIP05116 (s : Finset ℕ) (A : ℕ → ℕ → ℝ) (z : ℕ → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, A i j * (z i * z j - if i = j then 1 else 0)

private lemma int_q_LIP05116 (i j : ℕ) :
    Integrable (fun z : ℕ → ℝ => z i * z j - if i = j then (1 : ℝ) else 0) gam0_LIP05116 :=
  (int_mul2_LIP05116 i j).sub (integrable_const _)

private lemma int_qq_LIP05116 (i j k l : ℕ) :
    Integrable (fun z : ℕ → ℝ => (z i * z j - if i = j then (1 : ℝ) else 0) *
      (z k * z l - if k = l then (1 : ℝ) else 0)) gam0_LIP05116 := by
  have h : (fun z : ℕ → ℝ => (z i * z j - if i = j then (1 : ℝ) else 0) *
      (z k * z l - if k = l then (1 : ℝ) else 0)) =
      fun z => z i * z j * z k * z l - (if k = l then (1 : ℝ) else 0) * (z i * z j)
        - (if i = j then (1 : ℝ) else 0) * (z k * z l)
        + (if i = j then (1 : ℝ) else 0) * (if k = l then (1 : ℝ) else 0) := by
    funext z; ring
  rw [h]
  exact (((int_mul4_LIP05116 i j k l).sub ((int_mul2_LIP05116 i j).const_mul _)).sub
    ((int_mul2_LIP05116 k l).const_mul _)).add (integrable_const _)

private lemma cov_entry_LIP05116 (i j k l : ℕ) :
    ∫ z : ℕ → ℝ, (z i * z j - if i = j then (1 : ℝ) else 0) *
      (z k * z l - if k = l then (1 : ℝ) else 0) ∂gam0_LIP05116
      = (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        + (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0) := by
  have h : (fun z : ℕ → ℝ => (z i * z j - if i = j then (1 : ℝ) else 0) *
      (z k * z l - if k = l then (1 : ℝ) else 0)) =
      fun z => z i * z j * z k * z l - (if k = l then (1 : ℝ) else 0) * (z i * z j)
        - (if i = j then (1 : ℝ) else 0) * (z k * z l)
        + (if i = j then (1 : ℝ) else 0) * (if k = l then (1 : ℝ) else 0) := by
    funext z; ring
  have h1 : Integrable (fun z : ℕ → ℝ => z i * z j * z k * z l -
      (if k = l then (1 : ℝ) else 0) * (z i * z j)) gam0_LIP05116 :=
    (int_mul4_LIP05116 i j k l).sub ((int_mul2_LIP05116 i j).const_mul _)
  have h2 : Integrable (fun z : ℕ → ℝ => z i * z j * z k * z l -
      (if k = l then (1 : ℝ) else 0) * (z i * z j) -
      (if i = j then (1 : ℝ) else 0) * (z k * z l)) gam0_LIP05116 :=
    h1.sub ((int_mul2_LIP05116 k l).const_mul _)
  rw [h, integral_add h2 (integrable_const _), integral_sub h1 ((int_mul2_LIP05116 k l).const_mul _),
    integral_sub (int_mul4_LIP05116 i j k l) ((int_mul2_LIP05116 i j).const_mul _),
    integral_const_mul, integral_const_mul, integral_const, mean2_LIP05116, mean2_LIP05116,
    lip051_15_gaussian_fourth_moments.2.2.2.1 i j k l]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  ring

private lemma meas_Q_LIP05116 (s : Finset ℕ) (A : ℕ → ℕ → ℝ) :
    Measurable (wickQuad_LIP05116 s A) := by
  unfold wickQuad_LIP05116
  fun_prop

private lemma Q_prod_LIP05116 (s : Finset ℕ) (A : ℕ → ℕ → ℝ) (z : ℕ → ℝ) :
    wickQuad_LIP05116 s A z = ∑ p ∈ s ×ˢ s,
      A p.1 p.2 * (z p.1 * z p.2 - if p.1 = p.2 then (1 : ℝ) else 0) := by
  unfold wickQuad_LIP05116
  rw [Finset.sum_product]

private lemma QQ_expand_LIP05116 (s : Finset ℕ) (A B : ℕ → ℕ → ℝ) (z : ℕ → ℝ) :
    wickQuad_LIP05116 s A z * wickQuad_LIP05116 s B z = ∑ p ∈ s ×ˢ s, ∑ r ∈ s ×ˢ s,
      A p.1 p.2 * B r.1 r.2 *
        ((z p.1 * z p.2 - if p.1 = p.2 then (1 : ℝ) else 0) *
          (z r.1 * z r.2 - if r.1 = r.2 then (1 : ℝ) else 0)) := by
  rw [Q_prod_LIP05116, Q_prod_LIP05116, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  ring

private lemma int_QQ_LIP05116 (s : Finset ℕ) (A B : ℕ → ℕ → ℝ) :
    Integrable (fun z => wickQuad_LIP05116 s A z * wickQuad_LIP05116 s B z) gam0_LIP05116 := by
  simp only [QQ_expand_LIP05116]
  refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun r _ => ?_
  exact (int_qq_LIP05116 p.1 p.2 r.1 r.2).const_mul _

private lemma mean_Q_LIP05116 (s : Finset ℕ) (A : ℕ → ℕ → ℝ) :
    ∫ z, wickQuad_LIP05116 s A z ∂gam0_LIP05116 = 0 := by
  simp only [Q_prod_LIP05116]
  rw [integral_finsetSum _ fun p _ => (int_q_LIP05116 p.1 p.2).const_mul _]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [integral_const_mul, integral_sub (int_mul2_LIP05116 _ _) (integrable_const _),
    mean2_LIP05116]
  simp

private lemma cov_Q_LIP05116 (s : Finset ℕ) (A B : ℕ → ℕ → ℝ) :
    ∫ z, wickQuad_LIP05116 s A z * wickQuad_LIP05116 s B z ∂gam0_LIP05116
      = ∑ i ∈ s, ∑ j ∈ s, (A i j * B i j + A i j * B j i) := by
  simp only [QQ_expand_LIP05116]
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun r _ =>
    (int_qq_LIP05116 p.1 p.2 r.1 r.2).const_mul _]
  have : ∀ p ∈ s ×ˢ s, ∫ z, ∑ r ∈ s ×ˢ s, A p.1 p.2 * B r.1 r.2 *
      ((z p.1 * z p.2 - if p.1 = p.2 then (1 : ℝ) else 0) *
        (z r.1 * z r.2 - if r.1 = r.2 then (1 : ℝ) else 0)) ∂gam0_LIP05116
      = A p.1 p.2 * B p.1 p.2 + A p.1 p.2 * B p.2 p.1 := by
    intro p hp
    rw [integral_finsetSum _ fun r _ => (int_qq_LIP05116 p.1 p.2 r.1 r.2).const_mul _]
    simp only [integral_const_mul, cov_entry_LIP05116]
    obtain ⟨p1, p2⟩ := p
    have hp' : (p2, p1) ∈ s ×ˢ s := by
      simp only [Finset.mem_product] at hp ⊢
      exact ⟨hp.2, hp.1⟩
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single (p1, p2)]
      · simp
      · intro x _ hx
        obtain ⟨x1, x2⟩ := x
        by_cases h1 : p1 = x1
        · have h2 : p2 ≠ x2 := fun h2 => hx (by rw [← h1, ← h2])
          simp [h2]
        · simp [h1]
      · intro h; exact absurd hp h
    · rw [Finset.sum_eq_single (p2, p1)]
      · simp
      · intro x _ hx
        obtain ⟨x1, x2⟩ := x
        by_cases h1 : p1 = x2
        · have h2 : p2 ≠ x1 := fun h2 => hx (by rw [← h1, ← h2])
          simp [h2]
        · simp [h1]
      · intro h; exact absurd hp' h
  rw [Finset.sum_congr rfl this, Finset.sum_product]


private lemma cov_sym_LIP05116 (s : Finset ℕ) (A B : ℕ → ℕ → ℝ)
    (hA : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i) :
    ∑ i ∈ s, ∑ j ∈ s, (A i j * B i j + A i j * B j i) = 2 * ∑ i ∈ s, ∑ j ∈ s, A i j * B i j := by
  have h2 : ∑ i ∈ s, ∑ j ∈ s, A i j * B j i = ∑ i ∈ s, ∑ j ∈ s, A i j * B i j := by
    calc ∑ i ∈ s, ∑ j ∈ s, A i j * B j i = ∑ i ∈ s, ∑ j ∈ s, A j i * B j i :=
          Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [hA i hi j hj]
      _ = ∑ i ∈ s, ∑ j ∈ s, A i j * B i j := Finset.sum_comm
  simp only [Finset.sum_add_distrib, h2]
  ring

private lemma Q_sub_LIP05116 (s : Finset ℕ) (A B : ℕ → ℕ → ℝ) (z : ℕ → ℝ) :
    wickQuad_LIP05116 s A z - wickQuad_LIP05116 s B z
      = wickQuad_LIP05116 s (fun i j => A i j - B i j) z := by
  unfold wickQuad_LIP05116
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma Q_ext_LIP05116 (s t : Finset ℕ) (hst : s ⊆ t) (A : ℕ → ℕ → ℝ) (z : ℕ → ℝ) :
    wickQuad_LIP05116 t (fun i j => if i ∈ s ∧ j ∈ s then A i j else 0) z
      = wickQuad_LIP05116 s A z := by
  unfold wickQuad_LIP05116
  rw [← Finset.sum_subset hst (fun i _ hi => by simp [hi])]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_subset hst (fun j _ hj => by simp [hj])]
  exact Finset.sum_congr rfl fun j hj => by simp [hi, hj]

private lemma memLp_Q_LIP05116 (s : Finset ℕ) (A : ℕ → ℕ → ℝ) :
    MemLp (wickQuad_LIP05116 s A) 2 gam0_LIP05116 := by
  rw [memLp_two_iff_integrable_sq (meas_Q_LIP05116 s A).aestronglyMeasurable]
  simpa only [sq] using int_QQ_LIP05116 s A A

private lemma lpNorm_sq_LIP05116 (f : (ℕ → ℝ) → ℝ) (hf : Measurable f) :
    lpNorm f 2 gam0_LIP05116 ^ 2 = ∫ z, f z ^ 2 ∂gam0_LIP05116 := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  have h0 : 0 ≤ ∫ z, ‖f z‖ ^ (ENNReal.toReal 2) ∂gam0_LIP05116 :=
    integral_nonneg fun z => by positivity
  have h2 : ENNReal.toReal 2 = ((2 : ℕ) : ℝ) := by simp
  rw [h2] at h0 ⊢
  rw [Real.rpow_inv_natCast_pow (n := 2) h0 (by norm_num)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Real.rpow_natCast, Real.norm_eq_abs, sq_abs]

/-- **LIP051.16.** Finite Wick isometry for the reference product law
`γ₀ = Measure.infinitePi (fun _ => N(0,1))`. For a finite index set `s` and matrices `A B` that are
symmetric on `s × s`, with `Q_A = ∑ i ∈ s, ∑ j ∈ s, A i j * (z i * z j - δ_ij)`: both `Q_A`, `Q_B`
are in `L²(γ₀)` with mean zero; `E (Q_A Q_B) = 2 ∑ A_ij B_ij`; `‖Q_A - Q_B‖₂² = 2 ∑ (A_ij - B_ij)²`
(stated for the `L²` norm `lpNorm … 2` and for `∫ (Q_A - Q_B)²`); and zero extension of a matrix
from `s` to any `t ⊇ s` leaves the Wick polynomial unchanged. -/
theorem lip051_16_finite_wick_isometry (s : Finset ℕ) (A B : ℕ → ℕ → ℝ)
    (hA : ∀ i ∈ s, ∀ j ∈ s, A i j = A j i) (hB : ∀ i ∈ s, ∀ j ∈ s, B i j = B j i) :
    MemLp (wickQuad_LIP05116 s A) 2 (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) ∧
    MemLp (wickQuad_LIP05116 s B) 2 (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) ∧
    (∫ z, wickQuad_LIP05116 s A z ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))) = 0 ∧
    (∫ z, wickQuad_LIP05116 s B z ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))) = 0 ∧
    (∫ z, wickQuad_LIP05116 s A z * wickQuad_LIP05116 s B z
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)))
      = 2 * ∑ i ∈ s, ∑ j ∈ s, A i j * B i j ∧
    (∫ z, (wickQuad_LIP05116 s A z - wickQuad_LIP05116 s B z) ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)))
      = 2 * ∑ i ∈ s, ∑ j ∈ s, (A i j - B i j) ^ 2 ∧
    lpNorm (fun z => wickQuad_LIP05116 s A z - wickQuad_LIP05116 s B z) 2
        (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) ^ 2
      = 2 * ∑ i ∈ s, ∑ j ∈ s, (A i j - B i j) ^ 2 ∧
    (∀ t : Finset ℕ, s ⊆ t → ∀ z : ℕ → ℝ,
      wickQuad_LIP05116 t (fun i j => if i ∈ s ∧ j ∈ s then A i j else 0) z
        = wickQuad_LIP05116 s A z) := by
  have hC : ∀ i ∈ s, ∀ j ∈ s, (A i j - B i j) = (A j i - B j i) := fun i hi j hj => by
    rw [hA i hi j hj, hB i hi j hj]
  have hdiff : ∫ z, (wickQuad_LIP05116 s A z - wickQuad_LIP05116 s B z) ^ 2 ∂gam0_LIP05116
      = 2 * ∑ i ∈ s, ∑ j ∈ s, (A i j - B i j) ^ 2 := by
    simp only [Q_sub_LIP05116, sq]
    rw [cov_Q_LIP05116, cov_sym_LIP05116 s _ _ hC]
  refine ⟨memLp_Q_LIP05116 s A, memLp_Q_LIP05116 s B, mean_Q_LIP05116 s A, mean_Q_LIP05116 s B,
    ?_, hdiff, ?_, fun t hst z => Q_ext_LIP05116 s t hst A z⟩
  · rw [cov_Q_LIP05116, cov_sym_LIP05116 s _ _ hA]
  · have hm : Measurable (fun z => wickQuad_LIP05116 s A z - wickQuad_LIP05116 s B z) :=
      (meas_Q_LIP05116 s A).sub (meas_Q_LIP05116 s B)
    rw [lpNorm_sq_LIP05116 _ hm]
    exact hdiff

end DGPS.Frontier.LIP051
