import DGPS.Frontier.LIP051.T41
import DGPS.Frontier.LIP051.T42

/-!
# LIP051.43: Gaussian fourth-moment pairing identity

Task id `LIP051.43`, title "Gaussian fourth-moment pairing identity" (node LIP051, "Joint Gaussian
and quadratic fluctuation limit", category leaf formalization, verification V1).

## Provides

* `DGPS.Frontier.LIP051.lip051_43_gaussian_fourth_moment_pairing_identity`: for all natural
  indices `i j k l`, under `γ₀ = Measure.infinitePi (fun _ => gaussianReal 0 1)` on `ℕ → ℝ`,
  `∫ z i * z j * z k * z l dγ₀ = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk`, with the Kronecker symbols
  written as `if a = b then 1 else 0`.
* Helpers (all suffixed `_LIP05143`), not intended for use outside this file: the scalar moments
  `mom_zero/one/two/four_LIP05143` (from LIP051.41); `prod_add_zfn_LIP05143` and
  `prod_single_zfn_LIP05143` (the coordinate monomial `f.prod (fun i n => z i ^ n)` is additive
  in `f`, and a single is `z a ^ p`); `sum_add_LIP05143` and `sum_single_LIP05143` (total
  degree); `prod_disjoint_mom_LIP05143` (a product over `f1 + f2` with disjoint supports splits);
  `sep_LIP05143` (`E[z_a ^ p * g-monomial] = E[z_a ^ p] * ∏ moments` when `g a = 0`, derived from
  the LIP051.42 monomial factorization); `pair_LIP05143` (two distinct coordinates);
  `single_zero_LIP05143` (a coordinate occurring exactly once gives zero).

## R5 notes

1. Indexing (FD-002). The statement quantifies over all `i j k l : ℕ`, index zero included, as
   written in the specification. It concerns the reference law `γ₀` itself, a product of standard
   Gaussians in every coordinate, not a finite-`N` fluctuation `Z_{N,0}`. The zero-mode obstruction
   (`Z_{N,0} = sqrt N` almost surely) therefore does not arise, and no positive-mode restriction is
   added or dropped. The positive-mode convention matters only for the convergence statement of
   the node, not for this identity.
2. Measure and coordinates. `γ₀` is `Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)`, the same
   measure as in LIP051.42, and the coordinate maps are the evaluations `z ↦ z i`.
3. Kronecker symbols are read as `(if a = b then (1 : ℝ) else 0)` and multiplied and summed in
   `ℝ`, exactly as the three-term right-hand side of the specification.
4. Proof route. The equality pattern of `(i, j, k, l)` is split into cases. If some index differs
   from the other three, that coordinate enters with exponent one and the factor `E[z ^ 1]` vanishes
   (LIP051.41), so the left side is zero; the right side is zero too, since each Kronecker product
   contains an unequal pair. Otherwise every index has a partner: either all four coincide (the
   fourth moment `3`), or the indices form two distinct pairs (the product of two second moments,
   `1`). The factorization is LIP051.42 applied to a finitely supported exponent vector; the
   LIP051.37 block route is not used.
5. Hypotheses. None are added: the statement is the frozen three-term identity with no extra
   assumptions, and the file carries no unproved placeholders and no extra declarations.
-/

open MeasureTheory ProbabilityTheory

namespace DGPS.Frontier.LIP051

private lemma mom_zero_LIP05143 : ∫ x : ℝ, x ^ 0 ∂(gaussianReal 0 1) = 1 := by simp

private lemma mom_one_LIP05143 : ∫ x : ℝ, x ^ 1 ∂(gaussianReal 0 1) = 0 := by
  simp

private lemma mom_two_LIP05143 : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 :=
  (lip051_41_exact_scalar_gaussian_fourth_moment).2.1

private lemma mom_four_LIP05143 : ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1) = 3 :=
  (lip051_41_exact_scalar_gaussian_fourth_moment).2.2.2.1

private lemma prod_add_zfn_LIP05143 (f g : ℕ →₀ ℕ) (z : ℕ → ℝ) :
    (f + g).prod (fun i n => z i ^ n) = f.prod (fun i n => z i ^ n) * g.prod (fun i n => z i ^ n) :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

private lemma prod_single_zfn_LIP05143 (a p : ℕ) (z : ℕ → ℝ) :
    (Finsupp.single a p).prod (fun i n => z i ^ n) = z a ^ p :=
  Finsupp.prod_single_index (pow_zero _)

private lemma sum_add_LIP05143 (f g : ℕ →₀ ℕ) :
    (f + g).sum (fun _ n => n) = f.sum (fun _ n => n) + g.sum (fun _ n => n) :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private lemma sum_single_LIP05143 (a p : ℕ) : (Finsupp.single a p).sum (fun _ n => n) = p :=
  Finsupp.sum_single_index rfl

/-- Product of coordinatewise moments with disjoint support. -/
private lemma prod_disjoint_mom_LIP05143 (a p : ℕ) (g : ℕ →₀ ℕ) (hg : g a = 0) (m : ℕ → ℝ)
    (hm0 : m 0 = 1) :
    (Finsupp.single a p + g).prod (fun _ n => m n) = m p * g.prod (fun _ n => m n) := by
  have hd : Disjoint (Finsupp.single a p).support g.support :=
    Finset.disjoint_of_subset_left Finsupp.support_single_subset
      (Finset.disjoint_singleton_left.2 (Finsupp.notMem_support_iff.2 hg))
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_single_index hm0]

private lemma sep_LIP05143 (a p : ℕ) (g : ℕ →₀ ℕ) (hg : g a = 0)
    (hdeg : p + g.sum (fun _ n => n) ≤ 4) :
    ∫ z : ℕ → ℝ, z a ^ p * g.prod (fun i n => z i ^ n)
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
      = (∫ x : ℝ, x ^ p ∂(gaussianReal 0 1)) *
          g.prod (fun _ n => ∫ x : ℝ, x ^ n ∂(gaussianReal 0 1)) := by
  have hdeg' : (Finsupp.single a p + g).sum (fun _ n => n) ≤ 4 := by
    rw [sum_add_LIP05143, sum_single_LIP05143]
    exact hdeg
  have hT := (lip051_42_gaussian_monomial_factorization _ hdeg').2.2
  have hpt : ∀ z : ℕ → ℝ, (Finsupp.single a p + g).prod (fun i n => z i ^ n)
      = z a ^ p * g.prod (fun i n => z i ^ n) := fun z => by
    rw [prod_add_zfn_LIP05143, prod_single_zfn_LIP05143]
  have hm : (Finsupp.single a p + g).prod (fun _ n => ∫ x : ℝ, x ^ n ∂(gaussianReal 0 1))
      = (∫ x : ℝ, x ^ p ∂(gaussianReal 0 1)) *
          g.prod (fun _ n => ∫ x : ℝ, x ^ n ∂(gaussianReal 0 1)) :=
    prod_disjoint_mom_LIP05143 a p g hg (fun n => ∫ x : ℝ, x ^ n ∂(gaussianReal 0 1))
      mom_zero_LIP05143
  simp only [hpt] at hT
  rw [hT, hm]

private lemma pair_LIP05143 (a c : ℕ) (hac : a ≠ c) (p q : ℕ) (hpq : p + q ≤ 4) :
    ∫ z : ℕ → ℝ, z a ^ p * z c ^ q ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
      = (∫ x : ℝ, x ^ p ∂(gaussianReal 0 1)) * (∫ x : ℝ, x ^ q ∂(gaussianReal 0 1)) := by
  have hg : (Finsupp.single c q : ℕ →₀ ℕ) a = 0 := by
    simp [Ne.symm hac]
  have h := sep_LIP05143 a p (Finsupp.single c q) hg (by rw [sum_single_LIP05143]; exact hpq)
  simp only [prod_single_zfn_LIP05143] at h
  rw [h, Finsupp.prod_single_index mom_zero_LIP05143]

private lemma single_zero_LIP05143 (a b c d : ℕ) (hb : a ≠ b) (hc : a ≠ c) (hd : a ≠ d) :
    ∫ z : ℕ → ℝ, z a * z b * z c * z d
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) = 0 := by
  have hg : (Finsupp.single b 1 + Finsupp.single c 1 + Finsupp.single d 1 : ℕ →₀ ℕ) a = 0 := by
    simp [Ne.symm hb, Ne.symm hc, Ne.symm hd]
  have hint : ∀ z : ℕ → ℝ, z a * z b * z c * z d = z a ^ 1 *
      (Finsupp.single b 1 + Finsupp.single c 1 + Finsupp.single d 1).prod
        (fun i n => z i ^ n) := fun z => by
    rw [prod_add_zfn_LIP05143, prod_add_zfn_LIP05143, prod_single_zfn_LIP05143,
      prod_single_zfn_LIP05143, prod_single_zfn_LIP05143]
    ring
  simp only [hint]
  rw [sep_LIP05143 a 1 _ hg (by simp only [sum_add_LIP05143, sum_single_LIP05143]; omega),
    mom_one_LIP05143, zero_mul]


/-- The main identity. -/
theorem lip051_43_gaussian_fourth_moment_pairing_identity (i j k l : ℕ) :
    ∫ z : ℕ → ℝ, z i * z j * z k * z l
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
      = (if i = j then (1 : ℝ) else 0) * (if k = l then (1 : ℝ) else 0)
        + (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        + (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0) := by
  by_cases h1 : i ≠ j ∧ i ≠ k ∧ i ≠ l
  · obtain ⟨hj, hk, hl⟩ := h1
    rw [single_zero_LIP05143 i j k l hj hk hl]
    simp [hj, hk, hl]
  by_cases h2 : j ≠ i ∧ j ≠ k ∧ j ≠ l
  · obtain ⟨hi, hk, hl⟩ := h2
    have e : ∫ z : ℕ → ℝ, z i * z j * z k * z l
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
        = ∫ z : ℕ → ℝ, z j * z i * z k * z l
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) := by
      congr 1; funext z; ring
    rw [e, single_zero_LIP05143 j i k l hi hk hl]
    simp [Ne.symm hi, hk, hl]
  by_cases h3 : k ≠ i ∧ k ≠ j ∧ k ≠ l
  · obtain ⟨hi, hj, hl⟩ := h3
    have e : ∫ z : ℕ → ℝ, z i * z j * z k * z l
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
        = ∫ z : ℕ → ℝ, z k * z i * z j * z l
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) := by
      congr 1; funext z; ring
    rw [e, single_zero_LIP05143 k i j l hi hj hl]
    simp [Ne.symm hi, hl, Ne.symm hj]
  by_cases h4 : l ≠ i ∧ l ≠ j ∧ l ≠ k
  · obtain ⟨hi, hj, hk⟩ := h4
    have e : ∫ z : ℕ → ℝ, z i * z j * z k * z l
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1))
        = ∫ z : ℕ → ℝ, z l * z i * z j * z k
        ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) := by
      congr 1; funext z; ring
    rw [e, single_zero_LIP05143 l i j k hi hj hk]
    simp [Ne.symm hk, Ne.symm hj, Ne.symm hi]
  have p1 : i = j ∨ i = k ∨ i = l := by omega
  have p2 : j = i ∨ j = k ∨ j = l := by omega
  have p3 : k = i ∨ k = j ∨ k = l := by omega
  have p4 : l = i ∨ l = j ∨ l = k := by omega
  by_cases e1 : i = j
  · by_cases e2 : k = l
    · subst e1 e2
      by_cases e3 : i = k
      · subst e3
        have e : ∀ z : ℕ → ℝ, z i * z i * z i * z i = z i ^ 4 *
            (0 : ℕ →₀ ℕ).prod (fun m n => z m ^ n) := fun z => by
          simp only [Finsupp.prod_zero_index, mul_one]; ring
        simp only [e]
        rw [sep_LIP05143 i 4 0 (by simp) (by simp), mom_four_LIP05143, Finsupp.prod_zero_index]
        norm_num
      · have e : ∀ z : ℕ → ℝ, z i * z i * z k * z k = z i ^ 2 * z k ^ 2 :=
          fun z => by ring
        simp only [e]
        rw [pair_LIP05143 i k e3 2 2 (by norm_num), mom_two_LIP05143]
        simp [e3]
    · exfalso
      omega
  · by_cases e2 : k = l
    · exfalso
      omega
    · by_cases e3 : i = k
      · subst e3
        have e4 : j = l := by omega
        subst e4
        have e : ∀ z : ℕ → ℝ, z i * z j * z i * z j = z i ^ 2 * z j ^ 2 :=
          fun z => by ring
        simp only [e]
        rw [pair_LIP05143 i j e1 2 2 (by norm_num), mom_two_LIP05143]
        simp [e1]
      · have e4 : j = k := by omega
        have e5 : i = l := by omega
        subst e4 e5
        have e : ∀ z : ℕ → ℝ, z i * z j * z j * z i = z i ^ 2 * z j ^ 2 :=
          fun z => by ring
        simp only [e]
        rw [pair_LIP05143 i j e1 2 2 (by norm_num), mom_two_LIP05143]
        simp [e1]

end DGPS.Frontier.LIP051
