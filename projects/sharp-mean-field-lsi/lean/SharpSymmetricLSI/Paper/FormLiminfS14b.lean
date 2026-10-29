import SharpSymmetricLSI.Paper.FormLiminfS14a
import SharpSymmetricLSI.Paper.FormLiminfS12

/-!
# R33 cross term (S14b): the test functions `H_R` and the Gaussian side

For a cylinder `c` and finite-rank data `(s, a)`:
* `crossH1 lam c w = ∑_i λ'_i (w_i ∂_iφ(w) - ∂_i∂_iφ(w))` (the diagonal part of `genL`);
* `crossH2 lam c s a w zq = ∑_i ∂_iφ(w) ∑_{p,q∈s} a_{pq} zq_q [p = i] λ'_i` (the finite-rank force);
* `crossH lam c s a h w'` on `ℝ^{J'}` (`J ≤ J'`, `s ⊆ [0,J')`): both, through the projection.
`crossH` is continuous with linear growth (`continuous_crossH`, `crossH_growth`).
`neg_gen_eq` is the identity `-L_∞φ = ∑ λ'_i [(z_i + Y_i)∂_iφ - ∂_i∂_iφ]`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace SharpLSI

variable {d : ℕ}

/-- The first `J` coordinates of a vector in `ℝ^{J'}`. -/
def projJ {J J' : ℕ} (h : J ≤ J') (w : Fin J' → ℝ) : Fin J → ℝ := fun i => w (Fin.castLE h i)

/-- A vector in `ℝ^{J'}` as a sequence (zero beyond `J'`). -/
def extN {J' : ℕ} (w : Fin J' → ℝ) (q : ℕ) : ℝ := if h : q < J' then w ⟨q, h⟩ else 0

/-- The diagonal part of the generator. -/
noncomputable def crossH1 (lam : ℕ → ℝ) (c : Cyl) (w : Fin c.J → ℝ) : ℝ :=
  ∑ i : Fin c.J, lamShift lam i * (w i * cylD c i w - fderiv ℝ (cylD c i) w (Pi.single i 1))

/-- The finite-rank force part of the generator. -/
noncomputable def crossH2 (lam : ℕ → ℝ) (c : Cyl) (s : Finset ℕ) (a : ℕ → ℕ → ℝ)
    (w : Fin c.J → ℝ) (zq : ℕ → ℝ) : ℝ :=
  ∑ i : Fin c.J, cylD c i w * ∑ p ∈ s, ∑ q ∈ s, a p q * zq q *
    (if p = (i : ℕ) then lamShift lam i else 0)

/-- The test function of the main part. -/
noncomputable def crossH (lam : ℕ → ℝ) (c : Cyl) (s : Finset ℕ) (a : ℕ → ℕ → ℝ) {J' : ℕ}
    (h : c.J ≤ J') (w : Fin J' → ℝ) : ℝ :=
  crossH1 lam c (projJ h w) + crossH2 lam c s a (projJ h w) (extN w)

theorem continuous_projJ {J J' : ℕ} (h : J ≤ J') : Continuous (projJ h) :=
  continuous_pi fun i => continuous_apply _

theorem continuous_extN_apply {J' : ℕ} (q : ℕ) : Continuous fun w : Fin J' → ℝ => extN w q := by
  unfold extN
  by_cases h : q < J'
  · simp only [h, dite_true]; exact continuous_apply _
  · simp only [h, dite_false]; exact continuous_const

theorem continuous_crossH1 (lam : ℕ → ℝ) (c : Cyl) : Continuous (crossH1 lam c) := by
  unfold crossH1
  refine continuous_finset_sum _ fun i _ => continuous_const.mul ?_
  exact ((continuous_apply i).mul (contDiff_cylD c i).continuous).sub
    (((contDiff_cylD c i).continuous_fderiv one_ne_zero).clm_apply continuous_const)

theorem continuous_crossH (lam : ℕ → ℝ) (c : Cyl) (s : Finset ℕ) (a : ℕ → ℕ → ℝ) {J' : ℕ}
    (h : c.J ≤ J') : Continuous (crossH lam c s a h) := by
  unfold crossH crossH2
  refine ((continuous_crossH1 lam c).comp (continuous_projJ h)).add ?_
  refine continuous_finset_sum _ fun i _ =>
    ((contDiff_cylD c i).continuous.comp (continuous_projJ h)).mul ?_
  exact continuous_finset_sum _ fun p _ => continuous_finset_sum _ fun q _ =>
    (continuous_const.mul (continuous_extN_apply q)).mul continuous_const

theorem abs_extN_le {J' : ℕ} (w : Fin J' → ℝ) (q : ℕ) : |extN w q| ≤ ∑ j, |w j| := by
  unfold extN
  split_ifs with h
  · exact Finset.single_le_sum (f := fun j => |w j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ (⟨q, h⟩ : Fin J'))
  · simpa using Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => abs_nonneg (w j)

theorem sum_abs_projJ_le {J J' : ℕ} (h : J ≤ J') (w : Fin J' → ℝ) :
    ∑ i, |projJ h w i| ≤ ∑ j, |w j| := by
  unfold projJ
  have hinj : Function.Injective (Fin.castLE h) := Fin.castLE_injective h
  calc ∑ i, |w (Fin.castLE h i)| = ∑ j ∈ Finset.univ.map ⟨_, hinj⟩, |w j| := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ j, |w j| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun _ _ _ => abs_nonneg _

/-- **Linear growth of the test function.** -/
theorem crossH_growth (lam : ℕ → ℝ) (c : Cyl) (s : Finset ℕ) (a : ℕ → ℕ → ℝ) {J' : ℕ}
    (h : c.J ≤ J') : ∃ A, ∀ w, |crossH lam c s a h w| ≤ A * (1 + ∑ j, |w j|) := by
  have hK : ∀ i : Fin c.J, ∃ K, 0 ≤ K ∧ ∀ z, |cylD c i z| ≤ K := fun i =>
    exists_bound_of_compact (contDiff_cylD c i).continuous (hasCompactSupport_cylD c i)
  choose K hK0 hK using hK
  have hD : ∀ i : Fin c.J, ∃ K, 0 ≤ K ∧ ∀ z (j : Fin c.J), |fderiv ℝ (cylD c i) z (Pi.single j 1)| ≤ K :=
    fun i => exists_bound_fderiv_of (contDiff_cylD c i) (hasCompactSupport_cylD c i)
  choose D hD0 hD using hD
  set L : ℝ := ∑ i : Fin c.J, |lamShift lam i|
  set Ks : ℝ := ∑ i : Fin c.J, (K i + D i)
  set Aa : ℝ := ∑ p ∈ s, ∑ q ∈ s, |a p q|
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun i _ => add_nonneg (hK0 i) (hD0 i)
  have hAa0 : 0 ≤ Aa := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨L * Ks + Ks * Aa * L, fun w => ?_⟩
  set S := ∑ j, |w j|
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hpw : ∀ i, |projJ h w i| ≤ S := fun i =>
    (Finset.single_le_sum (f := fun i => |projJ h w i|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ i)).trans (sum_abs_projJ_le h w)
  -- the first part
  have h1 : |crossH1 lam c (projJ h w)| ≤ L * Ks * (1 + S) := by
    unfold crossH1
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin c.J, |lamShift lam i * (projJ h w i * cylD c i (projJ h w) -
          fderiv ℝ (cylD c i) (projJ h w) (Pi.single i 1))|
        ≤ ∑ i : Fin c.J, |lamShift lam i| * (Ks * (1 + S)) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (abs_sub _ _).trans ?_
          rw [abs_mul]
          have hKi : K i + D i ≤ Ks := Finset.single_le_sum (f := fun i => K i + D i)
            (fun i _ => add_nonneg (hK0 i) (hD0 i)) (Finset.mem_univ i)
          have := hK i (projJ h w); have := hD i (projJ h w) i; have := hpw i
          nlinarith [abs_nonneg (projJ h w i), abs_nonneg (cylD c i (projJ h w)), hK0 i, hD0 i]
      _ = L * Ks * (1 + S) := by rw [← Finset.sum_mul]; ring
  -- the second part
  have h2 : |crossH2 lam c s a (projJ h w) (extN w)| ≤ Ks * Aa * L * (1 + S) := by
    unfold crossH2
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin c.J, |cylD c i (projJ h w) * ∑ p ∈ s, ∑ q ∈ s, a p q * extN w q *
          (if p = (i : ℕ) then lamShift lam i else 0)|
        ≤ ∑ i : Fin c.J, K i * (Aa * (S * L)) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          refine mul_le_mul (hK i _) ?_ (abs_nonneg _) (hK0 i)
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun p _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun q _ => ?_
          rw [abs_mul, abs_mul]
          have hite : |(if p = (i : ℕ) then lamShift lam i else 0)| ≤ L := by
            split_ifs
            · exact Finset.single_le_sum (f := fun i : Fin c.J => |lamShift lam i|)
                (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
            · simpa using hL0
          have := abs_extN_le w q
          calc |a p q| * |extN w q| * |(if p = (i : ℕ) then lamShift lam i else 0)|
              ≤ |a p q| * S * L := mul_le_mul (mul_le_mul_of_nonneg_left this (abs_nonneg _))
                hite (abs_nonneg _) (mul_nonneg (abs_nonneg _) hS0)
            _ = |a p q| * (S * L) := by ring
      _ ≤ Ks * Aa * L * (1 + S) := by
          rw [← Finset.sum_mul]
          have hKK : ∑ i : Fin c.J, K i ≤ Ks :=
            Finset.sum_le_sum fun i _ => le_add_of_nonneg_right (hD0 i)
          have := mul_le_mul_of_nonneg_right hKK (mul_nonneg hAa0 (mul_nonneg hS0 hL0))
          nlinarith [mul_nonneg (mul_nonneg hKs0 hAa0) hL0]
  unfold crossH
  calc |crossH1 lam c (projJ h w) + crossH2 lam c s a (projJ h w) (extN w)|
      ≤ L * Ks * (1 + S) + Ks * Aa * L * (1 + S) := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = (L * Ks + Ks * Aa * L) * (1 + S) := by ring

/-- **`-L_∞φ = ∑ λ'_i [(z_i + Y_i)∂_iφ - ∂_i∂_iφ]`.** -/
theorem neg_gen_eq (lam : ℕ → ℝ) (c : Cyl) (Y : ℕ → (ℕ → ℝ) → ℝ) (z : ℕ → ℝ) :
    -(c.gen (lamShift lam) Y z) = crossH1 lam c (fun j => z j) +
      ∑ i : Fin c.J, (lamShift lam i * cylD c i (fun j => z j)) * Y i z := by
  unfold Cyl.gen crossH1
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : cylD c i = fun x => fderiv ℝ c.φ x (Pi.single i 1) := rfl
  rw [hc]
  ring

end SharpLSI
