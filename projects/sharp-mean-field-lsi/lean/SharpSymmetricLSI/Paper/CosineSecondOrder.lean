import SharpSymmetricLSI.Paper.CosineBochner

/-!
# Lemma 3.7, (3.34): the second-order inequality (Phase 3, lane C)

Route of the manuscript: the integrated Bochner formula (`bochner`), the off-diagonal bound
(3.36) on the lift (`offdiag_lift`), and the diagonal term (3.40) by Fubini along the coordinate
`x_j` and the one-dimensional inequality (`diag_integrated`), with oscillation `≤ 2κ` of `U_N`
along each fibre (`osc_UL`).
-/

open MeasureTheory Set Filter
open scoped Real ContDiff

namespace SharpLSI

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal term (3.40), integrated over the fibres of the coordinate `p`. -/
theorem diag_integrated {g h : (ι → ℝ) → ℝ} (hg : SmPer g) (hh : SmPer h) (p : ι) {κ' : ℝ}
    (hosc : ∀ a b b', h (mergeR p a b) - h (mergeR p a b') ≤ κ') :
    4 * π ^ 2 * Real.exp (-κ') * ∫ y, Real.exp (-h (secT y)) * Dk g p (secT y) ^ 2 ≤
      ∫ y, Real.exp (-h (secT y)) * (Dk (Dk g p) p (secT y) ^ 2 +
        Dk (Dk h p) p (secT y) * Dk g p (secT y) ^ 2) := by
  have i1 := (hh.expNeg.mul ((hg.Dk p).mul (hg.Dk p))).integrable
  have i2 := (hh.expNeg.mul ((((hg.Dk p).Dk p).mul ((hg.Dk p).Dk p)).add
    (((hh.Dk p).Dk p).mul ((hg.Dk p).mul (hg.Dk p))))).integrable
  have e1 : (fun y => Real.exp (-h (secT y)) * Dk g p (secT y) ^ 2) =
      fun y => Real.exp (-h (secT y)) * (Dk g p (secT y) * Dk g p (secT y)) := by
    funext y; ring
  have e2 : (fun y => Real.exp (-h (secT y)) * (Dk (Dk g p) p (secT y) ^ 2 +
      Dk (Dk h p) p (secT y) * Dk g p (secT y) ^ 2)) = fun y => Real.exp (-h (secT y)) *
      (Dk (Dk g p) p (secT y) * Dk (Dk g p) p (secT y) +
        Dk (Dk h p) p (secT y) * (Dk g p (secT y) * Dk g p (secT y))) := by
    funext y; ring
  rw [e1, e2, integral_split (p := p) i1, integral_split (p := p) i2, ← integral_const_mul]
  refine integral_mono ((integrable_split (p := p) i1).const_mul _) (integrable_split (p := p) i2)
    fun a => ?_
  simp only [secT_split]
  set xa := secT a
  have hd : ∀ {Φ : (ι → ℝ) → ℝ}, SmPer Φ → Differentiable ℝ Φ := fun hΦ =>
    hΦ.1.differentiable (by simp)
  have hu : ContDiff ℝ ∞ (fun b => g (mergeR p xa b)) := hg.1.comp (contDiff_mergeR xa)
  have hψ : ContDiff ℝ ∞ (fun b => h (mergeR p xa b)) := hh.1.comp (contDiff_mergeR xa)
  have h1 := diag_1d hu hψ (hg.2.fiber xa) (hh.2.fiber xa) (fun b b' => hosc xa b b')
  have fu : Dk (fun b => g (mergeR p xa b)) default = fun b => Dk g p (mergeR p xa b) :=
    funext (Dk_fiber (hd hg) xa)
  have fψ : Dk (fun b => h (mergeR p xa b)) default = fun b => Dk h p (mergeR p xa b) :=
    funext (Dk_fiber (hd hh) xa)
  rw [fu, fψ] at h1
  simp only [Dk_fiber (hd (hg.Dk p)) xa, Dk_fiber (hd (hh.Dk p)) xa] at h1
  convert h1 using 2
  · congr 1; funext b; ring
  · congr 1; funext b; ring

end Generic

section Cosine

variable {N : ℕ}

/-- `U_N` oscillates by at most `2κ` along the coordinate `x_j`. -/
theorem osc_UL {κ : ℝ} (hκ : 0 ≤ κ) (j : Fin N) {x x' : Fin N × Fin 1 → ℝ}
    (hx : ∀ l, l ≠ j → x (l, 0) = x' (l, 0)) : UL κ N x - UL κ N x' ≤ 2 * κ := by
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact j.elim0)
  set s := Finset.univ.erase j with hs
  have hθ : ∀ l ∈ s, thetaC x l = thetaC x' l := fun l hl => by
    simp only [thetaC, hx l (Finset.ne_of_mem_erase hl)]
  set C' := ∑ l ∈ s, Real.cos (thetaC x l)
  set S' := ∑ l ∈ s, Real.sin (thetaC x l)
  have hC : sumCos x = Real.cos (thetaC x j) + C' :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hS : sumSin x = Real.sin (thetaC x j) + S' :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
  have hC' : sumCos x' = Real.cos (thetaC x' j) + C' := by
    rw [sumCos, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1; exact Finset.sum_congr rfl fun l hl => by rw [hθ l hl]
  have hS' : sumSin x' = Real.sin (thetaC x' j) + S' := by
    rw [sumSin, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1; exact Finset.sum_congr rfl fun l hl => by rw [hθ l hl]
  have hcard : (s.card : ℝ) = N - 1 := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hN, Nat.cast_one]
  have hR : C' ^ 2 + S' ^ 2 ≤ ((N : ℝ) - 1) ^ 2 := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun l => Real.cos (thetaC x l))
    have h2 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun l => Real.sin (thetaC x l))
    have h3 : ∑ l ∈ s, Real.cos (thetaC x l) ^ 2 + ∑ l ∈ s, Real.sin (thetaC x l) ^ 2 =
        s.card := by
      rw [← Finset.sum_add_distrib]
      simp only [Real.cos_sq_add_sin_sq, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard] at h1 h2 h3
    nlinarith
  have hN1 : (0 : ℝ) ≤ N - 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hbound : ∀ θ : ℝ, |C' * Real.cos θ + S' * Real.sin θ| ≤ N - 1 := by
    intro θ
    have h4 : (C' * Real.cos θ + S' * Real.sin θ) ^ 2 ≤ C' ^ 2 + S' ^ 2 := by
      nlinarith [sq_nonneg (C' * Real.sin θ - S' * Real.cos θ), Real.sin_sq_add_cos_sq θ]
    exact abs_le_of_sq_le_sq' (h4.trans hR) hN1 |> fun h => abs_le.mpr h
  have hdiff : UL κ N x - UL κ N x' = κ / N *
      ((C' * Real.cos (thetaC x j) + S' * Real.sin (thetaC x j)) -
        (C' * Real.cos (thetaC x' j) + S' * Real.sin (thetaC x' j))) := by
    simp only [UL, hC, hS, hC', hS']
    have a1 := Real.sin_sq_add_cos_sq (thetaC x j)
    have a2 := Real.sin_sq_add_cos_sq (thetaC x' j)
    have hN' : (N : ℝ) ≠ 0 := by positivity
    field_simp
    linear_combination κ * a1 - κ * a2
  rw [hdiff]
  have b1 := abs_le.mp (hbound (thetaC x j))
  have b2 := abs_le.mp (hbound (thetaC x' j))
  have hNpos : (0 : ℝ) < N := by positivity
  have hk : 0 ≤ κ / N := div_nonneg hκ hNpos.le
  calc κ / N * ((C' * Real.cos (thetaC x j) + S' * Real.sin (thetaC x j)) -
        (C' * Real.cos (thetaC x' j) + S' * Real.sin (thetaC x' j)))
      ≤ κ / N * (2 * (N - 1)) := mul_le_mul_of_nonneg_left (by linarith) hk
    _ ≤ 2 * κ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]; nlinarith

theorem osc_UL_merge {κ : ℝ} (hκ : 0 ≤ κ) (p : Fin N × Fin 1) (a : {i // i ≠ p} → ℝ)
    (b b' : SpT p → ℝ) : UL κ N (mergeR p a b) - UL κ N (mergeR p a b') ≤ 2 * κ := by
  refine osc_UL hκ p.1 fun l hl => ?_
  have h : (l, (0 : Fin 1)) ≠ p := fun h => hl (by rw [← h])
  simp only [mergeR, dif_pos h]

theorem sum_fin_one {α : Type*} [AddCommMonoid α] (f : Fin N × Fin 1 → α) :
    ∑ p, f p = ∑ j : Fin N, f (j, 0) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun j _ => by rw [Fin.sum_univ_one]

theorem Dk_UL (κ : ℝ) (j : Fin N) : Dk (UL κ N) (j, 0) = dUL κ j := funext (fderiv_UL κ j)

/-- (3.36) on the lift. -/
theorem offdiag_lift {κ : ℝ} (hκ : 0 < κ) (x : Fin N × Fin 1 → ℝ) (v : Fin N × Fin 1 → ℝ) :
    -(4 * π ^ 2 * κ / N) * ∑ p, v p ^ 2 ≤
      ∑ p, ∑ r, (if r ≠ p then Dk (Dk (UL κ N) r) p x * v r * v p else 0) := by
  rw [sum_fin_one, sum_fin_one]
  simp_rw [sum_fin_one (fun r => if r ≠ (_, 0) then Dk (Dk (UL κ N) r) (_, 0) x * v r * v (_, 0)
    else 0)]
  set c := 4 * π ^ 2 * κ / N with hc
  set O : Fin N → Fin N → ℝ := fun k j =>
    c * (Real.cos (thetaC x j) * Real.cos (thetaC x k) +
      Real.sin (thetaC x j) * Real.sin (thetaC x k)) with hO
  have hrw : ∀ k j : Fin N, (if ((j, 0) : Fin N × Fin 1) ≠ (k, 0) then
      Dk (Dk (UL κ N) (j, 0)) (k, 0) x * v (j, 0) * v (k, 0) else 0) =
      O k j * v (j, 0) * v (k, 0) - (if j = k then O k j * v (j, 0) * v (k, 0) else 0) := by
    intro k j
    by_cases hjk : j = k
    · subst hjk; simp
    · have hne : ((j, 0) : Fin N × Fin 1) ≠ (k, 0) := fun h => hjk (Prod.mk.inj h).1
      rw [if_pos hne, if_neg hjk, Dk_UL, show Dk (dUL κ j) (k, 0) x = _ from fderiv_dUL κ j k x,
        if_neg hjk, hO, hc]
      ring
  simp_rw [hrw, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h1 : ∑ k, ∑ j, O k j * v (j, 0) * v (k, 0) =
      c * ((∑ j, v (j, 0) * Real.cos (thetaC x j)) ^ 2 +
        (∑ j, v (j, 0) * Real.sin (thetaC x j)) ^ 2) := by
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hO]
    ring
  have h2 : ∑ k, O k k * v (k, 0) * v (k, 0) = c * ∑ k, v (k, 0) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := Real.sin_sq_add_cos_sq (thetaC x k)
    simp only [hO]
    linear_combination (c * v (k, 0) ^ 2) * this
  rw [h1, h2]
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have : 0 ≤ c * ((∑ j, v (j, 0) * Real.cos (thetaC x j)) ^ 2 +
      (∑ j, v (j, 0) * Real.sin (thetaC x j)) ^ 2) := by positivity
  linarith

theorem smPer_UL (κ : ℝ) : SmPer (UL κ N) :=
  ⟨(contDiff_UL κ).of_le le_top, by rw [UL_eq_lift]; exact isPer_lift _⟩

theorem SmPer.sq' {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : (ι → ℝ) → ℝ} (h : SmPer Φ) :
    SmPer (fun x => Φ x ^ 2) := by
  have := h.mul h
  exact ⟨by simpa only [sq] using this.1, fun m x => by simp only [h.2 m x]⟩

/-- (3.34) on the lift. -/
theorem second_order_lift {κ : ℝ} (hκ : 0 < κ) {g : (Fin N × Fin 1 → ℝ) → ℝ} (hg : SmPer g) :
    4 * π ^ 2 * (Real.exp (-2 * κ) - κ / N) *
        ∫ y, Real.exp (-UL κ N (secT y)) * ∑ p, Dk g p (secT y) ^ 2 ≤
      ∫ y, Real.exp (-UL κ N (secT y)) * Lop g (UL κ N) (secT y) ^ 2 := by
  have hU := smPer_UL (N := N) κ
  rw [bochner hg hU]
  set c := 4 * π ^ 2 * κ / N with hc
  set ΦD : (Fin N × Fin 1 → ℝ) → ℝ := fun x => ∑ p, Real.exp (-UL κ N x) *
    (Dk (Dk g p) p x ^ 2 + Dk (Dk (UL κ N) p) p x * Dk g p x ^ 2) with hΦD
  set ΦG : (Fin N × Fin 1 → ℝ) → ℝ := fun x => Real.exp (-UL κ N x) * ∑ p, Dk g p x ^ 2
    with hΦG
  have sD : SmPer ΦD := SmPer.sum _ fun p => hU.expNeg.mul
    (((hg.Dk p).Dk p).sq'.add (((hU.Dk p).Dk p).mul (hg.Dk p).sq'))
  have sG : SmPer ΦG := hU.expNeg.mul (SmPer.sum _ fun p => (hg.Dk p).sq')
  have iR : Integrable (fun y => Real.exp (-UL κ N (secT y)) *
      (∑ p, ∑ r, Dk (Dk g p) r (secT y) ^ 2 +
        ∑ p, ∑ r, Dk (Dk (UL κ N) r) p (secT y) * Dk g r (secT y) * Dk g p (secT y))) volume :=
    (hU.expNeg.mul ((SmPer.sum Finset.univ fun p => SmPer.sum Finset.univ fun r =>
      ((hg.Dk p).Dk r).sq').add (SmPer.sum Finset.univ fun p => SmPer.sum Finset.univ fun r =>
      (((hU.Dk r).Dk p).mul (hg.Dk r)).mul (hg.Dk p)))).integrable
  -- pointwise lower bound
  have hpt : ∀ y, ΦD (secT y) - c * ΦG (secT y) ≤ Real.exp (-UL κ N (secT y)) *
      (∑ p, ∑ r, Dk (Dk g p) r (secT y) ^ 2 +
        ∑ p, ∑ r, Dk (Dk (UL κ N) r) p (secT y) * Dk g r (secT y) * Dk g p (secT y)) := by
    intro y
    set x := secT y
    have hoff := offdiag_lift hκ x (fun p => Dk g p x)
    have hsq : ∑ p, Dk (Dk g p) p x ^ 2 ≤ ∑ p, ∑ r, Dk (Dk g p) r x ^ 2 :=
      Finset.sum_le_sum fun p _ => Finset.single_le_sum (f := fun r => Dk (Dk g p) r x ^ 2)
        (fun r _ => sq_nonneg _) (Finset.mem_univ p)
    have hsplit : ∑ p, ∑ r, Dk (Dk (UL κ N) r) p x * Dk g r x * Dk g p x =
        ∑ p, Dk (Dk (UL κ N) p) p x * Dk g p x ^ 2 +
          ∑ p, ∑ r, (if r ≠ p then Dk (Dk (UL κ N) r) p x * Dk g r x * Dk g p x else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      have : ∀ r, Dk (Dk (UL κ N) r) p x * Dk g r x * Dk g p x =
          (if r = p then Dk (Dk (UL κ N) r) p x * Dk g r x * Dk g p x else 0) +
            (if r ≠ p then Dk (Dk (UL κ N) r) p x * Dk g r x * Dk g p x else 0) := fun r => by
        by_cases h : r = p <;> simp [h]
      rw [Finset.sum_congr rfl fun r _ => this r, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    have he : 0 ≤ Real.exp (-UL κ N x) := (Real.exp_pos _).le
    simp only [hΦD, hΦG, ← Finset.mul_sum]
    rw [hsplit]
    have : Real.exp (-UL κ N x) * (∑ p, (Dk (Dk g p) p x ^ 2 +
        Dk (Dk (UL κ N) p) p x * Dk g p x ^ 2)) - c * (Real.exp (-UL κ N x) *
          ∑ p, Dk g p x ^ 2) = Real.exp (-UL κ N x) * (∑ p, Dk (Dk g p) p x ^ 2 +
        (∑ p, Dk (Dk (UL κ N) p) p x * Dk g p x ^ 2 + -(c * ∑ p, Dk g p x ^ 2))) := by
      rw [Finset.sum_add_distrib]; ring
    rw [this]
    refine mul_le_mul_of_nonneg_left (add_le_add hsq (add_le_add le_rfl ?_)) he
    rw [hc]
    simpa [neg_mul] using hoff
  have hint0 : ∫ y, (ΦD (secT y) - c * ΦG (secT y)) ≤ ∫ y, Real.exp (-UL κ N (secT y)) *
      (∑ p, ∑ r, Dk (Dk g p) r (secT y) ^ 2 +
        ∑ p, ∑ r, Dk (Dk (UL κ N) r) p (secT y) * Dk g r (secT y) * Dk g p (secT y)) :=
    integral_mono (sD.integrable.sub (sG.integrable.const_mul c)) iR hpt
  have hsub : ∫ y, (ΦD (secT y) - c * ΦG (secT y)) =
      (∫ y, ΦD (secT y)) - ∫ y, c * ΦG (secT y) :=
    integral_sub sD.integrable (sG.integrable.const_mul c)
  have hint := hint0
  rw [hsub, integral_const_mul] at hint
  -- the diagonal terms
  have hdiag : 4 * π ^ 2 * Real.exp (-2 * κ) * ∫ y, ΦG (secT y) ≤ ∫ y, ΦD (secT y) := by
    simp only [hΦD, hΦG]
    rw [integral_finset_sum _ fun p _ => (hU.expNeg.mul (((hg.Dk p).Dk p).sq'.add
      (((hU.Dk p).Dk p).mul (hg.Dk p).sq'))).integrable]
    simp_rw [Finset.mul_sum]
    rw [integral_finset_sum _ fun p _ => (hU.expNeg.mul (hg.Dk p).sq').integrable,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have := diag_integrated hg hU p (κ' := 2 * κ) (osc_UL_merge hκ.le p)
    rw [show -2 * κ = -(2 * κ) by ring]
    exact this
  have : 4 * π ^ 2 * (Real.exp (-2 * κ) - κ / N) * (∫ y, ΦG (secT y)) =
      4 * π ^ 2 * Real.exp (-2 * κ) * (∫ y, ΦG (secT y)) - c * ∫ y, ΦG (secT y) := by
    rw [hc]; ring
  simp only [hΦG] at this hint hdiag ⊢
  linarith

theorem gradDotC_unflat (g : Config N 1 → ℝ) (y : UnitAddTorus (Fin N × Fin 1)) :
    gradDotC g g (unflat y) = ∑ p, Dk ((g ∘ unflat) ∘ liftT) p (secT y) ^ 2 := by
  simp only [gradDotC, cpartialC_unflat]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem cosGen_unflat (κ : ℝ) (g : Config N 1 → ℝ) (y : UnitAddTorus (Fin N × Fin 1)) :
    cosGen κ N g (unflat y) = Lop ((g ∘ unflat) ∘ liftT) (UL κ N) (secT y) := by
  simp only [cosGen, laplacianC, gradDotC, cpartialC_unflat, cpartial2C_unflat, ← UL_eq_lift,
    Lop]
  rw [Fintype.sum_prod_type, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_sub_distrib]

/-- Lemma 3.7, (3.34). -/
theorem cosine_second_order_aux {κ : ℝ} (hκ : 0 < κ) {g : Config N 1 → ℝ} (hg : IsSmoothC g) :
    aCos * (Real.exp (-2 * κ) - κ / N) * ∫ X, gradDotC g g X ∂gibbs cosV (cosW κ) N ≤
      ∫ X, cosGen κ N g X ^ 2 ∂gibbs cosV (cosW κ) N := by
  rw [integral_gibbs_cos, integral_gibbs_cos]
  have hH := continuous_hamiltonian (cosine_hyp_all κ) N
  have hZ := partition_pos_of_continuous (volume : Measure (Config N 1)) hH
  have hc : 0 ≤ Real.exp (κ * N / 2) / partitionFn cosV (cosW κ) N :=
    div_nonneg (Real.exp_pos _).le hZ.le
  have hgs : SmPer ((g ∘ unflat) ∘ liftT) := ⟨hg, isPer_lift _⟩
  have h := second_order_lift hκ hgs
  simp_rw [gradDotC_unflat, cosGen_unflat]
  have e1 : ∀ y, (∑ p, Dk ((g ∘ unflat) ∘ liftT) p (secT y) ^ 2) * Real.exp (-UL κ N (secT y)) =
      Real.exp (-UL κ N (secT y)) * ∑ p, Dk ((g ∘ unflat) ∘ liftT) p (secT y) ^ 2 :=
    fun y => mul_comm _ _
  have e2 : ∀ y, Lop ((g ∘ unflat) ∘ liftT) (UL κ N) (secT y) ^ 2 * Real.exp (-UL κ N (secT y)) =
      Real.exp (-UL κ N (secT y)) * Lop ((g ∘ unflat) ∘ liftT) (UL κ N) (secT y) ^ 2 :=
    fun y => mul_comm _ _
  simp_rw [e1, e2]
  unfold aCos
  calc 4 * π ^ 2 * (Real.exp (-2 * κ) - κ / N) *
        (Real.exp (κ * N / 2) / partitionFn cosV (cosW κ) N *
          ∫ y, Real.exp (-UL κ N (secT y)) * ∑ p, Dk ((g ∘ unflat) ∘ liftT) p (secT y) ^ 2)
      = Real.exp (κ * N / 2) / partitionFn cosV (cosW κ) N *
          (4 * π ^ 2 * (Real.exp (-2 * κ) - κ / N) *
            ∫ y, Real.exp (-UL κ N (secT y)) * ∑ p, Dk ((g ∘ unflat) ∘ liftT) p (secT y) ^ 2) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hc

end Cosine

end SharpLSI
