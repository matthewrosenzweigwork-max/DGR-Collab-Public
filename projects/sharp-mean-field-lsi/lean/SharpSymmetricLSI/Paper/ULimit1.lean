import SharpSymmetricLSI.Paper.WeightedHS3

/-!
# (6.6), (6.7): the decomposition of `U_N` and the variance of the off-diagonal part
(Phase 3, lane D; R26)
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

section generic
variable {α : Type*} [MeasurableSpace α] [Nonempty α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- A product integral vanishes when one coordinate enters only through a kernel centered in that
variable. -/
theorem integral_kernel_mul_eq_zero {n : ℕ} {κ : α → α → ℝ} (hcent : ∀ᵐ w ∂μ, ∫ y, κ y w ∂μ = 0)
    {u v : Fin (n + 1)} (huv : u ≠ v) {F : (Fin (n + 1) → α) → ℝ}
    (hF : ∀ X y, F (Function.update X u y) = F X)
    (hint : Integrable (fun X => κ (X u) (X v) * F X) (Measure.pi fun _ : Fin (n + 1) => μ)) :
    ∫ X, κ (X u) (X v) * F X ∂(Measure.pi fun _ : Fin (n + 1) => μ) = 0 := by
  set P := Measure.pi fun _ : Fin (n + 1) => μ
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) u
  have hmp : MeasurePreserving e P (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) u
  obtain ⟨v', hv'⟩ := Fin.exists_succAbove_eq huv.symm
  set G : (Fin (n + 1) → α) → ℝ := fun X => κ (X u) (X v) * F X
  have hsymm := hmp.symm
  rw [← hsymm.integral_comp' (g := G)]
  have hint' : Integrable (fun q => G (e.symm q)) (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
    (hsymm.integrable_comp_emb e.symm.measurableEmbedding).mpr hint
  rw [integral_prod_symm _ hint']
  have hes : ∀ (y : α) (r : Fin n → α), e.symm (y, r) = Fin.insertNth u y r := fun y r => rfl
  have hpt : ∀ r : Fin n → α, ∀ y : α, G (e.symm (y, r)) =
      κ y (r v') * F (e.symm (Classical.arbitrary α, r)) := fun r y => by
    simp only [G, hes]
    rw [Fin.insertNth_apply_same, ← hv', Fin.insertNth_apply_succAbove]
    congr 1
    have h1 : (Fin.insertNth u y r : Fin (n + 1) → α) =
        Function.update (Fin.insertNth (α := fun _ => α) u (Classical.arbitrary α) r) u y := by
      rw [Fin.update_insertNth]
    rw [h1, hF]
  have hmarg : ∀ᵐ r ∂(Measure.pi fun _ : Fin n => μ), ∫ y, κ y (r v') ∂μ = 0 :=
    (measurePreserving_eval (fun _ : Fin n => μ) v').quasiMeasurePreserving.ae hcent
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hmarg] with r hr
  simp_rw [hpt r]
  rw [integral_mul_const, hr, zero_mul]
  rfl

theorem map_pair_pi_gen {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    (Measure.pi fun _ : Fin N => μ).map (fun X => (X i, X j)) = μ.prod μ := by
  have hind := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ => id)
    (fun _ => aemeasurable_id)
  have h2 := (hind.indepFun hij)
  simp only [id_eq] at h2
  have h3 := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    (f := fun ω : Fin N → α => ω i) (g := fun ω : Fin N → α => ω j)
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable).mp h2
  rw [h3, (measurePreserving_eval (fun _ : Fin N => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) j).map_eq]

/-- The number of pairs `i < j` in `Fin N`. -/
theorem card_lt_pairs (N : ℕ) :
    ((Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2).card : ℝ) = N * (N - 1) / 2 := by
  have h : (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2).card =
      ∑ i : Fin N, (Finset.Ioi i).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.card_filter]
    congr 1; ext j; simp
  rw [h]
  simp_rw [Fin.card_Ioi]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have : ∑ i : Fin N, (N - 1 - (i : ℕ)) = ∑ k ∈ Finset.range N, k := by
    rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i)]
    exact Finset.sum_range_reflect (fun k => k) N
  rw [this]
  have h2 := Finset.sum_range_id_mul_two N
  have h3 : ((∑ k ∈ Finset.range N, k : ℕ) : ℝ) * 2 = N * (N - 1 : ℕ) := by exact_mod_cast h2
  rw [Nat.cast_sub hN] at h3
  push_cast at h3 ⊢
  linarith

/-- **(6.7)** for a centered symmetric square-integrable kernel. -/
theorem integral_offdiag_sq {N : ℕ} {κ : α → α → ℝ}
    (hm : AEStronglyMeasurable (Function.uncurry κ) (μ.prod μ)) (hsymm : ∀ x y, κ x y = κ y x)
    (hcent : ∀ᵐ w ∂μ, ∫ y, κ y w ∂μ = 0)
    (hL2 : Integrable (fun p : α × α => κ p.1 p.2 ^ 2) (μ.prod μ)) :
    ∫ X, (∑ i, ∑ j, if i < j then κ (X i) (X j) else 0) ^ 2 ∂(Measure.pi fun _ : Fin N => μ) =
      N * (N - 1) / 2 * ∫ p, κ p.1 p.2 ^ 2 ∂(μ.prod μ) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  set P := Measure.pi fun _ : Fin (n + 1) => μ
  set S := Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) => p.1 < p.2
  have hsum : ∀ X : Fin (n + 1) → α, (∑ i, ∑ j, if i < j then κ (X i) (X j) else 0) =
      ∑ p ∈ S, κ (X p.1) (X p.2) := fun X => by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp_rw [hsum]
  -- each `κ_p` is in `L²(P)` with the same norm
  have hpair : ∀ p ∈ S, (P.map fun X => (X p.1, X p.2)) = μ.prod μ := fun p hp =>
    map_pair_pi_gen (Finset.mem_filter.mp hp).2.ne
  have hmeasp : ∀ p : Fin (n + 1) × Fin (n + 1), Measurable fun X : Fin (n + 1) → α => (X p.1, X p.2) :=
    fun p => (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  have hL2p : ∀ p ∈ S, MemLp (fun X : Fin (n + 1) → α => κ (X p.1) (X p.2)) 2 P := fun p hp => by
    have h0 : MemLp (fun q : α × α => κ q.1 q.2) 2 (P.map fun X => (X p.1, X p.2)) := by
      rw [hpair p hp]; exact (memLp_two_iff_integrable_sq hm).mpr hL2
    exact h0.comp_of_map (hmeasp p).aemeasurable
  have hsq : ∀ p ∈ S, ∫ X, κ (X p.1) (X p.2) * κ (X p.1) (X p.2) ∂P = ∫ q, κ q.1 q.2 ^ 2 ∂(μ.prod μ) :=
    fun p hp => by
      rw [← hpair p hp, integral_map (hmeasp p).aemeasurable (by rw [hpair p hp]; exact hL2.1)]
      congr 1; funext X; ring
  -- off-diagonal products vanish
  have hzero : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      ∫ X, κ (X p.1) (X p.2) * κ (X q.1) (X q.2) ∂P = 0 := by
    intro p hp q hq hpq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hint := (hL2p p hp).integrable_mul (hL2p q hq)
    by_cases h1 : p.1 ≠ q.1 ∧ p.1 ≠ q.2
    · exact integral_kernel_mul_eq_zero hcent hp'.ne (F := fun X => κ (X q.1) (X q.2))
        (fun X y => by simp [Function.update_of_ne h1.1.symm, Function.update_of_ne h1.2.symm]) hint
    · by_cases h2 : p.2 ≠ q.1 ∧ p.2 ≠ q.2
      · have e1 : (fun X : Fin (n + 1) → α => κ (X p.1) (X p.2) * κ (X q.1) (X q.2)) =
            fun X => κ (X p.2) (X p.1) * κ (X q.1) (X q.2) := by
          funext X; rw [hsymm]
        have hint' : Integrable (fun X : Fin (n + 1) → α => κ (X p.2) (X p.1) * κ (X q.1) (X q.2)) P :=
          hint.congr (Eventually.of_forall fun X => by simp only [Pi.mul_apply]; rw [hsymm])
        rw [e1]
        exact integral_kernel_mul_eq_zero hcent hp'.ne.symm (F := fun X => κ (X q.1) (X q.2))
          (fun X y => by simp [Function.update_of_ne h2.1.symm, Function.update_of_ne h2.2.symm]) hint'
      · exfalso
        apply hpq
        push_neg at h1 h2
        rcases (em (p.1 = q.1)) with ha | ha
        · have hb : p.2 = q.2 := by
            rcases (em (p.2 = q.1)) with hc | hc
            · exact absurd (ha ▸ hc ▸ hp') (lt_irrefl _)
            · exact h2 hc
          exact Prod.ext ha hb
        · have hq2 := h1 ha
          have hb : p.2 = q.1 := by
            by_contra hc
            have := h2 hc
            rw [this] at hp'; rw [← hq2] at hp'; exact lt_irrefl _ hp'
          exfalso
          rw [hb, hq2] at hp'; exact lt_asymm hp' hq'
  have hexpand : ∀ X : Fin (n + 1) → α, (∑ p ∈ S, κ (X p.1) (X p.2)) ^ 2 =
      ∑ p ∈ S, ∑ q ∈ S, κ (X p.1) (X p.2) * κ (X q.1) (X q.2) := fun X => by
    rw [sq, Finset.sum_mul_sum]
  simp_rw [hexpand]
  rw [integral_finset_sum (f := fun (p : Fin (n + 1) × Fin (n + 1)) (X : Fin (n + 1) → α) =>
      ∑ q ∈ S, κ (X p.1) (X p.2) * κ (X q.1) (X q.2)) _
    fun p hp => integrable_finset_sum _ fun q hq => (hL2p p hp).integrable_mul (hL2p q hq)]
  have hrow : ∀ p ∈ S, ∫ X, ∑ q ∈ S, κ (X p.1) (X p.2) * κ (X q.1) (X q.2) ∂P =
      ∫ q, κ q.1 q.2 ^ 2 ∂(μ.prod μ) := fun p hp => by
    rw [integral_finset_sum (f := fun (q : Fin (n + 1) × Fin (n + 1)) (X : Fin (n + 1) → α) =>
      κ (X p.1) (X p.2) * κ (X q.1) (X q.2)) _
      fun q hq => (hL2p p hp).integrable_mul (hL2p q hq)]
    rw [Finset.sum_eq_single p (fun q hq hqp => hzero p hp q hq (Ne.symm hqp))
      (fun h => absurd hp h), hsq p hp]
  rw [Finset.sum_congr rfl hrow, Finset.sum_const, nsmul_eq_mul, card_lt_pairs]

/-- Splitting a symmetric double sum into twice the strict upper part plus the diagonal. -/
theorem sum_sum_symm_eq {N : ℕ} {f : Fin N → Fin N → ℝ} (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j, f i j = 2 * (∑ i, ∑ j, if i < j then f i j else 0) + ∑ i, f i i := by
  have hsplit : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f j i else 0) +
      (if i = j then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le, hf i j]
  have hswap : (∑ i, ∑ j, if j < i then f j i else (0 : ℝ)) =
      ∑ i, ∑ j, if i < j then f i j else 0 := Finset.sum_comm
  have hdiag : (∑ i, ∑ j, if i = j then f i j else (0 : ℝ)) = ∑ i, f i i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]; simp
  calc ∑ i, ∑ j, f i j = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f j i else 0) +
        (if i = j then f i j else 0)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j
    _ = _ := by
        simp only [Finset.sum_add_distrib]; rw [hswap, hdiag]; ring

end generic


variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section torus
variable (hyp : Hyp V W KV KW) (μ : ProbabilityMeasure (Torus d))
include hyp

theorem centeredKernel_symm' (x y : Torus d) :
    centeredKernel W (μ : Measure (Torus d)) x y = centeredKernel W μ y x := by
  unfold centeredKernel; rw [hyp.symm]; ring

/-- **(6.6)**. -/
theorem Ucentered_decomp {N : ℕ} (X : Config N d) :
    Ucentered W μ N X =
      (N : ℝ)⁻¹ * (∑ i, ∑ j, if i < j then centeredKernel W μ (X i) (X j) else 0) +
        (2 * (N : ℝ))⁻¹ * ∑ i, centeredKernel W μ (X i) (X i) := by
  unfold Ucentered
  rw [sum_sum_symm_eq (f := fun i j => centeredKernel W μ (X i) (X j))
    fun i j => centeredKernel_symm' hyp μ _ _]
  rcases eq_or_ne (N : ℝ) 0 with h | h
  · simp [h]
  · field_simp

/-- **(6.7)**. -/
theorem integral_offdiag_centered_sq {N : ℕ} (hN : 1 ≤ N) :
    ∫ X, ((N : ℝ)⁻¹ * ∑ i, ∑ j, if i < j then centeredKernel W μ (X i) (X j) else 0) ^ 2
        ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))) =
      ((N : ℝ) - 1) / (2 * N) * ∫ x, ∫ y, centeredKernel W μ x y ^ 2
        ∂(μ : Measure (Torus d)) ∂(μ : Measure (Torus d)) := by
  obtain ⟨B, hB⟩ := centeredKernel_bdd hyp (μ : Measure (Torus d))
  have hmeas := measurable_centeredKernel hyp (μ : Measure (Torus d))
  have hL2 : Integrable (fun p : Torus d × Torus d => centeredKernel W μ p.1 p.2 ^ 2)
      ((μ : Measure (Torus d)).prod μ) := by
    refine integrable_of_bdd (C := B ^ 2) (hmeas.pow_const 2) fun p => ?_
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _ _) 2
  have h := integral_offdiag_sq (μ := (μ : Measure (Torus d))) (N := N)
    hmeas.aestronglyMeasurable (centeredKernel_symm' hyp μ)
    (Eventually.of_forall fun w => by
      simp_rw [centeredKernel_symm' hyp μ _ w]; exact integral_centeredKernel hyp _ w) hL2
  simp_rw [mul_pow]
  rw [integral_const_mul, h, integral_prod _ hL2]
  have hN' : (N : ℝ) ≠ 0 := by positivity
  field_simp

end torus

end SharpLSI
