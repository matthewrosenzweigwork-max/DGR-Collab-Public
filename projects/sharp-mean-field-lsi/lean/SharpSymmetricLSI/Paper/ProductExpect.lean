import SharpSymmetricLSI.Paper.GibbsVariational

/-!
# Expectations under product states (Phase 3, lane D; R6)

Pair and triple laws of `ρ^{⊗N}` and the expansion of
`E (a(xᵢ) + c ∑_{j≠i} B(xᵢ,xⱼ))²`.
-/

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- The triple law `(xⱼ, xₗ, xᵢ) ∼ (μ⊗μ)⊗μ` for distinct indices. -/
theorem map_triple_pi {i j l : Fin N} (hji : j ≠ i) (hli : l ≠ i) (hjl : j ≠ l) :
    (Measure.pi fun _ : Fin N => μ).map (fun X => ((X j, X l), X i)) = (μ.prod μ).prod μ := by
  have hind := iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have h2 := hind.indepFun_prodMk (fun k => measurable_pi_apply k) j l i hji hli
  simp only [id_eq] at h2
  have h3 := (indepFun_iff_map_prod_eq_prod_map_map
    (f := fun ω : Config N d => (ω j, ω l)) (g := fun ω : Config N d => ω i)
    ((measurable_pi_apply j).prodMk (measurable_pi_apply l)).aemeasurable
    (measurable_pi_apply i).aemeasurable).mp h2
  rw [h3, map_pair_pi hjl, (measurePreserving_eval (fun _ : Fin N => μ) i).map_eq]

theorem integral_pair_pi {i j : Fin N} (hij : i ≠ j) {F : Torus d → Torus d → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    ∫ X, F (X i) (X j) ∂(Measure.pi fun _ : Fin N => μ) = ∫ p, F p.1 p.2 ∂(μ.prod μ) := by
  rw [← map_pair_pi (ρ := μ) hij, integral_map (φ := fun X : Config N d => (X i, X j))
    (f := fun p => F p.1 p.2) (by fun_prop) hF.aestronglyMeasurable]

theorem integral_triple_pi {i j l : Fin N} (hji : j ≠ i) (hli : l ≠ i) (hjl : j ≠ l)
    {G : Torus d → Torus d → Torus d → ℝ}
    (hG : Measurable fun q : (Torus d × Torus d) × Torus d => G q.2 q.1.1 q.1.2) :
    ∫ X, G (X i) (X j) (X l) ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ q, G q.2 q.1.1 q.1.2 ∂((μ.prod μ).prod μ) := by
  rw [← map_triple_pi (μ := μ) hji hli hjl, integral_map
    (φ := fun X : Config N d => ((X j, X l), X i)) (f := fun q => G q.2 q.1.1 q.1.2) (by fun_prop)
    hG.aestronglyMeasurable]

theorem card_erase_univ (hN : 1 ≤ N) (i : Fin N) :
    ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub hN, Nat.cast_one]

/-- **Expansion of `E(a(xᵢ) + c ∑_{j≠i} B(xᵢ,xⱼ))²` under `μ^{⊗N}`.** -/
theorem expect_sq (hN : 1 ≤ N) (i : Fin N) {a : Torus d → ℝ} {B : Torus d → Torus d → ℝ}
    (ha : Measurable a) (hB : Measurable (Function.uncurry B)) {A C : ℝ}
    (haA : ∀ x, |a x| ≤ A) (hBC : ∀ x y, |B x y| ≤ C) (c : ℝ) :
    ∫ X, (a (X i) + c * ∑ j ∈ Finset.univ.erase i, B (X i) (X j)) ^ 2
        ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ x, a x ^ 2 ∂μ + 2 * c * ((N : ℝ) - 1) * ∫ x, a x * ∫ y, B x y ∂μ ∂μ +
        c ^ 2 * ((N : ℝ) - 1) * ∫ x, ∫ y, B x y ^ 2 ∂μ ∂μ +
        c ^ 2 * (((N : ℝ) - 1) * ((N : ℝ) - 2)) * ∫ x, (∫ y, B x y ∂μ) ^ 2 ∂μ := by
  set P := Measure.pi fun _ : Fin N => μ with hP
  set E := Finset.univ.erase i with hE
  have ibdd : ∀ {α : Type} [MeasurableSpace α] {m : Measure α} [IsFiniteMeasure m] {f : α → ℝ},
      Measurable f → ∀ K, (∀ x, |f x| ≤ K) → Integrable f m := fun hf K hK =>
    Integrable.of_bound hf.aestronglyMeasurable K (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hK x)
  have hBij : ∀ j l : Fin N, Measurable fun X : Config N d => B (X j) (X l) := fun j l => by
    have := hB.comp ((measurable_pi_apply j).prodMk (measurable_pi_apply l) :
      Measurable fun X : Config N d => (X j, X l))
    exact this
  have haX : Measurable fun X : Config N d => a (X i) := ha.comp (measurable_pi_apply i)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hBC 0 0)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (haA 0)
  -- pointwise expansion
  have hexp : ∀ X : Config N d, (a (X i) + c * ∑ j ∈ E, B (X i) (X j)) ^ 2 =
      a (X i) ^ 2 + 2 * c * ∑ j ∈ E, a (X i) * B (X i) (X j) +
      c ^ 2 * ∑ j ∈ E, B (X i) (X j) ^ 2 +
      c ^ 2 * ∑ j ∈ E, ∑ l ∈ E.erase j, B (X i) (X j) * B (X i) (X l) := fun X => by
    have hsq : (∑ j ∈ E, B (X i) (X j)) ^ 2 = ∑ j ∈ E, B (X i) (X j) ^ 2 +
        ∑ j ∈ E, ∑ l ∈ E.erase j, B (X i) (X j) * B (X i) (X l) := by
      rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← Finset.add_sum_erase _ _ hj, sq]
    have hm : a (X i) * ∑ j ∈ E, B (X i) (X j) = ∑ j ∈ E, a (X i) * B (X i) (X j) :=
      Finset.mul_sum _ _ _
    rw [add_sq, mul_pow, hsq, ← hm]
    ring
  simp_rw [hexp]
  -- integrability of the pieces
  have i1 : Integrable (fun X : Config N d => a (X i) ^ 2) P := ibdd (haX.pow_const 2) (A ^ 2)
    fun X => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (haA _) 2
  have i2 : ∀ j, Integrable (fun X : Config N d => a (X i) * B (X i) (X j)) P := fun j =>
    ibdd (haX.mul (hBij i j)) (A * C) fun X => by
      rw [abs_mul]; exact mul_le_mul (haA _) (hBC _ _) (abs_nonneg _) (hA0)
  have i3 : ∀ j, Integrable (fun X : Config N d => B (X i) (X j) ^ 2) P := fun j =>
    ibdd ((hBij i j).pow_const 2) (C ^ 2) fun X => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hBC _ _) 2
  have i4 : ∀ j l, Integrable (fun X : Config N d => B (X i) (X j) * B (X i) (X l)) P :=
    fun j l => ibdd ((hBij i j).mul (hBij i l)) (C * C) fun X => by
      rw [abs_mul]; exact mul_le_mul (hBC _ _) (hBC _ _) (abs_nonneg _) hC0
  have j2 : Integrable (fun X : Config N d => ∑ j ∈ E, a (X i) * B (X i) (X j)) P :=
    integrable_finsetSum _ fun j _ => i2 j
  have j3 : Integrable (fun X : Config N d => ∑ j ∈ E, B (X i) (X j) ^ 2) P :=
    integrable_finsetSum _ fun j _ => i3 j
  have j4 : Integrable (fun X : Config N d =>
      ∑ j ∈ E, ∑ l ∈ E.erase j, B (X i) (X j) * B (X i) (X l)) P :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => i4 j l
  rw [integral_add (f := fun X : Config N d => a (X i) ^ 2 + 2 * c * ∑ j ∈ E, a (X i) * B (X i) (X j) +
      c ^ 2 * ∑ j ∈ E, B (X i) (X j) ^ 2)
      (g := fun X : Config N d => c ^ 2 * ∑ j ∈ E, ∑ l ∈ E.erase j, B (X i) (X j) * B (X i) (X l))
      ((i1.add (j2.const_mul _)).add (j3.const_mul _)) (j4.const_mul _),
    integral_add (f := fun X : Config N d => a (X i) ^ 2 + 2 * c * ∑ j ∈ E, a (X i) * B (X i) (X j))
      (g := fun X : Config N d => c ^ 2 * ∑ j ∈ E, B (X i) (X j) ^ 2)
      (i1.add (j2.const_mul _)) (j3.const_mul _),
    integral_add (f := fun X : Config N d => a (X i) ^ 2)
      (g := fun X : Config N d => 2 * c * ∑ j ∈ E, a (X i) * B (X i) (X j)) i1 (j2.const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun j _ => i2 j, integral_finsetSum _ fun j _ => i3 j,
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => i4 j l]
  simp_rw [integral_finsetSum _ fun l _ => i4 _ l]
  -- the four expectations
  have e1 : ∫ X, a (X i) ^ 2 ∂P = ∫ x, a x ^ 2 ∂μ :=
    integral_comp_eval (μ := fun _ : Fin N => μ) (ha.pow_const 2).aestronglyMeasurable
  have hpm : ∀ {f : Torus d × Torus d → ℝ}, Measurable f → ∀ K, (∀ p, |f p| ≤ K) →
      Integrable f (μ.prod μ) := fun hf K hK => ibdd hf K hK
  have e2 : ∀ j ∈ E, ∫ X, a (X i) * B (X i) (X j) ∂P = ∫ x, a x * ∫ y, B x y ∂μ ∂μ := by
    intro j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    have hm2 : Measurable fun p : Torus d × Torus d => a p.1 * B p.1 p.2 :=
      (ha.comp measurable_fst).mul hB
    rw [integral_pair_pi (F := fun x y => a x * B x y) hij hm2,
      integral_prod (fun p : Torus d × Torus d => a p.1 * B p.1 p.2) (hpm hm2 (A * C) fun p => by
        rw [abs_mul]; exact mul_le_mul (haA _) (hBC _ _) (abs_nonneg _) hA0)]
    simp_rw [integral_const_mul]
  have e3 : ∀ j ∈ E, ∫ X, B (X i) (X j) ^ 2 ∂P = ∫ x, ∫ y, B x y ^ 2 ∂μ ∂μ := by
    intro j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    have hm3 : Measurable fun p : Torus d × Torus d => B p.1 p.2 ^ 2 := hB.pow_const 2
    rw [integral_pair_pi (F := fun x y => B x y ^ 2) hij hm3,
      integral_prod (fun p : Torus d × Torus d => B p.1 p.2 ^ 2) (hpm hm3 (C ^ 2) fun p => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hBC _ _) 2)]
  have e4 : ∀ j ∈ E, ∀ l ∈ E.erase j, ∫ X, B (X i) (X j) * B (X i) (X l) ∂P =
      ∫ x, (∫ y, B x y ∂μ) ^ 2 ∂μ := by
    intro j hj l hl
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    have hGm : Measurable fun q : (Torus d × Torus d) × Torus d => B q.2 q.1.1 * B q.2 q.1.2 :=
      (hB.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).mul
        (hB.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    rw [integral_triple_pi (G := fun x y z => B x y * B x z) hji hli (Ne.symm hlj) hGm,
      integral_prod_symm (fun q : (Torus d × Torus d) × Torus d => B q.2 q.1.1 * B q.2 q.1.2)
        (ibdd hGm (C * C) fun q => by
        rw [abs_mul]; exact mul_le_mul (hBC _ _) (hBC _ _) (abs_nonneg _) hC0)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_prod_mul (fun y => B x y) (fun z => B x z), sq]
  rw [e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3,
    Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl (e4 j hj)]
  simp only [Finset.sum_const, nsmul_eq_mul, hE, card_erase_univ hN]
  have hc2 : ∀ j ∈ Finset.univ.erase i, (((Finset.univ.erase i).erase j).card : ℝ) =
      (N : ℝ) - 2 := fun j hj => by
    rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
    have h2 : 1 ≤ N - 1 := by
      have := Finset.mem_erase.mp hj
      have hN2 : 2 ≤ N := by
        by_contra h; push_neg at h
        have : N = 1 := by omega
        subst this; exact this.1 (Subsingleton.elim _ _)
      omega
    rw [Nat.cast_sub h2, Nat.cast_sub hN]; ring
  rw [Finset.sum_congr rfl fun j hj => by rw [hc2 j hj], Finset.sum_const, nsmul_eq_mul,
    card_erase_univ hN]
  ring

end SharpLSI
