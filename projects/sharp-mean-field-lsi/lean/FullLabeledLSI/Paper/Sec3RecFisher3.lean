import FullLabeledLSI.Paper.Sec3RecFisher2
import SharpSymmetricLSI.Paper.ProductFisherFormula
import SharpSymmetricLSI.Paper.ProductExpect

/-!
# Fisher information of products with nonidentical factors, III: moments and the formula

For independent but non-identically distributed coordinates `xⱼ ∼ μⱼ`, the expansion of
`E (a(xᵢ) + c ∑_{j≠i} B(xᵢ,xⱼ))²` and the final formula `product_fisher_gen`.
-/

noncomputable section
open MeasureTheory Set Filter Topology InformationTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {N : ℕ}

section Moments

variable {μ : Fin N → Measure (Torus d)} [∀ i, IsProbabilityMeasure (μ i)]

/-- The triple law `(xⱼ, xₗ, xᵢ) ∼ (μⱼ⊗μₗ)⊗μᵢ` for distinct indices. -/
theorem map_triple_pi_gen {i j l : Fin N} (hji : j ≠ i) (hli : l ≠ i) (hjl : j ≠ l) :
    (Measure.pi μ).map (fun X => ((X j, X l), X i)) = ((μ j).prod (μ l)).prod (μ i) := by
  have hind := iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)
  have h2 := hind.indepFun_prodMk (fun k => measurable_pi_apply k) j l i hji hli
  simp only [id_eq] at h2
  have h3 := (indepFun_iff_map_prod_eq_prod_map_map
    (f := fun Y : Config N d => (Y j, Y l)) (g := fun Y : Config N d => Y i)
    ((measurable_pi_apply j).prodMk (measurable_pi_apply l)).aemeasurable
    (measurable_pi_apply i).aemeasurable).mp h2
  rw [h3, map_pair_pi_gen hjl, (measurePreserving_eval μ i).map_eq]

theorem integral_pair_pi_gen {i j : Fin N} (hij : i ≠ j) {F : Torus d → Torus d → ℝ}
    (hF : Measurable (Function.uncurry F)) :
    ∫ X, F (X i) (X j) ∂(Measure.pi μ) = ∫ p, F p.1 p.2 ∂((μ i).prod (μ j)) := by
  rw [← map_pair_pi_gen (ρ := μ) hij, integral_map (φ := fun X : Config N d => (X i, X j))
    (f := fun p => F p.1 p.2) (by fun_prop) hF.aestronglyMeasurable]

theorem integral_triple_pi_gen {i j l : Fin N} (hji : j ≠ i) (hli : l ≠ i) (hjl : j ≠ l)
    {G : Torus d → Torus d → Torus d → ℝ}
    (hG : Measurable fun q : (Torus d × Torus d) × Torus d => G q.2 q.1.1 q.1.2) :
    ∫ X, G (X i) (X j) (X l) ∂(Measure.pi μ) =
      ∫ q, G q.2 q.1.1 q.1.2 ∂(((μ j).prod (μ l)).prod (μ i)) := by
  rw [← map_triple_pi_gen (μ := μ) hji hli hjl, integral_map
    (φ := fun X : Config N d => ((X j, X l), X i)) (f := fun q => G q.2 q.1.1 q.1.2) (by fun_prop)
    hG.aestronglyMeasurable]

/-- **Expansion of `E(a(xᵢ) + c ∑_{j≠i} B(xᵢ,xⱼ))²` under `⊗ⱼ μⱼ`.** -/
theorem expect_sq_gen (i : Fin N) {a : Torus d → ℝ} {B : Torus d → Torus d → ℝ}
    (ha : Measurable a) (hB : Measurable (Function.uncurry B)) {A C : ℝ}
    (haA : ∀ x, |a x| ≤ A) (hBC : ∀ x y, |B x y| ≤ C) (c : ℝ) :
    ∫ X, (a (X i) + c * ∑ j ∈ Finset.univ.erase i, B (X i) (X j)) ^ 2 ∂(Measure.pi μ) =
      ∫ x, a x ^ 2 ∂μ i + 2 * c * ∑ j ∈ Finset.univ.erase i, ∫ x, a x * ∫ y, B x y ∂μ j ∂μ i +
        c ^ 2 * ∑ j ∈ Finset.univ.erase i, ∫ x, ∫ y, B x y ^ 2 ∂μ j ∂μ i +
        c ^ 2 * ∑ j ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase j,
          ∫ x, (∫ y, B x y ∂μ j) * (∫ y, B x y ∂μ l) ∂μ i := by
  set P := Measure.pi μ with hP
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
  have e1 : ∫ X, a (X i) ^ 2 ∂P = ∫ x, a x ^ 2 ∂μ i :=
    integral_comp_eval (μ := μ) (ha.pow_const 2).aestronglyMeasurable
  have hpm : ∀ {j : Fin N} {f : Torus d × Torus d → ℝ}, Measurable f → ∀ K, (∀ p, |f p| ≤ K) →
      Integrable f ((μ i).prod (μ j)) := fun hf K hK => ibdd hf K hK
  have e2 : ∀ j ∈ E, ∫ X, a (X i) * B (X i) (X j) ∂P = ∫ x, a x * ∫ y, B x y ∂μ j ∂μ i := by
    intro j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    have hm2 : Measurable fun p : Torus d × Torus d => a p.1 * B p.1 p.2 :=
      (ha.comp measurable_fst).mul hB
    rw [integral_pair_pi_gen (F := fun x y => a x * B x y) hij hm2,
      integral_prod (fun p : Torus d × Torus d => a p.1 * B p.1 p.2) (hpm hm2 (A * C) fun p => by
        rw [abs_mul]; exact mul_le_mul (haA _) (hBC _ _) (abs_nonneg _) hA0)]
    simp_rw [integral_const_mul]
  have e3 : ∀ j ∈ E, ∫ X, B (X i) (X j) ^ 2 ∂P = ∫ x, ∫ y, B x y ^ 2 ∂μ j ∂μ i := by
    intro j hj
    have hij : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
    have hm3 : Measurable fun p : Torus d × Torus d => B p.1 p.2 ^ 2 := hB.pow_const 2
    rw [integral_pair_pi_gen (F := fun x y => B x y ^ 2) hij hm3,
      integral_prod (fun p : Torus d × Torus d => B p.1 p.2 ^ 2) (hpm hm3 (C ^ 2) fun p => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hBC _ _) 2)]
  have e4 : ∀ j ∈ E, ∀ l ∈ E.erase j, ∫ X, B (X i) (X j) * B (X i) (X l) ∂P =
      ∫ x, (∫ y, B x y ∂μ j) * (∫ y, B x y ∂μ l) ∂μ i := by
    intro j hj l hl
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    have hGm : Measurable fun q : (Torus d × Torus d) × Torus d => B q.2 q.1.1 * B q.2 q.1.2 :=
      (hB.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).mul
        (hB.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    rw [integral_triple_pi_gen (G := fun x y z => B x y * B x z) hji hli (Ne.symm hlj) hGm,
      integral_prod_symm (fun q : (Torus d × Torus d) × Torus d => B q.2 q.1.1 * B q.2 q.1.2)
        (ibdd hGm (C * C) fun q => by
        rw [abs_mul]; exact mul_le_mul (hBC _ _) (hBC _ _) (abs_nonneg _) hC0)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_prod_mul (fun y => B x y) (fun z => B x z)]
  rw [e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3,
    Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl (e4 j hj)]

end Moments

/-- The mean force exerted on a particle at `x` by a particle distributed as `μ`. -/
noncomputable def mForce (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (x : Torus d)
    (k : Fin d) : ℝ :=
  ∫ y, bGrad W x y k ∂μ

theorem product_fisher_gen (hyp : Hyp V W KV KW) {N q : ℕ} (hN : 1 ≤ N)
    (ρ : Fin q → Torus d → ℝ)
    (hρ : ∀ s, IsSmoothT (ρ s) ∧ (∀ x, 0 < ρ s x) ∧ ∫ x, ρ s x ∂haar d = 1)
    (a : Fin N → Fin q) :
    fisherInfoC (Measure.pi fun i : Fin N => densMeasure (ρ (a i))) (gibbs V W N) ≠ ⊤ ∧
    (fisherInfoC (Measure.pi fun i : Fin N => densMeasure (ρ (a i))) (gibbs V W N)).toReal / N =
      ∑ k : Fin d, (1 / (N : ℝ)) * ∑ i : Fin N,
        ( (∫ x, aGrad V (ρ (a i)) x k ^ 2 ∂densMeasure (ρ (a i)))
        + 2 * (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
            ∫ x, aGrad V (ρ (a i)) x k * mForce W (densMeasure (ρ (a j))) x k ∂densMeasure (ρ (a i))
        + (1 / (N : ℝ)) ^ 2 * ∑ j ∈ Finset.univ.erase i,
            ∫ x, ∫ y, bGrad W x y k ^ 2 ∂densMeasure (ρ (a j)) ∂densMeasure (ρ (a i))
        + (1 / (N : ℝ)) ^ 2 * ∑ j ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase j,
            ∫ x, mForce W (densMeasure (ρ (a j))) x k * mForce W (densMeasure (ρ (a l))) x k
              ∂densMeasure (ρ (a i)) ) := by
  have hs : ∀ i, IsSmoothT (ρ (a i)) := fun i => (hρ (a i)).1
  have hpos : ∀ i x, 0 < ρ (a i) x := fun i => (hρ (a i)).2.1
  have h1 : ∀ i, ∫ x, ρ (a i) x ∂haar d = 1 := fun i => (hρ (a i)).2.2
  have hF := (fisher_productState_gen (N := N) (V := V) (W := W) (KV := KV) (KW := KW) hyp
    (ρs := fun i => ρ (a i)) hs hpos h1).2.2
  have : ∀ i, IsProbabilityMeasure (densMeasure (ρ (a i))) := fun i =>
    isProbabilityMeasure_densMeasure' (fun x => (hpos i x).le) (h1 i)
  set ν := Measure.pi fun i : Fin N => densMeasure (ρ (a i)) with hν
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨Cg, hCg⟩ := gPhiG_bdd (N := N) hyp (ρs := fun i => ρ (a i)) hs hpos
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  have hAb : ∀ i, ∃ C, ∀ x k, |aGrad V (ρ (a i)) x k| ≤ C := fun i => aGrad_bdd hyp (hs i) (hpos i)
  have hmeas : ∀ p, AEStronglyMeasurable
      (fun X : Config N d => gPhiG V W (fun i => ρ (a i)) (flat X) p ^ 2) ν := by
    intro p
    obtain ⟨i, k⟩ := p
    simp_rw [gPhiG_flat hyp hN]
    refine (Measurable.pow_const ?_ 2).aestronglyMeasurable
    refine ((measurable_aGrad hyp (hs i) (hpos i) k).comp (measurable_pi_apply i)).add
      (measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_))
    have := (measurable_bGrad hyp (W := W) k).comp
      ((measurable_pi_apply i).prodMk (measurable_pi_apply j) :
        Measurable fun X : Config N d => (X i, X j))
    exact this
  have hint : ∀ p, Integrable (fun X : Config N d => gPhiG V W (fun i => ρ (a i)) (flat X) p ^ 2)
      ν := fun p =>
    integrable_bdd' (hmeas p) (C := Cg ^ 2) fun X => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCg _ p) 2
  have hterm : ∀ i k, ∫ X, gPhiG V W (fun i => ρ (a i)) (flat X) (i, k) ^ 2 ∂ν =
      (∫ x, aGrad V (ρ (a i)) x k ^ 2 ∂densMeasure (ρ (a i)))
        + 2 * (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
            ∫ x, aGrad V (ρ (a i)) x k * mForce W (densMeasure (ρ (a j))) x k ∂densMeasure (ρ (a i))
        + (1 / (N : ℝ)) ^ 2 * ∑ j ∈ Finset.univ.erase i,
            ∫ x, ∫ y, bGrad W x y k ^ 2 ∂densMeasure (ρ (a j)) ∂densMeasure (ρ (a i))
        + (1 / (N : ℝ)) ^ 2 * ∑ j ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase j,
            ∫ x, mForce W (densMeasure (ρ (a j))) x k * mForce W (densMeasure (ρ (a l))) x k
              ∂densMeasure (ρ (a i)) := by
    intro i k
    obtain ⟨Ca, hCa⟩ := hAb i
    simp_rw [gPhiG_flat hyp hN]
    exact expect_sq_gen (μ := fun i => densMeasure (ρ (a i))) i
      (measurable_aGrad hyp (hs i) (hpos i) k) (measurable_bGrad hyp k)
      (fun x => hCa x k) (fun x y => hCb x y k) (1 / (N : ℝ))
  rw [hF]
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  rw [ENNReal.toReal_ofReal (integral_nonneg fun X => sqNorm_nonneg _)]
  unfold sqNorm
  rw [integral_finsetSum _ fun p _ => hint p, Fintype.sum_prod_type]
  simp_rw [hterm]
  rw [Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_div, div_eq_inv_mul]

end SharpLSI.FL
