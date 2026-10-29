import DGPS.Particle.CenteredKernelMoments
import DGPS.Particle.DiagonalForce

/-!
# Exact force second moment with diagonal correction (LIP014)

For `F_R = K - K_R`, `δ_R(x) = F_R(x,x)` and `E_{N,R} = U_N^{F_R}`, the force of `E_{N,R}` is
`∇ᵢE = N⁻¹ ∑_{j≠i} ∇₁F_R(xᵢ,xⱼ) + (2N)⁻¹ ∇δ_R(xᵢ)` (LIP004), and
`∫ |∇E_{N,R}|² dQ_N = ((N-1)/N) ‖∇₁F_R‖²_{L²(μ²)} + (4N)⁻¹ ‖∇δ_R‖²_{L²(μ)}`.
The proof differentiates the centering identity `∫ F_R(x,y) dμ(y) = 0` in `x`, and uses that,
conditionally on `Xᵢ`, the off-diagonal force summands are centered and independent.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DGPS.Lipschitz.CenteredForceMoment

variable {α : Type*} [MeasurableSpace α]

theorem map_two {μ : Measure α} [IsProbabilityMeasure μ] {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    Measure.map (fun x : Fin N → α => (x i, x j)) (Measure.pi fun _ => μ) = μ.prod μ := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ => id)
    (fun _ => aemeasurable_id)).indepFun hij
  rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
    (measurable_pi_apply j).aemeasurable).1 hind]
  rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) j).map_eq]

theorem integral_two {μ : Measure α} [IsProbabilityMeasure μ] {N : ℕ} {i j : Fin N} (hij : i ≠ j)
    {h : α × α → ℝ} (hh : Measurable h) :
    ∫ x : Fin N → α, h (x i, x j) ∂(Measure.pi fun _ => μ) = ∫ p, h p ∂μ.prod μ := by
  rw [← map_two hij, integral_map ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable
    hh.aestronglyMeasurable]

theorem map_three {μ : Measure α} [IsProbabilityMeasure μ] {N : ℕ} {i j k : Fin N}
    (hik : i ≠ k) (hjk : j ≠ k) (hij : i ≠ j) :
    Measure.map (fun x : Fin N → α => ((x i, x j), x k)) (Measure.pi fun _ => μ) =
      (μ.prod μ).prod μ := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin N => μ) (X := fun _ => id)
    (fun _ => aemeasurable_id)).indepFun_prodMk (fun i => measurable_pi_apply i) i j k hik hjk
  rw [(indepFun_iff_map_prod_eq_prod_map_map
    (((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable)
    (measurable_pi_apply k).aemeasurable).1 hind, map_two hij,
    (measurePreserving_eval (fun _ : Fin N => μ) k).map_eq]

theorem integral_three {μ : Measure α} [IsProbabilityMeasure μ] {N : ℕ} {i j k : Fin N}
    (hik : i ≠ k) (hjk : j ≠ k) (hij : i ≠ j)
    {h : (α × α) × α → ℝ} (hh : Measurable h) :
    ∫ x : Fin N → α, h ((x i, x j), x k) ∂(Measure.pi fun _ => μ) =
      ∫ q, h q ∂(μ.prod μ).prod μ := by
  rw [← map_three hik hjk hij, integral_map
    (((measurable_pi_apply i).prodMk (measurable_pi_apply j)).prodMk
      (measurable_pi_apply k)).aemeasurable hh.aestronglyMeasurable]


section Meas

variable {E : Type*} [MeasurableSpace E] {b : α → α → E}

theorem measurable_edge (hbm : Measurable (Function.uncurry b)) {N : ℕ} (i j : Fin N) :
    Measurable fun x : Fin N → α => b (x i) (x j) :=
  hbm.comp (f := fun x : Fin N → α => (x i, x j))
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j))

end Meas

section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem intBdd {μ : Measure α} [IsProbabilityMeasure μ] {N : ℕ} {f : (Fin N → α) → ℝ}
    (hf : Measurable f) (C : ℝ) (h : ∀ x, |f x| ≤ C) :
    Integrable f (Measure.pi fun _ : Fin N => μ) :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact h x)

variable {b : α → α → E} {g : α → E}

theorem three_zero {μ : Measure α} [IsProbabilityMeasure μ]
    (hbm : Measurable (Function.uncurry b)) {M : ℝ} (hM : ∀ x y, ‖b x y‖ ≤ M)
    (hb0 : ∀ᵐ x ∂μ, ∫ y, b x y ∂μ = 0) {N : ℕ} {i j k : Fin N}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∫ x : Fin N → α, inner ℝ (b (x i) (x j)) (b (x i) (x k)) ∂(Measure.pi fun _ => μ) = 0 := by
  have hm : Measurable fun q : (α × α) × α => inner ℝ (b q.2 q.1.1) (b q.2 q.1.2) :=
    (hbm.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))).inner
      (hbm.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have hbd : ∀ q : (α × α) × α, ‖inner ℝ (b q.2 q.1.1) (b q.2 q.1.2)‖ ≤ M * M := fun q =>
    (norm_inner_le_norm _ _).trans (mul_le_mul (hM _ _) (hM _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (hM q.2 q.1.1)))
  have e := integral_three (μ := μ) (i := j) (j := k) (k := i) hij.symm hik.symm hjk
    (h := fun q : (α × α) × α => inner ℝ (b q.2 q.1.1) (b q.2 q.1.2)) hm
  simp only at e
  rw [e, integral_prod_symm _ (Integrable.of_bound hm.aestronglyMeasurable _ (ae_of_all _ hbd))]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hb0] with a ha
  have hbc : Measurable fun c => b a c := hbm.comp (f := fun c : α => (a, c)) measurable_prodMk_left
  have hint : ∀ c : α, Integrable (fun c' => b a c') μ := fun c =>
    Integrable.of_bound hbc.aestronglyMeasurable M (ae_of_all _ fun c' => hM a c')
  have h2 : ∀ c : α, ∫ c', inner ℝ (b a c) (b a c') ∂μ = 0 := fun c => by
    rw [integral_inner (hint c), ha, inner_zero_right]
  have hm2 : Measurable fun p : α × α => inner ℝ (b a p.1) (b a p.2) :=
    (hbc.comp measurable_fst).inner (hbc.comp measurable_snd)
  rw [integral_prod _ (Integrable.of_bound hm2.aestronglyMeasurable (M * M)
    (ae_of_all _ fun p => (norm_inner_le_norm _ _).trans (mul_le_mul (hM _ _) (hM _ _)
      (norm_nonneg _) ((norm_nonneg _).trans (hM a p.1)))))]
  simp [h2]

theorem cross_zero {μ : Measure α} [IsProbabilityMeasure μ]
    (hbm : Measurable (Function.uncurry b)) (hgm : Measurable g) {M : ℝ}
    (hM : ∀ x y, ‖b x y‖ ≤ M) {Mg : ℝ} (hMg : ∀ x, ‖g x‖ ≤ Mg)
    (hb0 : ∀ᵐ x ∂μ, ∫ y, b x y ∂μ = 0) {N : ℕ} {i j : Fin N} (hij : i ≠ j) :
    ∫ x : Fin N → α, inner ℝ (b (x i) (x j)) (g (x i)) ∂(Measure.pi fun _ => μ) = 0 := by
  have hm : Measurable fun p : α × α => inner ℝ (b p.1 p.2) (g p.1) :=
    hbm.inner (hgm.comp measurable_fst)
  rw [integral_two (h := fun p : α × α => inner ℝ (b p.1 p.2) (g p.1)) hij hm,
    integral_prod _ (Integrable.of_bound hm.aestronglyMeasurable (M * Mg)
      (ae_of_all _ fun p => (norm_inner_le_norm _ _).trans (mul_le_mul (hM _ _) (hMg _)
        (norm_nonneg _) ((norm_nonneg _).trans (hM p.1 p.2)))))]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hb0] with a ha
  have hbc : Measurable fun c => b a c := hbm.comp (f := fun c : α => (a, c)) measurable_prodMk_left
  have hint : Integrable (fun c' => b a c') μ :=
    Integrable.of_bound hbc.aestronglyMeasurable M (ae_of_all _ fun c' => hM a c')
  have : ∀ c : α, inner ℝ (b a c) (g a) = inner ℝ (g a) (b a c) := fun c => real_inner_comm _ _
  simp_rw [this]
  rw [integral_inner hint, ha, inner_zero_right]
  rfl



theorem force_term {μ : Measure α} [IsProbabilityMeasure μ]
    (hbm : Measurable (Function.uncurry b)) (hgm : Measurable g) {M : ℝ}
    (hM : ∀ x y, ‖b x y‖ ≤ M) {Mg : ℝ} (hMg : ∀ x, ‖g x‖ ≤ Mg)
    (hb0 : ∀ᵐ x ∂μ, ∫ y, b x y ∂μ = 0) {N : ℕ} (hN : 1 ≤ N) (i : Fin N) :
    ∫ x : Fin N → α, ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, b (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 ∂(Measure.pi fun _ => μ) =
      ((N : ℝ) - 1) / (N : ℝ) ^ 2 * ∫ p, ‖b p.1 p.2‖ ^ 2 ∂μ.prod μ +
        (4 * (N : ℝ) ^ 2)⁻¹ * ∫ a, ‖g a‖ ^ 2 ∂μ := by
  set S := Finset.univ.erase i with hS
  have hpt : ∀ x : Fin N → α, ‖(N : ℝ)⁻¹ • ∑ j ∈ S, b (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 =
      (N : ℝ)⁻¹ ^ 2 * ∑ j ∈ S, ∑ k ∈ S, inner ℝ (b (x i) (x j)) (b (x i) (x k)) +
      (N : ℝ)⁻¹ ^ 2 * ∑ j ∈ S, inner ℝ (b (x i) (x j)) (g (x i)) +
      (2 * (N : ℝ))⁻¹ ^ 2 * ‖g (x i)‖ ^ 2 := by
    intro x
    rw [norm_add_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
      Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right, sum_inner,
      ← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
    have : (N : ℝ) ≠ 0 := by positivity
    simp only [mul_inv, inv_pow]
    ring_nf
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hbm' := measurable_edge (N := N) hbm
  have hbd : ∀ (j k : Fin N) (x : Fin N → α), |inner ℝ (b (x i) (x j)) (b (x i) (x k))| ≤ M * M :=
    fun j k x => by
      rw [← Real.norm_eq_abs]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (hM _ _) (hM _ _) (norm_nonneg _)
        ((norm_nonneg _).trans (hM (x i) (x j))))
  have hgd : ∀ (j : Fin N) (x : Fin N → α), |inner ℝ (b (x i) (x j)) (g (x i))| ≤ M * Mg :=
    fun j x => by
      rw [← Real.norm_eq_abs]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul (hM _ _) (hMg _) (norm_nonneg _)
        ((norm_nonneg _).trans (hM (x i) (x j))))
  have hgm' : Measurable fun x : Fin N → α => g (x i) := hgm.comp (measurable_pi_apply i)
  have I1 : ∀ j k : Fin N, Integrable (fun x : Fin N → α =>
      inner ℝ (b (x i) (x j)) (b (x i) (x k))) (Measure.pi fun _ => μ) := fun j k =>
    intBdd ((hbm' i j).inner (hbm' i k)) _ (hbd j k)
  have I2 : ∀ j : Fin N, Integrable (fun x : Fin N → α =>
      inner ℝ (b (x i) (x j)) (g (x i))) (Measure.pi fun _ => μ) := fun j =>
    intBdd ((hbm' i j).inner hgm') _ (hgd j)
  have hdiag : ∀ j ∈ S, ∫ x : Fin N → α, inner ℝ (b (x i) (x j)) (b (x i) (x j))
      ∂(Measure.pi fun _ => μ) = ∫ p, ‖b p.1 p.2‖ ^ 2 ∂μ.prod μ := by
    intro j hj
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    simp_rw [real_inner_self_eq_norm_sq]
    exact integral_two (h := fun p : α × α => ‖b p.1 p.2‖ ^ 2) hij (hbm.norm.pow_const 2)
  have hoff : ∀ j ∈ S, ∀ k ∈ S, ∫ x : Fin N → α, inner ℝ (b (x i) (x j)) (b (x i) (x k))
      ∂(Measure.pi fun _ => μ) = if j = k then ∫ p, ‖b p.1 p.2‖ ^ 2 ∂μ.prod μ else 0 := by
    intro j hj k hk
    split_ifs with h
    · subst h; exact hdiag j hj
    · exact three_zero hbm hM hb0 (Finset.ne_of_mem_erase hj).symm
        (Finset.ne_of_mem_erase hk).symm h
  have hgi : ∫ x : Fin N → α, ‖g (x i)‖ ^ 2 ∂(Measure.pi fun _ => μ) = ∫ a, ‖g a‖ ^ 2 ∂μ := by
    have h := integral_map (μ := Measure.pi fun _ : Fin N => μ)
      (measurable_pi_apply i).aemeasurable (f := fun a : α => ‖g a‖ ^ 2)
      (hgm.norm.pow_const 2).aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq] at h
    exact h.symm
  have hcard : (S.card : ℝ) = (N : ℝ) - 1 := by
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hN, Nat.cast_one]
  simp_rw [hpt]
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => I1 j k)]
  · have e1 : ∑ j ∈ S, ∫ x : Fin N → α, ∑ k ∈ S, inner ℝ (b (x i) (x j)) (b (x i) (x k))
        ∂(Measure.pi fun _ => μ) = (S.card : ℝ) * ∫ p, ‖b p.1 p.2‖ ^ 2 ∂μ.prod μ := by
      rw [Finset.sum_congr rfl (fun j hj => integral_finsetSum _ (fun k _ => I1 j k))]
      rw [Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun k hk => hoff j hj k hk))]
      simp [Finset.sum_ite_eq, Finset.sum_const, nsmul_eq_mul]
    have e2 : ∑ j ∈ S, ∫ x : Fin N → α, inner ℝ (b (x i) (x j)) (g (x i))
        ∂(Measure.pi fun _ => μ) = 0 :=
      Finset.sum_eq_zero fun j hj =>
        cross_zero hbm hgm hM hMg hb0 (Finset.ne_of_mem_erase hj).symm
    rw [e1, integral_finsetSum _ (fun j _ => I2 j), e2, hgi, hcard]
    have : (N : ℝ) ≠ 0 := hNpos.ne'
    field_simp
    ring
  · exact (integrable_finsetSum _ fun j _ => (integrable_finsetSum _ fun k _ => I1 j k)).const_mul _
  · exact (integrable_finsetSum _ fun j _ => I2 j).const_mul _
  · exact ((integrable_finsetSum _ fun j _ => (integrable_finsetSum _ fun k _ => I1 j k)).const_mul _).add
      ((integrable_finsetSum _ fun j _ => I2 j).const_mul _)
  · refine Integrable.const_mul (intBdd (hgm'.norm.pow_const 2) (Mg ^ 2) fun x => ?_) _
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hMg _) 2

omit [CompleteSpace E] in
theorem force_sq_integrable {μ : Measure α} [IsProbabilityMeasure μ]
    (hbm : Measurable (Function.uncurry b)) (hgm : Measurable g) {M : ℝ}
    (hM : ∀ x y, ‖b x y‖ ≤ M) {Mg : ℝ} (hMg : ∀ x, ‖g x‖ ≤ Mg) {N : ℕ} (i : Fin N) :
    Integrable (fun x : Fin N → α => ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, b (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2) (Measure.pi fun _ : Fin N => μ) := by
  have hm : Measurable fun x : Fin N → α => ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
      b (x i) (x j) + (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 := by
    refine Measurable.pow_const (Measurable.norm (Measurable.add ?_ ?_)) 2
    · exact (Finset.measurable_sum _ fun j _ => measurable_edge hbm i j).const_smul _
    · exact (hgm.comp (measurable_pi_apply i)).const_smul _
  refine Integrable.of_bound hm.aestronglyMeasurable
    (((N : ℝ)⁻¹ * ((Finset.univ.erase i).card * M) + (2 * (N : ℝ))⁻¹ * Mg) ^ 2)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le _ _).trans (add_le_add ?_ ?_)) 2
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (by positivity)
    calc ∑ j ∈ Finset.univ.erase i, ‖b (x i) (x j)‖ ≤ ∑ j ∈ Finset.univ.erase i, M :=
          Finset.sum_le_sum fun j _ => hM (x i) (x j)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hMg _) (by positivity)

theorem force_second_moment_core {μ : Measure α} [IsProbabilityMeasure μ]
    (hbm : Measurable (Function.uncurry b)) (hgm : Measurable g) {M : ℝ}
    (hM : ∀ x y, ‖b x y‖ ≤ M) {Mg : ℝ} (hMg : ∀ x, ‖g x‖ ≤ Mg)
    (hb0 : ∀ᵐ x ∂μ, ∫ y, b x y ∂μ = 0) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x : Fin N → α, ∑ i : Fin N, ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, b (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 ∂(Measure.pi fun _ => μ) =
      ((N : ℝ) - 1) / N * ∫ p, ‖b p.1 p.2‖ ^ 2 ∂μ.prod μ +
        (4 * (N : ℝ))⁻¹ * ∫ a, ‖g a‖ ^ 2 ∂μ := by
  rw [integral_finsetSum _ (fun i _ => force_sq_integrable hbm hgm hM hMg i)]
  simp_rw [force_term hbm hgm hM hMg hb0 hN]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

end Core

section Centering

open DGPS

variable {d : ℕ}

/-- Weakly differentiating the centering identity `∫ F(x,y) dμ(y) = 0` in `x` gives
`∫ ∇₁F(x,y) dμ(y) = 0` for Haar-almost every `x`. -/
theorem centered_gradient_ae {μ : Measure (Torus d)} [IsFiniteMeasure μ]
    {F : Torus d → Torus d → ℝ} {B : Torus d → Torus d → Tangent d}
    (hFm : Measurable (Function.uncurry F)) (hBm : Measurable (Function.uncurry B))
    {CF CB : ℝ} (hF : ∀ x y, |F x y| ≤ CF) (hB : ∀ x y, ‖B x y‖ ≤ CB)
    (hw : ∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y))
    (h0 : ∀ x, ∫ y, F x y ∂μ = 0) :
    ∀ᵐ x ∂haar d, ∫ y, B x y ∂μ = 0 := by
  have hBj : ∀ j : Fin d, Measurable fun p : Torus d × Torus d => B p.1 p.2 j := fun j =>
    (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).measurable.comp hBm
  have hBjb : ∀ (j : Fin d) x y, |B x y j| ≤ CB := fun j x y =>
    ((Real.norm_eq_abs _).symm.le.trans (PiLp.norm_apply_le (B x y) j)).trans (hB x y)
  have hcj : ∀ j : Fin d, ∀ᵐ x ∂haar d, ∫ y, B x y j ∂μ = 0 := by
    intro j
    have hmeas : Measurable fun x => ∫ y, B x y j ∂μ :=
      (hBj j).stronglyMeasurable.integral_prod_right'.measurable
    have hmem : MemLp (fun x => ∫ y, B x y j ∂μ) 2 (haar d) := by
      refine memLp_top_of_bound hmeas.aestronglyMeasurable (CB * μ.real Set.univ)
        (ae_of_all _ fun x => ?_) |>.mono_exponent le_top
      rw [Real.norm_eq_abs]
      calc |∫ y, B x y j ∂μ| ≤ ∫ y, |B x y j| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ _y, CB ∂μ := integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
            (integrable_const _) (ae_of_all _ fun y => hBjb j x y)
        _ = CB * μ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]
    refine ae_eq_zero_of_forall_integral_mul_eq_zero hmem fun φ hφ => ?_
    have hφc := hφ.continuous_torus
    have hφp := hφ.continuous_coordPartial j
    obtain ⟨Cφ, hCφ⟩ := isCompact_univ.exists_bound_of_continuousOn hφc.continuousOn
    obtain ⟨Cp, hCp⟩ := isCompact_univ.exists_bound_of_continuousOn hφp.continuousOn
    have i1 : Integrable (Function.uncurry fun (x y : Torus d) => B x y j * φ x)
        ((haar d).prod μ) := by
      refine Integrable.of_bound (f := Function.uncurry fun (x y : Torus d) => B x y j * φ x)
        (((hBj j).mul (hφc.measurable.comp measurable_fst)).aestronglyMeasurable)
        (CB * Cφ) (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs]
      show |B p.1 p.2 j * φ p.1| ≤ CB * Cφ
      rw [abs_mul]
      exact mul_le_mul (hBjb j _ _) ((Real.norm_eq_abs _).symm.le.trans (hCφ p.1 (Set.mem_univ _)))
        (abs_nonneg _) ((abs_nonneg _).trans (hBjb j 0 0))
    have i2 : Integrable (Function.uncurry fun (x y : Torus d) => F x y * coordPartial j φ x)
        ((haar d).prod μ) := by
      refine Integrable.of_bound (f := Function.uncurry fun (x y : Torus d) =>
        F x y * coordPartial j φ x)
        ((hFm.mul (hφp.measurable.comp measurable_fst)).aestronglyMeasurable)
        (CF * Cp) (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs]
      show |F p.1 p.2 * coordPartial j φ p.1| ≤ CF * Cp
      rw [abs_mul]
      exact mul_le_mul (hF _ _) ((Real.norm_eq_abs _).symm.le.trans (hCp p.1 (Set.mem_univ _)))
        (abs_nonneg _) ((abs_nonneg _).trans (hF 0 0))
    have e1 : ∫ x, (∫ y, B x y j ∂μ) * φ x ∂haar d = ∫ x, ∫ y, B x y j * φ x ∂μ ∂haar d := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      exact (integral_mul_const _ _).symm
    have e2 : ∫ x, (∫ y, F x y ∂μ) * coordPartial j φ x ∂haar d =
        ∫ x, ∫ y, F x y * coordPartial j φ x ∂μ ∂haar d := by
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      exact (integral_mul_const _ _).symm
    have e3 : ∫ x, (∫ y, F x y ∂μ) * coordPartial j φ x ∂haar d = 0 := by
      simp [h0]
    rw [e1, integral_integral_swap i1]
    rw [e2, integral_integral_swap i2] at e3
    have e4 : ∀ y, ∫ x, B x y j * φ x ∂haar d = -∫ x, F x y * coordPartial j φ x ∂haar d := by
      intro y
      have := (hw y).ibp φ hφ j
      linarith
    simp_rw [e4]
    rw [integral_neg, e3, neg_zero]
  have hall := ae_all_iff.2 hcj
  filter_upwards [hall] with x hx
  ext j
  have hint : Integrable (fun y => B x y) μ :=
    Integrable.of_bound (hBm.comp (f := fun y : Torus d => (x, y)) measurable_prodMk_left).aestronglyMeasurable
      CB (ae_of_all _ fun y => hB x y)
  have := (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).integral_comp_comm hint
  simpa [hx j] using this.symm

end Centering


section Smoothed

open DGPS DGPS.Lipschitz.KernelApproximation

variable {d : ℕ}

/-- The eigenfunctions are in `W^{1,∞}`. -/
theorem vWlp (S : Spec d) (A : Aux S) (i : ℕ) : IsWeakGradientLp ∞ (S.v i) (A.g i) := by
  have hb : ∀ x, |S.v i x| + ‖A.g i x‖ ≤ A.Kc * (1 + S.lam i) ^ d := A.c1 i
  exact ⟨MemLp.of_bound (S.vc i).aestronglyMeasurable (A.Kc * (1 + S.lam i) ^ d)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]; exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hb x)),
    MemLp.of_bound (A.gm i).aestronglyMeasurable (A.Kc * (1 + S.lam i) ^ d)
      (ae_of_all _ fun x => (le_add_of_nonneg_left (abs_nonneg _)).trans (hb x)),
    (A.gw i).ibp⟩

/-- The diagonal of the smoothed kernel has weak gradient `(∇₁ + ∇₂)K_R(x,x)`. -/
theorem smoothK_diag_wg (S : Spec d) (A : Aux S) (D : KData d) (t : ℝ) (m : ℕ) :
    IsWeakGradient (fun x => smoothK S D t m x x)
      (fun x => smoothG1 S A D t m x x + smoothG2 S A D t m x x) := by
  set c : ℕ → ℕ → ℝ := fun i j => Real.exp (-(t * (S.lam i + S.lam j))) * TK S D.K i j with hc
  have hij : ∀ i j, IsWeakGradient (fun x => S.v i x * S.v j x)
      (fun x => S.v j x • A.g i x + S.v i x • A.g j x) :=
    fun i j => (A.gw i).mul_W1infty (vWlp S A j)
  have hin : ∀ i, IsWeakGradient
      (fun x => ∑ j ∈ Finset.range (m + 1), c i j * (S.v i x * S.v j x))
      (fun x => ∑ j ∈ Finset.range (m + 1), c i j • (S.v j x • A.g i x + S.v i x • A.g j x)) :=
    fun i => wg_sum (Finset.range (m + 1)) (c i) (fun j _ => hij i j)
  have h := wg_sum (Finset.range (m + 1)) (fun _ => (1 : ℝ)) (fun i _ => hin i)
  have e1 : (fun x => smoothK S D t m x x) = fun x => ∑ i ∈ Finset.range (m + 1),
      (1 : ℝ) * ∑ j ∈ Finset.range (m + 1), c i j * (S.v i x * S.v j x) := by
    funext x; simp [smoothK, hc]
  have e2 : (fun x => smoothG1 S A D t m x x + smoothG2 S A D t m x x) = fun x =>
      ∑ i ∈ Finset.range (m + 1), (1 : ℝ) •
        ∑ j ∈ Finset.range (m + 1), c i j • (S.v j x • A.g i x + S.v i x • A.g j x) := by
    funext x
    simp only [smoothG1, smoothG2, one_smul, smul_add, smul_smul, ← Finset.sum_add_distrib, hc]
  rw [e1, e2]
  exact h

end Smoothed

section Identity

open DGPS

variable {d : ℕ}

/-- The exact second moment of the force of `U_N^F` for a centered kernel `F`. -/
theorem force_identity {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hμ : ∀ P : Torus d → Prop, (∀ᵐ x ∂haar d, P x) → ∀ᵐ x ∂μ, P x)
    {F : Torus d → Torus d → ℝ} {B : Torus d → Torus d → Tangent d} {g : Torus d → Tangent d}
    (hFc : Continuous (Function.uncurry F)) (hBm : Measurable (Function.uncurry B))
    {M : ℝ} (hM : ∀ x y, ‖B x y‖ ≤ M) (hgm : Measurable g) {Mg : ℝ} (hMg : ∀ x, ‖g x‖ ≤ Mg)
    (hw : ∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y))
    (h0 : ∀ x, ∫ y, F x y ∂μ = 0) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x : Fin N → Torus d, ∑ i : Fin N, ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 ∂(Measure.pi fun _ => μ) =
      ((N : ℝ) - 1) / N * ∫ p, ‖B p.1 p.2‖ ^ 2 ∂μ.prod μ +
        (4 * (N : ℝ))⁻¹ * ∫ a, ‖g a‖ ^ 2 ∂μ := by
  obtain ⟨CF, hCF⟩ := (isCompact_univ (X := Torus d × Torus d)).exists_bound_of_continuousOn
    hFc.continuousOn
  have hF : ∀ x y, |F x y| ≤ CF := fun x y => by
    simpa [Real.norm_eq_abs] using hCF (x, y) (Set.mem_univ _)
  have hb0 := hμ _ (centered_gradient_ae hFc.measurable hBm hF hM hw h0)
  exact force_second_moment_core hBm hgm hM hMg hb0 hN

end Identity


section Package

open DGPS

variable {d : ℕ}

/-- The force of `U_N^F` is its `H¹(m^N)` gradient, and its exact second moment. -/
theorem force_package {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hμ : ∀ P : Torus d → Prop, (∀ᵐ x ∂haar d, P x) → ∀ᵐ x ∂μ, P x)
    {F : Torus d → Torus d → ℝ} {B : Torus d → Torus d → Tangent d} {g : Torus d → Tangent d}
    (hsymm : ∀ x y, F x y = F y x)
    (hFc : Continuous (Function.uncurry F)) (hBm : Measurable (Function.uncurry B))
    {M : ℝ} (hM : ∀ x y, ‖B x y‖ ≤ M) (hgm : Measurable g) {Mg : ℝ} (hMg : ∀ x, ‖g x‖ ≤ Mg)
    (hw : ∀ y, IsWeakGradient (fun x => F x y) (fun x => B x y))
    (hδ : IsWeakGradient (fun x => F x x) g)
    (h0 : ∀ x, ∫ y, F x y ∂μ = 0) :
    (∀ N : ℕ+, IsParticleHaarWeakGradient N
      (fun x : ParticleSpace d N => ((2 : ℝ) * (N : ℝ))⁻¹ * ∑ i, ∑ j, F (x i) (x j))
      (fun x i => (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i))) ∧
    ∀ N : ℕ, 1 ≤ N →
      ∫ x : Fin N → Torus d, ∑ i : Fin N, ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j) +
        (2 * (N : ℝ))⁻¹ • g (x i)‖ ^ 2 ∂(Measure.pi fun _ => μ) =
      ((N : ℝ) - 1) / N * ∫ p, ‖B p.1 p.2‖ ^ 2 ∂μ.prod μ +
        (4 * (N : ℝ))⁻¹ * ∫ a, ‖g a‖ ^ 2 ∂μ := by
  refine ⟨fun N => ?_, fun N hN => force_identity hμ hFc hBm hM hgm hMg hw h0 hN⟩
  have := DGPS.Lipschitz.df_core (V := fun _ => (0 : ℝ)) (gV := fun _ => 0) hsymm hFc hBm hM hw
    isWeakGradient_zero hδ N
  simpa using this

end Package

section Limit

/-- If `f N = ((N-1)/N) b + (4N)⁻¹ c` for all `N ≥ 1` then `f N → b`. -/
theorem tendsto_of_identity {f : ℕ → ℝ} {b c : ℝ}
    (h : ∀ N : ℕ, 1 ≤ N → f N = ((N : ℝ) - 1) / N * b + (4 * (N : ℝ))⁻¹ * c) :
    Filter.Tendsto f Filter.atTop (nhds b) := by
  have h1 : Filter.Tendsto (fun N : ℕ => 1 / (N : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).mul_const b |>.add
    ((h1.const_mul (1 / 4 : ℝ)).mul_const c)
  rw [show (1 - 0) * b + 1 / 4 * 0 * c = b by ring] at h2
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  rw [h N hN]
  have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  field_simp

end Limit

end DGPS.Lipschitz.CenteredForceMoment

namespace DGPS.Lipschitz

open MeasureTheory Filter Topology
open DGPS DGPS.Lipschitz.KernelApproximation DGPS.Lipschitz.CenteredForceMoment
  DGPS.Lipschitz.CenteredKernelMoments

/-- **Exact force second moment with diagonal correction (LIP014).**

For the spectral data `(S, A)` of LIP011, a centered symmetric kernel `K` (`KData`), and a bounded
measurable weak gradient `gK` of the diagonal `x ↦ K(x,x)`, put `F_R = K - K_R` (`K_R = smoothK`),
`∇₁F_R = G1 - smoothG1` and `∇δ_R = gK - (smoothG1 + smoothG2)(x,x)` (LIP012). Then for every `R`:

* for every `N ≥ 1`, the force `∇ᵢE_{N,R} = N⁻¹ ∑_{j≠i} ∇₁F_R(xᵢ,xⱼ) + (2N)⁻¹ ∇δ_R(xᵢ)` is the
  `H¹(m^N)` weak gradient of `E_{N,R} = U_N^{F_R} = (2N)⁻¹ ∑_{i,j} F_R(xᵢ,xⱼ)` (LIP004);
* `∫ |∇E_{N,R}|² dQ_N = ((N-1)/N) ‖∇₁F_R‖²_{L²(μ²)} + (4N)⁻¹ ‖∇δ_R‖²_{L²(μ)}`, `Q_N = μ^{⊗N}`;
* as `N → ∞` this tends to `‖∇₁F_R‖²_{L²(μ²)}`;
* `limsup_N` of it tends to `0` as `R → ∞`. -/
theorem exact_force_second_moment_with_diagonal_correction {d : ℕ}
    {Φ : Torus d → ℝ} {LΦ : ℝ} (hd : 0 < d) (hL : 0 ≤ LΦ)
    (hΦ : TorusLipschitzWith LΦ Φ) {b : Torus d → Tangent d}
    (hb : IsWeakGradient (fun x => Real.log (WeightedGenerator.gibbsW Φ x)) b) :
    ∃ (S : Spec d) (A : Aux S), S.w = WeightedGenerator.gibbsW Φ ∧
      ∀ D : KData d, (∀ y, ∫ x, D.K x y ∂S.mu = 0) → (∀ x y, D.K x y = D.K y x) →
      ∀ gK : Torus d → Tangent d, Measurable gK → (∃ M : ℝ, ∀ x, ‖gK x‖ ≤ M) →
        IsWeakGradient (fun x => D.K x x) gK →
        ∃ (t : ℕ → ℝ) (m : ℕ → ℕ), (∀ R, 0 < t R) ∧ Antitone t ∧
          Tendsto t atTop (𝓝 0) ∧ StrictMono m ∧
          (∀ R (N : ℕ+), IsParticleHaarWeakGradient N
            (fun x : ParticleSpace d N => ((2 : ℝ) * (N : ℝ))⁻¹ * ∑ i, ∑ j,
              (D.K (x i) (x j) - smoothK S D (t R) (m R) (x i) (x j)))
            (fun x i => (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
              (2 * (N : ℝ))⁻¹ • (gK (x i) -
                (smoothG1 S A D (t R) (m R) (x i) (x i) +
                  smoothG2 S A D (t R) (m R) (x i) (x i))))) ∧
          (∀ R (N : ℕ), 1 ≤ N →
            ∫ x : Fin N → Torus d, ∑ i : Fin N,
                ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                    (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
                  (2 * (N : ℝ))⁻¹ • (gK (x i) -
                    (smoothG1 S A D (t R) (m R) (x i) (x i) +
                      smoothG2 S A D (t R) (m R) (x i) (x i)))‖ ^ 2
                ∂(Measure.pi fun _ => S.mu) =
              ((N : ℝ) - 1) / N *
                  ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu +
                (4 * (N : ℝ))⁻¹ * ∫ a, ‖gK a - (smoothG1 S A D (t R) (m R) a a +
                  smoothG2 S A D (t R) (m R) a a)‖ ^ 2 ∂S.mu) ∧
          (∀ R, Tendsto (fun N : ℕ =>
            ∫ x : Fin N → Torus d, ∑ i : Fin N,
                ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                    (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
                  (2 * (N : ℝ))⁻¹ • (gK (x i) -
                    (smoothG1 S A D (t R) (m R) (x i) (x i) +
                      smoothG2 S A D (t R) (m R) (x i) (x i)))‖ ^ 2
                ∂(Measure.pi fun _ => S.mu)) atTop
            (𝓝 (∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu))) ∧
          Tendsto (fun R => limsup (fun N : ℕ =>
            ∫ x : Fin N → Torus d, ∑ i : Fin N,
                ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                    (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
                  (2 * (N : ℝ))⁻¹ • (gK (x i) -
                    (smoothG1 S A D (t R) (m R) (x i) (x i) +
                      smoothG2 S A D (t R) (m R) (x i) (x i)))‖ ^ 2
                ∂(Measure.pi fun _ => S.mu)) atTop) atTop (𝓝 0) := by
  obtain ⟨S, A, hw, hrest⟩ := product_form_parseval_and_smoothed_finite_rank_kernels hd hL hΦ hb
  refine ⟨S, A, hw, fun D hc hsym gK hgm ⟨Mgk, hMgk⟩ hδK => ?_⟩
  obtain ⟨-, t, m, C, ht, hanti, htend, hm, hC, hK, hG1, hG2, -, -, -, hconv⟩ := hrest D hc hsym
  have : IsProbabilityMeasure S.mu := ⟨by
    have h := S.real_univ
    rwa [measureReal_def, ENNReal.toReal_eq_one_iff] at h⟩
  have key : ∀ R, (∀ N : ℕ+, IsParticleHaarWeakGradient N
            (fun x : ParticleSpace d N => ((2 : ℝ) * (N : ℝ))⁻¹ * ∑ i, ∑ j,
              (D.K (x i) (x j) - smoothK S D (t R) (m R) (x i) (x j)))
            (fun x i => (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
              (2 * (N : ℝ))⁻¹ • (gK (x i) -
                (smoothG1 S A D (t R) (m R) (x i) (x i) +
                  smoothG2 S A D (t R) (m R) (x i) (x i))))) ∧
          (∀ N : ℕ, 1 ≤ N →
            ∫ x : Fin N → Torus d, ∑ i : Fin N,
                ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                    (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
                  (2 * (N : ℝ))⁻¹ • (gK (x i) -
                    (smoothG1 S A D (t R) (m R) (x i) (x i) +
                      smoothG2 S A D (t R) (m R) (x i) (x i)))‖ ^ 2
                ∂(Measure.pi fun _ => S.mu) =
              ((N : ℝ) - 1) / N *
                  ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu +
                (4 * (N : ℝ))⁻¹ * ∫ a, ‖gK a - (smoothG1 S A D (t R) (m R) a a +
                  smoothG2 S A D (t R) (m R) a a)‖ ^ 2 ∂S.mu) := by
    intro R
    have hG1m : Measurable (Function.uncurry (smoothG1 S A D (t R) (m R))) := by
      rw [smoothG1_eq]; exact G1fin_meas S A D (t R) (m R + 1)
    have hG2m : Measurable (Function.uncurry (smoothG2 S A D (t R) (m R))) := by
      rw [smoothG2_eq]; exact G2fin_meas S A D (t R) (m R + 1)
    have hdiag : Measurable fun x : Torus d => (x, x) := measurable_id.prodMk measurable_id
    refine force_package (F := fun x y => D.K x y - smoothK S D (t R) (m R) x y)
      (B := fun x y => D.G1 x y - smoothG1 S A D (t R) (m R) x y)
      (g := fun x => gK x - (smoothG1 S A D (t R) (m R) x x + smoothG2 S A D (t R) (m R) x x))
      (M := D.B + C) (Mg := Mgk + (C + C)) (fun P h => S.ae_mu h) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x y
      rw [hsym x y, smoothK_symm S D hsym _ _ x y]
    · exact D.Kc.sub (smoothK_continuous S D _ _)
    · exact D.G1m.sub hG1m
    · intro x y
      exact (norm_sub_le _ _).trans (add_le_add (D.G1b x y) (hG1 R x y))
    · exact hgm.sub ((hG1m.comp hdiag).add (hG2m.comp hdiag))
    · intro x
      exact (norm_sub_le _ _).trans (add_le_add (hMgk x)
        ((norm_add_le _ _).trans (add_le_add (hG1 R x x) (hG2 R x x))))
    · intro y
      refine wg_sub (D.g1 y) ?_
      have := Kfin_wg1 S A D (t R) (m R + 1) y
      simpa only [smoothK_eq, smoothG1_eq] using this
    · exact wg_sub hδK (smoothK_diag_wg S A D _ _)
    · intro x
      have h1 : Integrable (fun y => D.K x y) S.mu :=
        S.int_cont (D.Kc.comp (continuous_const.prodMk continuous_id))
      have h2 : Integrable (fun y => smoothK S D (t R) (m R) x y) S.mu :=
        S.int_cont ((smoothK_continuous S D (t R) (m R)).comp
          (continuous_const.prodMk continuous_id))
      rw [integral_sub h1 h2]
      have e1 : ∫ y, D.K x y ∂S.mu = 0 := by
        simp_rw [hsym x]; exact hc x
      have e2 : ∫ y, smoothK S D (t R) (m R) x y ∂S.mu = 0 := by
        simp_rw [smoothK_symm S D hsym _ _ x]
        exact smoothK_centered S D A.v0 hc _ _ x
      rw [e1, e2, sub_zero]
  have hb0 : Tendsto (fun R => ∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2
      ∂S.mu.prod S.mu) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun R => integral_nonneg fun p => sq_nonneg _) (fun R => ?_)
    have ha : 0 ≤ ∫ p, (D.K p.1 p.2 - smoothK S D (t R) (m R) p.1 p.2) ^ 2 ∂S.mu.prod S.mu :=
      integral_nonneg fun p => sq_nonneg _
    have hc2 : 0 ≤ ∫ p, ‖D.G2 p.1 p.2 - smoothG2 S A D (t R) (m R) p.1 p.2‖ ^ 2
        ∂S.mu.prod S.mu := integral_nonneg fun p => sq_nonneg _
    show _ ≤ _ + _ + _
    linarith
  have hlim : ∀ R, Tendsto (fun N : ℕ =>
            ∫ x : Fin N → Torus d, ∑ i : Fin N,
                ‖(N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i,
                    (D.G1 (x i) (x j) - smoothG1 S A D (t R) (m R) (x i) (x j)) +
                  (2 * (N : ℝ))⁻¹ • (gK (x i) -
                    (smoothG1 S A D (t R) (m R) (x i) (x i) +
                      smoothG2 S A D (t R) (m R) (x i) (x i)))‖ ^ 2
                ∂(Measure.pi fun _ => S.mu)) atTop
            (𝓝 (∫ p, ‖D.G1 p.1 p.2 - smoothG1 S A D (t R) (m R) p.1 p.2‖ ^ 2 ∂S.mu.prod S.mu)) :=
    fun R => tendsto_of_identity (key R).2
  exact ⟨t, m, ht, hanti, htend, hm, fun R => (key R).1, fun R => (key R).2, hlim,
    hb0.congr fun R => ((hlim R).limsup_eq).symm⟩

end DGPS.Lipschitz
