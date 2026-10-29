import DGPS.Particle.ProductRecovery
import DGPS.Particle.DiagonalForce

open MeasureTheory ProbabilityTheory Filter Topology
open DGPS DGPS.Lipschitz
open scoped ENNReal

namespace DGPS.Particle.ProductForceVariance

section Core

variable {α : Type*} [MeasurableSpace α] {d : ℕ}

theorem measurePreserving_update_pi {n : ℕ} (μ : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) :
    MeasurePreserving (fun p : (Fin n → α) × α => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  refine ⟨measurable_update', ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have : (fun p : (Fin n → α) × α => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi s) =
      (Set.univ.pi (Function.update s i Set.univ)) ×ˢ s i := by
    ext ⟨x, t⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun k => ?_, by simpa using h i⟩
      by_cases hk : k = i
      · subst hk; simp
      · simpa [Function.update_of_ne hk] using h k
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i
      · subst hk; simpa using h2
      · have := h1 k
        simpa [Function.update_of_ne hk] using this
  rw [this, Measure.prod_prod, Measure.pi_pi]
  have e1 : ∏ k, μ k (Function.update s i Set.univ k) = ∏ k ∈ Finset.univ.erase i, μ k (s k) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    simp only [Function.update_self, measure_univ, one_mul]
    refine Finset.prod_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [e1, mul_comm, Finset.mul_prod_erase Finset.univ (fun k => μ k (s k)) (Finset.mem_univ i)]

theorem integral_pi_update_split {n : ℕ} (μ : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) {h : (Fin n → α) → ℝ}
    (hh : Integrable h (Measure.pi μ)) :
    ∫ x, h x ∂Measure.pi μ =
      ∫ t, ∫ z, h (Function.update z i t) ∂Measure.pi μ ∂μ i := by
  have hmp := measurePreserving_update_pi μ i
  have hint : Integrable (h ∘ fun p : (Fin n → α) × α => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) := (hmp.integrable_comp hh.aestronglyMeasurable).2 hh
  calc ∫ x, h x ∂Measure.pi μ
      = ∫ x, h x ∂((Measure.pi μ).prod (μ i)).map
          (fun p : (Fin n → α) × α => Function.update p.1 i p.2) := by
        rw [hmp.map_eq]
    _ = ∫ p, h (Function.update p.1 i p.2) ∂(Measure.pi μ).prod (μ i) :=
        integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hh.aestronglyMeasurable)
    _ = _ := integral_prod_symm _ hint

theorem integral_pi_eval {n : ℕ} (μ : Fin n → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (j : Fin n) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] (g : α → F) (hg : Measurable g) :
    ∫ z, g (z j) ∂Measure.pi μ = ∫ y, g y ∂μ j := by
  have hi : Measure.map (fun ω : Fin n → α => ω j) (Measure.pi μ) = μ j :=
    (measurePreserving_eval μ j).map_eq
  conv_rhs => rw [← hi]
  rw [integral_map (measurable_pi_apply j).aemeasurable hg.aestronglyMeasurable]

theorem integrable_bdd_pi {n : ℕ} (μ : Fin n → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    {F : Type*} [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] {f : (Fin n → α) → F} (hf : Measurable f) {C : ℝ}
    (hb : ∀ z, ‖f z‖ ≤ C) :
    Integrable f (Measure.pi μ) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hb)

theorem integral_norm_sq_sum_pi {n : ℕ} (μ : Fin n → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (H : Fin n → α → Tangent d) (hH : ∀ j, Measurable (H j)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ j y, ‖H j y‖ ≤ M) (h0 : ∀ j, ∫ y, H j y ∂μ j = 0) (s : Finset (Fin n)) :
    ∫ z, ‖∑ j ∈ s, H j (z j)‖ ^ 2 ∂Measure.pi μ = ∑ j ∈ s, ∫ y, ‖H j y‖ ^ 2 ∂μ j := by
  have hint : ∀ j l, Integrable (fun z : Fin n → α => inner ℝ (H j (z j)) (H l (z l)))
      (Measure.pi μ) := by
    intro j l
    refine integrable_bdd_pi μ (C := M * M) ?_ fun z => ?_
    · have h1 : Measurable fun z : Fin n → α => H j (z j) := (hH j).comp (measurable_pi_apply j)
      have h2 : Measurable fun z : Fin n → α => H l (z l) := (hH l).comp (measurable_pi_apply l)
      exact h1.inner h2
    · calc ‖inner ℝ (H j (z j)) (H l (z l))‖ ≤ ‖H j (z j)‖ * ‖H l (z l)‖ := norm_inner_le_norm _ _
        _ ≤ M * M := mul_le_mul (hb _ _) (hb _ _) (norm_nonneg _) hM
  have expand : ∀ z : Fin n → α, ‖∑ j ∈ s, H j (z j)‖ ^ 2 =
      ∑ j ∈ s, ∑ l ∈ s, inner ℝ (H j (z j)) (H l (z l)) := by
    intro z
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sum]
  simp_rw [expand]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hint j l]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun l _ => hint j l, Finset.sum_eq_single j]
  · have : ∀ z : Fin n → α, inner ℝ (H j (z j)) (H j (z j)) = ‖H j (z j)‖ ^ 2 := fun z =>
      real_inner_self_eq_norm_sq _
    simp_rw [this]
    exact integral_pi_eval μ j (fun y => ‖H j y‖ ^ 2) ((hH j).norm.pow_const 2)
  · intro l _ hlj
    have hg : Measurable fun p : α × α => inner ℝ (H j p.1) (H l p.2) :=
      ((hH j).comp measurable_fst).inner ((hH l).comp measurable_snd)
    rw [DGPS.Particle.ProductRecovery.integral_pi_pair' n μ (Ne.symm hlj) (fun p => inner ℝ (H j p.1) (H l p.2)) hg]
    have hgi : Integrable (fun p : α × α => inner ℝ (H j p.1) (H l p.2))
        ((μ j).prod (μ l)) := by
      refine Integrable.of_bound hg.aestronglyMeasurable (M * M) (Eventually.of_forall fun p => ?_)
      calc ‖inner ℝ (H j p.1) (H l p.2)‖ ≤ ‖H j p.1‖ * ‖H l p.2‖ := norm_inner_le_norm _ _
        _ ≤ M * M := mul_le_mul (hb _ _) (hb _ _) (norm_nonneg _) hM
    rw [integral_prod _ hgi]
    have : ∀ y, ∫ y', inner ℝ (H j y) (H l y') ∂μ l = 0 := by
      intro y
      have hi : Integrable (H l) (μ l) :=
        Integrable.of_bound (hH l).aestronglyMeasurable M (Eventually.of_forall (hb l))
      rw [integral_inner hi, h0 l, inner_zero_right]
    simp [this]
  · intro h; exact absurd hj h

theorem integrable_bdd {μ : Measure α} [IsProbabilityMeasure μ] {G : α → Tangent d}
    (hG : Measurable G) {M : ℝ} (hb : ∀ y, ‖G y‖ ≤ M) : Integrable G μ :=
  Integrable.of_bound hG.aestronglyMeasurable M (Eventually.of_forall hb)

theorem integrable_sq_bdd {μ : Measure α} [IsProbabilityMeasure μ] {G : α → Tangent d}
    (hG : Measurable G) {M : ℝ} (hb : ∀ y, ‖G y‖ ≤ M) :
    Integrable (fun y => ‖G y‖ ^ 2) μ :=
  Integrable.of_bound (hG.norm.pow_const 2).aestronglyMeasurable (M ^ 2)
    (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb y) 2)

theorem variance_eq_sub {μ : Measure α} [IsProbabilityMeasure μ] {G : α → Tangent d}
    (hG : Measurable G) {M : ℝ} (hb : ∀ y, ‖G y‖ ≤ M) :
    ∫ y, ‖G y - ∫ y', G y' ∂μ‖ ^ 2 ∂μ = ∫ y, ‖G y‖ ^ 2 ∂μ - ‖∫ y, G y ∂μ‖ ^ 2 := by
  set m := ∫ y, G y ∂μ with hm
  have hi : Integrable G μ := integrable_bdd hG hb
  have hsq := integrable_sq_bdd (μ := μ) hG hb
  have hinner : Integrable (fun y => inner ℝ m (G y)) μ := hi.const_inner m
  calc ∫ y, ‖G y - m‖ ^ 2 ∂μ = ∫ y, (‖G y‖ ^ 2 - 2 * inner ℝ m (G y) + ‖m‖ ^ 2) ∂μ := by
        congr 1; funext y; rw [norm_sub_sq_real, real_inner_comm m (G y)]
    _ = ∫ y, ‖G y‖ ^ 2 ∂μ - ‖m‖ ^ 2 := by
        have h2 : Integrable (fun y => 2 * inner ℝ m (G y)) μ := hinner.const_mul 2
        have h3 : Integrable (fun y => ‖G y‖ ^ 2 - 2 * inner ℝ m (G y)) μ := hsq.sub h2
        rw [integral_add h3 (integrable_const _), integral_sub hsq h2, integral_const_mul,
          integral_inner hi, integral_const]
        rw [← hm, real_inner_self_eq_norm_sq]
        simp
        ring

theorem integral_sum_pi_zero {n : ℕ} (μ : Fin n → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (H : Fin n → α → Tangent d) (hH : ∀ j, Measurable (H j)) {M : ℝ}
    (hb : ∀ j y, ‖H j y‖ ≤ M) (h0 : ∀ j, ∫ y, H j y ∂μ j = 0) (s : Finset (Fin n)) :
    ∫ z, ∑ j ∈ s, H j (z j) ∂Measure.pi μ = 0 := by
  have hi : ∀ j ∈ s, Integrable (fun z : Fin n → α => H j (z j)) (Measure.pi μ) := fun j _ =>
    integrable_bdd_pi μ ((hH j).comp (measurable_pi_apply j)) (fun z => hb j (z j))
  rw [integral_finsetSum s hi]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_pi_eval μ j (H j) (hH j), h0 j]

theorem core_sq {n : ℕ} (μ : Fin n → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (H : Fin n → α → Tangent d) (hH : ∀ j, Measurable (H j)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ j y, ‖H j y‖ ≤ M) (h0 : ∀ j, ∫ y, H j y ∂μ j = 0) (s : Finset (Fin n))
    (m : Tangent d) :
    ∫ z, ‖m + ∑ j ∈ s, H j (z j)‖ ^ 2 ∂Measure.pi μ =
      ‖m‖ ^ 2 + ∑ j ∈ s, ∫ y, ‖H j y‖ ^ 2 ∂μ j := by
  set T : (Fin n → α) → Tangent d := fun z => ∑ j ∈ s, H j (z j) with hT
  have hTm : Measurable T :=
    Finset.measurable_sum _ fun j _ => (hH j).comp (measurable_pi_apply j)
  have hTb : ∀ z, ‖T z‖ ≤ s.card * M := fun z => (norm_sum_le _ _).trans (by
    calc ∑ j ∈ s, ‖H j (z j)‖ ≤ ∑ _j ∈ s, M := Finset.sum_le_sum fun j _ => hb _ _
      _ = s.card * M := by simp)
  have hTi : Integrable T (Measure.pi μ) := integrable_bdd_pi μ hTm hTb
  have hT0 : ∫ z, T z ∂Measure.pi μ = 0 := integral_sum_pi_zero μ H hH hb h0 s
  have hsq := integral_norm_sq_sum_pi μ H hH hM hb h0 s
  have hTsq : Integrable (fun z => ‖T z‖ ^ 2) (Measure.pi μ) :=
    integrable_bdd_pi μ (hTm.norm.pow_const 2) (C := ((s.card : ℝ) * M) ^ 2) (fun z => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hTb z) 2)
  have hin : Integrable (fun z => inner ℝ m (T z)) (Measure.pi μ) := hTi.const_inner m
  calc ∫ z, ‖m + T z‖ ^ 2 ∂Measure.pi μ
      = ∫ z, (‖m‖ ^ 2 + 2 * inner ℝ m (T z) + ‖T z‖ ^ 2) ∂Measure.pi μ := by
        congr 1; funext z; rw [norm_add_sq_real]
    _ = ‖m‖ ^ 2 + ∑ j ∈ s, ∫ y, ‖H j y‖ ^ 2 ∂μ j := by
        have h2 : Integrable (fun z => 2 * inner ℝ m (T z)) (Measure.pi μ) := hin.const_mul 2
        have h3 : Integrable (fun z => ‖m‖ ^ 2 + 2 * inner ℝ m (T z)) (Measure.pi μ) :=
          (integrable_const _).add h2
        rw [integral_add h3 hTsq, integral_add (integrable_const _) h2, integral_const_mul,
          integral_inner hTi, hT0]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, inner_zero_right, mul_zero,
          add_zero]
        rw [← hsq]

section Score

open DGPS.Particle.ProductRecovery

variable {q : ℕ} {N : ℕ+}

theorem sum_label {G : Type*} [AddCommMonoid G] [Module ℝ G] (σ : Fin N → Fin q)
    (f : Fin q → G) :
    (N : ℝ)⁻¹ • ∑ j, f (σ j) = ∑ t, proportion σ t • f t := by
  have h : ∑ j, f (σ j) = ∑ t, typeCount σ t • f t := by
    rw [← Finset.sum_fiberwise Finset.univ σ (fun j => f (σ j))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f t) (fun j hj => by rw [(Finset.mem_filter.1 hj).2])]
    simp [typeCount]
  rw [h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  simp [proportion, div_eq_inv_mul]

/-- The relative score at label `i`: `A_{σ i}(x_i) + N⁻¹ ∑_{j ≠ i} B(x_i, x_j)`. -/
noncomputable def score (a : Fin q → α → Tangent d) (B : α → α → Tangent d)
    (σ : Fin N → Fin q) (i : Fin N) (z : Fin N → α) : Tangent d :=
  a (σ i) (z i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (z i) (z j)

/-- The convolution `B * μ` at `x`. -/
noncomputable def kernelMean (μ : Measure α) (B : α → α → Tangent d) (x : α) : Tangent d :=
  ∫ y, B x y ∂μ

/-- The claimed conditional mean `A_s + B * ρ̄_N - N⁻¹ B * ρ_s` of the score of a species `s`
label. -/
noncomputable def meanForce (μ : Fin q → Measure α) (a : Fin q → α → Tangent d)
    (B : α → α → Tangent d) (σ : Fin N → Fin q) (s : Fin q) (x : α) : Tangent d :=
  a s x + ∑ t, proportion σ t • kernelMean (μ t) B x - (N : ℝ)⁻¹ • kernelMean (μ s) B x

omit [MeasurableSpace α] in
theorem score_update (a : Fin q → α → Tangent d) (B : α → α → Tangent d) (σ : Fin N → Fin q)
    (i : Fin N) (z : Fin N → α) (x : α) :
    score a B σ i (Function.update z i x) =
      a (σ i) x + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B x (z j) := by
  have h : ∀ j ∈ Finset.univ.erase i,
      B (Function.update z i x i) (Function.update z i x j) = B x (z j) := fun j hj => by
    rw [Function.update_self, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  unfold score
  rw [Finset.sum_congr rfl h, Function.update_self]

theorem meanForce_eq (μ : Fin q → Measure α) (a : Fin q → α → Tangent d)
    (B : α → α → Tangent d) (σ : Fin N → Fin q) (i : Fin N) (x : α) :
    meanForce μ a B σ (σ i) x =
      a (σ i) x + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, kernelMean (μ (σ j)) B x := by
  unfold meanForce
  rw [← sum_label σ (fun t => kernelMean (μ t) B x),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), smul_add]
  abel

/-- The centred, rescaled fluctuation of the `j`-th label at the conditioning value `x`. -/
noncomputable def fluct (μ : Fin q → Measure α) (B : α → α → Tangent d) (σ : Fin N → Fin q)
    (x : α) (j : Fin N) (y : α) : Tangent d :=
  (N : ℝ)⁻¹ • (B x y - kernelMean (μ (σ j)) B x)

theorem score_update_decomp (μ : Fin q → Measure α) (a : Fin q → α → Tangent d)
    (B : α → α → Tangent d) (σ : Fin N → Fin q) (i : Fin N) (z : Fin N → α) (x : α) :
    score a B σ i (Function.update z i x) =
      meanForce μ a B σ (σ i) x + ∑ j ∈ Finset.univ.erase i, fluct μ B σ x j (z j) := by
  rw [score_update, meanForce_eq]
  unfold fluct
  simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
  abel

theorem integrable_sum_pi {n : ℕ} (μ : Fin n → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (H : Fin n → α → Tangent d) (hH : ∀ j, Measurable (H j)) {M : ℝ}
    (hb : ∀ j y, ‖H j y‖ ≤ M) (s : Finset (Fin n)) :
    Integrable (fun z : Fin n → α => ∑ j ∈ s, H j (z j)) (Measure.pi μ) :=
  integrable_bdd_pi μ (C := s.card * M)
    (Finset.measurable_sum _ fun j _ => (hH j).comp (measurable_pi_apply j)) fun z =>
    (norm_sum_le _ _).trans (by
      calc ∑ j ∈ s, ‖H j (z j)‖ ≤ ∑ _j ∈ s, M := Finset.sum_le_sum fun j _ => hb _ _
        _ = s.card * M := by simp)

section Cond

variable {M : ℝ}

theorem norm_kernelMean_le (μ : Measure α) [IsProbabilityMeasure μ] {B : α → α → Tangent d}
    (hB : ∀ x y, ‖B x y‖ ≤ M) (x : α) : ‖kernelMean μ B x‖ ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => B x y) (C := M)
    (Eventually.of_forall (hB x))
  simpa [kernelMean] using this

theorem measurable_fluct (μ : Fin q → Measure α) {B : α → α → Tangent d}
    (hBm : Measurable (Function.uncurry B)) (σ : Fin N → Fin q) (x : α) (j : Fin N) :
    Measurable (fluct μ B σ x j) := by
  have hBx : Measurable (B x) := Measurable.of_uncurry_left hBm
  unfold fluct
  exact (hBx.sub measurable_const).const_smul (N : ℝ)⁻¹

theorem norm_fluct_le (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    {B : α → α → Tangent d} (hB : ∀ x y, ‖B x y‖ ≤ M) (σ : Fin N → Fin q) (x : α) (j : Fin N)
    (y : α) : ‖fluct μ B σ x j y‖ ≤ (N : ℝ)⁻¹ * (2 * M) := by
  unfold fluct
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
  gcongr
  have := norm_kernelMean_le (μ (σ j)) hB x
  have := hB x y
  linarith [norm_sub_le (B x y) (kernelMean (μ (σ j)) B x)]

theorem integral_fluct (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    {B : α → α → Tangent d} (hBm : Measurable (Function.uncurry B))
    (hB : ∀ x y, ‖B x y‖ ≤ M) (σ : Fin N → Fin q) (x : α) (j : Fin N) :
    ∫ y, fluct μ B σ x j y ∂μ (σ j) = 0 := by
  have hi : Integrable (B x) (μ (σ j)) := integrable_bdd (Measurable.of_uncurry_left hBm) (hB x)
  unfold fluct
  rw [integral_smul, integral_sub hi (integrable_const _), integral_const]
  simp [kernelMean]

theorem integral_sq_fluct (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    {B : α → α → Tangent d} (hBm : Measurable (Function.uncurry B))
    (hB : ∀ x y, ‖B x y‖ ≤ M) (σ : Fin N → Fin q) (x : α) (j : Fin N) :
    0 ≤ ∫ y, ‖fluct μ B σ x j y‖ ^ 2 ∂μ (σ j) ∧
      ∫ y, ‖fluct μ B σ x j y‖ ^ 2 ∂μ (σ j) ≤ ((N : ℝ)⁻¹) ^ 2 * M ^ 2 := by
  refine ⟨integral_nonneg fun y => sq_nonneg _, ?_⟩
  have hBx : Measurable (B x) := Measurable.of_uncurry_left hBm
  have h1 : ∀ y, ‖fluct μ B σ x j y‖ ^ 2 =
      ((N : ℝ)⁻¹) ^ 2 * ‖B x y - ∫ y', B x y' ∂μ (σ j)‖ ^ 2 := fun y => by
    unfold fluct kernelMean
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)), mul_pow]
  simp_rw [h1]
  rw [integral_const_mul, variance_eq_sub hBx (hB x)]
  gcongr
  have h2 : ∫ y, ‖B x y‖ ^ 2 ∂μ (σ j) ≤ M ^ 2 := by
    have := integral_mono (integrable_sq_bdd (μ := μ (σ j)) hBx (hB x))
      (integrable_const (M ^ 2)) (fun y => pow_le_pow_left₀ (norm_nonneg _) (hB x y) 2)
    simpa using this
  linarith [sq_nonneg ‖∫ y, B x y ∂μ (σ j)‖]

theorem sum_sq_fluct_le (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    {B : α → α → Tangent d} (hBm : Measurable (Function.uncurry B))
    (hB : ∀ x y, ‖B x y‖ ≤ M) (σ : Fin N → Fin q) (i : Fin N) (x : α) :
    ∑ j ∈ Finset.univ.erase i, ∫ y, ‖fluct μ B σ x j y‖ ^ 2 ∂μ (σ j) ≤ M ^ 2 / N := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 N.pos
  calc ∑ j ∈ Finset.univ.erase i, ∫ y, ‖fluct μ B σ x j y‖ ^ 2 ∂μ (σ j)
      ≤ ∑ _j ∈ Finset.univ.erase i, ((N : ℝ)⁻¹) ^ 2 * M ^ 2 :=
        Finset.sum_le_sum fun j _ => (integral_sq_fluct μ hBm hB σ x j).2
    _ = ((N : ℕ) - 1 : ℕ) * (((N : ℝ)⁻¹) ^ 2 * M ^ 2) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp
    _ ≤ (N : ℝ) * (((N : ℝ)⁻¹) ^ 2 * M ^ 2) := by
        gcongr
        exact_mod_cast Nat.sub_le _ _
    _ = M ^ 2 / N := by field_simp

/-- The conditional variance of the score of label `i`, given `X_i = x`. -/
noncomputable def condVar (μ : Fin q → Measure α) (a : Fin q → α → Tangent d)
    (B : α → α → Tangent d) (σ : Fin N → Fin q) (i : Fin N) (x : α) : ℝ :=
  ∫ z, ‖score a B σ i (Function.update z i x) - meanForce μ a B σ (σ i) x‖ ^ 2
    ∂Measure.pi fun j => μ (σ j)

theorem condMean_eq (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    (a : Fin q → α → Tangent d) {B : α → α → Tangent d}
    (hBm : Measurable (Function.uncurry B)) (hB : ∀ x y, ‖B x y‖ ≤ M) (σ : Fin N → Fin q)
    (i : Fin N) (x : α) :
    ∫ z, score a B σ i (Function.update z i x) ∂(Measure.pi fun j => μ (σ j)) =
      meanForce μ a B σ (σ i) x := by
  simp_rw [score_update_decomp μ a B σ i _ x]
  rw [integral_add (integrable_const _)
    (integrable_sum_pi (fun j => μ (σ j)) (fluct μ B σ x) (measurable_fluct μ hBm σ x)
      (fun j y => norm_fluct_le μ hB σ x j y) _),
    integral_const, integral_sum_pi_zero (fun j => μ (σ j)) (fluct μ B σ x)
      (measurable_fluct μ hBm σ x) (fun j y => norm_fluct_le μ hB σ x j y)
      (fun j => integral_fluct μ hBm hB σ x j)]
  simp

theorem condVar_eq (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    (a : Fin q → α → Tangent d) {B : α → α → Tangent d}
    (hBm : Measurable (Function.uncurry B)) (hM : 0 ≤ M) (hB : ∀ x y, ‖B x y‖ ≤ M)
    (σ : Fin N → Fin q) (i : Fin N) (x : α) :
    condVar μ a B σ i x = ∑ j ∈ Finset.univ.erase i, ∫ y, ‖fluct μ B σ x j y‖ ^ 2 ∂μ (σ j) := by
  unfold condVar
  simp_rw [score_update_decomp μ a B σ i _ x, add_sub_cancel_left]
  exact integral_norm_sq_sum_pi (fun j => μ (σ j)) (fluct μ B σ x) (measurable_fluct μ hBm σ x)
    (by positivity) (fun j y => norm_fluct_le μ hB σ x j y)
    (fun j => integral_fluct μ hBm hB σ x j) _

theorem condVar_bounds (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    (a : Fin q → α → Tangent d) {B : α → α → Tangent d}
    (hBm : Measurable (Function.uncurry B)) (hM : 0 ≤ M) (hB : ∀ x y, ‖B x y‖ ≤ M)
    (σ : Fin N → Fin q) (i : Fin N) (x : α) :
    0 ≤ condVar μ a B σ i x ∧ condVar μ a B σ i x ≤ M ^ 2 / N := by
  rw [condVar_eq μ a hBm hM hB]
  exact ⟨Finset.sum_nonneg fun j _ => (integral_sq_fluct μ hBm hB σ x j).1,
    sum_sq_fluct_le μ hBm hB σ i x⟩

theorem condSq_eq (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    (a : Fin q → α → Tangent d) {B : α → α → Tangent d}
    (hBm : Measurable (Function.uncurry B)) (hM : 0 ≤ M) (hB : ∀ x y, ‖B x y‖ ≤ M)
    (σ : Fin N → Fin q) (i : Fin N) (x : α) :
    ∫ z, ‖score a B σ i (Function.update z i x)‖ ^ 2 ∂(Measure.pi fun j => μ (σ j)) =
      ‖meanForce μ a B σ (σ i) x‖ ^ 2 + condVar μ a B σ i x := by
  rw [condVar_eq μ a hBm hM hB]
  simp_rw [score_update_decomp μ a B σ i _ x]
  exact core_sq (fun j => μ (σ j)) (fluct μ B σ x) (measurable_fluct μ hBm σ x)
    (by positivity) (fun j y => norm_fluct_le μ hB σ x j y)
    (fun j => integral_fluct μ hBm hB σ x j) _ _

end Cond

section Fisher

variable {M : ℝ}

theorem integrable_pi_update_split {n : ℕ} (μ : Fin n → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] (i : Fin n) {h : (Fin n → α) → ℝ}
    (hh : Integrable h (Measure.pi μ)) :
    Integrable (fun t => ∫ z, h (Function.update z i t) ∂Measure.pi μ) (μ i) := by
  have hmp := measurePreserving_update_pi μ i
  have hint : Integrable (h ∘ fun p : (Fin n → α) × α => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) := (hmp.integrable_comp hh.aestronglyMeasurable).2 hh
  exact hint.integral_prod_right

/-- The Fisher-type functional `∫ ∑ᵢ |score_i|² dν`. -/
noncomputable def fisher (μ : Fin q → Measure α) (a : Fin q → α → Tangent d)
    (B : α → α → Tangent d) (σ : Fin N → Fin q) : ℝ :=
  ∫ z, ∑ i, ‖score a B σ i z‖ ^ 2 ∂Measure.pi fun j => μ (σ j)

theorem measurable_kernelMean (ν : Measure α) [SFinite ν] {B : α → α → Tangent d}
    (hBm : Measurable (Function.uncurry B)) : Measurable (kernelMean ν B) :=
  (hBm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable

theorem aesm_meanForce (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    {a : Fin q → α → Tangent d} (hasm : ∀ s, AEStronglyMeasurable (a s) (μ s))
    {B : α → α → Tangent d} (hBm : Measurable (Function.uncurry B)) (σ : Fin N → Fin q)
    (s : Fin q) : AEStronglyMeasurable (meanForce μ a B σ s) (μ s) := by
  unfold meanForce
  have hk : ∀ t, Measurable (kernelMean (μ t) B) := fun t => measurable_kernelMean (μ t) hBm
  refine ((hasm s).add ?_).sub ?_
  · exact (Finset.measurable_sum _ fun t _ =>
      (hk t).const_smul (proportion σ t)).aestronglyMeasurable
  · exact ((hk s).const_smul (N : ℝ)⁻¹).aestronglyMeasurable

omit [MeasurableSpace α] in
theorem norm_score_le {a : Fin q → α → Tangent d} {B : α → α → Tangent d} (hM : 0 ≤ M)
    (hB : ∀ x y, ‖B x y‖ ≤ M) (σ : Fin N → Fin q) (i : Fin N) (z : Fin N → α) :
    ‖score a B σ i z‖ ≤ ‖a (σ i) (z i)‖ + M := by
  unfold score
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 N.pos
  have h1 : ‖∑ j ∈ Finset.univ.erase i, B (z i) (z j)‖ ≤ N * M := (norm_sum_le _ _).trans (by
    calc ∑ j ∈ Finset.univ.erase i, ‖B (z i) (z j)‖ ≤ ∑ _j ∈ Finset.univ.erase i, M :=
          Finset.sum_le_sum fun j _ => hB _ _
      _ = ((Finset.univ.erase i).card : ℝ) * M := by simp
      _ ≤ N * M := by
          have hc : ((Finset.univ.erase i).card : ℝ) ≤ N :=
            Nat.cast_le.2 ((Finset.card_le_card (Finset.erase_subset _ _)).trans (by simp))
          exact mul_le_mul_of_nonneg_right hc hM)
  calc (N : ℝ)⁻¹ * ‖∑ j ∈ Finset.univ.erase i, B (z i) (z j)‖ ≤ (N : ℝ)⁻¹ * (N * M) := by gcongr
    _ = M := by field_simp

theorem integrable_score_sq (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    {a : Fin q → α → Tangent d} (hasm : ∀ s, AEStronglyMeasurable (a s) (μ s))
    (hai : ∀ s, Integrable (fun x => ‖a s x‖ ^ 2) (μ s)) {B : α → α → Tangent d}
    (hBm : Measurable (Function.uncurry B)) (hM : 0 ≤ M) (hB : ∀ x y, ‖B x y‖ ≤ M)
    (σ : Fin N → Fin q) (i : Fin N) :
    Integrable (fun z => ‖score a B σ i z‖ ^ 2) (Measure.pi fun j => μ (σ j)) := by
  have hev := measurePreserving_eval (fun j => μ (σ j)) i
  have hasm_i : AEStronglyMeasurable (fun z : Fin N → α => a (σ i) (z i))
      (Measure.pi fun j => μ (σ j)) :=
    (hasm (σ i)).comp_quasiMeasurePreserving hev.quasiMeasurePreserving
  have hsum : Measurable fun z : Fin N → α => ∑ j ∈ Finset.univ.erase i, B (z i) (z j) :=
    Finset.measurable_sum _ fun j _ => by
      have hp : Measurable fun z : Fin N → α => (z i, z j) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      exact hBm.comp hp
  have hsc : AEStronglyMeasurable (fun z => score a B σ i z) (Measure.pi fun j => μ (σ j)) :=
    hasm_i.add (hsum.const_smul (N : ℝ)⁻¹).aestronglyMeasurable
  have hga : Integrable (fun z : Fin N → α => ‖a (σ i) (z i)‖ ^ 2)
      (Measure.pi fun j => μ (σ j)) :=
    (hev.integrable_comp (hai (σ i)).aestronglyMeasurable).2 (hai (σ i))
  refine Integrable.mono' ((hga.const_mul 2).add (integrable_const (2 * M ^ 2)))
    ((continuous_pow 2).comp_aestronglyMeasurable hsc.norm) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h1 := norm_score_le (a := a) hM hB σ i z
  have h0 := norm_nonneg (score a B σ i z)
  have h2 := pow_le_pow_left₀ h0 h1 2
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖a (σ i) (z i)‖ - M)]

theorem fisher_decomp (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    {a : Fin q → α → Tangent d} (hasm : ∀ s, AEStronglyMeasurable (a s) (μ s))
    (hai : ∀ s, Integrable (fun x => ‖a s x‖ ^ 2) (μ s)) {B : α → α → Tangent d}
    (hBm : Measurable (Function.uncurry B)) (hM : 0 ≤ M) (hB : ∀ x y, ‖B x y‖ ≤ M)
    (σ : Fin N → Fin q) :
    ∃ R : ℝ, 0 ≤ R ∧ R ≤ M ^ 2 / N ∧
      (N : ℝ)⁻¹ * fisher μ a B σ =
        ∑ s, proportion σ s * ∫ x, ‖meanForce μ a B σ s x‖ ^ 2 ∂μ s + R := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 N.pos
  have key : ∀ i : Fin N, ∃ Ri : ℝ, 0 ≤ Ri ∧ Ri ≤ M ^ 2 / N ∧
      ∫ z, ‖score a B σ i z‖ ^ 2 ∂(Measure.pi fun j => μ (σ j)) =
        ∫ x, ‖meanForce μ a B σ (σ i) x‖ ^ 2 ∂μ (σ i) + Ri := by
    intro i
    have hh := integrable_score_sq μ hasm hai hBm hM hB σ i
    have hφ := integrable_pi_update_split (fun j => μ (σ j)) i hh
    have hφeq : (fun t => ∫ z, ‖score a B σ i (Function.update z i t)‖ ^ 2
        ∂(Measure.pi fun j => μ (σ j))) =
        fun t => ‖meanForce μ a B σ (σ i) t‖ ^ 2 + condVar μ a B σ i t :=
      funext fun t => condSq_eq μ a hBm hM hB σ i t
    rw [hφeq] at hφ
    have hbd := fun t => condVar_bounds μ a hBm hM hB σ i t
    have hmsm : AEStronglyMeasurable (fun t => ‖meanForce μ a B σ (σ i) t‖ ^ 2) (μ (σ i)) :=
      (continuous_pow 2).comp_aestronglyMeasurable (aesm_meanForce μ hasm hBm σ (σ i)).norm
    have hmi : Integrable (fun t => ‖meanForce μ a B σ (σ i) t‖ ^ 2) (μ (σ i)) :=
      Integrable.mono' hφ hmsm (Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        linarith [(hbd t).1])
    have hcv : Integrable (fun t => condVar μ a B σ i t) (μ (σ i)) := by
      have : (fun t => condVar μ a B σ i t) =
          fun t => (‖meanForce μ a B σ (σ i) t‖ ^ 2 + condVar μ a B σ i t) -
            ‖meanForce μ a B σ (σ i) t‖ ^ 2 := by funext t; ring
      rw [this]; exact hφ.sub hmi
    refine ⟨∫ t, condVar μ a B σ i t ∂μ (σ i), integral_nonneg fun t => (hbd t).1, ?_, ?_⟩
    · calc ∫ t, condVar μ a B σ i t ∂μ (σ i) ≤ ∫ _t, M ^ 2 / N ∂μ (σ i) :=
            integral_mono hcv (integrable_const _) fun t => (hbd t).2
        _ = M ^ 2 / N := by simp
    · rw [integral_pi_update_split (fun j => μ (σ j)) i hh, hφeq, integral_add hmi hcv]
  choose R hR0 hRle hReq using key
  refine ⟨(N : ℝ)⁻¹ * ∑ i, R i, mul_nonneg (inv_nonneg.2 hN.le) (Finset.sum_nonneg fun i _ => hR0 i),
    ?_, ?_⟩
  · calc (N : ℝ)⁻¹ * ∑ i, R i ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, M ^ 2 / N := by
          gcongr with i; exact hRle i
      _ = M ^ 2 / N := by simp
  · unfold fisher
    rw [integral_finsetSum _ fun i _ => integrable_score_sq μ hasm hai hBm hM hB σ i]
    simp_rw [hReq]
    rw [Finset.sum_add_distrib, mul_add]
    congr 1
    have := sum_label σ (fun s => ∫ x, ‖meanForce μ a B σ s x‖ ^ 2 ∂μ s)
    simpa [smul_eq_mul] using this

end Fisher

section Limit

variable {M : ℝ}

theorem proportion_nonneg (σ : Fin N → Fin q) (s : Fin q) : 0 ≤ proportion σ s :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem sum_proportion (σ : Fin N → Fin q) : ∑ s, proportion σ s = 1 := by
  have h := sum_label (N := N) σ (fun _ => (1 : ℝ))
  have hN : (N : ℝ) ≠ 0 := (Nat.cast_pos.2 N.pos).ne'
  simpa [smul_eq_mul, hN] using h.symm

/-- The limit force `A_s + B * ρ̄_θ`. -/
noncomputable def limForce (μ : Fin q → Measure α) (a : Fin q → α → Tangent d)
    (B : α → α → Tangent d) (θ : Fin q → ℝ) (s : Fin q) (x : α) : Tangent d :=
  a s x + ∑ t, θ t • kernelMean (μ t) B x

theorem norm_meanForce_le (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    (a : Fin q → α → Tangent d) {B : α → α → Tangent d}
    (hB : ∀ x y, ‖B x y‖ ≤ M) (σ : Fin N → Fin q) (s : Fin q) (x : α) :
    ‖meanForce μ a B σ s x‖ ≤ ‖a s x‖ + 2 * M := by
  have hN : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast N.pos)
  have h1 : ‖∑ t, proportion σ t • kernelMean (μ t) B x‖ ≤ M := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ t, ‖proportion σ t • kernelMean (μ t) B x‖ ≤ ∑ t, proportion σ t * M :=
          Finset.sum_le_sum fun t _ => by
            rw [norm_smul, Real.norm_of_nonneg (proportion_nonneg σ t)]
            exact mul_le_mul_of_nonneg_left (norm_kernelMean_le (μ t) hB x)
              (proportion_nonneg σ t)
      _ = M := by rw [← Finset.sum_mul, sum_proportion, one_mul]
  have h2 : ‖(N : ℝ)⁻¹ • kernelMean (μ s) B x‖ ≤ M := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg _))]
    calc (N : ℝ)⁻¹ * ‖kernelMean (μ s) B x‖ ≤ 1 * M :=
          mul_le_mul hN (norm_kernelMean_le (μ s) hB x) (norm_nonneg _) zero_le_one
      _ = M := one_mul _
  unfold meanForce
  calc ‖a s x + ∑ t, proportion σ t • kernelMean (μ t) B x - (N : ℝ)⁻¹ • kernelMean (μ s) B x‖
      ≤ ‖a s x + ∑ t, proportion σ t • kernelMean (μ t) B x‖ +
        ‖(N : ℝ)⁻¹ • kernelMean (μ s) B x‖ := norm_sub_le _ _
    _ ≤ (‖a s x‖ + ‖∑ t, proportion σ t • kernelMean (μ t) B x‖) +
        ‖(N : ℝ)⁻¹ • kernelMean (μ s) B x‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖a s x‖ + 2 * M := by linarith

theorem tendsto_meanForce_sq (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    {a : Fin q → α → Tangent d} (hasm : ∀ s, AEStronglyMeasurable (a s) (μ s))
    (hai : ∀ s, Integrable (fun x => ‖a s x‖ ^ 2) (μ s)) {B : α → α → Tangent d}
    (hBm : Measurable (Function.uncurry B)) (hB : ∀ x y, ‖B x y‖ ≤ M)
    (σ : (N : ℕ+) → Fin N → Fin q) (θ : Fin q → ℝ)
    (hσ : ∀ s, Tendsto (fun N : ℕ+ => proportion (σ N) s) atTop (𝓝 (θ s))) (s : Fin q) :
    Tendsto (fun N : ℕ+ => ∫ x, ‖meanForce μ a B (σ N) s x‖ ^ 2 ∂μ s) atTop
      (𝓝 (∫ x, ‖limForce μ a B θ s x‖ ^ 2 ∂μ s)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => 2 * ‖a s x‖ ^ 2 + 8 * M ^ 2)
    (F := fun (N : ℕ+) x => ‖meanForce μ a B (σ N) s x‖ ^ 2)
    (f := fun x => ‖limForce μ a B θ s x‖ ^ 2) (Eventually.of_forall fun N => ?_)
    (Eventually.of_forall fun N => Eventually.of_forall fun x => ?_) ?_
    (Eventually.of_forall fun x => ?_)
  · exact (continuous_pow 2).comp_aestronglyMeasurable
      (aesm_meanForce μ hasm hBm (σ N) s).norm
  · rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := norm_meanForce_le μ a hB (σ N) s x
    have h0 := norm_nonneg (meanForce μ a B (σ N) s x)
    have h2 := pow_le_pow_left₀ h0 h 2
    nlinarith [sq_nonneg (‖a s x‖ - 2 * M)]
  · exact ((hai s).const_mul 2).add (integrable_const _)
  · have hc : Tendsto (fun N : ℕ+ => meanForce μ a B (σ N) s x) atTop
        (𝓝 (limForce μ a B θ s x)) := by
      unfold meanForce limForce
      have h1 : Tendsto (fun N : ℕ+ => ∑ t, proportion (σ N) t • kernelMean (μ t) B x) atTop
          (𝓝 (∑ t, θ t • kernelMean (μ t) B x)) :=
        tendsto_finsetSum _ fun t _ => (hσ t).smul_const _
      have h2 : Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ • kernelMean (μ s) B x) atTop
          (𝓝 ((0 : ℝ) • kernelMean (μ s) B x)) :=
        tendsto_nat_inv.smul_const _
      simpa using (h1.const_add (a s x)).sub h2
    exact ((continuous_pow 2).tendsto _).comp hc.norm

end Limit

section FisherLimit

variable {M : ℝ}

theorem tendsto_fisher (μ : Fin q → Measure α) [∀ s, IsProbabilityMeasure (μ s)]
    {a : Fin q → α → Tangent d} (hasm : ∀ s, AEStronglyMeasurable (a s) (μ s))
    (hai : ∀ s, Integrable (fun x => ‖a s x‖ ^ 2) (μ s)) {B : α → α → Tangent d}
    (hBm : Measurable (Function.uncurry B)) (hM : 0 ≤ M) (hB : ∀ x y, ‖B x y‖ ≤ M)
    (σ : (N : ℕ+) → Fin N → Fin q) (θ : Fin q → ℝ)
    (hσ : ∀ s, Tendsto (fun N : ℕ+ => proportion (σ N) s) atTop (𝓝 (θ s))) :
    Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ * fisher μ a B (σ N)) atTop
      (𝓝 (∑ s, θ s * ∫ x, ‖limForce μ a B θ s x‖ ^ 2 ∂μ s)) := by
  have key := fun N : ℕ+ => fisher_decomp μ hasm hai hBm hM hB (σ N)
  choose R hR0 hRle hReq using key
  have hR : Tendsto R atTop (𝓝 0) := by
    refine squeeze_zero hR0 hRle ?_
    have := tendsto_nat_inv.const_mul (M ^ 2)
    simpa [div_eq_mul_inv] using this
  have hS : Tendsto (fun N : ℕ+ => ∑ s, proportion (σ N) s *
      ∫ x, ‖meanForce μ a B (σ N) s x‖ ^ 2 ∂μ s) atTop
      (𝓝 (∑ s, θ s * ∫ x, ‖limForce μ a B θ s x‖ ^ 2 ∂μ s)) :=
    tendsto_finsetSum _ fun s _ =>
      (hσ s).mul (tendsto_meanForce_sq μ hasm hai hBm hB σ θ hσ s)
  have := hS.add hR
  rw [add_zero] at this
  refine this.congr fun N => ?_
  exact (hReq N).symm

end FisherLimit

end Score

end Core

section Species

open DGPS.Particle.ProductRecovery

variable {d : ℕ}

theorem aemeas_ofReal_sq (ρ : AbsoluteDensity d) :
    AEMeasurable (fun x => ENNReal.ofReal (ρ.sqrt x ^ 2)) (haar d) :=
  ENNReal.measurable_ofReal.comp_aemeasurable (aemeasurable_density' ρ)

theorem integral_densityMeasure_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : AbsoluteDensity d) (g : Torus d → E) :
    ∫ x, g x ∂(densityMeasure ρ : Measure (Torus d)) = ∫ x, ρ.density x • g x ∂haar d := by
  rw [densityMeasure_coe, integral_withDensity_eq_integral_toReal_smul₀ (aemeas_ofReal_sq ρ)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show (ENNReal.ofReal (ρ.sqrt x ^ 2)).toReal • g x = ρ.density x • g x
  rw [AbsoluteDensity.density, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem integrable_densityMeasure_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : AbsoluteDensity d) (g : Torus d → E) :
    Integrable g (densityMeasure ρ : Measure (Torus d)) ↔
      Integrable (fun x => ρ.density x • g x) (haar d) := by
  rw [densityMeasure_coe, integrable_withDensity_iff_integrable_smul₀' (aemeas_ofReal_sq ρ)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  show (ENNReal.ofReal (ρ.sqrt x ^ 2)).toReal • g x = ρ.density x • g x
  rw [AbsoluteDensity.density, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem speciesLaw_ac (F : SpeciesFamily d) (s : Fin F.count) : speciesLaw F s ≪ haar d := by
  unfold speciesLaw
  rw [densityMeasure_coe]
  exact withDensity_absolutelyContinuous _ _

/-- The species relative drift `∇ log ρ_s + c = 2 u⁻¹ ∇u + c`. -/
theorem species_weighted (F : SpeciesFamily d) (s : Fin F.count)
    (hpos : ∀ᵐ x ∂haar d, 0 < (F.density s).sqrt x)
    {c : Torus d → Tangent d} (hc : AEStronglyMeasurable c (haar d)) {C : ℝ}
    (hC : ∀ᵐ x ∂haar d, ‖c x‖ ≤ C) :
    AEStronglyMeasurable
        (fun x => ((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + c x)
        (speciesLaw F s) ∧
      Integrable
        (fun x => ‖((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + c x‖ ^ 2)
        (speciesLaw F s) ∧
      Integrable
        (fun x => ‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x‖ ^ 2) (haar d) ∧
      ∫ x, ‖((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + c x‖ ^ 2
          ∂speciesLaw F s =
        ∫ x, ‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x‖ ^ 2 ∂haar d := by
  have hu : AEStronglyMeasurable (F.density s).sqrt (haar d) :=
    (F.density s).memLp_sqrt.aestronglyMeasurable
  have hg : AEStronglyMeasurable (F.sqrtGradient s) (haar d) :=
    (F.isWeakGradient_sqrtGradient s).memLp_grad.aestronglyMeasurable
  have hw : AEStronglyMeasurable
      (fun x => ((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + c x) (haar d) :=
    ((hu.aemeasurable.inv.const_mul (2 : ℝ)).aestronglyMeasurable.smul hg).add hc
  have hv : AEStronglyMeasurable
      (fun x => (2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x) (haar d) :=
    (hg.const_smul (2 : ℝ)).add (hu.smul hc)
  have hint : Integrable
      (fun x => ‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x‖ ^ 2) (haar d) := by
    have h1 : Integrable (fun x => ‖F.sqrtGradient s x‖ ^ 2) (haar d) :=
      (F.isWeakGradient_sqrtGradient s).memLp_grad.norm.integrable_sq
    have h2 : Integrable (fun x => (F.density s).sqrt x ^ 2) (haar d) :=
      (F.density s).integrable_density
    refine Integrable.mono' ((h1.const_mul 8).add (h2.const_mul (2 * C ^ 2)))
      (hv.norm.pow 2) ?_
    filter_upwards [hC] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have e1 : ‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x‖ ≤
        2 * ‖F.sqrtGradient s x‖ + |(F.density s).sqrt x| * C := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul]; simp
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    have e2 := pow_le_pow_left₀ (norm_nonneg _) e1 2
    refine e2.trans ?_
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (2 * ‖F.sqrtGradient s x‖ - |(F.density s).sqrt x| * C),
      sq_abs ((F.density s).sqrt x)]
  have hpt : ∀ᵐ x ∂haar d, (F.density s).density x •
      ‖((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + c x‖ ^ 2 =
      ‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x‖ ^ 2 := by
    filter_upwards [hpos] with x hx
    have hx0 : (F.density s).sqrt x ≠ 0 := hx.ne'
    have : (F.density s).sqrt x • (((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x +
        c x) = (2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • c x := by
      rw [smul_add, smul_smul]
      congr 2
      field_simp
    rw [← this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, AbsoluteDensity.density,
      smul_eq_mul]
  refine ⟨hw.mono_ac (speciesLaw_ac F s), ?_, hint, ?_⟩
  · unfold speciesLaw
    rw [integrable_densityMeasure_iff]
    exact hint.congr (by filter_upwards [hpt] with x hx; exact hx.symm)
  · unfold speciesLaw
    rw [integral_densityMeasure_smul]
    exact integral_congr_ae hpt

end Species

section Drift

open DGPS.Particle.ProductRecovery

variable {d : ℕ}

theorem ae_bound_gV {A : InteractionData d} (hLip : LipschitzData A) {gV : Torus d → Tangent d}
    (hgV : IsWeakGradient A.V gV) : ∃ C : ℝ, ∀ᵐ x ∂haar d, ‖gV x‖ ≤ C := by
  obtain ⟨LV, hLV0, hV⟩ := hLip.exists_V_const
  obtain ⟨hVg, hbd⟩ := Lipschitz.exists_weak_gradient hLV0 hV
  have h2 : IsWeakGradient A.V (smoothGrad A.V) :=
    ⟨hVg.memLp.mono_exponent le_top, hVg.memLp_grad.mono_exponent le_top, hVg.ibp⟩
  refine ⟨LV, ?_⟩
  filter_upwards [hgV.ae_eq h2, hbd] with x h1 h3
  rw [h1]; exact h3

theorem integral_barycenter_kernel (F : SpeciesFamily d) {B : Torus d → Torus d → Tangent d}
    (hBm : Measurable (Function.uncurry B)) {M : ℝ} (hB : ∀ x y, ‖B x y‖ ≤ M) (x : Torus d) :
    ∫ y, (barycenter F).density y • B x y ∂haar d =
      ∑ t, F.weight t • ∫ y, B x y ∂(speciesLaw F t) := by
  have hBx : Measurable (B x) := hBm.of_uncurry_left
  have hint : ∀ t, Integrable (fun y => (F.density t).density y • B x y) (haar d) := fun t =>
    (integrable_densityMeasure_iff (F.density t) (B x)).1
      (Integrable.of_bound hBx.aestronglyMeasurable M (Eventually.of_forall (hB x)))
  have hfun : (fun y => (barycenter F).density y • B x y) =
      fun y => ∑ t, F.weight t • ((F.density t).density y • B x y) := by
    funext y
    rw [F.barycenter_density_apply y, Finset.sum_smul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_smul]
    rfl
  have hint' : ∀ t, Integrable
      (fun y => F.weight t • ((F.density t).density y • B x y)) (haar d) := fun t =>
    (hint t).smul (F.weight t)
  rw [hfun, integral_finsetSum _ fun t _ => hint' t]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_smul]
  unfold speciesLaw
  rw [integral_densityMeasure_smul]

end Drift

section Force

variable {d : ℕ}

theorem force_ae_eq {A : InteractionData d} (hLip : LipschitzData A) (b : AbsoluteDrift A)
    (F : SpeciesFamily d) {B : Torus d → Torus d → Tangent d}
    (hBm : Measurable (Function.uncurry B)) {M : ℝ} (hB : ∀ x y, ‖B x y‖ ≤ M)
    (hBg : ∀ y, IsWeakGradient (fun x => A.W x y) (fun x => B x y))
    {gV : Torus d → Tangent d} (hgV : IsWeakGradient A.V gV) :
    b.force (barycenter F) =ᵐ[haar d]
      fun x => gV x + ∑ t, F.weight t • ∫ y, B x y ∂(DGPS.Particle.ProductRecovery.speciesLaw F t) := by
  obtain ⟨L, hL0, hW⟩ := hLip.exists_W_section_const
  obtain ⟨LV, hLV0, hV⟩ := hLip.exists_V_const
  have hVg := Lipschitz.exists_weak_gradient hLV0 hV
  have hB' : MemLp (fun p : Torus d × Torus d => B p.1 p.2) ∞ ((haar d).prod (haar d)) :=
    memLp_top_of_bound hBm.aestronglyMeasurable M (Eventually.of_forall fun p => hB p.1 p.2)
  have hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ∞ (fun x => A.W x y) (fun x => B x y) :=
    Eventually.of_forall fun y => ⟨(Lipschitz.exists_weak_gradient hL0 (hW y)).1.memLp,
      memLp_top_of_bound hBm.of_uncurry_right.aestronglyMeasurable M
        (Eventually.of_forall fun x => hB x y), (hBg y).ibp⟩
  have hc := ((Lipschitz.weak_interaction_convolution d A.W B L A.W_continuous hW hBm hB'
    hWB).1 (barycenter F).density (Lipschitz.isProbDensity_density _)).1
  have hs := isWeakGradientLp_add hVg.1 hc
  have hpot : interactionPotential A (barycenter F) =
      fun x => A.V x + ∫ y, A.W x y * (barycenter F).density y ∂haar d := by
    funext x
    rw [interactionPotential_eq]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  have h1 : IsWeakGradientLp 1 (interactionPotential A (barycenter F))
      (fun x => smoothGrad A.V x + ∫ y, (barycenter F).density y • B x y ∂haar d) := by
    rw [hpot]
    exact ⟨hs.memLp.mono_exponent le_top, hs.memLp_grad.mono_exponent le_top, hs.ibp⟩
  have h2 := b.ae_eq_of_isWeakGradient (barycenter F) h1
  have h3 : IsWeakGradient A.V (smoothGrad A.V) :=
    ⟨hVg.1.memLp.mono_exponent le_top, hVg.1.memLp_grad.mono_exponent le_top, hVg.1.ibp⟩
  filter_upwards [h2, hgV.ae_eq h3] with x hx1 hx2
  rw [hx1, hx2, integral_barycenter_kernel F hBm hB x]

end Force

section Main

open DGPS.Particle.ProductRecovery

variable {d : ℕ}

/-- The species drift `A_s = ∇ log ρ_s + ∇V = 2 u_s⁻¹ ∇u_s + ∇V` for a weak gradient `gV` of `V`. -/
noncomputable def driftA (F : SpeciesFamily d) (gV : Torus d → Tangent d) (s : Fin F.count)
    (x : Torus d) : Tangent d :=
  ((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x + gV x

theorem limForce_eq (F : SpeciesFamily d) (gV : Torus d → Tangent d)
    (B : Torus d → Torus d → Tangent d) (s : Fin F.count) (x : Torus d) :
    limForce (speciesLaw F) (driftA F gV) B F.weight s x =
      ((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x +
        (gV x + ∑ t, F.weight t • kernelMean (speciesLaw F t) B x) := by
  unfold limForce driftA
  rw [add_assoc]

theorem dissipation_facts {A : InteractionData d} (hLip : LipschitzData A) (b : AbsoluteDrift A)
    (F : SpeciesFamily d) (hpos : ∀ s, ∀ᵐ x ∂haar d, 0 < (F.density s).sqrt x)
    {B : Torus d → Torus d → Tangent d} (hBm : Measurable (Function.uncurry B)) {M : ℝ}
    (hB : ∀ x y, ‖B x y‖ ≤ M) (hBg : ∀ y, IsWeakGradient (fun x => A.W x y) (fun x => B x y))
    {gV : Torus d → Tangent d} (hgV : IsWeakGradient A.V gV) :
    (∀ s, AEStronglyMeasurable (driftA F gV s) (speciesLaw F s)) ∧
      (∀ s, Integrable (fun x => ‖driftA F gV s x‖ ^ 2) (speciesLaw F s)) ∧
      speciesDissipation A b F ≠ ⊤ ∧
      (speciesDissipation A b F).toReal =
        ∑ s, F.weight s *
          ∫ x, ‖limForce (speciesLaw F) (driftA F gV) B F.weight s x‖ ^ 2 ∂speciesLaw F s := by
  obtain ⟨C, hC⟩ := ae_bound_gV hLip hgV
  have hgm : AEStronglyMeasurable gV (haar d) := hgV.memLp_grad.aestronglyMeasurable
  have hKm : Measurable fun x => ∑ t, F.weight t • kernelMean (speciesLaw F t) B x :=
    Finset.measurable_sum _ fun t _ =>
      ((measurable_kernelMean (speciesLaw F t) hBm).const_smul (F.weight t) :
        Measurable (F.weight t • kernelMean (speciesLaw F t) B))
  have hKb : ∀ x, ‖∑ t, F.weight t • kernelMean (speciesLaw F t) B x‖ ≤ M := by
    intro x
    refine (norm_sum_le _ _).trans ?_
    calc ∑ t, ‖F.weight t • kernelMean (speciesLaw F t) B x‖ ≤ ∑ t, F.weight t * M :=
          Finset.sum_le_sum fun t _ => by
            rw [norm_smul, Real.norm_of_nonneg (F.weight_nonneg t)]
            exact mul_le_mul_of_nonneg_left (norm_kernelMean_le (speciesLaw F t) hB x)
              (F.weight_nonneg t)
      _ = M := by rw [← Finset.sum_mul, F.weight_sum, one_mul]
  have hcm : AEStronglyMeasurable
      (fun x => gV x + ∑ t, F.weight t • kernelMean (speciesLaw F t) B x) (haar d) :=
    hgm.add hKm.aestronglyMeasurable
  have hcb : ∀ᵐ x ∂haar d,
      ‖gV x + ∑ t, F.weight t • kernelMean (speciesLaw F t) B x‖ ≤ C + M := by
    filter_upwards [hC] with x hx
    exact (norm_add_le _ _).trans (add_le_add hx (hKb x))
  have hI : ∀ s, ENNReal.ofReal
      (∫ x, ‖limForce (speciesLaw F) (driftA F gV) B F.weight s x‖ ^ 2 ∂speciesLaw F s) =
      ∫⁻ x, ENNReal.ofReal
        (‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • b.force (barycenter F) x‖ ^ 2)
        ∂haar d := by
    intro s
    obtain ⟨-, -, h3, h4⟩ := species_weighted F s (hpos s) hcm hcb
    have e1 : (fun x => ‖limForce (speciesLaw F) (driftA F gV) B F.weight s x‖ ^ 2) =
        fun x => ‖((2 : ℝ) * ((F.density s).sqrt x)⁻¹) • F.sqrtGradient s x +
          (gV x + ∑ t, F.weight t • kernelMean (speciesLaw F t) B x)‖ ^ 2 :=
      funext fun x => by rw [limForce_eq]
    rw [e1, h4, ofReal_integral_eq_lintegral_ofReal h3 (Eventually.of_forall fun x => sq_nonneg _)]
    refine lintegral_congr_ae ?_
    filter_upwards [force_ae_eq hLip b F hBm hB hBg hgV] with x hx
    have hx' : b.force (barycenter F) x =
        gV x + ∑ t, F.weight t • kernelMean (speciesLaw F t) B x := hx
    rw [hx']
  have hD : speciesDissipation A b F = ENNReal.ofReal (∑ s, F.weight s *
      ∫ x, ‖limForce (speciesLaw F) (driftA F gV) B F.weight s x‖ ^ 2 ∂speciesLaw F s) := by
    unfold speciesDissipation
    rw [ENNReal.ofReal_sum_of_nonneg fun s _ =>
      mul_nonneg (F.weight_nonneg s) (integral_nonneg fun _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ENNReal.ofReal_mul (F.weight_nonneg s), hI s]
  refine ⟨fun s => (species_weighted F s (hpos s) hgm hC).1,
    fun s => (species_weighted F s (hpos s) hgm hC).2.1, ?_, ?_⟩
  · rw [hD]; exact ENNReal.ofReal_ne_top
  · rw [hD]
    exact ENNReal.toReal_ofReal (Finset.sum_nonneg fun s _ =>
      mul_nonneg (F.weight_nonneg s) (integral_nonneg fun _ => sq_nonneg _))

end Main

end DGPS.Particle.ProductForceVariance

namespace DGPS.Lipschitz

open DGPS.Particle.ProductForceVariance DGPS.Particle.ProductRecovery

/-- **Product force: conditional mean, conditional variance and Fisher limit.**
For a Lipschitz family and species densities `ρ_s = u_s²` (with `u_s > 0` a.e.), there are a
bounded measurable kernel `B = ∇_x W` and a rounded labelling `σ` with proportions converging to
the weights, such that for every weak gradient `gV` of `V` and `A_s = ∇ log ρ_s + ∇V`, the relative
score `A_s(x_i) + N⁻¹ ∑_{j ≠ i} B(x_i, x_j)` of the product law has conditional mean
`A_s + B * ρ̄_N - N⁻¹ B * ρ_s`, conditional variance at most `‖B‖∞² / N`, and
`N⁻¹ ∫ ∑ᵢ |scoreᵢ|² = ∑_s p_s ∫ |conditional mean|² ρ_s + R_N` with `0 ≤ R_N ≤ ‖B‖∞² / N`; this
tends to the species dissipation `D_θ`. -/
theorem product_force_conditional_variance_and_fisher_limit {d : ℕ} (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (F : SpeciesFamily d)
    (hpos : ∀ s, ∀ᵐ x ∂haar d, 0 < (F.density s).sqrt x) :
    ∃ (B : Torus d → Torus d → Tangent d) (M : ℝ) (σ : (N : ℕ+) → Fin N → Fin F.count),
      Measurable (Function.uncurry B) ∧ 0 ≤ M ∧ (∀ x y, ‖B x y‖ ≤ M) ∧
      (∀ y, IsWeakGradient (fun x => A.W x y) (fun x => B x y)) ∧
      (∀ s, Tendsto (fun N : ℕ+ => proportion (σ N) s) atTop (𝓝 (F.weight s))) ∧
      (∃ gV : Torus d → Tangent d, IsWeakGradient A.V gV) ∧
      (∀ (gV : Torus d → Tangent d) (N : ℕ+), IsWeakGradient A.V gV →
        IsParticleWeakGradient A N (particleHamiltonian A N)
          (fun x i => gV (x i) + (N : ℝ)⁻¹ • ∑ j ∈ Finset.univ.erase i, B (x i) (x j))) ∧
      ∀ gV : Torus d → Tangent d, IsWeakGradient A.V gV →
        (∀ (N : ℕ+) (i : Fin N) (x : Torus d),
          ∫ z, score (driftA F gV) B (σ N) i (Function.update z i x) ∂productLaw F (σ N) =
            meanForce (speciesLaw F) (driftA F gV) B (σ N) (σ N i) x) ∧
        (∀ (N : ℕ+) (i : Fin N) (x : Torus d),
          ∫ z, ‖score (driftA F gV) B (σ N) i (Function.update z i x) -
              meanForce (speciesLaw F) (driftA F gV) B (σ N) (σ N i) x‖ ^ 2
            ∂productLaw F (σ N) ≤ M ^ 2 / ((N : ℕ) : ℝ)) ∧
        (∀ N : ℕ+, ∃ R : ℝ, 0 ≤ R ∧ R ≤ M ^ 2 / ((N : ℕ) : ℝ) ∧
          ((N : ℕ) : ℝ)⁻¹ * ∫ z, ∑ i, ‖score (driftA F gV) B (σ N) i z‖ ^ 2 ∂productLaw F (σ N) =
            ∑ s, proportion (σ N) s *
              ∫ x, ‖meanForce (speciesLaw F) (driftA F gV) B (σ N) s x‖ ^ 2 ∂speciesLaw F s + R) ∧
        Tendsto (fun N : ℕ+ => ((N : ℕ) : ℝ)⁻¹ *
          ∫ z, ∑ i, ‖score (driftA F gV) B (σ N) i z‖ ^ 2 ∂productLaw F (σ N)) atTop
          (𝓝 (speciesDissipation A b F).toReal) ∧
        speciesDissipation A b F ≠ ⊤ := by
  obtain ⟨hgex, B, hBm, ⟨M0, hM0⟩, hBg, hPart⟩ := (particle_force_including_the_diagonal d).2.2 A hLip
  obtain ⟨σ, hσ, -⟩ := rounded_finite_species_product_entropy A F
  have hB : ∀ x y, ‖B x y‖ ≤ max M0 0 := fun x y => (hM0 x y).trans (le_max_left _ _)
  refine ⟨B, max M0 0, σ, hBm, le_max_right _ _, hB, hBg, hσ, hgex, hPart, ?_⟩
  intro gV hgV
  obtain ⟨hasm, hai, hne, hD⟩ := dissipation_facts hLip b F hpos hBm hB hBg hgV
  have hM : 0 ≤ max M0 0 := le_max_right _ _
  refine ⟨fun N i x => condMean_eq (speciesLaw F) (driftA F gV) hBm hB (σ N) i x,
    fun N i x => (condVar_bounds (speciesLaw F) (driftA F gV) hBm hM hB (σ N) i x).2,
    fun N => fisher_decomp (speciesLaw F) hasm hai hBm hM hB (σ N), ?_, hne⟩
  rw [hD]
  exact tendsto_fisher (speciesLaw F) hasm hai hBm hM hB σ F.weight hσ

end DGPS.Lipschitz
