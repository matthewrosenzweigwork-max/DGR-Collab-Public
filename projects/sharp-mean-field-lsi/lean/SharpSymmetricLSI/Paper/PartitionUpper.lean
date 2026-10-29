import SharpSymmetricLSI.Paper.TypesCount

/-!
# Lemma 2.4, the upper half (Phase 3, lane D; R5)

`N^{-1} log Z_N ≤ -F_* + 3ω + K^d log(N+1)/N` when `V`, `W` oscillate by at most `ω` on the
cells of resolution `K`, by the method of types (route departure from Sanov/Varadhan, recorded in
`Audit/statement_map.md`).
-/

open MeasureTheory InformationTheory Set Filter Finset
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {K : ℕ} [NeZero K]

theorem measureReal_cell (a : Fin d → Fin K) :
    (haar d).real {x | cellIdx K x = a} = ((K : ℝ) ^ d)⁻¹ := by
  rw [measureReal_def, volume_cell, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast]

theorem integral_comp_cellIdx (g : (Fin d → Fin K) → ℝ) :
    ∫ x, g (cellIdx K x) ∂haar d = (∑ a, g a) / (K : ℝ) ^ d := by
  have hm : ∀ a : Fin d → Fin K, MeasurableSet {x : Torus d | cellIdx K x = a} := fun a =>
    measurable_cellIdx (measurableSet_singleton a)
  have e : (fun x => g (cellIdx K x)) =
      fun x => ∑ a, {x : Torus d | cellIdx K x = a}.indicator (fun _ => g a) x := by
    funext x
    rw [Finset.sum_eq_single (cellIdx K x)]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [e, integral_finsetSum _ fun a _ => (integrable_const (g a)).indicator (hm a)]
  simp_rw [integral_indicator_const _ (hm _), measureReal_cell, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem integral_comp_cellIdx_pi {N : ℕ} (G : (Fin N → Fin d → Fin K) → ℝ) :
    ∫ X, G (fun i => cellIdx K (X i)) ∂(volume : Measure (Config N d)) =
      (∑ σ, G σ) / ((K : ℝ) ^ d) ^ N := by
  have hS : ∀ σ : Fin N → Fin d → Fin K, {X : Config N d | (fun i => cellIdx K (X i)) = σ} =
      univ.pi fun i => {x | cellIdx K x = σ i} := fun σ => by
    ext X; simp [funext_iff]
  have hm : ∀ σ : Fin N → Fin d → Fin K,
      MeasurableSet {X : Config N d | (fun i => cellIdx K (X i)) = σ} := fun σ => by
    rw [hS]; exact MeasurableSet.univ_pi fun i => measurable_cellIdx (measurableSet_singleton _)
  have hv : ∀ σ : Fin N → Fin d → Fin K,
      (volume : Measure (Config N d)).real {X | (fun i => cellIdx K (X i)) = σ} =
        (((K : ℝ) ^ d) ^ N)⁻¹ := fun σ => by
    rw [hS, measureReal_def, volume_pi, Measure.pi_pi]
    have hc : ∀ i, (volume : Measure (Torus d)) {x | cellIdx K x = σ i} = ((K : ℝ≥0∞) ^ d)⁻¹ :=
      fun i => volume_cell (σ i)
    simp_rw [hc]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, inv_pow]
  have e : (fun X : Config N d => G (fun i => cellIdx K (X i))) = fun X => ∑ σ,
      {X : Config N d | (fun i => cellIdx K (X i)) = σ}.indicator (fun _ => G σ) X := by
    funext X
    rw [Finset.sum_eq_single (fun i => cellIdx K (X i))]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [e, integral_finsetSum _ fun σ _ => (integrable_const (G σ)).indicator (hm σ)]
  simp_rw [integral_indicator_const _ (hm _), hv, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem integrable_of_abs_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : AEStronglyMeasurable g μ) {B : ℝ} (hB : ∀ x, |g x| ≤ B) : Integrable g μ :=
  Integrable.of_bound hg B (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

theorem sum_mul_log_mul {C : Type*} [Fintype C] {p : C → ℝ} (hp1 : ∑ a, p a = 1) {M : ℝ}
    (hM : 0 < M) : ∑ a, p a * Real.log (M * p a) = ∑ a, p a * Real.log (p a) + Real.log M := by
  have : ∀ a, p a * Real.log (M * p a) = p a * Real.log (p a) + p a * Real.log M := fun a => by
    rcases eq_or_ne (p a) 0 with h | h
    · simp [h]
    · rw [Real.log_mul hM.ne' h]; ring
  rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]

section Cells

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The cell energy `Φ(p) = ∑ₐ p_a V(z_a) + ½ ∑ₐ∑_b p_a p_b W(z_a,z_b)`. -/
noncomputable def cellEnergy (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (K : ℕ)
    (p : (Fin d → Fin K) → ℝ) : ℝ :=
  ∑ a, p a * V (cellPt K a) + (∑ a, ∑ b, p a * p b * W (cellPt K a) (cellPt K b)) / 2

/-- `F(ρ_p) ≤ ∑ₐ p_a log(K^d p_a) + Φ(p) + 3ω/2` for the piecewise-constant density `ρ_p`. -/
theorem freeEnergy_cell_le (hyp : Hyp V W KV KW) {ω : ℝ}
    (hV : ∀ x, |V x - V (cellPt K (cellIdx K x))| ≤ ω)
    (hW : ∀ x y, |W x y - W (cellPt K (cellIdx K x)) (cellPt K (cellIdx K y))| ≤ ω)
    {p : (Fin d → Fin K) → ℝ} (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ∃ ρ : ProbabilityMeasure (Torus d), klDiv (ρ : Measure (Torus d)) (haar d) ≠ ⊤ ∧
      (klDiv (ρ : Measure (Torus d)) (haar d)).toReal + energyMF V W ρ ≤
        ∑ a, p a * Real.log ((K : ℝ) ^ d * p a) + cellEnergy V W K p + 3 / 2 * ω := by
  set M : ℝ := (K : ℝ) ^ d with hMdef
  have hM : 0 < M := by have : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
                        positivity
  have hcard : (Fintype.card (Fin d → Fin K) : ℝ) = M := by simp [hMdef]
  set f : Torus d → ℝ := fun x => M * p (cellIdx K x) with hf
  have hfm : Measurable f :=
    measurable_const.mul ((measurable_of_countable p).comp measurable_cellIdx)
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg hM.le (hp0 _)
  have hp1' : ∀ a, p a ≤ 1 := fun a => by
    rw [← hp1]; exact Finset.single_le_sum (fun b _ => hp0 b) (Finset.mem_univ a)
  have hfB : ∀ x, f x ≤ M := fun x => by
    simp only [hf]; nlinarith [hp1' (cellIdx K x), hp0 (cellIdx K x)]
  have hfabs : ∀ x, |f x| ≤ M := fun x => by rw [abs_of_nonneg (hf0 x)]; exact hfB x
  have hf1 : ∫ x, f x ∂haar d = 1 := by
    rw [integral_comp_cellIdx (fun a => M * p a), ← hMdef, ← Finset.mul_sum, hp1]
    field_simp
  have hprob := isProbabilityMeasure_densMeasure' hf0 hf1
  obtain ⟨hkt, hkv⟩ := klDiv_densMeasure_bdd hfm hf0 hf1 hfB
  refine ⟨⟨densMeasure f, hprob⟩, hkt, ?_⟩
  change (klDiv (densMeasure f) (haar d)).toReal + energyMF V W (densMeasure f) ≤ _
  -- entropy
  have hK : (klDiv (densMeasure f) (haar d)).toReal = ∑ a, p a * Real.log (M * p a) := by
    rw [hkv, integral_comp_cellIdx (fun a => klFun (M * p a)), ← hMdef]
    rw [Finset.sum_div]
    have : ∀ a, klFun (M * p a) / M = p a * Real.log (M * p a) + (1 / M - p a) := fun a => by
      rw [klFun_apply]; field_simp; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hp1, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, hcard]
    field_simp
    simp_rw [mul_comm M]
    ring
  -- bounds for `V` and `W`
  obtain ⟨BV, hBV⟩ := exists_bound_of_continuous hyp.continuous_V
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hVm : Measurable V := hyp.continuous_V.measurable
  -- potential energy
  have hPot : potE V (densMeasure f) ≤ ∑ a, p a * V (cellPt K a) + ω := by
    unfold potE
    rw [integral_densMeasure' hf0 hf1]
    have i1 : Integrable (fun x => f x * V x) (haar d) :=
      integrable_of_abs_le (hfm.mul hVm).aestronglyMeasurable (B := M * BV) fun x => by
        rw [abs_mul]; exact mul_le_mul (hfabs x) (hBV x) (abs_nonneg _) hM.le
    calc ∫ x, f x * V x ∂haar d ≤ ∫ x, M * p (cellIdx K x) * (V (cellPt K (cellIdx K x)) + ω)
          ∂haar d := by
          refine integral_mono i1 ?_ fun x => mul_le_mul_of_nonneg_left ?_ (hf0 x)
          · exact integrable_of_abs_le ((measurable_of_countable
              (fun a => M * p a * (V (cellPt K a) + ω))).comp measurable_cellIdx).aestronglyMeasurable
              (B := ∑ a, |M * p a * (V (cellPt K a) + ω)|) fun x =>
                Finset.single_le_sum (f := fun a => |M * p a * (V (cellPt K a) + ω)|)
                  (fun _ _ => abs_nonneg _) (Finset.mem_univ (cellIdx K x))
          · linarith [(abs_le.mp (hV x)).2]
      _ = ∑ a, p a * V (cellPt K a) + ω := by
          rw [integral_comp_cellIdx (fun a => M * p a * (V (cellPt K a) + ω)), ← hMdef]
          rw [Finset.sum_div]
          have : ∀ a, M * p a * (V (cellPt K a) + ω) / M = p a * V (cellPt K a) + p a * ω :=
            fun a => by field_simp
          simp_rw [this]
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]
  -- interaction energy
  have hInt : interE W (densMeasure f) (densMeasure f) ≤
      ∑ a, ∑ b, p a * p b * W (cellPt K a) (cellPt K b) + ω := by
    unfold interE
    set inner : Torus d → ℝ := fun y => ∫ x, W x y ∂densMeasure f with hinner
    set h : (Fin d → Fin K) → ℝ := fun b => ∑ a, p a * W (cellPt K a) (cellPt K b) + ω with hh
    have hinm : StronglyMeasurable inner :=
      hyp.continuous_W.stronglyMeasurable.integral_prod_left (f := W) (μ := densMeasure f)
    have hinb : ∀ y, |inner y| ≤ BW := fun y => by
      simp only [hinner]
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ x, |W x y| ∂densMeasure f ≤ ∫ _, BW ∂densMeasure f :=
            integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
              (integrable_const BW) (Eventually.of_forall fun x => hBW (x, y))
        _ = BW := by simp
    have hinle : ∀ y, inner y ≤ h (cellIdx K y) := fun y => by
      simp only [hinner, hh]
      rw [integral_densMeasure' hf0 hf1]
      have hWy : Measurable fun x => W x y :=
        (hyp.continuous_W.comp (continuous_id.prodMk continuous_const)).measurable
      have i1 : Integrable (fun x => f x * W x y) (haar d) :=
        integrable_of_abs_le (hfm.mul hWy).aestronglyMeasurable (B := M * BW) fun x => by
          rw [abs_mul]; exact mul_le_mul (hfabs x) (hBW (x, y)) (abs_nonneg _) hM.le
      calc ∫ x, f x * W x y ∂haar d ≤ ∫ x, M * p (cellIdx K x) *
            (W (cellPt K (cellIdx K x)) (cellPt K (cellIdx K y)) + ω) ∂haar d := by
            refine integral_mono i1 ?_ fun x => mul_le_mul_of_nonneg_left ?_ (hf0 x)
            · exact integrable_of_abs_le ((measurable_of_countable (fun a => M * p a *
                (W (cellPt K a) (cellPt K (cellIdx K y)) + ω))).comp
                  measurable_cellIdx).aestronglyMeasurable
                (B := ∑ a, |M * p a * (W (cellPt K a) (cellPt K (cellIdx K y)) + ω)|) fun x =>
                  Finset.single_le_sum
                    (f := fun a => |M * p a * (W (cellPt K a) (cellPt K (cellIdx K y)) + ω)|)
                    (fun _ _ => abs_nonneg _) (Finset.mem_univ (cellIdx K x))
            · linarith [(abs_le.mp (hW x y)).2]
        _ = ∑ a, p a * W (cellPt K a) (cellPt K (cellIdx K y)) + ω := by
            rw [integral_comp_cellIdx (fun a => M * p a *
              (W (cellPt K a) (cellPt K (cellIdx K y)) + ω)), ← hMdef]
            rw [Finset.sum_div]
            have : ∀ a, M * p a * (W (cellPt K a) (cellPt K (cellIdx K y)) + ω) / M =
                p a * W (cellPt K a) (cellPt K (cellIdx K y)) + p a * ω := fun a => by field_simp
            simp_rw [this]
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul]
    rw [integral_densMeasure' hf0 hf1]
    have i1 : Integrable (fun y => f y * inner y) (haar d) :=
      integrable_of_abs_le (hfm.aestronglyMeasurable.mul hinm.aestronglyMeasurable)
        (B := M * BW) fun y => by
          rw [abs_mul]; exact mul_le_mul (hfabs y) (hinb y) (abs_nonneg _) hM.le
    calc ∫ y, f y * inner y ∂haar d ≤ ∫ y, M * p (cellIdx K y) * h (cellIdx K y) ∂haar d := by
          refine integral_mono i1 ?_ fun y => mul_le_mul_of_nonneg_left (hinle y) (hf0 y)
          exact integrable_of_abs_le ((measurable_of_countable (fun b => M * p b * h b)).comp
              measurable_cellIdx).aestronglyMeasurable
            (B := ∑ b, |M * p b * h b|) fun y =>
              Finset.single_le_sum (f := fun b => |M * p b * h b|)
                (fun _ _ => abs_nonneg _) (Finset.mem_univ (cellIdx K y))
      _ = ∑ a, ∑ b, p a * p b * W (cellPt K a) (cellPt K b) + ω := by
          rw [integral_comp_cellIdx (fun b => M * p b * h b), ← hMdef, Finset.sum_div]
          have : ∀ b, M * p b * h b / M = p b * h b := fun b => by field_simp
          simp_rw [this, hh, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul,
            Finset.mul_sum]
          rw [Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          ring
  unfold energyMF cellEnergy
  rw [hK]
  linarith

theorem cnt_eq_mul_typ {C : Type*} [Fintype C] [DecidableEq C] {N : ℕ} (hN : 1 ≤ N)
    (σ : Fin N → C) (a : C) : (cnt σ a : ℝ) = N * typ σ a := by
  have : (N : ℝ) ≠ 0 := by have : (0 : ℝ) < N := by exact_mod_cast hN
                           exact this.ne'
  unfold typ; field_simp

/-- On cells, `H_N ≥ N Φ(p_σ) - 3Nω/2`. -/
theorem hamiltonian_ge_cell {ω : ℝ}
    (hV : ∀ x, |V x - V (cellPt K (cellIdx K x))| ≤ ω)
    (hW : ∀ x y, |W x y - W (cellPt K (cellIdx K x)) (cellPt K (cellIdx K y))| ≤ ω)
    {N : ℕ} (hN : 1 ≤ N) (X : Config N d) :
    N * cellEnergy V W K (typ fun i => cellIdx K (X i)) - 3 / 2 * N * ω ≤
      hamiltonian V W N X := by
  set σ : Fin N → Fin d → Fin K := fun i => cellIdx K (X i) with hσ
  set z := cellPt K
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsV : ∑ i, V (z (σ i)) = N * ∑ a, typ σ a * V (z a) := by
    rw [sum_comp_eq_cnt σ (fun a => V (z a)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [nsmul_eq_mul, cnt_eq_mul_typ hN]; ring
  have hsW : ∑ i, ∑ j, W (z (σ i)) (z (σ j)) =
      (N : ℝ) ^ 2 * ∑ a, ∑ b, typ σ a * typ σ b * W (z a) (z b) := by
    have h1 : ∀ i, ∑ j, W (z (σ i)) (z (σ j)) = N * ∑ b, typ σ b * W (z (σ i)) (z b) := fun i => by
      rw [sum_comp_eq_cnt σ (fun b => W (z (σ i)) (z b)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [nsmul_eq_mul, cnt_eq_mul_typ hN]; ring
    simp_rw [h1]
    rw [sum_comp_eq_cnt σ (fun a => (N : ℝ) * ∑ b, typ σ b * W (z a) (z b)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [nsmul_eq_mul, cnt_eq_mul_typ hN, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hV' : ∑ i, V (z (σ i)) - N * ω ≤ ∑ i, V (X i) := by
    have : ∑ i, V (z (σ i)) ≤ ∑ i, (V (X i) + ω) :=
      Finset.sum_le_sum fun i _ => by linarith [(abs_le.mp (hV (X i))).1]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    linarith
  have hW' : ∑ i, ∑ j, W (z (σ i)) (z (σ j)) - (N : ℝ) ^ 2 * ω ≤ ∑ i, ∑ j, W (X i) (X j) := by
    have : ∑ i, ∑ j, W (z (σ i)) (z (σ j)) ≤ ∑ i, ∑ j, (W (X i) (X j) + ω) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        linarith [(abs_le.mp (hW (X i) (X j))).1]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at this
    nlinarith
  unfold hamiltonian cellEnergy
  rw [hsV] at hV'
  rw [hsW] at hW'
  have e : 1 / (2 * (N : ℝ)) * ((N : ℝ) ^ 2 * ∑ a, ∑ b, typ σ a * typ σ b * W (z a) (z b) -
      (N : ℝ) ^ 2 * ω) = N * ((∑ a, ∑ b, typ σ a * typ σ b * W (z a) (z b)) / 2) - N * ω / 2 := by
    field_simp
  have h2 := mul_le_mul_of_nonneg_left hW' (by positivity : (0 : ℝ) ≤ 1 / (2 * N))
  rw [e] at h2
  nlinarith

/-- **Upper half of Lemma 2.4 at resolution `K`**: `log Z_N ≤ N(3ω - F_*) + K^d log(N+1)`. -/
theorem log_partition_le_cells (hyp : Hyp V W KV KW) {N : ℕ} (hN : 1 ≤ N) {ω : ℝ}
    (hV : ∀ x, |V x - V (cellPt K (cellIdx K x))| ≤ ω)
    (hW : ∀ x y, |W x y - W (cellPt K (cellIdx K x)) (cellPt K (cellIdx K y))| ≤ ω)
    {F : ℝ} (hF : Fstar V W = F) :
    Real.log (partitionFn V W N) ≤ N * (3 * ω - F) + (K : ℝ) ^ d * Real.log (N + 1) := by
  set M : ℝ := (K : ℝ) ^ d with hMdef
  have hM : 0 < M := by have : (0 : ℝ) < K := by exact_mod_cast NeZero.pos K
                        positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set G : (Fin N → Fin d → Fin K) → ℝ := fun σ =>
    Real.exp (-(N * cellEnergy V W K (typ σ)) + 3 / 2 * N * ω) with hG
  -- the free-energy lower bound for every type
  have hΨ : ∀ σ : Fin N → Fin d → Fin K, F - 3 / 2 * ω ≤
      ∑ a, typ σ a * Real.log (M * typ σ a) + cellEnergy V W K (typ σ) := fun σ => by
    obtain ⟨ρ, hk, hle⟩ := freeEnergy_cell_le hyp hV hW (typ_nonneg σ) (sum_typ hN σ)
    have h1 : (F : EReal) ≤ freeEnergy V W ρ := by
      rw [← hF]; exact iInf_le _ ρ
    rw [freeEnergy_eq _ hk, EReal.coe_le_coe_iff] at h1
    linarith
  -- per-type bound
  have hper : ∀ σ : Fin N → Fin d → Fin K, G σ / M ^ N ≤
      Real.exp (N * (3 * ω - F)) * ∏ i, typ σ (σ i) := fun σ => by
    rw [prod_typ hN σ, ← Real.exp_add]
    have hMN : M ^ N = Real.exp (N * Real.log M) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hM N)]
    rw [hMN, hG, ← Real.exp_sub]
    refine Real.exp_le_exp.mpr ?_
    have := hΨ σ
    rw [sum_mul_log_mul (sum_typ hN σ) hM] at this
    nlinarith
  -- integrate
  have hH := continuous_hamiltonian hyp N
  have hint1 : Integrable (fun X => Real.exp (-hamiltonian V W N X)) (volume : Measure (Config N d)) :=
    integrable_of_continuous (Real.continuous_exp.comp hH.neg)
  have hcm : Measurable fun X : Config N d => fun i => cellIdx K (X i) :=
    measurable_pi_iff.mpr fun i => measurable_cellIdx.comp (measurable_pi_apply i)
  have hint2 : Integrable (fun X : Config N d => G fun i => cellIdx K (X i)) volume :=
    integrable_of_abs_le ((measurable_of_countable G).comp hcm).aestronglyMeasurable
      (B := ∑ σ, |G σ|) fun X => Finset.single_le_sum (f := fun σ => |G σ|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  have hZ : partitionFn V W N ≤ (∑ σ, G σ) / M ^ N := by
    unfold partitionFn
    calc ∫ X, Real.exp (-hamiltonian V W N X) ≤ ∫ X : Config N d, G fun i => cellIdx K (X i) :=
          integral_mono hint1 hint2 fun X => by
            simp only [hG]
            refine Real.exp_le_exp.mpr ?_
            have := hamiltonian_ge_cell hV hW hN X
            linarith
      _ = _ := integral_comp_cellIdx_pi G
  have hZ2 : partitionFn V W N ≤ Real.exp (N * (3 * ω - F)) * ((N : ℝ) + 1) ^ (K ^ d) := by
    have hcard : Fintype.card (Fin d → Fin K) = K ^ d := by simp
    refine hZ.trans ?_
    rw [Finset.sum_div]
    calc ∑ σ, G σ / M ^ N ≤ ∑ σ, Real.exp (N * (3 * ω - F)) * ∏ i, typ σ (σ i) :=
          Finset.sum_le_sum fun σ _ => hper σ
      _ = Real.exp (N * (3 * ω - F)) * ∑ σ : Fin N → Fin d → Fin K, ∏ i, typ σ (σ i) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by
          rw [← hcard]
          exact mul_le_mul_of_nonneg_left (sum_prod_typ_le hN) (Real.exp_pos _).le
  have hZ0 : 0 < partitionFn V W N := by
    unfold partitionFn
    exact integral_exp_pos hint1
  have hlog := Real.log_le_log hZ0 hZ2
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_pow] at hlog
  push_cast at hlog
  exact hlog

end Cells

end SharpLSI
