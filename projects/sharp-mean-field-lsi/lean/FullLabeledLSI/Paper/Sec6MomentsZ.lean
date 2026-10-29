import Mathlib
import FullLabeledLSI.Paper.Sec6MomentsU

/-!
# Fluctuation moment bound (Section 6, item M1)

For i.i.d. `X₁, …, X_N ∼ μ` and a bounded centered observable `f` (`|f| ≤ B` a.e.,
`∫ f dμ = 0`) we prove
`E[(∑_l f(X_l))^{2k}] ≤ C_k N^k B^{2k}`
with `C_k` independent of `N`, `f`, `μ`, and the underlying type, and the normalised version
`E[(N^{-1/2} ∑_l f(X_l))^{2k}] ≤ C_k B^{2k}` for `N ≥ 1`.

Route: expand the power into a sum over tuples `g : Fin (2k) → Fin N`; a term whose integral
does not vanish must have every occurring label appearing at least twice (otherwise integrate
out that coordinate and use centering); hence at most `k` distinct labels occur, and the number
of such tuples is `O_k(N^k)`; each term is bounded by `B^{2k}`.
-/

open MeasureTheory

namespace SharpLSI.FL.Sec6

/-! ### Combinatorics -/

/-- Number of slots of the label tuple `g` carrying the label `j`. -/
def cntL {N r : ℕ} (g : Fin r → Fin N) (j : Fin N) : ℕ :=
  (Finset.univ.filter (fun i => g i = j)).card

/-- No label occurs exactly once in the tuple `g`. -/
def NoSingle {N r : ℕ} (g : Fin r → Fin N) : Prop :=
  ∀ j : Fin N, cntL g j ≠ 1

instance {N r : ℕ} : DecidablePred (@NoSingle N r) := fun g => by
  unfold NoSingle; infer_instance

lemma two_mul_card_le_of_noSingle {N r : ℕ} (g : Fin r → Fin N) (hg : NoSingle g) :
    2 * (Finset.univ.image g).card ≤ r := by
  have hs : ∑ j ∈ Finset.univ.image g, cntL g j = r := by
    have h : (Finset.univ : Finset (Fin r)).card = ∑ j ∈ Finset.univ.image g, cntL g j :=
      Finset.card_eq_sum_card_fiberwise (f := g)
        (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hge : ∀ j ∈ Finset.univ.image g, 2 ≤ cntL g j := by
    intro j hj
    have hne := hg j
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hj
    have : 0 < cntL g j :=
      Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
    omega
  have hsum : (Finset.univ.image g).card • 2 ≤ ∑ j ∈ Finset.univ.image g, cntL g j :=
    Finset.card_nsmul_le_sum _ (fun j => cntL g j) 2 hge
  rw [hs, smul_eq_mul] at hsum
  omega

lemma card_noSingle_le (N k : ℕ) (hN : 1 ≤ N) :
    ((Finset.univ : Finset (Fin (2 * k) → Fin N)).filter (fun g => NoSingle g)).card ≤
      (k + 1) * k ^ (2 * k) * N ^ k := by
  have hcover : (Finset.univ : Finset (Fin (2 * k) → Fin N)).filter (fun g => NoSingle g) ⊆
      ((Finset.univ : Finset (Finset (Fin N))).filter (fun R => R.card ≤ k)).biUnion
        (fun R => Fintype.piFinset (fun _ : Fin (2 * k) => R)) := by
    intro g hg
    rw [Finset.mem_filter] at hg
    rw [Finset.mem_biUnion]
    refine ⟨Finset.univ.image g, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have := two_mul_card_le_of_noSingle g hg.2
      omega
    · rw [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  calc _ ≤ _ := Finset.card_le_card hcover
    _ ≤ ∑ R ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun R => R.card ≤ k),
          (Fintype.piFinset (fun _ : Fin (2 * k) => R)).card := Finset.card_biUnion_le
    _ ≤ ∑ R ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun R => R.card ≤ k),
          k ^ (2 * k) := by
        apply Finset.sum_le_sum
        intro R hR
        have hRr : R.card ≤ k := (Finset.mem_filter.1 hR).2
        rw [Fintype.card_piFinset_const]
        exact Nat.pow_le_pow_left hRr _
    _ = ((Finset.univ : Finset (Finset (Fin N))).filter (fun R => R.card ≤ k)).card *
          k ^ (2 * k) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (k + 1) * N ^ k * k ^ (2 * k) := Nat.mul_le_mul_right _ (card_powerset_le N k hN)
    _ = (k + 1) * k ^ (2 * k) * N ^ k := by ring

lemma card_noSingle_le_all (N k : ℕ) :
    ((Finset.univ : Finset (Fin (2 * k) → Fin N)).filter (fun g => NoSingle g)).card ≤
      (k + 1) * k ^ (2 * k) * N ^ k := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : (Finset.univ : Finset (Fin (2 * k) → Fin 0)).card = 0 ^ (2 * k) := by simp
    calc _ ≤ (Finset.univ : Finset (Fin (2 * k) → Fin 0)).card := Finset.card_filter_le _ _
      _ = 0 ^ (2 * k) := h0
      _ ≤ _ := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp
        · simp [hk.ne']
  · exact card_noSingle_le N k hN

lemma exists_unique_slotL {N r : ℕ} (g : Fin r → Fin N) (j : Fin N) (h : cntL g j = 1) :
    ∃ i₀, g i₀ = j ∧ ∀ i, i ≠ i₀ → g i ≠ j := by
  unfold cntL at h
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.1 h
  have hmem : i₀ ∈ Finset.univ.filter (fun i => g i = j) := by
    rw [hi₀]; exact Finset.mem_singleton_self _
  refine ⟨i₀, (Finset.mem_filter.1 hmem).2, ?_⟩
  intro i hi hpi
  have : i ∈ Finset.univ.filter (fun i => g i = j) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hpi⟩
  rw [hi₀, Finset.mem_singleton] at this
  exact hi this

/-! ### Analysis -/

section AnalysisZ

variable {α : Type} [MeasurableSpace α]

lemma measurable_termL {N r : ℕ} (f : α → ℝ) (hf : Measurable f) (g : Fin r → Fin N) :
    Measurable (fun ω : Fin N → α => ∏ i, f (ω (g i))) :=
  Finset.measurable_prod _ (fun i _ => hf.comp (measurable_pi_apply (g i)))

lemma ae_abs_termL (μ : Measure α) [IsProbabilityMeasure μ] {N r : ℕ} (f : α → ℝ) (B : ℝ)
    (hB : ∀ᵐ x ∂μ, |f x| ≤ B) (g : Fin r → Fin N) :
    ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => μ), |∏ i, f (ω (g i))| ≤ B ^ r := by
  have hall : ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => μ), ∀ i, |f (ω (g i))| ≤ B := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun _ : Fin N => μ) (g i)).quasiMeasurePreserving.ae hB
  filter_upwards [hall] with ω hω
  rw [Finset.abs_prod]
  calc ∏ i, |f (ω (g i))| ≤ ∏ _i : Fin r, B :=
        Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hω i)
    _ = B ^ r := by simp

lemma integrable_termL (μ : Measure α) [IsProbabilityMeasure μ] {N r : ℕ} (f : α → ℝ) (B : ℝ)
    (hf : Measurable f) (hB : ∀ᵐ x ∂μ, |f x| ≤ B) (g : Fin r → Fin N) :
    Integrable (fun ω : Fin N → α => ∏ i, f (ω (g i))) (Measure.pi fun _ : Fin N => μ) :=
  Integrable.of_bound (measurable_termL f hf g).aestronglyMeasurable (B ^ r)
    ((ae_abs_termL μ f B hB g).mono fun ω hω => by rwa [Real.norm_eq_abs])

/-- Vanishing when the label `j` occurs exactly once (at slot `i₀`): integrate out the
coordinate `j`. -/
lemma integral_termL_eq_zero_aux (μ : Measure α) [IsProbabilityMeasure μ] {n r : ℕ}
    (f : α → ℝ) (hf0 : ∫ x, f x ∂μ = 0)
    (g : Fin r → Fin (n + 1)) (j : Fin (n + 1)) (i₀ : Fin r)
    (hg0 : g i₀ = j) (hg : ∀ i, i ≠ i₀ → g i ≠ j)
    (F : (Fin (n + 1) → α) → ℝ) (hF : ∀ ω, F ω = ∏ i, f (ω (g i)))
    (hint : Integrable F (Measure.pi fun _ : Fin (n + 1) => μ)) :
    ∫ ω, F ω ∂(Measure.pi fun _ : Fin (n + 1) => μ) = 0 := by
  obtain ⟨x₀⟩ : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) j
  have hint' := (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)
    (g := F)).2 hint
  have hsymm : ∀ (x : α) (y : Fin n → α),
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) j).symm (x, y) =
        Fin.insertNth (α := fun _ => α) j x y := fun x y => rfl
  have step1 : ∫ ω, F ω ∂(Measure.pi fun _ : Fin (n + 1) => μ) =
      ∫ y, ∫ x, F (Fin.insertNth (α := fun _ => α) j x y) ∂μ ∂(Measure.pi fun _ : Fin n => μ) := by
    rw [← hmp.symm.integral_comp' F]
    have h2 := integral_prod_symm
      (fun z => F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) j).symm z)) hint'
    rw [h2]
    simp only [hsymm]
  have step2 : ∀ y : Fin n → α,
      ∫ x, F (Fin.insertNth (α := fun _ => α) j x y) ∂μ = 0 := by
    intro y
    have hfac : ∀ x : α, F (Fin.insertNth (α := fun _ => α) j x y) =
        f x * ∏ i ∈ Finset.univ.erase i₀,
          f ((Fin.insertNth (α := fun _ => α) j x₀ y) (g i)) := by
      intro x
      rw [hF, ← Finset.mul_prod_erase Finset.univ
        (fun i => f ((Fin.insertNth (α := fun _ => α) j x y) (g i))) (Finset.mem_univ i₀)]
      congr 1
      · rw [hg0, Fin.insertNth_apply_same]
      · refine Finset.prod_congr rfl (fun i hi => ?_)
        have hi0 : i ≠ i₀ := Finset.ne_of_mem_erase hi
        rw [insertNth_apply_eq_of_ne j (g i) (hg i hi0) x x₀ y]
    calc ∫ x, F (Fin.insertNth (α := fun _ => α) j x y) ∂μ
        = ∫ x, f x * ∏ i ∈ Finset.univ.erase i₀,
            f ((Fin.insertNth (α := fun _ => α) j x₀ y) (g i)) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hfac)
      _ = 0 := by rw [integral_mul_const, hf0, zero_mul]
  rw [step1]
  simp [step2]

/-- Vanishing when some label occurs exactly once. -/
lemma integral_termL_eq_zero (μ : Measure α) [IsProbabilityMeasure μ] {N r : ℕ}
    (f : α → ℝ) (hf0 : ∫ x, f x ∂μ = 0) (g : Fin r → Fin N) (j : Fin N)
    (hj : ∃ i₀, g i₀ = j ∧ ∀ i, i ≠ i₀ → g i ≠ j)
    (hint : Integrable (fun ω : Fin N → α => ∏ i, f (ω (g i)))
      (Measure.pi fun _ : Fin N => μ)) :
    ∫ ω, ∏ i, f (ω (g i)) ∂(Measure.pi fun _ : Fin N => μ) = 0 := by
  cases N with
  | zero => exact j.elim0
  | succ n =>
    obtain ⟨i₀, h0, h1⟩ := hj
    exact integral_termL_eq_zero_aux μ f hf0 g j i₀ h0 h1 _ (fun _ => rfl) hint

/-- Main estimate for the `2k`-th moment of a centered i.i.d. sum. -/
theorem sum_moment_bound_aux (μ : Measure α) [IsProbabilityMeasure μ] (N k : ℕ)
    (f : α → ℝ) (B : ℝ) (hf : Measurable f) (hB : ∀ᵐ x ∂μ, |f x| ≤ B)
    (hf0 : ∫ x, f x ∂μ = 0) :
    ∫ ω, (∑ l : Fin N, f (ω l)) ^ (2 * k) ∂(Measure.pi fun _ : Fin N => μ) ≤
      (((k + 1) * k ^ (2 * k) : ℕ) : ℝ) * (N : ℝ) ^ k * B ^ (2 * k) := by
  have hB0 : 0 ≤ B := by
    obtain ⟨z, hz⟩ := hB.exists
    exact (abs_nonneg _).trans hz
  have hexp : ∀ ω : Fin N → α, (∑ l : Fin N, f (ω l)) ^ (2 * k) =
      ∑ g : Fin (2 * k) → Fin N, ∏ i, f (ω (g i)) := by
    intro ω
    rw [Finset.sum_pow' Finset.univ (fun l => f (ω l)) (2 * k), Fintype.piFinset_univ]
  have hint : ∀ g : Fin (2 * k) → Fin N,
      Integrable (fun ω : Fin N → α => ∏ i, f (ω (g i))) (Measure.pi fun _ : Fin N => μ) :=
    fun g => integrable_termL μ f B hf hB g
  have hbound : ∀ g : Fin (2 * k) → Fin N,
      ∫ ω, ∏ i, f (ω (g i)) ∂(Measure.pi fun _ : Fin N => μ) ≤
        if NoSingle g then B ^ (2 * k) else 0 := by
    intro g
    split_ifs with hng
    · calc ∫ ω, ∏ i, f (ω (g i)) ∂(Measure.pi fun _ : Fin N => μ)
          ≤ ∫ _ω, B ^ (2 * k) ∂(Measure.pi fun _ : Fin N => μ) :=
            integral_mono_ae (hint g) (integrable_const _)
              ((ae_abs_termL μ f B hB g).mono fun ω hω => (le_abs_self _).trans hω)
        _ = B ^ (2 * k) := by simp
    · refine le_of_eq ?_
      have hex : ∃ j, cntL g j = 1 := by
        by_contra h
        exact hng (fun j hj => h ⟨j, hj⟩)
      obtain ⟨j, hj⟩ := hex
      exact integral_termL_eq_zero μ f hf0 g j (exists_unique_slotL g j hj) (hint g)
  have hcard := card_noSingle_le_all N k
  calc ∫ ω, (∑ l : Fin N, f (ω l)) ^ (2 * k) ∂(Measure.pi fun _ : Fin N => μ)
      = ∫ ω, ∑ g : Fin (2 * k) → Fin N, ∏ i, f (ω (g i))
        ∂(Measure.pi fun _ : Fin N => μ) :=
        integral_congr_ae (Filter.Eventually.of_forall hexp)
    _ = ∑ g : Fin (2 * k) → Fin N, ∫ ω, ∏ i, f (ω (g i))
        ∂(Measure.pi fun _ : Fin N => μ) := integral_finsetSum _ (fun g _ => hint g)
    _ ≤ ∑ g : Fin (2 * k) → Fin N, (if NoSingle g then B ^ (2 * k) else 0) :=
        Finset.sum_le_sum (fun g _ => hbound g)
    _ = ((((Finset.univ : Finset (Fin (2 * k) → Fin N)).filter (fun g => NoSingle g)).card : ℕ) : ℝ)
          * B ^ (2 * k) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((k + 1) * k ^ (2 * k) * N ^ k : ℕ) : ℝ) * B ^ (2 * k) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (pow_nonneg hB0 _)
    _ = (((k + 1) * k ^ (2 * k) : ℕ) : ℝ) * (N : ℝ) ^ k * B ^ (2 * k) := by
        push_cast; ring

end AnalysisZ

/-- **Fluctuation moment bound (unnormalised).** For i.i.d. `X₁, …, X_N ∼ μ` and a measurable
centered observable `f` with `|f| ≤ B` a.e., `E[(∑_l f(X_l))^{2k}] ≤ C_k N^k B^{2k}` with `C_k`
independent of `N`, `f`, `μ`, `α`. -/
theorem sum_moment_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
      (N : ℕ) (f : α → ℝ) (B : ℝ), Measurable f → (∀ᵐ x ∂μ, |f x| ≤ B) → ∫ x, f x ∂μ = 0 →
      ∫ ω, (∑ l : Fin N, f (ω l)) ^ (2 * k) ∂(Measure.pi fun _ : Fin N => μ)
        ≤ C * (N : ℝ) ^ k * B ^ (2 * k) := by
  refine ⟨(((k + 1) * k ^ (2 * k) : ℕ) : ℝ), Nat.cast_nonneg _, ?_⟩
  intro α _ μ _ N f B hf hB hf0
  exact sum_moment_bound_aux μ N k f B hf hB hf0

/-- **Fluctuation moment bound (normalised).** For `N ≥ 1`,
`E[(N^{-1/2} ∑_l f(X_l))^{2k}] ≤ C_k B^{2k}`. -/
theorem fluct_moment_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α : Type) [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
      (N : ℕ), 1 ≤ N → ∀ (f : α → ℝ) (B : ℝ), Measurable f → (∀ᵐ x ∂μ, |f x| ≤ B) →
      ∫ x, f x ∂μ = 0 →
      ∫ ω, ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l : Fin N, f (ω l)) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin N => μ) ≤ C * B ^ (2 * k) := by
  obtain ⟨C, hC0, hC⟩ := sum_moment_bound k
  refine ⟨C, hC0, ?_⟩
  intro α _ μ _ N hN f B hf hB hf0
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hc2 : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    norm_num [Real.rpow_neg_one]
  have hpt : ∀ ω : Fin N → α,
      ((N : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ l : Fin N, f (ω l)) ^ (2 * k) =
        ((N : ℝ)⁻¹) ^ k * (∑ l : Fin N, f (ω l)) ^ (2 * k) := by
    intro ω
    rw [mul_pow, pow_mul, hc2]
  have hmain := hC α μ N f B hf hB hf0
  have hinv : ((N : ℝ)⁻¹) ^ k * (N : ℝ) ^ k = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hNpos.ne', one_pow]
  simp_rw [hpt]
  rw [integral_const_mul]
  calc ((N : ℝ)⁻¹) ^ k * ∫ ω, (∑ l : Fin N, f (ω l)) ^ (2 * k) ∂(Measure.pi fun _ : Fin N => μ)
      ≤ ((N : ℝ)⁻¹) ^ k * (C * (N : ℝ) ^ k * B ^ (2 * k)) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = C * B ^ (2 * k) * (((N : ℝ)⁻¹) ^ k * (N : ℝ) ^ k) := by ring
    _ = C * B ^ (2 * k) := by rw [hinv, mul_one]

end SharpLSI.FL.Sec6
