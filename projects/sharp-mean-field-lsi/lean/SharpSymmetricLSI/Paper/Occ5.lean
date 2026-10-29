import SharpSymmetricLSI.Paper.Occ4

/-!
# Completeness of the tensor basis and of the occupation basis (Phase 3, lane D; R28)

If `(e_j)` is complete in `L²(ν)`, the products `∏ᵢ e_{cᵢ}(xᵢ)` are complete in `L²(ν^{⊗N})`
(induction on `N`, Fubini). A symmetric function orthogonal to every `B_{α,N}` is orthogonal to
every such product (they are permutations of the summands of `B_{α,N}`), hence vanishes.
-/

noncomputable section
open MeasureTheory Filter

namespace SharpLSI

section tensor
variable {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
  {e : ℕ → α → ℝ}

/-- `∏ᵢ e_{cᵢ}(xᵢ)`. -/
def tensorE (e : ℕ → α → ℝ) {N : ℕ} (c : Fin N → ℕ) (X : Fin N → α) : ℝ := ∏ i, e (c i) (X i)

theorem measurable_tensorE (hem : ∀ j, Measurable (e j)) {N : ℕ} (c : Fin N → ℕ) :
    Measurable (tensorE e c) :=
  Finset.measurable_prod _ fun i _ => (hem _).comp (measurable_pi_apply i)

theorem memLp_tensorE (hem : ∀ j, Measurable (e j)) (hL : ∀ j, MemLp (e j) 2 ν) {N : ℕ}
    (c : Fin N → ℕ) : MemLp (tensorE e c) 2 (Measure.pi fun _ : Fin N => ν) := by
  refine (memLp_two_iff_integrable_sq (measurable_tensorE hem c).aestronglyMeasurable).mpr ?_
  have : (fun X : Fin N → α => tensorE e c X ^ 2) = fun X => ∏ i, e (c i) (X i) ^ 2 := by
    funext X; simp [tensorE, Finset.prod_pow]
  rw [this]
  exact Integrable.fintype_prod (f := fun i x => e (c i) x ^ 2) fun i => (hL _).integrable_sq

theorem tensorE_cons {N : ℕ} (j : ℕ) (c : Fin N → ℕ) (x : α) (Y : Fin N → α) :
    tensorE e (Fin.cons j c : Fin (N + 1) → ℕ) (Fin.cons x Y) = e j x * tensorE e c Y := by
  simp [tensorE, Fin.prod_univ_succ]

/-- **Completeness of the tensor basis.** -/
theorem tensor_complete (hem : ∀ j, Measurable (e j)) (hL : ∀ j, MemLp (e j) 2 ν)
    (hcomp : ∀ g : α → ℝ, MemLp g 2 ν → (∀ j, ∫ x, g x * e j x ∂ν = 0) → g =ᵐ[ν] 0) :
    ∀ (N : ℕ) (f : (Fin N → α) → ℝ), Measurable f → MemLp f 2 (Measure.pi fun _ : Fin N => ν) →
      (∀ c : Fin N → ℕ, ∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => ν) = 0) →
      f =ᵐ[Measure.pi fun _ : Fin N => ν] 0 := by
  intro N
  induction N with
  | zero =>
    intro f _ _ h
    have h0 := h Fin.elim0
    have hX : ∀ X : Fin 0 → α, X = Fin.elim0 := fun X => funext fun i => i.elim0
    have : ∀ X : Fin 0 → α, f X * tensorE e Fin.elim0 X = f Fin.elim0 := fun X => by
      rw [hX X]; simp [tensorE]
    simp_rw [this] at h0
    rw [integral_const, probReal_univ, one_smul] at h0
    exact Eventually.of_forall fun X => by rw [hX X, h0]; rfl
  | succ n ih =>
    intro f hfm hf hf0
    set P := Measure.pi fun _ : Fin n => ν
    set E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0
    have hmp : MeasurePreserving E (Measure.pi fun _ : Fin (n + 1) => ν) (ν.prod P) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0
    set g : α × (Fin n → α) → ℝ := fun z => f (E.symm z)
    have hgm : Measurable g := hfm.comp E.symm.measurable
    have hg : MemLp g 2 (ν.prod P) := hf.comp_measurePreserving hmp.symm
    have hEs : ∀ x Y, E.symm (x, Y) = Fin.cons x Y := fun x Y => by
      simp [E, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']
    have hfg : ∀ X, f X = g (E X) := fun X => by simp [g]
    -- the partial coefficients
    set h : (Fin n → ℕ) → α → ℝ := fun c x => ∫ Y, g (x, Y) * tensorE e c Y ∂P
    have hgP : ∀ c, Integrable (fun z : α × (Fin n → α) => g z * tensorE e c z.2) (ν.prod P) :=
      fun c => by
        have hP2 : MemLp (fun z : α × (Fin n → α) => tensorE e c z.2) 2 (ν.prod P) :=
          (memLp_tensorE hem hL c).comp_measurePreserving measurePreserving_snd
        exact hg.integrable_mul hP2
    have hhm : ∀ c, Measurable (h c) := fun c =>
      (hgm.mul ((measurable_tensorE hem c).comp measurable_snd)).stronglyMeasurable.integral_prod_right'
        |>.measurable
    have hcoef : ∀ c j, ∫ x, h c x * e j x ∂ν = 0 := fun c j => by
      have hint : Integrable (fun z : α × (Fin n → α) => g z * (e j z.1 * tensorE e c z.2))
          (ν.prod P) := by
        refine hg.integrable_mul (q := 2) ?_
        refine (memLp_two_iff_integrable_sq (((hem j).comp measurable_fst).mul
          ((measurable_tensorE hem c).comp measurable_snd)).aestronglyMeasurable).mpr ?_
        exact ((hL j).integrable_sq.mul_prod (memLp_tensorE hem hL c).integrable_sq).congr
          (Eventually.of_forall fun z => by simp only [Pi.mul_apply, Function.comp]; ring)
      have h1 : ∫ x, h c x * e j x ∂ν = ∫ z, g z * (e j z.1 * tensorE e c z.2) ∂(ν.prod P) := by
        rw [integral_prod _ hint]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [h]
        rw [← integral_mul_const]
        congr 1; funext Y; ring
      have h2 : ∫ z, g z * (e j z.1 * tensorE e c z.2) ∂(ν.prod P) =
          ∫ X, f X * tensorE e (Fin.cons j c : Fin (n + 1) → ℕ) X
            ∂(Measure.pi fun _ : Fin (n + 1) => ν) := by
        rw [← hmp.integral_comp']
        refine integral_congr_ae (Eventually.of_forall fun X => ?_)
        simp only [g, MeasurableEquiv.symm_apply_apply]
        have hX : X = Fin.cons (E X).1 (E X).2 := by rw [← hEs, Prod.mk.eta, E.symm_apply_apply]
        conv_rhs => rw [hX, tensorE_cons]
        rw [← hX]
      rw [h1, h2, hf0]
    -- the coefficients are in `L²`
    have hhL : ∀ c, MemLp (h c) 2 ν := fun c => by
      refine (memLp_two_iff_integrable_sq (hhm c).aestronglyMeasurable).mpr ?_
      set C := ∫ Y, tensorE e c Y ^ 2 ∂P
      have hg2 := hg.integrable_sq
      have hrow : Integrable (fun x => ∫ Y, g (x, Y) ^ 2 ∂P) ν := hg2.integral_prod_left
      refine (hrow.const_mul C).mono' ((hhm c).pow_const 2).aestronglyMeasurable ?_
      filter_upwards [hg2.prod_right_ae] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hxm : MemLp (fun Y => g (x, Y)) 2 P :=
        (memLp_two_iff_integrable_sq (hgm.comp measurable_prodMk_left).aestronglyMeasurable).mpr hx
      have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
        (Eventually.of_forall fun Y => abs_nonneg (g (x, Y)))
        (Eventually.of_forall fun Y => abs_nonneg (tensorE e c Y))
        (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact hxm.abs)
        (by rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_tensorE hem hL c).abs)
      simp only [Real.rpow_two, sq_abs] at hcs
      have hle : |h c x| ≤ ∫ Y, |g (x, Y)| * |tensorE e c Y| ∂P := by
        simp only [h, ← abs_mul]; exact abs_integral_le_integral_abs
      have hA : 0 ≤ ∫ Y, g (x, Y) ^ 2 ∂P := integral_nonneg fun _ => sq_nonneg _
      have hB : 0 ≤ C := integral_nonneg fun _ => sq_nonneg _
      have h3 : |h c x| ≤ (∫ Y, g (x, Y) ^ 2 ∂P) ^ (1 / (2 : ℝ)) * C ^ (1 / (2 : ℝ)) :=
        hle.trans hcs
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h3
      have h4 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      rw [sq_abs, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB] at h4
      linarith
    have hh0 : ∀ c, h c =ᵐ[ν] 0 := fun c => hcomp _ (hhL c) (hcoef c)
    have hall : ∀ᵐ x ∂ν, ∀ c : Fin n → ℕ, h c x = 0 := ae_all_iff.mpr hh0
    have hsec : ∀ᵐ x ∂ν, (fun Y => g (x, Y)) =ᵐ[P] 0 := by
      filter_upwards [hall, hg.integrable_sq.prod_right_ae] with x hx hx2
      refine ih _ (hgm.comp measurable_prodMk_left)
        ((memLp_two_iff_integrable_sq (hgm.comp measurable_prodMk_left).aestronglyMeasurable).mpr
          hx2) fun c => hx c
    have hg0 : g =ᵐ[ν.prod P] 0 := by
      show ∀ᵐ z ∂(ν.prod P), g z = 0
      rw [Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hgm measurable_const)]
      exact hsec
    have := hmp.quasiMeasurePreserving.ae_eq_comp hg0
    refine this.mono fun X hX => ?_
    simp only [Function.comp, Pi.zero_apply] at hX
    rw [hfg X]; exact hX

end tensor


/-! ### Permutations of labellings -/

theorem exists_perm_comp {L : Type*} [Fintype L] [DecidableEq L] {N : ℕ} (c₁ c₂ : Fin N → L)
    (h : ∀ ℓ, (Finset.univ.filter fun i => c₁ i = ℓ).card = (Finset.univ.filter fun i => c₂ i = ℓ).card) :
    ∃ σ : Equiv.Perm (Fin N), c₂ = c₁ ∘ σ := by
  have e : ∀ ℓ, {i // c₂ i = ℓ} ≃ {i // c₁ i = ℓ} := fun ℓ =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype, h ℓ])
  refine ⟨(Equiv.sigmaFiberEquiv c₂).symm.trans ((Equiv.sigmaCongrRight e).trans
    (Equiv.sigmaFiberEquiv c₁)), ?_⟩
  funext i
  simp only [Function.comp, Equiv.trans_apply, Equiv.sigmaFiberEquiv_symm_apply_fst,
    Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply]
  exact ((e (c₂ i)) ⟨i, rfl⟩).2.symm

theorem integral_comp_perm {d N : ℕ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (σ : Equiv.Perm (Fin N)) (F : Config N d → ℝ) :
    ∫ X, F (X ∘ σ) ∂(Measure.pi fun _ : Fin N => μ) = ∫ X, F X ∂(Measure.pi fun _ : Fin N => μ) := by
  have hmp := measurePreserving_piCongrLeft (fun _ : Fin N => μ) σ.symm
  rw [← hmp.integral_comp' F]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  show F (X ∘ σ) = F ((MeasurableEquiv.piCongrLeft (fun _ => Torus d) σ.symm) X)
  congr 1
  funext j
  have := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin N => Torus d) σ.symm X (σ j)
  rw [Equiv.symm_apply_apply] at this
  simpa [MeasurableEquiv.coe_piCongrLeft] using this.symm


/-! ### From the occupation basis to the tensor basis -/

/-- The occupation type of a labelling: `α n = #{i | c i = n + 1}`. -/
def typeOf {N : ℕ} (c : Fin N → ℕ) : ℕ →₀ ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i => c i ≠ 0), Finsupp.single (c i - 1) 1

theorem typeOf_apply {N : ℕ} (c : Fin N → ℕ) (n : ℕ) :
    typeOf c n = (Finset.univ.filter fun i => c i = n + 1).card := by
  rw [typeOf, Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_boole, Nat.cast_id, Finset.filter_filter]
  congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega

theorem occSize_typeOf_le {N : ℕ} (c : Fin N → ℕ) : occSize (typeOf c) ≤ N := by
  rw [occSize_eq_sum_range]
  simp_rw [typeOf_apply]
  rw [← Finset.card_biUnion]
  · exact (Finset.card_le_univ _).trans (by simp)
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro i _ h1 h2; omega

/-- **A symmetric function orthogonal to all `B_{α,N}` is orthogonal to all tensor products.** -/
theorem integral_mul_tensorE_eq_zero {d N : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {e : ℕ → Torus d → ℝ} {f : Config N d → ℝ} (hfsym : IsSymmetric f)
    (hint : ∀ c : Fin N → ℕ, Integrable (fun X => f X * tensorE e c X) (Measure.pi fun _ => μ))
    (horth : ∀ α : ℕ →₀ ℕ, occSize α ≤ N →
      ∫ X, f X * occBasis e α N X ∂(Measure.pi fun _ : Fin N => μ) = 0)
    (c : Fin N → ℕ) : ∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => μ) = 0 := by
  set α := typeOf c
  have hq := occSize_typeOf_le c
  set S := α.support.sup id
  have hlt : ∀ i, c i < S + 2 := fun i => by
    by_cases hci : c i = 0
    · omega
    · have hmem : c i - 1 ∈ α.support := by
        rw [Finsupp.mem_support_iff, typeOf_apply]
        refine Finset.card_ne_zero.mpr ⟨i, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have := support_lt α hmem
      omega
  set ĉ : Fin N → Fin (S + 2) := fun i => ⟨c i, hlt i⟩
  have hĉ : ĉ ∈ occLabellings α N := by
    rw [mem_occLabellings]
    intro n
    rw [typeOf_apply]
  -- every labelling of type `α` gives the same integral
  have hsame : ∀ c' ∈ occLabellings α N,
      ∫ X, f X * ∏ i, e (c' i : ℕ) (X i) ∂(Measure.pi fun _ : Fin N => μ) =
        ∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => μ) := by
    intro c' hc'
    have hfib : ∀ ℓ, (Finset.univ.filter fun i => ĉ i = ℓ).card =
        (Finset.univ.filter fun i => c' i = ℓ).card := by
      have h1 := occLabellings_eq α hq
      have hĉ' : ĉ ∈ fibreLab N (occFibre α N) := h1 ▸ hĉ
      have hc'' : c' ∈ fibreLab N (occFibre α N) := h1 ▸ hc'
      simp only [fibreLab, Finset.mem_filter, Finset.mem_univ, true_and] at hĉ' hc''
      intro ℓ; rw [hĉ' ℓ, hc'' ℓ]
    obtain ⟨σ, hσ⟩ := exists_perm_comp ĉ c' hfib
    have hpt : ∀ X : Config N d, f X * ∏ i, e (c' i : ℕ) (X i) =
        (fun Y => f Y * tensorE e c Y) (X ∘ σ.symm) := by
      intro X
      simp only [tensorE]
      rw [← hfsym σ.symm X]
      congr 1
      rw [hσ, ← Equiv.prod_comp σ.symm]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp [ĉ]
    simp_rw [hpt]
    exact integral_comp_perm μ σ.symm (fun Y => f Y * tensorE e c Y)
  have hB := horth α hq
  unfold occBasis at hB
  simp_rw [mul_comm (Real.sqrt _), ← mul_assoc, Finset.mul_sum] at hB
  rw [integral_mul_const, integral_finsetSum _ fun c' _ => ?_] at hB
  · rw [Finset.sum_congr rfl hsame, Finset.sum_const, nsmul_eq_mul] at hB
    have hpos : 0 < Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ)) := by
      refine Real.sqrt_pos.mpr (div_pos ?_ ?_)
      · exact_mod_cast Nat.pos_of_ne_zero (by unfold occFactorial; simp [Finsupp.prod,
          Finset.prod_ne_zero_iff, Nat.factorial_ne_zero])
      · exact_mod_cast Nat.descFactorial_pos.mpr hq
    have hcard : (0 : ℝ) < (occLabellings α N).card := by
      exact_mod_cast Finset.card_pos.mpr ⟨ĉ, hĉ⟩
    rcases mul_eq_zero.mp hB with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hcard.ne'
      · exact h'
    · exact absurd h hpos.ne'
  · have := hint (fun i => (c' i : ℕ))
    simpa [tensorE] using this


/-! ### R28: completeness of the occupation basis in the symmetric subspace -/

theorem ae_eq_e_mk {d N : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e : ℕ → Torus d → ℝ}
    {lam : ℕ → ℝ} (he : IsRefEigenbasis μ e lam) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ (i : Fin N) (j : ℕ),
      e j (X i) = (he.memLp j).aestronglyMeasurable.mk (e j) (X i) := by
  rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
  exact (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae_eq
    (he.memLp j).aestronglyMeasurable.ae_eq_mk

/-- **Completeness of `(B_{α,N})_{|α| ≤ N}` in the symmetric subspace of `L²(μ^{⊗N})`.** -/
theorem occBasis_complete {d N : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis μ e lam) (f : Config N d → ℝ)
    (hf : MemLp f 2 (Measure.pi fun _ : Fin N => μ)) (hfsym : IsSymmetric f)
    (horth : ∀ α : ℕ →₀ ℕ, occSize α ≤ N →
      ∫ X, f X * occBasis e α N X ∂(Measure.pi fun _ : Fin N => μ) = 0) :
    f =ᵐ[Measure.pi fun _ : Fin N => μ] 0 := by
  set P := Measure.pi fun _ : Fin N => μ
  set e' : ℕ → Torus d → ℝ := fun j => (he.memLp j).aestronglyMeasurable.mk (e j)
  have hem : ∀ j, Measurable (e' j) := fun j =>
    (he.memLp j).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : ∀ j, e j =ᵐ[μ] e' j := fun j => (he.memLp j).aestronglyMeasurable.ae_eq_mk
  have hL : ∀ j, MemLp (e' j) 2 μ := fun j => (he.memLp j).ae_eq (hae j)
  have hcomp : ∀ g : Torus d → ℝ, MemLp g 2 μ → (∀ j, ∫ x, g x * e' j x ∂μ = 0) → g =ᵐ[μ] 0 :=
    fun g hg h => he.complete g hg fun j => by
      rw [← h j]; exact integral_congr_ae ((hae j).mono fun x hx => by simp only [hx])
  have hX := ae_eq_e_mk (N := N) he
  have horth' : ∀ α : ℕ →₀ ℕ, occSize α ≤ N → ∫ X, f X * occBasis e' α N X ∂P = 0 := by
    intro α hα
    rw [← horth α hα]
    refine integral_congr_ae (hX.mono fun X hX => ?_)
    simp only [occBasis]
    congr 2
    refine Finset.sum_congr rfl fun c _ => Finset.prod_congr rfl fun i _ => ?_
    rw [hX i]
  have hint : ∀ c : Fin N → ℕ, Integrable (fun X => f X * tensorE e' c X) P := fun c =>
    hf.integrable_mul (memLp_tensorE hem hL c)
  have h1 : ∀ c : Fin N → ℕ, ∫ X, f X * tensorE e' c X ∂P = 0 := fun c =>
    integral_mul_tensorE_eq_zero hfsym hint horth' c
  -- a measurable representative
  set f' := hf.aestronglyMeasurable.mk f
  have hff : f =ᵐ[P] f' := hf.aestronglyMeasurable.ae_eq_mk
  have h2 : ∀ c : Fin N → ℕ, ∫ X, f' X * tensorE e' c X ∂P = 0 := fun c => by
    rw [← h1 c]; exact integral_congr_ae (hff.mono fun X hX => by simp only [hX])
  exact hff.trans (tensor_complete hem hL hcomp N f'
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable (hf.ae_eq hff) h2)

end SharpLSI
