import SharpSymmetricLSI.Paper.NBody4

/-!
# Parseval in the symmetric subspace (Phase 3, lane D; R29)

The tensor products `T_c = ∏ e_{cᵢ}(Xᵢ)` form a Hilbert basis of `L²(μ^{⊗N})`. For symmetric `Ψ`,
`⟨Ψ,T_c⟩` depends only on the type of `c`, and `⟨Ψ,B_α⟩² = #L_α · ⟨Ψ,T_c⟩²`; hence
`∑_α ⟨Ψ,B_α⟩² = ∫Ψ²`.
-/

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ} {ν : Measure (Torus d)} [IsProbabilityMeasure ν] {e : ℕ → Torus d → ℝ}

theorem inner_toLp' {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) : ⟪hf.toLp, hg.toLp⟫_ℝ = ∫ x, f x * g x ∂P := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
  simp [mul_comm]

section hb
variable (hem : ∀ j, Measurable (e j)) (hL : ∀ j, MemLp (e j) 2 ν)
  (horth : ∀ i j, ∫ x, e i x * e j x ∂ν = if i = j then 1 else 0)
  (hcomp : ∀ g : Torus d → ℝ, MemLp g 2 ν → (∀ j, ∫ x, g x * e j x ∂ν = 0) → g =ᵐ[ν] 0)

include horth in
theorem integral_tensorE_mul (c c' : Fin N → ℕ) :
    ∫ X, tensorE e c X * tensorE e c' X ∂(Measure.pi fun _ : Fin N => ν) =
      if c = c' then 1 else 0 := by
  have : (fun X : Fin N → Torus d => tensorE e c X * tensorE e c' X) =
      fun X => ∏ i, e (c i) (X i) * e (c' i) (X i) := by
    funext X; simp only [tensorE, ← Finset.prod_mul_distrib]
  rw [this, integral_fintype_prod_eq_prod (f := fun i x => e (c i) x * e (c' i) x)]
  simp_rw [horth]
  by_cases h : c = c'
  · subst h; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The tensor basis as vectors of `L²(μ^{⊗N})`. -/
def tensorVec (c : Fin N → ℕ) : Lp ℝ 2 (Measure.pi fun _ : Fin N => ν) :=
  (memLp_tensorE hem hL c).toLp

include horth in
theorem orthonormal_tensorVec : Orthonormal ℝ (tensorVec (N := N) hem hL) := by
  rw [orthonormal_iff_ite]
  intro c c'
  rw [tensorVec, tensorVec, inner_toLp', integral_tensorE_mul horth]

include hcomp in
theorem tensorVec_span :
    (Submodule.span ℝ (Set.range (tensorVec (N := N) hem hL)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  rw [Submodule.mem_orthogonal'] at hw
  have hz : ∀ c, ∫ X, w X * tensorE e c X ∂(Measure.pi fun _ : Fin N => ν) = 0 := fun c => by
    have := hw (tensorVec hem hL c) (Submodule.subset_span ⟨c, rfl⟩)
    rw [L2.inner_def] at this
    rw [← this]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_tensorE hem hL c).coeFn_toLp] with x hx
    simp only [tensorVec]
    rw [hx, real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial]
    simp [mul_comm]
  have h0 := tensor_complete hem hL hcomp N w (Lp.stronglyMeasurable w).measurable (Lp.memLp w) hz
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr h0

/-- The tensor Hilbert basis of `L²(μ^{⊗N})`. -/
def tensorHB : HilbertBasis (Fin N → ℕ) ℝ (Lp ℝ 2 (Measure.pi fun _ : Fin N => ν)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_tensorVec hem hL horth) (tensorVec_span hem hL hcomp)

include hem hL horth hcomp in
/-- **Parseval for the tensor basis.** -/
theorem hasSum_sq_tensor {f : Config N d → ℝ} (hf : MemLp f 2 (Measure.pi fun _ : Fin N => ν)) :
    HasSum (fun c => (∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => ν)) ^ 2)
      (∫ X, f X ^ 2 ∂(Measure.pi fun _ : Fin N => ν)) := by
  have h := (tensorHB hem hL horth hcomp).hasSum_inner_mul_inner hf.toLp hf.toLp
  have hc : ∀ c, ⟪hf.toLp, (tensorHB hem hL horth hcomp) c⟫_ℝ *
      ⟪(tensorHB hem hL horth hcomp) c, hf.toLp⟫_ℝ =
      (∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => ν)) ^ 2 := fun c => by
    have hb : (tensorHB hem hL horth hcomp) c = tensorVec hem hL c := by
      simp only [tensorHB, HilbertBasis.coe_mkOfOrthogonalEqBot]
    rw [hb, tensorVec, real_inner_comm (hf.toLp), inner_toLp' hf (memLp_tensorE hem hL c), sq]
  rw [show (fun c => ⟪hf.toLp, (tensorHB hem hL horth hcomp) c⟫_ℝ *
      ⟪(tensorHB hem hL horth hcomp) c, hf.toLp⟫_ℝ) = fun c =>
      (∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => ν)) ^ 2 from funext hc,
    inner_toLp' hf hf] at h
  simpa [sq] using h

end hb

/-! ### Symmetric functions -/

theorem typeOf_val_of_mem {α : ℕ →₀ ℕ} {c : Fin N → Fin (α.support.sup id + 2)}
    (hc : c ∈ occLabellings α N) : typeOf (fun i => (c i : ℕ)) = α := by
  ext n
  rw [typeOf_apply, ← mem_occLabellings.mp hc n]

theorem occSize_le_of_mem {α : ℕ →₀ ℕ} {c : Fin N → Fin (α.support.sup id + 2)}
    (hc : c ∈ occLabellings α N) : occSize α ≤ N :=
  typeOf_val_of_mem hc ▸ occSize_typeOf_le _

/-- The labelling `ĉ ∈ L_α` attached to a `ℕ`-valued `c` of type `α`. -/
def hatLab (c : Fin N → ℕ) : Fin N → Fin ((typeOf c).support.sup id + 2) := fun i =>
  ⟨c i, by
    by_cases hci : c i = 0
    · omega
    · have hmem : c i - 1 ∈ (typeOf c).support := by
        rw [Finsupp.mem_support_iff, typeOf_apply]
        refine Finset.card_ne_zero.mpr ⟨i, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      have := support_lt (typeOf c) hmem
      omega⟩

theorem hatLab_mem (c : Fin N → ℕ) : hatLab c ∈ occLabellings (typeOf c) N := by
  rw [mem_occLabellings]; intro n; rw [typeOf_apply]; rfl

section sym
variable {f : Config N d → ℝ} (hfsym : IsSymmetric f)
  (hint : ∀ c : Fin N → ℕ, Integrable (fun X => f X * tensorE e c X) (Measure.pi fun _ => ν))
include hfsym hint

/-- All labellings of the same type give the same coefficient. -/
theorem integral_tensor_eq_of_mem (c : Fin N → ℕ) {c' : Fin N → Fin ((typeOf c).support.sup id + 2)}
    (hc' : c' ∈ occLabellings (typeOf c) N) :
    ∫ X, f X * ∏ i, e (c' i : ℕ) (X i) ∂(Measure.pi fun _ : Fin N => ν) =
      ∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => ν) := by
  have hq := occSize_typeOf_le c
  have hfib : ∀ ℓ, (Finset.univ.filter fun i => hatLab c i = ℓ).card =
      (Finset.univ.filter fun i => c' i = ℓ).card := by
    have h1 := occLabellings_eq (typeOf c) hq
    have hĉ' : hatLab c ∈ fibreLab N (occFibre (typeOf c) N) := h1 ▸ hatLab_mem c
    have hc'' : c' ∈ fibreLab N (occFibre (typeOf c) N) := h1 ▸ hc'
    simp only [fibreLab, Finset.mem_filter, Finset.mem_univ, true_and] at hĉ' hc''
    intro ℓ; rw [hĉ' ℓ, hc'' ℓ]
  obtain ⟨σ, hσ⟩ := exists_perm_comp (hatLab c) c' hfib
  have hpt : ∀ X : Config N d, f X * ∏ i, e (c' i : ℕ) (X i) =
      (fun Y => f Y * tensorE e c Y) (X ∘ σ.symm) := by
    intro X
    simp only [tensorE]
    rw [← hfsym σ.symm X]
    congr 1
    rw [hσ, ← Equiv.prod_comp σ.symm]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [hatLab]
  simp_rw [hpt]
  exact integral_comp_perm ν σ.symm (fun Y => f Y * tensorE e c Y)

/-- `⟨f, B_α⟩ = s_α #L_α ⟨f, T_c⟩` for `c` of type `α`. -/
theorem integral_occBasis_eq (c : Fin N → ℕ) :
    ∫ X, f X * occBasis e (typeOf c) N X ∂(Measure.pi fun _ : Fin N => ν) =
      Real.sqrt ((occFactorial (typeOf c) : ℝ) / (N.descFactorial (occSize (typeOf c)) : ℝ)) *
        (occLabellings (typeOf c) N).card *
          ∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => ν) := by
  unfold occBasis
  have hint' : ∀ c' ∈ occLabellings (typeOf c) N,
      Integrable (fun X => f X * ∏ i, e (c' i : ℕ) (X i)) (Measure.pi fun _ : Fin N => ν) :=
    fun c' _ => by simpa [tensorE] using hint (fun i => (c' i : ℕ))
  simp_rw [mul_comm (Real.sqrt _), ← mul_assoc, Finset.mul_sum]
  rw [integral_mul_const, integral_finsetSum _ hint',
    Finset.sum_congr rfl fun c' hc' => integral_tensor_eq_of_mem hfsym hint c hc',
    Finset.sum_const, nsmul_eq_mul]
  ring

theorem integral_occBasis_eq' (c : Fin N → ℕ) (α : ℕ →₀ ℕ) (hα : typeOf c = α) :
    ∫ X, f X * occBasis e α N X ∂(Measure.pi fun _ : Fin N => ν) =
      Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ)) *
        (occLabellings α N).card *
          ∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => ν) := by
  subst hα; exact integral_occBasis_eq hfsym hint c

theorem integral_tensor_eq_of_typeOf {c₁ c₂ : Fin N → ℕ} (h : typeOf c₁ = typeOf c₂) :
    ∫ X, f X * tensorE e c₂ X ∂(Measure.pi fun _ : Fin N => ν) =
      ∫ X, f X * tensorE e c₁ X ∂(Measure.pi fun _ : Fin N => ν) := by
  set α := typeOf c₁
  have h1 := integral_occBasis_eq' hfsym hint c₁ α rfl
  have h2 := integral_occBasis_eq' hfsym hint c₂ α h.symm
  have hq := occSize_typeOf_le c₁
  have hpos : 0 < Real.sqrt ((occFactorial α : ℝ) / (N.descFactorial (occSize α) : ℝ)) *
      (occLabellings α N).card := by
    refine mul_pos (Real.sqrt_pos.mpr (div_pos ?_ ?_)) ?_
    · exact_mod_cast Nat.pos_of_ne_zero (by unfold occFactorial; simp [Finsupp.prod,
        Finset.prod_ne_zero_iff, Nat.factorial_ne_zero])
    · exact_mod_cast Nat.descFactorial_pos.mpr hq
    · exact_mod_cast Finset.card_pos.mpr ⟨_, hatLab_mem c₁⟩
  rw [h1] at h2
  exact (mul_left_cancel₀ hpos.ne' h2).symm

/-- The fibre bound `∑_{c ∈ C, type c = α} ⟨f,T_c⟩² ≤ ⟨f,B_α⟩²`. -/
theorem sum_fibre_le (C : Finset (Fin N → ℕ)) (α : ℕ →₀ ℕ) :
    ∑ c ∈ C.filter (fun c => typeOf c = α),
        (∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => ν)) ^ 2 ≤
      (∫ X, f X * occBasis e α N X ∂(Measure.pi fun _ : Fin N => ν)) ^ 2 := by
  rcases (C.filter fun c => typeOf c = α).eq_empty_or_nonempty with h0 | ⟨c0, hc0⟩
  · rw [h0, Finset.sum_empty]; positivity
  have hc0α : typeOf c0 = α := (Finset.mem_filter.mp hc0).2
  subst hc0α
  set a := ∫ X, f X * tensorE e c0 X ∂(Measure.pi fun _ : Fin N => ν)
  have hconst : ∀ c ∈ C.filter (fun c => typeOf c = typeOf c0),
      (∫ X, f X * tensorE e c X ∂(Measure.pi fun _ : Fin N => ν)) ^ 2 = a ^ 2 := fun c hc => by
    rw [integral_tensor_eq_of_typeOf hfsym hint (Finset.mem_filter.mp hc).2.symm]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, integral_occBasis_eq hfsym hint c0]
  set M := (typeOf c0).support.sup id
  have hcard : (C.filter fun c => typeOf c = typeOf c0).card ≤
      (occLabellings (typeOf c0) N).card := by
    have hbound : ∀ c ∈ C.filter (fun c => typeOf c = typeOf c0), ∀ i, c i ≤ M + 1 := by
      intro c hc i
      have ht := (Finset.mem_filter.mp hc).2
      by_cases hci : c i = 0
      · omega
      · have hmem : c i - 1 ∈ (typeOf c0).support := by
          rw [← ht, Finsupp.mem_support_iff, typeOf_apply]
          refine Finset.card_ne_zero.mpr ⟨i, ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
        have := Finset.le_sup (f := id) hmem
        simp only [id] at this
        omega
    refine Finset.card_le_card_of_injOn (fun c i => (⟨min (c i) (M + 1), by omega⟩ : Fin (M + 2)))
      (fun c hc => ?_) (fun c hc c' hc' h => ?_)
    · show _ ∈ occLabellings (typeOf c0) N
      rw [mem_occLabellings]
      rw [Finset.mem_coe] at hc
      intro n
      have ht := (Finset.mem_filter.mp hc).2
      have h1 := typeOf_apply c n
      rw [ht] at h1
      rw [h1]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, min_eq_left (hbound c hc i)]
    · rw [Finset.mem_coe] at hc hc'
      funext i
      have := congrFun h i
      simp only [Fin.mk.injEq] at this
      rwa [min_eq_left (hbound c hc i), min_eq_left (hbound c' hc' i)] at this
  have hq := occSize_typeOf_le c0
  have hL := card_occLabellings (typeOf c0) hq
  have hpos : (0 : ℝ) < N.descFactorial (occSize (typeOf c0)) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hq
  have hs : Real.sqrt ((occFactorial (typeOf c0) : ℝ) / (N.descFactorial (occSize (typeOf c0)) : ℝ))
      ^ 2 * ((occLabellings (typeOf c0) N).card : ℝ) ^ 2 = (occLabellings (typeOf c0) N).card := by
    rw [Real.sq_sqrt (by positivity)]
    have hL' : ((occLabellings (typeOf c0) N).card : ℝ) * occFactorial (typeOf c0) =
        N.descFactorial (occSize (typeOf c0)) := by
      exact_mod_cast hL
    field_simp
    rw [← hL']; ring
  calc ((C.filter fun c => typeOf c = typeOf c0).card : ℝ) * a ^ 2 ≤
        ((occLabellings (typeOf c0) N).card : ℝ) * a ^ 2 := by
        gcongr
    _ = _ := by rw [mul_pow, mul_pow, hs]

end sym

section parseval
variable (hem : ∀ j, Measurable (e j)) (hL : ∀ j, MemLp (e j) 2 ν)
  (horth : ∀ i j, ∫ x, e i x * e j x ∂ν = if i = j then 1 else 0)
  (hcomp : ∀ g : Torus d → ℝ, MemLp g 2 ν → (∀ j, ∫ x, g x * e j x ∂ν = 0) → g =ᵐ[ν] 0)
include hem hL horth hcomp

theorem occBasis_eq_zero_of_lt {α : ℕ →₀ ℕ} (h : N < occSize α) : occBasis e α N = 0 := by
  funext X
  unfold occBasis
  rw [Finset.sum_eq_zero fun c hc => absurd (occSize_le_of_mem hc) (by omega), mul_zero]
  rfl

/-- **Parseval in the symmetric subspace**: `∑_α ⟨f,B_α⟩² = ∫ f²` for symmetric `f ∈ L²`. -/
theorem hasSum_sq_occ {f : Config N d → ℝ} (hf : MemLp f 2 (Measure.pi fun _ : Fin N => ν))
    (hfsym : IsSymmetric f) :
    HasSum (fun α => (∫ X, f X * occBasis e α N X ∂(Measure.pi fun _ : Fin N => ν)) ^ 2)
      (∫ X, f X ^ 2 ∂(Measure.pi fun _ : Fin N => ν)) := by
  set P := Measure.pi fun _ : Fin N => ν
  have hint : ∀ c : Fin N → ℕ, Integrable (fun X => f X * tensorE e c X) P := fun c =>
    hf.integrable_mul (memLp_tensorE hem hL c)
  have hB : ∀ α, MemLp (occBasis e α N) 2 P := fun α => by
    unfold occBasis
    exact (memLp_finsetSum _ fun c _ => memLp_prod_eval fun i => hL _).const_mul _
  refine hasSum_of_isLUB_of_nonneg _ (fun α => sq_nonneg _) ⟨?_, ?_⟩
  · -- Bessel
    rintro _ ⟨S, rfl⟩
    dsimp only
    set S' := S.filter fun α => occSize α ≤ N
    have hzero : ∀ α ∈ S, α ∉ S' → (∫ X, f X * occBasis e α N X ∂P) ^ 2 = 0 := fun α hα hα' => by
      have : N < occSize α := by
        by_contra h; exact hα' (Finset.mem_filter.mpr ⟨hα, by omega⟩)
      rw [occBasis_eq_zero_of_lt hem hL horth hcomp this]; simp
    rw [← Finset.sum_subset (Finset.filter_subset _ S) hzero]
    set c : (ℕ →₀ ℕ) → ℝ := fun α => ∫ X, f X * occBasis e α N X ∂P
    have h := expand_sq_nonneg (P := P) (ι := Unit) S' (fun X _ => f X)
      (fun α X _ => occBasis e α N X) c (fun _ => hf) (fun α _ => hB α)
    simp only [Finset.univ_unique, Finset.sum_singleton] at h
    have horthB : ∀ α ∈ S', ∀ β ∈ S', ∫ X, occBasis e α N X * occBasis e β N X ∂P =
        if α = β then 1 else 0 := fun α hα β hβ =>
      integral_occBasis_mul hL horth (Finset.mem_filter.mp hα).2 (Finset.mem_filter.mp hβ).2
    have h3 : ∑ α ∈ S', ∑ β ∈ S', c α * c β * ∫ X, occBasis e α N X * occBasis e β N X ∂P =
        ∑ α ∈ S', c α ^ 2 := by
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [Finset.sum_congr rfl fun β hβ => by rw [horthB α hα β hβ]]
      simp [Finset.sum_ite_eq, hα, sq]
    have h2 : ∑ α ∈ S', c α * ∫ X, f X * occBasis e α N X ∂P = ∑ α ∈ S', c α ^ 2 :=
      Finset.sum_congr rfl fun α _ => by simp [c, sq]
    rw [h2, h3] at h
    show ∑ α ∈ S', c α ^ 2 ≤ _
    linarith
  · -- the tensor Parseval identity bounds `∫ f²` by the occupation sums
    intro b hb
    have hT := hasSum_sq_tensor hem hL horth hcomp hf
    rw [← hT.tsum_eq]
    refine Real.tsum_le_of_sum_le (fun c => sq_nonneg _) fun C => ?_
    rw [← Finset.sum_fiberwise_of_maps_to (t := C.image typeOf) (g := typeOf)
      (fun c hc => Finset.mem_image_of_mem _ hc)]
    exact (Finset.sum_le_sum fun α _ => sum_fibre_le hfsym hint C α).trans
      (hb ⟨C.image typeOf, rfl⟩)

end parseval

end SharpLSI
