import Mathlib
import SharpSymmetricLSI.Infra.EntropyTensor

/-!
# Tensorization of a one-particle log-Sobolev inequality for the entropy of squares

Let `μ` be a probability measure on `α`, `A` an abstract admissibility predicate on functions
`α → ℝ`, and `Γ f : α → ℝ` an abstract "carré du champ" of `f`.  Assume the one-particle
inequality

`Ent_μ(f²) ≤ C ∫ Γ f dμ`   for admissible, measurable, bounded `f` bounded away from zero.

Then on the finite product `Fin N → α` with `Measure.pi (fun _ => μ)`, for admissible slices,

`Ent(F²) ≤ C ∑ᵢ ∫ Γ (slice F x i) (x i) dμ^{⊗N}(x)`,

where `slice F x i = F (update x i ·)` is the one-variable slice of `F` through `x` in the
coordinate `i`.  The proof is induction on `N`, splitting off the first coordinate with
`measurePreserving_piFinSuccAbove` and using the subadditivity of the entropy
(`SharpLSI.entR_prod_le`).

* `slice` : the slice of `F` through `x` in coordinate `i`;
* `entR_pi_le` : the tensorized inequality.
-/

open MeasureTheory

namespace SharpLSI.FL.Tensor

/-- The slice of `F` through `x` in coordinate `i`. -/
def slice {α : Type*} {N : ℕ} (F : (Fin N → α) → ℝ) (x : Fin N → α) (i : Fin N) : α → ℝ :=
  fun y => F (Function.update x i y)

section Slice

variable {α : Type*}

lemma slice_apply {N : ℕ} (F : (Fin N → α) → ℝ) (x : Fin N → α) (i : Fin N) (y : α) :
    slice F x i y = F (Function.update x i y) := rfl

lemma slice_cons_tail {N : ℕ} (F : (Fin (N + 1) → α) → ℝ) (a : α) (y : Fin N → α) (i : Fin N) :
    slice (fun y' => F (Fin.cons a y' : Fin (N + 1) → α)) y i =
      slice F (Fin.cons a y : Fin (N + 1) → α) i.succ := by
  funext w
  simp only [slice_apply, Fin.cons_update]

lemma slice_cons_zero {N : ℕ} (F : (Fin (N + 1) → α) → ℝ) (a : α) (y : Fin N → α) :
    slice F (Fin.cons a y : Fin (N + 1) → α) 0 = fun w => F (Fin.cons w y : Fin (N + 1) → α) := by
  funext w
  simp only [slice_apply, Fin.update_cons_zero]

end Slice

section Aux

variable {α : Type*} [MeasurableSpace α]

/-- The `N`-fold product measure on `Fin N → α`. -/
noncomputable abbrev piMeas (μ : Measure α) (N : ℕ) : Measure (Fin N → α) :=
  Measure.pi (fun _ : Fin N => μ)

/-! ### Elementary measure-theoretic lemmas -/

lemma entR_const {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]
    (t : ℝ) : SharpLSI.entR ρ (fun _ => t) = 0 := by
  unfold SharpLSI.entR
  simp

lemma abs_integral_le_of_bdd {X : Type*} [MeasurableSpace X] {ρ : Measure X}
    [IsProbabilityMeasure ρ] {f : X → ℝ} (hf : AEStronglyMeasurable f ρ) {K : ℝ}
    (hK : ∀ y, |f y| ≤ K) : |∫ y, f y ∂ρ| ≤ K := by
  obtain ⟨h1, h2⟩ := SharpLSI.integral_mem_Icc (ρ := ρ) hf (c := -K) (C := K)
    (fun y => (abs_le.1 (hK y)).1) (fun y => (abs_le.1 (hK y)).2)
  exact abs_le.2 ⟨h1, h2⟩

lemma integrable_integral_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : X × Y → ℝ} (hH : Measurable H) {K : ℝ} (hK : ∀ z, |H z| ≤ K) :
    Integrable (fun x => ∫ y, H (x, y) ∂ν) μ :=
  Integrable.of_bound (SharpLSI.measurable_integral_right (ν := ν) hH).aestronglyMeasurable K
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_bdd (hH.comp measurable_prodMk_left).aestronglyMeasurable
        (fun y => hK _))

lemma integrable_integral_snd {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {H : X × Y → ℝ} (hH : Measurable H) {K : ℝ} (hK : ∀ z, |H z| ≤ K) :
    Integrable (fun y => ∫ x, H (x, y) ∂μ) ν :=
  Integrable.of_bound (SharpLSI.measurable_integral_left (μ := μ) hH).aestronglyMeasurable K
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_bdd (hH.comp measurable_prodMk_right).aestronglyMeasurable
        (fun x => hK _))

/-! ### Splitting off the first coordinate -/

lemma piFinSuccAbove_zero_symm {n : ℕ} (x : α) (y : Fin n → α) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm (x, y) =
      (Fin.cons x y : Fin (n + 1) → α) := by
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
  exact Fin.insertNth_zero' x y

lemma measurable_cons (N : ℕ) :
    Measurable (fun z : α × (Fin N → α) => (Fin.cons z.1 z.2 : Fin (N + 1) → α)) := by
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => α) 0).symm.measurable
  have e : (fun z : α × (Fin N → α) => (Fin.cons z.1 z.2 : Fin (N + 1) → α)) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => α) 0).symm := by
    funext z
    exact (piFinSuccAbove_zero_symm z.1 z.2).symm
  rw [e]
  exact h

lemma measurable_cons_left (N : ℕ) (a : α) :
    Measurable (fun y : Fin N → α => (Fin.cons a y : Fin (N + 1) → α)) :=
  (measurable_cons N).comp measurable_prodMk_left

lemma measurable_cons_right (N : ℕ) (y : Fin N → α) :
    Measurable (fun a : α => (Fin.cons a y : Fin (N + 1) → α)) :=
  (measurable_cons N).comp measurable_prodMk_right

section Prob

variable (μ : Measure α) [IsProbabilityMeasure μ]

lemma mp_cons (N : ℕ) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => α) 0).symm
      (μ.prod (piMeas μ N)) (piMeas μ (N + 1)) :=
  (measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) 0).symm

lemma integral_pi_succ_prod (N : ℕ) (H : (Fin (N + 1) → α) → ℝ) :
    ∫ x, H x ∂(piMeas μ (N + 1)) =
      ∫ z, H (Fin.cons z.1 z.2 : Fin (N + 1) → α) ∂(μ.prod (piMeas μ N)) := by
  rw [← (mp_cons μ N).integral_comp' H]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact congrArg H (piFinSuccAbove_zero_symm z.1 z.2)

lemma entR_succ_eq (N : ℕ) (f : (Fin (N + 1) → α) → ℝ) :
    SharpLSI.entR (piMeas μ (N + 1)) f =
      SharpLSI.entR (μ.prod (piMeas μ N)) (fun z => f (Fin.cons z.1 z.2 : Fin (N + 1) → α)) := by
  unfold SharpLSI.entR
  rw [integral_pi_succ_prod μ N (fun x => f x * Real.log (f x)), integral_pi_succ_prod μ N f]

lemma integrable_cons {N : ℕ} {H : (Fin (N + 1) → α) → ℝ} (hH : Measurable H) {K : ℝ}
    (hK : ∀ x, |H x| ≤ K) :
    Integrable (fun z : α × (Fin N → α) => H (Fin.cons z.1 z.2 : Fin (N + 1) → α))
      (μ.prod (piMeas μ N)) :=
  Integrable.of_bound (hH.comp (measurable_cons N)).aestronglyMeasurable K
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hK _)

lemma integral_pi_succ_left (N : ℕ) {H : (Fin (N + 1) → α) → ℝ} (hH : Measurable H) {K : ℝ}
    (hK : ∀ x, |H x| ≤ K) :
    ∫ x, H x ∂(piMeas μ (N + 1)) =
      ∫ a, ∫ y, H (Fin.cons a y : Fin (N + 1) → α) ∂(piMeas μ N) ∂μ := by
  rw [integral_pi_succ_prod μ N H]
  exact integral_prod (fun z : α × (Fin N → α) => H (Fin.cons z.1 z.2 : Fin (N + 1) → α))
    (integrable_cons μ hH hK)

lemma integral_pi_succ_right (N : ℕ) {H : (Fin (N + 1) → α) → ℝ} (hH : Measurable H) {K : ℝ}
    (hK : ∀ x, |H x| ≤ K) :
    ∫ x, H x ∂(piMeas μ (N + 1)) =
      ∫ y, ∫ a, H (Fin.cons a y : Fin (N + 1) → α) ∂μ ∂(piMeas μ N) := by
  rw [integral_pi_succ_prod μ N H]
  exact integral_prod_symm (fun z : α × (Fin N → α) => H (Fin.cons z.1 z.2 : Fin (N + 1) → α))
    (integrable_cons μ hH hK)

lemma integrable_integral_cons_left {N : ℕ} {H : (Fin (N + 1) → α) → ℝ} (hH : Measurable H)
    {K : ℝ} (hK : ∀ x, |H x| ≤ K) :
    Integrable (fun a => ∫ y, H (Fin.cons a y : Fin (N + 1) → α) ∂(piMeas μ N)) μ :=
  integrable_integral_fst (H := fun z : α × (Fin N → α) => H (Fin.cons z.1 z.2 : Fin (N + 1) → α))
    (hH.comp (measurable_cons N)) (fun _ => hK _)

lemma integrable_integral_cons_right {N : ℕ} {H : (Fin (N + 1) → α) → ℝ} (hH : Measurable H)
    {K : ℝ} (hK : ∀ x, |H x| ≤ K) :
    Integrable (fun y => ∫ a, H (Fin.cons a y : Fin (N + 1) → α) ∂μ) (piMeas μ N) :=
  integrable_integral_snd (H := fun z : α × (Fin N → α) => H (Fin.cons z.1 z.2 : Fin (N + 1) → α))
    (hH.comp (measurable_cons N)) (fun _ => hK _)

/-! ### The induction -/

theorem entR_pi_le_aux (A : (α → ℝ) → Prop) (Γ : (α → ℝ) → α → ℝ) (C : ℝ)
    (hLSI : ∀ f : α → ℝ, A f → Measurable f → (∃ c, 0 < c ∧ ∀ y, c ≤ f y) →
      (∃ B, ∀ y, f y ≤ B) → SharpLSI.entR μ (fun y => f y ^ 2) ≤ C * ∫ y, Γ f y ∂μ)
    {c B : ℝ} (hc : 0 < c) (N : ℕ) :
    ∀ F : (Fin N → α) → ℝ, Measurable F → (∀ x, c ≤ F x) → (∀ x, F x ≤ B) →
      (∀ x i, A (slice F x i)) → (∀ i, Measurable fun x => Γ (slice F x i) (x i)) →
      (∃ K, ∀ x i, |Γ (slice F x i) (x i)| ≤ K) →
      SharpLSI.entR (piMeas μ N) (fun x => F x ^ 2) ≤
        C * ∑ i, ∫ x, Γ (slice F x i) (x i) ∂(piMeas μ N) := by
  induction N with
  | zero =>
    intro F _ _ _ _ _ _
    have hconst : (fun x : Fin 0 → α => F x ^ 2) = fun _ => F (fun i => i.elim0) ^ 2 := by
      funext x
      rw [Subsingleton.elim x (fun i => i.elim0)]
    rw [hconst, entR_const]
    simp
  | succ n ih =>
    intro F hFm hFc hFB hA hΓm hΓb
    obtain ⟨K, hK⟩ := hΓb
    obtain ⟨a₀⟩ : Nonempty α := nonempty_of_isProbabilityMeasure μ
    -- the carré du champ terms
    obtain ⟨H, hH⟩ : ∃ H : Fin (n + 1) → (Fin (n + 1) → α) → ℝ,
        ∀ i x, H i x = Γ (slice F x i) (x i) :=
      ⟨fun i x => Γ (slice F x i) (x i), fun _ _ => rfl⟩
    have hHm : ∀ i, Measurable (H i) := fun i => by
      have h : H i = fun x => Γ (slice F x i) (x i) := funext (hH i)
      rw [h]
      exact hΓm i
    have hHb : ∀ i x, |H i x| ≤ K := fun i x => by
      rw [hH]
      exact hK x i
    -- the squared function on the product
    obtain ⟨G, hG⟩ : ∃ G : α × (Fin n → α) → ℝ,
        ∀ a y, G (a, y) = F (Fin.cons a y : Fin (n + 1) → α) ^ 2 :=
      ⟨fun z => F (Fin.cons z.1 z.2 : Fin (n + 1) → α) ^ 2, fun _ _ => rfl⟩
    have hGfun : G = fun z => F (Fin.cons z.1 z.2 : Fin (n + 1) → α) ^ 2 := by
      funext z
      exact hG z.1 z.2
    have hGm : Measurable G := by
      rw [hGfun]
      exact (hFm.comp (measurable_cons n)).pow_const 2
    have hGc : ∀ z, c ^ 2 ≤ G z := fun z => by
      rw [hGfun]
      exact pow_le_pow_left₀ hc.le (hFc _) 2
    have hGB : ∀ z, G z ≤ B ^ 2 := fun z => by
      rw [hGfun]
      exact pow_le_pow_left₀ (lt_of_lt_of_le hc (hFc _)).le (hFB _) 2
    have hc2 : (0 : ℝ) < c ^ 2 := by positivity
    have hprod := SharpLSI.entR_prod_le (μ := μ) (ν := piMeas μ n) hGm hc2 hGc hGB
    have hLHS : SharpLSI.entR (piMeas μ (n + 1)) (fun x => F x ^ 2) =
        SharpLSI.entR (μ.prod (piMeas μ n)) G := by
      rw [entR_succ_eq μ n, hGfun]
    -- induction hypothesis on the slices `y ↦ F (cons a y)`
    have hIH : ∀ a : α, SharpLSI.entR (piMeas μ n) (fun y => F (Fin.cons a y : Fin (n + 1) → α) ^ 2) ≤
        C * ∑ i : Fin n, ∫ y, H i.succ (Fin.cons a y : Fin (n + 1) → α) ∂(piMeas μ n) := by
      intro a
      have h := ih (fun y => F (Fin.cons a y : Fin (n + 1) → α))
        (hFm.comp (measurable_cons_left n a)) (fun y => hFc _) (fun y => hFB _)
        (fun y i => by rw [slice_cons_tail F a y i]; exact hA _ _)
        (fun i => by
          have h1 := (hΓm i.succ).comp (measurable_cons_left n a)
          simpa only [Function.comp_def, slice_cons_tail, Fin.cons_succ] using h1)
        ⟨K, fun y i => by simpa only [slice_cons_tail, Fin.cons_succ] using hK (Fin.cons a y) i.succ⟩
      simpa only [hH, slice_cons_tail, Fin.cons_succ] using h
    -- one-particle inequality on the slices `a ↦ F (cons a y)`
    have hLSI' : ∀ y : Fin n → α,
        SharpLSI.entR μ (fun a => F (Fin.cons a y : Fin (n + 1) → α) ^ 2) ≤
          C * ∫ a, H 0 (Fin.cons a y : Fin (n + 1) → α) ∂μ := by
      intro y
      have hAy : A (fun a => F (Fin.cons a y : Fin (n + 1) → α)) := by
        have h := hA (Fin.cons a₀ y : Fin (n + 1) → α) 0
        rwa [slice_cons_zero] at h
      have hf := hLSI (fun a => F (Fin.cons a y : Fin (n + 1) → α)) hAy
        (hFm.comp (measurable_cons_right n y)) ⟨c, hc, fun a => hFc _⟩ ⟨B, fun a => hFB _⟩
      have e : ∫ a, Γ (fun a => F (Fin.cons a y : Fin (n + 1) → α)) a ∂μ =
          ∫ a, H 0 (Fin.cons a y : Fin (n + 1) → α) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
        beta_reduce
        rw [hH, slice_cons_zero, Fin.cons_zero]
      rw [e] at hf
      exact hf
    have hint1 : ∀ i : Fin n,
        Integrable (fun a => ∫ y, H i.succ (Fin.cons a y : Fin (n + 1) → α) ∂(piMeas μ n)) μ :=
      fun i => integrable_integral_cons_left μ (hHm i.succ) (hHb i.succ)
    have hint0 : Integrable (fun y => ∫ a, H 0 (Fin.cons a y : Fin (n + 1) → α) ∂μ)
        (piMeas μ n) :=
      integrable_integral_cons_right μ (hHm 0) (hHb 0)
    have hT1 : ∫ a, SharpLSI.entR (piMeas μ n) (fun b => G (a, b)) ∂μ ≤
        ∫ a, C * ∑ i : Fin n, ∫ y, H i.succ (Fin.cons a y : Fin (n + 1) → α) ∂(piMeas μ n) ∂μ := by
      refine integral_mono
        (SharpLSI.integrable_entR_left (μ := μ) (ν := piMeas μ n) hGm hc2 hGc hGB)
        ((integrable_finsetSum Finset.univ (fun i _ => hint1 i)).const_mul C) (fun a => ?_)
      simp only [hG]
      exact hIH a
    have hT2 : ∫ y, SharpLSI.entR μ (fun a => G (a, y)) ∂(piMeas μ n) ≤
        ∫ y, C * ∫ a, H 0 (Fin.cons a y : Fin (n + 1) → α) ∂μ ∂(piMeas μ n) := by
      refine integral_mono
        (SharpLSI.integrable_entR_right (μ := μ) (ν := piMeas μ n) hGm hc2 hGc hGB)
        (hint0.const_mul C) (fun y => ?_)
      simp only [hG]
      exact hLSI' y
    have hT1' : ∫ a, C * ∑ i : Fin n, ∫ y, H i.succ (Fin.cons a y : Fin (n + 1) → α)
          ∂(piMeas μ n) ∂μ =
        C * ∑ i : Fin n, ∫ x, H i.succ x ∂(piMeas μ (n + 1)) := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hint1 i)]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact (integral_pi_succ_left μ n (hHm i.succ) (hHb i.succ)).symm
    have hT2' : ∫ y, C * ∫ a, H 0 (Fin.cons a y : Fin (n + 1) → α) ∂μ ∂(piMeas μ n) =
        C * ∫ x, H 0 x ∂(piMeas μ (n + 1)) := by
      rw [integral_const_mul]
      congr 1
      exact (integral_pi_succ_right μ n (hHm 0) (hHb 0)).symm
    have hsum : ∑ i : Fin (n + 1), ∫ x, Γ (slice F x i) (x i) ∂(piMeas μ (n + 1)) =
        ∑ i : Fin (n + 1), ∫ x, H i x ∂(piMeas μ (n + 1)) := by
      simp only [hH]
    rw [hsum, Fin.sum_univ_succ, mul_add, hLHS]
    linarith

end Prob

end Aux

/-- **Tensorization of a one-particle log-Sobolev inequality for the entropy of squares.**

If `Ent_μ(f²) ≤ C ∫ Γ f dμ` for admissible (`A`), measurable, bounded `f` bounded away from `0`,
then for a measurable `F : (Fin N → α) → ℝ` with `0 < c ≤ F ≤ B`, all of whose slices are
admissible and whose product-level carré du champ terms are measurable and uniformly bounded,
`Ent_{μ^{⊗N}}(F²) ≤ C ∑ᵢ ∫ Γ (slice F x i) (x i) dμ^{⊗N}(x)`. -/
theorem entR_pi_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : (α → ℝ) → Prop) (Γ : (α → ℝ) → α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hLSI : ∀ f : α → ℝ, A f → Measurable f → (∃ c, 0 < c ∧ ∀ y, c ≤ f y) → (∃ B, ∀ y, f y ≤ B) →
      SharpLSI.entR μ (fun y => f y ^ 2) ≤ C * ∫ y, Γ f y ∂μ)
    (N : ℕ) (F : (Fin N → α) → ℝ) (hFm : Measurable F) {c B : ℝ} (hc : 0 < c)
    (hFc : ∀ x, c ≤ F x) (hFB : ∀ x, F x ≤ B)
    (hA : ∀ x i, A (slice F x i))
    (hΓm : ∀ i, Measurable fun x => Γ (slice F x i) (x i))
    (hΓb : ∃ K, ∀ x i, |Γ (slice F x i) (x i)| ≤ K) :
    SharpLSI.entR (Measure.pi fun _ : Fin N => μ) (fun x => F x ^ 2)
      ≤ C * ∑ i, ∫ x, Γ (slice F x i) (x i) ∂(Measure.pi fun _ : Fin N => μ) := by
  have _hC := hC
  exact entR_pi_le_aux μ A Γ C hLSI hc N F hFm hFc hFB hA hΓm hΓb

end SharpLSI.FL.Tensor
