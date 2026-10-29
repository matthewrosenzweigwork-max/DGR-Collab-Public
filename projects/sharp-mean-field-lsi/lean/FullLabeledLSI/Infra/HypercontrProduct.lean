import Mathlib

/-!
# Resampling one coordinate of a product measure; per-coordinate eigenfunction integration by parts

Let `μ` be a probability measure on `α` and `Q = Measure.pi (fun _ : Fin N => μ)`.

* `measurePreserving_update`: `(x, y) ↦ Function.update x l y` carries `Q.prod μ` to `Q`
  ("resampling coordinate `l` with an independent copy preserves the product law").
* `integral_update_resample`: the corresponding integral identity (Fubini).
* `eigen_ibp_label`: abstract per-coordinate integration by parts.  If `e l` is an eigenfunction
  for the (abstract) carré du champ `Γ` on admissible functions, i.e.
  `∫ Γ φ (e l) dμ = lam l * ∫ e l * φ dμ`, then for `F` all of whose coordinate slices are
  admissible,
  `lam l * ∫ F * ∏ e m (x m) dQ = ∫ Γ (F(x[l := ·])) (e l) (x l) * ∏_{m ≠ l} e m (x m) dQ`.
* `eigen_ibp`: the sum over all coordinates `l`.
-/

open MeasureTheory

namespace SharpLSI.FL.Product

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-! ### Resampling one coordinate -/

/-- Resampling coordinate `l` of a sample from the product law with an independent copy
preserves the product law. -/
theorem measurePreserving_update {N : ℕ} (l : Fin N) :
    MeasurePreserving (fun p : (Fin N → α) × α => Function.update p.1 l p.2)
      ((Measure.pi fun _ : Fin N => μ).prod μ) (Measure.pi fun _ : Fin N => μ) := by
  cases N with
  | zero => exact l.elim0
  | succ n =>
    have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) l)
        (Measure.pi fun _ : Fin (n + 1) => μ) (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) l
    have h1 : MeasurePreserving
        (Prod.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) l) (id : α → α))
        ((Measure.pi fun _ : Fin (n + 1) => μ).prod μ)
        ((μ.prod (Measure.pi fun _ : Fin n => μ)).prod μ) :=
      hmp.prod (MeasurePreserving.id μ)
    have h2 : MeasurePreserving
        (Prod.swap : (α × (Fin n → α)) × α → α × (α × (Fin n → α)))
        ((μ.prod (Measure.pi fun _ : Fin n => μ)).prod μ)
        (μ.prod (μ.prod (Measure.pi fun _ : Fin n => μ))) :=
      Measure.measurePreserving_swap
    have h3 : MeasurePreserving
        (Prod.map (id : α → α) (Prod.snd : α × (Fin n → α) → (Fin n → α)))
        (μ.prod (μ.prod (Measure.pi fun _ : Fin n => μ)))
        (μ.prod (Measure.pi fun _ : Fin n => μ)) :=
      (MeasurePreserving.id μ).prod measurePreserving_snd
    have h4 := hmp.symm
    have h5 := h4.comp (h3.comp (h2.comp h1))
    have hfun : (fun p : (Fin (n + 1) → α) × α => Function.update p.1 l p.2) =
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) l).symm ∘
          (Prod.map (id : α → α) (Prod.snd : α × (Fin n → α) → (Fin n → α))) ∘ Prod.swap ∘
          (Prod.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) l)
            (id : α → α)) := by
      funext p
      exact (Fin.insertNth_removeNth l p.2 p.1).symm
    rw [hfun]
    exact h5

/-- Integral identity for resampling coordinate `l` (Fubini). -/
theorem integral_update_resample {N : ℕ} (l : Fin N) {H : (Fin N → α) → ℝ}
    (hH : Integrable H (Measure.pi fun _ : Fin N => μ)) :
    ∫ x, H x ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ x, ∫ y, H (Function.update x l y) ∂μ ∂(Measure.pi fun _ : Fin N => μ) := by
  have hp := measurePreserving_update (μ := μ) l
  have hint : Integrable (fun p : (Fin N → α) × α => H (Function.update p.1 l p.2))
      ((Measure.pi fun _ : Fin N => μ).prod μ) := hp.integrable_comp_of_integrable hH
  have hH' : AEStronglyMeasurable H
      (Measure.map (fun p : (Fin N → α) × α => Function.update p.1 l p.2)
        ((Measure.pi fun _ : Fin N => μ).prod μ)) := by
    rw [hp.map_eq]
    exact hH.aestronglyMeasurable
  have h1 := integral_map (f := H) hp.measurable.aemeasurable hH'
  rw [hp.map_eq] at h1
  rw [h1]
  exact integral_prod _ hint

/-! ### Helpers -/

lemma measurable_prod_coord {N : ℕ} (e : Fin N → α → ℝ) (he : ∀ m, Measurable (e m))
    (s : Finset (Fin N)) :
    Measurable (fun x : Fin N → α => ∏ m ∈ s, e m (x m)) :=
  Finset.measurable_prod _ (fun m _ => (he m).comp (measurable_pi_apply m))

omit [MeasurableSpace α] in
lemma abs_prod_coord_le {N : ℕ} (e : Fin N → α → ℝ) (K : Fin N → ℝ)
    (hK : ∀ m y, |e m y| ≤ K m) (s : Finset (Fin N)) (x : Fin N → α) :
    |∏ m ∈ s, e m (x m)| ≤ ∏ m ∈ s, K m := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun m _ => abs_nonneg _) (fun m _ => hK m _)

omit [MeasurableSpace α] in
lemma prod_coord_update {N : ℕ} (e : Fin N → α → ℝ) (x : Fin N → α) (l : Fin N) (y : α)
    (s : Finset (Fin N)) (hl : l ∉ s) :
    ∏ m ∈ s, e m (Function.update x l y m) = ∏ m ∈ s, e m (x m) := by
  refine Finset.prod_congr rfl (fun m hm => ?_)
  have hne : m ≠ l := fun h => hl (h ▸ hm)
  rw [Function.update_of_ne hne]

/-! ### Per-coordinate integration by parts -/

/-- Per-coordinate eigenfunction integration by parts for the i.i.d. product law. -/
theorem eigen_ibp_label {N : ℕ} (A : (α → ℝ) → Prop) (Γ : (α → ℝ) → (α → ℝ) → α → ℝ)
    (e : Fin N → α → ℝ) (lam : Fin N → ℝ)
    (he_meas : ∀ m, Measurable (e m)) (he_bdd : ∀ m, ∃ K, ∀ y, |e m y| ≤ K)
    (heig : ∀ m (φ : α → ℝ), A φ → ∫ y, Γ φ (e m) y ∂μ = lam m * ∫ y, e m y * φ y ∂μ)
    (F : (Fin N → α) → ℝ) (hFm : Measurable F) (hFb : ∃ K, ∀ x, |F x| ≤ K)
    (hFA : ∀ x l, A (fun y => F (Function.update x l y))) (l : Fin N)
    (hΓm : Measurable fun x => Γ (fun y => F (Function.update x l y)) (e l) (x l))
    (hΓb : ∃ K, ∀ x, |Γ (fun y => F (Function.update x l y)) (e l) (x l)| ≤ K) :
    lam l * ∫ x, F x * ∏ m, e m (x m) ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ x, Γ (fun y => F (Function.update x l y)) (e l) (x l) *
        ∏ m ∈ Finset.univ.erase l, e m (x m) ∂(Measure.pi fun _ : Fin N => μ) := by
  obtain ⟨KF, hKF⟩ := hFb
  obtain ⟨KG, hKG⟩ := hΓb
  choose K hK using he_bdd
  let R : (Fin N → α) → ℝ := fun x => ∏ m ∈ Finset.univ.erase l, e m (x m)
  have hR : ∀ x, R x = ∏ m ∈ Finset.univ.erase l, e m (x m) := fun x => rfl
  have hRm : Measurable R := measurable_prod_coord e he_meas _
  have hRb : ∀ x, |R x| ≤ ∏ m ∈ Finset.univ.erase l, K m := fun x =>
    abs_prod_coord_le e K hK _ x
  have hRupd : ∀ x y, R (Function.update x l y) = R x := fun x y =>
    prod_coord_update e x l y _ (Finset.notMem_erase l _)
  have hMeas : Measurable (fun x : Fin N → α => ∏ m, e m (x m)) :=
    measurable_prod_coord e he_meas Finset.univ
  have hMb : ∀ x : Fin N → α, |∏ m, e m (x m)| ≤ ∏ m, K m := fun x =>
    abs_prod_coord_le e K hK _ x
  have hprod : ∀ x : Fin N → α, ∏ m, e m (x m) = e l (x l) * R x := fun x =>
    (Finset.mul_prod_erase Finset.univ (fun m => e m (x m)) (Finset.mem_univ l)).symm
  have hH1int : Integrable (fun x => F x * ∏ m, e m (x m))
      (Measure.pi fun _ : Fin N => μ) := by
    refine Integrable.of_bound (hFm.mul hMeas).aestronglyMeasurable (KF * ∏ m, K m)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hKF x) (hMb x) (abs_nonneg _) ((abs_nonneg _).trans (hKF x))
  have hH2int : Integrable
      (fun x => Γ (fun y => F (Function.update x l y)) (e l) (x l) * R x)
      (Measure.pi fun _ : Fin N => μ) := by
    refine Integrable.of_bound (hΓm.mul hRm).aestronglyMeasurable
      (KG * ∏ m ∈ Finset.univ.erase l, K m) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hKG x) (hRb x) (abs_nonneg _) ((abs_nonneg _).trans (hKG x))
  -- Step 1: resample coordinate `l` in the left-hand integral.
  have step1 : ∫ x, F x * ∏ m, e m (x m) ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ x, R x * ∫ y, e l y * F (Function.update x l y) ∂μ
        ∂(Measure.pi fun _ : Fin N => μ) := by
    rw [integral_update_resample l hH1int]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show ∫ y, F (Function.update x l y) * ∏ m, e m (Function.update x l y m) ∂μ =
      R x * ∫ y, e l y * F (Function.update x l y) ∂μ
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show F (Function.update x l y) * ∏ m, e m (Function.update x l y m) =
      R x * (e l y * F (Function.update x l y))
    rw [hprod (Function.update x l y), Function.update_self, hRupd]
    ring
  -- Step 2: apply the eigenfunction identity slice by slice.
  have step2 : lam l * ∫ x, R x * ∫ y, e l y * F (Function.update x l y) ∂μ
        ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ x, R x * ∫ y, Γ (fun y => F (Function.update x l y)) (e l) y ∂μ
        ∂(Measure.pi fun _ : Fin N => μ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have h : ∫ y, Γ (fun y => F (Function.update x l y)) (e l) y ∂μ =
        lam l * ∫ y, e l y * F (Function.update x l y) ∂μ := heig l _ (hFA x l)
    show lam l * (R x * ∫ y, e l y * F (Function.update x l y) ∂μ) =
      R x * ∫ y, Γ (fun y => F (Function.update x l y)) (e l) y ∂μ
    rw [h]
    ring
  -- Step 3: resample coordinate `l` backwards on the right-hand side.
  have step3 : ∫ x, Γ (fun y => F (Function.update x l y)) (e l) (x l) * R x
        ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ x, R x * ∫ y, Γ (fun y => F (Function.update x l y)) (e l) y ∂μ
        ∂(Measure.pi fun _ : Fin N => μ) := by
    rw [integral_update_resample l hH2int]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hpt : ∀ y, Γ (fun y' => F (Function.update (Function.update x l y) l y')) (e l)
        (Function.update x l y l) * R (Function.update x l y) =
        Γ (fun y' => F (Function.update x l y')) (e l) y * R x := by
      intro y
      simp only [Function.update_idem, Function.update_self, hRupd]
    show ∫ y, Γ (fun y' => F (Function.update (Function.update x l y) l y')) (e l)
        (Function.update x l y l) * R (Function.update x l y) ∂μ =
      R x * ∫ y, Γ (fun y => F (Function.update x l y)) (e l) y ∂μ
    rw [integral_congr_ae (ae_of_all _ hpt), integral_mul_const, mul_comm]
  calc lam l * ∫ x, F x * ∏ m, e m (x m) ∂(Measure.pi fun _ : Fin N => μ)
      = lam l * ∫ x, R x * ∫ y, e l y * F (Function.update x l y) ∂μ
          ∂(Measure.pi fun _ : Fin N => μ) := by rw [step1]
    _ = ∫ x, R x * ∫ y, Γ (fun y => F (Function.update x l y)) (e l) y ∂μ
          ∂(Measure.pi fun _ : Fin N => μ) := step2
    _ = ∫ x, Γ (fun y => F (Function.update x l y)) (e l) (x l) * R x
          ∂(Measure.pi fun _ : Fin N => μ) := step3.symm

/-- Sum over all coordinates of `eigen_ibp_label`. -/
theorem eigen_ibp {N : ℕ} (A : (α → ℝ) → Prop) (Γ : (α → ℝ) → (α → ℝ) → α → ℝ)
    (e : Fin N → α → ℝ) (lam : Fin N → ℝ)
    (he_meas : ∀ m, Measurable (e m)) (he_bdd : ∀ m, ∃ K, ∀ y, |e m y| ≤ K)
    (heig : ∀ m (φ : α → ℝ), A φ → ∫ y, Γ φ (e m) y ∂μ = lam m * ∫ y, e m y * φ y ∂μ)
    (F : (Fin N → α) → ℝ) (hFm : Measurable F) (hFb : ∃ K, ∀ x, |F x| ≤ K)
    (hFA : ∀ x l, A (fun y => F (Function.update x l y)))
    (hΓm : ∀ l, Measurable fun x => Γ (fun y => F (Function.update x l y)) (e l) (x l))
    (hΓb : ∀ l, ∃ K, ∀ x, |Γ (fun y => F (Function.update x l y)) (e l) (x l)| ≤ K) :
    (∑ l, lam l) * ∫ x, F x * ∏ m, e m (x m) ∂(Measure.pi fun _ : Fin N => μ) =
      ∑ l, ∫ x, Γ (fun y => F (Function.update x l y)) (e l) (x l) *
        ∏ m ∈ Finset.univ.erase l, e m (x m) ∂(Measure.pi fun _ : Fin N => μ) := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ =>
    eigen_ibp_label A Γ e lam he_meas he_bdd heig F hFm hFb hFA l (hΓm l) (hΓb l)

end SharpLSI.FL.Product
