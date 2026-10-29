import SharpSymmetricLSI.Paper.CondEmpirical

/-!
# Lemma 5.4, tools (Phase 3, lane D; R21)

Disintegration identities over the past, the conditional Pinsker comparison with
past-dependent bounded tests, absolute continuity of the conditional laws, and product
integrals over `Fin 2`, `Fin 3`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

theorem integrable_of_bdd {α : Type*} [MeasurableSpace α] {P : Measure α} [IsFiniteMeasure P]
    {f : α → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

theorem abs_integral_le_of_bdd {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] {f : α → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) : |∫ x, f x ∂P| ≤ C := by
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |f x| ∂P ≤ ∫ _, C ∂P := integral_mono_of_nonneg
        (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const C) (Eventually.of_forall hC)
    _ = C := by simp

theorem law_pastNext (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j : ℕ} (hj : j < N) :
    ν.map (fun X => (past j hj.le X, X ⟨j, hj⟩)) = (ν.map (past j hj.le)) ⊗ₘ condNext ν j hj :=
  (compProd_map_condDistrib (measurable_past _).aemeasurable
    (measurable_pi_apply _).aemeasurable).symm

/-- `E F(past, X_j) = E_P ∫ F(p,x) dρ_j(p)(x)`. -/
theorem integral_pastNext (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j : ℕ}
    (hj : j < N) {F : (Fin j → Torus d) → Torus d → ℝ} (hF : Measurable (Function.uncurry F))
    {C : ℝ} (hC : ∀ p x, |F p x| ≤ C) :
    ∫ X, F (past j hj.le X) (X ⟨j, hj⟩) ∂ν =
      ∫ p, ∫ x, F p x ∂condNext ν j hj p ∂(ν.map (past j hj.le)) := by
  haveI : IsProbabilityMeasure (ν.map (past j hj.le)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
  have hi : Integrable (Function.uncurry F) ((ν.map (past j hj.le)) ⊗ₘ condNext ν j hj) :=
    integrable_of_bdd hF fun q => hC q.1 q.2
  calc ∫ X, F (past j hj.le X) (X ⟨j, hj⟩) ∂ν
      = ∫ q, Function.uncurry F q ∂(ν.map (fun X => (past j hj.le X, X ⟨j, hj⟩))) :=
        (integral_map ((measurable_past _).prodMk (measurable_pi_apply _)).aemeasurable
          hF.aestronglyMeasurable).symm
    _ = ∫ q, Function.uncurry F q ∂((ν.map (past j hj.le)) ⊗ₘ condNext ν j hj) := by
        rw [law_pastNext]
    _ = _ := Measure.integral_compProd hi

/-- `E T(past, block) = E_P ∫ T(p,z) dν_{j,k}(p)(z)`. -/
theorem integral_pastBlock (ν : Measure (Config N d)) [IsProbabilityMeasure ν] {j k : ℕ}
    (hj : j < N) (h : j + k ≤ N) {T : (Fin j → Torus d) → (Fin k → Torus d) → ℝ}
    (hT : Measurable (Function.uncurry T)) {C : ℝ} (hC : ∀ p z, |T p z| ≤ C) :
    ∫ X, T (past j hj.le X) (block j k h X) ∂ν =
      ∫ p, ∫ z, T p z ∂condBlock ν j k h p ∂(ν.map (past j hj.le)) := by
  haveI : IsProbabilityMeasure (ν.map (past j hj.le)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
  have hlaw : ν.map (fun X => (past j hj.le X, block j k h X)) =
      (ν.map (past j hj.le)) ⊗ₘ condBlock ν j k h :=
    (compProd_map_condDistrib (measurable_past _).aemeasurable
      (measurable_block h).aemeasurable).symm
  have hi : Integrable (Function.uncurry T) ((ν.map (past j hj.le)) ⊗ₘ condBlock ν j k h) :=
    integrable_of_bdd hT fun q => hC q.1 q.2
  calc ∫ X, T (past j hj.le X) (block j k h X) ∂ν
      = ∫ q, Function.uncurry T q ∂(ν.map (fun X => (past j hj.le X, block j k h X))) :=
        (integral_map ((measurable_past _).prodMk (measurable_block h)).aemeasurable
          hT.aestronglyMeasurable).symm
    _ = ∫ q, Function.uncurry T q ∂((ν.map (past j hj.le)) ⊗ₘ condBlock ν j k h) := by
        rw [hlaw]
    _ = _ := Measure.integral_compProd hi

/-- **Conditional Pinsker with a past-dependent test.** -/
theorem pastTest_sub_block (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν] (hsym : IsSymmetricMeasure ν)
    (hH : klDiv ν (Measure.pi fun _ : Fin N => μ) ≠ ⊤) {j k : ℕ} (hj : j < N) (h : j + k ≤ N)
    {T : (Fin j → Torus d) → (Fin k → Torus d) → ℝ} (hT : Measurable (Function.uncurry T))
    {C : ℝ} (hC : ∀ p z, |T p z| ≤ C) :
    |∫ p, ∫ z, T p z ∂(Measure.pi fun _ : Fin k => condNext ν j hj p) ∂(ν.map (past j hj.le)) -
      ∫ X, T (past j hj.le X) (block j k h X) ∂ν| ≤
      C * Real.sqrt (2 * (DCond ν j k hj h).toReal) := by
  set P := ν.map (past j hj.le) with hPdef
  haveI hP : IsProbabilityMeasure P :=
    (Measure.isProbabilityMeasure_map_iff (measurable_past _).aemeasurable).mpr inferInstance
  obtain ⟨hDm, hDlt, hDeq⟩ := DCond_data μ ν hsym hH hj h
  set F : (Fin j → Torus d) → ℝ := fun p =>
    ∫ z, T p z ∂(Measure.pi fun _ : Fin k => condNext ν j hj p) with hFdef
  set G : (Fin j → Torus d) → ℝ := fun p => ∫ z, T p z ∂(condBlock ν j k h p) with hGdef
  have hFm : Measurable F := by
    have := hT.stronglyMeasurable.integral_kernel_prod_right' (κ := piK (condNext ν j hj) k)
    have e : F = fun p => ∫ z, Function.uncurry T (p, z) ∂(piK (condNext ν j hj) k p) := by
      funext p; rw [piK_apply]; rfl
    rw [e]; exact this.measurable
  have hGm : Measurable G :=
    (hT.stronglyMeasurable.integral_kernel_prod_right' (κ := condBlock ν j k h)).measurable
  obtain ⟨p0⟩ : Nonempty (Fin j → Torus d) := inferInstance
  obtain ⟨z0⟩ : Nonempty (Fin k → Torus d) := inferInstance
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p0 z0)
  have hFb : ∀ p, |F p| ≤ C := fun p => abs_integral_le_of_bdd (hC p)
  have hGb : ∀ p, |G p| ≤ C := fun p => abs_integral_le_of_bdd (hC p)
  rw [integral_pastBlock ν hj h hT hC, ← integral_sub (integrable_of_bdd hFm hFb)
    (integrable_of_bdd hGm hGb)]
  refine (abs_integral_le_integral_abs).trans ?_
  set D : (Fin j → Torus d) → ℝ := fun p => (klDiv (condBlock ν j k h p)
    (Measure.pi fun _ : Fin k => condNext ν j hj p)).toReal with hD
  have hpt : ∀ᵐ p ∂P, |F p - G p| ≤ C * Real.sqrt (2 * D p) := by
    filter_upwards [hDlt] with p hp
    rw [abs_sub_comm]
    exact abs_integral_sub_le_pinsker (hT.comp measurable_prodMk_left) (hC p) hp.ne
  have hDi : Integrable D P := integrable_toReal_of_lintegral_ne_top hDm (by
    rw [← hDeq]; exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr fun a _ =>
      hCondT_ne_top μ ν hH (j + a)) (by
        rw [DCond_add μ ν hsym hH hj h]; exact le_self_add))
  have hDint : ∫ p, D p ∂P = (DCond ν j k hj h).toReal := by
    rw [hDeq, integral_toReal hDm hDlt]
  have hD0 : ∀ᵐ p ∂P, 0 ≤ 2 * D p := Eventually.of_forall fun p => by
    simp only [hD]; positivity
  calc ∫ p, |F p - G p| ∂P ≤ ∫ p, C * Real.sqrt (2 * D p) ∂P :=
        integral_mono_ae ((integrable_of_bdd hFm hFb).sub (integrable_of_bdd hGm hGb)).abs
          ((integrable_sqrt_of hD0 (hDi.const_mul 2)).const_mul C) hpt
    _ = C * ∫ p, Real.sqrt (2 * D p) ∂P := integral_const_mul _ _
    _ ≤ C * Real.sqrt (∫ p, 2 * D p ∂P) :=
        mul_le_mul_of_nonneg_left (integral_sqrt_le hD0 (hDi.const_mul 2)) hC0
    _ = C * Real.sqrt (2 * (DCond ν j k hj h).toReal) := by rw [integral_const_mul, hDint]

/-- The conditional laws are absolutely continuous with respect to `μ`, `P`-a.e. -/
theorem condNext_ac (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (ν : Measure (Config N d)) [IsProbabilityMeasure ν]
    (hac : ν ≪ Measure.pi fun _ : Fin N => μ) {j : ℕ} (hj : j < N) :
    ∀ᵐ p ∂(ν.map (past j hj.le)), condNext ν j hj p ≪ μ := by
  have hf : Measurable fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩) :=
    (measurable_past _).prodMk (measurable_pi_apply _)
  have hpi : (Measure.pi fun _ : Fin N => μ).map (fun X => (past j hj.le X, X ⟨j, hj⟩)) =
      (Measure.pi fun _ : Fin j => μ).prod μ := by
    have e : (fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩)) =
        initLast d j ∘ past (j + 1) hj := funext fun X => (initLast_past hj X).symm
    rw [e, ← Measure.map_map (initLast d j).measurable (measurable_past _), map_past_pi,
      map_initLast_pi]
  have h1 : (ν.map (past j hj.le)) ⊗ₘ condNext ν j hj ≪
      (Measure.pi fun _ : Fin j => μ) ⊗ₘ Kernel.const _ μ := by
    rw [Measure.compProd_const, ← hpi, ← law_pastNext]
    exact hac.map hf
  exact (Measure.absolutelyContinuous_compProd_iff'.mp h1).2

/-- `∫ f(z₀,z₁) dρ^{⊗2} = ∫∫ f dρ dρ`. -/
theorem integral_pi_two {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ] {f : Torus d → Torus d → ℝ}
    (hf : Measurable (Function.uncurry f)) {C : ℝ} (hC : ∀ x y, |f x y| ≤ C) :
    ∫ z, f (z 0) (z 1) ∂(Measure.pi fun _ : Fin 2 => ρ) = ∫ x, ∫ y, f x y ∂ρ ∂ρ := by
  calc ∫ z, f (z 0) (z 1) ∂(Measure.pi fun _ : Fin 2 => ρ)
      = ∫ z, Function.uncurry f (MeasurableEquiv.finTwoArrow z) ∂(Measure.pi fun _ : Fin 2 => ρ) :=
        rfl
    _ = ∫ q, Function.uncurry f q ∂(ρ.prod ρ) := (measurePreserving_finTwoArrow ρ).integral_comp' _
    _ = _ := integral_prod _ (integrable_of_bdd hf fun q => hC q.1 q.2)

/-- `∫ f(z₀,z₁,z₂) dρ^{⊗3} = ∫∫∫ f dρ dρ dρ`. -/
theorem integral_pi_three {ρ : Measure (Torus d)} [IsProbabilityMeasure ρ]
    {f : Torus d → Torus d → Torus d → ℝ}
    (hf : Measurable fun q : Torus d × Torus d × Torus d => f q.1 q.2.1 q.2.2) {C : ℝ}
    (hC : ∀ x y w, |f x y w| ≤ C) :
    ∫ z, f (z 0) (z 1) (z 2) ∂(Measure.pi fun _ : Fin 3 => ρ) =
      ∫ x, ∫ y, ∫ w, f x y w ∂ρ ∂ρ ∂ρ := by
  have hmp : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Torus d) 0)
      (Measure.pi fun _ : Fin 3 => ρ) (ρ.prod (Measure.pi fun _ : Fin 2 => ρ)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin 3 => ρ) 0
  have hm2 : Measurable fun q : Torus d × (Fin 2 → Torus d) => f q.1 (q.2 0) (q.2 1) := by
    have hp : Measurable fun q : Torus d × (Fin 2 → Torus d) => (q.1, q.2 0, q.2 1) := by fun_prop
    exact hf.comp hp
  calc ∫ z, f (z 0) (z 1) (z 2) ∂(Measure.pi fun _ : Fin 3 => ρ)
      = ∫ z, (fun q : Torus d × (Fin 2 → Torus d) => f q.1 (q.2 0) (q.2 1))
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => Torus d) 0 z)
          ∂(Measure.pi fun _ : Fin 3 => ρ) := rfl
    _ = ∫ q, f q.1 (q.2 0) (q.2 1) ∂(ρ.prod (Measure.pi fun _ : Fin 2 => ρ)) :=
        hmp.integral_comp' (fun q : Torus d × (Fin 2 → Torus d) => f q.1 (q.2 0) (q.2 1))
    _ = ∫ x, ∫ z, f x (z 0) (z 1) ∂(Measure.pi fun _ : Fin 2 => ρ) ∂ρ :=
        integral_prod _ (integrable_of_bdd hm2 fun q => hC _ _ _)
    _ = _ := integral_congr_ae (Eventually.of_forall fun x =>
        integral_pi_two (f := f x) (hf.comp (measurable_const.prodMk measurable_id)) (hC x))

end SharpLSI
