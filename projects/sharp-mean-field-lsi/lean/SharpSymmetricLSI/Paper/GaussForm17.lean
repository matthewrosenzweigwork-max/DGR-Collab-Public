import SharpSymmetricLSI.Infra.Gross1
import SharpSymmetricLSI.Paper.GaussForm6

/-!
# R32 (E2): Gross' inequality on `ℝⁿ` by tensorization

For the standard Gaussian `γ_n = N(0,1)^{⊗n}` on `Fin n → ℝ`, `ψ ∈ C^∞_c` and a constant `a` with
`a + ψ > 0`:  `Ent_{γ_n}((a+ψ)²) ≤ 2 ∫ ∑_k (∂_kψ)² dγ_n` (`grossProp_all`), by induction on `n`,
splitting off the coordinate `0` (`MeasurableEquiv.piFinSuccAbove`), the subadditivity
`entR_prod_le` (which needs `0 < c ≤ (a+ψ)² ≤ C`) and the one-dimensional `gross_1d_shift`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff

namespace SharpLSI

/-- `γ_n = N(0,1)^{⊗n}`. -/
noncomputable abbrev gpi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

/-! ### Helpers -/

theorem hasCompactSupport_comp_of_norm_le {E F : Type*} [NormedAddCommGroup E] [ProperSpace E]
    [NormedAddCommGroup F] {ψ : F → ℝ} (hc : HasCompactSupport ψ) {g : E → F}
    (hg : ∀ e, ‖e‖ ≤ ‖g e‖) : HasCompactSupport fun e => ψ (g e) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E) R) fun e he => ?_
  refine image_eq_zero_of_notMem_tsupport fun hmem => he ?_
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
  exact (hg e).trans h1

/-- Positive lower and finite upper bounds for `a + ψ`, `ψ` continuous with compact support. -/
theorem exists_bounds_shift {E : Type*} [TopologicalSpace E] [Nonempty E] {ψ : E → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) {a : ℝ} (hpos : ∀ x, 0 < a + ψ x) :
    ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ a + ψ x ∧ a + ψ x ≤ C := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hψ
  have hup : ∀ x, a + ψ x ≤ a + B := fun x => by
    have := hB x; rw [Real.norm_eq_abs] at this; linarith [le_abs_self (ψ x)]
  have hf : Continuous fun x => a + ψ x := continuous_const.add hψ
  by_cases h : ∃ x0, x0 ∉ tsupport ψ
  · obtain ⟨x0, hx0⟩ := h
    obtain ⟨m, -, hmin⟩ := (hc.isCompact.insert x0).exists_isMinOn ⟨x0, mem_insert _ _⟩
      hf.continuousOn
    refine ⟨a + ψ m, a + B, hpos m, fun x => ⟨?_, hup x⟩⟩
    by_cases hx : x ∈ tsupport ψ
    · exact hmin (mem_insert_of_mem _ hx)
    · have e1 : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
      have e2 : ψ x0 = 0 := image_eq_zero_of_notMem_tsupport hx0
      have := hmin (mem_insert x0 (tsupport ψ))
      simp only [mem_setOf_eq, e2] at this
      rw [e1]; exact this
  · push_neg at h
    obtain ⟨x1⟩ := ‹Nonempty E›
    obtain ⟨m, -, hmin⟩ := hc.isCompact.exists_isMinOn ⟨x1, h x1⟩ hf.continuousOn
    exact ⟨a + ψ m, a + B, hpos m, fun x => ⟨hmin (h x), hup x⟩⟩

theorem insertNth_zero_add_single {n : ℕ} (t : ℝ) (y : Fin n → ℝ) (k : Fin n) (s : ℝ) :
    (Fin.insertNth 0 t (y + s • Pi.single k 1) : Fin (n + 1) → ℝ) =
      Fin.insertNth 0 t y + s • Pi.single k.succ 1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.insertNth_zero', Fin.cons_succ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = k
    · subst hj; simp
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne (fun h => hj (Fin.succ_injective _ h))]

theorem contDiff_insertNth_zero {n : ℕ} (t : ℝ) :
    ContDiff ℝ ∞ (fun y : Fin n → ℝ => (Fin.insertNth 0 t y : Fin (n + 1) → ℝ)) := by
  refine contDiff_pi.2 fun i => Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.insertNth_apply_same]; exact contDiff_const
  · simp only [Fin.insertNth_zero', Fin.cons_succ]; exact contDiff_apply ℝ ℝ j

theorem continuous_insertNth_zero {n : ℕ} :
    Continuous fun p : ℝ × (Fin n → ℝ) => (Fin.insertNth 0 p.1 p.2 : Fin (n + 1) → ℝ) := by
  refine continuous_pi fun j => Fin.cases ?_ (fun i => ?_) j
  · simpa using continuous_fst
  · simp only [Fin.insertNth_zero', Fin.cons_succ]
    exact (continuous_apply i).comp continuous_snd

theorem norm_le_norm_insertNth_right {n : ℕ} (t : ℝ) (y : Fin n → ℝ) :
    ‖y‖ ≤ ‖(Fin.insertNth 0 t y : Fin (n + 1) → ℝ)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have := norm_le_pi_norm (Fin.insertNth 0 t y : Fin (n + 1) → ℝ) j.succ
  simpa [Fin.insertNth_zero'] using this

theorem norm_le_norm_insertNth_left {n : ℕ} (t : ℝ) (y : Fin n → ℝ) :
    ‖t‖ ≤ ‖(Fin.insertNth 0 t y : Fin (n + 1) → ℝ)‖ := by
  have := norm_le_pi_norm (Fin.insertNth 0 t y : Fin (n + 1) → ℝ) 0
  simpa using this

/-- Partial derivatives of the fibre `y ↦ ψ(t, y)`. -/
theorem fderiv_fiber_right {n : ℕ} {ψ : (Fin (n + 1) → ℝ) → ℝ} (hψ : Differentiable ℝ ψ)
    (t : ℝ) (y : Fin n → ℝ) (k : Fin n) :
    fderiv ℝ (fun y => ψ (Fin.insertNth 0 t y)) y (Pi.single k 1) =
      fderiv ℝ ψ (Fin.insertNth 0 t y) (Pi.single k.succ 1) := by
  have hd : Differentiable ℝ (fun y : Fin n → ℝ => ψ (Fin.insertNth 0 t y)) :=
    hψ.comp ((contDiff_insertNth_zero t).differentiable (by simp))
  have hline : ∀ (z : Fin n → ℝ) (v : Fin n → ℝ), HasDerivAt (fun s : ℝ => z + s • v) v 0 :=
    fun z v => by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h1 := (hd (y + (0 : ℝ) • Pi.single k 1)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hline y (Pi.single k 1))
  have hline' : HasDerivAt (fun s : ℝ => (Fin.insertNth 0 t y : Fin (n + 1) → ℝ) +
      s • Pi.single k.succ 1) (Pi.single k.succ 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
      (Pi.single k.succ (1 : ℝ) : Fin (n + 1) → ℝ)).const_add (Fin.insertNth 0 t y)
  have h2 := (hψ (Fin.insertNth 0 t y + (0 : ℝ) • Pi.single k.succ 1)).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hline'
  simp only [zero_smul, add_zero] at h1 h2
  have e : ((fun y => ψ (Fin.insertNth 0 t y)) ∘ fun s : ℝ => y + s • Pi.single k 1) =
      ψ ∘ fun s : ℝ => (Fin.insertNth 0 t y : Fin (n + 1) → ℝ) + s • Pi.single k.succ 1 := by
    funext s; simp only [Function.comp_apply, insertNth_zero_add_single]
  rw [e] at h1
  exact h1.unique h2

/-- The derivative of the fibre `t ↦ ψ(t, y)`. -/
theorem deriv_fiber_left {n : ℕ} {ψ : (Fin (n + 1) → ℝ) → ℝ} (hψ : Differentiable ℝ ψ)
    (t : ℝ) (y : Fin n → ℝ) :
    deriv (fun t => ψ (Fin.insertNth 0 t y)) t = fderiv ℝ ψ (Fin.insertNth 0 t y) (Pi.single 0 1) :=
  ((hψ _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth 0 y t)).deriv

theorem abs_fderiv_single_le {n : ℕ} {ψ : (Fin n → ℝ) → ℝ} {B : ℝ}
    (hB : ∀ x, ‖fderiv ℝ ψ x‖ ≤ B) (x : Fin n → ℝ) (k : Fin n) :
    |fderiv ℝ ψ x (Pi.single k 1)| ≤ B := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  have : ‖(Pi.single k 1 : Fin n → ℝ)‖ = 1 := by simp [Pi.norm_single]
  rw [this, mul_one]; exact hB x

/-! ### The tensorization -/

/-- Gross' inequality on `Fin n → ℝ` for positive functions `a + ψ`, `ψ ∈ C^∞_c`. -/
def GrossProp (n : ℕ) : Prop :=
  ∀ (a : ℝ) (ψ : (Fin n → ℝ) → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ x, 0 < a + ψ x) →
    entR (gpi n) (fun x => (a + ψ x) ^ 2) ≤
      2 * ∫ x, ∑ k, fderiv ℝ ψ x (Pi.single k 1) ^ 2 ∂gpi n

theorem grossProp_zero : GrossProp 0 := by
  intro a ψ _ _ _
  unfold entR
  simp only [Finset.univ_eq_empty, Finset.sum_empty, integral_zero, mul_zero]
  rw [integral_unique, integral_unique]
  simp

theorem grossProp_succ {n : ℕ} (IH : GrossProp n) : GrossProp (n + 1) := by
  intro a ψ hψ hc hpos
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  set P := gpi (n + 1)
  set Q := gpi n
  set μ2 : Measure (ℝ × (Fin n → ℝ)) := (gaussianReal 0 1).prod Q with hμ2
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp : MeasurePreserving e P μ2 :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0
  have htrans : ∀ H : (Fin (n + 1) → ℝ) → ℝ,
      ∫ y, H y ∂P = ∫ p, H (Fin.insertNth 0 p.1 p.2) ∂μ2 := fun H => by
    rw [← hmp.integral_comp' (g := fun p => H (Fin.insertNth 0 p.1 p.2))]
    congr 1; funext y
    exact congrArg H ((Fin.insertNthEquiv (fun _ => ℝ) 0).apply_symm_apply y).symm
  obtain ⟨c, C, hc0, hcC⟩ := exists_bounds_shift hψ.continuous hc hpos
  set F : ℝ × (Fin n → ℝ) → ℝ := fun p => (a + ψ (Fin.insertNth 0 p.1 p.2)) ^ 2 with hFdef
  have hFcont : Continuous F :=
    (continuous_const.add (hψ.continuous.comp continuous_insertNth_zero)).pow 2
  have hFm : Measurable F := hFcont.measurable
  have hFc : ∀ p, c ^ 2 ≤ F p := fun p =>
    pow_le_pow_left₀ hc0.le (hcC _).1 2
  have hFC : ∀ p, F p ≤ C ^ 2 := fun p =>
    pow_le_pow_left₀ (hc0.le.trans (hcC _).1) (hcC _).2 2
  have hent : entR P (fun x => (a + ψ x) ^ 2) = entR μ2 F := by
    unfold entR
    rw [htrans, htrans (fun x => (a + ψ x) ^ 2)]
  have hP := entR_prod_le (μ := gaussianReal 0 1) (ν := Q) hFm (pow_pos hc0 2) hFc hFC
  -- gradient pieces
  obtain ⟨B, -, hBd, hcd, -⟩ := exists_bounds_of_cc hψ hc
  have hD : ∀ k, Continuous fun x => fderiv ℝ ψ x (Pi.single k 1) := fun k =>
    hcd.clm_apply continuous_const
  set gp : ℝ × (Fin n → ℝ) → ℝ :=
    fun p => fderiv ℝ ψ (Fin.insertNth 0 p.1 p.2) (Pi.single 0 1) ^ 2 with hgp
  set gq : ℝ × (Fin n → ℝ) → ℝ :=
    fun p => ∑ j : Fin n, fderiv ℝ ψ (Fin.insertNth 0 p.1 p.2) (Pi.single j.succ 1) ^ 2 with hgq
  have hsqB : ∀ x k, fderiv ℝ ψ x (Pi.single k 1) ^ 2 ≤ B ^ 2 := fun x k => by
    have h := pow_le_pow_left₀ (abs_nonneg _) (abs_fderiv_single_le hBd x k) 2
    rwa [sq_abs] at h
  have hgpi : Integrable gp μ2 := Integrable.of_bound
    (((hD 0).comp continuous_insertNth_zero).pow 2).aestronglyMeasurable (B ^ 2)
    (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsqB _ _)
  have hgqi : Integrable gq μ2 := by
    simp only [hgq]
    refine integrable_finsetSum _ fun j _ => Integrable.of_bound
      (((hD j.succ).comp continuous_insertNth_zero).pow 2).aestronglyMeasurable (B ^ 2)
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsqB _ _
  -- fibre inequalities
  have h1 : ∀ t, entR Q (fun y => F (t, y)) ≤ 2 * ∫ y, gq (t, y) ∂Q := by
    intro t
    have := IH a (fun y => ψ (Fin.insertNth 0 t y)) (hψ.comp (contDiff_insertNth_zero t))
      (hasCompactSupport_comp_of_norm_le hc (norm_le_norm_insertNth_right t))
      (fun y => hpos _)
    simp only [fderiv_fiber_right hψd] at this
    exact this
  have h2 : ∀ y, entR (gaussianReal 0 1) (fun t => F (t, y)) ≤
      2 * ∫ t, gp (t, y) ∂gaussianReal 0 1 := by
    intro y
    have hci : ContDiff ℝ ∞ (fun t : ℝ => (Fin.insertNth 0 t y : Fin (n + 1) → ℝ)) := by
      have : (fun t : ℝ => (Fin.insertNth 0 t y : Fin (n + 1) → ℝ)) =
          fun t => Fin.insertNth 0 0 y + t • Pi.single 0 1 :=
        funext fun t => insertNth_eq_add 0 t y
      rw [this]; exact contDiff_const.add (contDiff_id.smul contDiff_const)
    have := gross_1d_shift (ψ := fun t => ψ (Fin.insertNth 0 t y)) (hψ.comp hci)
      (hasCompactSupport_comp_of_norm_le hc (fun t => norm_le_norm_insertNth_left t y)) a
    simp only [deriv_fiber_left hψd] at this
    exact this
  have hI1 : ∫ t, entR Q (fun y => F (t, y)) ∂gaussianReal 0 1 ≤ 2 * ∫ p, gq p ∂μ2 := by
    rw [integral_prod gq hgqi, ← integral_const_mul]
    exact integral_mono (integrable_entR_left hFm (pow_pos hc0 2) hFc hFC)
      (hgqi.integral_prod_left.const_mul _) h1
  have hI2 : ∫ y, entR (gaussianReal 0 1) (fun t => F (t, y)) ∂Q ≤ 2 * ∫ p, gp p ∂μ2 := by
    rw [integral_prod_symm gp hgpi, ← integral_const_mul]
    exact integral_mono (integrable_entR_right hFm (pow_pos hc0 2) hFc hFC)
      (hgpi.integral_prod_right.const_mul _) h2
  have hsum : ∫ x, ∑ k, fderiv ℝ ψ x (Pi.single k 1) ^ 2 ∂P = ∫ p, gp p ∂μ2 + ∫ p, gq p ∂μ2 := by
    rw [htrans, ← integral_add hgpi hgqi]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [hgp, hgq]
    exact Fin.sum_univ_succ _
  rw [hent, hsum]
  linarith

/-- **Gross' inequality on `ℝⁿ`** for `a + ψ > 0`, `ψ ∈ C^∞_c`. -/
theorem grossProp_all (n : ℕ) : GrossProp n := by
  induction n with
  | zero => exact grossProp_zero
  | succ n ih => exact grossProp_succ ih

end SharpLSI
