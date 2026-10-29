import DGPS.Examples.RoughBoundary.Semicontinuity
import DGPS.Examples.RoughBoundary.Model

/-!
# Quantitative product kernel convergence (SEM006)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 8.1, equations (8.5)-(8.6).

For unit-vector circle features `U`, `Ũ` put `W_U(x,y) = κ (1 - U(x)·U(y))` (`prodKernel`), and
`E = Ũ - U`.  Then, with the max-product Hölder norm on `𝕋 × 𝕋`,
`‖W_Ũ - W_U‖_{C^α} ≤ κ (‖Ũ‖_{C^α} + ‖U‖_{C^α}) ‖E‖_{C^α}`; in `L^p(𝕋²)`,
`‖W_Ũ - W_U‖_p ≤ 2κ ‖E‖_p`, and the explicit weak partial derivatives
`∂x W_U = -κ U'(x)·U(y)`, `∂y W_U = -κ U(x)·U'(y)` satisfy
`‖∂x(W_Ũ - W_U)‖_p ≤ κ (‖Ũ' - U'‖_p + ‖U'‖_p ‖E‖_∞)`, and the same for `∂y`.
The Euclidean-product Hölder estimate follows from the max-product one by `max ≤ Euclidean`.
-/

open MeasureTheory Set
open scoped Real ENNReal

namespace DGPS.Examples.RoughBoundary.Semicontinuity

open DGPS.Analysis.RateTopology (q1 q2 pairPt)

/-- The product kernel `W_U(x,y) = κ (1 - U(x)·U(y))`. -/
noncomputable def prodKernel (U : Torus 1 → EuclideanSpace ℝ (Fin 2)) (x y : Torus 1) : ℝ :=
  Model.kappa * (1 - inner ℝ (U x) (U y))

/-- The `x`-partial derivative `-κ U'(x)·U(y)` of `prodKernel U`. -/
noncomputable def prodGradX (U U' : Torus 1 → EuclideanSpace ℝ (Fin 2)) (x y : Torus 1) : ℝ :=
  -(Model.kappa * inner ℝ (U' x) (U y))

/-- The `y`-partial derivative `-κ U(x)·U'(y)` of `prodKernel U`. -/
noncomputable def prodGradY (U U' : Torus 1 → EuclideanSpace ℝ (Fin 2)) (x y : Torus 1) : ℝ :=
  -(Model.kappa * inner ℝ (U x) (U' y))

/-- The sup norm of a function on `𝕋 × 𝕋`. -/
noncomputable def prodSupNorm (D : Torus 1 → Torus 1 → ℝ) : ℝ := ⨆ z : Torus 1 × Torus 1, |D z.1 z.2|

/-- The Hölder seminorm on `𝕋 × 𝕋` for the max-product metric. -/
noncomputable def prodHolderSeminorm (α : ℝ) (D : Torus 1 → Torus 1 → ℝ) : ℝ :=
  ⨆ p : (Torus 1 × Torus 1) × (Torus 1 × Torus 1),
    |D p.1.1 p.1.2 - D p.2.1 p.2.2| /
      (max (DGPS.torusDist p.1.1 p.2.1) (DGPS.torusDist p.1.2 p.2.2)) ^ α

/-- The Hölder norm `‖D‖_{C^α} = ‖D‖_∞ + [D]_α` on `𝕋 × 𝕋` (max-product metric). -/
noncomputable def prodHolderNorm (α : ℝ) (D : Torus 1 → Torus 1 → ℝ) : ℝ :=
  prodSupNorm D + prodHolderSeminorm α D

/-- The Hölder norm `‖F‖_{C^α} = ‖F‖_∞ + [F]_α` of a vector-valued circle function. -/
noncomputable def vecHolderNorm (α : ℝ) (F : Torus 1 → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  vecSupNorm F + vecHolderSeminorm α F

lemma prodSupNorm_le {D : Torus 1 → Torus 1 → ℝ} {M : ℝ} (h : ∀ x y, |D x y| ≤ M) :
    prodSupNorm D ≤ M := ciSup_le fun z => h z.1 z.2

lemma prodSupNorm_nonneg (D : Torus 1 → Torus 1 → ℝ) : 0 ≤ prodSupNorm D :=
  Real.iSup_nonneg fun _ => abs_nonneg _

lemma prodHolderSeminorm_le {α : ℝ} (hα : 0 < α) {D : Torus 1 → Torus 1 → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y x' y', |D x y - D x' y'| ≤
      C * (max (DGPS.torusDist x x') (DGPS.torusDist y y')) ^ α) :
    prodHolderSeminorm α D ≤ C := by
  refine ciSup_le fun p => ?_
  by_cases hm : max (DGPS.torusDist p.1.1 p.2.1) (DGPS.torusDist p.1.2 p.2.2) = 0
  · rw [hm, Real.zero_rpow hα.ne', div_zero]; exact hC
  · have hm0 : 0 ≤ max (DGPS.torusDist p.1.1 p.2.1) (DGPS.torusDist p.1.2 p.2.2) :=
      le_max_of_le_left (Real.sqrt_nonneg _)
    have hpos : 0 < (max (DGPS.torusDist p.1.1 p.2.1) (DGPS.torusDist p.1.2 p.2.2)) ^ α :=
      Real.rpow_pos_of_pos (lt_of_le_of_ne hm0 (Ne.symm hm)) _
    rw [div_le_iff₀ hpos]
    exact h _ _ _ _

lemma norm_sub_le_two_vec {U Ut : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hU : ∀ x, ‖U x‖ = 1) (hUt : ∀ x, ‖Ut x‖ = 1) (x : Torus 1) : ‖Ut x - U x‖ ≤ 2 := by
  calc ‖Ut x - U x‖ ≤ ‖Ut x‖ + ‖U x‖ := norm_sub_le _ _
    _ = 2 := by rw [hU, hUt]; norm_num

lemma vecSupNorm_unit {U : Torus 1 → EuclideanSpace ℝ (Fin 2)} (hU : ∀ x, ‖U x‖ = 1) :
    vecSupNorm U = 1 := by
  refine le_antisymm (vecSupNorm_le fun x => (hU x).le) ?_
  have := norm_le_vecSupNorm (F := U) (M := 1) (fun x => (hU x).le) 0
  rwa [hU] at this

/-- Algebraic expansion: the kernel difference has one difference factor in each term. -/
lemma prodKernel_sub (U Ut : Torus 1 → EuclideanSpace ℝ (Fin 2)) (x y : Torus 1) :
    prodKernel Ut x y - prodKernel U x y =
      -(Model.kappa * (inner ℝ (Ut x - U x) (Ut y) + inner ℝ (U x) (Ut y - U y))) := by
  unfold prodKernel
  simp only [inner_sub_left, inner_sub_right]; ring

lemma prodGradX_sub (U Ut U' Ut' : Torus 1 → EuclideanSpace ℝ (Fin 2)) (x y : Torus 1) :
    prodGradX Ut Ut' x y - prodGradX U U' x y =
      -(Model.kappa * (inner ℝ (Ut' x - U' x) (Ut y) + inner ℝ (U' x) (Ut y - U y))) := by
  unfold prodGradX
  simp only [inner_sub_left, inner_sub_right]; ring

lemma prodGradY_sub (U Ut U' Ut' : Torus 1 → EuclideanSpace ℝ (Fin 2)) (x y : Torus 1) :
    prodGradY Ut Ut' x y - prodGradY U U' x y =
      -(Model.kappa * (inner ℝ (Ut x) (Ut' y - U' y) + inner ℝ (Ut x - U x) (U' y))) := by
  unfold prodGradY
  simp only [inner_sub_left, inner_sub_right]; ring

lemma kappa_nonneg : 0 ≤ Model.kappa := by unfold Model.kappa; norm_num

/-- Pointwise sup bound `|W̃ - W| ≤ κ (|E x| + |E y|)`. -/
lemma abs_prodKernel_sub_le {U Ut : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hU : ∀ x, ‖U x‖ = 1) (hUt : ∀ x, ‖Ut x‖ = 1) (x y : Torus 1) :
    |prodKernel Ut x y - prodKernel U x y| ≤
      Model.kappa * (‖Ut x - U x‖ + ‖Ut y - U y‖) := by
  rw [prodKernel_sub, abs_neg, abs_mul, abs_of_nonneg kappa_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ kappa_nonneg
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hUt, mul_one]
  · refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hU, one_mul]

/-- The max-product Hölder estimate of the kernel difference. -/
lemma abs_prodKernel_holder_le {α : ℝ} (hα : 0 < α) {U Ut : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hU : ∀ x, ‖U x‖ = 1) (hUt : ∀ x, ‖Ut x‖ = 1)
    (hUh : VecHolderBdd α U) (hUth : VecHolderBdd α Ut) (x y x' y' : Torus 1) :
    |(prodKernel Ut x y - prodKernel U x y) - (prodKernel Ut x' y' - prodKernel U x' y')| ≤
      Model.kappa * (2 * vecHolderSeminorm α (fun z => Ut z - U z) +
        vecSupNorm (fun z => Ut z - U z) * (vecHolderSeminorm α Ut + vecHolderSeminorm α U)) *
      (max (DGPS.torusDist x x') (DGPS.torusDist y y')) ^ α := by
  set E : Torus 1 → EuclideanSpace ℝ (Fin 2) := fun z => Ut z - U z with hE
  have hEh : VecHolderBdd α E := by
    obtain ⟨C1, hC1, h1⟩ := hUh
    obtain ⟨C2, hC2, h2⟩ := hUth
    refine ⟨C2 + C1, add_nonneg hC2 hC1, fun a b => ?_⟩
    have e : E a - E b = (Ut a - Ut b) - (U a - U b) := by simp only [hE]; abel
    rw [e]
    calc _ ≤ ‖Ut a - Ut b‖ + ‖U a - U b‖ := norm_sub_le _ _
      _ ≤ _ := by have := h1 a b; have := h2 a b; linarith
  have hS : ∀ z, ‖E z‖ ≤ vecSupNorm E := fun z =>
    norm_le_vecSupNorm (fun z => norm_sub_le_two_vec hU hUt z) z
  have hS0 : 0 ≤ vecSupNorm E := vecSupNorm_nonneg _
  set δ := max (DGPS.torusDist x x') (DGPS.torusDist y y') with hδ
  have hdx : DGPS.torusDist x x' ^ α ≤ δ ^ α :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) (le_max_left _ _) hα.le
  have hdy : DGPS.torusDist y y' ^ α ≤ δ ^ α :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) (le_max_right _ _) hα.le
  have hEx := hEh.norm_sub_le x x'
  have hEy := hEh.norm_sub_le y y'
  have hUtx := hUth.norm_sub_le x x'
  have hUty := hUth.norm_sub_le y y'
  have hUx := hUh.norm_sub_le x x'
  have hsE := vecHolderSeminorm_nonneg α E
  have hsU := vecHolderSeminorm_nonneg α U
  have hsUt := vecHolderSeminorm_nonneg α Ut
  have e : (prodKernel Ut x y - prodKernel U x y) - (prodKernel Ut x' y' - prodKernel U x' y') =
      -(Model.kappa * ((inner ℝ (E x - E x') (Ut y) + inner ℝ (E x') (Ut y - Ut y')) +
        (inner ℝ (U x - U x') (E y) + inner ℝ (U x') (E y - E y')))) := by
    rw [prodKernel_sub, prodKernel_sub]
    simp only [hE, inner_sub_left, inner_sub_right]; ring
  rw [e, abs_neg, abs_mul, abs_of_nonneg kappa_nonneg]
  have b1 : |inner ℝ (E x - E x') (Ut y)| ≤ vecHolderSeminorm α E * δ ^ α := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hUt, mul_one]
    exact hEx.trans (by gcongr)
  have b2 : |inner ℝ (E x') (Ut y - Ut y')| ≤
      vecSupNorm E * (vecHolderSeminorm α Ut * δ ^ α) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (hS x') (hUty.trans (by gcongr)) (norm_nonneg _) hS0
  have b3 : |inner ℝ (U x - U x') (E y)| ≤ vecHolderSeminorm α U * δ ^ α * vecSupNorm E := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (hUx.trans (by gcongr)) (hS y) (norm_nonneg _)
      (mul_nonneg hsU (Real.rpow_nonneg (le_max_of_le_left (Real.sqrt_nonneg _)) _))
  have b4 : |inner ℝ (U x') (E y - E y')| ≤ vecHolderSeminorm α E * δ ^ α := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hU, one_mul]
    exact hEy.trans (by gcongr)
  have := abs_add_le (inner ℝ (E x - E x') (Ut y) + inner ℝ (E x') (Ut y - Ut y'))
    (inner ℝ (U x - U x') (E y) + inner ℝ (U x') (E y - E y'))
  have := abs_add_le (inner ℝ (E x - E x') (Ut y)) (inner ℝ (E x') (Ut y - Ut y'))
  have := abs_add_le (inner ℝ (U x - U x') (E y)) (inner ℝ (U x') (E y - E y'))
  have key : |(inner ℝ (E x - E x') (Ut y) + inner ℝ (E x') (Ut y - Ut y')) +
      (inner ℝ (U x - U x') (E y) + inner ℝ (U x') (E y - E y'))| ≤
      (2 * vecHolderSeminorm α E + vecSupNorm E * (vecHolderSeminorm α Ut +
        vecHolderSeminorm α U)) * δ ^ α := by nlinarith
  calc _ ≤ Model.kappa * ((2 * vecHolderSeminorm α E + vecSupNorm E * (vecHolderSeminorm α Ut +
        vecHolderSeminorm α U)) * δ ^ α) := mul_le_mul_of_nonneg_left key kappa_nonneg
    _ = _ := by ring

/-! ### `L^p` estimates -/

lemma measurePreserving_q1 :
    MeasurePreserving q1 (DGPS.haar 2) (DGPS.haar 1) :=
  (measurePreserving_fst (μ := DGPS.haar 1) (ν := DGPS.haar 1)).comp
    DGPS.Analysis.RateTopology.measurePreserving_q

lemma measurePreserving_q2 :
    MeasurePreserving q2 (DGPS.haar 2) (DGPS.haar 1) :=
  (measurePreserving_snd (μ := DGPS.haar 1) (ν := DGPS.haar 1)).comp
    DGPS.Analysis.RateTopology.measurePreserving_q

lemma aesm_comp_q {q : Torus 2 → Torus 1} (hq : MeasurePreserving q (DGPS.haar 2) (DGPS.haar 1))
    {F : Type*} [NormedAddCommGroup F] {f : Torus 1 → F}
    (hf : AEStronglyMeasurable f (DGPS.haar 1)) :
    AEStronglyMeasurable (fun z => f (q z)) (DGPS.haar 2) :=
  hf.comp_quasiMeasurePreserving hq.quasiMeasurePreserving

lemma eLpNorm_const_norm_comp {q : Torus 2 → Torus 1}
    (hq : MeasurePreserving q (DGPS.haar 2) (DGPS.haar 1)) (p : ℝ≥0∞) {c : ℝ} (hc : 0 ≤ c)
    {f : Torus 1 → EuclideanSpace ℝ (Fin 2)} (hf : AEStronglyMeasurable f (DGPS.haar 1)) :
    eLpNorm (fun z => c * ‖f (q z)‖) p (DGPS.haar 2) =
      ENNReal.ofReal c * eLpNorm f p (DGPS.haar 1) := by
  have e : (fun z => c * ‖f (q z)‖) = c • (fun z => ‖f (q z)‖) := rfl
  have hm : AEStronglyMeasurable (fun z => f (q z)) (DGPS.haar 2) := aesm_comp_q hq hf
  rw [e, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc,
    eLpNorm_norm _ hm]
  have := eLpNorm_comp_measurePreserving (p := p) hf hq
  rw [← this]; rfl

/-- Generic `L^p` bound: if `‖G‖ ≤ c₁ ‖f ∘ q1‖ + c₂ ‖g ∘ q2‖`... -/
lemma eLpNorm_two_term {p : ℝ≥0∞} (hp : 1 ≤ p) {G : Torus 2 → ℝ}
    (hG : AEStronglyMeasurable G (DGPS.haar 2))
    {q q' : Torus 2 → Torus 1} (hq : MeasurePreserving q (DGPS.haar 2) (DGPS.haar 1))
    (hq' : MeasurePreserving q' (DGPS.haar 2) (DGPS.haar 1)) {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    {f g : Torus 1 → EuclideanSpace ℝ (Fin 2)} (hf : AEStronglyMeasurable f (DGPS.haar 1))
    (hg : AEStronglyMeasurable g (DGPS.haar 1))
    (h : ∀ z, |G z| ≤ c * ‖f (q z)‖ + c' * ‖g (q' z)‖) :
    eLpNorm G p (DGPS.haar 2) ≤
      ENNReal.ofReal c * eLpNorm f p (DGPS.haar 1) +
        ENNReal.ofReal c' * eLpNorm g p (DGPS.haar 1) := by
  calc eLpNorm G p (DGPS.haar 2)
      ≤ eLpNorm ((fun z => c * ‖f (q z)‖) + (fun z => c' * ‖g (q' z)‖)) p (DGPS.haar 2) := by
        refine eLpNorm_mono hG fun z => ?_
        have hnn : 0 ≤ c * ‖f (q z)‖ + c' * ‖g (q' z)‖ :=
          add_nonneg (mul_nonneg hc (norm_nonneg _)) (mul_nonneg hc' (norm_nonneg _))
        rw [Real.norm_eq_abs, Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg hnn]
        exact h z
    _ ≤ eLpNorm (fun z => c * ‖f (q z)‖) p (DGPS.haar 2) +
          eLpNorm (fun z => c' * ‖g (q' z)‖) p (DGPS.haar 2) := eLpNorm_add_le hp
    _ = _ := by rw [eLpNorm_const_norm_comp hq p hc hf, eLpNorm_const_norm_comp hq' p hc' hg]

lemma abs_prodGradX_le {U Ut U' Ut' : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hUt : ∀ x, ‖Ut x‖ = 1)
    (hS : ∀ z, ‖Ut z - U z‖ ≤ vecSupNorm (fun z => Ut z - U z)) (x y : Torus 1) :
    |prodGradX Ut Ut' x y - prodGradX U U' x y| ≤
      Model.kappa * ‖Ut' x - U' x‖ + (Model.kappa * vecSupNorm (fun z => Ut z - U z)) * ‖U' x‖ := by
  rw [prodGradX_sub, abs_neg, abs_mul, abs_of_nonneg kappa_nonneg]
  have e1 : |inner ℝ (Ut' x - U' x) (Ut y)| ≤ ‖Ut' x - U' x‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_; rw [hUt, mul_one]
  have e2 : |inner ℝ (U' x) (Ut y - U y)| ≤ vecSupNorm (fun z => Ut z - U z) * ‖U' x‖ := by
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (hS y) (norm_nonneg _)).trans_eq (mul_comm _ _))
  have := abs_add_le (inner ℝ (Ut' x - U' x) (Ut y)) (inner ℝ (U' x) (Ut y - U y))
  calc _ ≤ Model.kappa * (‖Ut' x - U' x‖ + vecSupNorm (fun z => Ut z - U z) * ‖U' x‖) :=
        mul_le_mul_of_nonneg_left (this.trans (add_le_add e1 e2)) kappa_nonneg
    _ = _ := by ring

lemma abs_prodGradY_le {U Ut U' Ut' : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hUt : ∀ x, ‖Ut x‖ = 1)
    (hS : ∀ z, ‖Ut z - U z‖ ≤ vecSupNorm (fun z => Ut z - U z)) (x y : Torus 1) :
    |prodGradY Ut Ut' x y - prodGradY U U' x y| ≤
      Model.kappa * ‖Ut' y - U' y‖ + (Model.kappa * vecSupNorm (fun z => Ut z - U z)) * ‖U' y‖ := by
  rw [prodGradY_sub, abs_neg, abs_mul, abs_of_nonneg kappa_nonneg]
  have e1 : |inner ℝ (Ut x) (Ut' y - U' y)| ≤ ‖Ut' y - U' y‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_; rw [hUt, one_mul]
  have e2 : |inner ℝ (Ut x - U x) (U' y)| ≤ vecSupNorm (fun z => Ut z - U z) * ‖U' y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hS x) (norm_nonneg _))
  have := abs_add_le (inner ℝ (Ut x) (Ut' y - U' y)) (inner ℝ (Ut x - U x) (U' y))
  calc _ ≤ Model.kappa * (‖Ut' y - U' y‖ + vecSupNorm (fun z => Ut z - U z) * ‖U' y‖) :=
        mul_le_mul_of_nonneg_left (this.trans (add_le_add e1 e2)) kappa_nonneg
    _ = _ := by ring

/-- **SEM006 (quantitative product kernel convergence).**  Let `U, Ũ` be unit-vector circle
features with a.e. derivatives `U', Ũ'`, `E = Ũ - U`, `W_U = prodKernel U` and
`D = W_Ũ - W_U`.

(a) For `α > 0` and `α`-Hölder `U, Ũ`: `‖D‖_∞ ≤ 2κ ‖E‖_∞`,
`[D]_α ≤ κ (2 [E]_α + ‖E‖_∞ ([Ũ]_α + [U]_α))` for the max-product metric,
`‖D‖_{C^α} ≤ κ (‖Ũ‖_{C^α} + ‖U‖_{C^α}) ‖E‖_{C^α}`, and the same Hölder estimate for the Euclidean
product metric `√(d(x,x')² + d(y,y')²)` (since `max ≤ Euclidean`).
(b) For `p ≥ 1`: `‖D‖_{L^p(𝕋²)} ≤ 2κ ‖E‖_{L^p(𝕋)}`.
(c) For `p ≥ 1`: `‖∂x D‖_p ≤ κ (‖Ũ' - U'‖_p + ‖U'‖_p ‖E‖_∞)` and likewise for `∂y D`, where
`∂x W_U = -κ U'(x)·U(y)` and `∂y W_U = -κ U(x)·U'(y)` (`prodGradX`, `prodGradY`). -/
theorem quantitative_product_kernel_convergence
    {U Ut U' Ut' : Torus 1 → EuclideanSpace ℝ (Fin 2)}
    (hU : ∀ x, ‖U x‖ = 1) (hUt : ∀ x, ‖Ut x‖ = 1) :
    (∀ α : ℝ, 0 < α → VecHolderBdd α U → VecHolderBdd α Ut →
      prodSupNorm (fun x y => prodKernel Ut x y - prodKernel U x y) ≤
        2 * Model.kappa * vecSupNorm (fun z => Ut z - U z) ∧
      prodHolderSeminorm α (fun x y => prodKernel Ut x y - prodKernel U x y) ≤
        Model.kappa * (2 * vecHolderSeminorm α (fun z => Ut z - U z) +
          vecSupNorm (fun z => Ut z - U z) * (vecHolderSeminorm α Ut + vecHolderSeminorm α U)) ∧
      prodHolderNorm α (fun x y => prodKernel Ut x y - prodKernel U x y) ≤
        Model.kappa * (vecHolderNorm α Ut + vecHolderNorm α U) *
          vecHolderNorm α (fun z => Ut z - U z) ∧
      ∀ x y x' y' : Torus 1,
        |(prodKernel Ut x y - prodKernel U x y) - (prodKernel Ut x' y' - prodKernel U x' y')| ≤
          Model.kappa * (2 * vecHolderSeminorm α (fun z => Ut z - U z) +
            vecSupNorm (fun z => Ut z - U z) *
              (vecHolderSeminorm α Ut + vecHolderSeminorm α U)) *
          Real.sqrt (DGPS.torusDist x x' ^ 2 + DGPS.torusDist y y' ^ 2) ^ α) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → AEStronglyMeasurable U (DGPS.haar 1) →
      AEStronglyMeasurable Ut (DGPS.haar 1) →
      eLpNorm (fun z : Torus 2 => prodKernel Ut (q1 z) (q2 z) - prodKernel U (q1 z) (q2 z)) p
          (DGPS.haar 2) ≤
        ENNReal.ofReal (2 * Model.kappa) * eLpNorm (fun z => Ut z - U z) p (DGPS.haar 1)) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → AEStronglyMeasurable U (DGPS.haar 1) →
      AEStronglyMeasurable Ut (DGPS.haar 1) → AEStronglyMeasurable U' (DGPS.haar 1) →
      AEStronglyMeasurable Ut' (DGPS.haar 1) →
      eLpNorm (fun z : Torus 2 => prodGradX Ut Ut' (q1 z) (q2 z) - prodGradX U U' (q1 z) (q2 z)) p
          (DGPS.haar 2) ≤
        ENNReal.ofReal Model.kappa *
          (eLpNorm (fun z => Ut' z - U' z) p (DGPS.haar 1) +
            eLpNorm U' p (DGPS.haar 1) * ENNReal.ofReal (vecSupNorm (fun z => Ut z - U z))) ∧
      eLpNorm (fun z : Torus 2 => prodGradY Ut Ut' (q1 z) (q2 z) - prodGradY U U' (q1 z) (q2 z)) p
          (DGPS.haar 2) ≤
        ENNReal.ofReal Model.kappa *
          (eLpNorm (fun z => Ut' z - U' z) p (DGPS.haar 1) +
            eLpNorm U' p (DGPS.haar 1) * ENNReal.ofReal (vecSupNorm (fun z => Ut z - U z)))) := by
  have hS : ∀ z, ‖Ut z - U z‖ ≤ vecSupNorm (fun z => Ut z - U z) := fun z =>
    norm_le_vecSupNorm (fun z => norm_sub_le_two_vec hU hUt z) z
  have hS0 : 0 ≤ vecSupNorm (fun z => Ut z - U z) := vecSupNorm_nonneg _
  have hk := kappa_nonneg
  refine ⟨fun α hα hUh hUth => ?_, fun p hp hu hut => ?_, fun p hp hu hut hu' hut' => ?_⟩
  · set S := vecSupNorm (fun z => Ut z - U z) with hSdef
    set sE := vecHolderSeminorm α (fun z => Ut z - U z) with hsE
    have hsE0 := vecHolderSeminorm_nonneg α (fun z => Ut z - U z)
    have hsU := vecHolderSeminorm_nonneg α U
    have hsUt := vecHolderSeminorm_nonneg α Ut
    have hsup : prodSupNorm (fun x y => prodKernel Ut x y - prodKernel U x y) ≤
        2 * Model.kappa * S := by
      refine prodSupNorm_le fun x y => ?_
      have := abs_prodKernel_sub_le hU hUt x y
      have h1 := hS x
      have h2 := hS y
      nlinarith
    have hsem : ∀ x y x' y' : Torus 1,
        |(prodKernel Ut x y - prodKernel U x y) - (prodKernel Ut x' y' - prodKernel U x' y')| ≤
          Model.kappa * (2 * sE + S * (vecHolderSeminorm α Ut + vecHolderSeminorm α U)) *
            (max (DGPS.torusDist x x') (DGPS.torusDist y y')) ^ α :=
      fun x y x' y' => abs_prodKernel_holder_le hα hU hUt hUh hUth x y x' y'
    have hB : 0 ≤ Model.kappa * (2 * sE + S * (vecHolderSeminorm α Ut + vecHolderSeminorm α U)) := by
      positivity
    have hsemle := prodHolderSeminorm_le hα hB hsem
    refine ⟨hsup, hsemle, ?_, fun x y x' y' => ?_⟩
    · unfold prodHolderNorm vecHolderNorm
      rw [vecSupNorm_unit hU, vecSupNorm_unit hUt]
      have hE : 0 ≤ vecSupNorm (fun z => Ut z - U z) + sE := by positivity
      nlinarith [mul_nonneg hk (mul_nonneg hS0 (add_nonneg hsU hsUt)),
        mul_nonneg hk (mul_nonneg hsE0 (add_nonneg hsU hsUt))]
    · refine (hsem x y x' y').trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hB
      refine Real.rpow_le_rpow (le_max_of_le_left (Real.sqrt_nonneg _)) ?_ hα.le
      refine max_le ?_ ?_
      · exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
      · exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))
  · have hEm : AEStronglyMeasurable (fun z => Ut z - U z) (DGPS.haar 1) := hut.sub hu
    have hKm : ∀ {V : Torus 1 → EuclideanSpace ℝ (Fin 2)}, AEStronglyMeasurable V (DGPS.haar 1) →
        AEStronglyMeasurable (fun z : Torus 2 => prodKernel V (q1 z) (q2 z)) (DGPS.haar 2) :=
      fun hV => (aestronglyMeasurable_const.sub ((aesm_comp_q measurePreserving_q1 hV).inner
        (aesm_comp_q measurePreserving_q2 hV))).const_mul _
    have hG := (hKm hut).sub (hKm hu)
    have := eLpNorm_two_term hp hG measurePreserving_q1 measurePreserving_q2 hk hk hEm hEm
      (G := fun z : Torus 2 => prodKernel Ut (q1 z) (q2 z) - prodKernel U (q1 z) (q2 z))
      (fun z => (abs_prodKernel_sub_le hU hUt (q1 z) (q2 z)).trans_eq (mul_add _ _ _))
    refine this.trans (le_of_eq ?_)
    rw [← add_mul, ← ENNReal.ofReal_add hk hk]
    congr 2; ring
  · have hEm : AEStronglyMeasurable (fun z => Ut z - U z) (DGPS.haar 1) := hut.sub hu
    have hEm' : AEStronglyMeasurable (fun z => Ut' z - U' z) (DGPS.haar 1) := hut'.sub hu'
    have hKX : ∀ {V V' : Torus 1 → EuclideanSpace ℝ (Fin 2)},
        AEStronglyMeasurable V (DGPS.haar 1) → AEStronglyMeasurable V' (DGPS.haar 1) →
        AEStronglyMeasurable (fun z : Torus 2 => prodGradX V V' (q1 z) (q2 z)) (DGPS.haar 2) :=
      fun hV hV' => (((aesm_comp_q measurePreserving_q1 hV').inner
        (aesm_comp_q measurePreserving_q2 hV)).const_mul _).neg
    have hKY : ∀ {V V' : Torus 1 → EuclideanSpace ℝ (Fin 2)},
        AEStronglyMeasurable V (DGPS.haar 1) → AEStronglyMeasurable V' (DGPS.haar 1) →
        AEStronglyMeasurable (fun z : Torus 2 => prodGradY V V' (q1 z) (q2 z)) (DGPS.haar 2) :=
      fun hV hV' => (((aesm_comp_q measurePreserving_q1 hV).inner
        (aesm_comp_q measurePreserving_q2 hV')).const_mul _).neg
    have hkS : 0 ≤ Model.kappa * vecSupNorm (fun z => Ut z - U z) := mul_nonneg hk hS0
    have fin : ENNReal.ofReal Model.kappa * eLpNorm (fun z => Ut' z - U' z) p (DGPS.haar 1) +
        ENNReal.ofReal (Model.kappa * vecSupNorm (fun z => Ut z - U z)) *
          eLpNorm U' p (DGPS.haar 1) =
        ENNReal.ofReal Model.kappa *
          (eLpNorm (fun z => Ut' z - U' z) p (DGPS.haar 1) +
            eLpNorm U' p (DGPS.haar 1) * ENNReal.ofReal (vecSupNorm (fun z => Ut z - U z))) := by
      rw [ENNReal.ofReal_mul hk]; ring
    constructor
    · have := eLpNorm_two_term hp ((hKX hut hut').sub (hKX hu hu')) measurePreserving_q1
        measurePreserving_q1 hk hkS hEm' hu'
        (G := fun z : Torus 2 => prodGradX Ut Ut' (q1 z) (q2 z) - prodGradX U U' (q1 z) (q2 z))
        (fun z => abs_prodGradX_le hUt hS (q1 z) (q2 z))
      refine this.trans (le_of_eq ?_)
      exact fin
    · have := eLpNorm_two_term hp ((hKY hut hut').sub (hKY hu hu')) measurePreserving_q2
        measurePreserving_q2 hk hkS hEm' hu'
        (G := fun z : Torus 2 => prodGradY Ut Ut' (q1 z) (q2 z) - prodGradY U U' (q1 z) (q2 z))
        (fun z => abs_prodGradY_le hUt hS (q1 z) (q2 z))
      refine this.trans (le_of_eq ?_)
      exact fin

/-- The model kernel is the product kernel of the model feature. -/
lemma modelW_eq_prodKernel (L ε : ℝ) : Model.modelW L ε = prodKernel (Feature.Ufeat L ε) := rfl

/-- SEM005 + SEM006: for the phase features `U_f, U_g2` the kernel difference obeys
`‖W_{U_g2} - W_{U_f}‖_p ≤ 2κ · 2π |η| ‖g2 - f‖_p`. -/
theorem prodKernel_UfeatF_Lp_le {L : ℝ} (hL : 0 < L) (η : ℝ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f g2 : Torus 1 → ℝ} (hf : AEStronglyMeasurable f (DGPS.haar 1))
    (hg2 : AEStronglyMeasurable g2 (DGPS.haar 1))
    (hd : AEStronglyMeasurable (fun y => g2 y - f y) (DGPS.haar 1)) :
    eLpNorm (fun z : Torus 2 => prodKernel (UfeatF L η g2) (q1 z) (q2 z) -
        prodKernel (UfeatF L η f) (q1 z) (q2 z)) p (DGPS.haar 2) ≤
      ENNReal.ofReal (2 * Model.kappa) * (ENNReal.ofReal (2 * π) *
        (ENNReal.ofReal |η| * eLpNorm (fun y => g2 y - f y) p (DGPS.haar 1))) := by
  have h1 := (quantitative_product_kernel_convergence (U := UfeatF L η f) (Ut := UfeatF L η g2)
    (U' := fun _ => 0) (Ut' := fun _ => 0) (norm_UfeatF L η f) (norm_UfeatF L η g2)).2.1 p hp
    (aestronglyMeasurable_UfeatF L η hf) (aestronglyMeasurable_UfeatF L η hg2)
  have h2 := ((quantitative_phase_composition_continuity hL η).2.2.1 p f g2).1 hf hg2
  have h3 := ((quantitative_phase_composition_continuity hL η).2.2.1 p f g2).2 hd
  refine h1.trans (mul_le_mul' le_rfl ?_)
  rw [← h3]
  exact h2

end DGPS.Examples.RoughBoundary.Semicontinuity
