import SharpSymmetricLSI.Paper.Moser1
import SharpSymmetricLSI.Paper.Moser2
import SharpSymmetricLSI.Infra.ChainRule

/-!
# The Moser energy inequality for eigenfunctions (Phase 3, lane D)

Let `P` be a probability measure on `𝕋^ι` comparable to Haar measure, and `e ∈ H¹(P)` a weak
eigenfunction: `∫ ∇e·∇φ dP = λ ∫ eφ dP` for `φ ∈ H¹(P)`. Testing with `φ = G_δ(e)` gives
`∫ |∇F_δ(e)|² dP ≤ (1+2m) λ ∫ F_δ(e)² dP`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Measure (UnitAddTorus ι)}
  [IsProbabilityMeasure P] {a b : ℝ}
  (ha : (volume : Measure (UnitAddTorus ι)) ≤ ENNReal.ofReal a • P)
  (hb : P ≤ ENNReal.ofReal b • volume) {e : UnitAddTorus ι → ℝ} (he : MemH1 P e)

include hb in
theorem ac_of_le_smul : P ≪ volume := Measure.absolutelyContinuous_of_le_smul hb

include ha he in
theorem memLp_vol : MemLp e 2 volume := he.2.1.of_measure_le_smul ENNReal.ofReal_ne_top ha

include hb he in
theorem memLp_grad_P (k : ι) : MemLp (fun x => weakGrad e x k) 2 P := by
  refine he.2.2.of_le (((isWeakGrad_weakGrad he.1).aestronglyMeasurable_grad k).mono_ac
    (ac_of_le_smul hb)) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact abs_le_sqrt_sqNorm _ k

include ha hb he in
theorem memLp_grad_vol (k : ι) : MemLp (fun x => weakGrad e x k) 2 volume :=
  (memLp_grad_P hb he k).of_measure_le_smul ENNReal.ofReal_ne_top ha

include hb he in
theorem integrable_sqNorm_P : Integrable (fun x => sqNorm (weakGrad e x)) P := by
  have := he.2.2.integrable_sq
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [Real.sq_sqrt (sqNorm_nonneg _)]

include ha hb he in
/-- Chain rule in `H¹(P)` for `C¹` functions with bounded derivative vanishing at `0`. -/
theorem memH1_comp {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) {L : ℝ} (hL : ∀ t, |deriv H t| ≤ L)
    (hH0 : H 0 = 0) :
    IsWeakGrad (fun y => H (e y)) (fun y k => deriv H (e y) * weakGrad e y k) ∧
      MemH1 P (fun y => H (e y)) ∧
      weakGrad (fun y => H (e y)) =ᵐ[P] fun y k => deriv H (e y) * weakGrad e y k := by
  have hw := isWeakGrad_comp (isWeakGrad_weakGrad he.1) ((memLp_vol ha he).integrable one_le_two)
    (fun k => (memLp_grad_vol ha hb he k).integrable one_le_two) hH hL
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  have hlip : ∀ s, |H s| ≤ L * |s| := fun s => by
    have := lipschitz_of_deriv_le hH hL s 0
    rwa [hH0, sub_zero, sub_zero] at this
  have hae : weakGrad (fun y => H (e y)) =ᵐ[P] fun y k => deriv H (e y) * weakGrad e y k :=
    (ac_of_le_smul hb).ae_le (weakGrad_ae_eq hw)
  refine ⟨hw, ⟨⟨_, hw⟩, ?_, ?_⟩, hae⟩
  · refine (he.2.1.const_mul L).of_le (hH.continuous.comp_aestronglyMeasurable
      he.2.1.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hL0]
    exact hlip _
  · refine (he.2.2.const_mul L).of_le ?_ ?_
    · refine (Real.continuous_sqrt.comp_aestronglyMeasurable ?_)
      have h1 : AEStronglyMeasurable (fun x => sqNorm (fun k => deriv H (e x) * weakGrad e x k)) P :=
        Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
          (((hH.continuous_deriv le_rfl).comp_aestronglyMeasurable
            he.2.1.aestronglyMeasurable).mul (memLp_grad_P hb he k).aestronglyMeasurable).pow 2
      exact h1.congr (hae.mono fun x hx => by simp only [hx])
    · filter_upwards [hae] with x hx
      rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_mul,
        abs_of_nonneg hL0, abs_of_nonneg (Real.sqrt_nonneg _)]
      have : sqNorm (fun k => deriv H (e x) * weakGrad e x k) =
          deriv H (e x) ^ 2 * sqNorm (weakGrad e x) := by
        unfold sqNorm; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
      exact mul_le_mul_of_nonneg_right (hL _) (Real.sqrt_nonneg _)

include ha hb he in
/-- **The Moser energy inequality.** -/
theorem moser_energy {lam : ℝ}
    (heig : ∀ φ, MemH1 P φ → ∫ x, ∑ k, weakGrad e x k * weakGrad φ x k ∂P =
      lam * ∫ x, e x * φ x ∂P) {δ : ℝ} (hδ : 0 < δ) (m : ℕ) :
    ∫ x, sqNorm (fun k => deriv (Fδ δ m) (e x) * weakGrad e x k) ∂P ≤
      (1 + 2 * m) * lam * ∫ x, Fδ δ m (e x) ^ 2 ∂P := by
  obtain ⟨-, hG, hGae⟩ := memH1_comp ha hb he (contDiff_Gδ hδ m) (abs_deriv_Gδ_le hδ m)
    (by simp [Gδ])
  have h1 := heig _ hG
  have hL : ∫ x, ∑ k, weakGrad e x k * weakGrad (fun y => Gδ δ m (e y)) x k ∂P =
      ∫ x, deriv (Gδ δ m) (e x) * sqNorm (weakGrad e x) ∂P := by
    refine integral_congr_ae (hGae.mono fun x hx => ?_)
    simp only [hx, sqNorm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hR : ∫ x, e x * Gδ δ m (e x) ∂P = ∫ x, Fδ δ m (e x) ^ 2 ∂P := by
    simp_rw [mul_Gδ]
  rw [hL, hR] at h1
  have hbd : ∀ t, |deriv (Gδ δ m) t| ≤ (1 / δ) ^ (2 * m) * (1 + 2 * (2 * m : ℕ)) :=
    abs_deriv_Gδ_le hδ m
  have hint : Integrable (fun x => deriv (Gδ δ m) (e x) * sqNorm (weakGrad e x)) P := by
    refine Integrable.bdd_mul (c := (1 / δ) ^ (2 * m) * (1 + 2 * (2 * m : ℕ)))
      (integrable_sqNorm_P hb he)
      ((contDiff_Gδ hδ m).continuous_deriv le_rfl |>.comp_aestronglyMeasurable
        he.2.1.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact hbd _
  calc ∫ x, sqNorm (fun k => deriv (Fδ δ m) (e x) * weakGrad e x k) ∂P
      ≤ ∫ x, (1 + 2 * m) * (deriv (Gδ δ m) (e x) * sqNorm (weakGrad e x)) ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => sqNorm_nonneg _)
          (hint.const_mul _) (Eventually.of_forall fun x => ?_)
        have : sqNorm (fun k => deriv (Fδ δ m) (e x) * weakGrad e x k) =
            deriv (Fδ δ m) (e x) ^ 2 * sqNorm (weakGrad e x) := by
          unfold sqNorm; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        dsimp only
        rw [this, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (deriv_Fδ_sq_le hδ m _) (sqNorm_nonneg _)
    _ = (1 + 2 * m) * lam * ∫ x, Fδ δ m (e x) ^ 2 ∂P := by
        rw [integral_const_mul, h1, mul_assoc]

end SharpLSI
