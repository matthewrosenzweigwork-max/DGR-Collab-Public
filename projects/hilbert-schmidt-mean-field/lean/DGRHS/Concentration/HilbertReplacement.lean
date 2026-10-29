import DGRHS.Concentration.HilbertQuadratic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Module.RCLike.Basic

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace
namespace DGRHS.Concentration

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {n : ℕ}

def empiricalNorm (z : Fin n → H) : ℝ := ‖∑ i, z i‖

def empiricalNormOnProduct {Ω : Type*} (Z : Fin n → Ω → H) (ω : Fin n → Ω) : ℝ :=
  empiricalNorm (fun i ↦ Z i (ω i))

omit [InnerProductSpace ℝ H] in
lemma sum_coordinate_update (z : Fin n → H) (i : Fin n) (a : H) :
    (∑ j, Function.update z i a j) = (∑ j, z j)-z i+a := by
  classical
  have he : ∀ j, Function.update z i a j = z j + if j=i then a-z i else 0 := by
    intro j
    by_cases h : j=i <;> simp [h,Function.update]
  calc
    _ = ∑ j, (z j + if j=i then a-z i else 0) := Finset.sum_congr rfl fun j _ ↦ he j
    _ = _ := by simp [Finset.sum_add_distrib]; abel

lemma norm_support_replacement (z : Fin n → H) (i : Fin n) (a u : H)
    (hu : ‖u‖ ≤ 1) (hs : inner ℝ u (∑ j, z j) = empiricalNorm z) :
    (max (empiricalNorm z-empiricalNorm (Function.update z i a)) 0)^2 ≤
      (inner ℝ u (z i)-inner ℝ u a)^2 := by
  have hb : inner ℝ u (∑ j, Function.update z i a j) ≤ empiricalNorm (Function.update z i a) := by
    exact (real_inner_le_norm _ _).trans (by
      unfold empiricalNorm
      nlinarith [norm_nonneg (∑ j, Function.update z i a j)])
  rw [sum_coordinate_update, inner_add_right, inner_sub_right, hs] at hb
  have hd : empiricalNorm z-empiricalNorm (Function.update z i a) ≤ inner ℝ u (z i)-inner ℝ u a := by linarith
  have hp : max (empiricalNorm z-empiricalNorm (Function.update z i a)) 0 ≤
      |inner ℝ u (z i)-inner ℝ u a| := max_le (hd.trans (le_abs_self _)) (abs_nonneg _)
  nlinarith [le_max_right (empiricalNorm z-empiricalNorm (Function.update z i a)) 0,
    abs_nonneg (inner ℝ u (z i)-inner ℝ u a),sq_abs (inner ℝ u (z i)-inner ℝ u a)]

lemma normalized_sum_support (z : Fin n → H) (hz : (∑ i, z i) ≠ 0) :
    ‖(‖∑ i, z i‖⁻¹ : ℝ) • (∑ i, z i)‖ ≤ 1 ∧
    inner ℝ ((‖∑ i, z i‖⁻¹ : ℝ) • (∑ i, z i)) (∑ i, z i) = empiricalNorm z := by
  refine ⟨(norm_smul_inv_norm hz).le, ?_⟩
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  unfold empiricalNorm
  have hn : ‖∑ i, z i‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  field_simp

lemma bounded_centered_shift_square_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → ℝ} {B : ℝ}
    (hT : AEStronglyMeasurable T μ) (hB : ∀ᵐ x ∂μ, |T x| ≤ B)
    (hMean : ∫ x, T x ∂μ = 0) (a : ℝ) :
    (∫ x, (a-T x)^2 ∂μ) = a^2 + ∫ x, (T x)^2 ∂μ := by
  have htI := integrable_of_ae_abs_le hT hB
  have htSq := bounded_square hT hB
  have htSqI := integrable_of_ae_abs_le htSq.1 htSq.2
  have hsub := (integrable_const (a^2)).sub (htI.const_mul (2*a))
  have he : (fun x ↦ (a-T x)^2) =ᵐ[μ] (fun x ↦ a^2-2*a*T x+(T x)^2) :=
    Filter.Eventually.of_forall fun x ↦ by dsimp only; ring
  have hAdd := integral_add hsub htSqI
  have hSub := integral_sub (integrable_const (a^2)) (htI.const_mul (2*a))
  simp only [Pi.sub_apply] at hAdd hSub
  rw [integral_congr_ae he,hAdd,hSub,integral_const_mul,hMean]
  simp

omit [InnerProductSpace ℝ H] in
lemma fixed_norm_replacement_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → H}
    (hY : AEStronglyMeasurable Y μ) (z : Fin n → H) (i : Fin n) :
    Integrable (fun x ↦ (max (empiricalNorm z-empiricalNorm (Function.update z i (Y x))) 0)^2) μ := by
  have hc : Continuous (fun a : H ↦ (max (empiricalNorm z-empiricalNorm (Function.update z i a)) 0)^2) := by
    unfold empiricalNorm
    fun_prop
  apply integrable_of_ae_abs_le (B := (empiricalNorm z)^2) (hc.comp_aestronglyMeasurable hY)
  refine Filter.Eventually.of_forall fun x ↦ ?_
  have hp : 0 ≤ max (empiricalNorm z-empiricalNorm (Function.update z i (Y x))) 0 := le_max_right _ _
  have hq : max (empiricalNorm z-empiricalNorm (Function.update z i (Y x))) 0 ≤ empiricalNorm z :=
    max_le (by unfold empiricalNorm; linarith [norm_nonneg (∑ j, Function.update z i (Y x) j)])
      (by unfold empiricalNorm; exact norm_nonneg _)
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [show 0 ≤ empiricalNorm z from norm_nonneg _]

omit [InnerProductSpace ℝ H] in
lemma empirical_norm_update {Ω : Type*} (Z : Fin n → Ω → H)
    (ω : Fin n → Ω) (i : Fin n) (x : Ω) :
    empiricalNormOnProduct Z (Function.update ω i x) =
      empiricalNorm (Function.update (fun j ↦ Z j (ω j)) i (Z i x)) := by
  unfold empiricalNormOnProduct
  congr 1
  funext j
  by_cases h : j=i <;> simp [Function.update,h]

omit [InnerProductSpace ℝ H] in
lemma bounded_hilbert_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → H} {B : ℝ}
    (hY : AEStronglyMeasurable Y μ) (hB : ∀ᵐ x ∂μ, ‖Y x‖ ≤ B) : Integrable Y μ := by
  have hi : Integrable (fun x ↦ ‖Y x‖) μ := integrable_of_ae_abs_le hY.norm
    (hB.mono fun x hx ↦ by simpa using hx)
  exact (integrable_norm_iff hY).mp hi

lemma empirical_norm_replacement_variance_le [CompleteSpace H] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Fin n → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : Fin n → Ω → H) (B D : ℝ)
    (hZ : ∀ i, AEStronglyMeasurable (Z i) (μ i))
    (hB : ∀ i, ∀ᵐ x ∂μ i, ‖Z i x‖ ≤ B)
    (hMean : ∀ i, ∫ x, Z i x ∂μ i = 0)
    (hWeak : ∀ u : H, ‖u‖ ≤ 1 → (∑ i, ∫ x, (inner ℝ u (Z i x))^2 ∂μ i) ≤ D^2)
    (ω : Fin n → Ω) :
    (∑ i, coordinateReplacementVariance μ (empiricalNormOnProduct Z) i ω) ≤
      empiricalQuadraticOnProduct Z ω+D^2 := by
  let z := fun i ↦ Z i (ω i)
  by_cases hz : (∑ i, z i) = 0
  · have he : ∀ i, coordinateReplacementVariance μ (empiricalNormOnProduct Z) i ω = 0 := by
      intro i
      unfold coordinateReplacementVariance
      apply integral_eq_zero_of_ae
      refine Filter.Eventually.of_forall fun x ↦ ?_
      dsimp only [Pi.zero_apply]
      rw [empirical_norm_update]
      have h0 : empiricalNormOnProduct Z ω = 0 := by
        change empiricalNorm z = 0
        simp [empiricalNorm,hz]
      rw [h0,max_eq_right (by unfold empiricalNorm; linarith [norm_nonneg (∑ j, Function.update z i (Z i x) j)])]
      simp
    simp only [he,Finset.sum_const_zero]
    have hv : 0 ≤ empiricalQuadraticOnProduct Z ω := empirical_quadratic_nonneg _
    nlinarith [sq_nonneg D]
  · let u := (‖∑ i, z i‖⁻¹ : ℝ) • (∑ i, z i)
    have hu := normalized_sum_support z hz
    have hi : ∀ i, coordinateReplacementVariance μ (empiricalNormOnProduct Z) i ω ≤
        (inner ℝ u (z i))^2 + ∫ x, (inner ℝ u (Z i x))^2 ∂μ i := by
      intro i
      let T := fun x ↦ inner ℝ u (Z i x)
      have ht : AEStronglyMeasurable T (μ i) :=
        (show Continuous (fun y : H ↦ inner ℝ u y) from by fun_prop).comp_aestronglyMeasurable (hZ i)
      have hb : ∀ᵐ x ∂μ i, |T x| ≤ ‖u‖*B := (hB i).mono fun x hx ↦
        (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg u))
      have hm : ∫ x, T x ∂μ i = 0 := by
        rw [integral_inner (bounded_hilbert_integrable (hZ i) (hB i)),hMean i]
        simp
      have hdiff := difference_ae_bounded aestronglyMeasurable_const ht
        (Filter.Eventually.of_forall fun _ ↦ (show |inner ℝ u (z i)| ≤ |inner ℝ u (z i)| from le_rfl)) hb
      have hs := bounded_square hdiff.1 hdiff.2
      have hrI := integrable_of_ae_abs_le hs.1 hs.2
      have hpoint : ∀ᵐ x ∂μ i,
          (max (empiricalNorm z-empiricalNorm (Function.update z i (Z i x))) 0)^2 ≤
            (inner ℝ u (z i)-T x)^2 := Filter.Eventually.of_forall fun x ↦
        norm_support_replacement z i (Z i x) u hu.1 hu.2
      have h := integral_mono_ae (fixed_norm_replacement_integrable (hZ i) z i) hrI hpoint
      rw [bounded_centered_shift_square_integral ht hb hm] at h
      change (∫ x, (max (empiricalNormOnProduct Z ω-
        empiricalNormOnProduct Z (Function.update ω i x)) 0)^2 ∂μ i) ≤ _
      simp_rw [empirical_norm_update]
      exact h
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hi i)
    rw [Finset.sum_add_distrib] at hsum
    have hEmp : (∑ i, (inner ℝ u (z i))^2) ≤ empiricalQuadraticOnProduct Z ω := by
      simpa only [empiricalDirectionalSquare,real_inner_comm,empiricalQuadraticOnProduct,z] using
        empirical_directional_le_quadratic z hu.1
    exact hsum.trans (add_le_add hEmp (hWeak u hu.1))

#print axioms DGRHS.Concentration.norm_support_replacement
#print axioms DGRHS.Concentration.bounded_centered_shift_square_integral
#print axioms DGRHS.Concentration.empirical_norm_replacement_variance_le
#check @DGRHS.Concentration.empirical_norm_replacement_variance_le

end DGRHS.Concentration
