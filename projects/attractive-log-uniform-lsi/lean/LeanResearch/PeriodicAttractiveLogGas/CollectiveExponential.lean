import LeanResearch.PeriodicAttractiveLogGas.CollectiveIntegrationByParts
import LeanResearch.PeriodicAttractiveLogGas.LocalizedVirialScalar

/-! Ordinary finite-C2 exponential calculus used in the source separated
coercivity proof. These constructions preserve the existing gradient,
Laplacian, attractive generator and full collision-crossing test class. -/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ContDiff BigOperators NNReal ENNReal RealInnerProductSpace

namespace PeriodicAttractiveLogGas.CollectiveExponential

open CollectiveIntegrationByParts MovingPoleDerivativeIdentification

def negativeExp {N : ℕ} (Q : C2Function N) (γ : ℝ) : C2Function N where
  value := ⟨fun X ↦ Real.exp (-γ * Q.value X), by fun_prop⟩
  regularity := (contDiff_const.mul Q.regularity).exp

@[simp] theorem negativeExp_value {N : ℕ} (Q : C2Function N) (γ : ℝ)
    (X : Configuration N) : (negativeExp Q γ).value X = Real.exp (-γ * Q.value X) := rfl

theorem negativeExp_pos {N : ℕ} (Q : C2Function N) (γ : ℝ) (X : Configuration N) :
    0 < (negativeExp Q γ).value X := Real.exp_pos _

theorem negativeExp_le_one {N : ℕ} (Q : C2Function N) {γ : ℝ} (hγ : 0 ≤ γ)
    {X : Configuration N} (hQ : 0 ≤ Q.value X) : (negativeExp Q γ).value X ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hQ)

private def negativeExpC1 {N : ℕ} (Q : C2Function N) (γ : ℝ) : C1Function N where
  value := (negativeExp Q γ).value
  gradient := ⟨fun X ↦ (-γ * (negativeExp Q γ).value X) • Q.gradient X, by fun_prop⟩
  differential := by
    intro y
    convert! ((Q.differential y).const_mul (-γ)).exp using 1
    ext v
    simp only [ContinuousMap.coe_mk, innerSL_apply_apply, inner_smul_left, conj_trivial,
      smul_apply, smul_eq_mul, negativeExp_value]
    ring

theorem negativeExp_gradient {N : ℕ} (Q : C2Function N) (γ : ℝ) (X : Configuration N) :
    (negativeExp Q γ).gradient X = (-γ * (negativeExp Q γ).value X) • Q.gradient X := by
  calc
    _ = descendedLiftGradient (negativeExp Q γ).value X :=
      (negativeExp Q γ).toC1.gradient_eq_descended X
    _ = (negativeExpC1 Q γ).gradient X := ((negativeExpC1 Q γ).gradient_eq_descended X).symm
    _ = _ := rfl

theorem negativeExp_particleGradient {N : ℕ} (Q : C2Function N) (γ : ℝ)
    (i : Fin N) (X : Configuration N) :
    (negativeExp Q γ).particleGradient i X =
      (-γ * (negativeExp Q γ).value X) • Q.particleGradient i X := by
  simp only [C2Function.particleGradient, negativeExp_gradient, map_smul]

theorem negativeExp_directional_second {N : ℕ} (Q : C2Function N) (γ : ℝ)
    (v : Gradient N) (X : Configuration N) :
    inner ℝ (((negativeExp Q γ).directional v).gradient X) v =
      γ ^ 2 * (negativeExp Q γ).value X * (inner ℝ (Q.gradient X) v) ^ 2 -
        γ * (negativeExp Q γ).value X * inner ℝ ((Q.directional v).gradient X) v := by
  obtain ⟨y, rfl⟩ := configurationQuotient_surjective N X
  have he : (fun z : Gradient N ↦ ((negativeExp Q γ).directional v).value
      (configurationQuotient N z)) = fun z ↦
        -γ * ((negativeExp Q γ).value (configurationQuotient N z) *
          (Q.directional v).value (configurationQuotient N z)) := by
    funext z
    simp only [C2Function.directional_value, negativeExp_gradient, inner_smul_left,
      conj_trivial]
    ring
  have hd := (((negativeExpC1 Q γ).differential y).mul
    ((Q.directional v).differential y)).const_mul (-γ)
  have hactual := ((negativeExp Q γ).directional v).differential y
  rw [he] at hactual
  have h := congrArg (fun L : Gradient N →L[ℝ] ℝ ↦ L v) (hactual.unique hd)
  simp only [innerSL_apply_apply, smul_apply,
    add_apply, smul_eq_mul, negativeExpC1,
    ContinuousMap.coe_mk, C2Function.directional_value, inner_smul_left,
    conj_trivial] at h
  nlinarith only [h]

theorem negativeExp_laplacian {N : ℕ} (Q : C2Function N) (γ : ℝ) (X : Configuration N) :
    (negativeExp Q γ).laplacian X =
      γ ^ 2 * (negativeExp Q γ).value X * ‖Q.gradient X‖ ^ 2 -
        γ * (negativeExp Q γ).value X * Q.laplacian X := by
  have hnorm : (∑ ik : Fin N × Fin 2,
      (inner ℝ (Q.gradient X) (EuclideanSpace.single ik 1)) ^ 2) = ‖Q.gradient X‖ ^ 2 := by
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] using
      (EuclideanSpace.real_norm_sq_eq (Q.gradient X)).symm
  change (∑ ik : Fin N × Fin 2, inner ℝ
    (((negativeExp Q γ).directional (EuclideanSpace.single ik 1)).gradient X)
    (EuclideanSpace.single ik 1)) = _
  simp_rw [negativeExp_directional_second]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hnorm]
  rfl

theorem negativeExp_pairDrift {N : ℕ} (Q : C2Function N) (γ β : ℝ)
    (H : Torus → PlanarSpace) (X : Configuration N) :
    (negativeExp Q γ).pairDrift H β X =
      (-γ * (negativeExp Q γ).value X) * Q.pairDrift H β X := by
  simp only [C2Function.pairDrift, negativeExp_particleGradient, ← smul_sub,
    inner_smul_right, ← Finset.mul_sum]
  ring

/-- This identity uses the actual attractive generator, at every
configuration; subsequent lower bounds may discard the null collision set. -/
theorem negativeExp_generator {N : ℕ} (Q : C2Function N) (γ β : ℝ) (X : Configuration N) :
    (negativeExp Q γ).generator β X = (negativeExp Q γ).value X *
      (γ ^ 2 * ‖Q.gradient X‖ ^ 2 - γ * Q.generator β X) := by
  simp only [C2Function.generator, negativeExp_laplacian, negativeExp_pairDrift]
  ring

theorem negativeExp_generator_quotient {N : ℕ} (Q : C2Function N) (γ β : ℝ)
    (X : Configuration N) :
    -(negativeExp Q γ).generator β X / (negativeExp Q γ).value X =
      γ * Q.generator β X - γ ^ 2 * ‖Q.gradient X‖ ^ 2 := by
  rw [negativeExp_generator]
  have hp := (negativeExp_pos Q γ X).ne'
  field_simp
  ring

/-- The common scalar exponential factor multiplies the difference of
particle gradients at the same configuration, so no extra derivative term
is introduced. The nonnegative Q gives exactly the source gamma*K. -/
theorem negativeExp_pairGradientBound {N : ℕ} (Q : C2Function N) {γ K : ℝ}
    (hγ : 0 ≤ γ) (hQ : ∀ X, 0 ≤ Q.value X) (hK : Q.PairGradientBound K) :
    (negativeExp Q γ).PairGradientBound (γ * K) := by
  intro X i j hij
  have hp := negativeExp_pos Q γ X
  have hb := negativeExp_le_one Q hγ (hQ X)
  have hk := hK X i j hij
  have hkr := (norm_nonneg _).trans hk
  rw [negativeExp_particleGradient, negativeExp_particleGradient, ← smul_sub, norm_smul]
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hγ, abs_of_pos hp]
  calc
    _ ≤ (γ * (negativeExp Q γ).value X) * (K * torusEuclideanNorm (X i - X j)) :=
      mul_le_mul_of_nonneg_left hk (by positivity)
    _ ≤ γ * (K * torusEuclideanNorm (X i - X j)) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hkr
    _ = _ := by ring

/-- Conditional assembly for a genuine C2 observable with proved generator
and gradient bounds on U. The actual bounds for the localized second
moment are separate obligations, not fields of a replacement test class. -/
theorem exponential_coercivity {N : ℕ} (Q : C2Function N) (hN : 2 ≤ N)
    {β K ell g : ℝ} (hβ : 0 ≤ β) (hsub : β < 4)
    (hpair : Q.PairGradientBound K) (hQ : ∀ X, 0 ≤ Q.value X)
    (hell : 0 < ell) (hg : 0 < g) (U : Set (Configuration N)) (hU : IsOpen U)
    (hLQ : ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      ell ≤ Q.generator β X)
    (hgrad : ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      ‖Q.gradient X‖ ^ 2 ≤ g)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (hsupport : ∀ X, X ∉ U → F X = 0) :
    (∫ X, F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) ≤ (4 * g / ell ^ 2) *
      ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) := by
  let γ := ell / (2 * g)
  let V := negativeExp Q γ
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have hκ : 0 < ell ^ 2 / (4 * g) := by positivity
  have hLV : ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      ell ^ 2 / (4 * g) * V.value X ≤ -V.generator β X := by
    filter_upwards [hLQ, hgrad] with X hX hY
    have hr := LocalizedVirialScalar.exponential_generator_rate hell hg hX hY
    change ell ^ 2 / (4 * g) ≤ γ * Q.generator β X - γ ^ 2 * ‖Q.gradient X‖ ^ 2 at hr
    rw [← negativeExp_generator_quotient Q γ β X] at hr
    exact (le_div_iff₀ (negativeExp_pos Q γ X)).mp hr
  have h := V.positive_test_ambientEnergy hN hβ hsub
    (negativeExp_pairGradientBound Q hγ hQ hpair) (negativeExp_pos Q γ) U hU hκ hLV F hF hsupport
  have he : 1 / (ell ^ 2 / (4 * g)) = 4 * g / ell ^ 2 := by field_simp
  simpa only [he] using h

/-- The source numerical coefficient, once the actual localized generator
and squared-gradient estimates have been supplied. This is not yet the
unconditional separated-region proposition. -/
theorem separated_coercivity_from_generator {N : ℕ} (Q : C2Function N) (hN : 2 ≤ N)
    {β β₀ K δ s : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hβ4 : β₀ < 4)
    (hδ : 0 < δ) (hs : 0 < s) (hpair : Q.PairGradientBound K)
    (hQ : ∀ X, 0 ≤ Q.value X) (U : Set (Configuration N)) (hU : IsOpen U)
    (hLQ : ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      (4 - β₀) * δ ^ 2 * N / 4 ≤ Q.generator β X)
    (hgrad : ∀ᵐ X ∂(gibbsMeasure greenRealRepresentative N β).restrict U,
      ‖Q.gradient X‖ ^ 2 ≤ 6400 * N * s ^ 2)
    (F : C(Configuration N, ℝ)) {L : ℝ≥0}
    (hF : LipschitzWith L (fun y ↦ F (configurationQuotient N y)))
    (hsupport : ∀ X, X ∉ U → F X = 0) :
    (∫ X, F X ^ 2 ∂gibbsMeasure greenRealRepresentative N β) ≤
      (409600 * s ^ 2 / ((4 - β₀) ^ 2 * δ ^ 4 * N)) *
      ambientEnergy (configurationLipschitzAmbient (gibbsMeasure greenRealRepresentative N β)
        (gibbsMeasure_absolutelyContinuous greenRealRepresentative N β) F hF) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hgap : 0 < 4 - β₀ := by linarith
  have h := exponential_coercivity Q hN hβ (hβ₀.trans_lt hβ4) hpair hQ
    (by positivity : 0 < (4 - β₀) * δ ^ 2 * N / 4)
    (by positivity : 0 < 6400 * N * s ^ 2) U hU hLQ hgrad F hF hsupport
  have he : 4 * (6400 * (N : ℝ) * s ^ 2) / ((4 - β₀) * δ ^ 2 * N / 4) ^ 2 =
      409600 * s ^ 2 / ((4 - β₀) ^ 2 * δ ^ 4 * N) := by
    have hN0 := hNp.ne'
    have hgap0 := hgap.ne'
    field_simp
    ring
  simpa only [he] using h

end PeriodicAttractiveLogGas.CollectiveExponential
