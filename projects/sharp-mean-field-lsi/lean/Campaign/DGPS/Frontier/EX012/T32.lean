import DGPS.Frontier.EX012.T24
import DGPS.Frontier.EX012.T26
import DGPS.Frontier.EX012.T27
import DGPS.Frontier.EX012.T28

/-!
# EX012.32: Bilinear norm constant

Task id: EX012.32 (node EX012, one-site complementary range equation).
Title: Bilinear norm constant.

Provides:
* `DGPS.Frontier.EX012.ex012_32_bilinear_norm_constant`: the main statement. With
  `B₂ = bilin_EX01232 α : PH α 2 →L[ℝ] PH α 2 →L[ℝ] PH.orthSub α 2`,
  `b₂ = bConst_EX01232 α` and `M₁ = mConst_EX01232 α`: (i) `B₂ f g = ½ L⁻¹ Q₀ ((D f)(D g))`;
  (ii) `B₂ f g = B₂ g f`; (iii) `b₂ = max 1 (½ ‖L⁻¹‖ ‖Q₀‖ C_mul ‖D‖²)` and `1 ≤ b₂`;
  (iv) `‖B₂ f g‖ ≤ b₂ ‖f‖ ‖g‖`; (v) `M₁ = max 1 (max ‖c₁‖ ‖s₁‖)` and `1 ≤ M₁`;
  (vi) `‖a c₁ + b s₁‖ ≤ M₁ (|a| + |b|)`.
* `DGPS.Frontier.EX012.ex012_32_bilinear_norm_constant_apply`: the defining formula (i) alone.
* `DGPS.Frontier.EX012.ex012_32_bilinear_norm_constant_symm`: the symmetry (ii) alone.
* `DGPS.Frontier.EX012.ex012_32_bilinear_norm_constant_bound`: the norm inequality (iv) alone,
  with `1 ≤ b₂`.
* `DGPS.Frontier.EX012.ex012_32_bilinear_norm_constant_harmonic`: the harmonic bound (vi) alone,
  with `1 ≤ M₁`.
* `DGPS.Frontier.EX012.ex012_32_bilinear_norm_constant_explicit`: the same inequality (iv) with the
  explicit constant `max 1 (½ ‖L⁻¹‖ ‖Q₀‖ C_mul (3/(2π))²)` of the node text in place of `b₂`.
* Helpers (all suffixed `_EX01232`): `bilinFun_EX01232` (the unbundled formula),
  `bilinFun_add_left_EX01232`, `bilinFun_smul_left_EX01232`, `bilinFun_add_right_EX01232`,
  `bilinFun_smul_right_EX01232` (bilinearity of the formula), `bilinLin_EX01232` (the bilinear
  map before bundling), `bilinBound_aux_EX01232` (the norm inequality for the formula with any bound `d ≥ ‖D‖`),
  `bilinBound_EX01232` (the same with the constant `b₂`),
  `bConst_EX01232` (`b₂`), `one_le_bConst_EX01232`, `bilin_EX01232` (`B₂`),
  `bilin_apply_EX01232`, `mConst_EX01232` (`M₁`), `one_le_mConst_EX01232`,
  `harmonicBound_EX01232`.

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. No further
  hypothesis is added.
* The objects of the formula are those of EX012.29: `L⁻¹` is `ComplementaryElliptic.ellInv`
  (the inverse of `ellEquiv`, the equivalence `W ≃L Y` of FOU018 with `L w = D² w + w`),
  `Q₀ = proj_EX01226 α 0 : PH α 0 →L PH.orthSub α 0` (EX012.26), `D = angDeriv_EX01224`
  (EX012.24), and the product is `ex012_27_bounded_multiplication` (EX012.27), so
  `B₂ f g = (1/2) • ellInv (Q₀ ((D f) * (D g)))` as an element of `W = PH.orthSub α 2`.
* "A symmetric continuous bilinear map on `PH α 2`" is realised as the curried form
  `PH α 2 →L[ℝ] PH α 2 →L[ℝ] PH.orthSub α 2`, the standard Mathlib encoding. Its codomain is `W`
  (not `PH α 2`), the codomain `L⁻¹` has and the one Task 10 and Task 11 consume. The bundled
  map is built from the unbundled formula with `LinearMap.mk₂` and `mkContinuous₂` using the
  norm inequality with the constant `b₂`, so continuity is not assumed.
* Operator norms `‖L⁻¹‖`, `‖Q₀‖`, `‖D‖` are the operator norms (`‖·‖` on `→L[ℝ]`) of `ellInv`,
  `proj_EX01226 α 0` and `angDeriv_EX01224`, and `C_mul` is `mulConst_EX01227 α`, the FOU017
  constant chosen in EX012.27. `‖D‖²` is read literally as `‖D‖ ^ 2` with the operator norm of
  `D : PH α 2 →L PH α 0`; the node text's displayed `[3/(2π)]²` is dominated by this
  (`‖D‖ ≤ 3/(2π)` from EX012.24), and the `_explicit` theorem states the inequality with the
  `3/(2π)` form of the constant too. Both are proved.
* `c₁, s₁` are read in `PH α 2`, as `cosMode_EX01228 α 2 1` and `sinMode_EX01228 α 2 1`, the space
  of the logarithm `v = a c₁ + b s₁ + w`; the norm in `‖a c₁ + b s₁‖` is the `PH α 2` norm. The
  `max` in `M₁` is written `max 1 (max ‖c₁‖ ‖s₁‖)`, which is `max(1, ‖c₁‖, ‖s₁‖)`.
* "Symmetric" is read as `B₂ f g = B₂ g f` in `W`, from commutativity of the ring product in
  EX012.27.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

section Construction

variable (α : ℝ) [HolderExponent α]

/-- The formula `(f, g) ↦ ½ L⁻¹ Q₀ ((D f)(D g))`, with values in `W = PH.orthSub α 2`. -/
noncomputable def bilinFun_EX01232 (f g : PH α 2) : PH.orthSub α 2 :=
  (1 / 2 : ℝ) • ellInv (proj_EX01226 α 0
    (ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g)))

theorem bilinFun_add_left_EX01232 (f₁ f₂ g : PH α 2) :
    bilinFun_EX01232 α (f₁ + f₂) g = bilinFun_EX01232 α f₁ g + bilinFun_EX01232 α f₂ g := by
  simp only [bilinFun_EX01232, map_add, add_apply, smul_add]

theorem bilinFun_smul_left_EX01232 (c : ℝ) (f g : PH α 2) :
    bilinFun_EX01232 α (c • f) g = c • bilinFun_EX01232 α f g := by
  simp only [bilinFun_EX01232, map_smul, smul_apply, smul_comm c]

theorem bilinFun_add_right_EX01232 (f g₁ g₂ : PH α 2) :
    bilinFun_EX01232 α f (g₁ + g₂) = bilinFun_EX01232 α f g₁ + bilinFun_EX01232 α f g₂ := by
  simp only [bilinFun_EX01232, map_add, smul_add]

theorem bilinFun_smul_right_EX01232 (c : ℝ) (f g : PH α 2) :
    bilinFun_EX01232 α f (c • g) = c • bilinFun_EX01232 α f g := by
  simp only [bilinFun_EX01232, map_smul, smul_comm c]

/-- The bilinear map before bundling continuity. -/
noncomputable def bilinLin_EX01232 : PH α 2 →ₗ[ℝ] PH α 2 →ₗ[ℝ] PH.orthSub α 2 :=
  LinearMap.mk₂ ℝ (bilinFun_EX01232 α) (bilinFun_add_left_EX01232 α)
    (bilinFun_smul_left_EX01232 α) (bilinFun_add_right_EX01232 α)
    (bilinFun_smul_right_EX01232 α)

/-- The constant `b₂ = max 1 (½ ‖L⁻¹‖ ‖Q₀‖ C_mul ‖D‖²)`. -/
noncomputable def bConst_EX01232 : ℝ :=
  max 1 (1 / 2 * ‖(ellInv : PH.orthSub α 0 →L[ℝ] PH.orthSub α 2)‖ *
    ‖(proj_EX01226 α 0 : PH α 0 →L[ℝ] PH.orthSub α 0)‖ * mulConst_EX01227 α *
    ‖(angDeriv_EX01224 : PH α 2 →L[ℝ] PH α 0)‖ ^ 2)

theorem one_le_bConst_EX01232 : 1 ≤ bConst_EX01232 α :=
  le_max_left _ _

/-- The norm inequality for the unbundled formula, with a constant `K` at least the explicit one
and bounds `‖D‖ ≤ d` for any `d`. -/
theorem bilinBound_aux_EX01232 {d : ℝ} (hd : ‖(angDeriv_EX01224 : PH α 2 →L[ℝ] PH α 0)‖ ≤ d)
    (f g : PH α 2) :
    ‖bilinFun_EX01232 α f g‖ ≤
      1 / 2 * ‖(ellInv : PH.orthSub α 0 →L[ℝ] PH.orthSub α 2)‖ *
        ‖(proj_EX01226 α 0 : PH α 0 →L[ℝ] PH.orthSub α 0)‖ * mulConst_EX01227 α * d ^ 2 *
        (‖f‖ * ‖g‖) := by
  set E := ‖(ellInv : PH.orthSub α 0 →L[ℝ] PH.orthSub α 2)‖ with hE
  set P := ‖(proj_EX01226 α 0 : PH α 0 →L[ℝ] PH.orthSub α 0)‖ with hP
  set C := mulConst_EX01227 α with hC
  have hE0 : 0 ≤ E := ContinuousLinearMap.opNorm_nonneg _
  have hP0 : 0 ≤ P := ContinuousLinearMap.opNorm_nonneg _
  have hC0 : 0 ≤ C := mulConst_nonneg_EX01227 α
  have hf : ‖angDeriv_EX01224 f‖ ≤ d * ‖f‖ :=
    ((ContinuousLinearMap.le_opNorm _ f).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _)))
  have hg : ‖angDeriv_EX01224 g‖ ≤ d * ‖g‖ :=
    ((ContinuousLinearMap.le_opNorm _ g).trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _)))
  have hm := (ex012_27_bounded_multiplication_bound α).2 (angDeriv_EX01224 f) (angDeriv_EX01224 g)
  have h1 : ‖proj_EX01226 α 0
      (ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g))‖ ≤
      P * ‖ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g)‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖ellInv (proj_EX01226 α 0
      (ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g)))‖ ≤
      E * ‖proj_EX01226 α 0
      (ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g))‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hdd : ‖angDeriv_EX01224 f‖ * ‖angDeriv_EX01224 g‖ ≤ d * ‖f‖ * (d * ‖g‖) :=
    mul_le_mul hf hg (norm_nonneg _) ((norm_nonneg _).trans hf)
  have h3 : ‖ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g)‖ ≤
      C * (d * ‖f‖ * (d * ‖g‖)) :=
    hm.trans (mul_le_mul_of_nonneg_left hdd hC0)
  have h4 : ‖ellInv (proj_EX01226 α 0
      (ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g)))‖ ≤
      E * (P * (C * (d * ‖f‖ * (d * ‖g‖)))) :=
    h2.trans (mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h3 hP0)) hE0)
  have h5 : ‖bilinFun_EX01232 α f g‖ = 1 / 2 * ‖ellInv (proj_EX01226 α 0
      (ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g)))‖ := by
    rw [bilinFun_EX01232, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  rw [h5]
  calc 1 / 2 * ‖ellInv (proj_EX01226 α 0
      (ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g)))‖
      ≤ 1 / 2 * (E * (P * (C * (d * ‖f‖ * (d * ‖g‖))))) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
    _ = _ := by ring

/-- The norm inequality for the unbundled formula, with the constant `b₂`. -/
theorem bilinBound_EX01232 (f g : PH α 2) :
    ‖bilinFun_EX01232 α f g‖ ≤ bConst_EX01232 α * (‖f‖ * ‖g‖) := by
  refine (bilinBound_aux_EX01232 α le_rfl f g).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The symmetric continuous bilinear map `B₂(f, g) = ½ L⁻¹ Q₀ ((D f)(D g))` on `PH α 2`. -/
noncomputable def bilin_EX01232 : PH α 2 →L[ℝ] PH α 2 →L[ℝ] PH.orthSub α 2 :=
  (bilinLin_EX01232 α).mkContinuous₂ (bConst_EX01232 α) (fun f g => by
    have := bilinBound_EX01232 α f g
    calc _ ≤ _ := this
      _ = _ := by ring)

theorem bilin_apply_EX01232 (f g : PH α 2) : bilin_EX01232 α f g = bilinFun_EX01232 α f g := rfl

/-- The constant `M₁ = max (1, ‖c₁‖, ‖s₁‖)`, with `c₁, s₁` taken in `PH α 2`. -/
noncomputable def mConst_EX01232 : ℝ :=
  max 1 (max ‖cosMode_EX01228 α 2 1‖ ‖sinMode_EX01228 α 2 1‖)

theorem one_le_mConst_EX01232 : 1 ≤ mConst_EX01232 α :=
  le_max_left _ _

/-- The harmonic bound `‖a c₁ + b s₁‖ ≤ M₁ (|a| + |b|)`. -/
theorem harmonicBound_EX01232 (a b : ℝ) :
    ‖a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1‖ ≤
      mConst_EX01232 α * (|a| + |b|) := by
  have hc : ‖cosMode_EX01228 α 2 1‖ ≤ mConst_EX01232 α :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hs : ‖sinMode_EX01228 α 2 1‖ ≤ mConst_EX01232 α :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  have h1 := mul_le_mul_of_nonneg_left hc (abs_nonneg a)
  have h2 := mul_le_mul_of_nonneg_left hs (abs_nonneg b)
  linarith

end Construction

section Main

variable {α : ℝ} [HolderExponent α]

/-- The defining formula `B₂ f g = ½ L⁻¹ Q₀ ((D f)(D g))`. -/
theorem ex012_32_bilinear_norm_constant_apply (f g : PH α 2) :
    bilin_EX01232 α f g =
      (1 / 2 : ℝ) • ellInv (proj_EX01226 α 0
        (ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g))) :=
  rfl

/-- Symmetry of `B₂`. -/
theorem ex012_32_bilinear_norm_constant_symm (f g : PH α 2) :
    bilin_EX01232 α f g = bilin_EX01232 α g f := by
  rw [bilin_apply_EX01232, bilin_apply_EX01232, bilinFun_EX01232, bilinFun_EX01232,
    ex012_27_bounded_multiplication_comm]

/-- The norm inequality `‖B₂(f, g)‖ ≤ b₂ ‖f‖ ‖g‖`, with `1 ≤ b₂`. -/
theorem ex012_32_bilinear_norm_constant_bound :
    1 ≤ bConst_EX01232 α ∧ ∀ f g : PH α 2,
      ‖bilin_EX01232 α f g‖ ≤ bConst_EX01232 α * (‖f‖ * ‖g‖) :=
  ⟨one_le_bConst_EX01232 α, bilinBound_EX01232 α⟩

/-- The harmonic bound `‖a c₁ + b s₁‖ ≤ M₁ (|a| + |b|)`, with `1 ≤ M₁`. -/
theorem ex012_32_bilinear_norm_constant_harmonic :
    1 ≤ mConst_EX01232 α ∧ ∀ a b : ℝ,
      ‖a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1‖ ≤
        mConst_EX01232 α * (|a| + |b|) :=
  ⟨one_le_mConst_EX01232 α, harmonicBound_EX01232 α⟩

/-- The norm inequality with the explicit constant of the node text,
`max 1 (½ ‖L⁻¹‖ ‖Q₀‖ C_mul (3/(2π))²)`. -/
theorem ex012_32_bilinear_norm_constant_explicit (f g : PH α 2) :
    ‖bilin_EX01232 α f g‖ ≤
      max 1 (1 / 2 * ‖(ellInv : PH.orthSub α 0 →L[ℝ] PH.orthSub α 2)‖ *
        ‖(proj_EX01226 α 0 : PH α 0 →L[ℝ] PH.orthSub α 0)‖ * mulConst_EX01227 α *
        (3 / (2 * Real.pi)) ^ 2) * (‖f‖ * ‖g‖) := by
  have hD : ‖(angDeriv_EX01224 : PH α 2 →L[ℝ] PH α 0)‖ ≤ 3 / (2 * Real.pi) :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h =>
      ex012_24_bounded_angular_first_derivative_norm h
  refine (bilinBound_aux_EX01232 α hD f g).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- **EX012.32.**  The map `B₂(f, g) = ½ L⁻¹ Q₀ ((D f)(D g))` is a symmetric continuous bilinear
map `PH α 2 → PH α 2 → W`; with `b₂ = max(1, ½ ‖L⁻¹‖ ‖Q₀‖ C_mul ‖D‖²)` one has
`‖B₂(f, g)‖ ≤ b₂ ‖f‖ ‖g‖`, and with `M₁ = max(1, ‖c₁‖, ‖s₁‖)` one has
`‖a c₁ + b s₁‖ ≤ M₁ (|a| + |b|)`. -/
theorem ex012_32_bilinear_norm_constant :
    (∀ f g : PH α 2, bilin_EX01232 α f g =
      (1 / 2 : ℝ) • ellInv (proj_EX01226 α 0
        (ex012_27_bounded_multiplication α (angDeriv_EX01224 f) (angDeriv_EX01224 g)))) ∧
    (∀ f g : PH α 2, bilin_EX01232 α f g = bilin_EX01232 α g f) ∧
    (bConst_EX01232 α =
      max 1 (1 / 2 * ‖(ellInv : PH.orthSub α 0 →L[ℝ] PH.orthSub α 2)‖ *
        ‖(proj_EX01226 α 0 : PH α 0 →L[ℝ] PH.orthSub α 0)‖ * mulConst_EX01227 α *
        ‖(angDeriv_EX01224 : PH α 2 →L[ℝ] PH α 0)‖ ^ 2)) ∧
    1 ≤ bConst_EX01232 α ∧
    (∀ f g : PH α 2, ‖bilin_EX01232 α f g‖ ≤ bConst_EX01232 α * (‖f‖ * ‖g‖)) ∧
    mConst_EX01232 α =
      max 1 (max ‖cosMode_EX01228 α 2 1‖ ‖sinMode_EX01228 α 2 1‖) ∧
    1 ≤ mConst_EX01232 α ∧
    (∀ a b : ℝ, ‖a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1‖ ≤
      mConst_EX01232 α * (|a| + |b|)) :=
  ⟨ex012_32_bilinear_norm_constant_apply, ex012_32_bilinear_norm_constant_symm, rfl,
    ex012_32_bilinear_norm_constant_bound.1, ex012_32_bilinear_norm_constant_bound.2, rfl,
    ex012_32_bilinear_norm_constant_harmonic.1, ex012_32_bilinear_norm_constant_harmonic.2⟩

end Main

end DGPS.Frontier.EX012
