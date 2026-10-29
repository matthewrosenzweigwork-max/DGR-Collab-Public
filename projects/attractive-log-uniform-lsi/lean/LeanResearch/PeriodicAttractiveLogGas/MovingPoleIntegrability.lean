import LeanResearch.PeriodicAttractiveLogGas.CappedPointWeights
import LeanResearch.PeriodicAttractiveLogGas.GreenMollifierFarUpper
import LeanResearch.PeriodicAttractiveLogGas.GreenMollifierGradient
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Uniform moments for regularized moving logarithmic poles

Source Lemma 3.5, the paragraph giving the uniform three-halves moment.
The additional inverse-distance factor is an extra pole of weight one.
Consequently the total power is at most `(3/2) * (1 + 1/16) = 51/32 < 2`.
All pole positions, including coincidences and boundary positions, are allowed.

The actual mollified Green function and its ordinary Euclidean Riesz gradient
are used below. Geometric hypotheses are the nearby-lift and far-separation
conclusions already supplied by `GreenPointWeights`. All measures in the main
analytic estimate are actual probability measures dominated by planar volume.
The final mesh wrapper supplies these hypotheses for both edge orientations.

Distributional passage to the unmollified conditional integrals remains a
separate step.
-/

noncomputable section

open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal BigOperators Topology ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas.MovingPoleIntegrability

open SingularRectangleMoments GreenPointRescaling GreenPointWeights

/-- Uniform bound for the three-halves integral, after adding one pole. -/
def momentConstant : ℝ := 1 + 64 * Real.pi / 13

/-- Uniform bound for the actual finite three-halves norm. -/
def normConstant : ℝ := momentConstant ^ (2 / 3 : ℝ)

theorem momentConstant_pos : 0 < momentConstant := by
  unfold momentConstant
  positivity

theorem normConstant_nonneg : 0 ≤ normConstant :=
  Real.rpow_nonneg momentConstant_pos.le _

theorem local_power_identity : (3 / 2 : ℝ) * (1 + 1 / 16) = 51 / 32 := by norm_num

theorem local_power_lt_two : (51 / 32 : ℝ) < 2 := by norm_num

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Generalized Hölder and the actual planar disk integral give this bound;
integrability of the moment is part of the conclusion. -/
theorem poleProduct_three_halves_moment {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : ∑ i, w i ≤ 17 / 16) :
    Integrable (fun Z ↦ poleProduct Y w Z ^ (3 / 2 : ℝ)) μ ∧
      (∫ Z, poleProduct Y w Z ^ (3 / 2 : ℝ) ∂μ) ≤ momentConstant := by
  have hp : (3 / 2 : ℝ) * (∑ i, w i) < 2 := by linarith
  obtain ⟨hi, hb⟩ := poleProduct_moment hμ Y w hw (by norm_num : (0 : ℝ) < 3 / 2) hp
  refine ⟨hi, hb.trans ?_⟩
  have hd : (13 / 32 : ℝ) ≤ 2 - (3 / 2 : ℝ) * (∑ i, w i) := by linarith
  have hh := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * Real.pi)
    (by norm_num : (0 : ℝ) < 13 / 32) hd
  calc
    1 + 2 * Real.pi / (2 - (3 / 2 : ℝ) * (∑ i, w i)) ≤
        1 + 2 * Real.pi / (13 / 32) := add_le_add le_rfl hh
    _ = momentConstant := by unfold momentConstant; ring

theorem poleProduct_three_halves {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : ∑ i, w i ≤ 17 / 16) :
    MemLp (poleProduct Y w) (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
      lpNorm (poleProduct Y w) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ normConstant := by
  have hm := measurable_poleProduct Y w
  have h := poleProduct_three_halves_moment hμ Y w hw hκ
  have he : (fun Z ↦ ‖poleProduct Y w Z‖ ^ (3 / 2 : ℝ)) =
      (fun Z ↦ poleProduct Y w Z ^ (3 / 2 : ℝ)) := by
    funext Z
    rw [Real.norm_of_nonneg (poleProduct_nonneg Y w Z)]
  have hmem : MemLp (poleProduct Y w) (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    apply (integrable_norm_rpow_iff hm.aestronglyMeasurable
      (by norm_num : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2), he]
    exact h.1
  refine ⟨hmem, ?_⟩
  rw [DensityMoments.lpNorm_ofReal_eq (by norm_num : (0 : ℝ) < 3 / 2)
    hm.aestronglyMeasurable, he]
  norm_num only [one_div_div, div_one]
  exact Real.rpow_le_rpow
    (integral_nonneg fun Z ↦ Real.rpow_nonneg (poleProduct_nonneg Y w Z) _) h.2 (by norm_num)

/-- The new pole need not differ from any old pole. It can be an old pole
whose interaction coefficient is zero. -/
def augmentedPoles (Y : ι → PlanarSpace) (X : PlanarSpace) : Option ι → PlanarSpace
  | none => X
  | some i => Y i

def augmentedWeights (w : ι → ℝ) : Option ι → ℝ
  | none => 1
  | some i => w i

theorem sum_augmentedWeights (w : ι → ℝ) :
    (∑ i, augmentedWeights w i) = 1 + ∑ i, w i := by
  simp [Fintype.sum_option, augmentedWeights]

theorem poleProduct_augmented (Y : ι → PlanarSpace) (w : ι → ℝ)
    (X Z : PlanarSpace) :
    poleProduct (augmentedPoles Y X) (augmentedWeights w) Z =
      (‖Z - X‖)⁻¹ * poleProduct Y w Z := by
  rw [poleProduct, Fintype.prod_option]
  simp only [augmentedPoles, augmentedWeights, inverseDistancePower, Real.rpow_neg_one,
    poleProduct]

theorem inverseDistance_mul_poleProduct_three_halves {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hκ : ∑ i, w i ≤ 1 / 16) (X : PlanarSpace) :
    MemLp (fun Z ↦ (‖Z - X‖)⁻¹ * poleProduct Y w Z)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
    lpNorm (fun Z ↦ (‖Z - X‖)⁻¹ * poleProduct Y w Z)
      (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ normConstant := by
  have ha : ∀ i, 0 ≤ augmentedWeights w i := by
    intro i
    cases i with
    | none => exact zero_le_one
    | some i => exact hw i
  have hs : (∑ i, augmentedWeights w i) ≤ 17 / 16 := by
    rw [sum_augmentedWeights]
    linarith
  have he : poleProduct (augmentedPoles Y X) (augmentedWeights w) =
      (fun Z ↦ (‖Z - X‖)⁻¹ * poleProduct Y w Z) :=
    funext (poleProduct_augmented Y w X)
  simpa only [he] using
    poleProduct_three_halves hμ (augmentedPoles Y X) (augmentedWeights w) ha hs

/-- A measurable vector field can be bounded by these actual finite scalar
norms. This helper does not assert that a totalized real norm is finite. -/
theorem memLp_and_norm_le_of_scalar_bound {E : Type*} [NormedAddCommGroup E]
    {μ : Measure PlanarSpace} {g : PlanarSpace → ℝ} {f : PlanarSpace → E}
    {A M : ℝ} (hA : 0 ≤ A) (hg : MemLp g (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hgM : lpNorm g (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ M)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ Z ∂μ, ‖f Z‖ ≤ A * g Z) :
    MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
      lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ A * M := by
  have hAg := hg.const_mul A
  refine ⟨hAg.mono' hf hb, ?_⟩
  have hn : lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      lpNorm (fun Z ↦ A * g Z) (ENNReal.ofReal (3 / 2 : ℝ)) μ :=
    ENNReal.toReal_mono hAg.eLpNorm_ne_top (eLpNorm_mono_ae_real hf hb)
  rw [DensityEntropy.lpNorm_const_mul, abs_of_nonneg hA] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left hgM hA)

/-- Uniform boundedness in the genuine finite three-halves norm implies
probability-theoretic uniform integrability in L1. There is no common
pointwise dominating function among the hypotheses. -/
theorem uniformIntegrable_of_three_halves_bound {T A E : Type*}
    [MeasurableSpace A] [NormedAddCommGroup E] {μ : Measure A} [IsProbabilityMeasure μ]
    {f : T → A → E} {C : ℝ} (_hC : 0 ≤ C)
    (hf : ∀ t, MemLp (f t) (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hb : ∀ t, lpNorm (f t) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ C) :
    UniformIntegrable f 1 μ := by
  have he (t : T) : eLpNorm (f t) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ ENNReal.ofReal C := by
    rw [← ofReal_lpNorm (hf t)]
    exact ENNReal.ofReal_le_ofReal (hb t)
  have hu : UnifIntegrable f 1 μ := by
    unfold UnifIntegrable
    apply tendsto_nhds_bot_mono
      (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos (c := ENNReal.ofReal C) ENNReal.ofReal_ne_top
        (by norm_num : (0 : ℝ) < 1 / 3))
    apply Eventually.of_forall
    intro δ
    simp only [iSup_le_iff]
    intro t s hs
    have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict s)
      (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ))
      (hf t).aestronglyMeasurable.restrict
    have hc' : eLpNorm (f t) 1 (μ.restrict s) ≤
        eLpNorm (f t) (ENNReal.ofReal (3 / 2 : ℝ)) (μ.restrict s) * μ s ^ (1 / 3 : ℝ) := by
      norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2),
        Measure.restrict_apply_univ] at hc
      convert hc using 1
    exact hc'.trans (mul_le_mul'
      ((eLpNorm_restrict_le _ _ _ _).trans (he t))
      (ENNReal.rpow_le_rpow hs (by norm_num)))
  refine ⟨hu, ⟨(ENNReal.ofReal C).toNNReal, fun t ↦ ?_⟩⟩
  have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 / 2 : ℝ)) (hf t).aestronglyMeasurable
  have hc' : eLpNorm (f t) 1 μ ≤ eLpNorm (f t) (ENNReal.ofReal (3 / 2 : ℝ)) μ := by
    simpa only [measure_univ, ENNReal.one_rpow, mul_one] using hc
  rw [ENNReal.coe_toNNReal ENNReal.ofReal_ne_top]
  exact hc'.trans (he t)

/-- Only previously proved kernel and regularization conclusions are stored.
In particular this record contains no moving-pole integrability assertion. -/
structure KernelBounds where
  value : ℝ
  upper : ℝ
  gradient : ℝ
  value_nonneg : 0 ≤ value
  upper_nonneg : 0 ≤ upper
  gradient_nonneg : 0 ≤ gradient
  value_bound : ∀ z : Torus, z ≠ 0 →
    |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ value
  upper_bound : ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
    ∀ z : Torus, z ≠ 0 → regularizedGreen ε hε z ≤ regularGreenRepresentative z + upper * ε ^ 2
  gradient_bound : ∀ ε : ℝ, ∀ hε : 0 < ε, ε ≤ (1 / 16 : ℝ) →
    ∀ z : Torus, z ≠ 0 → ‖regularizedGreenGradient ε hε z‖ ≤ gradient / torusEuclideanNorm z

theorem kernelBounds_nonempty : Nonempty KernelBounds := by
  obtain ⟨C₀, hC₀, hk⟩ := exists_regularGreenRepresentative_torus_bounds
  obtain ⟨Cu, hCu, hu⟩ := exists_regularizedGreen_upper_bound
  obtain ⟨C₁, hC₁, h₁⟩ := exists_regularizedGreenGradient_bound
  exact ⟨⟨C₀, Cu, C₁, hC₀.le, hCu.le, hC₁.le, fun z hz ↦ (hk z hz).1, hu, h₁⟩⟩

/-- One fixed choice, independent of the mesh, coefficients, sources and scale. -/
def fixedKernelBounds : KernelBounds := Classical.choice kernelBounds_nonempty

def regularizedTorusWeight (y : ι → Torus) (w : ι → ℝ)
    (ε : ℝ) (hε : 0 < ε) (z : Torus) : ℝ :=
  Real.exp (∑ i, w i * regularizedGreen ε hε (z - y i))

def regularizedSourceGradient (y : ι → Torus) (w : ι → ℝ)
    (ε : ℝ) (hε : 0 < ε) (j : ι) (z : Torus) : PlanarSpace :=
  (-w j * regularizedTorusWeight y w ε hε z) • regularizedGreenGradient ε hε (z - y j)

theorem continuous_regularizedTorusWeight (y : ι → Torus) (w : ι → ℝ)
    (ε : ℝ) (hε : 0 < ε) : Continuous (regularizedTorusWeight y w ε hε) := by
  apply Real.continuous_exp.comp
  exact continuous_finsetSum _ fun i _ ↦ continuous_const.mul
    ((continuous_regularizedGreen ε hε).comp (continuous_id.sub continuous_const))

theorem continuous_regularizedSourceGradient (y : ι → Torus) (w : ι → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (j : ι) :
    Continuous (regularizedSourceGradient y w ε hε j) :=
  (continuous_const.mul (continuous_regularizedTorusWeight y w ε hε)).smul
    ((continuous_regularizedGreenGradient ε hε hs).comp (continuous_id.sub continuous_const))

/-- Ordinary differentiation with respect to the physical source coordinate.
The negative sign comes from `z - x`. No reciprocal mesh factor occurs when
differentiating with respect to this physical coordinate. -/
theorem hasFDerivAt_single_source (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    (z : Torus) (A c : ℝ) (x : PlanarSpace) :
    HasFDerivAt (fun X : PlanarSpace ↦ Real.exp (A + c * regularizedGreen ε hε (z - torusQuotient X)))
      ((-c * Real.exp (A + c * regularizedGreen ε hε (z - torusQuotient x))) •
        regularizedGreenDifferential ε hε (z - torusQuotient x)) x := by
  have hd := ((contDiff_regularizedGreen_lift ε hε hs).differentiable (by simp))
    (centeredLift z - x)
  have hsub := hd.hasFDerivAt.comp x ((hasFDerivAt_id x).const_sub (centeredLift z))
  have hD : fderiv ℝ (fun X : PlanarSpace ↦ regularizedGreen ε hε (torusQuotient X))
      (centeredLift z - x) = regularizedGreenDifferential ε hε (z - torusQuotient x) := by
    rw [← regularizedGreenDifferential_lift, torusQuotient_sub, torusQuotient_centeredLift]
  have hh : HasFDerivAt (fun X : PlanarSpace ↦ regularizedGreen ε hε (z - torusQuotient X))
      (-regularizedGreenDifferential ε hε (z - torusQuotient x)) x := by
    simpa only [Function.comp_def, torusQuotient_sub, torusQuotient_centeredLift, hD,
      ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] using hsub
  convert ((hh.const_mul c).const_add A).exp using 1
  ext v
  simp only [smul_apply, neg_apply, smul_eq_mul]
  ring

theorem regularizedTorusWeight_update [DecidableEq ι] (y : ι → Torus) (w : ι → ℝ)
    (ε : ℝ) (hε : 0 < ε) (j : ι) (z q : Torus) :
    regularizedTorusWeight (Function.update y j q) w ε hε z =
      Real.exp ((∑ i ∈ Finset.univ.erase j, w i * regularizedGreen ε hε (z - y i)) +
        w j * regularizedGreen ε hε (z - q)) := by
  unfold regularizedTorusWeight
  congr 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

/-- The field being estimated is the Riesz gradient of the actual weight
when a single source position is varied in an ordinary Euclidean lift. -/
theorem sourceGradient_eq_riesz_fderiv [DecidableEq ι]
    (y : ι → Torus) (w : ι → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) (j : ι) (z : Torus) (x : PlanarSpace)
    (hx : torusQuotient x = y j) :
    (InnerProductSpace.toDual ℝ PlanarSpace).symm
      (fderiv ℝ (fun X : PlanarSpace ↦
        regularizedTorusWeight (Function.update y j (torusQuotient X)) w ε hε z) x) =
      regularizedSourceGradient y w ε hε j z := by
  have he := funext fun X : PlanarSpace ↦ regularizedTorusWeight_update y w ε hε j z (torusQuotient X)
  rw [he, (hasFDerivAt_single_source ε hε hs z _ (w j) x).fderiv]
  have hW := regularizedTorusWeight_update y w ε hε j z (torusQuotient x)
  rw [hx, Function.update_eq_self] at hW
  rw [hx, ← hW]
  simp only [map_smul, regularizedSourceGradient, regularizedGreenGradient]

theorem norm_source_fderiv [DecidableEq ι] (y : ι → Torus) (w : ι → ℝ)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (j : ι) (z : Torus)
    (x : PlanarSpace) (hx : torusQuotient x = y j) :
    ‖fderiv ℝ (fun X : PlanarSpace ↦
      regularizedTorusWeight (Function.update y j (torusQuotient X)) w ε hε z) x‖ =
      ‖regularizedSourceGradient y w ε hε j z‖ := by
  rw [← sourceGradient_eq_riesz_fderiv y w ε hε hs j z x hx]
  exact ((InnerProductSpace.toDual ℝ PlanarSpace).symm.norm_map _).symm

def splitSources (a : PlanarSpace) (J : ℝ) (Y : ι → PlanarSpace) (y : κ → Torus) : ι ⊕ κ → Torus :=
  Sum.elim (fun i ↦ chart a J (Y i)) y

def splitWeights (w : ι → ℝ) (v : κ → ℝ) : ι ⊕ κ → ℝ := Sum.elim w v

def referenceWeight (a : PlanarSpace) (J : ℝ) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (y : κ → Torus) (v : κ → ℝ) (ε : ℝ) (hε : 0 < ε) (Z : PlanarSpace) : ℝ :=
  regularizedTorusWeight (splitSources a J Y y) (splitWeights w v) ε hε (chart a J Z)

theorem referenceWeight_eq (a : PlanarSpace) (J : ℝ) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (y : κ → Torus) (v : κ → ℝ) (ε : ℝ) (hε : 0 < ε) (Z : PlanarSpace) :
    referenceWeight a J Y w y v ε hε Z =
      Real.exp ((∑ i, w i * regularizedGreen ε hε (chart a J Z - chart a J (Y i))) +
        ∑ i, v i * regularizedGreen ε hε (chart a J Z - y i)) := by
  simp only [referenceWeight, regularizedTorusWeight, Fintype.sum_sum_type, splitSources, splitWeights,
    Sum.elim_inl, Sum.elim_inr]

theorem continuous_chart (a : PlanarSpace) (J : ℝ) : Continuous (chart a J) := by
  have hq : Continuous torusQuotient := by unfold torusQuotient; fun_prop
  exact hq.comp (RectangleDilation.continuous_affine a J)

theorem continuous_referenceWeight (a : PlanarSpace) (J : ℝ) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (y : κ → Torus) (v : κ → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (referenceWeight a J Y w y v ε hε) :=
  (continuous_regularizedTorusWeight _ _ ε hε).comp (continuous_chart a J)

/-- This constant is allowed to depend on the fixed mesh scale. It is
independent of the pole positions and of the regularization parameter. -/
def exponentBound (K : KernelBounds) (J R : ℝ) : ℝ :=
  K.value + |Real.log J| + |Real.log (R / J)| + K.upper

def weightConstant (K : KernelBounds) (β₀ J R : ℝ) : ℝ := Real.exp (β₀ * exponentBound K J R)

theorem exponentBound_nonneg (K : KernelBounds) (J R : ℝ) : 0 ≤ exponentBound K J R := by
  unfold exponentBound
  exact add_nonneg (add_nonneg (add_nonneg K.value_nonneg (abs_nonneg _)) (abs_nonneg _))
    K.upper_nonneg

theorem weightConstant_pos (K : KernelBounds) (β₀ J R : ℝ) : 0 < weightConstant K β₀ J R :=
  Real.exp_pos _

/-- The exact local quotient radius, with the physical inverse mesh scale. -/
theorem near_radius (a : PlanarSpace) {J D : ℝ} (hJ : 0 < J) (hDJ : D < J / 2)
    {Y Z : PlanarSpace} (hd : ‖Z - Y‖ ≤ D) :
    torusEuclideanNorm (chart a J Z - chart a J Y) = ‖Z - Y‖ / J := by
  rw [chart_sub]
  have hn : ‖J⁻¹ • (Z - Y)‖ = ‖Z - Y‖ / J := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hJ), div_eq_mul_inv, mul_comm]
  have hs : ‖J⁻¹ • (Z - Y)‖ < (1 / 2 : ℝ) := by
    rw [hn]
    apply (div_lt_iff₀ hJ).mpr
    linarith
  rw [torusEuclideanNorm_quotient_eq_of_norm_lt_half hs, hn]

theorem near_ne_zero (a : PlanarSpace) {J D : ℝ} (hJ : 0 < J) (hDJ : D < J / 2)
    {Y Z : PlanarSpace} (hne : Z ≠ Y) (hd : ‖Z - Y‖ ≤ D) : chart a J Z - chart a J Y ≠ 0 := by
  intro hz
  have hr := near_radius a hJ hDJ hd
  rw [hz, torusEuclideanNorm_zero] at hr
  exact (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) hJ).ne' hr.symm

theorem far_ne_zero (a : PlanarSpace) {J R : ℝ} (hJ : 0 < J) (hR : 0 < R)
    {y : Torus} {Z : PlanarSpace} (hs : R / J ≤ torusEuclideanNorm (chart a J Z - y)) :
    chart a J Z - y ≠ 0 := by
  intro hz
  rw [hz, torusEuclideanNorm_zero] at hs
  exact (not_le_of_gt (div_pos hR hJ)) hs

theorem regularized_near_upper (K : KernelBounds) (a : PlanarSpace) {J D R : ℝ}
    (hJ : 0 < J) (hDJ : D < J / 2) (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    {Y Z : PlanarSpace} (hne : Z ≠ Y) (hd : ‖Z - Y‖ ≤ D) :
    regularizedGreen ε hε (chart a J Z - chart a J Y) ≤ exponentBound K J R - Real.log ‖Z - Y‖ := by
  have hu := K.upper_bound ε hε hs _ (near_ne_zero a hJ hDJ hne hd)
  have hb := (abs_le.mp (abs_logRemainder_le hJ hDJ K.value_bound hne hd)).2
  rw [logRemainder, ← chart_sub a Z Y J] at hb
  have he : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le (by linarith)
  have heu := mul_le_mul_of_nonneg_left he K.upper_nonneg
  have hj := le_abs_self (Real.log J)
  have hr := abs_nonneg (Real.log (R / J))
  unfold exponentBound
  linarith

theorem regularized_far_upper (K : KernelBounds) (a : PlanarSpace) {J R : ℝ}
    (hJ : 0 < J) (hR : 0 < R) (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ))
    {y : Torus} {Z : PlanarSpace} (hsep : R / J ≤ torusEuclideanNorm (chart a J Z - y)) :
    regularizedGreen ε hε (chart a J Z - y) ≤ exponentBound K J R := by
  have hn := far_ne_zero a hJ hR hsep
  have hu := K.upper_bound ε hε hs _ hn
  have hb := (abs_le.mp (K.value_bound _ hn)).2
  have hl := Real.log_le_log (div_pos hR hJ) hsep
  have he : ε ^ 2 ≤ 1 := pow_le_one₀ hε.le (by linarith)
  have heu := mul_le_mul_of_nonneg_left he K.upper_nonneg
  have hr := neg_le_abs (Real.log (R / J))
  have hj := abs_nonneg (Real.log J)
  unfold exponentBound
  linarith

theorem referenceWeight_le_poleProduct (K : KernelBounds) (a : PlanarSpace)
    {β₀ J D R : ℝ} (hJ : 0 < J) (hR : 0 < R) (hDJ : D < J / 2)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (y : κ → Torus) (v : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) (ht : (∑ i, w i) + (∑ i, v i) ≤ β₀)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) {Z : PlanarSpace}
    (hne : ∀ i, Z ≠ Y i) (hd : ∀ i, ‖Z - Y i‖ ≤ D)
    (hsep : ∀ i, R / J ≤ torusEuclideanNorm (chart a J Z - y i)) :
    referenceWeight a J Y w y v ε hε Z ≤ weightConstant K β₀ J R * poleProduct Y w Z := by
  have hn : (∑ i, w i * regularizedGreen ε hε (chart a J Z - chart a J (Y i))) ≤
      ∑ i, w i * (exponentBound K J R - Real.log ‖Z - Y i‖) :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
      (regularized_near_upper K a hJ hDJ ε hε hs (hne i) (hd i)) (hw i)
  have hf : (∑ i, v i * regularizedGreen ε hε (chart a J Z - y i)) ≤
      ∑ i, v i * exponentBound K J R :=
    Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
      (regularized_far_upper K a hJ hR ε hε hs (hsep i)) (hv i)
  have ht' := mul_le_mul_of_nonneg_right ht (exponentBound_nonneg K J R)
  have hexp :
      (∑ i, w i * regularizedGreen ε hε (chart a J Z - chart a J (Y i))) +
        (∑ i, v i * regularizedGreen ε hε (chart a J Z - y i)) ≤
      β₀ * exponentBound K J R + ∑ i, (-w i) * Real.log ‖Z - Y i‖ := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, neg_mul,
      Finset.sum_neg_distrib] at hn hf ⊢
    nlinarith
  have hp : poleProduct Y w Z = Real.exp (∑ i, (-w i) * Real.log ‖Z - Y i‖) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    rw [inverseDistancePower, Real.rpow_def_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hne i)))]
    congr 1
    ring
  rw [referenceWeight_eq, hp, weightConstant, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexp

def referenceSourceGradient (a : PlanarSpace) (J : ℝ) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (y : κ → Torus) (v : κ → ℝ) (ε : ℝ) (hε : 0 < ε) (j : ι ⊕ κ)
    (Z : PlanarSpace) : PlanarSpace :=
  regularizedSourceGradient (splitSources a J Y y) (splitWeights w v) ε hε j (chart a J Z)

theorem continuous_referenceSourceGradient (a : PlanarSpace) (J : ℝ) (Y : ι → PlanarSpace)
    (w : ι → ℝ) (y : κ → Torus) (v : κ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) (j : ι ⊕ κ) :
    Continuous (referenceSourceGradient a J Y w y v ε hε j) :=
  (continuous_regularizedSourceGradient _ _ ε hε hs j).comp (continuous_chart a J)

theorem norm_referenceSourceGradient_near (a : PlanarSpace) (J : ℝ) (Y : ι → PlanarSpace)
    (w : ι → ℝ) (y : κ → Torus) (v : κ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (j : ι) (hw : 0 ≤ w j) (Z : PlanarSpace) :
    ‖referenceSourceGradient a J Y w y v ε hε (.inl j) Z‖ =
      w j * referenceWeight a J Y w y v ε hε Z *
        ‖regularizedGreenGradient ε hε (chart a J Z - chart a J (Y j))‖ := by
  simp only [referenceSourceGradient, regularizedSourceGradient, splitWeights, splitSources,
    Sum.elim_inl, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hw,
    referenceWeight, regularizedTorusWeight, abs_of_pos (Real.exp_pos _)]

theorem norm_referenceSourceGradient_far (a : PlanarSpace) (J : ℝ) (Y : ι → PlanarSpace)
    (w : ι → ℝ) (y : κ → Torus) (v : κ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (j : κ) (hv : 0 ≤ v j) (Z : PlanarSpace) :
    ‖referenceSourceGradient a J Y w y v ε hε (.inr j) Z‖ =
      v j * referenceWeight a J Y w y v ε hε Z *
        ‖regularizedGreenGradient ε hε (chart a J Z - y j)‖ := by
  simp only [referenceSourceGradient, regularizedSourceGradient, splitWeights, splitSources,
    Sum.elim_inr, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hv,
    referenceWeight, regularizedTorusWeight, abs_of_pos (Real.exp_pos _)]

theorem norm_regularized_near_gradient_le (K : KernelBounds) (a : PlanarSpace)
    {J D : ℝ} (hJ : 0 < J) (hDJ : D < J / 2) (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) {Y Z : PlanarSpace} (hne : Z ≠ Y) (hd : ‖Z - Y‖ ≤ D) :
    ‖regularizedGreenGradient ε hε (chart a J Z - chart a J Y)‖ ≤
      (K.gradient * J) * (‖Z - Y‖)⁻¹ := by
  have hb := K.gradient_bound ε hε hs _ (near_ne_zero a hJ hDJ hne hd)
  rw [near_radius a hJ hDJ hd] at hb
  simpa only [div_div_eq_mul_div, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc] using hb

theorem norm_regularized_far_gradient_le (K : KernelBounds) (a : PlanarSpace)
    {J R : ℝ} (hJ : 0 < J) (hR : 0 < R) (ε : ℝ) (hε : 0 < ε)
    (hs : ε ≤ (1 / 16 : ℝ)) {y : Torus} {Z : PlanarSpace}
    (hsep : R / J ≤ torusEuclideanNorm (chart a J Z - y)) :
    ‖regularizedGreenGradient ε hε (chart a J Z - y)‖ ≤ K.gradient * J / R := by
  have hb := K.gradient_bound ε hε hs _ (far_ne_zero a hJ hR hsep)
  calc
    _ ≤ K.gradient / torusEuclideanNorm (chart a J Z - y) := hb
    _ ≤ K.gradient / (R / J) :=
      div_le_div_of_nonneg_left K.gradient_nonneg (div_pos hR hJ) hsep
    _ = K.gradient * J / R := div_div_eq_mul_div _ _ _

theorem referenceWeight_three_halves (K : KernelBounds) {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume) (a : PlanarSpace)
    {β₀ J D R : ℝ} (hJ : 0 < J) (hR : 0 < R) (hDJ : D < J / 2)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (y : κ → Torus) (v : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) (ht : (∑ i, w i) + (∑ i, v i) ≤ β₀)
    (hnear : ∑ i, w i ≤ 1 / 16)
    (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D)
    (hsep : ∀ᵐ Z ∂μ, ∀ i, R / J ≤ torusEuclideanNorm (chart a J Z - y i))
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) :
    MemLp (referenceWeight a J Y w y v ε hε) (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
    lpNorm (referenceWeight a J Y w y v ε hε) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      weightConstant K β₀ J R * normConstant := by
  have hP := poleProduct_three_halves hμ Y w hw (by linarith)
  apply memLp_and_norm_le_of_scalar_bound (weightConstant_pos K β₀ J R).le hP.1 hP.2
    (continuous_referenceWeight a J Y w y v ε hε).measurable.aestronglyMeasurable
  filter_upwards [hd, hsep, ae_avoid_poles hμ.absolutelyContinuous Y] with Z hD hS hne
  have hn : 0 ≤ referenceWeight a J Y w y v ε hε Z := (Real.exp_pos _).le
  rw [Real.norm_of_nonneg hn]
  exact referenceWeight_le_poleProduct K a hJ hR hDJ Y w y v hw hv ht ε hε hs hne hD hS

theorem referenceSourceGradient_near_three_halves (K : KernelBounds) {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume) (a : PlanarSpace)
    {β₀ J D R : ℝ} (hJ : 0 < J) (hR : 0 < R) (hDJ : D < J / 2)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (y : κ → Torus) (v : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) (ht : (∑ i, w i) + (∑ i, v i) ≤ β₀)
    (hnear : ∑ i, w i ≤ 1 / 16)
    (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D)
    (hsep : ∀ᵐ Z ∂μ, ∀ i, R / J ≤ torusEuclideanNorm (chart a J Z - y i))
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (j : ι) :
    MemLp (referenceSourceGradient a J Y w y v ε hε (.inl j))
      (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
    lpNorm (referenceSourceGradient a J Y w y v ε hε (.inl j))
      (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      (w j * weightConstant K β₀ J R * (K.gradient * J)) * normConstant := by
  have hP := inverseDistance_mul_poleProduct_three_halves hμ Y w hw hnear (Y j)
  have hA : 0 ≤ w j * weightConstant K β₀ J R * (K.gradient * J) :=
    mul_nonneg (mul_nonneg (hw j) (weightConstant_pos K β₀ J R).le)
      (mul_nonneg K.gradient_nonneg hJ.le)
  apply memLp_and_norm_le_of_scalar_bound hA hP.1 hP.2
    (continuous_referenceSourceGradient a J Y w y v ε hε hs (.inl j)).measurable.aestronglyMeasurable
  filter_upwards [hd, hsep, ae_avoid_poles hμ.absolutelyContinuous Y] with Z hD hS hne
  rw [norm_referenceSourceGradient_near a J Y w y v ε hε j (hw j) Z]
  have hW := referenceWeight_le_poleProduct K a hJ hR hDJ Y w y v hw hv ht ε hε hs hne hD hS
  have hG := norm_regularized_near_gradient_le K a hJ hDJ ε hε hs (hne j) (hD j)
  calc
    _ ≤ (w j * (weightConstant K β₀ J R * poleProduct Y w Z)) *
        ((K.gradient * J) * (‖Z - Y j‖)⁻¹) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hW (hw j)) hG (norm_nonneg _)
        (mul_nonneg (hw j) (mul_nonneg (weightConstant_pos K β₀ J R).le (poleProduct_nonneg Y w Z)))
    _ = _ := by ring

theorem referenceSourceGradient_far_three_halves (K : KernelBounds) {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume) (a : PlanarSpace)
    {β₀ J D R : ℝ} (hJ : 0 < J) (hR : 0 < R) (hDJ : D < J / 2)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (y : κ → Torus) (v : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) (ht : (∑ i, w i) + (∑ i, v i) ≤ β₀)
    (hnear : ∑ i, w i ≤ 1 / 16)
    (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D)
    (hsep : ∀ᵐ Z ∂μ, ∀ i, R / J ≤ torusEuclideanNorm (chart a J Z - y i))
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (j : κ) :
    MemLp (referenceSourceGradient a J Y w y v ε hε (.inr j))
      (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
    lpNorm (referenceSourceGradient a J Y w y v ε hε (.inr j))
      (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      (v j * weightConstant K β₀ J R * (K.gradient * J / R)) * normConstant := by
  have hP := poleProduct_three_halves hμ Y w hw (by linarith)
  have hA : 0 ≤ v j * weightConstant K β₀ J R * (K.gradient * J / R) :=
    mul_nonneg (mul_nonneg (hv j) (weightConstant_pos K β₀ J R).le)
      (div_nonneg (mul_nonneg K.gradient_nonneg hJ.le) hR.le)
  apply memLp_and_norm_le_of_scalar_bound hA hP.1 hP.2
    (continuous_referenceSourceGradient a J Y w y v ε hε hs (.inr j)).measurable.aestronglyMeasurable
  filter_upwards [hd, hsep, ae_avoid_poles hμ.absolutelyContinuous Y] with Z hD hS hne
  rw [norm_referenceSourceGradient_far a J Y w y v ε hε j (hv j) Z]
  have hW := referenceWeight_le_poleProduct K a hJ hR hDJ Y w y v hw hv ht ε hε hs hne hD hS
  have hG := norm_regularized_far_gradient_le K a hJ hR ε hε hs (hS j)
  calc
    _ ≤ (v j * (weightConstant K β₀ J R * poleProduct Y w Z)) * (K.gradient * J / R) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hW (hv j)) hG (norm_nonneg _)
        (mul_nonneg (hv j) (mul_nonneg (weightConstant_pos K β₀ J R).le (poleProduct_nonneg Y w Z)))
    _ = _ := by ring

/-- A common derivative norm bound for the near and far cases. Its value
vanishes when the total coupling is zero. -/
def sourceNormBound (K : KernelBounds) (β₀ J R : ℝ) : ℝ :=
  (β₀ * weightConstant K β₀ J R * (K.gradient * J) * (1 + R⁻¹)) * normConstant

theorem sourceNormBound_nonneg (K : KernelBounds) {β₀ J R : ℝ}
    (hβ : 0 ≤ β₀) (hJ : 0 ≤ J) (hR : 0 ≤ R) : 0 ≤ sourceNormBound K β₀ J R := by
  unfold sourceNormBound
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg hβ (weightConstant_pos K β₀ J R).le)
      (mul_nonneg K.gradient_nonneg hJ)) (add_nonneg zero_le_one (inv_nonneg.mpr hR)))
    normConstant_nonneg

theorem referenceSourceGradient_three_halves (K : KernelBounds) {μ : Measure PlanarSpace}
    [IsProbabilityMeasure μ] (hμ : μ ≤ volume) (a : PlanarSpace)
    {β₀ J D R : ℝ} (hJ : 0 < J) (hR : 0 < R) (hDJ : D < J / 2)
    (Y : ι → PlanarSpace) (w : ι → ℝ) (y : κ → Torus) (v : κ → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) (ht : (∑ i, w i) + (∑ i, v i) ≤ β₀)
    (hnear : ∑ i, w i ≤ 1 / 16)
    (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D)
    (hsep : ∀ᵐ Z ∂μ, ∀ i, R / J ≤ torusEuclideanNorm (chart a J Z - y i))
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (j : ι ⊕ κ) :
    MemLp (referenceSourceGradient a J Y w y v ε hε j) (ENNReal.ofReal (3 / 2 : ℝ)) μ ∧
    lpNorm (referenceSourceGradient a J Y w y v ε hε j) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤
      sourceNormBound K β₀ J R := by
  have hwn : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ ↦ hw i
  have hvn : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun i _ ↦ hv i
  have hβ : 0 ≤ β₀ := (add_nonneg hwn hvn).trans ht
  have hKg : 0 ≤ K.gradient := K.gradient_nonneg
  have hA : 0 ≤ weightConstant K β₀ J R := (weightConstant_pos K β₀ J R).le
  have hfactor : 0 ≤ β₀ * weightConstant K β₀ J R * (K.gradient * J) :=
    mul_nonneg (mul_nonneg hβ (weightConstant_pos K β₀ J R).le)
      (mul_nonneg K.gradient_nonneg hJ.le)
  cases j with
  | inl j =>
    have h := referenceSourceGradient_near_three_halves K hμ a hJ hR hDJ
      Y w y v hw hv ht hnear hd hsep ε hε hs j
    have hj : w j ≤ β₀ := by
      have hj' := Finset.single_le_sum (fun i _ ↦ hw i) (Finset.mem_univ j)
      linarith
    refine ⟨h.1, h.2.trans ?_⟩
    unfold sourceNormBound
    apply mul_le_mul_of_nonneg_right _ normConstant_nonneg
    calc
      _ ≤ β₀ * weightConstant K β₀ J R * (K.gradient * J) := by
        gcongr
      _ ≤ _ := le_mul_of_one_le_right hfactor (by linarith [inv_pos.mpr hR])
  | inr j =>
    have h := referenceSourceGradient_far_three_halves K hμ a hJ hR hDJ
      Y w y v hw hv ht hnear hd hsep ε hε hs j
    have hj : v j ≤ β₀ := by
      have hj' := Finset.single_le_sum (fun i _ ↦ hv i) (Finset.mem_univ j)
      linarith
    refine ⟨h.1, h.2.trans ?_⟩
    unfold sourceNormBound
    apply mul_le_mul_of_nonneg_right _ normConstant_nonneg
    calc
      _ ≤ β₀ * weightConstant K β₀ J R * (K.gradient * J / R) := by
        gcongr
      _ = (β₀ * weightConstant K β₀ J R * (K.gradient * J)) * R⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith : R⁻¹ ≤ 1 + R⁻¹) hfactor

open MeshCells MeshNearbyGeometry ConditionalParameters LabelOccupations

/-- Geometry is discharged using the actual prescribed source cells. The
domain can be a cell or either orientation of an adjacent-cell union. The
closed-cell hypotheses include wraparound and boundary source positions. -/
theorem reference_mesh_bounds (K : KernelBounds) {J R : ℕ}
    (hJ : 0 < J) (hR : 1 ≤ R) (hmesh : 8 * (R + 4) ≤ J)
    (a : MeshIndex J) (b : Patch) (y : ι → Torus) (labels : ι → MeshIndex J)
    (hy : ∀ i, y i ∈ closure (meshCell J hJ (labels i)))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {β₀ : ℝ} (htotal : ∑ i, w i ≤ β₀)
    (hnear : ∑ i : {i // labels i ∈ nearby J hJ R a b}, w i ≤ 1 / 16)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) :
    MemLp (fun Z ↦ regularizedTorusWeight y w ε hε (meshChart J a Z))
      (ENNReal.ofReal (3 / 2 : ℝ)) (patchReference b) ∧
    lpNorm (fun Z ↦ regularizedTorusWeight y w ε hε (meshChart J a Z))
      (ENNReal.ofReal (3 / 2 : ℝ)) (patchReference b) ≤
      weightConstant K β₀ J R * normConstant ∧
    ∀ j, MemLp (fun Z ↦ regularizedSourceGradient y w ε hε j (meshChart J a Z))
      (ENNReal.ofReal (3 / 2 : ℝ)) (patchReference b) ∧
      lpNorm (fun Z ↦ regularizedSourceGradient y w ε hε j (meshChart J a Z))
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchReference b) ≤ sourceNormBound K β₀ J R := by
  classical
  let P : ι → Prop := fun i ↦ labels i ∈ nearby J hJ R a b
  let Near := {i // P i}
  let Far := {i // ¬P i}
  have hlift (i : Near) : ∃ Y : PlanarSpace, meshChart J a Y = y i ∧
      ∀ Z ∈ patchClosed b, ‖Z - Y‖ ≤ distanceBound R :=
    nearby_lift hJ a (labels i) b i.property (hy i)
  choose Y hY hd using hlift
  let A := meshTranslation J a
  have hj : (0 : ℝ) < J := by exact_mod_cast hJ
  have hr : (0 : ℝ) < R := by exact_mod_cast hR
  have hYi (i : Near) : chart A J (Y i) = y i := by
    simpa only [meshChart_eq_chart, A] using hY i
  have hchart (Z : PlanarSpace) : chart A J Z = meshChart J a Z :=
    (congrFun (meshChart_eq_chart J a) Z).symm
  have ht : (∑ i : Near, w i) + (∑ i : Far, w i) ≤ β₀ := by
    rw [Fintype.sum_subtype_add_sum_subtype P w]
    exact htotal
  have hd' : ∀ᵐ Z ∂patchReference b, ∀ i : Near, ‖Z - Y i‖ ≤ distanceBound R := by
    filter_upwards [ae_mem_patchClosed b] with Z hZ
    exact fun i ↦ hd i Z hZ
  have hsep : ∀ᵐ Z ∂patchReference b, ∀ i : Far,
      (R : ℝ) / J ≤ torusEuclideanNorm (chart A J Z - y i) := by
    filter_upwards [ae_mem_patchClosed b] with Z hZ
    intro i
    rw [hchart]
    exact far_gap hJ a (labels i) b i.property hZ (hy i)
  have hW := referenceWeight_three_halves K (patchReference_le_volume b) A
    hj hr (distanceBound_lt_half hR hmesh) Y (fun i : Near ↦ w i)
    (fun i : Far ↦ y i) (fun i : Far ↦ w i) (fun i ↦ hw i) (fun i ↦ hw i)
    ht hnear hd' hsep ε hε hs
  have he : referenceWeight A J Y (fun i : Near ↦ w i) (fun i : Far ↦ y i)
      (fun i : Far ↦ w i) ε hε =
      (fun Z ↦ regularizedTorusWeight y w ε hε (meshChart J a Z)) := by
    funext Z
    rw [referenceWeight_eq]
    simp only [hYi, hchart, regularizedTorusWeight]
    congr 1
    exact Fintype.sum_subtype_add_sum_subtype P
      (fun i ↦ w i * regularizedGreen ε hε (meshChart J a Z - y i))
  rw [he] at hW
  refine ⟨hW.1, hW.2, fun j ↦ ?_⟩
  by_cases hjnear : P j
  · let jn : Near := ⟨j, hjnear⟩
    have hG := referenceSourceGradient_three_halves K (patchReference_le_volume b) A
      hj hr (distanceBound_lt_half hR hmesh) Y (fun i : Near ↦ w i)
      (fun i : Far ↦ y i) (fun i : Far ↦ w i) (fun i ↦ hw i) (fun i ↦ hw i)
      ht hnear hd' hsep ε hε hs (.inl jn)
    have heG : referenceSourceGradient A J Y (fun i : Near ↦ w i) (fun i : Far ↦ y i)
        (fun i : Far ↦ w i) ε hε (.inl jn) =
        (fun Z ↦ regularizedSourceGradient y w ε hε j (meshChart J a Z)) := by
      funext Z
      change (-w j * referenceWeight A J Y (fun i : Near ↦ w i) (fun i : Far ↦ y i)
        (fun i : Far ↦ w i) ε hε Z) •
        regularizedGreenGradient ε hε (chart A J Z - chart A J (Y jn)) = _
      rw [he, hYi, hchart]
      rfl
    simpa only [heG] using hG
  · let jf : Far := ⟨j, hjnear⟩
    have hG := referenceSourceGradient_three_halves K (patchReference_le_volume b) A
      hj hr (distanceBound_lt_half hR hmesh) Y (fun i : Near ↦ w i)
      (fun i : Far ↦ y i) (fun i : Far ↦ w i) (fun i ↦ hw i) (fun i ↦ hw i)
      ht hnear hd' hsep ε hε hs (.inr jf)
    have heG : referenceSourceGradient A J Y (fun i : Near ↦ w i) (fun i : Far ↦ y i)
        (fun i : Far ↦ w i) ε hε (.inr jf) =
        (fun Z ↦ regularizedSourceGradient y w ε hε j (meshChart J a Z)) := by
      funext Z
      change (-w j * referenceWeight A J Y (fun i : Near ↦ w i) (fun i : Far ↦ y i)
        (fun i : Far ↦ w i) ε hε Z) •
        regularizedGreenGradient ε hε (chart A J Z - y j) = _
      rw [he, hchart]
      rfl
    simpa only [heG] using hG

/-- Actual normalized torus cell/union measures, with their physical source
gradients. The quotient pushforward preserves these finite norms exactly. -/
theorem mesh_bounds (K : KernelBounds) {J R : ℕ}
    (hJ : 0 < J) (hR : 1 ≤ R) (hmesh : 8 * (R + 4) ≤ J)
    (a : MeshIndex J) (b : Patch) (y : ι → Torus) (labels : ι → MeshIndex J)
    (hy : ∀ i, y i ∈ closure (meshCell J hJ (labels i)))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {β₀ : ℝ} (htotal : ∑ i, w i ≤ β₀)
    (hnear : ∑ i : {i // labels i ∈ nearby J hJ R a b}, w i ≤ 1 / 16)
    (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) :
    MemLp (regularizedTorusWeight y w ε hε) (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ∧
    lpNorm (regularizedTorusWeight y w ε hε) (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ≤
      weightConstant K β₀ J R * normConstant ∧
    ∀ j, MemLp (regularizedSourceGradient y w ε hε j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ∧
      lpNorm (regularizedSourceGradient y w ε hε j)
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ≤ sourceNormBound K β₀ J R := by
  have h := reference_mesh_bounds K hJ hR hmesh a b y labels hy w hw htotal hnear ε hε hs
  have hmp := measurePreserving_patch J hJ a b
  have heW := eLpNorm_comp_measurePreserving
    (continuous_regularizedTorusWeight y w ε hε).measurable.aestronglyMeasurable hmp
    (p := ENNReal.ofReal (3 / 2 : ℝ))
  have hWm : MemLp (regularizedTorusWeight y w ε hε)
      (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) := by
    change eLpNorm _ _ _ < (∞ : ℝ≥0∞)
    rw [← heW]
    exact h.1
  have hWb : lpNorm (regularizedTorusWeight y w ε hε)
      (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ≤
      weightConstant K β₀ J R * normConstant := by
    change (eLpNorm _ _ _).toReal ≤ _
    rw [← heW]
    exact h.2.1
  refine ⟨hWm, hWb, fun j ↦ ?_⟩
  have heG := eLpNorm_comp_measurePreserving
    (continuous_regularizedSourceGradient y w ε hε hs j).measurable.aestronglyMeasurable hmp
    (p := ENNReal.ofReal (3 / 2 : ℝ))
  constructor
  · change eLpNorm _ _ _ < (∞ : ℝ≥0∞)
    rw [← heG]
    exact (h.2.2 j).1
  · change (eLpNorm _ _ _).toReal ≤ _
    rw [← heG]
    exact (h.2.2 j).2

/-- The occupation cap yields the exact one-sixteenth nearby total. Every
coefficient is only required to lie between zero and beta/N, so deleting one
(or several) coefficients is included without a separate argument. -/
theorem capped_mesh_bounds (K : KernelBounds) {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : LabelVector J N) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (I : Finset (Fin N)) (X : Configuration N)
    (hX : ∀ i ∈ I, X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) :
    let y : I → Torus := fun i ↦ X i
    let v : I → ℝ := fun i ↦ w i
    MemLp (regularizedTorusWeight y v ε hε) (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ∧
    lpNorm (regularizedTorusWeight y v ε hε) (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ≤
      weightConstant K β₀ J (nearRadius β₀ C₁) * normConstant ∧
    ∀ j, MemLp (regularizedSourceGradient y v ε hε j)
      (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ∧
      lpNorm (regularizedSourceGradient y v ε hε j)
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ≤
        sourceNormBound K β₀ J (nearRadius β₀ C₁) := by
  classical
  have ht : ∑ i : I, w i ≤ β₀ := by
    rw [Finset.sum_coe_sort]
    exact total_source_weight_le hN hβ hβ₀ I hw
  have hn : ∑ i : {i : I // η i ∈ nearby J hJ (nearRadius β₀ C₁) a b}, w i.1 ≤ 1 / 16 := by
    rw [CappedPointWeights.sum_near_eq_sourceWeight]
    exact sourceWeight_fixedDelta_le hN hβ hβ₀ hC₀ hη I _
      (card_nearby_le J hJ (nearRadius β₀ C₁) a b) hw
  exact mesh_bounds K hJ (nearRadius_one_le β₀ C₁) hmesh a b
    (fun i : I ↦ X i) (fun i : I ↦ η i) (fun i ↦ hX i i.2)
    (fun i : I ↦ w i) (fun i ↦ hw₀ i i.2) ht hn ε hε hs

/-- Uniform integrability over an arbitrary family of placements and scales.
The prescribed labels may vary with the placement, as when choosing the
applicable completion of an admissible two-cell source domain. This theorem
requires the actual cap and closed-cell membership for each such labeling. -/
theorem capped_mesh_uniformIntegrable {T : Type*} (K : KernelBounds) {J N : ℕ}
    (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : T → LabelVector J N) (hη : ∀ t, OccupationCap (fixedDelta β₀ C₀ C₁) (η t))
    (I : Finset (Fin N)) (X : T → Configuration N)
    (hX : ∀ t i, i ∈ I → X t i ∈ closure (meshCell J hJ (η t i)))
    (w : T → Fin N → ℝ) (hw₀ : ∀ t i, i ∈ I → 0 ≤ w t i)
    (hw : ∀ t i, i ∈ I → w t i ≤ β / N)
    (a : MeshIndex J) (b : Patch) (ε : T → ℝ) (hε : ∀ t, 0 < ε t)
    (hs : ∀ t, ε t ≤ (1 / 16 : ℝ)) :
    UniformIntegrable (fun t z ↦ regularizedTorusWeight (fun i : I ↦ X t i)
      (fun i : I ↦ w t i) (ε t) (hε t) z) 1 (patchMeasure J hJ a b) ∧
    UniformIntegrable (fun t : T × I ↦ regularizedSourceGradient (fun i : I ↦ X t.1 i)
      (fun i : I ↦ w t.1 i) (ε t.1) (hε t.1) t.2) 1 (patchMeasure J hJ a b) := by
  let := patchMeasure_probability J hJ a b
  have h (t : T) := capped_mesh_bounds K hJ hN hβ hβ₀ hC₀ hmesh (η t) (hη t) I
    (X t) (hX t) (w t) (hw₀ t) (hw t) a b (ε t) (hε t) (hs t)
  constructor
  · exact uniformIntegrable_of_three_halves_bound
      (mul_nonneg (weightConstant_pos K β₀ J (nearRadius β₀ C₁)).le normConstant_nonneg)
      (fun t ↦ (h t).1) (fun t ↦ (h t).2.1)
  · exact uniformIntegrable_of_three_halves_bound
      (sourceNormBound_nonneg K (hβ.trans hβ₀) (by positivity) (by positivity))
      (fun t ↦ ((h t.1).2.2 t.2).1) (fun t ↦ ((h t.1).2.2 t.2).2)

/-- Fubini upgrades uniform fibre moments to an actual joint moment. Joint
measurability is explicit; fibre integrability and its bound are used to
prove joint integrability, not assumed to imply it without argument. -/
theorem joint_three_halves_of_fibre_bounds {A B E : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [NormedAddCommGroup E]
    {σ : Measure A} {μ : Measure B} [IsProbabilityMeasure σ] [IsProbabilityMeasure μ]
    {f : A × B → E} (hf : AEStronglyMeasurable f (σ.prod μ))
    {C : ℝ} (hC : 0 ≤ C)
    (hfm : ∀ᵐ a ∂σ, MemLp (fun z ↦ f (a, z)) (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hfb : ∀ᵐ a ∂σ, lpNorm (fun z ↦ f (a, z)) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ C) :
    MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) (σ.prod μ) ∧
      lpNorm f (ENNReal.ofReal (3 / 2 : ℝ)) (σ.prod μ) ≤ C := by
  let F : A × B → ℝ := fun x ↦ ‖f x‖ ^ (3 / 2 : ℝ)
  have hF : AEStronglyMeasurable F (σ.prod μ) :=
    (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 3 / 2)).comp_aestronglyMeasurable hf.norm
  have hF0 (x : A × B) : 0 ≤ F x := Real.rpow_nonneg (norm_nonneg _) _
  have hFi : ∀ᵐ a ∂σ, Integrable (fun z ↦ F (a, z)) μ := by
    filter_upwards [hfm] with a ha
    have hh := (integrable_norm_rpow_iff ha.aestronglyMeasurable
      (by norm_num : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0) ENNReal.ofReal_ne_top).mpr ha
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using hh
  have hFb : ∀ᵐ a ∂σ, (∫ z, F (a, z) ∂μ) ≤ C ^ (3 / 2 : ℝ) := by
    filter_upwards [hfm, hfb] with a ha hb
    change (∫ z, ‖f (a, z)‖ ^ (3 / 2 : ℝ) ∂μ) ≤ _
    rw [← DensityMoments.lpNorm_rpow_eq_integral (by norm_num : (0 : ℝ) < 3 / 2)
      ha.aestronglyMeasurable]
    exact Real.rpow_le_rpow lpNorm_nonneg hb (by norm_num)
  have hHI : Integrable (fun a ↦ ∫ z, F (a, z) ∂μ) σ := by
    apply (integrable_const (C ^ (3 / 2 : ℝ))).mono' hF.integral_prod_right'
    filter_upwards [hFb] with a ha
    rw [Real.norm_of_nonneg (integral_nonneg fun z ↦ hF0 (a, z))]
    exact ha
  have hFI : Integrable F (σ.prod μ) := by
    apply (integrable_prod_iff hF).mpr
    refine ⟨hFi, ?_⟩
    have he : (fun a ↦ ∫ z, ‖F (a, z)‖ ∂μ) = (fun a ↦ ∫ z, F (a, z) ∂μ) := by
      funext a
      apply integral_congr_ae
      exact ae_of_all _ fun z ↦ Real.norm_of_nonneg (hF0 (a, z))
    rw [he]
    exact hHI
  have hIb : (∫ x, F x ∂σ.prod μ) ≤ C ^ (3 / 2 : ℝ) := by
    rw [integral_prod _ hFI]
    calc
      _ ≤ ∫ _a, C ^ (3 / 2 : ℝ) ∂σ := integral_mono_ae hHI (integrable_const _) hFb
      _ = _ := by simp only [integral_const, probReal_univ, one_smul]
  have hmem : MemLp f (ENNReal.ofReal (3 / 2 : ℝ)) (σ.prod μ) := by
    apply (integrable_norm_rpow_iff hf
      (by norm_num : ENNReal.ofReal (3 / 2 : ℝ) ≠ 0) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3 / 2)] using hFI
  refine ⟨hmem, ?_⟩
  rw [DensityMoments.lpNorm_ofReal_eq (by norm_num : (0 : ℝ) < 3 / 2) hf]
  change (∫ x, F x ∂σ.prod μ) ^ (1 / (3 / 2 : ℝ)) ≤ C
  calc
    _ ≤ (C ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) :=
      Real.rpow_le_rpow (integral_nonneg hF0) hIb (by norm_num)
    _ = C := by rw [← Real.rpow_mul hC]; norm_num

theorem joint_uniformIntegrable_of_fibre_bounds {T A B E : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [NormedAddCommGroup E]
    {σ : Measure A} {μ : Measure B} [IsProbabilityMeasure σ] [IsProbabilityMeasure μ]
    {f : T → A × B → E} (hf : ∀ t, AEStronglyMeasurable (f t) (σ.prod μ))
    {C : ℝ} (hC : 0 ≤ C)
    (hfm : ∀ t, ∀ᵐ a ∂σ, MemLp (fun z ↦ f t (a, z)) (ENNReal.ofReal (3 / 2 : ℝ)) μ)
    (hfb : ∀ t, ∀ᵐ a ∂σ,
      lpNorm (fun z ↦ f t (a, z)) (ENNReal.ofReal (3 / 2 : ℝ)) μ ≤ C) :
    UniformIntegrable f 1 (σ.prod μ) := by
  have h t := joint_three_halves_of_fibre_bounds (hf t) hC (hfm t) (hfb t)
  exact uniformIntegrable_of_three_halves_bound hC (fun t ↦ (h t).1) (fun t ↦ (h t).2)

theorem measurable_joint_weight {A : Type*} [MeasurableSpace A]
    (X : A → ι → Torus) (hX : ∀ i, Measurable (fun a ↦ X a i))
    (w : ι → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Measurable (fun x : A × Torus ↦ regularizedTorusWeight (X x.1) w ε hε x.2) := by
  apply Real.continuous_exp.measurable.comp
  apply Finset.measurable_sum
  intro i hi
  exact ((continuous_regularizedGreen ε hε).measurable.comp
    (measurable_snd.sub ((hX i).comp measurable_fst))).const_mul (w i)

theorem measurable_joint_sourceGradient {A : Type*} [MeasurableSpace A]
    (X : A → ι → Torus) (hX : ∀ i, Measurable (fun a ↦ X a i))
    (w : ι → ℝ) (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ (1 / 16 : ℝ)) (j : ι) :
    Measurable (fun x : A × Torus ↦ regularizedSourceGradient (X x.1) w ε hε j x.2) := by
  exact ((measurable_joint_weight X hX w ε hε).const_mul (-w j)).smul
    ((continuous_regularizedGreenGradient ε hε hs).measurable.comp
      (measurable_snd.sub ((hX j).comp measurable_fst)))

/-- Actual joint uniform integrability for a measurable family of source
placements. The source-parameter law is a probability measure; products of
normalized cell/union laws are allowed. The labeling need not be measurable,
because it is used solely to prove a uniform bound for the actual fields.
The hypotheses impose cap and closed-cell geometry only almost everywhere
under the source-parameter law, and impose no integrability conclusion. -/
theorem capped_joint_uniformIntegrable {T A : Type*} [MeasurableSpace A]
    {σ : Measure A} [IsProbabilityMeasure σ] (K : KernelBounds)
    {J N : ℕ} (hJ : 0 < J) (hN : 0 < N) {β β₀ C₀ C₁ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hC₀ : 0 ≤ C₀)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : A → LabelVector J N)
    (hη : ∀ᵐ x ∂σ, OccupationCap (fixedDelta β₀ C₀ C₁) (η x))
    (I : Finset (Fin N)) (X : A → Configuration N)
    (hXm : ∀ i, Measurable (fun x ↦ X x i))
    (hX : ∀ᵐ x ∂σ, ∀ i ∈ I, X x i ∈ closure (meshCell J hJ (η x i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) (ε : T → ℝ) (hε : ∀ t, 0 < ε t)
    (hs : ∀ t, ε t ≤ (1 / 16 : ℝ)) :
    UniformIntegrable (fun t (x : A × Torus) ↦ regularizedTorusWeight
      (fun i : I ↦ X x.1 i) (fun i : I ↦ w i) (ε t) (hε t) x.2)
      1 (σ.prod (patchMeasure J hJ a b)) ∧
    UniformIntegrable (fun t : T × I ↦ fun x : A × Torus ↦ regularizedSourceGradient
      (fun i : I ↦ X x.1 i) (fun i : I ↦ w i) (ε t.1) (hε t.1) t.2 x.2)
      1 (σ.prod (patchMeasure J hJ a b)) := by
  let := patchMeasure_probability J hJ a b
  let CW := weightConstant K β₀ J (nearRadius β₀ C₁) * normConstant
  let CG := sourceNormBound K β₀ J (nearRadius β₀ C₁)
  have hCW : 0 ≤ CW :=
    mul_nonneg (weightConstant_pos K β₀ J (nearRadius β₀ C₁)).le normConstant_nonneg
  have hCG : 0 ≤ CG := sourceNormBound_nonneg K (hβ.trans hβ₀) (by positivity) (by positivity)
  have hb (t : T) : ∀ᵐ x ∂σ,
      MemLp (regularizedTorusWeight (fun i : I ↦ X x i) (fun i : I ↦ w i) (ε t) (hε t))
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ∧
      lpNorm (regularizedTorusWeight (fun i : I ↦ X x i) (fun i : I ↦ w i) (ε t) (hε t))
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ≤ CW ∧
      ∀ j, MemLp (regularizedSourceGradient (fun i : I ↦ X x i) (fun i : I ↦ w i) (ε t) (hε t) j)
        (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ∧
        lpNorm (regularizedSourceGradient (fun i : I ↦ X x i) (fun i : I ↦ w i) (ε t) (hε t) j)
          (ENNReal.ofReal (3 / 2 : ℝ)) (patchMeasure J hJ a b) ≤ CG := by
    filter_upwards [hη, hX] with x hηx hXx
    exact capped_mesh_bounds K hJ hN hβ hβ₀ hC₀ hmesh (η x) hηx I (X x) hXx w hw₀ hw
      a b (ε t) (hε t) (hs t)
  constructor
  · exact joint_uniformIntegrable_of_fibre_bounds
      (fun t ↦ (measurable_joint_weight (fun x (i : I) ↦ X x i)
        (fun i ↦ hXm i) (fun i : I ↦ w i) (ε t) (hε t)).aestronglyMeasurable)
      hCW (fun t ↦ (hb t).mono fun _ h ↦ h.1) (fun t ↦ (hb t).mono fun _ h ↦ h.2.1)
  · exact joint_uniformIntegrable_of_fibre_bounds
      (fun t ↦ (measurable_joint_sourceGradient (fun x (i : I) ↦ X x i)
        (fun i ↦ hXm i) (fun i : I ↦ w i) (ε t.1) (hε t.1) (hs t.1) t.2).aestronglyMeasurable)
      hCG (fun t ↦ (hb t.1).mono fun _ h ↦ (h.2.2 t.2).1)
      (fun t ↦ (hb t.1).mono fun _ h ↦ (h.2.2 t.2).2)

theorem regularizedTorusWeight_zero (y : ι → Torus) (ε : ℝ) (hε : 0 < ε) (z : Torus) :
    regularizedTorusWeight y (fun _ ↦ 0) ε hε z = 1 := by
  simp [regularizedTorusWeight]

theorem regularizedSourceGradient_eq_zero_of_coefficient_zero (y : ι → Torus) (w : ι → ℝ)
    (ε : ℝ) (hε : 0 < ε) (j : ι) (hj : w j = 0) (z : Torus) :
    regularizedSourceGradient y w ε hε j z = 0 := by
  simp [regularizedSourceGradient, hj]

theorem sourceNormBound_zero (K : KernelBounds) (J R : ℝ) : sourceNormBound K 0 J R = 0 := by
  simp [sourceNormBound]

end PeriodicAttractiveLogGas.MovingPoleIntegrability
