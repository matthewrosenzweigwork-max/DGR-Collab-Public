import DGPS.Examples.RoughBoundary.Model
import DGPS.Foundations.AbsoluteDensity
import DGPS.Foundations.SobolevCalculus
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.SobolevEntropy
import DGPS.Model.Drift

/-!
# Absolute-domain force exists before squaring (RUF031)

For the rough product model `W_{L,ε}(x,y) = κ (1 - U(x)·U(y))`, `κ = 11/6`, `V = 0`, and **every**
absolute-admissible density `ρ = u²` (`u ∈ H¹(𝕋)`, `u ≥ 0`, `∫ u² = 1`):

* `u` and `ρ` are essentially bounded and `ρ` has finite entropy;
* the feature mean `M = ∫ U ρ dm ∈ ℝ²` is defined;
* `W * ρ = κ (1 - U·M)` (the potential of `DGPS.AbsoluteDrift`), with `L^p` weak derivative
  `-κ (M·U')` for every `1 ≤ p < 2`; every weak-drift provider agrees with it a.e.;
* the score `2u' - κ u (M·U')` is an `L^p` function for `1 ≤ p < 2`; it does not depend (a.e.) on
  the chosen weak derivative of `u`, hence its squared extended integral does not depend on
  representatives. Nothing is divided at zeros of `u`.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Examples.RoughBoundary.Nonlinear

open DGPS.Examples.RoughBoundary.Feature DGPS.Examples.RoughBoundary.Model

/-- The feature mean `M(ρ) = ∫ ρ U dm ∈ ℝ²`. -/
noncomputable def featureMean (L ε : ℝ) (ρ : AbsoluteDensity 1) : EuclideanSpace ℝ (Fin 2) :=
  ∫ y, ρ.density y • Ufeat L ε y ∂haar 1

/-- The force `(W*ρ)' = -κ (M·U')` as a vector field on `𝕋¹`. -/
noncomputable def forceVec (L ε : ℝ) (M : EuclideanSpace ℝ (Fin 2)) : Torus 1 → Tangent 1 :=
  fun x => !₂[-(kappa * inner ℝ M (Uprime L ε x))]

/-- The score `2 u' - κ u (M·U')`, built from a given derivative field `g` of `u = √ρ`. -/
noncomputable def forceScore (L ε : ℝ) (ρ : AbsoluteDensity 1) (g : Torus 1 → Tangent 1) :
    Torus 1 → ℝ :=
  fun x => 2 * g x 0 - kappa * ρ.sqrt x * inner ℝ (featureMean L ε ρ) (Uprime L ε x)

lemma integrable_density_smul_Ufeat {L : ℝ} (hL : 0 < L) (ε : ℝ) (ρ : AbsoluteDensity 1) :
    Integrable (fun y => ρ.density y • Ufeat L ε y) (haar 1) := by
  refine ρ.integrable_density.mono'
    (ρ.integrable_density.aestronglyMeasurable.smul (continuous_Ufeat hL ε).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [norm_smul, norm_Ufeat, mul_one, Real.norm_eq_abs, abs_of_nonneg (ρ.density_nonneg y)]

lemma potential_eq {L : ℝ} (hL : 0 < L) (ε : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    interactionPotential (modelData hL ε) ρ x =
      kappa * (1 - inner ℝ (Ufeat L ε x) (featureMean L ε ρ)) := by
  rw [interactionPotential_eq]
  have h1 : (modelData hL ε).V x = 0 := rfl
  have h2 : ∀ y, ρ.density y * (modelData hL ε).W x y =
      kappa * ρ.density y - kappa * inner ℝ (Ufeat L ε x) (ρ.density y • Ufeat L ε y) := by
    intro y
    simp only [modelData, modelW, inner_smul_right]
    ring
  simp_rw [h2]
  rw [h1, zero_add, integral_sub (ρ.integrable_density.const_mul _)
    (((integrable_density_smul_Ufeat hL ε ρ).const_inner (Ufeat L ε x)).const_mul _),
    integral_const_mul, integral_const_mul, ρ.integral_density,
    integral_inner (integrable_density_smul_Ufeat hL ε ρ)]
  unfold featureMean
  ring

lemma continuous_potential {L : ℝ} (hL : 0 < L) (ε : ℝ) (ρ : AbsoluteDensity 1) :
    Continuous (interactionPotential (modelData hL ε) ρ) := by
  have : interactionPotential (modelData hL ε) ρ =
      fun x => kappa * (1 - inner ℝ (Ufeat L ε x) (featureMean L ε ρ)) :=
    funext (potential_eq hL ε ρ)
  rw [this]
  exact continuous_const.mul (continuous_const.sub
    ((continuous_Ufeat hL ε).inner continuous_const))

lemma memLp_Uprime_comp {L : ℝ} (hL : 0 < L) (ε : ℝ) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2)
    (j : Fin 2) : MemLp (fun y => Uprime L ε y j) (ENNReal.ofReal p) (haar 1) := by
  have h := (isWeakGradientLp_Ufeat hL ε hp hp2 j).memLp_grad
  simpa using memLp_coord_of_memLp h 0

lemma kappa_nonneg : 0 ≤ kappa := by unfold kappa; norm_num

/-- `-κ (M·U')` is an `L^p` function. -/
lemma memLp_forceCoeff {L : ℝ} (hL : 0 < L) (ε : ℝ) (M : EuclideanSpace ℝ (Fin 2)) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p < 2) :
    MemLp (fun x => -(kappa * inner ℝ M (Uprime L ε x))) (ENNReal.ofReal p) (haar 1) := by
  have e : (fun x => -(kappa * inner ℝ M (Uprime L ε x))) =
      fun x => (-(kappa * M 0)) * Uprime L ε x 0 + (-(kappa * M 1)) * Uprime L ε x 1 := by
    funext x; rw [inner_two]; ring
  rw [e]
  exact ((memLp_Uprime_comp hL ε hp hp2 0).const_mul _).add
    ((memLp_Uprime_comp hL ε hp hp2 1).const_mul _)

lemma isWeakGradientLp_potential {L : ℝ} (hL : 0 < L) (ε : ℝ) (ρ : AbsoluteDensity 1) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p < 2) :
    IsWeakGradientLp (ENNReal.ofReal p) (interactionPotential (modelData hL ε) ρ)
      (forceVec L ε (featureMean L ε ρ)) := by
  set M := featureMean L ε ρ with hM
  have hc := memLp_forceCoeff hL ε M hp hp2
  have hmeas : Measurable (forceVec L ε M) := by
    unfold forceVec
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun i => ?_)
    fin_cases i
    exact ((measurable_const.inner (measurable_Uprime_vec hL ε)).const_mul _).neg
  refine ⟨?_, ?_, ?_⟩
  · refine MemLp.of_bound (continuous_potential hL ε ρ).aestronglyMeasurable
      (kappa * (1 + ‖M‖)) (Eventually.of_forall fun x => ?_)
    rw [potential_eq, Real.norm_eq_abs, abs_mul, abs_of_nonneg kappa_nonneg]
    refine mul_le_mul_of_nonneg_left ?_ kappa_nonneg
    have := abs_real_inner_le_norm (Ufeat L ε x) M
    rw [norm_Ufeat, one_mul] at this
    calc |1 - inner ℝ (Ufeat L ε x) M| ≤ |1| + |inner ℝ (Ufeat L ε x) M| := abs_sub _ _
      _ ≤ 1 + ‖M‖ := by simpa using this
  · refine MemLp.mono hc hmeas.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    simp [forceVec, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  · intro φ hφ j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have hd := hφ.continuous_coordPartial 0
    have hcφ := hφ.continuous_torus
    have e1 : ∀ x, interactionPotential (modelData hL ε) ρ x * coordPartial 0 φ x =
        kappa * coordPartial 0 φ x - kappa * M 0 * (Ufeat L ε x 0 * coordPartial 0 φ x) -
          kappa * M 1 * (Ufeat L ε x 1 * coordPartial 0 φ x) := by
      intro x; rw [potential_eq, inner_two]; ring
    have e2 : ∀ x, forceVec L ε M x 0 * φ x =
        -(kappa * M 0) * (Uprime L ε x 0 * φ x) + -(kappa * M 1) * (Uprime L ε x 1 * φ x) := by
      intro x; simp only [forceVec]; rw [inner_two]; simp; ring
    simp_rw [e1, e2]
    rw [integral_sub, integral_sub, integral_add, integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_coordPartial_zero' hφ, ibp_comp hL ε 0 hφ, ibp_comp hL ε 1 hφ]
    · ring
    · exact (integrable_Uprime_mul hL ε 0 hcφ).const_mul _
    · exact (integrable_Uprime_mul hL ε 1 hcφ).const_mul _
    · exact (integrable_cont hd).const_mul _
    · exact (integrable_Ufeat_mul hL ε 0 hd).const_mul _
    · exact ((integrable_cont hd).const_mul _).sub ((integrable_Ufeat_mul hL ε 0 hd).const_mul _)
    · exact (integrable_Ufeat_mul hL ε 1 hd).const_mul _

lemma isWeakGradientLp_one_of {u : Torus 1 → ℝ} {g : Torus 1 → Tangent 1}
    (h : IsWeakGradient u g) : IsWeakGradientLp 1 u g :=
  ⟨h.memLp.mono_exponent one_le_two, h.memLp_grad.mono_exponent one_le_two, h.ibp⟩

lemma forceScore_ae_eq (L ε : ℝ) (ρ : AbsoluteDensity 1) {g g' : Torus 1 → Tangent 1}
    (hg : IsWeakGradient ρ.sqrt g) (hg' : IsWeakGradient ρ.sqrt g') :
    forceScore L ε ρ g =ᵐ[haar 1] forceScore L ε ρ g' := by
  have h := (isWeakGradientLp_one_of hg).ae_eq_of_one (isWeakGradientLp_one_of hg')
  filter_upwards [h] with x hx
  simp only [forceScore, hx]

lemma memLp_forceScore {L : ℝ} (hL : 0 < L) (ε : ℝ) (ρ : AbsoluteDensity 1)
    {g : Torus 1 → Tangent 1} (hg : IsWeakGradient ρ.sqrt g) {p : ℝ} (hp : 1 ≤ p) (hp2 : p < 2) :
    MemLp (forceScore L ε ρ g) (ENNReal.ofReal p) (haar 1) := by
  have hc := memLp_forceCoeff hL ε (featureMean L ε ρ) hp hp2
  obtain ⟨B, hB0, hB⟩ := exists_ae_bound_one hg
  have h1 : MemLp (fun x => g x 0) (ENNReal.ofReal p) (haar 1) :=
    (memLp_coord_of_memLp hg.memLp_grad 0).mono_exponent
      (by simpa using (ENNReal.ofReal_le_ofReal hp2.le : ENNReal.ofReal p ≤ ENNReal.ofReal 2))
  have h2 : MemLp (fun x => ρ.sqrt x * -(kappa * inner ℝ (featureMean L ε ρ) (Uprime L ε x)))
      (ENNReal.ofReal p) (haar 1) := by
    refine MemLp.mono (hc.const_mul B)
      (hg.memLp.aestronglyMeasurable.mul hc.aestronglyMeasurable)
      ?_
    filter_upwards [hB] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hB0]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have e : forceScore L ε ρ g = fun x => 2 * g x 0 +
      ρ.sqrt x * -(kappa * inner ℝ (featureMean L ε ρ) (Uprime L ε x)) := by
    funext x; simp only [forceScore]; ring
  rw [e]
  exact (h1.const_mul 2).add h2

/-- **Absolute-domain force exists before squaring** (RUF031). -/
theorem absolute_domain_force_exists_before_squaring {L : ℝ} (hL : 0 < L) (ε : ℝ)
    (ρ : AbsoluteDensity 1) :
    (∃ B : ℝ, 0 ≤ B ∧ (∀ᵐ x ∂haar 1, |ρ.sqrt x| ≤ B) ∧ (∀ᵐ x ∂haar 1, ρ.density x ≤ B ^ 2)) ∧
    (Integrable (fun x => ρ.density x * Real.log (ρ.density x)) (haar 1) ∧
      relativeEntropy (densityMeasure ρ) (haar 1) ≠ ⊤) ∧
    Integrable (fun y => ρ.density y • Ufeat L ε y) (haar 1) ∧
    (∀ x, interactionPotential (modelData hL ε) ρ x =
      kappa * (1 - inner ℝ (Ufeat L ε x) (featureMean L ε ρ))) ∧
    (∀ p : ℝ, 1 ≤ p → p < 2 →
      IsWeakGradientLp (ENNReal.ofReal p) (interactionPotential (modelData hL ε) ρ)
        (forceVec L ε (featureMean L ε ρ)) ∧
      MemLp (forceScore L ε ρ (weakGradient ρ.sqrt ρ.sqrt_mem)) (ENNReal.ofReal p) (haar 1)) ∧
    (∀ b : AbsoluteDrift (modelData hL ε),
      b.force ρ =ᵐ[haar 1] forceVec L ε (featureMean L ε ρ) ∧
      forceScore L ε ρ (weakGradient ρ.sqrt ρ.sqrt_mem) =ᵐ[haar 1]
        fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 + ρ.sqrt x * b.force ρ x 0) ∧
    (∀ g : Torus 1 → Tangent 1, IsWeakGradient ρ.sqrt g →
      forceScore L ε ρ g =ᵐ[haar 1] forceScore L ε ρ (weakGradient ρ.sqrt ρ.sqrt_mem) ∧
      ∫⁻ x, ‖forceScore L ε ρ g x‖ₑ ^ 2 ∂haar 1 =
        ∫⁻ x, ‖forceScore L ε ρ (weakGradient ρ.sqrt ρ.sqrt_mem) x‖ₑ ^ 2 ∂haar 1) := by
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  refine ⟨?_, ⟨(absoluteDensity_entropy_finite ρ).1, (absoluteDensity_entropy_finite ρ).2.2.1⟩,
    integrable_density_smul_Ufeat hL ε ρ, potential_eq hL ε ρ,
    fun p hp hp2 => ⟨isWeakGradientLp_potential hL ε ρ hp hp2, memLp_forceScore hL ε ρ hw hp hp2⟩,
    fun b => ?_, fun g hg => ?_⟩
  · obtain ⟨B, hB0, hB⟩ := exists_ae_bound_one hw
    refine ⟨B, hB0, hB, ?_⟩
    filter_upwards [hB] with x hx
    have : ρ.sqrt x ^ 2 ≤ B ^ 2 := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
    exact this
  · have h1 := isWeakGradientLp_potential hL ε ρ (p := 1) le_rfl one_lt_two
    rw [ENNReal.ofReal_one] at h1
    have hF := b.ae_eq_of_isWeakGradient ρ h1
    refine ⟨hF, ?_⟩
    filter_upwards [hF] with x hx
    simp only [forceScore, hx, forceVec]
    simp
    ring
  · exact ⟨forceScore_ae_eq L ε ρ hg hw, lintegral_congr_ae
      ((forceScore_ae_eq L ε ρ hg hw).mono fun x hx => congrArg (fun r : ℝ => ‖r‖ₑ ^ 2) hx)⟩

end DGPS.Examples.RoughBoundary.Nonlinear
