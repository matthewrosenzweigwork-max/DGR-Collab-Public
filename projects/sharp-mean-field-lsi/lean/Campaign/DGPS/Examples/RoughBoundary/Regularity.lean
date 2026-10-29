import DGPS.Examples.RoughBoundary.FeatureMoments
import DGPS.Examples.RoughBoundary.FeatureRough
import DGPS.Examples.RoughBoundary.Model
import DGPS.Lipschitz.Representatives
import DGPS.Model.Drift

/-!
# Bulk obstruction to the interaction `H¹` regularity (RUF009)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 1.6.

For `L > 0`, `ε ≠ 0` and a nonempty open `J ⊂ ℝ`, the `x`-derivative of the product interaction
`W_{L,ε}(x,y) = κ (1 - U(x)·U(y))` satisfies
`∫_J ∫_T |∂ₓW(x,y)|² dm(y) dx = ∞`; hence `W ∉ H¹(𝕋²)`, and in particular `W` is not Lipschitz.

The `x`-derivative is the explicit formal derivative `-κ U'(x)·U(y)` (`gradW`, RUF008), which is
the unique `W^{1,1}` weak derivative, so no alternative `L²` weak derivative exists.
-/

open MeasureTheory Set Filter
open scoped Real ENNReal

namespace DGPS.Examples.RoughBoundary.Regularity

open DGPS.Examples.RoughBoundary.Feature
open DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Spikes (pt measurable_pt)
open DGPS.Analysis.RateTopology (q1 q2 pairPt)

lemma enorm_sq_eq (r : ℝ) : ‖r‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg r), Real.norm_eq_abs, sq_abs]

/-- Exact covariance: `∫ ⟨a, U(y)⟩² dm(y) = |a|²/2`. -/
lemma integral_inner_Ufeat_sq {L : ℝ} (hL : 0 < L) (ε : ℝ) (a : EuclideanSpace ℝ (Fin 2)) :
    ∫ y, (inner ℝ a (Ufeat L ε y)) ^ 2 ∂haar 1 = ‖a‖ ^ 2 / 2 := by
  have hm := (exact_shift_symmetries_and_feature_moments hL ε).1.2.2.2
  have hint : ∀ i j : Fin 2, Integrable (fun y => Ufeat L ε y i * Ufeat L ε y j) (haar 1) :=
    fun i j => integrable_cont ((continuous_Ufeat_comp hL ε i).mul (continuous_Ufeat_comp hL ε j))
  have e : ∀ y, (inner ℝ a (Ufeat L ε y)) ^ 2 =
      a 0 ^ 2 * (Ufeat L ε y 0 * Ufeat L ε y 0) + 2 * (a 0 * a 1) * (Ufeat L ε y 0 * Ufeat L ε y 1)
        + a 1 ^ 2 * (Ufeat L ε y 1 * Ufeat L ε y 1) := fun y => by
    rw [inner_two]; ring
  simp_rw [e]
  rw [integral_add (f := fun y => a 0 ^ 2 * (Ufeat L ε y 0 * Ufeat L ε y 0) +
      2 * (a 0 * a 1) * (Ufeat L ε y 0 * Ufeat L ε y 1))
      (g := fun y => a 1 ^ 2 * (Ufeat L ε y 1 * Ufeat L ε y 1))
      (((hint 0 0).const_mul _).add ((hint 0 1).const_mul _)) ((hint 1 1).const_mul _),
    integral_add (f := fun y => a 0 ^ 2 * (Ufeat L ε y 0 * Ufeat L ε y 0))
      (g := fun y => 2 * (a 0 * a 1) * (Ufeat L ε y 0 * Ufeat L ε y 1))
      ((hint 0 0).const_mul _) ((hint 0 1).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul, hm 0 0, hm 0 1, hm 1 1,
    EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp
  ring

/-- Step 1 (exact covariance): for every `x`, `∫ |∂ₓW(x,y)|² dm(y) = (κ²/2) |U'(x)|²`. -/
lemma lintegral_y {L : ℝ} (hL : 0 < L) (ε : ℝ) (x : Torus 1) :
    ∫⁻ y, ‖gradW L ε (pairPt x y) 0‖ₑ ^ 2 ∂haar 1 =
      ENNReal.ofReal (kappa ^ 2 / 2 * ‖Uprime L ε x‖ ^ 2) := by
  have h : ∀ y, ‖gradW L ε (pairPt x y) 0‖ₑ ^ 2 =
      ENNReal.ofReal (kappa ^ 2 * (inner ℝ (Uprime L ε x) (Ufeat L ε y)) ^ 2) := fun y => by
    rw [enorm_sq_eq, gradW_pairPt]
    simp only [gradPair]
    simp
    ring_nf
  simp_rw [h]
  have hc : Continuous fun y => kappa ^ 2 * (inner ℝ (Uprime L ε x) (Ufeat L ε y)) ^ 2 :=
    continuous_const.mul ((continuous_const.inner (continuous_Ufeat hL ε)).pow 2)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_cont hc)
    (Eventually.of_forall fun y => by positivity), integral_const_mul,
    integral_inner_Ufeat_sq hL ε]
  congr 1
  ring

/-- The phase derivative is not square integrable on a nonempty open set (RUF007). -/
lemma lintegral_dtheta_top {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0) {J : Set ℝ}
    (hJ : IsOpen J) (hne : J.Nonempty) :
    ∫⁻ t in J, ‖dtheta L ε t‖ₑ ^ 2 = ∞ := by
  by_contra hfin
  have h0 := (every_nonzero_direction_is_rough hL hε hJ hne
    (a := EuclideanSpace.single 0 1) (by
      intro h
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
      simp at this)).1
  refine h0 ?_
  rw [MemLp, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)]
  · simpa using lt_top_iff_ne_top.2 hfin
  · exact (measurable_dtheta L ε).aestronglyMeasurable

lemma lintegral_Uprime_top {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0) {J : Set ℝ}
    (hJ : IsOpen J) (hne : J.Nonempty) :
    ∫⁻ t in J, ENNReal.ofReal (kappa ^ 2 / 2 * ‖Uprime L ε (pt t)‖ ^ 2) = ∞ := by
  have e : ∀ t, ENNReal.ofReal (kappa ^ 2 / 2 * ‖Uprime L ε (pt t)‖ ^ 2) =
      ENNReal.ofReal (kappa ^ 2 / 2 * (2 * π) ^ 2) * ‖dtheta L ε t‖ₑ ^ 2 := fun t => by
    rw [enorm_sq_eq, ← ENNReal.ofReal_mul (by positivity), norm_Uprime, dthetaT_pt, mul_pow,
      sq_abs]
    congr 1
    ring
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_dtheta_top hL hε hJ hne]
  have : ENNReal.ofReal (kappa ^ 2 / 2 * (2 * π) ^ 2) ≠ 0 := by
    have : 0 < kappa ^ 2 / 2 * (2 * π) ^ 2 := by unfold kappa; positivity
    simpa using this
  simp [this]

/-- Bulk obstruction on the whole torus: the `L²(𝕋)` mass of `U'` is infinite. -/
lemma lintegral_Uprime_torus_top {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (kappa ^ 2 / 2 * ‖Uprime L ε x‖ ^ 2) ∂haar 1 = ∞ := by
  have hJ : IsOpen (Ioo (0 : ℝ) 1) := isOpen_Ioo
  have h := lintegral_Uprime_top hL hε hJ ⟨1 / 2, by norm_num, by norm_num⟩
  have hmeas : Measurable fun x : Torus 1 => ENNReal.ofReal (kappa ^ 2 / 2 * ‖Uprime L ε x‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_const.mul ((measurable_Uprime_vec hL ε).norm.pow_const 2)))
  rw [← DGPS.Examples.RoughBoundary.Spikes.nl_lintegral_pt (a := 0) (b := 1) (by norm_num) _
    hmeas] at h
  exact top_unique (h ▸ setLIntegral_le_lintegral _ _)

/-- A Mathlib-Lipschitz function on the torus is `TorusLipschitzWith`. -/
lemma torusLipschitz_of_lipschitzWith {d : ℕ} {f : Torus d → ℝ} {K : NNReal}
    (h : LipschitzWith K f) : TorusLipschitzWith (K : ℝ) f := fun x y => by
  have h1 := h.dist_le_mul x y
  rw [Real.dist_eq] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (torusDist_comparison x y).1 K.2)

/-- **Bulk obstruction to interaction `H¹`** (RUF009). -/
theorem bulk_obstruction_to_interaction_h1 {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    {J : Set ℝ} (hJ : IsOpen J) (hne : J.Nonempty) :
    (∀ x : Torus 1, ∫⁻ y, ‖gradW L ε (pairPt x y) 0‖ₑ ^ 2 ∂haar 1 =
      ENNReal.ofReal (kappa ^ 2 / 2 * ‖Uprime L ε x‖ ^ 2)) ∧
    ∫⁻ t in J, ∫⁻ y, ‖gradW L ε (pairPt (pt t) y) 0‖ₑ ^ 2 ∂haar 1 = ∞ ∧
    (∀ g : Torus 2 → Tangent 2, IsWeakGradientLp 1 (Wtor L ε) g → g =ᵐ[haar 2] gradW L ε) ∧
    (∀ g : Torus 2 → Tangent 2, IsWeakGradientLp 1 (Wtor L ε) g →
      ∫⁻ p, ‖g p 0‖ₑ ^ 2 ∂haar 2 = ∞) ∧
    ¬ MemH1 (Wtor L ε) ∧
    ∀ K : NNReal, ¬ LipschitzWith K (Wtor L ε) := by
  have hw1 : IsWeakGradientLp 1 (Wtor L ε) (gradW L ε) := by
    simpa using isWeakGradientLp_Wtor hL ε (p := 1) le_rfl one_lt_two
  have huniq : ∀ g : Torus 2 → Tangent 2, IsWeakGradientLp 1 (Wtor L ε) g →
      g =ᵐ[haar 2] gradW L ε := fun g hg => hg.ae_eq_of_one hw1
  -- the total mass of `|∂ₓW|²` on the torus
  have htot : ∫⁻ p, ‖gradW L ε p 0‖ₑ ^ 2 ∂haar 2 = ∞ := by
    have hmeas : Measurable fun z : Torus 1 × Torus 1 => ‖gradPair L ε z.1 z.2 0‖ₑ ^ 2 :=
      (((EuclideanSpace.proj (0 : Fin 2) : Tangent 2 →L[ℝ] ℝ).measurable.comp
        (measurable_gradPair hL ε)).enorm).pow_const 2
    have h1 := (DGPS.Analysis.RateTopology.measurePreserving_q).lintegral_comp hmeas
    have h2 : ∀ p : Torus 2, ‖gradPair L ε (q1 p) (q2 p) 0‖ₑ ^ 2 = ‖gradW L ε p 0‖ₑ ^ 2 :=
      fun p => rfl
    simp only [h2] at h1
    rw [h1, lintegral_prod _ hmeas.aemeasurable]
    have h3 : ∀ x, ∫⁻ y, ‖gradPair L ε x y 0‖ₑ ^ 2 ∂haar 1 =
        ENNReal.ofReal (kappa ^ 2 / 2 * ‖Uprime L ε x‖ ^ 2) := fun x => by
      have := lintegral_y hL ε x
      simpa [gradW_pairPt] using this
    simp_rw [h3]
    exact lintegral_Uprime_torus_top hL hε
  have hL2 : ∀ g : Torus 2 → Tangent 2, IsWeakGradientLp 1 (Wtor L ε) g →
      ∫⁻ p, ‖g p 0‖ₑ ^ 2 ∂haar 2 = ∞ := fun g hg => by
    rw [← htot]
    refine lintegral_congr_ae ?_
    filter_upwards [huniq g hg] with p hp
    rw [hp]
  have hnotH1 : ¬ MemH1 (Wtor L ε) := by
    rintro ⟨g, hg⟩
    have hg1 : IsWeakGradientLp 1 (Wtor L ε) g :=
      ⟨hg.memLp.mono_exponent (by simp), hg.memLp_grad.mono_exponent (by simp), hg.ibp⟩
    have hc := memLp_coord_of_memLp hg.memLp_grad 0
    have := hc.eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by simp)
      (hc.aestronglyMeasurable)] at this
    have h2 := hL2 g hg1
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat] at this
    rw [h2] at this
    exact lt_irrefl _ this
  refine ⟨lintegral_y hL ε, ?_, huniq, hL2, hnotH1, fun K hK => ?_⟩
  · simp_rw [lintegral_y hL ε]
    exact lintegral_Uprime_top hL hε hJ hne
  · obtain ⟨hg', -⟩ := Lipschitz.exists_weak_gradient K.2 (torusLipschitz_of_lipschitzWith hK)
    exact hnotH1 ⟨_, isWeakGradient_iff_isWeakGradientLp.mpr
      ⟨hg'.memLp.mono_exponent (by simp), hg'.memLp_grad.mono_exponent (by simp), hg'.ibp⟩⟩

end DGPS.Examples.RoughBoundary.Regularity
