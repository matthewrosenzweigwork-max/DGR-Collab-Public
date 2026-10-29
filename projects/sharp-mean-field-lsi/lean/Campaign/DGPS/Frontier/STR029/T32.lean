import DGPS.Frontier.STR029.T26
import DGPS.Variational.FrozenGibbs
import DGPS.Foundations.WeakContractions

/-!
# STR029.32: all zero-deficit roots

## Provides

* `str029_32_zero_deficit_roots_of_data`: for any supplied exhaustive triple of
  positive-entropy global optimizers, the zero-deficit measures are exactly the
  reference and the measures of those three densities.
* `str029_32_zero_deficit_roots`: the unconditional small-positive-field conclusion,
  with the same three witnesses as STR029.26.

## R5 notes

The specification is informal; the statements below use exactly the absolute domain
and the finite-information zero-deficit convention of STR029.01. The optimal rate
is the infimum of the physical quotient over every positive-entropy absolute
competitor. `quot_eq_inf_STR02932` identifies each optimizing branch's quotient
with this infimum; the rate is independent of the branch. `ordinaryFisher` already
contains the physical factor `DGPS.Circle.AngularNormalization.a0`, as proved in
STR029.01 and retained in STR029.26. No angular quotient is substituted here.

The canonical `ordinaryLSRate` is defined using signed, unnormalized weighted
Sobolev functions. `ordinaryLSRate_eq_abs_inf_STR02932` proves exact agreement with
the packet domain: normalize `|f|` by its weighted square mass and use the Sobolev
absolute-value contraction. Thus the final classification uses the canonical rate. All measures, including singular measures and measures outside the
finite-information domain, are quantified over in the zero-set equivalence.
Finite information and finite entropy are supplied by STR029.01, before any
real-valued subtraction. Equality of densities is almost everywhere with respect
to Haar; equality of their induced probability measures is literal equality.
-/

open MeasureTheory
open scoped ENNReal
open DGPS DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Frontier.STR029

/-- Homogeneity of the entropy used in the signed-test normalization. The calculation
is the generic normalization argument in `EngineeredRankOneRates.homogeneousEntropy_scale`. -/
theorem homogeneousEntropy_scale_STR02932 {α : Type*} [MeasurableSpace α]
    (P : Measure α) (v : α → ℝ) {k : ℝ} (hk : 0 < k) :
    homogeneousEntropy P (fun x => k * v x) =
      ENNReal.ofReal k * homogeneousEntropy P v := by
  by_cases h0 : ∫ x, v x ∂P = 0
  · rw [homogeneousEntropy_of_integral_eq_zero h0, mul_zero,
      homogeneousEntropy_of_integral_eq_zero (by rw [integral_const_mul, h0, mul_zero])]
  · have h1 : ∫ x, k * v x ∂P ≠ 0 := by
      rw [integral_const_mul]
      exact mul_ne_zero hk.ne' h0
    rw [homogeneousEntropy_of_integral_ne_zero h1,
      homogeneousEntropy_of_integral_ne_zero h0, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    rw [integral_const_mul]
    have he : entropyIntegrand (k * ∫ x, v x ∂P) (k * v x) =
        k * entropyIntegrand (∫ x, v x ∂P) (v x) := by
      unfold entropyIntegrand
      rw [show k * v x / (k * ∫ x, v x ∂P) = v x / ∫ x, v x ∂P by field_simp]
      ring
    rw [he, ENNReal.ofReal_mul hk.le]

/-- Every signed weighted Sobolev test of positive entropy yields a normalized
absolute density with no larger information/entropy quotient. The argument is the
normalization and absolute-value contraction used in
`EngineeredRankOneRates.quotient_le`, applied directly to the packet reference. -/
theorem signed_test_to_abs_STR02932 (h : ℝ) {f : Torus 1 → ℝ}
    (hmem : f ∈ WeightedH1 (ordinaryReference h))
    (hpos : 0 < homogeneousEntropy (ordinaryReference h).measure (fun x => f x ^ 2)) :
    ∃ ρ : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ ∧
      str025_quot h ρ ≤
        2 * (∫⁻ x, ‖weightedGradient (ordinaryReference h) f hmem x‖ₑ ^ 2
          ∂(ordinaryReference h).measure) /
          homogeneousEntropy (ordinaryReference h).measure (fun x => f x ^ 2) := by
  let P := ordinaryReference h
  let g := weightedGradient P f hmem
  have hg : IsWeakGradient f g :=
    (isWeightedWeakGradient_iff P).1 (isWeightedWeakGradient_weightedGradient P hmem)
  let ga : Torus 1 → Tangent 1 :=
    fun x => if 0 < f x then g x else if f x < 0 then -g x else 0
  have hga : IsWeakGradient (fun x => |f x|) ga := hg.abs
  have hganorm : ∀ x, ‖ga x‖ₑ ^ 2 ≤ ‖g x‖ₑ ^ 2 := by
    intro x
    dsimp [ga]
    split_ifs <;> simp
  let Z := ∫ x, f x ^ 2 ∂P.measure
  have hZne : Z ≠ 0 := by
    intro hZ
    have he := homogeneousEntropy_of_integral_eq_zero hZ
    exact hpos.ne' he
  have hZpos : 0 < Z :=
    lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) (Ne.symm hZne)
  let c := Real.sqrt (1 / Z)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hc2 : c ^ 2 = 1 / Z := Real.sq_sqrt (by positivity)
  have hc2pos : 0 < c ^ 2 := by rw [hc2]; positivity
  have hca : IsWeakGradient (fun x => c * |f x|) (fun x => c • ga x) := hga.smul c
  let S := fun x => P.density x ^ (1 / 2 : ℝ) * (c * |f x|)
  have hSmem : MemH1 S :=
    (RelativeFisher.memWeightedH1_iff_memH1_mul_sqrt (ordinaryReference_lip h)).1
      ((mem_weightedH1_iff P).2 ⟨_, hca⟩)
  have hSq : ∀ x, S x ^ 2 = c ^ 2 * (referenceDensity h x * f x ^ 2) := by
    intro x
    change (referenceDensity h x ^ (1 / 2 : ℝ) * (c * |f x|)) ^ 2 = _
    rw [← Real.sqrt_eq_rpow, mul_pow, mul_pow, sq_abs,
      Real.sq_sqrt (referenceDensity_pos (h := h) x).le]
    ring
  have hmass : ∫ x, S x ^ 2 ∂haar 1 = 1 := by
    simp_rw [hSq]
    rw [integral_const_mul, ← integral_threefoldReference]
    change c ^ 2 * Z = 1
    rw [hc2]
    field_simp
  let ρ : AbsoluteDensity 1 := {
    sqrt := S
    sqrt_mem := hSmem
    sqrt_nonneg := Filter.Eventually.of_forall fun x =>
      mul_nonneg (Real.rpow_nonneg (referenceDensity_pos (h := h) x).le _) (mul_nonneg hc (abs_nonneg _))
    mass_one := hmass }
  have hU : str025_u h ρ = fun x => c * |f x| := by
    funext x
    rw [str025_u_eq]
    change referenceDensity h x ^ (1 / 2 : ℝ) * (c * |f x|) /
      Real.sqrt (referenceDensity h x) = _
    rw [← Real.sqrt_eq_rpow]
    field_simp [(Real.sqrt_pos.2 (referenceDensity_pos (h := h) x)).ne']
  have hfm : AEMeasurable f (haar 1) := hg.memLp.aestronglyMeasurable.aemeasurable
  have hmeas : (densityMeasure ρ : Measure (Torus 1)) =
      P.measure.withDensity (fun x => ENNReal.ofReal (c ^ 2 * f x ^ 2)) := by
    have hmul := withDensity_mul₀ (μ := haar 1)
      (f := fun x => ENNReal.ofReal (P.density x))
      (g := fun x => ENNReal.ofReal (c ^ 2 * f x ^ 2))
      P.measurable_ofReal_density.aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable ((hfm.pow_const 2).const_mul (c ^ 2)))
    rw [densityMeasure_coe, BoundedPositiveReference.measure, ← hmul]
    congr 1
    funext x
    change ENNReal.ofReal (S x ^ 2) =
      ENNReal.ofReal (referenceDensity h x) * ENNReal.ofReal (c ^ 2 * f x ^ 2)
    rw [← ENNReal.ofReal_mul (referenceDensity_pos (h := h) x).le, hSq]
    congr 1
    ring
  let Ent := homogeneousEntropy P.measure (fun x => f x ^ 2)
  let k := ENNReal.ofReal (c ^ 2)
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.2 hc2pos).ne'
  have hH : ordinaryEntropy h ρ = k * Ent := by
    change relativeEntropy (densityMeasure ρ : Measure (Torus 1)) P.measure = _
    rw [hmeas, relativeEntropy_withDensity
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (((hfm.pow_const 2).const_mul (c ^ 2)).mono_ac P.measure_ac_haar)]
    exact homogeneousEntropy_scale_STR02932 P.measure (fun x => f x ^ 2) hc2pos
  have hHpos : 0 < ordinaryEntropy h ρ := by
    rw [hH]
    exact ENNReal.mul_pos hk0 hpos.ne'
  let E := ∫⁻ x, ‖g x‖ₑ ^ 2 ∂P.measure
  have hgrad : str025_grad h ρ =ᵐ[haar 1] fun x => c • ga x := by
    have hca' : IsWeakGradient (str025_u h ρ) (fun x => c • ga x) := by
      rw [hU]
      exact hca
    exact (str025_isWeak h ρ).ae_eq hca'
  have hF : ordinaryFisher h ρ ≤ 4 * (k * E) := by
    rw [str025_fisher_eq]
    change 4 * (∫⁻ x, ‖str025_grad h ρ x‖ₑ ^ 2 ∂P.measure) ≤ _
    apply mul_le_mul_right
    calc (∫⁻ x, ‖str025_grad h ρ x‖ₑ ^ 2 ∂P.measure)
        = ∫⁻ x, ‖c • ga x‖ₑ ^ 2 ∂P.measure := by
          refine lintegral_congr_ae ?_
          filter_upwards [P.measure_ac_haar.ae_le hgrad] with x hx
          rw [hx]
      _ ≤ ∫⁻ x, k * ‖g x‖ₑ ^ 2 ∂P.measure := by
          apply lintegral_mono
          intro x
          change ‖c • ga x‖ₑ ^ 2 ≤ k * ‖g x‖ₑ ^ 2
          rw [enorm_smul, mul_pow, Real.enorm_eq_ofReal_abs, abs_of_nonneg hc,
            ← ENNReal.ofReal_pow hc]
          exact mul_le_mul_right (hganorm x) k
      _ = k * E := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  refine ⟨ρ, hHpos, ?_⟩
  unfold str025_quot
  rw [hH]
  calc ordinaryFisher h ρ / (2 * (k * Ent)) ≤ (4 * (k * E)) / (2 * (k * Ent)) :=
        ENNReal.div_le_div_right hF _
    _ = ((2 * k) * (2 * E)) / ((2 * k) * Ent) := by congr 1 <;> ring
    _ = 2 * E / Ent := ENNReal.mul_div_mul_left _ _ (mul_ne_zero (by norm_num) hk0)
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)

/-- The canonical ordinary LSI rate is exactly the infimum on the full absolute
variational domain of STR029.01. Both infima use physical Fisher information. -/
theorem ordinaryLSRate_eq_abs_inf_STR02932 (h : ℝ) :
    DGPS.ordinaryLSRate (ordinaryReference h) =
      ⨅ σ : {σ : AbsoluteDensity 1 // 0 < ordinaryEntropy h σ}, str025_quot h σ.1 := by
  apply le_antisymm
  · refine le_iInf fun ⟨ρ, hpos⟩ => ?_
    let P := ordinaryReference h
    let ν : Measure (Torus 1) := densityMeasure ρ
    have hac : ν ≪ P.measure :=
      (withDensity_absolutelyContinuous _ _).trans P.haar_ac_measure
    have hmem : relativeSqrt ν P ∈ WeightedH1 P := by
      by_contra hn
      exact str025_fisher_ne_top h ρ (ordinaryRelativeFisher_of_not_mem hn)
    have hEnt : homogeneousEntropy P.measure (fun x => relativeSqrt ν P x ^ 2) =
        ordinaryEntropy h ρ := by
      change _ = relativeEntropy ν P.measure
      rw [relativeEntropy_of_absolutelyContinuous hac]
      congr 1
      funext x
      exact Real.sq_sqrt ENNReal.toReal_nonneg
    have htest : ordinaryLSRate P ≤
        2 * (∫⁻ x, ‖weightedGradient P (relativeSqrt ν P) hmem x‖ₑ ^ 2 ∂P.measure) /
          homogeneousEntropy P.measure (fun x => relativeSqrt ν P x ^ 2) := by
      unfold ordinaryLSRate
      let z : {f : Torus 1 → ℝ // f ∈ WeightedH1 P ∧
          0 < homogeneousEntropy P.measure (fun x => f x ^ 2)} :=
        ⟨relativeSqrt ν P, hmem, by rw [hEnt]; exact hpos⟩
      exact iInf_le (fun F : {f : Torus 1 → ℝ // f ∈ WeightedH1 P ∧
          0 < homogeneousEntropy P.measure (fun x => f x ^ 2)} =>
        2 * (∫⁻ x, ‖weightedGradient P F.1 F.2.1 x‖ₑ ^ 2 ∂P.measure) /
          homogeneousEntropy P.measure (fun x => F.1 x ^ 2)) z
    refine htest.trans_eq ?_
    rw [hEnt]
    unfold str025_quot ordinaryFisher
    rw [ordinaryRelativeFisher, dite_eq_left_of_eq_true (eq_true ⟨hac, hmem⟩)]
    calc (2 * (∫⁻ x, ‖weightedGradient P (relativeSqrt ν P) hmem x‖ₑ ^ 2 ∂P.measure)) /
          ordinaryEntropy h ρ
        = ((2 : ℝ≥0∞) *
            (2 * ∫⁻ x, ‖weightedGradient P (relativeSqrt ν P) hmem x‖ₑ ^ 2 ∂P.measure)) /
            (2 * ordinaryEntropy h ρ) :=
          (ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)).symm
      _ = _ := by congr 1; ring
  · unfold ordinaryLSRate
    refine le_iInf fun ⟨f, hmem, hpos⟩ => ?_
    obtain ⟨ρ, hρpos, hρ⟩ := signed_test_to_abs_STR02932 h hmem hpos
    have hle : (⨅ σ : {σ : AbsoluteDensity 1 // 0 < ordinaryEntropy h σ},
        str025_quot h σ.1) ≤ str025_quot h ρ :=
      iInf_le (fun σ : {σ : AbsoluteDensity 1 // 0 < ordinaryEntropy h σ} =>
        str025_quot h σ.1) ⟨ρ, hρpos⟩
    exact hle.trans hρ

theorem quot_ne_top_STR02932 (h : ℝ) (ρ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h ρ) : str025_quot h ρ ≠ ⊤ :=
  ENNReal.div_ne_top (str025_fisher_ne_top h ρ) (mul_ne_zero (by norm_num) hpos.ne')

theorem quot_eq_inf_STR02932 (h : ℝ) (ρ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h ρ)
    (hmin : ∀ σ : AbsoluteDensity 1, 0 < ordinaryEntropy h σ →
      str025_quot h ρ ≤ str025_quot h σ) :
    str025_quot h ρ =
      ⨅ σ : {σ : AbsoluteDensity 1 // 0 < ordinaryEntropy h σ}, str025_quot h σ.1 := by
  apply le_antisymm
  · exact le_iInf fun σ => hmin σ.1 σ.2
  · exact iInf_le (fun σ : {σ : AbsoluteDensity 1 // 0 < ordinaryEntropy h σ} =>
      str025_quot h σ.1) ⟨ρ, hpos⟩

theorem str029_32_zero_deficit_roots_of_data (h : ℝ) (ρ : Fin 3 → AbsoluteDensity 1)
    (hpos : ∀ j, 0 < ordinaryEntropy h (ρ j))
    (hmin : ∀ (j : Fin 3) (σ : AbsoluteDensity 1), 0 < ordinaryEntropy h σ →
      str025_quot h (ρ j) ≤ str025_quot h σ)
    (hexact : ∀ σ : AbsoluteDensity 1, 0 < ordinaryEntropy h σ →
      (∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ →
        str025_quot h σ ≤ str025_quot h τ) →
      ∃ j : Fin 3, σ.density =ᵐ[haar 1] (ρ j).density)
    (ν : Measure (Torus 1)) :
    ZeroDeficit_STR02901 h
        (ordinaryLSRate (ordinaryReference h)).toReal ν ↔
      ν = threefoldReference h ∨ ∃ j : Fin 3, ν = (densityMeasure (ρ j) : Measure (Torus 1)) := by
  rw [ordinaryLSRate_eq_abs_inf_STR02932,
    ← quot_eq_inf_STR02932 h (ρ 0) (hpos 0) (hmin 0)]
  constructor
  · intro hz
    rcases zeroDeficit_dichotomy_STR02901 hz with href | ⟨σ, hσ, hσpos, hquot⟩
    · exact Or.inl href.1
    · have hq : str025_quot h σ = str025_quot h (ρ 0) :=
        (ENNReal.toReal_eq_toReal_iff' (quot_ne_top_STR02932 h σ hσpos)
          (quot_ne_top_STR02932 h (ρ 0) (hpos 0))).1 hquot
      obtain ⟨j, hj⟩ := hexact σ hσpos (by
        intro τ hτ
        rw [hq]
        exact hmin 0 τ hτ)
      exact Or.inr ⟨j, hσ.symm.trans ((densityMeasure_eq_iff_STR02901 σ (ρ j)).2 hj)⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact zeroDeficit_reference_STR02901 h _
    · refine (zeroDeficit_iff_abs_STR02901 h _ _).2 ⟨ρ j, rfl, ?_⟩
      have hq : str025_quot h (ρ j) = str025_quot h (ρ 0) :=
        le_antisymm (hmin j (ρ 0) (hpos 0)) (hmin 0 (ρ j) (hpos j))
      have hr := congrArg ENNReal.toReal hq
      change (ordinaryFisher h (ρ j) / (2 * ordinaryEntropy h (ρ j))).toReal = _ at hr
      rw [ENNReal.toReal_div, ENNReal.toReal_mul] at hr
      simp only [ENNReal.toReal_ofNat] at hr
      have hH : 0 < (ordinaryEntropy h (ρ j)).toReal :=
        ENNReal.toReal_pos (hpos j).ne' (str025_entropy_ne_top h (ρ j))
      have heq := (div_eq_iff (by positivity : (2 : ℝ) * (ordinaryEntropy h (ρ j)).toReal ≠ 0)).1 hr
      nlinarith

theorem str029_32_zero_deficit_roots :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ρ : Fin 3 → AbsoluteDensity 1,
        (∀ j : Fin 3, 0 < ordinaryEntropy h (ρ j)) ∧
        (∀ j : Fin 3, str025_quot h (ρ j) = ordinaryLSRate (ordinaryReference h)) ∧
        (∀ (j : Fin 3) (σ : AbsoluteDensity 1), 0 < ordinaryEntropy h σ →
          str025_quot h (ρ j) ≤ str025_quot h σ) ∧
        (∀ i j : Fin 3, i ≠ j → ¬ (ρ i).density =ᵐ[haar 1] (ρ j).density) ∧
        (∀ σ : AbsoluteDensity 1, 0 < ordinaryEntropy h σ →
          (∀ τ : AbsoluteDensity 1, 0 < ordinaryEntropy h τ →
            str025_quot h σ ≤ str025_quot h τ) →
          ∃ j : Fin 3, σ.density =ᵐ[haar 1] (ρ j).density) ∧
        (∀ j : Fin 3, (densityMeasure (ρ j) : Measure (Torus 1)) ≠ threefoldReference h) ∧
        (∀ ν : Measure (Torus 1),
          ZeroDeficit_STR02901 h
              (ordinaryLSRate (ordinaryReference h)).toReal ν ↔
            ν = threefoldReference h ∨ ∃ j : Fin 3, ν = (densityMeasure (ρ j) : Measure (Torus 1))) := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC,
    hval, hzero, η, hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2,
    hZC, hZN, hZrot, hZs, hKuniq, δ, hδ, hδη, hopt⟩ :=
    str029_26_exactly_three_global_positive_entropy_optimizers
  refine ⟨δ, hδ, fun h hh hlt => ?_⟩
  obtain ⟨ρ, hρ, hpos, hquot, hmin, hdist, hexact⟩ :=
    hopt h (by simpa [abs_of_pos hh] using hh) (by simpa [abs_of_pos hh] using hlt)
  refine ⟨ρ, hpos, fun j => (quot_eq_inf_STR02932 h (ρ j) (hpos j) (hmin j)).trans
      (ordinaryLSRate_eq_abs_inf_STR02932 h).symm,
    hmin, hdist, hexact, ?_, str029_32_zero_deficit_roots_of_data h ρ hpos hmin hexact⟩
  intro j heq
  have hzero : ordinaryEntropy h (ρ j) = 0 := by
    unfold ordinaryEntropy
    rw [heq]
    exact relativeEntropy_self _
  exact (hpos j).ne' hzero

end DGPS.Frontier.STR029
