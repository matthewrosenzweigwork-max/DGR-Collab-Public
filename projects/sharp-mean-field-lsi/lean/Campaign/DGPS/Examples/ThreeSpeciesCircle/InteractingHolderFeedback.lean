import DGPS.Examples.ThreeSpeciesCircle.InteractingChartCalculus
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarWeakEuler

/-! Fixed-h Holder control of the actual nonlinear correction on ALL absolute
H1 densities. The field is identified pointwise with the native correction.
There is no minimizer, chart-capture, or family-stationarity hypothesis. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

private def hf (h : ℝ) (i : Fin 3) : Torus 1 → ℝ := ![featureC h, featureS h, featureB h] i
private def hc (i : Fin 3) : ℝ := ![kAlpha, kAlpha, -kBeta] i
private def hm (h : ℝ) (ρ : AbsoluteDensity 1) (i : Fin 3) : ℝ :=
  ∫ x, hf h i x ∂(densityMeasure ρ : Measure (Torus 1))
private def hma (h : ℝ) (ρ : AbsoluteDensity 1) (i : Fin 3) : ℝ :=
  ∫ x, elementaryFeatureGenerator h (hf h i) x ∂(densityMeasure ρ : Measure (Torus 1))
private def hmp (h : ℝ) (ρ : AbsoluteDensity 1) (i : Fin 3) : ℝ :=
  ∫ x, elementaryKprime h (densityMeasure ρ) x * coordPartial 0 (hf h i) x
    ∂(densityMeasure ρ : Measure (Torus 1))
private def hK (h : ℝ) (ρ : AbsoluteDensity 1) : PeriodicHolder_STR02968 :=
  ∑ i : Fin 3, (hc i * hm h ρ i) • interactingHolderFeature h i
private def hD (h : ℝ) (ρ : AbsoluteDensity 1) : PeriodicHolder_STR02968 :=
  ∑ i : Fin 3, (hc i * hm h ρ i) • interactingHolderDerivative h i
private def hA (h : ℝ) (ρ : AbsoluteDensity 1) : PeriodicHolder_STR02968 :=
  ∑ i : Fin 3, (hc i * hm h ρ i) • interactingHolderGenerator h i
private def hLA (h : ℝ) (ρ : AbsoluteDensity 1) : PeriodicHolder_STR02968 :=
  ∑ i : Fin 3, (hc i * hma h ρ i) • interactingHolderFeature h i
private def hLP (h : ℝ) (ρ : AbsoluteDensity 1) : PeriodicHolder_STR02968 :=
  ∑ i : Fin 3, (hc i * hmp h ρ i) • interactingHolderFeature h i

/-- The actual Euler field as an element of the retained angular Holder space. -/
def elementaryEulerHolder (h ε r : ℝ) (ρ : AbsoluteDensity 1) : PeriodicHolder_STR02968 :=
  (2 * ε) • (hA h ρ + hLA h ρ - r • hK h ρ) +
    ε ^ 2 • (hD h ρ * hD h ρ + (2 : ℝ) • hLP h ρ)

private theorem hK_native {h : ℝ} (hh : 0 < h) (ρ : AbsoluteDensity 1) (t : ℝ) :
    (hK h ρ).val t = elementaryKernelMean h (densityMeasure ρ) (angEquiv.symm (t : AngCircle)) := by
  simp only [hK, Fin.sum_univ_three, PeriodicHolder_STR02968.val_add,
    PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    (interactingHolderFeature_native hh 0 t).1, (interactingHolderFeature_native hh 1 t).1,
    (interactingHolderFeature_native hh 2 t).1]
  dsimp only [hc, hm, hf, elementaryKernelMean, momC, momS, momB]
  simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem hD_native {h : ℝ} (hh : 0 < h) (ρ : AbsoluteDensity 1) (t : ℝ) :
    (hD h ρ).val t = elementaryKprime h (densityMeasure ρ) (angEquiv.symm (t : AngCircle)) := by
  rw [elementaryKprime_three_features]
  simp only [hD, Fin.sum_univ_three, PeriodicHolder_STR02968.val_add,
    PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    (interactingHolderFeature_native hh 0 t).2.1, (interactingHolderFeature_native hh 1 t).2.1,
    (interactingHolderFeature_native hh 2 t).2.1]
  dsimp only [hc, hm, hf, momC, momS, momB]
  simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem hA_native {h : ℝ} (hh : 0 < h) (ρ : AbsoluteDensity 1) (t : ℝ) :
    (hA h ρ).val t = elementaryAK h (densityMeasure ρ) (angEquiv.symm (t : AngCircle)) := by
  rw [elementaryAK_moments]
  simp only [hA, Fin.sum_univ_three, PeriodicHolder_STR02968.val_add,
    PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    (interactingHolderFeature_native hh 0 t).2.2, (interactingHolderFeature_native hh 1 t).2.2,
    (interactingHolderFeature_native hh 2 t).2.2]
  dsimp only [hc, hm, hf, momC, momS, momB]
  simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Identification is pointwise and uses the original density only through its
actual probability moments; no special stored-root representative is required. -/
theorem elementaryEulerHolder_native {h : ℝ} (hh : 0 < h) (ε r : ℝ)
    (ρ : AbsoluteDensity 1) (t : ℝ) :
    (elementaryEulerHolder h ε r ρ).val t =
      elementaryEulerCorrection h ε r ρ (angEquiv.symm (t : AngCircle)) := by
  have hLA0 : (hLA h ρ).val t =
      elementaryGeneratorFeedback h ρ (angEquiv.symm (t : AngCircle)) := by
    simp only [hLA, Fin.sum_univ_three, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      (interactingHolderFeature_native hh 0 t).1, (interactingHolderFeature_native hh 1 t).1,
      (interactingHolderFeature_native hh 2 t).1]
    dsimp only [hc, hma, hf, elementaryGeneratorFeedback]
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hLP0 : (hLP h ρ).val t =
      elementaryForceFeedback h ρ (angEquiv.symm (t : AngCircle)) := by
    simp only [hLP, Fin.sum_univ_three, PeriodicHolder_STR02968.val_add,
      PeriodicHolder_STR02968.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      (interactingHolderFeature_native hh 0 t).1, (interactingHolderFeature_native hh 1 t).1,
      (interactingHolderFeature_native hh 2 t).1]
    dsimp only [hc, hmp, hf, elementaryForceFeedback]
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  simp only [elementaryEulerHolder, PeriodicHolder_STR02968.val_add,
    PeriodicHolder_STR02968.val_sub, PeriodicHolder_STR02968.val_smul,
    val_mul_STR02954, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply,
    smul_eq_mul, hLA0, hLP0, hK_native hh, hD_native hh, hA_native hh]
  unfold elementaryEulerCorrection
  ring

private theorem eval_le_norm (F : PeriodicHolder_STR02968) (t : ℝ) : |F.val t| ≤ ‖F‖ := by
  rw [PeriodicHolder_STR02968.norm_def]
  exact (F.isPerHolder.abs_le_supNorm t).trans (le_add_of_nonneg_right (holderSemi_nonneg_STR02968 _ _))

private theorem native_le_norm {F : PeriodicHolder_STR02968} {f : Torus 1 → ℝ}
    (heq : ∀ t, F.val t = f (angEquiv.symm (t : AngCircle))) (x : Torus 1) : |f x| ≤ ‖F‖ := by
  have he := heq (angSec (angEquiv x))
  rw [coe_angSec_STR02962, angEquiv.symm_apply_apply] at he
  rw [← he]
  exact eval_le_norm F _

private theorem moment_bound (ν : ProbabilityMeasure (Torus 1)) {f : Torus 1 → ℝ}
    {B : ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂(ν : Measure (Torus 1))| ≤ B := by
  have hi := hf.integrable_of_hasCompactSupport (μ := (ν : Measure (Torus 1)))
    (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x, |f x| ∂(ν : Measure (Torus 1)) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := (ν : Measure (Torus 1))) f
    _ ≤ ∫ _ : Torus 1, B ∂(ν : Measure (Torus 1)) := integral_mono hi.abs (integrable_const B) hb
    _ = B := by simp

private theorem hf_smooth (h : ℝ) (i : Fin 3) : IsSmoothPeriodic (hf h i) := by
  fin_cases i
  · exact isSmooth_featureC h
  · exact isSmooth_featureS h
  · exact isSmooth_featureB h

private theorem combination_bound (F : Fin 3 → PeriodicHolder_STR02968) (m : Fin 3 → ℝ)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L) (hF : ∀ i, ‖F i‖ ≤ B) (hm : ∀ i, |m i| ≤ L) :
    ‖∑ i : Fin 3, (hc i * m i) • F i‖ ≤ (∑ i : Fin 3, |hc i|) * L * B := by
  calc
    _ ≤ ∑ i : Fin 3, ‖(hc i * m i) • F i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, |hc i| * L * B := Finset.sum_le_sum fun i _ => by
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hm i) (abs_nonneg _)) (hF i)
        (norm_nonneg _) (mul_nonneg (abs_nonneg _) hL)
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]

/-- The common feedback field and scalar multiplier are O(epsilon) in their
actual parameter norms, uniformly over ALL absolute densities and bounded real
rates. Constants are fixed after h,R and before epsilon or the density. -/
theorem elementaryEulerHolder_uniform_bound {h : ℝ} (hh : 0 < h) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : AbsoluteDensity 1, ∀ r : ℝ, |r| ≤ R →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        ‖elementaryEulerHolder h ε r ρ‖ ≤ K * ε ∧
          |elementaryEulerMultiplier h ε r ρ| ≤ K * ε := by
  let B := 1 + ∑ i : Fin 3,
    (‖interactingHolderFeature h i‖ + ‖interactingHolderDerivative h i‖ + ‖interactingHolderGenerator h i‖)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (i : Fin 3) : ‖interactingHolderFeature h i‖ ≤ B ∧
      ‖interactingHolderDerivative h i‖ ≤ B ∧ ‖interactingHolderGenerator h i‖ ≤ B := by
    have hi : ‖interactingHolderFeature h i‖ + ‖interactingHolderDerivative h i‖ +
        ‖interactingHolderGenerator h i‖ ≤ ∑ j : Fin 3,
          (‖interactingHolderFeature h j‖ + ‖interactingHolderDerivative h j‖ + ‖interactingHolderGenerator h j‖) :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin 3 => ‖interactingHolderFeature h j‖ +
          ‖interactingHolderDerivative h j‖ + ‖interactingHolderGenerator h j‖)
        (fun j _ => by positivity) (Finset.mem_univ i)
    dsimp only [B]
    constructor
    · linarith [norm_nonneg (interactingHolderDerivative h i), norm_nonneg (interactingHolderGenerator h i)]
    · constructor <;> linarith [norm_nonneg (interactingHolderFeature h i),
        norm_nonneg (interactingHolderDerivative h i), norm_nonneg (interactingHolderGenerator h i)]
  let C := ∑ i : Fin 3, |hc i|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let M := C * B * B
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg hC hB) hB
  let K := 1 + 3 * (2 + R) * M + 5 * M ^ 2
  have hKpos : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hKpos, fun ρ r hr ε hε he => ?_⟩
  have hm0 (i : Fin 3) : |hm h ρ i| ≤ B :=
    moment_bound (densityMeasure ρ) (hf_smooth h i).continuous_torus fun x =>
      (native_le_norm (fun t => (interactingHolderFeature_native hh i t).1) x).trans (hb i).1
  have hma0 (i : Fin 3) : |hma h ρ i| ≤ B :=
    moment_bound (densityMeasure ρ) (continuous_elementaryFeatureGenerator h _ (hf_smooth h i)) fun x =>
      (native_le_norm (fun t => (interactingHolderFeature_native hh i t).2.2) x).trans (hb i).2.2
  have hK0 : ‖hK h ρ‖ ≤ M := combination_bound _ _ B B hB hB (fun i => (hb i).1) hm0
  have hD0 : ‖hD h ρ‖ ≤ M := combination_bound _ _ B B hB hB (fun i => (hb i).2.1) hm0
  have hA0 : ‖hA h ρ‖ ≤ M := combination_bound _ _ B B hB hB (fun i => (hb i).2.2) hm0
  have hLA0 : ‖hLA h ρ‖ ≤ M := combination_bound _ _ B B hB hB (fun i => (hb i).1) hma0
  have hmp0 (i : Fin 3) : |hmp h ρ i| ≤ M * B := by
    apply moment_bound (densityMeasure ρ)
      (((isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_coordPartial 0).mul
        ((hf_smooth h i).continuous_coordPartial 0))
    intro x
    change |elementaryKprime h (densityMeasure ρ) x * coordPartial 0 (hf h i) x| ≤ M * B
    rw [abs_mul]
    exact mul_le_mul
      ((native_le_norm (hD_native hh ρ) x).trans hD0)
      ((native_le_norm (fun t => (interactingHolderFeature_native hh i t).2.1) x).trans (hb i).2.1)
      (abs_nonneg _) hM
  have hLP0 : ‖hLP h ρ‖ ≤ M ^ 2 := by
    have hc0 := combination_bound (interactingHolderFeature h) (hmp h ρ) B (M * B)
      hB (mul_nonneg hM hB) (fun i => (hb i).1) hmp0
    calc _ ≤ C * (M * B) * B := hc0
      _ = M ^ 2 := by dsimp only [M]; ring
  have hFC : ‖hA h ρ + hLA h ρ - r • hK h ρ‖ ≤ (2 + R) * M := by
    calc
      _ ≤ ‖hA h ρ‖ + ‖hLA h ρ‖ + |r| * ‖hK h ρ‖ := by
        exact (norm_sub_le _ _).trans
          (add_le_add (norm_add_le _ _) (by rw [norm_smul, Real.norm_eq_abs]))
      _ ≤ M + M + R * M := by gcongr
      _ = _ := by ring
  have hFJ : ‖hD h ρ * hD h ρ + (2 : ℝ) • hLP h ρ‖ ≤ 3 * M ^ 2 := by
    calc
      _ ≤ ‖hD h ρ‖ * ‖hD h ρ‖ + 2 * ‖hLP h ρ‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add (norm_mul_le _ _) (by norm_num [norm_smul]))
      _ ≤ M * M + 2 * M ^ 2 := by gcongr
      _ = _ := by ring
  have hC0 : |elementaryC h r ρ| ≤ (2 + R) * M := by
    have ha : |∫ x, elementaryAK h (densityMeasure ρ) x
        ∂(densityMeasure ρ : Measure (Torus 1))| ≤ M :=
      moment_bound (densityMeasure ρ) (continuous_elementaryAK h (densityMeasure ρ))
        (fun x => (native_le_norm (hA_native hh ρ) x).trans hA0)
    have hk : |∫ x, elementaryKernelMean h (densityMeasure ρ) x
        ∂(densityMeasure ρ : Measure (Torus 1))| ≤ M :=
      moment_bound (densityMeasure ρ) (isSmooth_elementaryKernelMean h _).continuous_torus
        (fun x => (native_le_norm (hK_native hh ρ) x).trans hK0)
    unfold elementaryC elementaryQ
    rw [← Structural.budget_integral_densityMeasure]
    calc
      _ ≤ 2 * |∫ x, elementaryAK h (densityMeasure ρ) x
          ∂(densityMeasure ρ : Measure (Torus 1))| +
          |r| * |∫ x, elementaryKernelMean h (densityMeasure ρ) x
            ∂(densityMeasure ρ : Measure (Torus 1))| := by
        simpa only [abs_mul, abs_two] using abs_sub
          (2 * ∫ x, elementaryAK h (densityMeasure ρ) x ∂(densityMeasure ρ : Measure (Torus 1)))
          (r * ∫ x, elementaryKernelMean h (densityMeasure ρ) x ∂(densityMeasure ρ : Measure (Torus 1)))
      _ ≤ 2 * M + R * M := by gcongr
      _ = _ := by ring
  have hJ0 : |elementaryJ h ρ| ≤ M ^ 2 := by
    unfold elementaryJ
    rw [← Structural.budget_integral_densityMeasure]
    apply moment_bound (densityMeasure ρ)
      (((isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_coordPartial 0).pow 2)
    intro x
    change |(elementaryKprime h (densityMeasure ρ) x) ^ 2| ≤ M ^ 2
    have hx := (native_le_norm (hD_native hh ρ) x).trans hD0
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_abs (elementaryKprime h (densityMeasure ρ) x), abs_nonneg (elementaryKprime h (densityMeasure ρ) x)]
  have he2 : ε ^ 2 ≤ ε := by nlinarith
  have hεsqAbs : |(ε ^ 2 : ℝ)| = ε ^ 2 := abs_of_nonneg (sq_nonneg ε)
  have htwoεAbs : |(2 * ε : ℝ)| = 2 * ε :=
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε)
  have htwoεsqAbs : |(2 * ε ^ 2 : ℝ)| = 2 * ε ^ 2 :=
    abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg ε))
  constructor
  · calc
      _ ≤ (2 * ε) * ‖hA h ρ + hLA h ρ - r • hK h ρ‖ +
          ε ^ 2 * ‖hD h ρ * hD h ρ + (2 : ℝ) • hLP h ρ‖ := by
        change ‖(2 * ε) • (hA h ρ + hLA h ρ - r • hK h ρ) +
          ε ^ 2 • (hD h ρ * hD h ρ + (2 : ℝ) • hLP h ρ)‖ ≤ _
        calc
          _ ≤ ‖(2 * ε) • (hA h ρ + hLA h ρ - r • hK h ρ)‖ +
              ‖ε ^ 2 • (hD h ρ * hD h ρ + (2 : ℝ) • hLP h ρ)‖ := norm_add_le _ _
          _ = _ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              htwoεAbs, hεsqAbs]
      _ ≤ (2 * ε) * ((2 + R) * M) + ε * (3 * M ^ 2) := by gcongr
      _ ≤ K * ε := by
        have hrem : 0 ≤ ε * (1 + (2 + R) * M + 2 * M ^ 2) :=
          mul_nonneg hε (by positivity)
        dsimp only [K]
        nlinarith only [hrem]
  · calc
      _ ≤ ε * |elementaryC h r ρ| + 2 * ε ^ 2 * |elementaryJ h ρ| := by
        change |ε * elementaryC h r ρ + 2 * ε ^ 2 * elementaryJ h ρ| ≤ _
        calc
          _ ≤ |ε * elementaryC h r ρ| + |(2 * ε ^ 2) * elementaryJ h ρ| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hε, htwoεsqAbs]
      _ ≤ ε * ((2 + R) * M) + 2 * ε * M ^ 2 := by gcongr
      _ ≤ K * ε := by
        have hrem : 0 ≤ ε * (1 + 2 * (2 + R) * M + 3 * M ^ 2) :=
          mul_nonneg hε (by positivity)
        dsimp only [K]
        nlinarith only [hrem]

end DGPS.Examples.ThreeSpeciesCircle
