import DGPS.Examples.PolynomialUniformCompactness
import DGPS.Examples.PolynomialSpeciesOriginDeficit
import DGPS.Analysis.WeakConvolution

/-! Passage from the true moving polynomial models to their actual Haar origin.
Original root convergence and the proved uniform data control every changing
coefficient. No positive limiting gap or desired dissipation limit is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.PolynomialExactGap
open DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.PolynomialSpecies

private theorem root_pointwise (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n) :
    ∀ᵐ x ∂haar 1, Tendsto (fun n => (ρ n).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
  filter_upwards [ae_all_iff.mpr hae] with x hx
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
    simpa only [Real.norm_eq_abs] using hx n) hη

private theorem fixed_moment (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R)
    (f : Torus 1 → ℝ) (hf : Continuous f) :
    Tendsto (fun n => ∫ x, f x ∂(densityMeasure (ρ n) : Measure (Torus 1))) atTop
      (𝓝 (∫ x, f x ∂(densityMeasure ρL : Measure (Torus 1)))) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have ht := tendsto_integral_comp_mul (T := fun t : ℝ => t ^ 2) (continuous_pow 2)
    hf (Cc := C) (fun x => by simpa only [Real.norm_eq_abs] using hC x (Set.mem_univ x))
    (fun n => (ρ n).memLp_sqrt.aestronglyMeasurable) hub (root_pointwise ρ ρL hη hae)
  simpa only [RankOneModel.integral_densityMeasure, AbsoluteDensity.density] using ht

private theorem varying_moment (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R)
    (f : ℕ → Torus 1 → ℝ) (fL : Torus 1 → ℝ) (hf : ∀ n, Continuous (f n)) (hfL : Continuous fL)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hbound : ∀ n x, |f n x - fL x| ≤ ε n) :
    Tendsto (fun n => ∫ x, f n x ∂(densityMeasure (ρ n) : Measure (Torus 1))) atTop
      (𝓝 (∫ x, fL x ∂(densityMeasure ρL : Measure (Torus 1)))) := by
  have hzero : Tendsto (fun n => (∫ x, f n x ∂(densityMeasure (ρ n) : Measure (Torus 1))) -
      ∫ x, fL x ∂(densityMeasure (ρ n) : Measure (Torus 1))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (Eventually.of_forall fun n => ?_) hε
    rw [← integral_sub ((hf n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hfL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    have hb := norm_integral_le_of_norm_le_const (μ := (densityMeasure (ρ n) : Measure (Torus 1)))
      (f := fun x => f n x - fL x) (C := ε n)
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound n x)
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hb
  have ht := hzero.add (fixed_moment ρ ρL hη hae R hub fL hfL)
  simpa only [zero_add, sub_add_cancel] using ht

private theorem uniform_parts (ε : ℝ → ℝ)
    (hb : ∀ h x, |(polynomialRankOne h).φ x - (polynomialRankOne 0).φ x| +
      |(polynomialRankOne h).Aq x - (polynomialRankOne 0).Aq x| +
      |Real.log ((polynomialRankOne h).q x)| + |(polynomialRankOne h).dlogq x| +
      |(polynomialRankOne h).dφ x - (polynomialRankOne 0).dφ x| ≤ ε h) (h : ℝ) (x : Torus 1) :
    |(polynomialRankOne h).φ x - (polynomialRankOne 0).φ x| ≤ ε h ∧
    |Real.log ((polynomialRankOne h).q x)| ≤ ε h ∧ |(polynomialRankOne h).dlogq x| ≤ ε h ∧
    |(polynomialRankOne h).dφ x - (polynomialRankOne 0).dφ x| ≤ ε h := by
  have ht := hb h x
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    linarith [abs_nonneg ((polynomialRankOne h).φ x - (polynomialRankOne 0).φ x),
      abs_nonneg ((polynomialRankOne h).Aq x - (polynomialRankOne 0).Aq x),
      abs_nonneg (Real.log ((polynomialRankOne h).q x)), abs_nonneg ((polynomialRankOne h).dlogq x),
      abs_nonneg ((polynomialRankOne h).dφ x - (polynomialRankOne 0).dφ x)]

private theorem score_origin (x : Torus 1) : (polynomialRankOne 0).dlogq x = 0 := by
  unfold RankOneModel.dlogq
  simp_rw [polynomial_reference_origin, Real.log_one]
  simp [coordPartial, Function.comp_def]

private theorem weighted_fourier (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R)
    (c : ℕ → Torus 1 → ℝ) (cL : Torus 1 → ℝ) (hc : ∀ n, Continuous (c n)) (hcL : Continuous cL)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hb : ∀ n x, |c n x - cL x| ≤ ε n)
    (k : Fin 1 → ℤ) :
    Tendsto (fun n => DGPS.fourierCoeff (fun x => (ρ n).sqrt x * c n x) k) atTop
      (𝓝 (DGPS.fourierCoeff (fun x => ρL.sqrt x * cL x) k)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcL.continuousOn
  let B := |C| + 1
  let R' := |R| + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hR : 0 ≤ R' := by dsimp [R']; positivity
  have hcB (x : Torus 1) : |cL x| ≤ B := by
    have ht := hC x (Set.mem_univ x)
    rw [Real.norm_eq_abs] at ht
    exact ht.trans (by dsimp [B]; linarith [le_abs_self C])
  have hδ : Tendsto (fun n => |η n| * B + R' * ε n) atTop (𝓝 0) := by
    simpa using (hη.abs.mul_const B).add (hε.const_mul R')
  refine tendsto_fourierCoeff_of_ae_bound
    (fun n => RankOneModel.memLp_mul_cont (hc n) (ρ n).memLp_sqrt)
    (RankOneModel.memLp_mul_cont hcL ρL.memLp_sqrt) hδ (fun n => ?_) k
  filter_upwards [hae n, hub n] with x hx hu
  have he : (ρ n).sqrt x * c n x - ρL.sqrt x * cL x =
      ((ρ n).sqrt x - ρL.sqrt x) * cL x + (ρ n).sqrt x * (c n x - cL x) := by ring
  rw [he]
  have ht := abs_add_le (((ρ n).sqrt x - ρL.sqrt x) * cL x) ((ρ n).sqrt x * (c n x - cL x))
  rw [abs_mul, abs_mul] at ht
  have hu' : |(ρ n).sqrt x| ≤ R' := hu.trans (by dsimp [R']; linarith [le_abs_self R])
  have h1 := mul_le_mul (hx.trans (le_abs_self _)) (hcB x) (abs_nonneg _) (abs_nonneg _)
  have h2 := mul_le_mul hu' (hb n x) (abs_nonneg _) hR
  linarith

private theorem coefficient_add {f g : Torus 1 → ℝ} (hf : MemLp f 2 (haar 1))
    (hg : MemLp g 2 (haar 1)) (k : Fin 1 → ℤ) :
    DGPS.fourierCoeff (fun x => f x + g x) k = DGPS.fourierCoeff f k + DGPS.fourierCoeff g k := by
  have he : (fun x => f x + g x) = fun x => f x - (-1 : ℝ) * g x := by funext x; ring
  rw [he, fourierCoeff_sub' hf (hg.const_mul (-1)), fourierCoeff_const_mul]
  simp

/-- Exact finite actual scalar dissipation as its physical rank-one score square.
The constant-potential gauge changes neither the force nor the original domain. -/
theorem polynomial_scalar_score_square (h : ℝ)
    (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) (ρ : AbsoluteDensity 1) :
    let M := polynomialRankOne h
    scalarDissipation (canonical_elementary_polynomial_model h) b ρ =
      ENNReal.ofReal (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x +
        (eta * ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))) * (ρ.sqrt x * M.dφ x)) ^ 2 ∂haar 1) := by
  let M := polynomialRankOne h
  let bM := polynomialRankOneDrift h b
  have he : scalarDissipation (canonical_elementary_polynomial_model h) b ρ = scalarDissipation M.data bM ρ := rfl
  rw [he]
  unfold scalarDissipation scalarScore
  have hi := (M.dissipation_integral (isWeakGradient_weakGradient ρ.sqrt_mem)
    (eta * ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1)))).2.1
  have hi' : Integrable (fun x => (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x +
      (eta * ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))) * (ρ.sqrt x * M.dφ x)) ^ 2) (haar 1) := by
    convert hi using 1 <;> funext x <;> congr 1 <;> ring
  change (∫⁻ x, ENNReal.ofReal
      (‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • bM.force ρ x‖ ^ 2) ∂haar 1) =
    ENNReal.ofReal (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x +
      (eta * ∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))) * (ρ.sqrt x * M.dφ x)) ^ 2 ∂haar 1)
  rw [RankOneModel.ofReal_integral_eq hi' (fun _ => sq_nonneg _)]
  refine lintegral_congr_ae ?_
  filter_upwards [M.force_coord bM ρ] with x hx
  rw [RankOneModel.norm_sq_tangent]
  congr 2
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hx]
  change 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 + ρ.sqrt x *
      (-M.dlogq x + eta * (∫ y, M.φ y ∂(densityMeasure ρ : Measure (Torus 1))) * M.dφ x) = _
  ring

/-- Gap continuity and genuine dissipation lower semicontinuity for the actual
changing fields at their Haar origin. All competitors keep the original H1 domain. -/
theorem polynomial_varying_scalar_limits (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n)))
    (ρ : ℕ → AbsoluteDensity 1) (ρL : AbsoluteDensity 1)
    {η : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0))
    (hae : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x - ρL.sqrt x| ≤ η n)
    (R : ℝ) (hub : ∀ n, ∀ᵐ x ∂haar 1, |(ρ n).sqrt x| ≤ R) :
    let b0 := lipschitz_absoluteDrift (canonical_elementary_polynomial_model 0) (lipschitzData_canonical_model 0)
    Tendsto (fun n => (scalarGap (canonical_elementary_polynomial_model (h n)) (ρ n) : ℝ≥0∞)) atTop
      (𝓝 (scalarGap (canonical_elementary_polynomial_model 0) ρL : ℝ≥0∞)) ∧
    scalarDissipation (canonical_elementary_polynomial_model 0) b0 ρL ≤
      liminf (fun n => scalarDissipation (canonical_elementary_polynomial_model (h n)) (b n) (ρ n)) atTop := by
  let b0 := lipschitz_absoluteDrift (canonical_elementary_polynomial_model 0) (lipschitzData_canonical_model 0)
  let M := fun n => polynomialRankOne (h n)
  let M0 := polynomialRankOne 0
  obtain ⟨ε, hε, hb⟩ := polynomial_uniform_data_at_origin
  have hεn := hε.comp hh
  have hpart := fun n x => uniform_parts ε hb (h n) x
  have hm := varying_moment ρ ρL hη hae R hub (fun n => (M n).φ) M0.φ
    (fun n => (M n).φ_cont) M0.φ_cont hεn (fun n x => (hpart n x).1)
  have hl := varying_moment ρ ρL hη hae R hub (fun n x => Real.log ((M n).q x))
    (fun x => Real.log (M0.q x)) (fun n => (M n).log_smooth.continuous_torus)
    M0.log_smooth.continuous_torus hεn (fun n x => by
      simp only [M0, polynomial_reference_origin, Real.log_one, sub_zero]
      exact (hpart n x).2.1)
  have hH := tendsto_circleEntropy hub (root_pointwise ρ ρL hη hae)
  have hg (s : ℝ) (bs : AbsoluteDrift (canonical_elementary_polynomial_model s)) (τ : AbsoluteDensity 1) :
      (scalarGap (canonical_elementary_polynomial_model s) τ : ℝ) =
        DGPS.Analysis.circleEntropy τ -
          (∫ x, Real.log ((polynomialRankOne s).q x) ∂(densityMeasure τ : Measure (Torus 1))) +
        eta / 2 * (∫ x, (polynomialRankOne s).φ x ∂(densityMeasure τ : Measure (Torus 1))) ^ 2 := by
    have hi := positive_rank_one_scalar_case (polynomialRankOne s) (polynomialRankOneDrift s bs) τ
    rw [polynomialRankOne_speciesGap, speciesGap_single] at hi
    rw [hi.1, (polynomialRankOne s).entropy_ref_eq (densityMeasure τ) (absoluteDensity_entropy_finite τ).2.2.1,
      ← circleEntropy_eq_relativeEntropy]
    rfl
  constructor
  · have ht := ENNReal.tendsto_ofReal ((hH.sub hl).add ((hm.pow 2).const_mul (eta / 2)))
    have hs (n : ℕ) := hg (h n) (b n) (ρ n)
    have hs0 := hg 0 b0 ρL
    simpa only [M, M0, ← hs, ← hs0, ENNReal.ofReal_coe_nnreal] using ht
  · let S := fun (s : ℝ) (τ : AbsoluteDensity 1) => fun x =>
      2 * weakGradient τ.sqrt τ.sqrt_mem x 0 - τ.sqrt x * (polynomialRankOne s).dlogq x +
        (eta * ∫ y, (polynomialRankOne s).φ y ∂(densityMeasure τ : Measure (Torus 1))) *
          (τ.sqrt x * (polynomialRankOne s).dφ x)
    have hs (s : ℝ) (τ : AbsoluteDensity 1) : MemLp (S s τ) 2 (haar 1) :=
      (((memLp_coord (isWeakGradient_weakGradient τ.sqrt_mem).memLp_grad 0).const_mul 2).sub
        (RankOneModel.memLp_mul_cont (polynomialRankOne s).dlogq_cont τ.memLp_sqrt)).add
          ((RankOneModel.memLp_mul_cont (polynomialRankOne s).dφ_cont τ.memLp_sqrt).const_mul _)
    simp_rw [polynomial_scalar_score_square]
    change ENNReal.ofReal (∫ x, S 0 ρL x ^ 2 ∂haar 1) ≤
      liminf (fun n => ENNReal.ofReal (∫ x, S (h n) (ρ n) x ^ 2 ∂haar 1)) atTop
    refine ofReal_integral_sq_le_liminf (fun n => hs (h n) (ρ n)) (hs 0 ρL) fun k => ?_
    have hu := tendsto_fourierCoeff_of_ae_bound (fun n => (ρ n).memLp_sqrt) ρL.memLp_sqrt hη hae k
    have hlog := weighted_fourier ρ ρL hη hae R hub (fun n => (M n).dlogq) M0.dlogq
      (fun n => (M n).dlogq_cont) M0.dlogq_cont hεn (fun n x => by
        rw [show M0.dlogq x = 0 from score_origin x, sub_zero]
        exact (hpart n x).2.2.1) k
    have hgrad := weighted_fourier ρ ρL hη hae R hub (fun n => (M n).dφ) M0.dφ
      (fun n => (M n).dφ_cont) M0.dφ_cont hεn (fun n x => (hpart n x).2.2.2) k
    have hid (s : ℝ) (τ : AbsoluteDensity 1) : DGPS.fourierCoeff (S s τ) k =
        2 * (2 * Real.pi * Complex.I * (k 0 : ℂ) * DGPS.fourierCoeff τ.sqrt k) -
          DGPS.fourierCoeff (fun x => τ.sqrt x * (polynomialRankOne s).dlogq x) k +
          ((eta * ∫ y, (polynomialRankOne s).φ y ∂(densityMeasure τ : Measure (Torus 1))) : ℂ) *
            DGPS.fourierCoeff (fun x => τ.sqrt x * (polynomialRankOne s).dφ x) k := by
      calc
        DGPS.fourierCoeff (S s τ) k =
            DGPS.fourierCoeff (fun x => 2 * weakGradient τ.sqrt τ.sqrt_mem x 0 - τ.sqrt x * (polynomialRankOne s).dlogq x) k +
            DGPS.fourierCoeff (fun x => (eta * ∫ y, (polynomialRankOne s).φ y ∂(densityMeasure τ : Measure (Torus 1))) *
              (τ.sqrt x * (polynomialRankOne s).dφ x)) k :=
          coefficient_add
            (((memLp_coord (isWeakGradient_weakGradient τ.sqrt_mem).memLp_grad 0).const_mul 2).sub
              (RankOneModel.memLp_mul_cont (polynomialRankOne s).dlogq_cont τ.memLp_sqrt))
            ((RankOneModel.memLp_mul_cont (polynomialRankOne s).dφ_cont τ.memLp_sqrt).const_mul _) k
        _ = _ := by
          rw [fourierCoeff_sub' ((memLp_coord (isWeakGradient_weakGradient τ.sqrt_mem).memLp_grad 0).const_mul 2)
            (RankOneModel.memLp_mul_cont (polynomialRankOne s).dlogq_cont τ.memLp_sqrt), fourierCoeff_const_mul,
            fourierCoeff_weakGradient (isWeakGradient_weakGradient τ.sqrt_mem) 0 k, fourierCoeff_const_mul]
          simp
    simp_rw [hid]
    simpa only [M, M0, Function.comp_apply, Complex.ofReal_mul] using
      (((hu.const_mul _).const_mul _).sub hlog).add
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp (hm.const_mul eta)).mul hgrad)

end DGPS.Examples.PolynomialSpecies
