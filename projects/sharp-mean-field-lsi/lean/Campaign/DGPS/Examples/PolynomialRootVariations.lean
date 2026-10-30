import DGPS.Examples.PolynomialSpeciesDescentBridge
import DGPS.Examples.ThreeSpeciesCircle.InteractingRootVariations

/-! Actual normalized original-H1 variations against the moving polynomial
reference. The generic absolute-root path is reused; its Fisher and entropy
identities are proved for this actual reference, including zeros of the root. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.PositiveRankOne DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.PolynomialSpecies

/-- Normalizing an arbitrary original H1 root preserves the true polynomial
relative Fisher square, including its absolute value at zeros. -/
theorem polynomial_normAbs_fisher (h : ℝ) {v : Torus 1 → ℝ} {G : Torus 1 → Tangent 1}
    (hG : IsWeakGradient v G) (hn : 0 < ∫ x, v x ^ 2 ∂haar 1) :
    ordinaryRelativeFisher (densityMeasure (normAbs v ⟨G, hG⟩ hn) : Measure (Torus 1))
      (polynomialRankOne h).ref = ENNReal.ofReal
      ((∫ x, (2 * G x 0 - v x * (polynomialRankOne h).dlogq x) ^ 2 ∂haar 1) /
        ∫ x, v x ^ 2 ∂haar 1) := by
  let M := polynomialRankOne h
  rw [M.fisher_eq]
  congr 1
  set n := ∫ x, v x ^ 2 ∂haar 1 with hn_def
  have hGa := (hG.abs).smul (Real.sqrt n)⁻¹
  have hu : IsWeakGradient (normAbs v ⟨G, hG⟩ hn).sqrt
      (fun x => (Real.sqrt n)⁻¹ • (if 0 < v x then G x else if v x < 0 then -G x else 0)) :=
    hGa.congr_ae (Eventually.of_forall fun x => by simp [normAbs, div_eq_inv_mul, hn_def])
      (Eventually.of_forall fun x => rfl)
  have hae := weakGradient_ae_eq hu
  rw [← integral_div]
  have hsn : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn.le
  refine integral_congr_ae ?_
  filter_upwards [hae, hG.ae_grad_eq_zero 0] with x hx hz
  have hx0 : weakGradient (normAbs v ⟨G, hG⟩ hn).sqrt (normAbs v ⟨G, hG⟩ hn).sqrt_mem x 0 =
      (Real.sqrt n)⁻¹ * (if 0 < v x then G x 0 else if v x < 0 then -G x 0 else 0) := by
    have hh := congrArg (fun y : Tangent 1 => y 0) hx
    simp only at hh
    rw [hh]
    split_ifs <;> simp
  rw [hx0]
  simp only [normAbs, hn_def.symm]
  rcases lt_trichotomy (v x) 0 with h1 | h1 | h1
  · have he : (if 0 < v x then G x 0 else if v x < 0 then -G x 0 else 0) = -G x 0 := by
      simp [not_lt.2 h1.le, h1]
    rw [he, abs_of_neg h1]
    field_simp
    rw [hsn]
    ring
  · have he := hz h1
    rw [h1]
    simp [he]
  · have he : (if 0 < v x then G x 0 else if v x < 0 then -G x 0 else 0) = G x 0 := by simp [h1]
    rw [he, abs_of_pos h1]
    field_simp
    rw [hsn]
    ring

/-- The finite real relative entropy has its actual normalization identity.
Nonnegativity comes from relative entropy itself, so no positive-entropy premise
or artificial clipping-neighborhood assumption is needed. -/
theorem polynomial_normAbs_entropy_real (h : ℝ) {v : Torus 1 → ℝ} (hv : MemH1 v)
    (hn : 0 < ∫ x, v x ^ 2 ∂haar 1) :
    (relativeEntropy (densityMeasure (normAbs v hv hn) : Measure (Torus 1))
      (polynomialRankOne h).ref.measure).toReal =
      (∫ x, eulF (v x) ∂haar 1) / (∫ x, v x ^ 2 ∂haar 1) - Real.log (∫ x, v x ^ 2 ∂haar 1) -
        (∫ x, v x ^ 2 * Real.log ((polynomialRankOne h).q x) ∂haar 1) / ∫ x, v x ^ 2 ∂haar 1 := by
  let M := polynomialRankOne h
  rw [M.entropy_ref_eq (densityMeasure (normAbs v hv hn))
    (absoluteDensity_entropy_finite (normAbs v hv hn)).2.2.1,
    ← circleEntropy_eq_relativeEntropy, circleEntropy_eq, RankOneModel.integral_densityMeasure]
  set n := ∫ x, v x ^ 2 ∂haar 1 with hn_def
  obtain ⟨G, hG⟩ := id hv
  have i1 : Integrable (fun x => eulF (v x)) (haar 1) := integrable_sq_mul_log_sq_of_memH1 1 hv
  have i2 : Integrable (fun x => v x ^ 2) (haar 1) := hG.memLp.integrable_sq
  obtain ⟨B, hB⟩ := M.log_bound
  have i3 : Integrable (fun x => v x ^ 2 * Real.log (M.q x)) (haar 1) :=
    i2.mul_bdd M.log_smooth.continuous_torus.aestronglyMeasurable
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  have he1 : (∫ x, (normAbs v hv hn).density x * Real.log ((normAbs v hv hn).density x) ∂haar 1) =
      (∫ x, eulF (v x) ∂haar 1) / n - Real.log n := by
    have he : (fun x => (normAbs v hv hn).density x * Real.log ((normAbs v hv hn).density x)) =
        fun x => eulF (v x) / n - Real.log n * (v x ^ 2 / n) := by
      funext x
      rw [normAbs_density]
      by_cases hx : v x = 0
      · simp [hx, eulF]
      · rw [Real.log_div (pow_ne_zero 2 hx) hn.ne']
        simp only [eulF]
        ring
    rw [he, integral_sub (i1.div_const _) ((i2.div_const _).const_mul _), integral_div,
      integral_const_mul, integral_div, ← hn_def]
    field_simp
  have he2 : (∫ x, (normAbs v hv hn).density x * Real.log (M.q x) ∂haar 1) =
      (∫ x, v x ^ 2 * Real.log (M.q x) ∂haar 1) / n := by
    rw [← integral_div]
    exact integral_congr_ae (Eventually.of_forall fun x => by dsimp only; rw [normAbs_density]; ring)
  rw [he1, he2]

/-- Genuine Fisher differentiation on the full normalized absolute-root path,
with the actual moving-reference logarithmic derivative. -/
theorem polynomial_rootVariation_fisher_hasDerivAt (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt (fun t : ℝ => (ordinaryRelativeFisher
      (densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1)) (polynomialRankOne h).ref).toReal)
      (2 * (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * (polynomialRankOne h).dlogq x) *
          (2 * G x 0 - φ x * (polynomialRankOne h).dlogq x) ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) *
          (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) (polynomialRankOne h).ref).toReal) 0 := by
  let M := polynomialRankOne h
  let S := fun x => 2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * M.dlogq x
  let T := fun x => 2 * G x 0 - φ x * M.dlogq x
  let n := fun t : ℝ => ∫ x, (ρ.sqrt x + t * φ x) ^ 2 ∂haar 1
  let A := fun t : ℝ => ∫ x, (S x + t * T x) ^ 2 ∂haar 1
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hS : MemLp S 2 (haar 1) :=
    ((memLp_coord hw.memLp_grad 0).const_mul 2).sub (RankOneModel.memLp_mul_cont M.dlogq_cont ρ.memLp_sqrt)
  have hT : MemLp T 2 (haar 1) :=
    ((memLp_coord hφ.memLp_grad 0).const_mul 2).sub (RankOneModel.memLp_mul_cont M.dlogq_cont hφ.memLp)
  have hn0 : n 0 = 1 := by simpa only [n, zero_mul, add_zero] using ρ.mass_one
  have hn : HasDerivAt n (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) 0 := by
    simpa only [n, mul_one] using hasDerivAt_integral_quad
      (c := fun _ : Torus 1 => (1 : ℝ)) (C := 1) aestronglyMeasurable_const
      (fun x => by norm_num) ρ.memLp_sqrt hφ.memLp
  have hA : HasDerivAt A (2 * ∫ x, S x * T x ∂haar 1) 0 := by
    simpa only [A, mul_one] using hasDerivAt_integral_quad
      (c := fun _ : Torus 1 => (1 : ℝ)) (C := 1) aestronglyMeasurable_const
      (fun x => by norm_num) hS hT
  have hA0 : A 0 = (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal := by
    rw [M.fisher_eq, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
    simp only [A, S, zero_mul, add_zero]
  have hd := hA.div hn (by rw [hn0]; exact one_ne_zero)
  have hd' : HasDerivAt (fun t => A t / n t)
      (2 * (∫ x, S x * T x ∂haar 1) - (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) *
        (ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus 1)) M.ref).toReal) 0 := by
    convert hd using 1
    rw [hn0, hA0]
    ring
  apply hd'.congr_of_eventuallyEq
  have hnpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < n t := hn.continuousAt.eventually (lt_mem_nhds (show 0 < n 0 by rw [hn0]; norm_num))
  filter_upwards [hnpos] with t ht
  unfold absoluteRootVariation
  rw [dif_pos ht, polynomial_normAbs_fisher h (hw.add (hφ.smul t)) ht,
    ENNReal.toReal_ofReal (div_nonneg (integral_nonneg fun _ => sq_nonneg _) ht.le)]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => by
    dsimp only [S, T]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring)

/-- Relative entropy differentiation needs no positive stored root or positive
entropy. The actual finite real entropy identity removes clipping at zero. -/
theorem polynomial_rootVariation_entropy_hasDerivAt (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt (fun t : ℝ => (relativeEntropy
      (densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1)) (polynomialRankOne h).ref.measure).toReal)
      ((∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) -
        2 * (∫ x, ρ.sqrt x * φ x * Real.log ((polynomialRankOne h).q x) ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) *
          ((relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (polynomialRankOne h).ref.measure).toReal + 1)) 0 := by
  let M := polynomialRankOne h
  let n := fun t : ℝ => ∫ x, (ρ.sqrt x + t * φ x) ^ 2 ∂haar 1
  let Φ := fun t : ℝ => ∫ x, eulF (ρ.sqrt x + t * φ x) ∂haar 1
  let R := fun t : ℝ => ∫ x, (ρ.sqrt x + t * φ x) ^ 2 * Real.log (M.q x) ∂haar 1
  let E := fun t : ℝ => Φ t / n t - Real.log (n t) - R t / n t
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hn0 : n 0 = 1 := by simpa only [n, zero_mul, add_zero] using ρ.mass_one
  have hn : HasDerivAt n (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) 0 := by
    simpa only [n, mul_one] using hasDerivAt_integral_quad
      (c := fun _ : Torus 1 => (1 : ℝ)) (C := 1) aestronglyMeasurable_const
      (fun x => by norm_num) ρ.memLp_sqrt hφ.memLp
  have hΦ : HasDerivAt Φ (∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) 0 := hasDerivAt_integral_eulF hw hφ
  obtain ⟨B, hB⟩ := M.log_bound
  have hR : HasDerivAt R (2 * ∫ x, ρ.sqrt x * φ x * Real.log (M.q x) ∂haar 1) 0 :=
    hasDerivAt_integral_quad M.log_smooth.continuous_torus.aestronglyMeasurable hB ρ.memLp_sqrt hφ.memLp
  have hH0 : (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal = Φ 0 - R 0 := by
    rw [M.entropy_ref_eq (densityMeasure ρ) (absoluteDensity_entropy_finite ρ).2.2.1,
      ← circleEntropy_eq_relativeEntropy, circleEntropy_eq, RankOneModel.integral_densityMeasure]
    simp only [Φ, R, zero_mul, add_zero, eulF, AbsoluteDensity.density]
  have hd := ((hΦ.div hn (by rw [hn0]; exact one_ne_zero)).sub
    (hn.log (by rw [hn0]; exact one_ne_zero))).sub
      (hR.div hn (by rw [hn0]; exact one_ne_zero))
  have hd' : HasDerivAt E
      ((∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) -
        2 * (∫ x, ρ.sqrt x * φ x * Real.log (M.q x) ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) *
          ((relativeEntropy (densityMeasure ρ : Measure (Torus 1)) M.ref.measure).toReal + 1)) 0 := by
    convert hd using 1
    rw [hn0, hH0]
    ring
  apply hd'.congr_of_eventuallyEq
  have hnpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < n t := hn.continuousAt.eventually (lt_mem_nhds (show 0 < n 0 by rw [hn0]; norm_num))
  filter_upwards [hnpos] with t ht
  unfold absoluteRootVariation
  rw [dif_pos ht]
  exact polynomial_normAbs_entropy_real h ⟨_, hw.add (hφ.smul t)⟩ ht

end DGPS.Examples.PolynomialSpecies
