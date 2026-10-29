import DGPS.Examples.HarmonicNonattainment
import DGPS.Analysis.CircleLSI

/-!
# Exact harmonic family deficit polynomial (EX077)

For a finite species family `F` and the first-harmonic model `attractiveXY (2k) 0`, every species
sees the same smooth force, the gradient of `W * ρ̄` with `ρ̄` the barycenter. Expanding the squared
species dissipation against this force, the physical derivative terms give the Fisher information,
and the interaction terms reduce to the common cosine/sine moments `c = ∫ cos dρ̄`, `s = ∫ sin dρ̄`.

With `a0 = 4π²`, `r = a0 (1 - k)`, `J = ∑ θ_s I(ρ_s) / (2 a0)`, `E = ∑ θ_s H(ρ_s | Haar)`,
`M = c² + s²`, `P = ∫ (c sin - s cos)² dρ̄` and `G = E - k M` (EX076), one has

  `(D - 2 r G) / (2 a0) = (J - E) + k (E - M) + k² (2P - M)`.

Design choices (R5 notes).
* This is a new module because `HarmonicNonattainment` is the EX076 module.
* The hypotheses `0 ≤ k < 1` are those of EX076; they identify the free-energy minimum `F_* = k`
  used in the gap `G`. The identity for `D` itself does not use them.
* `E`, `M`, `P` and `J` are written inline in the statement.
* Helper lemmas carry the suffix `_ex077`.
-/

open MeasureTheory UnitAddTorus
open scoped ENNReal NNReal

namespace DGPS.Examples

open DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYCritical DGPS.Models

/-- EX077 helper: the species integrand `‖2 ∇√ρ + √ρ f‖²`, for a force with `f₀ = ψ = xyTrig A B 0`,
integrates to the Fisher information, minus twice the flux `∫ ρ ∂ψ`, plus `∫ ρ ψ²`. -/
theorem score_ex077 (ρ : DGPS.AbsoluteDensity 1) (A B : ℝ) (f : DGPS.Torus 1 → DGPS.Tangent 1)
    (hf : ∀ᵐ x ∂DGPS.haar 1, f x 0 = xyTrig A B 0 x) :
    Integrable (fun x => ‖(2 : ℝ) • DGPS.weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • f x‖ ^ 2)
      (DGPS.haar 1) ∧
    ∫ x, ‖(2 : ℝ) • DGPS.weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • f x‖ ^ 2 ∂DGPS.haar 1 =
      DGPS.Analysis.circleFisherInformation ρ
        - 2 * ∫ x, ρ.density x * DGPS.coordPartial 0 (xyTrig A B 0) x ∂DGPS.haar 1
        + ∫ x, ρ.density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 := by
  set g := DGPS.weakGradient ρ.sqrt ρ.sqrt_mem with hgdef
  set ψ := xyTrig A B 0 with hψdef
  have hψ : DGPS.IsSmoothPeriodic ψ := isSmoothPeriodic_xyTrig _ _ _
  have hψc : Continuous ψ := continuous_xyTrig A B 0
  have hwg : DGPS.IsWeakGradient ρ.sqrt g := DGPS.isWeakGradient_weakGradient ρ.sqrt_mem
  have hbd : ∀ x, ‖ψ x‖ ≤ |A| + |B| := fun x => by
    rw [Real.norm_eq_abs]; exact abs_xyTrig_zero_le A B x
  have hpt : ∀ᵐ x ∂DGPS.haar 1, ‖(2 : ℝ) • g x + ρ.sqrt x • f x‖ ^ 2 =
      4 * (g x 0) ^ 2 + 4 * (ρ.sqrt x * g x 0 * ψ x) + ρ.density x * ψ x ^ 2 := by
    filter_upwards [hf] with x hx
    rw [DGPS.tangent_norm_sq]
    simp only [Fin.sum_univ_one, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hx,
      DGPS.AbsoluteDensity.density]
    ring
  have hg2 : Integrable (fun x => (g x 0) ^ 2) (DGPS.haar 1) :=
    (DGPS.haar_circle_lsi ρ).2.1.congr (Filter.Eventually.of_forall fun x => by
      show ‖g x‖ ^ 2 = _
      rw [DGPS.tangent_norm_sq]; simp)
  have hug : Integrable (fun x => ρ.sqrt x * g x 0) (DGPS.haar 1) :=
    ρ.memLp_sqrt.integrable_mul (DGPS.memLp_coord hwg.memLp_grad 0)
  have hI2 : Integrable (fun x => ρ.sqrt x * g x 0 * ψ x) (DGPS.haar 1) :=
    hug.mul_bdd hψc.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hI3 : Integrable (fun x => ρ.density x * ψ x ^ 2) (DGPS.haar 1) := by
    refine ρ.integrable_density.mul_bdd (c := (|A| + |B|) ^ 2)
      (hψc.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have h0 := hbd x
    rw [Real.norm_eq_abs] at h0 ⊢
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have hint : Integrable (fun x => 4 * (g x 0) ^ 2 + 4 * (ρ.sqrt x * g x 0 * ψ x) +
      ρ.density x * ψ x ^ 2) (DGPS.haar 1) :=
    ((hg2.const_mul 4).add (hI2.const_mul 4)).add hI3
  refine ⟨hint.congr (hpt.mono fun x hx => hx.symm), ?_⟩
  have h1 : Integrable (fun x => 4 * (g x 0) ^ 2) (DGPS.haar 1) := hg2.const_mul 4
  have h2 : Integrable (fun x => 4 * (ρ.sqrt x * g x 0 * ψ x)) (DGPS.haar 1) := hI2.const_mul 4
  have hF : DGPS.Analysis.circleFisherInformation ρ = 4 * ∫ x, (g x 0) ^ 2 ∂DGPS.haar 1 := by
    unfold DGPS.Analysis.circleFisherInformation
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖g x‖ ^ 2 = _
    rw [DGPS.tangent_norm_sq]; simp
  -- integration by parts against the smooth test function ψ
  have hib := (DGPS.density_gradient ρ).1.ibp ψ hψ 0
  simp only [PiLp.smul_apply, smul_eq_mul] at hib
  have hR : ∫ x, 4 * (ρ.sqrt x * g x 0 * ψ x) ∂DGPS.haar 1 =
      2 * ∫ x, (2 * ρ.sqrt x * g x 0) * ψ x ∂DGPS.haar 1 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  have e1 : ∫ x, (4 * (g x 0) ^ 2 + 4 * (ρ.sqrt x * g x 0 * ψ x)) ∂DGPS.haar 1 =
      ∫ x, 4 * (g x 0) ^ 2 ∂DGPS.haar 1 + ∫ x, 4 * (ρ.sqrt x * g x 0 * ψ x) ∂DGPS.haar 1 :=
    integral_add h1 h2
  have e2 : ∫ x, (4 * (g x 0) ^ 2 + 4 * (ρ.sqrt x * g x 0 * ψ x) + ρ.density x * ψ x ^ 2)
      ∂DGPS.haar 1 =
      ∫ x, (4 * (g x 0) ^ 2 + 4 * (ρ.sqrt x * g x 0 * ψ x)) ∂DGPS.haar 1 +
        ∫ x, ρ.density x * ψ x ^ 2 ∂DGPS.haar 1 :=
    integral_add (h1.add h2) hI3
  rw [integral_congr_ae hpt, e2, e1, hR, integral_const_mul 4, hF]
  linear_combination 2 * hib

/-- EX077 helper: the first-harmonic force of the attractive XY model, in coordinate `0`. -/
theorem force_ae_ex077 (κ h : ℝ) (b : DGPS.AbsoluteDrift (attractiveXY κ h))
    (ρ : DGPS.AbsoluteDensity 1) (A B : ℝ)
    (hA : A = 2 * Real.pi * (-(κ * xyZ2 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)))))
    (hB : B = -(2 * Real.pi) * (-(h + κ * xyZ1 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))))) :
    ∀ᵐ x ∂DGPS.haar 1, b.force ρ x 0 = xyTrig A B 0 x := by
  have hg := isWeakGradientLp_one_of_smooth (isSmoothPeriodic_interactionPotential κ h ρ)
  have h1 := b.ae_eq_of_isWeakGradient ρ hg
  filter_upwards [h1] with x hx
  rw [hx, DGPS.smoothGrad_apply, interactionPotential_attractiveXY, coordPartial_xyTrig, hA, hB]

/-- EX077 helper: a density integrates the first-harmonic function against its two moments. -/
theorem integral_density_mul_xyTrig_ex077 (σ : DGPS.AbsoluteDensity 1) (a b : ℝ) :
    ∫ x, σ.density x * xyTrig a b 0 x ∂DGPS.haar 1 =
      a * xyZ1 (DGPS.densityMeasure σ : Measure (DGPS.Torus 1)) +
        b * xyZ2 (DGPS.densityMeasure σ : Measure (DGPS.Torus 1)) := by
  rw [← integral_densityMeasure σ (xyTrig a b 0)]
  simp only [xyTrig, add_zero]
  rw [integral_add ((integrable_xyMode_re (DGPS.densityMeasure σ : Measure (DGPS.Torus 1))).const_mul a)
      ((integrable_xyMode_im (DGPS.densityMeasure σ : Measure (DGPS.Torus 1))).const_mul b),
    integral_const_mul, integral_const_mul]
  rfl

/-- EX077 helper: the barycenter mixes the species integrals of a bounded continuous function. -/
theorem barycenter_integral_ex077 (F : DGPS.SpeciesFamily 1) (φ : DGPS.Torus 1 → ℝ)
    (h : ∀ s, Integrable (fun x => (F.density s).density x * φ x) (DGPS.haar 1)) :
    ∑ s, F.weight s * ∫ x, (F.density s).density x * φ x ∂DGPS.haar 1 =
      ∫ x, (DGPS.barycenter F).density x * φ x ∂DGPS.haar 1 := by
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun s _ => (h s).const_mul _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [F.barycenter_density_apply x, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [DGPS.AbsoluteDensity.density]
  ring

/-- EX077 helper: the species dissipation is the ENNReal image of the real sum of the species
integrals of the squared score. -/
theorem speciesDissipation_real_ex077 (κ h : ℝ) (b : DGPS.AbsoluteDrift (attractiveXY κ h))
    (F : DGPS.SpeciesFamily 1) (A B : ℝ)
    (hf : ∀ᵐ x ∂DGPS.haar 1, b.force (DGPS.barycenter F) x 0 = xyTrig A B 0 x) :
    DGPS.speciesDissipation (attractiveXY κ h) b F = ENNReal.ofReal
      (∑ s, F.weight s * ∫ x, ‖(2 : ℝ) • F.sqrtGradient s x +
        (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2 ∂DGPS.haar 1) := by
  have hs : ∀ s, ∫⁻ x, ENNReal.ofReal
      (‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2)
        ∂DGPS.haar 1 =
      ENNReal.ofReal (∫ x, ‖(2 : ℝ) • F.sqrtGradient s x +
        (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2 ∂DGPS.haar 1) := fun s =>
    (ofReal_integral_eq_lintegral_ofReal (score_ex077 (F.density s) A B _ hf).1
      (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
  have hnn : ∀ s ∈ (Finset.univ : Finset (Fin F.count)),
      0 ≤ F.weight s * ∫ x, ‖(2 : ℝ) • F.sqrtGradient s x +
        (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2 ∂DGPS.haar 1 := fun s _ =>
    mul_nonneg (F.weight_nonneg s) (integral_nonneg fun x => sq_nonneg _)
  unfold DGPS.speciesDissipation
  simp_rw [hs, ← ENNReal.ofReal_mul (F.weight_nonneg _)]
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]

/-- EX077: exact harmonic family deficit polynomial. For `0 ≤ k < 1`, the species dissipation of the
first-harmonic model is finite, and `(D - 2 r G) / (2 a0)` equals `(J - E) + k (E - M) + k² (2P - M)`
with `a0 = 4π²`, `r = a0 (1 - k)`, `G = E - k M` the species gap, `E` the mixed relative entropy,
`M = c² + s²` and `P = ∫ (c sin - s cos)² dρ̄` the barycenter moments. -/
theorem exact_harmonic_family_deficit_polynomial (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) (F : DGPS.SpeciesFamily 1) :
    DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b F ≠ ⊤ ∧
      ((DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b F).toReal -
          2 * (4 * Real.pi ^ 2 * (1 - k)) *
            (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ)) /
          (2 * (4 * Real.pi ^ 2)) =
        ((∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s)) /
            (2 * (4 * Real.pi ^ 2)) -
          (∑ s, F.weight s * (DGPS.relativeEntropy
            (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal)) +
        k * ((∑ s, F.weight s * (DGPS.relativeEntropy
            (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) -
          (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2 +
            xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2)) +
        k ^ 2 * (2 * (∫ x, (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) *
            (xyMode x).im - xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) *
            (xyMode x).re) ^ 2 ∂(DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1))) -
          (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2 +
            xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2)) := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 2 * Real.pi * (-((2 * k) *
      xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)))) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = -(2 * Real.pi) * (-(0 + (2 * k) *
      xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)))) := ⟨_, rfl⟩
  have hf : ∀ᵐ x ∂DGPS.haar 1, b.force (DGPS.barycenter F) x 0 = xyTrig A B 0 x :=
    force_ae_ex077 (2 * k) 0 b (DGPS.barycenter F) A B hA hB
  have hD := speciesDissipation_real_ex077 (2 * k) 0 b F A B hf
  have hI0 : 0 ≤ ∑ s, F.weight s * ∫ x, ‖(2 : ℝ) • F.sqrtGradient s x +
      (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2 ∂DGPS.haar 1 :=
    Finset.sum_nonneg fun s _ =>
      mul_nonneg (F.weight_nonneg s) (integral_nonneg fun x => sq_nonneg _)
  refine ⟨by rw [hD]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [hD, ENNReal.toReal_ofReal hI0]
  -- per-species Fisher, flux and quadratic decomposition
  have hsp : ∀ s, ∫ x, ‖(2 : ℝ) • F.sqrtGradient s x +
      (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2 ∂DGPS.haar 1 =
      DGPS.Analysis.circleFisherInformation (F.density s) -
        2 * ∫ x, (F.density s).density x * DGPS.coordPartial 0 (xyTrig A B 0) x ∂DGPS.haar 1 +
        ∫ x, (F.density s).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 := fun s =>
    (score_ex077 (F.density s) A B _ hf).2
  have key : ∑ s, F.weight s * ∫ x, ‖(2 : ℝ) • F.sqrtGradient s x +
      (F.density s).sqrt x • b.force (DGPS.barycenter F) x‖ ^ 2 ∂DGPS.haar 1 =
      (∑ s, F.weight s * DGPS.Analysis.circleFisherInformation (F.density s)) -
        2 * (∑ s, F.weight s *
          ∫ x, (F.density s).density x * DGPS.coordPartial 0 (xyTrig A B 0) x ∂DGPS.haar 1) +
        ∑ s, F.weight s * ∫ x, (F.density s).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hsp s]
    ring
  -- the flux term: the derivative of the first-harmonic force, summed over the species
  have hcp : DGPS.coordPartial 0 (xyTrig A B 0) = xyTrig (2 * Real.pi * B) (-(2 * Real.pi) * A) 0 :=
    funext fun x => coordPartial_xyTrig A B 0 x
  have hX : ∑ s, F.weight s * ∫ x, (F.density s).density x *
      DGPS.coordPartial 0 (xyTrig A B 0) x ∂DGPS.haar 1 =
      (2 * Real.pi * B) * xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) +
        (-(2 * Real.pi) * A) *
          xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) := by
    have e : ∀ s, F.weight s * ∫ x, (F.density s).density x *
        DGPS.coordPartial 0 (xyTrig A B 0) x ∂DGPS.haar 1 =
        (2 * Real.pi * B) * (F.weight s *
          xyZ1 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1))) +
        (-(2 * Real.pi) * A) * (F.weight s *
          xyZ2 (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1))) := fun s => by
      rw [hcp, integral_density_mul_xyTrig_ex077]
      ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← xyZ1_barycenter, ← xyZ2_barycenter]
  -- the quadratic term: integrate over the barycenter
  have hφc : Continuous (fun x => xyTrig A B 0 x ^ 2) := (continuous_xyTrig A B 0).pow 2
  have hφb : ∀ x, ‖xyTrig A B 0 x ^ 2‖ ≤ (|A| + |B|) ^ 2 := fun x => by
    have h0 := abs_xyTrig_zero_le A B x
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h0 2
  have hBar : ∑ s, F.weight s * ∫ x, (F.density s).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 =
      ∫ x, (DGPS.barycenter F).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 :=
    barycenter_integral_ex077 F (fun x => xyTrig A B 0 x ^ 2) fun s =>
      (F.density s).integrable_density.mul_bdd hφc.aestronglyMeasurable
        (Filter.Eventually.of_forall hφb)
  have hI : ∫ x, (DGPS.barycenter F).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 =
      ∫ x, xyTrig A B 0 x ^ 2 ∂(DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) :=
    (integral_densityMeasure (DGPS.barycenter F) (fun x => xyTrig A B 0 x ^ 2)).symm
  have hsq : ∀ x, xyTrig A B 0 x ^ 2 = 16 * Real.pi ^ 2 * k ^ 2 *
      (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) * (xyMode x).im -
        xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) * (xyMode x).re) ^ 2 :=
    fun x => by
      rw [hA, hB]
      simp only [xyTrig, add_zero]
      ring
  have hY : ∑ s, F.weight s * ∫ x, (F.density s).density x * xyTrig A B 0 x ^ 2 ∂DGPS.haar 1 =
      16 * Real.pi ^ 2 * k ^ 2 * ∫ x, (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) :
          Measure (DGPS.Torus 1)) * (xyMode x).im - xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) :
          Measure (DGPS.Torus 1)) * (xyMode x).re) ^ 2
        ∂(DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) := by
    rw [hBar, hI, integral_congr_ae (Filter.Eventually.of_forall hsq), integral_const_mul]
  -- the gap, from EX076
  have hG : (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F : ℝ) =
      (∑ s, F.weight s * (DGPS.relativeEntropy
        (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal) -
        k * (xyZ1 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2 +
          xyZ2 (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1)) ^ 2) := by
    rw [speciesGap_identity_ex076 k hk0 hk1 F, norm_sq_integral_xyMode_xyc]
  rw [key, hX, hY, hG]
  subst hA hB
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end DGPS.Examples
