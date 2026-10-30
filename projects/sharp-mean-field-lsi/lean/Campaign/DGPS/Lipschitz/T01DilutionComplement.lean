import DGPS.Lipschitz.T01ReferenceEigenbasis
import DGPS.Analysis.RelativeFisher
import FullLabeledLSI.Paper.Sec3DiluteC

/-!
# The weighted Sobolev complement in exact binary dilution

The complementary square root is constructed on the full weighted H¹ domain. The
gradient estimate is uniform in the dilution parameter, including zero, and is quadratic
in that parameter at the Dirichlet-energy level.
-/

noncomputable section
open MeasureTheory Filter

namespace DGPS.Lipschitz

variable {d : ℕ}

noncomputable def t01DilutionComplement (ε a : ℝ) (g : Torus d → ℝ) : Torus d → ℝ :=
  fun x => Real.sqrt (1 / (1 - ε)) * Real.sqrt (1 - ε * a * g x ^ 2)

theorem t01DilutionComplement_nonneg (ε a : ℝ) (g : Torus d → ℝ) (x : Torus d) :
    0 ≤ t01DilutionComplement ε a g x :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem t01DilutionComplement_sq {ε a M : ℝ} (g : Torus d → ℝ)
    (hgM : ∀ x, |g x| ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (ha : 0 ≤ a)
    (hεM : ε * a * M ^ 2 ≤ 1 / 2) (x : Torus d) :
    (1 - ε) * t01DilutionComplement ε a g x ^ 2 = 1 - ε * a * g x ^ 2 := by
  have hgsq : g x ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs (g x)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hgM x) 2
  have hrho : 0 ≤ 1 - ε * a * g x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hgsq (mul_nonneg hε0 ha)]
  have hden : 0 < 1 - ε := by linarith
  unfold t01DilutionComplement
  rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hrho]
  field_simp

/-- A genuine current weak gradient and the pointwise quadratic energy bound. -/
theorem t01DilutionComplement_gradient (P : BoundedPositiveReference d)
    {g : Torus d → ℝ} (hg : g ∈ WeightedH1 P) {ε a M : ℝ}
    (hgM : ∀ x, |g x| ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (ha : 0 ≤ a)
    (hεM : ε * a * M ^ 2 ≤ 1 / 2) :
    ∃ G : Torus d → Tangent d,
      IsWeakGradient (t01DilutionComplement ε a g) G ∧
        ∀ x, ‖G x‖ ^ 2 ≤ 8 * ε ^ 2 * a ^ 2 * M ^ 2 *
          ‖weightedGradient P g hg x‖ ^ 2 := by
  let G := weightedGradient P g hg
  have hG : IsWeakGradient g G :=
    (isWeightedWeakGradient_iff P).mp (isWeightedWeakGradient_weightedGradient P hg)
  have hGj : ∀ k, MemLp (fun x => G x k) 2 (haar d) := memLp_coord hG.memLp_grad
  let b := Real.sqrt (1 / (1 - ε))
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hden : 0 < 1 - ε := by linarith
  have hb2 : b ^ 2 = 1 / (1 - ε) := Real.sq_sqrt (by positivity)
  have hb2le : b ^ 2 ≤ 2 := by
    rw [hb2, div_le_iff₀ hden]
    linarith
  have hr : 0 ≤ ε * a := mul_nonneg hε0 ha
  let H : Torus d → Fin d → ℝ := fun x k =>
    b * (-(ε * a * g x * G x k) / Real.sqrt (1 - ε * a * g x ^ 2))
  have hleg : SharpLSI.IsWeakGrad (t01DilutionComplement ε a g) H :=
    (SharpLSI.FL.isWeakGrad_sqrt_one_sub hG.isWeakGrad hgM hGj hr hεM).cmul b
  have hbound : ∀ x k, |H x k| ≤ b * (2 * (ε * a) * M) * |G x k| := by
    intro x k
    change |b * _| ≤ _
    rw [abs_mul, abs_of_nonneg hb0]
    have h := SharpLSI.FL.abs_grad_sqrt_one_sub_le (G := G x k) (hgM x) hr hεM
    calc b * |-(ε * a * g x * G x k) / Real.sqrt (1 - ε * a * g x ^ 2)|
      ≤ b * (2 * (ε * a) * M * |G x k|) := mul_le_mul_of_nonneg_left h hb0
      _ = _ := by ring
  have hHj : ∀ k, MemLp (fun x => H x k) 2 (haar d) := fun k =>
    (hGj k).of_le_mul (hleg.aestronglyMeasurable_grad k)
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x k)
  have hH : MemLp (fun x => WithLp.toLp 2 (H x)) 2 (haar d) :=
    memLp_piLp_iff.mpr hHj
  have huB : ∀ x, t01DilutionComplement ε a g x ≤ b := by
    intro x
    change b * Real.sqrt (1 - ε * a * g x ^ 2) ≤ b
    apply mul_le_of_le_one_right hb0
    rw [Real.sqrt_le_one]
    nlinarith [mul_nonneg hr (sq_nonneg (g x))]
  have hu : MemLp (t01DilutionComplement ε a g) 2 (haar d) :=
    MemLp.of_bound hleg.aestronglyMeasurable_fun b (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (t01DilutionComplement_nonneg ε a g x)]
      exact huB x)
  refine ⟨fun x => WithLp.toLp 2 (H x), isWeakGradient_of_legacy_pair hleg hu hH, fun x => ?_⟩
  have hsq := SharpLSI.FL.sqNorm_le_of_abs_le (hbound x)
  change SharpLSI.sqNorm (H x) ≤ (b * (2 * (ε * a) * M)) ^ 2 *
    SharpLSI.sqNorm (fun k => G x k) at hsq
  simp only [tangent_norm_sq]
  change SharpLSI.sqNorm (H x) ≤ 8 * ε ^ 2 * a ^ 2 * M ^ 2 *
    SharpLSI.sqNorm (fun k => G x k)
  calc SharpLSI.sqNorm (H x) ≤ _ := hsq
    _ = b ^ 2 * ((2 * (ε * a) * M) ^ 2 * SharpLSI.sqNorm (fun k => G x k)) := by ring
    _ ≤ 2 * ((2 * (ε * a) * M) ^ 2 * SharpLSI.sqNorm (fun k => G x k)) :=
      mul_le_mul_of_nonneg_right hb2le (mul_nonneg (sq_nonneg _) (SharpLSI.sqNorm_nonneg _))
    _ = _ := by ring

theorem t01DilutionComplement_mem (P : BoundedPositiveReference d)
    {g : Torus d → ℝ} (hg : g ∈ WeightedH1 P) {ε a M : ℝ}
    (hgM : ∀ x, |g x| ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (ha : 0 ≤ a)
    (hεM : ε * a * M ^ 2 ≤ 1 / 2) : t01DilutionComplement ε a g ∈ WeightedH1 P := by
  obtain ⟨G, hG, -⟩ := t01DilutionComplement_gradient P hg hgM hε0 hε1 ha hεM
  exact (mem_weightedH1_iff P).mpr ⟨G, hG⟩

theorem t01DilutionComplement_mass (P : BoundedPositiveReference d)
    {g : Torus d → ℝ} (hg : g ∈ WeightedH1 P) {ε a M : ℝ}
    (hgM : ∀ x, |g x| ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (ha : 0 ≤ a)
    (hεM : ε * a * M ^ 2 ≤ 1 / 2) (hZ : a * ∫ x, g x ^ 2 ∂P.measure = 1) :
    ∫ x, t01DilutionComplement ε a g x ^ 2 ∂P.measure = 1 := by
  have hu := isWeightedWeakGradient_weightedGradient P
    (t01DilutionComplement_mem P hg hgM hε0 hε1 ha hεM)
  have hg' := isWeightedWeakGradient_weightedGradient P hg
  have hint : (1 - ε) * ∫ x, t01DilutionComplement ε a g x ^ 2 ∂P.measure = 1 - ε := by
    rw [← integral_const_mul]
    simp_rw [t01DilutionComplement_sq g hgM hε0 hε1 ha hεM]
    rw [integral_sub (integrable_const _) (hg'.memLp.integrable_sq.const_mul (ε * a)),
      integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    nlinarith [hZ]
  nlinarith [show 0 < 1 - ε by linarith]

theorem t01DilutionComplement_energy_bound (P : BoundedPositiveReference d)
    {g : Torus d → ℝ} (hg : g ∈ WeightedH1 P) {ε a M : ℝ}
    (hgM : ∀ x, |g x| ≤ M) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (ha : 0 ≤ a)
    (hεM : ε * a * M ^ 2 ≤ 1 / 2)
    (hu : t01DilutionComplement ε a g ∈ WeightedH1 P) :
    ∫ x, ‖weightedGradient P (t01DilutionComplement ε a g) hu x‖ ^ 2 ∂P.measure ≤
      8 * ε ^ 2 * a ^ 2 * M ^ 2 * ∫ x, ‖weightedGradient P g hg x‖ ^ 2 ∂P.measure := by
  obtain ⟨G, hG, hGb⟩ := t01DilutionComplement_gradient P hg hgM hε0 hε1 ha hεM
  have hrep : weightedGradient P (t01DilutionComplement ε a g) hu =ᵐ[P.measure] G :=
    P.measure_ac_haar.ae_le (weightedGradient_ae_eq P hu hG)
  have hGw := (isWeightedWeakGradient_iff P).mpr hG
  rw [integral_congr_ae (hrep.mono fun x hx => by rw [hx]), ← integral_const_mul]
  exact integral_mono hGw.memLp_grad.norm.integrable_sq
    ((isWeightedWeakGradient_weightedGradient P hg).memLp_grad.norm.integrable_sq.const_mul _)
    hGb

end DGPS.Lipschitz
