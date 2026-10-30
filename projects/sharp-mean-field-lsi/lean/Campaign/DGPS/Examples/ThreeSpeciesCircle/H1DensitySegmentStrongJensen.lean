import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentJensen
import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentStrongScalar

/-! Quantitative density-path Jensen. The gain controls the Haar L2 distance of
the ORIGINAL densities, with constants independent of the mixing weight. -/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem strong_segment_dirichlet_real (μ : ProbabilityMeasure (Torus 1)) (f : WeakH1Test μ) :
    dirichletEnergy μ f = ENNReal.ofReal (∫ x, ‖f.grad x‖ ^ 2 ∂(μ : Measure (Torus 1))) := by
  unfold dirichletEnergy
  rw [ofReal_integral_eq_lintegral_ofReal f.isWeak.memLp_grad.norm.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

private theorem strong_segment_native_energy_bound (μ : ProbabilityMeasure (Torus 1))
    (f : WeakH1Test μ) (p : ℝ) (hp : 0 ≤ p) (hPC : ENNReal.ofReal p ≤ poincareRate μ) :
    p * weightedVariance μ f.fn ≤ ∫ x, ‖f.grad x‖ ^ 2 ∂(μ : Measure (Torus 1)) := by
  by_cases hV : 0 < weightedVariance μ f.fn
  · have hh := (le_poincareRate_iff_forall μ _).mp hPC f hV
    rw [strong_segment_dirichlet_real, ← ENNReal.ofReal_mul hp] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ => sq_nonneg _)).mp hh
  · have hz : weightedVariance μ f.fn = 0 :=
      le_antisymm (not_lt.mp hV) (weightedVariance_nonneg _ _)
    rw [hz, mul_zero]
    exact integral_nonneg fun _ => sq_nonneg _

/-- The actual native Hessian controls the unweighted Haar L2 density
separation whenever the true segment density has the factual upper bound M. -/
theorem h1DensitySegment_native_hessian_lower (h r κ M : ℝ)
    (hr : 0 ≤ r) (hκ : 0 < κ) (hM : 0 < M)
    (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hupper : ∀ x, h1DensitySegmentValue u v t x ≤ M)
    (hPC : ENNReal.ofReal (r + κ) ≤
      poincareRate (densityMeasure (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht))) :
    let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
    let f := h1DensitySegmentRatio ρ σ u v hu hv hup hvp hρ hσ t ht
    (2 * κ / M) * (∫ x, (v x ^ 2 - u x ^ 2) ^ 2 ∂haar 1) ≤
      2 * (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure τ : Measure (Torus 1))) -
        2 * r * weightedVariance (densityMeasure τ) f.fn := by
  let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
  let f := h1DensitySegmentRatio ρ σ u v hu hv hup hvp hρ hσ t ht
  let P := h1DensitySegmentValue u v t
  let d := fun x => v x ^ 2 - u x ^ 2
  have hPc := h1DensitySegmentValue_continuous u v hu hv t
  have hp := h1DensitySegmentValue_positive u v hup hvp t ht
  have hdc : Continuous d := (hv.pow 2).sub (hu.pow 2)
  have hDI : Integrable (fun x => d x ^ 2) (haar 1) :=
    (hdc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hRI : Integrable (fun x => d x ^ 2 / P x) (haar 1) :=
    ((hdc.pow 2).div hPc (fun x => (hp x).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hV : weightedVariance (densityMeasure τ) f.fn = ∫ x, d x ^ 2 / P x ∂haar 1 := by
    unfold weightedVariance
    rw [h1DensitySegmentRatio_mean ρ σ u v hu hv hup hvp hρ hσ t ht]
    simp only [sub_zero]
    rw [Structural.budget_integral_densityMeasure]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change τ.density x * f.fn x ^ 2 = d x ^ 2 / P x
      dsimp only [τ]
      rw [h1DensitySegment_density]
      dsimp only [f, h1DensitySegmentRatio, P, d]
      field_simp [(hp x).ne']
      <;> ring
  have hND : (∫ x, d x ^ 2 ∂haar 1) ≤ M * weightedVariance (densityMeasure τ) f.fn := by
    rw [hV, ← integral_const_mul]
    apply integral_mono hDI (hRI.const_mul M)
    intro x
    calc
      _ = P x * (d x ^ 2 / P x) := by
        have hPx : P x ≠ 0 := (hp x).ne'
        field_simp [hPx]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hupper x) (div_nonneg (sq_nonneg _) (hp x).le)
  have hpc := strong_segment_native_energy_bound (densityMeasure τ) f (r + κ)
    (add_nonneg hr hκ.le) hPC
  have hscaled : (κ / M) * (∫ x, d x ^ 2 ∂haar 1) ≤ κ * weightedVariance (densityMeasure τ) f.fn := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hM]
    nlinarith only [mul_le_mul_of_nonneg_left hND hκ.le]
  change (2 * κ / M) * (∫ x, d x ^ 2 ∂haar 1) ≤
    2 * (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure τ : Measure (Torus 1))) -
      2 * r * weightedVariance (densityMeasure τ) f.fn
  rw [show 2 * κ / M = 2 * (κ / M) by ring]
  nlinarith only [hpc, hscaled]

private theorem strong_segment_density_difference (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v) :
    (∫ x, (σ.density x - ρ.density x) ^ 2 ∂haar 1) = ∫ x, (v x ^ 2 - u x ^ 2) ^ 2 ∂haar 1 := by
  apply integral_congr_ae
  filter_upwards [hρ, hσ] with x hx hy
  change (σ.sqrt x ^ 2 - ρ.sqrt x ^ 2) ^ 2 = _
  rw [hx, hy]

/-- Quantitative actual-cost Jensen with a factual uniform PC tube and upper
density bound. The next reference consumer derives both tube facts internally. -/
theorem h1DensitySegment_cost_strongJensen (h r κ M : ℝ)
    (hr : 0 ≤ r) (hκ : 0 < κ) (hM : 0 < M)
    (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (hupper : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, h1DensitySegmentValue u v t x ≤ M)
    (hPC : ∀ t : ℝ, ∀ ht : t ∈ Icc (0 : ℝ) 1,
      ENNReal.ofReal (r + κ) ≤
        poincareRate (densityMeasure (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht))) :
    ∀ θ : ℝ, ∀ hθ : θ ∈ Icc (0 : ℝ) 1,
      let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ θ hθ
      (ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal ≤
        (1 - θ) * ((ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal) +
          θ * ((ordinaryFisher h σ).toReal - 2 * r * (ordinaryEntropy h σ).toReal) -
            (κ / M) * θ * (1 - θ) * ∫ x, (σ.density x - ρ.density x) ^ 2 ∂haar 1 := by
  let F2 := fun t : ℝ => if ht : t ∈ Icc (0 : ℝ) 1 then
    let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
    let f := h1DensitySegmentRatio ρ σ u v hu hv hup hvp hρ hσ t ht
    2 * (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure τ : Measure (Torus 1))) -
      2 * r * weightedVariance (densityMeasure τ) f.fn else 0
  let A := (κ / M) * ∫ x, (v x ^ 2 - u x ^ 2) ^ 2 ∂haar 1
  have h1 := h1DensitySegmentPhi_hasDerivAt h r ρ σ u v hu hv hup hvp
  have h2 (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (h1DensitySegmentPhiDerivative h r ρ σ u v) (F2 t) t := by
    dsimp only [F2]
    rw [dif_pos ⟨ht.1.le, ht.2.le⟩]
    exact h1DensitySegmentPhiDerivative_native_hasDerivAt h r ρ σ u v hu hv hup hvp hρ hσ t ⟨ht.1.le, ht.2.le⟩
  have hlow (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : 2 * A ≤ F2 t := by
    dsimp only [F2]
    rw [dif_pos ⟨ht.1.le, ht.2.le⟩]
    have hh := h1DensitySegment_native_hessian_lower h r κ M hr hκ hM ρ σ u v hu hv hup hvp hρ hσ
      t ⟨ht.1.le, ht.2.le⟩ (hupper t ⟨ht.1.le, ht.2.le⟩) (hPC t ⟨ht.1.le, ht.2.le⟩)
    convert hh using 1 <;> dsimp only [A] <;> ring
  intro θ hθ
  have hj := h1DensitySegment_scalar_strongJensen (h1DensitySegmentPhi h r ρ σ u v)
    (h1DensitySegmentPhiDerivative h r ρ σ u v) F2 A h1 h2 hlow θ hθ
  have hep := h1DensitySegmentPhi_endpoints h r ρ σ u v hu hv hup hvp hρ hσ
  rw [h1DensitySegmentPhi_eq ρ σ u v hu hv hup hvp hρ hσ θ hθ h r, hep.1, hep.2] at hj
  have hnorm := strong_segment_density_difference ρ σ u v hρ hσ
  dsimp only [A] at hj
  rw [← hnorm] at hj
  convert hj using 1 <;> ring

/-- Quantitative reference consumer: both the common PC margin and upper
density bound are derived internally. The neighborhood and positive gain
precede EVERY smaller real rate, both endpoint laws and the mixing parameter. -/
theorem h1DensitySegment_cost_uniformStrongJensen_of_reference (h rMax p : ℝ)
    (hrMax : 0 ≤ rMax) (hp : rMax < p)
    (ω : AbsoluteDensity 1) (w : Torus 1 → ℝ) (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hω : ω.sqrt =ᵐ[haar 1] w) (hPC : ENNReal.ofReal p ≤ poincareRate (densityMeasure ω)) :
    ∃ q c : ℝ, 0 < q ∧ q ≤ 1 / 4 ∧ 0 < c ∧
      ∀ r : ℝ, 0 ≤ r → r ≤ rMax →
      ∀ (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ),
        ∀ (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x),
        ∀ (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v),
        (∀ x, (1 - q) ^ 2 * w x ^ 2 ≤ u x ^ 2) →
        (∀ x, u x ^ 2 ≤ (1 + q) ^ 2 * w x ^ 2) →
        (∀ x, (1 - q) ^ 2 * w x ^ 2 ≤ v x ^ 2) →
        (∀ x, v x ^ 2 ≤ (1 + q) ^ 2 * w x ^ 2) →
        ∀ θ : ℝ, ∀ hθ : θ ∈ Icc (0 : ℝ) 1,
          let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ θ hθ
          (ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal ≤
            (1 - θ) * ((ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal) +
              θ * ((ordinaryFisher h σ).toReal - 2 * r * (ordinaryEntropy h σ).toReal) -
                c * θ * (1 - θ) * ∫ x, (σ.density x - ρ.density x) ^ 2 ∂haar 1 := by
  obtain ⟨q, κ, hq, hq4, hκ, hmargin⟩ :=
    h1DensitySegment_poincare_margin_of_reference ω w hw hwp hω rMax p hrMax hp hPC
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (hw.pow 2).continuousOn
  let M := (1 + q) ^ 2 * (|B| + 1)
  have hM : 0 < M := by dsimp only [M]; positivity
  have hwB (x : Torus 1) : w x ^ 2 ≤ |B| + 1 := by
    have hh : w x ^ 2 ≤ B := by
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (w x))] using hB x (mem_univ x)
    linarith [le_abs_self B]
  refine ⟨q, κ / M, hq, hq4, div_pos hκ hM,
    fun r hr hrr ρ σ u v hu hv hup hvp hρ hσ hulo huhi hvlo hvhi θ hθ => ?_⟩
  have hPCr : ∀ t : ℝ, ∀ ht : t ∈ Icc (0 : ℝ) 1,
      ENNReal.ofReal (r + κ) ≤
        poincareRate (densityMeasure (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht)) :=
    fun t ht => (ENNReal.ofReal_le_ofReal (show r + κ ≤ rMax + κ by linarith)).trans
      (hmargin ρ σ u v hu hv hup hvp hρ hσ hulo huhi hvlo hvhi t ht)
  have huM (x : Torus 1) : u x ^ 2 ≤ M :=
    (huhi x).trans (mul_le_mul_of_nonneg_left (hwB x) (sq_nonneg _))
  have hvM (x : Torus 1) : v x ^ 2 ≤ M :=
    (hvhi x).trans (mul_le_mul_of_nonneg_left (hwB x) (sq_nonneg _))
  have hupper (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : Torus 1) :
      h1DensitySegmentValue u v t x ≤ M := by
    have h1 := mul_le_mul_of_nonneg_left (huM x) (sub_nonneg.mpr ht.2)
    have h2 := mul_le_mul_of_nonneg_left (hvM x) ht.1
    unfold h1DensitySegmentValue
    nlinarith only [h1, h2]
  exact h1DensitySegment_cost_strongJensen h r κ M hr hκ hM ρ σ u v hu hv hup hvp hρ hσ hupper hPCr θ hθ

end DGPS.Examples.ThreeSpeciesCircle
