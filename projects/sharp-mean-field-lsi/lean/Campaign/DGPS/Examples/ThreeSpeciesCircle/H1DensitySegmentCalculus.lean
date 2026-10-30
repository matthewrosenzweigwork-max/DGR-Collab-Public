import DGPS.Examples.ThreeSpeciesCircle.H1FixedBarycenterSplit

/-! Actual positive-H1 density segments. The original absolute laws and chosen
weak gradients are retained; no smooth density or ratio-domain assumption is used. -/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Density interpolation between continuous positive representatives of the
original square roots. -/
def h1DensitySegmentValue (u v : Torus 1 → ℝ) (t : ℝ) (x : Torus 1) : ℝ :=
  (1 - t) * u x ^ 2 + t * v x ^ 2

def h1DensitySegmentGradient (ρ σ : AbsoluteDensity 1)
    (u v : Torus 1 → ℝ) (t : ℝ) (x : Torus 1) : Tangent 1 :=
  (2 * (1 - t) * u x) • weakGradient ρ.sqrt ρ.sqrt_mem x +
    (2 * t * v x) • weakGradient σ.sqrt σ.sqrt_mem x

theorem h1DensitySegmentValue_continuous (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (t : ℝ) :
    Continuous (h1DensitySegmentValue u v t) :=
  ((hu.pow 2).const_mul (1 - t)).add ((hv.pow 2).const_mul t)

theorem h1DensitySegmentValue_positive (u v : Torus 1 → ℝ)
    (hu : ∀ x, 0 < u x) (hv : ∀ x, 0 < v x) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ x, 0 < h1DensitySegmentValue u v t x := by
  intro x
  by_cases hz : t = 0
  · simp only [h1DensitySegmentValue, hz, sub_zero, one_mul, zero_mul, add_zero]
    exact sq_pos_of_pos (hu x)
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg _))
      (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm hz)) (sq_pos_of_pos (hv x)))

theorem h1DensitySegmentValue_weak (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v) (t : ℝ) :
    IsWeakGradient (h1DensitySegmentValue u v t) (h1DensitySegmentGradient ρ σ u v t) := by
  have hu := (isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hρ (EventuallyEq.refl _ _)
  have hv := (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hσ (EventuallyEq.refl _ _)
  have hh := ((hu.mul_one_dim hu).smul (1 - t)).add ((hv.mul_one_dim hv).smul t)
  refine hh.congr_ae (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · dsimp only [h1DensitySegmentValue]
    ring
  · ext j
    simp only [h1DensitySegmentGradient, Pi.add_apply, Pi.smul_apply,
      PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

/-- The actual normalized absolute H1 law at every segment parameter. -/
def h1DensitySegment (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : AbsoluteDensity 1 where
  sqrt := fun x => Real.sqrt (h1DensitySegmentValue u v t x)
  sqrt_mem := by
    exact ⟨_, continuousH1_sqrt_gradient (h1DensitySegmentValue_weak ρ σ u v hρ hσ t)
      (h1DensitySegmentValue_continuous u v hu hv t)
      (h1DensitySegmentValue_positive u v hup hvp t ht)⟩
  sqrt_nonneg := Eventually.of_forall fun x => Real.sqrt_nonneg _
  mass_one := by
    have huW := (isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hρ (EventuallyEq.refl _ _)
    have hvW := (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hσ (EventuallyEq.refl _ _)
    have huI : ∫ x, u x ^ 2 ∂haar 1 = 1 :=
      (integral_congr_ae (hρ.mono fun x hx => congrArg (fun a : ℝ => a ^ 2) hx)).symm.trans ρ.mass_one
    have hvI : ∫ x, v x ^ 2 ∂haar 1 = 1 :=
      (integral_congr_ae (hσ.mono fun x hx => congrArg (fun a : ℝ => a ^ 2) hx)).symm.trans σ.mass_one
    simp_rw [Real.sq_sqrt (h1DensitySegmentValue_positive u v hup hvp t ht _).le]
    unfold h1DensitySegmentValue
    rw [integral_add (huW.memLp.integrable_sq.const_mul _) (hvW.memLp.integrable_sq.const_mul _),
      integral_const_mul, integral_const_mul, huI, hvI]
    ring

theorem h1DensitySegment_density (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : Torus 1) :
    (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht).density x =
      h1DensitySegmentValue u v t x := by
  exact Real.sq_sqrt (h1DensitySegmentValue_positive u v hup hvp t ht x).le

/-- The density interpolation represents the weighted mixture of the original
laws even when their stored square roots have arbitrary null-set values. -/
theorem h1DensitySegment_density_ae (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht).density =ᵐ[haar 1]
      (fun x => (1 - t) * ρ.density x + t * σ.density x) := by
  filter_upwards [hρ, hσ] with x hx hy
  rw [h1DensitySegment_density]
  simp only [h1DensitySegmentValue, AbsoluteDensity.density, hx, hy]

/-- The genuine Haar weak gradient of the density difference divided by the
segment density. In particular the ratio belongs to the original native weak-H1
domain of the segment law; this first statement retains the precise Haar gradient. -/
theorem h1DensitySegment_ratio_weak (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    IsWeakGradient
      (fun x => (v x ^ 2 - u x ^ 2) / h1DensitySegmentValue u v t x)
      (fun x => (h1DensitySegmentValue u v t x ^ 2)⁻¹ •
        (h1DensitySegmentValue u v t x •
            ((2 * v x) • weakGradient σ.sqrt σ.sqrt_mem x -
              (2 * u x) • weakGradient ρ.sqrt ρ.sqrt_mem x) -
          (v x ^ 2 - u x ^ 2) • h1DensitySegmentGradient ρ σ u v t x)) := by
  have huW := (isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hρ (EventuallyEq.refl _ _)
  have hvW := (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hσ (EventuallyEq.refl _ _)
  have hD : IsWeakGradient (fun x => v x ^ 2 - u x ^ 2)
      (fun x => (2 * v x) • weakGradient σ.sqrt σ.sqrt_mem x -
        (2 * u x) • weakGradient ρ.sqrt ρ.sqrt_mem x) := by
    have hh := (hvW.mul_one_dim hvW).add ((huW.mul_one_dim huW).smul (-1))
    refine hh.congr_ae (Eventually.of_forall fun x => by ring)
      (Eventually.of_forall fun x => ?_)
    ext j
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  have hT := h1DensitySegmentValue_weak ρ σ u v hρ hσ t
  have hc := h1DensitySegmentValue_continuous u v hu hv t
  have hp := h1DensitySegmentValue_positive u v hup hvp t ht
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  have hi := hT.inv_of_pos hc (hp x0) (fun x => hx0 (Set.mem_univ x))
  have hh := hD.mul_one_dim hi
  refine hh.congr_ae (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · simp only [pow_two, div_eq_mul_inv]
  · ext j
    simp only [Pi.sub_apply, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [(hp x).ne']
    <;> ring

end DGPS.Examples.ThreeSpeciesCircle
