import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentHessian
import Mathlib.Analysis.Convex.Deriv

/-! Strict density-segment Jensen from the genuine full-H1 Hessian. Segment
Poincare subrates are explicit factual inputs to the generic lemma; actual
near-reference consumers must derive them by bounded-density comparison. -/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem segment_dirichlet_real (μ : ProbabilityMeasure (Torus 1)) (f : WeakH1Test μ) :
    dirichletEnergy μ f = ENNReal.ofReal (∫ x, ‖f.grad x‖ ^ 2 ∂(μ : Measure (Torus 1))) := by
  have hi := f.isWeak.memLp_grad.norm.integrable_sq
  unfold dirichletEnergy
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _)]
  apply lintegral_congr
  intro x
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- Distinct original laws give strictly positive variance of the actual
constructed ratio, without a pointwise condition on their stored roots. -/
theorem h1DensitySegmentRatio_variance_pos (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (hne : densityMeasure ρ ≠ densityMeasure σ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
    let f := h1DensitySegmentRatio ρ σ u v hu hv hup hvp hρ hσ t ht
    0 < weightedVariance (densityMeasure τ) f.fn := by
  let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
  let f := h1DensitySegmentRatio ρ σ u v hu hv hup hvp hρ hσ t ht
  have hmean := h1DensitySegmentRatio_mean ρ σ u v hu hv hup hvp hρ hσ t ht
  have hV : weightedVariance (densityMeasure τ) f.fn =
      ∫ x, f.fn x ^ 2 ∂(densityMeasure τ : Measure (Torus 1)) := by
    unfold weightedVariance
    rw [hmean]
    simp only [sub_zero]
  have hp := h1DensitySegmentValue_positive u v hup hvp t ht
  have hc := h1DensitySegmentValue_continuous u v hu hv t
  have hfc : Continuous f.fn :=
    ((hv.pow 2).sub (hu.pow 2)).div hc (fun x => (hp x).ne')
  obtain ⟨P, hPμ, _⟩ := ordinaryRoot_boundedReference τ _ hc.sqrt
    (fun x => Real.sqrt_pos.mpr (hp x)) (Eventually.of_forall fun _ => rfl)
  have hac : haar 1 ≪ (densityMeasure τ : Measure (Torus 1)) := by
    rw [← hPμ]
    exact P.haar_ac_measure
  by_contra hnot
  have hzero : weightedVariance (densityMeasure τ) f.fn = 0 :=
    le_antisymm (not_lt.mp hnot) (weightedVariance_nonneg _ _)
  rw [hV] at hzero
  have hsq := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun _ => sq_nonneg _) f.isWeak.memLp.integrable_sq).mp hzero
  have hfn : f.fn =ᵐ[haar 1] 0 := by
    filter_upwards [hsq.filter_mono hac.ae_le] with x hx
    exact (sq_eq_zero_iff).mp hx
  have hpoint := MeasureTheory.Measure.eq_of_ae_eq hfn hfc continuous_const
  have hd (x : Torus 1) : v x ^ 2 = u x ^ 2 := by
    have hz := congrFun hpoint x
    change (v x ^ 2 - u x ^ 2) / h1DensitySegmentValue u v t x = 0 at hz
    have he := (div_eq_iff (hp x).ne').mp hz
    simp only [zero_mul] at he
    exact sub_eq_zero.mp he
  apply hne
  apply Subtype.ext
  apply withDensity_congr_ae
  filter_upwards [hρ, hσ] with x hx hy
  apply congrArg ENNReal.ofReal
  change ρ.sqrt x ^ 2 = σ.sqrt x ^ 2
  rw [hx, hy]
  exact (hd x).symm

/-- A factual common native Poincare margin makes the genuine density-path
Hessian strictly positive. The ratio-domain and nonzero variance are derived. -/
theorem h1DensitySegment_native_hessian_pos (h r κ : ℝ) (hr : 0 ≤ r) (hκ : 0 < κ)
    (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (hne : densityMeasure ρ ≠ densityMeasure σ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hPC : ENNReal.ofReal (r + κ) ≤
      poincareRate (densityMeasure (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht))) :
    let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
    let f := h1DensitySegmentRatio ρ σ u v hu hv hup hvp hρ hσ t ht
    0 < 2 * (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure τ : Measure (Torus 1))) -
      2 * r * weightedVariance (densityMeasure τ) f.fn := by
  let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
  let f := h1DensitySegmentRatio ρ σ u v hu hv hup hvp hρ hσ t ht
  have hV := h1DensitySegmentRatio_variance_pos ρ σ u v hu hv hup hvp hρ hσ hne t ht
  have hPCf := (le_poincareRate_iff_forall _ _).mp hPC f hV
  rw [segment_dirichlet_real, ← ENNReal.ofReal_mul (add_nonneg hr hκ.le)] at hPCf
  have he := (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg fun _ => sq_nonneg _)).mp hPCf
  have hδ := mul_pos hκ hV
  change 0 < 2 * (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure τ : Measure (Torus 1))) -
    2 * r * weightedVariance (densityMeasure τ) f.fn
  nlinarith only [he, hδ]

/-- Generic strict convexity with a factual segment Poincare margin. No Hessian
or convexity hypothesis is supplied; both actual parameter derivatives were proved. -/
theorem h1DensitySegmentPhi_strictConvexOn (h r κ : ℝ) (hr : 0 ≤ r) (hκ : 0 < κ)
    (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (hne : densityMeasure ρ ≠ densityMeasure σ)
    (hPC : ∀ t : ℝ, ∀ ht : t ∈ Icc (0 : ℝ) 1,
      ENNReal.ofReal (r + κ) ≤
        poincareRate (densityMeasure (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht))) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (h1DensitySegmentPhi h r ρ σ u v) := by
  apply strictConvexOn_of_deriv2_pos (convex_Icc _ _)
  · intro t ht
    exact (h1DensitySegmentPhi_hasDerivAt h r ρ σ u v hu hv hup hvp t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have heq : deriv (h1DensitySegmentPhi h r ρ σ u v) =ᶠ[𝓝 t]
        h1DensitySegmentPhiDerivative h r ρ σ u v := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact (h1DensitySegmentPhi_hasDerivAt h r ρ σ u v hu hv hup hvp s ⟨hs.1.le, hs.2.le⟩).deriv
    have hD := (h1DensitySegmentPhiDerivative_native_hasDerivAt h r ρ σ u v hu hv hup hvp hρ hσ t
      ⟨ht.1.le, ht.2.le⟩).congr_of_eventuallyEq heq
    change 0 < deriv (deriv (h1DensitySegmentPhi h r ρ σ u v)) t
    rw [hD.deriv]
    exact h1DensitySegment_native_hessian_pos h r κ hr hκ ρ σ u v hu hv hup hvp hρ hσ hne t
      ⟨ht.1.le, ht.2.le⟩ (hPC t ⟨ht.1.le, ht.2.le⟩)

/-- The common segment Poincare margin is DERIVED from the same reference
subrate and actual pointwise endpoint density bounds. It is not a public premise. -/
theorem h1DensitySegment_poincare_margin_of_reference (ω : AbsoluteDensity 1)
    (w : Torus 1 → ℝ) (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hω : ω.sqrt =ᵐ[haar 1] w) (r p : ℝ) (hr : 0 ≤ r) (hrp : r < p)
    (hPC : ENNReal.ofReal p ≤ poincareRate (densityMeasure ω)) :
    ∃ q κ : ℝ, 0 < q ∧ q ≤ 1 / 4 ∧ 0 < κ ∧
      ∀ (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ),
        ∀ (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x),
        ∀ (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v),
        (∀ x, (1 - q) ^ 2 * w x ^ 2 ≤ u x ^ 2) →
        (∀ x, u x ^ 2 ≤ (1 + q) ^ 2 * w x ^ 2) →
        (∀ x, (1 - q) ^ 2 * w x ^ 2 ≤ v x ^ 2) →
        (∀ x, v x ^ 2 ≤ (1 + q) ^ 2 * w x ^ 2) →
        ∀ t : ℝ, ∀ ht : t ∈ Icc (0 : ℝ) 1,
          ENNReal.ofReal (r + κ) ≤
            poincareRate (densityMeasure (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht)) := by
  have hp : 0 < p := hr.trans_lt hrp
  let q := min (1 / 4 : ℝ) ((p - r) / (8 * (p + 1)))
  have hq : 0 < q := lt_min (by norm_num) (div_pos (sub_pos.mpr hrp) (by positivity))
  have hq4 : q ≤ 1 / 4 := min_le_left _ _
  have hqp : q * (p + 1) ≤ (p - r) / 8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * (p + 1))).mp
      (min_le_right (1 / 4 : ℝ) ((p - r) / (8 * (p + 1))))
    change q * (8 * (p + 1)) ≤ p - r at hh
    nlinarith
  have hprod : 2 * q * (p + r) ≤ (p - r) / 2 := by
    nlinarith [mul_nonneg hq.le (show 0 ≤ p - r + 2 by linarith)]
  let c := ((1 - q) ^ 2 / (1 + q) ^ 2) * p
  have hrc : r < c := by
    dsimp only [c]
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 1 + q))).mpr
    nlinarith [mul_nonneg (sub_pos.mpr hrp).le (sq_nonneg q)]
  let κ := (c - r) / 2
  have hκ : 0 < κ := half_pos (sub_pos.mpr hrc)
  obtain ⟨P, hPμ, hPd⟩ := ordinaryRoot_boundedReference ω w hw hwp hω
  have hPprob : (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) =
      densityMeasure ω := ProbabilityMeasure.toMeasure_injective hPμ
  refine ⟨q, κ, hq, hq4, hκ, fun ρ σ u v hu hv hup hvp hρ hσ hulo huhi hvlo hvhi t ht => ?_⟩
  let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
  let T := h1DensitySegmentValue u v t
  have hc := h1DensitySegmentValue_continuous u v hu hv t
  have hpos := h1DensitySegmentValue_positive u v hup hvp t ht
  obtain ⟨Q, hQμ, hQd⟩ := ordinaryRoot_boundedReference τ _ hc.sqrt
    (fun x => Real.sqrt_pos.mpr (hpos x)) (Eventually.of_forall fun _ => rfl)
  have hQprob : (⟨Q.measure, Q.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) =
      densityMeasure τ := ProbabilityMeasure.toMeasure_injective hQμ
  have hQval (x : Torus 1) : Q.density x = T x := by
    rw [hQd]
    exact Real.sq_sqrt (hpos x).le
  have hlo : ∀ᵐ x ∂haar 1, (1 - q) ^ 2 * P.density x ≤ Q.density x :=
    Eventually.of_forall fun x => by
      rw [hPd, hQval]
      have h1 := mul_le_mul_of_nonneg_left (hulo x) (sub_nonneg.mpr ht.2)
      have h2 := mul_le_mul_of_nonneg_left (hvlo x) ht.1
      dsimp only [T, h1DensitySegmentValue]
      nlinarith only [h1, h2]
  have hhi : ∀ᵐ x ∂haar 1, Q.density x ≤ (1 + q) ^ 2 * P.density x :=
    Eventually.of_forall fun x => by
      rw [hPd, hQval]
      have h1 := mul_le_mul_of_nonneg_left (huhi x) (sub_nonneg.mpr ht.2)
      have h2 := mul_le_mul_of_nonneg_left (hvhi x) ht.1
      dsimp only [T, h1DensitySegmentValue]
      nlinarith only [h1, h2]
  have hcomp := boundedReference_poincare_sandwich P Q
    (sq_pos_of_pos (by linarith : 0 < 1 - q))
    (sq_pos_of_pos (by positivity : 0 < 1 + q)) hlo hhi
  rw [hPprob, hQprob] at hcomp
  have hpQ := (mul_le_mul' (le_refl (ENNReal.ofReal ((1 - q) ^ 2 / (1 + q) ^ 2))) hPC).trans hcomp
  rw [← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (sq_nonneg _))] at hpQ
  exact (ENNReal.ofReal_le_ofReal (show r + κ ≤ c by dsimp only [κ]; linarith)).trans hpQ

/-- Strict Jensen for the actual density-coordinate cost, with the segment
Poincare inequality derived internally from a genuine reference comparison. -/
theorem h1DensitySegment_strictJensen_of_reference (h r p : ℝ) (hr : 0 ≤ r) (hrp : r < p)
    (ω : AbsoluteDensity 1) (w : Torus 1 → ℝ) (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hω : ω.sqrt =ᵐ[haar 1] w) (hPC : ENNReal.ofReal p ≤ poincareRate (densityMeasure ω)) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 4 ∧
      ∀ (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ),
        ∀ (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x),
        ∀ (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v),
        densityMeasure ρ ≠ densityMeasure σ →
        (∀ x, (1 - q) ^ 2 * w x ^ 2 ≤ u x ^ 2) →
        (∀ x, u x ^ 2 ≤ (1 + q) ^ 2 * w x ^ 2) →
        (∀ x, (1 - q) ^ 2 * w x ^ 2 ≤ v x ^ 2) →
        (∀ x, v x ^ 2 ≤ (1 + q) ^ 2 * w x ^ 2) →
        ∀ θ : ℝ, 0 < θ → θ < 1 →
          h1DensitySegmentPhi h r ρ σ u v θ <
            (1 - θ) * h1DensitySegmentPhi h r ρ σ u v 0 +
              θ * h1DensitySegmentPhi h r ρ σ u v 1 := by
  obtain ⟨q, κ, hq, hq4, hκ, hmargin⟩ :=
    h1DensitySegment_poincare_margin_of_reference ω w hw hwp hω r p hr hrp hPC
  refine ⟨q, hq, hq4, fun ρ σ u v hu hv hup hvp hρ hσ hne hulo huhi hvlo hvhi θ hθ0 hθ1 => ?_⟩
  have hSC := h1DensitySegmentPhi_strictConvexOn h r κ hr hκ ρ σ u v hu hv hup hvp hρ hσ hne
    (hmargin ρ σ u v hu hv hup hvp hρ hσ hulo huhi hvlo hvhi)
  have hj := hSC.2 (by constructor <;> norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≠ 1)
    (sub_pos.mpr hθ1) hθ0 (by ring : (1 - θ) + θ = 1)
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add] using hj

private theorem segment_ordinaryCost_congr (h r : ℝ) (ρ σ : AbsoluteDensity 1)
    (he : ρ.density =ᵐ[haar 1] σ.density) :
    (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal =
      (ordinaryFisher h σ).toReal - 2 * r * (ordinaryEntropy h σ).toReal := by
  have hroot := AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq he
  have hg := ((isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hroot
    (EventuallyEq.refl _ _)).ae_eq (isWeakGradient_weakGradient σ.sqrt_mem)
  have hI : ordinaryFisher h ρ = ordinaryFisher h σ := by
    rw [ordinaryFisher_eq, ordinaryFisher_eq]
    congr 1
    apply integral_congr_ae
    filter_upwards [hroot, hg] with x hx hG
    rw [hx, hG]
  have hμ : densityMeasure ρ = densityMeasure σ := by
    apply Subtype.ext
    apply withDensity_congr_ae
    exact he.mono fun x hx => congrArg ENNReal.ofReal hx
  have hH : ordinaryEntropy h ρ = ordinaryEntropy h σ := by
    unfold ordinaryEntropy
    rw [hμ]
  rw [hI, hH]

/-- Endpoint costs are the actual original laws, not merely chosen continuous
representatives or new law witnesses. -/
theorem h1DensitySegmentPhi_endpoints (h r : ℝ) (ρ σ : AbsoluteDensity 1)
    (u v : Torus 1 → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v) :
    h1DensitySegmentPhi h r ρ σ u v 0 =
      (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal ∧
    h1DensitySegmentPhi h r ρ σ u v 1 =
      (ordinaryFisher h σ).toReal - 2 * r * (ordinaryEntropy h σ).toReal := by
  have ht0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have ht1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have he0 := h1DensitySegment_density_ae ρ σ u v hu hv hup hvp hρ hσ 0 ht0
  have he1 := h1DensitySegment_density_ae ρ σ u v hu hv hup hvp hρ hσ 1 ht1
  simp only [sub_zero, one_mul, zero_mul, add_zero] at he0
  simp only [sub_self, zero_mul, one_mul, zero_add] at he1
  exact ⟨(h1DensitySegmentPhi_eq ρ σ u v hu hv hup hvp hρ hσ 0 ht0 h r).trans
      (segment_ordinaryCost_congr h r _ ρ he0),
    (h1DensitySegmentPhi_eq ρ σ u v hu hv hup hvp hρ hσ 1 ht1 h r).trans
      (segment_ordinaryCost_congr h r _ σ he1)⟩

/-- Genuine strict local merging inequality on the original positive-H1 laws.
The entire segment Poincare margin is derived from the actual reference subrate
and endpoint bounds, and both endpoint costs are the original laws. -/
theorem h1DensitySegment_cost_strictJensen_of_reference (h r p : ℝ) (hr : 0 ≤ r) (hrp : r < p)
    (ω : AbsoluteDensity 1) (w : Torus 1 → ℝ) (hw : Continuous w) (hwp : ∀ x, 0 < w x)
    (hω : ω.sqrt =ᵐ[haar 1] w) (hPC : ENNReal.ofReal p ≤ poincareRate (densityMeasure ω)) :
    ∃ q : ℝ, 0 < q ∧ q ≤ 1 / 4 ∧
      ∀ (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ),
        ∀ (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x),
        ∀ (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v),
        densityMeasure ρ ≠ densityMeasure σ →
        (∀ x, (1 - q) ^ 2 * w x ^ 2 ≤ u x ^ 2) →
        (∀ x, u x ^ 2 ≤ (1 + q) ^ 2 * w x ^ 2) →
        (∀ x, (1 - q) ^ 2 * w x ^ 2 ≤ v x ^ 2) →
        (∀ x, v x ^ 2 ≤ (1 + q) ^ 2 * w x ^ 2) →
        ∀ θ : ℝ, ∀ hθ0 : 0 < θ, ∀ hθ1 : θ < 1,
          let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ θ ⟨hθ0.le, hθ1.le⟩
          (ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal <
            (1 - θ) * ((ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal) +
              θ * ((ordinaryFisher h σ).toReal - 2 * r * (ordinaryEntropy h σ).toReal) := by
  obtain ⟨q, hq, hq4, hj⟩ := h1DensitySegment_strictJensen_of_reference h r p hr hrp ω w hw hwp hω hPC
  refine ⟨q, hq, hq4, fun ρ σ u v hu hv hup hvp hρ hσ hne hulo huhi hvlo hvhi θ hθ0 hθ1 => ?_⟩
  have hh := hj ρ σ u v hu hv hup hvp hρ hσ hne hulo huhi hvlo hvhi θ hθ0 hθ1
  have hep := h1DensitySegmentPhi_endpoints h r ρ σ u v hu hv hup hvp hρ hσ
  rw [h1DensitySegmentPhi_eq ρ σ u v hu hv hup hvp hρ hσ θ ⟨hθ0.le, hθ1.le⟩ h r,
    hep.1, hep.2] at hh
  exact hh

end DGPS.Examples.ThreeSpeciesCircle
