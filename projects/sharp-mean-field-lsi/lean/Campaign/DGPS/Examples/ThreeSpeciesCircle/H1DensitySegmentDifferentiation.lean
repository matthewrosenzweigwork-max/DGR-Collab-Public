import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentCalculus
import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentBounds

/-! Native weighted ratio domains and genuine parameter calculus for positive H1
density segments. No segment Poincare or convexity conclusion is assumed here. -/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual original native weak-H1 ratio, with the same explicit Haar weak
gradient derived from the original endpoint weak gradients. -/
def h1DensitySegmentRatio (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    WeakH1Test (densityMeasure (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht)) where
  fn := fun x => (v x ^ 2 - u x ^ 2) / h1DensitySegmentValue u v t x
  grad := fun x => (h1DensitySegmentValue u v t x ^ 2)⁻¹ •
    (h1DensitySegmentValue u v t x •
        ((2 * v x) • weakGradient σ.sqrt σ.sqrt_mem x -
          (2 * u x) • weakGradient ρ.sqrt ρ.sqrt_mem x) -
      (v x ^ 2 - u x ^ 2) • h1DensitySegmentGradient ρ σ u v t x)
  isWeak := by
    let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
    have hc := (h1DensitySegmentValue_continuous u v hu hv t).sqrt
    have hp : ∀ x, 0 < Real.sqrt (h1DensitySegmentValue u v t x) := fun x =>
      Real.sqrt_pos.mpr (h1DensitySegmentValue_positive u v hup hvp t ht x)
    obtain ⟨P, hPμ, _⟩ := ordinaryRoot_boundedReference τ _ hc hp
      (Eventually.of_forall fun _ => rfl)
    have hPprob : (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) =
        densityMeasure τ := ProbabilityMeasure.toMeasure_injective hPμ
    rw [← hPprob]
    exact (isMeasureWeakGradient_iff P).2 ((isWeightedWeakGradient_iff P).2
      (h1DensitySegment_ratio_weak ρ σ u v hu hv hup hvp hρ hσ t ht))

/-- The ratio has genuine mean zero under the SAME interpolated law. -/
theorem h1DensitySegmentRatio_mean (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ x, (h1DensitySegmentRatio ρ σ u v hu hv hup hvp hρ hσ t ht).fn x
      ∂(densityMeasure (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht) : Measure (Torus 1)) = 0 := by
  rw [Structural.budget_integral_densityMeasure]
  change (∫ x, (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht).density x *
    ((v x ^ 2 - u x ^ 2) / h1DensitySegmentValue u v t x) ∂haar 1) = 0
  have he (x : Torus 1) :
      (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht).density x *
        ((v x ^ 2 - u x ^ 2) / h1DensitySegmentValue u v t x) = v x ^ 2 - u x ^ 2 := by
    rw [h1DensitySegment_density]
    field_simp [(h1DensitySegmentValue_positive u v hup hvp t ht x).ne']
  simp_rw [he]
  have huW := (isWeakGradient_weakGradient ρ.sqrt_mem).congr_ae hρ (EventuallyEq.refl _ _)
  have hvW := (isWeakGradient_weakGradient σ.sqrt_mem).congr_ae hσ (EventuallyEq.refl _ _)
  have huI : ∫ x, u x ^ 2 ∂haar 1 = 1 :=
    (integral_congr_ae (hρ.mono fun x hx => congrArg (fun a : ℝ => a ^ 2) hx)).symm.trans ρ.mass_one
  have hvI : ∫ x, v x ^ 2 ∂haar 1 = 1 :=
    (integral_congr_ae (hσ.mono fun x hx => congrArg (fun a : ℝ => a ^ 2) hx)).symm.trans σ.mass_one
  rw [integral_sub hvW.memLp.integrable_sq huW.memLp.integrable_sq, hvI, huI, sub_self]

/-- The nonlinear part of the actual density-path Fisher-minus-entropy
integrand. Reference-score terms are affine in the density and its weak gradient. -/
def h1SegmentCostIntegrand (r p d a b t : ℝ) : ℝ :=
  (a + t * b) ^ 2 / (p + t * d) - 2 * r * ((p + t * d) * Real.log (p + t * d))

def h1SegmentCostDerivative (r p d a b t : ℝ) : ℝ :=
  (2 * b) * ((a + t * b) / (p + t * d)) -
    d * ((a + t * b) ^ 2 / (p + t * d) ^ 2) -
      (2 * r * d) * (Real.log (p + t * d) + 1)

/-- Honest scalar first differentiation at every positive density value. -/
theorem h1SegmentCostIntegrand_hasDerivAt (r p d a b t : ℝ) (hp : 0 < p + t * d) :
    HasDerivAt (h1SegmentCostIntegrand r p d a b)
      (h1SegmentCostDerivative r p d a b t) t := by
  have hA : HasDerivAt (fun s : ℝ => a + s * b) b t := by
    simpa using ((hasDerivAt_id t).mul_const b).const_add a
  have hP : HasDerivAt (fun s : ℝ => p + s * d) d t := by
    simpa using ((hasDerivAt_id t).mul_const d).const_add p
  have hI := (hA.pow 2).div hP hp.ne'
  have hH := hP.mul (hP.log hp.ne')
  convert hI.sub (hH.const_mul (2 * r)) using 1
  · rfl
  · dsimp only [h1SegmentCostDerivative]
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply]
    field_simp [hp.ne'] <;> ring_nf

/-- The true pointwise second derivative. Its numerator is the density times
the weak derivative of the ratio, not a spatial derivative of the H1 gradient. -/
theorem h1SegmentCostDerivative_hasDerivAt (r p d a b t : ℝ) (hp : 0 < p + t * d) :
    HasDerivAt (h1SegmentCostDerivative r p d a b)
      (2 * (b * (p + t * d) - d * (a + t * b)) ^ 2 / (p + t * d) ^ 3 -
        2 * r * d ^ 2 / (p + t * d)) t := by
  have hA : HasDerivAt (fun s : ℝ => a + s * b) b t := by
    simpa using ((hasDerivAt_id t).mul_const b).const_add a
  have hP : HasDerivAt (fun s : ℝ => p + s * d) d t := by
    simpa using ((hasDerivAt_id t).mul_const d).const_add p
  have h1 := (hA.div hP hp.ne').const_mul (2 * b)
  have h2 := ((hA.pow 2).div (hP.pow 2) (pow_ne_zero 2 hp.ne')).const_mul d
  have h3 := ((hP.log hp.ne').add_const 1).const_mul (2 * r * d)
  convert (h1.sub h2).sub h3 using 1
  · rfl
  · simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply]
    field_simp [hp.ne'] <;> ring_nf

/-- Explicit parameter-uniform first-derivative majorant. With L2 spatial
gradients a,b its right side is genuinely L1; no spatial gradient bound is needed. -/
theorem h1SegmentCostDerivative_abs_le (r p d a b t K T : ℝ)
    (hK : 0 ≤ K) (hT : 0 ≤ T) (ht : |t| ≤ T)
    (hp : 0 < p + t * d) (hd : |d| ≤ K)
    (hl : |Real.log (p + t * d)| ≤ K) (hi : |(p + t * d)⁻¹| ≤ K) :
    |h1SegmentCostDerivative r p d a b t| ≤
      (K + K ^ 3) * (|a| + T * |b|) ^ 2 + K * b ^ 2 +
        2 * |r| * K * (K + 1) := by
  let A := a + t * b
  let V := |a| + T * |b|
  have hV : 0 ≤ V := add_nonneg (abs_nonneg _) (mul_nonneg hT (abs_nonneg _))
  have hAV : |A| ≤ V := by
    calc
      |A| ≤ |a| + |t * b| := abs_add_le a (t * b)
      _ = |a| + |t| * |b| := by rw [abs_mul]
      _ ≤ V := by dsimp only [V]; exact add_le_add_right (mul_le_mul_of_nonneg_right ht (abs_nonneg b)) _
  have hA2 : A ^ 2 ≤ V ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg A) hV).2 hAV
  have hi2 : |(p + t * d)⁻¹| ^ 2 ≤ K ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) hK).2 hi
  have h1 : |(2 * b) * (A / (p + t * d))| ≤ K * (V ^ 2 + b ^ 2) := by
    calc
      _ = (2 * |b| * |A|) * |(p + t * d)⁻¹| := by
        rw [div_eq_mul_inv, abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ (A ^ 2 + b ^ 2) * K := by
        apply mul_le_mul _ hi (abs_nonneg _) (by positivity)
        nlinarith [sq_nonneg (|A| - |b|), sq_abs A, sq_abs b]
      _ ≤ _ := by
        calc
          (A ^ 2 + b ^ 2) * K = K * (A ^ 2 + b ^ 2) := by ring
          _ ≤ K * (V ^ 2 + b ^ 2) := mul_le_mul_of_nonneg_left (add_le_add_left hA2 _) hK
  have h2 : |d * (A ^ 2 / (p + t * d) ^ 2)| ≤ K ^ 3 * V ^ 2 := by
    calc
      _ = |d| * A ^ 2 * |(p + t * d)⁻¹| ^ 2 := by
        rw [div_eq_mul_inv, ← inv_pow]
        simp only [abs_mul, abs_pow, sq_abs]
        ring
      _ ≤ K * V ^ 2 * K ^ 2 := by gcongr
      _ = _ := by ring
  have hlog : |Real.log (p + t * d) + 1| ≤ K + 1 :=
    (abs_add_le _ _).trans (by simpa using add_le_add_right hl 1)
  have h3 : |(2 * r * d) * (Real.log (p + t * d) + 1)| ≤ 2 * |r| * K * (K + 1) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    gcongr
  have htri : |h1SegmentCostDerivative r p d a b t| ≤
      |(2 * b) * (A / (p + t * d))| + |d * (A ^ 2 / (p + t * d) ^ 2)| +
        |(2 * r * d) * (Real.log (p + t * d) + 1)| := by
    unfold h1SegmentCostDerivative
    dsimp only [A]
    calc
      _ ≤ |(2 * b) * ((a + t * b) / (p + t * d)) -
          d * ((a + t * b) ^ 2 / (p + t * d) ^ 2)| +
            |(2 * r * d) * (Real.log (p + t * d) + 1)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
          ((2 * b) * ((a + t * b) / (p + t * d)) - d * ((a + t * b) ^ 2 / (p + t * d) ^ 2))
          0 ((2 * r * d) * (Real.log (p + t * d) + 1))
      _ ≤ _ := by
        gcongr
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le
          ((2 * b) * ((a + t * b) / (p + t * d))) 0 (d * ((a + t * b) ^ 2 / (p + t * d) ^ 2))
  exact htri.trans (by dsimp only [V] at h1 h2; nlinarith only [h1, h2, h3])

/-- The second-derivative majorant depends only on endpoint L2 gradients and
actual compact coefficient bounds. The Wronskian numerator is parameter-independent. -/
theorem h1SegmentCostSecondDerivative_abs_le (r p d a b t K : ℝ)
    (hK : 0 ≤ K) (hp : 0 < p + t * d) (hpK : |p| ≤ K) (hd : |d| ≤ K)
    (hi : |(p + t * d)⁻¹| ≤ K) :
    |2 * (b * (p + t * d) - d * (a + t * b)) ^ 2 / (p + t * d) ^ 3 -
        2 * r * d ^ 2 / (p + t * d)| ≤
      2 * K ^ 5 * (|a| + |b|) ^ 2 + 2 * |r| * K ^ 3 := by
  have hW : |b * p - d * a| ≤ K * (|a| + |b|) := by
    calc
      _ ≤ |b * p| + |d * a| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (b * p) 0 (d * a)
      _ = |b| * |p| + |d| * |a| := by rw [abs_mul, abs_mul]
      _ ≤ |b| * K + K * |a| := by gcongr
      _ = _ := by ring
  have hW2 : (b * p - d * a) ^ 2 ≤ K ^ 2 * (|a| + |b|) ^ 2 := by
    have ht := (sq_le_sq₀ (abs_nonneg (b * p - d * a)) (by positivity : 0 ≤ K * (|a| + |b|))).2 hW
    simpa only [sq_abs, mul_pow] using ht
  have hd2 : d ^ 2 ≤ K ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg d) hK).2 hd
  have hi0 : 0 ≤ (p + t * d)⁻¹ := (inv_pos.mpr hp).le
  have hiK : (p + t * d)⁻¹ ≤ K := (le_abs_self _).trans hi
  have hi3 : ((p + t * d)⁻¹) ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ hi0 hiK 3
  have h1 : |2 * (b * (p + t * d) - d * (a + t * b)) ^ 2 / (p + t * d) ^ 3| ≤
      2 * K ^ 5 * (|a| + |b|) ^ 2 := by
    rw [show b * (p + t * d) - d * (a + t * b) = b * p - d * a by ring]
    rw [abs_of_nonneg (by positivity), div_eq_mul_inv, ← inv_pow]
    calc
      _ ≤ 2 * (K ^ 2 * (|a| + |b|) ^ 2) * K ^ 3 := by gcongr
      _ = _ := by ring
  have h2 : |2 * r * d ^ 2 / (p + t * d)| ≤ 2 * |r| * K ^ 3 := by
    rw [div_eq_mul_inv, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow, sq_abs,
      abs_of_nonneg hi0]
    calc
      _ ≤ 2 * |r| * K ^ 2 * K := by gcongr
      _ = _ := by ring
  exact (show |2 * (b * (p + t * d) - d * (a + t * b)) ^ 2 / (p + t * d) ^ 3 -
      2 * r * d ^ 2 / (p + t * d)| ≤
        |2 * (b * (p + t * d) - d * (a + t * b)) ^ 2 / (p + t * d) ^ 3| +
          |2 * r * d ^ 2 / (p + t * d)| by
    convert (abs_sub_le
      (2 * (b * (p + t * d) - d * (a + t * b)) ^ 2 / (p + t * d) ^ 3)
      0 (2 * r * d ^ 2 / (p + t * d))) using 1 <;> simp).trans (add_le_add h1 h2)

/-- Both parameter majorants are L1 for the original spatial L2 gradients. No
continuous or bounded representative of either gradient is required. -/
theorem h1SegmentCost_majorants_integrable (a b : Torus 1 → ℝ)
    (ha : MemLp a 2 (haar 1)) (hb : MemLp b 2 (haar 1)) (r K T : ℝ) :
    Integrable (fun x => (K + K ^ 3) * (|a x| + T * |b x|) ^ 2 + K * b x ^ 2 +
      2 * |r| * K * (K + 1)) (haar 1) ∧
    Integrable (fun x => 2 * K ^ 5 * (|a x| + |b x|) ^ 2 + 2 * |r| * K ^ 3) (haar 1) := by
  have hV : Integrable (fun x => (|a x| + T * |b x|) ^ 2) (haar 1) := by
    simpa only [Real.norm_eq_abs, Pi.add_apply, Pi.mul_apply] using (ha.norm.add (hb.norm.const_mul T)).integrable_sq
  have hW : Integrable (fun x => (|a x| + |b x|) ^ 2) (haar 1) := by
    simpa only [Real.norm_eq_abs, Pi.add_apply] using (ha.norm.add hb.norm).integrable_sq
  exact ⟨((hV.const_mul _).add (hb.integrable_sq.const_mul _)).add (integrable_const _),
    (hW.const_mul _).add (integrable_const _)⟩

/-- Parameter-integral nonlinear cost. It is defined on the real line; the
actual positive density extension justifies differentiation even at segment endpoints. -/
def h1SegmentNonlinearCost (r : ℝ) (u v a b : Torus 1 → ℝ) (t : ℝ) : ℝ :=
  ∫ x, h1SegmentCostIntegrand r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t ∂haar 1

/-- Honest first differentiation under the integral on the full closed segment.
Spatial gradients need only belong to their original L2 classes. -/
theorem h1SegmentNonlinearCost_hasDerivAt (r : ℝ) (u v a b : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (ha : MemLp a 2 (haar 1)) (hb : MemLp b 2 (haar 1))
    (t0 : ℝ) (ht0 : t0 ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (h1SegmentNonlinearCost r u v a b)
      (∫ x, h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t0 ∂haar 1) t0 := by
  obtain ⟨η, m, K, hη, hm, hK, hbounds⟩ :=
    h1DensitySegment_uniform_positive_extension u v hu hv hup hvp
  let P := fun t x => u x ^ 2 + t * (v x ^ 2 - u x ^ 2)
  let A := fun t x => a x + t * b x
  have hshape (t : ℝ) (x : Torus 1) : P t x = h1DensitySegmentValue u v t x := by
    dsimp only [P, h1DensitySegmentValue]
    ring
  have hPm (t : ℝ) : Continuous (P t) := by dsimp only [P]; fun_prop
  have hAm (t : ℝ) : AEStronglyMeasurable (A t) (haar 1) :=
    ha.aestronglyMeasurable.add (hb.aestronglyMeasurable.const_mul t)
  have hDm : Continuous (fun x => v x ^ 2 - u x ^ 2) := (hv.pow 2).sub (hu.pow 2)
  have hlogm (t : ℝ) : AEStronglyMeasurable (fun x => Real.log (P t x)) (haar 1) :=
    (Real.measurable_log.comp_aemeasurable (hPm t).aemeasurable).aestronglyMeasurable
  have hInv (t : ℝ) : AEStronglyMeasurable (fun x => (P t x)⁻¹) (haar 1) :=
    ((hPm t).measurable.inv).aestronglyMeasurable
  have hFm (t : ℝ) : AEStronglyMeasurable
      (fun x => h1SegmentCostIntegrand r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t) (haar 1) :=
    (((hAm t).pow 2).mul (hInv t)).sub
      (((hPm t).aestronglyMeasurable.mul (hlogm t)).const_mul (2 * r))
  have hFdm (t : ℝ) : AEStronglyMeasurable
      (fun x => h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t) (haar 1) := by
    convert (((hb.aestronglyMeasurable.const_mul 2).mul
      ((hAm t).mul (hInv t))).sub
        (hDm.aestronglyMeasurable.mul (((hAm t).pow 2).mul ((hInv t).pow 2)))).sub
          ((hDm.aestronglyMeasurable.const_mul (2 * r)).mul ((hlogm t).add_const 1)) using 1
    funext x
    simp only [h1SegmentCostDerivative, P, A, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, div_eq_mul_inv, ← inv_pow]
  have ht0' : t0 ∈ Icc (-η) (1 + η) := by constructor <;> linarith [ht0.1, ht0.2]
  have hpos (t : ℝ) (ht : t ∈ Icc (-η) (1 + η)) (x : Torus 1) : 0 < P t x := by
    rw [hshape]
    exact hm.trans_le (hbounds t ht x).1
  have hFi : Integrable
      (fun x => h1SegmentCostIntegrand r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t0) (haar 1) := by
    have hAi := (ha.add (hb.const_mul t0)).integrable_sq
    have hinv : Continuous (fun x => (P t0 x)⁻¹) := by
      convert ((continuous_const : Continuous (fun _ : Torus 1 => (1 : ℝ))).div
        (hPm t0) (fun x => (hpos t0 ht0' x).ne')) using 1
      funext x
      simp only [Pi.div_apply, one_div]
    have hIi := hAi.mul_bdd hinv.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, hshape] using (hbounds t0 ht0' x).2.2.2.2)
    have hHi : Integrable (fun x => P t0 x * Real.log (P t0 x)) (haar 1) :=
      ((hPm t0).mul ((hPm t0).log (fun x => (hpos t0 ht0' x).ne'))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    convert hIi.sub (hHi.const_mul (2 * r)) using 1
    funext x
    simp only [h1SegmentCostIntegrand, P, A, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, div_eq_mul_inv]
  let majorant := fun x => (K + K ^ 3) * (|a x| + (1 + η) * |b x|) ^ 2 + K * b x ^ 2 +
    2 * |r| * K * (K + 1)
  have hmajorant : Integrable majorant (haar 1) :=
    (h1SegmentCost_majorants_integrable a b ha hb r K (1 + η)).1
  have hbd (x : Torus 1) (t : ℝ) (ht : t ∈ Ioo (-η) (1 + η)) :
      ‖h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t‖ ≤ majorant x := by
    have ht' : t ∈ Icc (-η) (1 + η) := ⟨ht.1.le, ht.2.le⟩
    have hB := hbounds t ht' x
    rw [← hshape] at hB
    rw [Real.norm_eq_abs]
    exact h1SegmentCostDerivative_abs_le r _ _ _ _ t K (1 + η) hK (by positivity)
      (abs_le.mpr (by constructor <;> linarith [ht.1, ht.2]))
      (hpos t ht' x) hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => h1SegmentCostIntegrand r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t)
    (F' := fun t x => h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t)
    (x₀ := t0) (s := Ioo (-η) (1 + η)) (bound := majorant)
    (Ioo_mem_nhds (by linarith [ht0.1]) (by linarith [ht0.2]))
    (Eventually.of_forall hFm) hFi (hFdm t0)
    (Eventually.of_forall hbd) hmajorant
    (Eventually.of_forall fun x t ht => h1SegmentCostIntegrand_hasDerivAt r _ _ _ _ t
      (hpos t ⟨ht.1.le, ht.2.le⟩ x))
  exact hh.2

/-- Honest second differentiation under the integral. The common L1 bound
is derived from the actual positive extension and endpoint L2 gradients. -/
theorem h1SegmentNonlinearCostDerivative_hasDerivAt (r : ℝ) (u v a b : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (ha : MemLp a 2 (haar 1)) (hb : MemLp b 2 (haar 1))
    (t0 : ℝ) (ht0 : t0 ∈ Icc (0 : ℝ) 1) :
    HasDerivAt
      (fun t => ∫ x, h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t ∂haar 1)
      (∫ x, 2 * (b x * (u x ^ 2 + t0 * (v x ^ 2 - u x ^ 2)) -
          (v x ^ 2 - u x ^ 2) * (a x + t0 * b x)) ^ 2 /
            (u x ^ 2 + t0 * (v x ^ 2 - u x ^ 2)) ^ 3 -
        2 * r * (v x ^ 2 - u x ^ 2) ^ 2 /
          (u x ^ 2 + t0 * (v x ^ 2 - u x ^ 2)) ∂haar 1) t0 := by
  obtain ⟨η, m, K, hη, hm, hK, hbounds⟩ :=
    h1DensitySegment_uniform_positive_extension u v hu hv hup hvp
  let P := fun t x => u x ^ 2 + t * (v x ^ 2 - u x ^ 2)
  let A := fun t x => a x + t * b x
  let D := fun x => v x ^ 2 - u x ^ 2
  let F2 := fun t x => 2 * (b x * P t x - D x * A t x) ^ 2 / P t x ^ 3 -
    2 * r * D x ^ 2 / P t x
  have hshape (t : ℝ) (x : Torus 1) : P t x = h1DensitySegmentValue u v t x := by
    dsimp only [P, h1DensitySegmentValue]
    ring
  have hPm (t : ℝ) : Continuous (P t) := by dsimp only [P]; fun_prop
  have hAm (t : ℝ) : AEStronglyMeasurable (A t) (haar 1) :=
    ha.aestronglyMeasurable.add (hb.aestronglyMeasurable.const_mul t)
  have hDm : Continuous D := (hv.pow 2).sub (hu.pow 2)
  have hlogm (t : ℝ) : AEStronglyMeasurable (fun x => Real.log (P t x)) (haar 1) :=
    (Real.measurable_log.comp_aemeasurable (hPm t).aemeasurable).aestronglyMeasurable
  have hInv (t : ℝ) : AEStronglyMeasurable (fun x => (P t x)⁻¹) (haar 1) :=
    ((hPm t).measurable.inv).aestronglyMeasurable
  have hFm (t : ℝ) : AEStronglyMeasurable
      (fun x => h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t) (haar 1) := by
    convert (((hb.aestronglyMeasurable.const_mul 2).mul
      ((hAm t).mul (hInv t))).sub
        (hDm.aestronglyMeasurable.mul (((hAm t).pow 2).mul ((hInv t).pow 2)))).sub
          ((hDm.aestronglyMeasurable.const_mul (2 * r)).mul ((hlogm t).add_const 1)) using 1
    funext x
    simp only [h1SegmentCostDerivative, P, A, D, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, div_eq_mul_inv, ← inv_pow]
  have hF2m (t : ℝ) : AEStronglyMeasurable (F2 t) (haar 1) := by
    convert (((((hb.aestronglyMeasurable.mul (hPm t).aestronglyMeasurable).sub
      (hDm.aestronglyMeasurable.mul (hAm t))).pow 2).const_mul 2).mul
        ((hInv t).pow 3)).sub
          (((hDm.aestronglyMeasurable.pow 2).const_mul (2 * r)).mul (hInv t)) using 1
    funext x
    simp only [F2, P, A, D, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, div_eq_mul_inv, ← inv_pow]
  have hpos (t : ℝ) (ht : t ∈ Icc (-η) (1 + η)) (x : Torus 1) : 0 < P t x := by
    rw [hshape]
    exact hm.trans_le (hbounds t ht x).1
  have ht0' : t0 ∈ Ioo (-η) (1 + η) := by constructor <;> linarith [ht0.1, ht0.2]
  have hzero : (0 : ℝ) ∈ Icc (-η) (1 + η) := by constructor <;> linarith
  have hpK (x : Torus 1) : |u x ^ 2| ≤ K := by
    simpa only [h1DensitySegmentValue, sub_zero, one_mul, zero_mul, add_zero] using
      (hbounds 0 hzero x).2.1
  let majorant1 := fun x => (K + K ^ 3) * (|a x| + (1 + η) * |b x|) ^ 2 + K * b x ^ 2 +
    2 * |r| * K * (K + 1)
  let majorant2 := fun x => 2 * K ^ 5 * (|a x| + |b x|) ^ 2 + 2 * |r| * K ^ 3
  have hMaj := h1SegmentCost_majorants_integrable a b ha hb r K (1 + η)
  have hbd1 (x : Torus 1) (t : ℝ) (ht : t ∈ Ioo (-η) (1 + η)) :
      ‖h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t‖ ≤ majorant1 x := by
    have ht' : t ∈ Icc (-η) (1 + η) := ⟨ht.1.le, ht.2.le⟩
    have hB := hbounds t ht' x
    rw [← hshape] at hB
    rw [Real.norm_eq_abs]
    exact h1SegmentCostDerivative_abs_le r _ _ _ _ t K (1 + η) hK (by positivity)
      (abs_le.mpr (by constructor <;> linarith [ht.1, ht.2]))
      (hpos t ht' x) hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2
  have hbd2 (x : Torus 1) (t : ℝ) (ht : t ∈ Ioo (-η) (1 + η)) : ‖F2 t x‖ ≤ majorant2 x := by
    have ht' : t ∈ Icc (-η) (1 + η) := ⟨ht.1.le, ht.2.le⟩
    have hB := hbounds t ht' x
    rw [← hshape] at hB
    rw [Real.norm_eq_abs]
    exact h1SegmentCostSecondDerivative_abs_le r _ _ _ _ t K hK
      (hpos t ht' x) (hpK x) hB.2.2.1 hB.2.2.2.2
  have hFi : Integrable
      (fun x => h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t0) (haar 1) :=
    Integrable.mono' hMaj.1 (hFm t0) (Eventually.of_forall fun x => hbd1 x t0 ht0')
  have hh := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x => h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t)
    (F' := F2) (x₀ := t0) (s := Ioo (-η) (1 + η)) (bound := majorant2)
    (Ioo_mem_nhds ht0'.1 ht0'.2) (Eventually.of_forall hFm) hFi (hF2m t0)
    (Eventually.of_forall hbd2) hMaj.2
    (Eventually.of_forall fun x t ht => h1SegmentCostDerivative_hasDerivAt r _ _ _ _ t
      (hpos t ⟨ht.1.le, ht.2.le⟩ x))
  exact hh.2

end DGPS.Examples.ThreeSpeciesCircle
