import LeanResearch.PeriodicAttractiveLogGas.ConditionalLawEstimates
import LeanResearch.PeriodicAttractiveLogGas.NormalizedExponentialInterpolation
import LeanResearch.PeriodicAttractiveLogGas.DeletedPairConditionals

/-! Source-only development of the near/far one-source estimates in source
Proposition 3.8. Actual normalized point laws and the actual interpolation
majorant are used throughout. Source geometry, all endpoint caps, and ordinary
Euclidean Green derivatives remain explicit. Central checking is pending.
-/

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas.GreenConditionalInfluence

open MeshCells MeshAdjacentCells MeshNearbyGeometry GreenPointWeights
  LabelOccupations ConditionalParameters PoleLogMoments RectangleRotation


def conjugateExponent : ℝ≥0∞ := ENNReal.ofReal (4 / 3 : ℝ)

theorem four_holder_conjugate : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) := by
  constructor <;> norm_num

instance four_conjugate_holderTriple : ENNReal.HolderTriple 4 conjugateExponent 1 := by
  simpa only [conjugateExponent, ENNReal.ofReal_ofNat] using four_holder_conjugate.ennrealOfReal

section Analysis

variable {A : Type*} [MeasurableSpace A] {μ : Measure A}

theorem integrable_four_mul_conjugate {p w : A → ℝ}
    (hp : MemLp p 4 μ) (hw : MemLp w conjugateExponent μ) :
    Integrable (fun x ↦ p x * w x) μ := by
  exact memLp_one_iff_integrable.mp (hp.fun_mul hw)

theorem integral_norm_mul_le {p w : A → ℝ}
    (hp : MemLp p 4 μ) (hw : MemLp w conjugateExponent μ) :
    (∫ x, |p x| * |w x| ∂μ) ≤ lpNorm p 4 μ * lpNorm w conjugateExponent μ := by
  have hp' : MemLp p (ENNReal.ofReal (4 : ℝ)) μ := by simpa using hp
  have h := integral_mul_norm_le_Lp_mul_Lq four_holder_conjugate hp' hw
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hp.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num [conjugateExponent])
      (by simp [conjugateExponent]) hw.aestronglyMeasurable]
  simpa only [conjugateExponent, ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4 / 3), Real.norm_eq_abs,
    one_div] using h

/-- Endpoint L4 weights and a genuine conjugate moment prove the actual
integrable majorant needed by the normalized-exponential theorem. -/
theorem admissible_of_four_and_conjugate [IsFiniteMeasure μ] {u w : A → ℝ}
    (hu : Measurable u) (hw : Measurable w)
    (h0 : MemLp (fun x ↦ Real.exp (u x)) 4 μ)
    (h1 : MemLp (fun x ↦ Real.exp (u x + w x)) 4 μ)
    (hwm : MemLp w conjugateExponent μ) : NormalizedExponentialInterpolation.Admissible μ u w := by
  have habs : MemLp (fun x ↦ |w x|) conjugateExponent μ := by
    simpa only [Real.norm_eq_abs] using hwm.norm
  have hone : MemLp (fun _ : A ↦ (1 : ℝ)) conjugateExponent μ := memLp_const 1
  have hfactor : MemLp (fun x : A ↦ (1 : ℝ) + |w x|) conjugateExponent μ := by
    change MemLp ((fun _ : A ↦ (1 : ℝ)) + (fun x : A ↦ |w x|)) conjugateExponent μ
    exact hone.add habs
  have hend : MemLp (NormalizedExponentialInterpolation.endpointBound u w) 4 μ := by
    change MemLp ((fun x : A ↦ Real.exp (u x)) +
      (fun x : A ↦ Real.exp (u x + w x))) 4 μ
    exact h0.add h1
  have hprod : Integrable (fun x : A ↦
      NormalizedExponentialInterpolation.endpointBound u w x * (1 + |w x|)) μ :=
    integrable_four_mul_conjugate
      (p := NormalizedExponentialInterpolation.endpointBound u w)
      (w := fun x : A ↦ (1 : ℝ) + |w x|) hend hfactor
  exact ⟨hu.aemeasurable, hw.aemeasurable, hprod⟩

theorem lpNorm_le_of_bound [IsProbabilityMeasure μ] {f : A → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f μ) (hC : 0 ≤ C) (hbound : ∀ᵐ x ∂μ, |f x| ≤ C) :
    MemLp f conjugateExponent μ ∧ lpNorm f conjugateExponent μ ≤ C := by
  have hm : MemLp f conjugateExponent μ :=
    MemLp.of_bound hf C (by simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hm, ?_⟩
  have hc : MemLp (fun _ : A ↦ C) conjugateExponent μ := memLp_const C
  have hle : eLpNorm f conjugateExponent μ ≤
      eLpNorm (fun _ : A ↦ C) conjugateExponent μ :=
    eLpNorm_mono_ae_real hf (by simpa only [Real.norm_eq_abs] using hbound)
  have hreal := ENNReal.toReal_mono hc.eLpNorm_ne_top hle
  change lpNorm f conjugateExponent μ ≤ lpNorm (fun _ : A ↦ C) conjugateExponent μ at hreal
  simpa only [lpNorm_const' (p := conjugateExponent) (μ := μ)
      (by norm_num [conjugateExponent]) (by simp [conjugateExponent]) C,
    probReal_univ, Real.one_rpow,
    mul_one, Real.norm_eq_abs, abs_of_nonneg hC] using hreal

theorem setTV_interpolation_le_four [NeZero μ] {u w : A → ℝ}
    (h : NormalizedExponentialInterpolation.Admissible μ u w) (hw : MemLp w conjugateExponent μ) {K : ℝ}
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, MemLp (NormalizedExponentialInterpolation.density μ u w t) 4 μ)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, lpNorm (NormalizedExponentialInterpolation.density μ u w t) 4 μ ≤ K) :
    NormalizedExponentialInterpolation.setTotalVariation (NormalizedExponentialInterpolation.law μ u w 0) (NormalizedExponentialInterpolation.law μ u w 1) ≤
      K * lpNorm w conjugateExponent μ := by
  refine h.setTV_interpolation.1.trans ?_
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      NormalizedExponentialInterpolation.meanAbs μ u w t ≤ K * lpNorm w conjugateExponent μ := by
    rw [NormalizedExponentialInterpolation.meanAbs, h.integral_law ht]
    have he : (fun x ↦ NormalizedExponentialInterpolation.density μ u w t x * |w x|) =
        (fun x ↦ |NormalizedExponentialInterpolation.density μ u w t x| * |w x|) := by
      funext x
      rw [abs_of_pos (h.density_pos ht x)]
    rw [he]
    exact (integral_norm_mul_le (hp t ht) hw).trans
      (mul_le_mul_of_nonneg_right (hK t ht) lpNorm_nonneg)
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    h.intervalIntegrable_meanAbs (intervalIntegrable_const (c := K * lpNorm w conjugateExponent μ)) hb
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hi

theorem setTV_interpolation_le_bound [NeZero μ] {u w : A → ℝ}
    (h : NormalizedExponentialInterpolation.Admissible μ u w) {C : ℝ} (hb : ∀ᵐ x ∂μ, |w x| ≤ C) :
    NormalizedExponentialInterpolation.setTotalVariation (NormalizedExponentialInterpolation.law μ u w 0) (NormalizedExponentialInterpolation.law μ u w 1) ≤ C := by
  refine h.setTV_interpolation.1.trans ?_
  have hmean (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : NormalizedExponentialInterpolation.meanAbs μ u w t ≤ C := by
    let hprob : IsProbabilityMeasure (NormalizedExponentialInterpolation.law μ u w t) := h.law_probability ht
    have hba : ∀ᵐ x ∂NormalizedExponentialInterpolation.law μ u w t, |w x| ≤ C :=
      (withDensity_absolutelyContinuous _ _).ae_le hb
    have hi := integral_mono_ae (h.integrable_w_law ht).abs (integrable_const C) hba
    simpa only [NormalizedExponentialInterpolation.meanAbs, integral_const, probReal_univ, one_smul] using hi
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    h.intervalIntegrable_meanAbs (intervalIntegrable_const (c := C)) hmean
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using hi

end Analysis

section SplitSources

variable {ι : Type*} [Fintype ι]

def potential (X : ι → Torus) (v : ι → ℝ) (z : Torus) : ℝ :=
  ∑ k, v k * regularGreenRepresentative (z - X k)

theorem measurable_potential (X : ι → Torus) (v : ι → ℝ) : Measurable (potential X v) :=
  Finset.measurable_sum _ fun _k _ ↦
    (regularGreenRepresentative_measurable.comp (measurable_id.sub measurable_const)).const_mul _

def splitPositions {A : Type*} (X Y : ι → A) (p : Fin 2 × ι) : A :=
  if p.1 = 0 then X p.2 else Y p.2

def splitCoefficients (v : ι → ℝ) (t : ℝ) (p : Fin 2 × ι) : ℝ :=
  if p.1 = 0 then (1 - t) * v p.2 else t * v p.2

theorem sum_split (v f g : ι → ℝ) (t : ℝ) :
    (∑ p : Fin 2 × ι, splitCoefficients v t p * splitPositions f g p) =
      (1 - t) * (∑ k, v k * f k) + t * (∑ k, v k * g k) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, splitCoefficients, splitPositions,
    ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  simp only [Finset.mul_sum, mul_assoc]

omit [Fintype ι] in
theorem splitCoefficients_nonneg {v : ι → ℝ} (hv : ∀ k, 0 ≤ v k)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (p : Fin 2 × ι) :
    0 ≤ splitCoefficients v t p := by
  unfold splitCoefficients
  split_ifs
  · exact mul_nonneg (sub_nonneg.mpr ht.2) (hv _)
  · exact mul_nonneg ht.1 (hv _)

theorem sum_splitCoefficients (v : ι → ℝ) (t : ℝ) :
    (∑ p : Fin 2 × ι, splitCoefficients v t p) = ∑ k, v k := by
  have h := sum_split v (fun _ ↦ 1) (fun _ ↦ 1) t
  simpa only [splitPositions, ite_self, mul_one, ← add_mul, sub_add_cancel, one_mul] using h

theorem potential_split (X Y : ι → Torus) (v : ι → ℝ) (t : ℝ) (z : Torus) :
    potential (splitPositions X Y) (splitCoefficients v t) z =
      potential X v z + t * (potential Y v z - potential X v z) := by
  have h := sum_split v (fun k ↦ regularGreenRepresentative (z - X k))
    (fun k ↦ regularGreenRepresentative (z - Y k)) t
  have he (p : Fin 2 × ι) :
      regularGreenRepresentative (z - splitPositions X Y p) =
        splitPositions (fun k ↦ regularGreenRepresentative (z - X k))
          (fun k ↦ regularGreenRepresentative (z - Y k)) p := by
    simp only [splitPositions]
    split_ifs <;> rfl
  simp_rw [potential, he]
  exact h.trans (by ring)

/-- Repeated identical fixed poles combine back to their original coefficient;
only the distinguished pole changes in the interpolated potential. -/
theorem potential_sub_single [DecidableEq ι] (X Y : ι → Torus) (v : ι → ℝ) (j : ι)
    (hXY : ∀ k, k ≠ j → Y k = X k) (z : Torus) :
    potential Y v z - potential X v z =
      v j * (regularGreenRepresentative (z - Y j) - regularGreenRepresentative (z - X j)) := by
  rw [potential, potential, ← Finset.sum_sub_distrib]
  calc
    _ = v j * regularGreenRepresentative (z - Y j) -
        v j * regularGreenRepresentative (z - X j) := by
      apply Finset.sum_eq_single j
      · intro k hk hkj
        rw [hXY k hkj, sub_self]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    _ = _ := by ring

theorem interpolated_weight_eq (X Y : ι → Torus) (v : ι → ℝ) (t : ℝ) :
    NormalizedExponentialInterpolation.weight (potential X v) (fun z ↦ potential Y v z - potential X v z) t =
      torusWeight (splitPositions X Y) (splitCoefficients v t) := by
  funext z
  exact congrArg Real.exp (potential_split X Y v t z).symm

theorem interpolated_density_eq (μ : Measure Torus) (X Y : ι → Torus) (v : ι → ℝ) (t : ℝ) :
    NormalizedExponentialInterpolation.density μ (potential X v) (fun z ↦ potential Y v z - potential X v z) t =
      pointDensity μ (splitPositions X Y) (splitCoefficients v t) := by
  funext z
  simp only [NormalizedExponentialInterpolation.density, NormalizedExponentialInterpolation.normalizer, interpolated_weight_eq, pointDensity,
    div_eq_mul_inv, mul_comm]

theorem interpolation_endpoint_laws (μ : Measure Torus) (X Y : ι → Torus) (v : ι → ℝ) :
    NormalizedExponentialInterpolation.law μ (potential X v) (fun z ↦ potential Y v z - potential X v z) 0 = pointLaw μ X v ∧
    NormalizedExponentialInterpolation.law μ (potential X v) (fun z ↦ potential Y v z - potential X v z) 1 = pointLaw μ Y v := by
  have h0 : NormalizedExponentialInterpolation.weight (potential X v)
      (fun z ↦ potential Y v z - potential X v z) 0 = torusWeight X v := by
    funext z
    simp only [NormalizedExponentialInterpolation.weight, zero_mul, add_zero, potential, torusWeight]
  have h1 : NormalizedExponentialInterpolation.weight (potential X v)
      (fun z ↦ potential Y v z - potential X v z) 1 = torusWeight Y v := by
    funext z
    unfold NormalizedExponentialInterpolation.weight torusWeight
    change Real.exp (potential X v z + 1 * (potential Y v z - potential X v z)) =
      Real.exp (potential Y v z)
    congr 1
    ring
  constructor <;>
    simp only [NormalizedExponentialInterpolation.law, NormalizedExponentialInterpolation.density,
      NormalizedExponentialInterpolation.normalizer, h0, h1, pointLaw, pointDensity,
      div_eq_mul_inv, mul_comm]

theorem weight_memLp_four_of_density (μ : Measure Torus) (X : ι → Torus) (v : ι → ℝ)
    (hz : 0 < ∫ z, torusWeight X v z ∂μ) (hp : MemLp (pointDensity μ X v) 4 μ) :
    MemLp (torusWeight X v) 4 μ := by
  have he : torusWeight X v = fun z ↦ (∫ u, torusWeight X v u ∂μ) * pointDensity μ X v z := by
    funext z
    simp only [pointDensity]
    field_simp [hz.ne']
  rw [he]
  exact hp.const_mul _

end SplitSources

theorem sum_split_near {J N : ℕ} (η₀ η₁ : LabelVector J N)
    (v : Fin N → ℝ) (t : ℝ) (S : Finset (MeshIndex J)) :
    (∑ p : {p : Fin 2 × Fin N // splitPositions η₀ η₁ p ∈ S}, splitCoefficients v t p) =
      (1 - t) * sourceWeight η₀ Finset.univ S v + t * sourceWeight η₁ Finset.univ S v := by
  classical
  rw [← Finset.sum_subtype (p := fun p : Fin 2 × Fin N ↦ splitPositions η₀ η₁ p ∈ S)
    (Finset.univ.filter fun p : Fin 2 × Fin N ↦ splitPositions η₀ η₁ p ∈ S)
    (by simp) (splitCoefficients v t), Finset.sum_filter,
    sourceWeight_eq_sum_ite, sourceWeight_eq_sum_ite]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, splitPositions, splitCoefficients,
    ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k hk <;> split_ifs <;> simp

/-- All split poles, their actual integrals, and the exact source Kstar are
conclusions. Both completed endpoint caps are used in the nearby count. -/
theorem capped_interpolation_bounds {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η₀ η₁ : LabelVector J N)
    (hη₀ : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η₀)
    (hη₁ : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η₁)
    (X Y : Configuration N)
    (hX : ∀ k, X k ∈ closure (meshCell J hJ (η₀ k)))
    (hY : ∀ k, Y k ∈ closure (meshCell J hJ (η₁ k)))
    (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k) (hvc : ∀ k, v k ≤ β / N)
    (a : MeshIndex J) (b : Patch) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    let μ := patchMeasure J hJ a b
    let w := torusWeight (splitPositions X Y) (splitCoefficients v t)
    Integrable w μ ∧ 0 < (∫ z, w z ∂μ) ∧
      IsProbabilityMeasure (pointLaw μ (splitPositions X Y) (splitCoefficients v t)) ∧
      MemLp (NormalizedExponentialInterpolation.density μ (potential X v) (fun z ↦ potential Y v z - potential X v z) t) 4 μ ∧
      lpNorm (NormalizedExponentialInterpolation.density μ (potential X v) (fun z ↦ potential Y v z - potential X v z) t) 4 μ ≤
        ConditionalLawEstimates.densityNormBound β₀ := by
  dsimp only
  have htotal : ∑ p, splitCoefficients v t p ≤ β₀ := by
    rw [sum_splitCoefficients]
    exact total_source_weight_le hN hβ hβ₀ Finset.univ (fun k _ ↦ hvc k)
  have hnear : ∑ p : {p : Fin 2 × Fin N // splitPositions η₀ η₁ p ∈
      nearby J hJ (ConditionalLawEstimates.radius β₀) a b}, splitCoefficients v t p ≤ 1 / 4 := by
    rw [sum_split_near]
    have h0 := sourceWeight_fixedDelta_le hN hβ hβ₀ ConditionalLawEstimates.kernelConstant_pos.le hη₀
      Finset.univ _ (card_nearby_le J hJ (ConditionalLawEstimates.radius β₀) a b) (fun k _ ↦ hvc k)
    have h1 := sourceWeight_fixedDelta_le hN hβ hβ₀ ConditionalLawEstimates.kernelConstant_pos.le hη₁
      Finset.univ _ (card_nearby_le J hJ (ConditionalLawEstimates.radius β₀) a b) (fun k _ ↦ hvc k)
    have hm0 := mul_le_mul_of_nonneg_left h0 (sub_nonneg.mpr ht.2)
    have hm1 := mul_le_mul_of_nonneg_left h1 ht.1
    nlinarith
  have hplace (p : Fin 2 × Fin N) : splitPositions X Y p ∈
      closure (meshCell J hJ (splitPositions η₀ η₁ p)) := by
    unfold splitPositions
    split_ifs
    · exact hX _
    · exact hY _
  have h := pointWeight_bounds hJ (ConditionalLawEstimates.radius_one_le β₀) hmesh a b
    (splitPositions X Y) (splitPositions η₀ η₁) hplace (splitCoefficients v t)
    (splitCoefficients_nonneg hv ht) ConditionalLawEstimates.kernelConstant_pos.le ConditionalLawEstimates.kernelConstant_pos.le
    ConditionalLawEstimates.kernel_log_bound ConditionalLawEstimates.kernel_gradient_bound htotal hnear
  rw [interpolated_density_eq]
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

theorem vertical_poleLog_bound {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : Y ∈ admissiblePoles RectangleRotation.closedVerticalRectangle R) :
    MemLp (poleLog Y) conjugateExponent RectangleRotation.verticalLebesgue ∧
      lpNorm (poleLog Y) conjugateExponent RectangleRotation.verticalLebesgue ≤ lambdaStar R := by
  have hs : coordinateSwap Y ∈ admissiblePoles closedDoubleRectangle R := by
    intro Z hZ
    have hZ' : coordinateSwap Z ∈ closedVerticalRectangle :=
      (coordinateSwap_mem_closedVertical_iff Z).mpr hZ
    have hb := hY (coordinateSwap Z) hZ'
    apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R + 4)).mpr
    intro k
    have hk := (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ R + 4)).mp hb (swapIndex k)
    simpa only [coordinateSupNorm, PiLp.sub_apply, Real.norm_eq_abs,
      coordinateSwap_apply, swapIndex_swapIndex] using hk
  have h := rectangle_poleLog_bound hR hs
  have he : (poleLog Y) ∘ coordinateSwap = poleLog (coordinateSwap Y) := by
    funext Z
    rw [Function.comp_apply, poleLog, poleLog, ← norm_coordinateSwap (coordinateSwap Z - Y),
      map_sub, coordinateSwap_involutive]
  have hm := RectangleRotation.measurePreserving_swap_horizontal
  have hn := eLpNorm_comp_measurePreserving (p := conjugateExponent)
    (measurable_poleLog Y).aestronglyMeasurable hm
  rw [he] at hn
  refine ⟨?_, ?_⟩
  · apply memLp_iff.mpr
    rw [← hn]
    exact h.1.eLpNorm_lt_top
  · change (eLpNorm _ conjugateExponent _).toReal ≤ _
    rw [← hn]
    exact h.2

theorem patch_poleLog_bound (b : Patch) {R : ℝ} (hR : 1 ≤ R) {Y : PlanarSpace}
    (hY : ∀ Z ∈ patchClosed b, coordinateSupNorm (Z - Y) ≤ R + 4) :
    MemLp (poleLog Y) conjugateExponent (patchReference b) ∧
      lpNorm (poleLog Y) conjugateExponent (patchReference b) ≤ lambdaStar R := by
  cases b with
  | cell => exact square_poleLog_bound hR hY
  | edge j =>
    fin_cases j
    · change MemLp (poleLog Y) conjugateExponent (edgeLebesgue 0) ∧
        lpNorm (poleLog Y) conjugateExponent (edgeLebesgue 0) ≤ lambdaStar R
      rw [edgeLebesgue_zero]
      exact rectangle_poleLog_bound hR hY
    · change ∀ Z ∈ closedEdgeRectangle 1, coordinateSupNorm (Z - Y) ≤ R + 4 at hY
      rw [TorusPatchDensity.closedEdgeRectangle_one] at hY
      change MemLp (poleLog Y) conjugateExponent (edgeLebesgue 1) ∧
        lpNorm (poleLog Y) conjugateExponent (edgeLebesgue 1) ≤ lambdaStar R
      rw [TorusPatchDensity.edgeLebesgue_one]
      exact vertical_poleLog_bound hR hY

def centeredSource (J : ℕ) (y : Torus) (z : Torus) : ℝ :=
  regularGreenRepresentative (z - y) - Real.log (J : ℝ)

theorem measurable_centeredSource (J : ℕ) (y : Torus) : Measurable (centeredSource J y) :=
  (regularGreenRepresentative_measurable.comp (measurable_id.sub measurable_const)).sub measurable_const

theorem centeredSource_bound_of_lift {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    (hmesh : 8 * (R + 4) ≤ J) (a : MeshIndex J) (b : Patch) (Y : PlanarSpace)
    (hY : ∀ Z ∈ patchClosed b, coordinateSupNorm (Z - Y) ≤ (R : ℝ) + 4) :
    MemLp (centeredSource J (meshChart J a Y)) conjugateExponent (patchMeasure J hJ a b) ∧
      lpNorm (centeredSource J (meshChart J a Y)) conjugateExponent (patchMeasure J hJ a b) ≤
        lambdaStar R + ConditionalLawEstimates.kernelConstant := by
  let μ := patchReference b
  let ν := patchMeasure J hJ a b
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hRr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hmeshr : 8 * ((R : ℝ) + 4) ≤ J := by exact_mod_cast hmesh
  have hsmall : 2 * ((R : ℝ) + 4) < (J : ℝ) / 2 := by linarith
  have hb : ∀ᵐ Z ∂μ, |GreenPointRescaling.logRemainder J Y Z| ≤
      ConditionalLawEstimates.kernelConstant := by
    filter_upwards [ae_mem_patchClosed b, ae_ne_pole (patchReference_le_volume b) Y] with Z hZ hne
    exact GreenPointRescaling.abs_logRemainder_le hJr hsmall ConditionalLawEstimates.kernel_log_bound
      hne (euclidean_norm_le_two_mul (by linarith) (hY Z hZ))
  obtain ⟨hrm, hrn⟩ := lpNorm_le_of_bound
    (GreenPointRescaling.measurable_logRemainder J Y).aestronglyMeasurable
    ConditionalLawEstimates.kernelConstant_pos.le hb
  obtain ⟨hlm, hln⟩ := patch_poleLog_bound b hRr hY
  have he : (centeredSource J (meshChart J a Y)) ∘ meshChart J a =
      (fun Z ↦ GreenPointRescaling.logRemainder J Y Z - poleLog Y Z) := by
    funext Z
    have hsub : meshChart J a Z - meshChart J a Y =
        torusQuotient ((J : ℝ)⁻¹ • (Z - Y)) := by
      simp only [meshChart, ← torusQuotient_sub, meshAffine_sub]
    simp only [Function.comp_apply, centeredSource, hsub,
      GreenPointRescaling.logRemainder, poleLog]
    ring
  have hcomp : MemLp ((centeredSource J (meshChart J a Y)) ∘ meshChart J a) conjugateExponent μ := by
    rw [he]
    exact hrm.sub hlm
  have hcompNorm : lpNorm ((centeredSource J (meshChart J a Y)) ∘ meshChart J a)
      conjugateExponent μ ≤ lambdaStar R + ConditionalLawEstimates.kernelConstant := by
    rw [he]
    have h := lpNorm_sub_le (g := poleLog Y) hrm (by norm_num [conjugateExponent])
    exact h.trans (by linarith)
  have hm := measurePreserving_patch J hJ a b
  have hn := eLpNorm_comp_measurePreserving (p := conjugateExponent)
    (measurable_centeredSource J (meshChart J a Y)).aestronglyMeasurable hm
  refine ⟨memLp_iff.mpr ?_, ?_⟩
  · rw [← hn]
    exact hcomp.eLpNorm_lt_top
  · change (eLpNorm _ conjugateExponent ν).toReal ≤ _
    rw [← hn]
    exact hcompNorm

/-- The radius is enlarged only for the two moved poles. Its coordinate
bound is exactly R+4, the range in the source definition of Lambda*. -/
theorem centeredSource_bound_of_nearby {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    (hmesh : 8 * (R + 4) ≤ J) (a c : MeshIndex J) (b : Patch)
    (hc : c ∈ nearby J hJ (R + 2) a b) {y : Torus}
    (hy : y ∈ closure (meshCell J hJ c)) :
    MemLp (centeredSource J y) conjugateExponent (patchMeasure J hJ a b) ∧
      lpNorm (centeredSource J y) conjugateExponent (patchMeasure J hJ a b) ≤
        lambdaStar R + ConditionalLawEstimates.kernelConstant := by
  have hex : ∃ Y : PlanarSpace, meshChart J a Y = y ∧
      ∀ Z ∈ patchClosed b, ∀ k : Fin 2, |Z k - Y k| ≤ (R : ℝ) + 4 := by
    cases b with
    | cell => simpa only [patchClosed, Nat.cast_add, Nat.cast_ofNat, add_assoc,
        show (2 : ℝ) + 2 = 4 by norm_num] using
        exists_compatible_cell_lift hJ a c hc hy
    | edge j => simpa only [patchClosed, Nat.cast_add, Nat.cast_ofNat, add_assoc,
        show (2 : ℝ) + 2 = 4 by norm_num] using
        exists_compatible_edge_lift hJ a c j hc hy
  obtain ⟨Y, hY, hb⟩ := hex
  rw [← hY]
  apply centeredSource_bound_of_lift hJ hR hmesh a b Y
  intro Z hZ
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (R : ℝ) + 4)).mpr
  intro k
  simpa only [coordinateSupNorm, PiLp.sub_apply, Real.norm_eq_abs] using hb Z hZ k

def sourceChange (c : ℝ) (x y z : Torus) : ℝ :=
  c * (regularGreenRepresentative (z - y) - regularGreenRepresentative (z - x))

theorem measurable_sourceChange (c : ℝ) (x y : Torus) : Measurable (sourceChange c x y) :=
  ((regularGreenRepresentative_measurable.comp (measurable_id.sub measurable_const)).sub
    (regularGreenRepresentative_measurable.comp (measurable_id.sub measurable_const))).const_mul c

theorem sourceChange_memLp_near {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    (hmesh : 8 * (R + 4) ≤ J) (a c d : MeshIndex J) (b : Patch)
    (hc : c ∈ nearby J hJ (R + 2) a b) (hd : d ∈ nearby J hJ (R + 2) a b)
    {x y : Torus} (hx : x ∈ closure (meshCell J hJ c)) (hy : y ∈ closure (meshCell J hJ d))
    {v : ℝ} (hv : 0 ≤ v) :
    MemLp (sourceChange v x y) conjugateExponent (patchMeasure J hJ a b) ∧
      lpNorm (sourceChange v x y) conjugateExponent (patchMeasure J hJ a b) ≤
        2 * v * (lambdaStar R + ConditionalLawEstimates.kernelConstant) := by
  obtain ⟨hxm, hxn⟩ := centeredSource_bound_of_nearby hJ hR hmesh a c b hc hx
  obtain ⟨hym, hyn⟩ := centeredSource_bound_of_nearby hJ hR hmesh a d b hd hy
  have he : sourceChange v x y = v • (centeredSource J y - centeredSource J x) := by
    funext z
    simp only [sourceChange, centeredSource, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    ring
  rw [he]
  refine ⟨(hym.sub hxm).const_smul v, ?_⟩
  rw [lpNorm_const_smul]
  change |v| * lpNorm (centeredSource J y - centeredSource J x) conjugateExponent _ ≤ _
  rw [abs_of_nonneg hv]
  have hs := lpNorm_sub_le (g := centeredSource J x) hym (by norm_num [conjugateExponent])
  have hn : lpNorm (centeredSource J y - centeredSource J x) conjugateExponent
      (patchMeasure J hJ a b) ≤
      2 * (lambdaStar R + ConditionalLawEstimates.kernelConstant) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hn hv]

def patchCells (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : Patch → Finset (MeshIndex J)
  | .cell => {a}
  | .edge j => {a, nextCell J hJ a j}

def patchDomain (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) : Patch → Set Torus
  | .cell => meshCell J hJ a
  | .edge j => edgeCellUnion J hJ a j

theorem chart_image_patchClosed (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    meshChart J a '' patchClosed b = closure (patchDomain J hJ a b) := by
  cases b with
  | cell => exact (closure_meshCell J hJ a).symm
  | edge j => exact (closure_edgeCellUnion J hJ a j).symm

theorem mem_closure_patch_iff (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) (z : Torus) :
    z ∈ closure (patchDomain J hJ a b) ↔
      ∃ c ∈ patchCells J hJ a b, z ∈ closure (meshCell J hJ c) := by
  cases b <;> simp [patchDomain, patchCells, edgeCellUnion, closure_union]

theorem ae_mem_closure_patch (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    ∀ᵐ z ∂patchMeasure J hJ a b, z ∈ closure (patchDomain J hJ a b) := by
  have hm := measurePreserving_patch J hJ a b
  rw [← hm.map_eq]
  apply (ae_map_iff hm.aemeasurable isClosed_closure.measurableSet).mpr
  filter_upwards [ae_mem_patchClosed b] with Z hZ
  change meshChart J a Z ∈ closure (patchDomain J hJ a b)
  rw [← chart_image_patchClosed]
  exact ⟨Z, hZ, rfl⟩

theorem nearby_iff_patchCells {J R : ℕ} (hJ : 0 < J) (a c : MeshIndex J) (b : Patch) :
    c ∈ nearby J hJ R a b ↔ ∃ d ∈ patchCells J hJ a b, periodicIndexDistance d c ≤ R := by
  cases b <;> simp [nearby, patchCells, mem_nearbyEdgeCells, mem_nearbyCells]

theorem periodicIndexDistance_triangle {J : ℕ} (hJ : 0 < J) (a b c : MeshIndex J) :
    periodicIndexDistance a c ≤ periodicIndexDistance a b + periodicIndexDistance b c := by
  let hJnz : NeZero J := ⟨hJ.ne'⟩
  apply (periodicIndexDistance_le_iff a c).mpr
  intro k
  have hmin : (centeredIndexOffset a c k).natAbs ≤
      (centeredIndexOffset a b k + centeredIndexOffset b c k).natAbs := by
    apply ZMod.natAbs_min_of_le_div_two J
    · simp only [centeredIndexOffset_cast, Int.cast_add]
      abel
    · exact ZMod.natAbs_valMinAbs_le _
  exact hmin.trans ((Int.natAbs_add_le _ _).trans
    (add_le_add ((periodicIndexDistance_le_iff a b).mp le_rfl k)
      ((periodicIndexDistance_le_iff b c).mp le_rfl k)))

@[simp] theorem periodicIndexDistance_self {J : ℕ} (a : MeshIndex J) :
    periodicIndexDistance a a = 0 := by
  simp [periodicIndexDistance, centeredIndexOffset]

theorem periodicIndexDistance_nextCell_le (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (j : Fin 2) :
    periodicIndexDistance a (nextCell J hJ a j) ≤ 1 := by
  let hJnz : NeZero J := ⟨hJ.ne'⟩
  apply (periodicIndexDistance_le_iff _ _).mpr
  intro k
  have hmin : (centeredIndexOffset a (nextCell J hJ a j) k).natAbs ≤
      (-(integerEdgeStep j k)).natAbs := by
    apply ZMod.natAbs_min_of_le_div_two J
    · rw [centeredIndexOffset_cast, nextCell_indexClass]
      simp only [Int.cast_neg]
      abel
    · exact ZMod.natAbs_valMinAbs_le _
  exact hmin.trans (by simp only [integerEdgeStep]; split_ifs <;> norm_num)

theorem patchCells_distance_le_one {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    {c d : MeshIndex J} (hc : c ∈ patchCells J hJ a b) (hd : d ∈ patchCells J hJ a b) :
    periodicIndexDistance c d ≤ 1 := by
  cases b with
  | cell =>
    simp only [patchCells, Finset.mem_singleton] at hc hd
    subst c; subst d
    simp
  | edge j =>
    simp only [patchCells, Finset.mem_insert, Finset.mem_singleton] at hc hd
    rcases hc with hc | hc <;> rcases hd with hd | hd <;> rw [hc, hd]
    · simp
    · exact periodicIndexDistance_nextCell_le J hJ a j
    · rw [periodicIndexDistance_comm]
      exact periodicIndexDistance_nextCell_le J hJ a j
    · simp

/-- The literal source definition: some prescribed cell of the target is
within periodic index distance R+1 of some prescribed cell of the source. -/
def NearPair (J : ℕ) (hJ : 0 < J) (R : ℕ) (a c : MeshIndex J) (b d : Patch) : Prop :=
  ∃ a' ∈ patchCells J hJ a b, ∃ c' ∈ patchCells J hJ c d,
    periodicIndexDistance a' c' ≤ R + 1

theorem NearPair.all_source_cells_nearby {J R : ℕ} {hJ : 0 < J}
    {a c : MeshIndex J} {b d : Patch} (h : NearPair J hJ R a c b d)
    {e : MeshIndex J} (he : e ∈ patchCells J hJ c d) :
    e ∈ nearby J hJ (R + 2) a b := by
  obtain ⟨a', ha', c', hc', hdist⟩ := h
  apply (nearby_iff_patchCells hJ a e b).mpr
  refine ⟨a', ha', ?_⟩
  have htri := periodicIndexDistance_triangle hJ a' c' e
  have hdiam := patchCells_distance_le_one hJ c d hc' he
  omega

theorem not_nearPair_source_far {J R : ℕ} {hJ : 0 < J}
    {a c : MeshIndex J} {b d : Patch} (h : ¬ NearPair J hJ R a c b d)
    {e : MeshIndex J} (he : e ∈ patchCells J hJ c d) : e ∉ nearby J hJ R a b := by
  intro hnear
  obtain ⟨a', ha', hdist⟩ := (nearby_iff_patchCells hJ a e b).mp hnear
  exact h ⟨a', ha', e, he, hdist.trans (by omega)⟩

theorem far_patch_separation {J R : ℕ} (hJ : 0 < J) (a c : MeshIndex J) (b d : Patch)
    (hfar : ¬ NearPair J hJ R a c b d) {z y : Torus}
    (hz : z ∈ closure (patchDomain J hJ a b)) (hy : y ∈ closure (patchDomain J hJ c d)) :
    (R : ℝ) / J ≤ torusEuclideanNorm (z - y) := by
  rw [← chart_image_patchClosed] at hz
  obtain ⟨Z, hZ, rfl⟩ := hz
  obtain ⟨e, he, hye⟩ := (mem_closure_patch_iff J hJ c d y).mp hy
  exact far_gap hJ a e b (not_nearPair_source_far hfar he) hZ hye

/-- The mean-value estimate is applied on the entire actual source
rectangle. The derivative and the sqrt(5) diameter are already proved
ordinary Euclidean facts, including both coordinate orientations. -/
theorem sourceChange_bound_far {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    (a c : MeshIndex J) (b d : Patch) (hfar : ¬ NearPair J hJ R a c b d)
    {x y : Torus} (hx : x ∈ closure (patchDomain J hJ c d))
    (hy : y ∈ closure (patchDomain J hJ c d)) {v : ℝ} (hv : 0 ≤ v)
    {z : Torus} (hz : z ∈ closure (patchDomain J hJ a b)) :
    |sourceChange v x y z| ≤ Real.sqrt 5 * v * ConditionalLawEstimates.kernelConstant / R := by
  rw [← chart_image_patchClosed] at hx hy
  obtain ⟨X, hX, rfl⟩ := hx
  obtain ⟨Y, hY, rfl⟩ := hy
  have hsep (Z : PlanarSpace) (hZ : Z ∈ patchClosed d) (_ : Unit) :
      (R : ℝ) / J ≤ torusEuclideanNorm
        (torusQuotient (RectangleDilation.affine (meshTranslation J c) J Z) - z) := by
    have hyZ : meshChart J c Z ∈ closure (patchDomain J hJ c d) := by
      rw [← chart_image_patchClosed]
      exact ⟨Z, hZ, rfl⟩
    have hh := far_patch_separation hJ a c b d hfar hz hyZ
    rw [show z - meshChart J c Z = -(meshChart J c Z - z) by abel,
      torusEuclideanNorm_neg] at hh
    simpa only [meshChart_eq_chart, GreenPointRescaling.chart] using hh
  have h := far_oscillation d (meshTranslation J c) (β₀ := v)
    (by exact_mod_cast hJ : (0 : ℝ) < J)
    (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR) : (0 : ℝ) < R)
    ConditionalLawEstimates.kernelConstant_pos.le ConditionalLawEstimates.kernel_gradient_bound
    (fun _ : Unit ↦ z) (fun _ : Unit ↦ v) (fun _ ↦ hv) (by simp) hsep hY hX
  have he (Z : PlanarSpace) :
      GreenFarOscillation.referencePotential (meshTranslation J c) J
        (fun _ : Unit ↦ z) (fun _ : Unit ↦ v) Z =
      v * regularGreenRepresentative (z - meshChart J c Z) := by
    simp only [GreenFarOscillation.referencePotential, GreenFarOscillation.referenceSource,
      Fintype.sum_unique, meshChart_eq_chart, GreenPointRescaling.chart]
    congr 1
    rw [show z - torusQuotient (RectangleDilation.affine (meshTranslation J c) J Z) =
      -(torusQuotient (RectangleDilation.affine (meshTranslation J c) J Z) - z) by abel,
      regularGreenRepresentative_even]
  rw [he Y, he X] at h
  simpa only [sourceChange, mul_sub] using h

theorem capped_change_admissible {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η₀ η₁ : LabelVector J N)
    (hη₀ : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η₀)
    (hη₁ : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η₁)
    (X Y : Configuration N)
    (hX : ∀ k, X k ∈ closure (meshCell J hJ (η₀ k)))
    (hY : ∀ k, Y k ∈ closure (meshCell J hJ (η₁ k)))
    (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k) (hvc : ∀ k, v k ≤ β / N)
    (a : MeshIndex J) (b : Patch)
    (hw : MemLp (fun z ↦ potential Y v z - potential X v z) conjugateExponent
      (patchMeasure J hJ a b)) :
    NormalizedExponentialInterpolation.Admissible (patchMeasure J hJ a b)
      (potential X v) (fun z ↦ potential Y v z - potential X v z) := by
  let μ := patchMeasure J hJ a b
  let hprob : IsProbabilityMeasure μ := patchMeasure_probability J hJ a b
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    capped_interpolation_bounds hJ hN hβ hβ₀ hmesh η₀ η₁ hη₀ hη₁ X Y hX hY v hv hvc a b ht
  have hweight (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      MemLp (NormalizedExponentialInterpolation.weight (potential X v)
        (fun z ↦ potential Y v z - potential X v z) t) 4 μ := by
    obtain ⟨hi, hz, hpr, hp, hnorm⟩ := hs t ht
    rw [interpolated_density_eq] at hp
    rw [interpolated_weight_eq]
    exact weight_memLp_four_of_density μ _ _ hz hp
  apply admissible_of_four_and_conjugate (μ := μ)
    (u := potential X v) (w := fun z : Torus ↦ potential Y v z - potential X v z)
    (measurable_potential X v) ((measurable_potential Y v).sub (measurable_potential X v))
  · have he0 : NormalizedExponentialInterpolation.weight (potential X v)
        (fun z : Torus ↦ potential Y v z - potential X v z) 0 =
        (fun z : Torus ↦ Real.exp (potential X v z)) := by
      funext z
      simp only [NormalizedExponentialInterpolation.weight, zero_mul, add_zero]
    have h0 := hweight 0 ⟨le_rfl, by norm_num⟩
    rw [he0] at h0
    exact h0
  · have he1 : NormalizedExponentialInterpolation.weight (potential X v)
        (fun z : Torus ↦ potential Y v z - potential X v z) 1 =
        (fun z : Torus ↦ Real.exp (potential X v z + (potential Y v z - potential X v z))) := by
      funext z
      simp only [NormalizedExponentialInterpolation.weight, one_mul]
    have h1 := hweight 1 ⟨by norm_num, le_rfl⟩
    rw [he1] at h1
    exact h1
  · exact hw

def nearInfluenceConstant (β₀ : ℝ) (N : ℕ) : ℝ :=
  2 * β₀ / N * ConditionalLawEstimates.densityNormBound β₀ *
    (lambdaStar (ConditionalLawEstimates.radius β₀) + ConditionalLawEstimates.kernelConstant)

def farInfluenceConstant (β₀ : ℝ) (N : ℕ) : ℝ :=
  Real.sqrt 5 * β₀ * ConditionalLawEstimates.kernelConstant /
    ((N : ℝ) * ConditionalLawEstimates.radius β₀)

/-- The actual near-source total variation estimate, with no interpolation
density, logarithmic moment, or majorant premise. -/
theorem capped_source_change_near {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η₀ η₁ : LabelVector J N)
    (hη₀ : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η₀)
    (hη₁ : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η₁)
    (X Y : Configuration N)
    (hX : ∀ k, X k ∈ closure (meshCell J hJ (η₀ k)))
    (hY : ∀ k, Y k ∈ closure (meshCell J hJ (η₁ k)))
    (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k) (hvc : ∀ k, v k ≤ β / N)
    (j : Fin N) (hXY : ∀ k, k ≠ j → Y k = X k)
    (a c : MeshIndex J) (b d : Patch)
    (hcell₀ : η₀ j ∈ patchCells J hJ c d) (hcell₁ : η₁ j ∈ patchCells J hJ c d)
    (hnear : NearPair J hJ (ConditionalLawEstimates.radius β₀) a c b d) :
    NormalizedExponentialInterpolation.setTotalVariation
      (pointLaw (patchMeasure J hJ a b) X v) (pointLaw (patchMeasure J hJ a b) Y v) ≤
        nearInfluenceConstant β₀ N := by
  let μ := patchMeasure J hJ a b
  let hprob : IsProbabilityMeasure μ := patchMeasure_probability J hJ a b
  have he : (fun z ↦ potential Y v z - potential X v z) = sourceChange (v j) (X j) (Y j) :=
    funext (potential_sub_single X Y v j hXY)
  obtain ⟨hwm, hwn⟩ := sourceChange_memLp_near hJ (ConditionalLawEstimates.radius_one_le β₀)
    hmesh a (η₀ j) (η₁ j) b (hnear.all_source_cells_nearby hcell₀)
    (hnear.all_source_cells_nearby hcell₁) (hX j) (hY j) (hv j)
  rw [← he] at hwm hwn
  have had := capped_change_admissible hJ hN hβ hβ₀ hmesh η₀ η₁ hη₀ hη₁
    X Y hX hY v hv hvc a b hwm
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    capped_interpolation_bounds hJ hN hβ hβ₀ hmesh η₀ η₁ hη₀ hη₁ X Y hX hY v hv hvc a b ht
  have htv := setTV_interpolation_le_four had hwm
    (fun t ht ↦ (hs t ht).2.2.2.1) (fun t ht ↦ (hs t ht).2.2.2.2)
  rw [(interpolation_endpoint_laws μ X Y v).1, (interpolation_endpoint_laws μ X Y v).2] at htv
  have hNv : (0 : ℝ) < N := by exact_mod_cast hN
  have hvj : v j ≤ β₀ / N := (hvc j).trans (div_le_div_of_nonneg_right hβ₀ hNv.le)
  have hL : 0 ≤ lambdaStar (ConditionalLawEstimates.radius β₀) +
      ConditionalLawEstimates.kernelConstant :=
    add_nonneg (lambdaStar_nonneg (by exact_mod_cast ConditionalLawEstimates.radius_one_le β₀))
      ConditionalLawEstimates.kernelConstant_pos.le
  calc
    _ ≤ ConditionalLawEstimates.densityNormBound β₀ *
        lpNorm (fun z ↦ potential Y v z - potential X v z) conjugateExponent μ := htv
    _ ≤ ConditionalLawEstimates.densityNormBound β₀ *
        (2 * v j * (lambdaStar (ConditionalLawEstimates.radius β₀) +
          ConditionalLawEstimates.kernelConstant)) :=
      mul_le_mul_of_nonneg_left hwn (ConditionalLawEstimates.densityNormBound_pos β₀).le
    _ ≤ ConditionalLawEstimates.densityNormBound β₀ *
        (2 * (β₀ / N) * (lambdaStar (ConditionalLawEstimates.radius β₀) +
          ConditionalLawEstimates.kernelConstant)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvj (by norm_num)) hL)
        (ConditionalLawEstimates.densityNormBound_pos β₀).le
    _ = nearInfluenceConstant β₀ N := by unfold nearInfluenceConstant; ring

/-- Far sources are controlled along their entire closed rectangular
chart, rather than by a pointwise derivative assertion at the endpoints. -/
theorem capped_source_change_far {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η₀ η₁ : LabelVector J N)
    (hη₀ : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η₀)
    (hη₁ : OccupationCap (ConditionalLawEstimates.occupationBound β₀) η₁)
    (X Y : Configuration N)
    (hX : ∀ k, X k ∈ closure (meshCell J hJ (η₀ k)))
    (hY : ∀ k, Y k ∈ closure (meshCell J hJ (η₁ k)))
    (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k) (hvc : ∀ k, v k ≤ β / N)
    (j : Fin N) (hXY : ∀ k, k ≠ j → Y k = X k)
    (a c : MeshIndex J) (b d : Patch)
    (hcell₀ : η₀ j ∈ patchCells J hJ c d) (hcell₁ : η₁ j ∈ patchCells J hJ c d)
    (hfar : ¬ NearPair J hJ (ConditionalLawEstimates.radius β₀) a c b d) :
    NormalizedExponentialInterpolation.setTotalVariation
      (pointLaw (patchMeasure J hJ a b) X v) (pointLaw (patchMeasure J hJ a b) Y v) ≤
        farInfluenceConstant β₀ N := by
  let μ := patchMeasure J hJ a b
  let hprob : IsProbabilityMeasure μ := patchMeasure_probability J hJ a b
  have he : (fun z ↦ potential Y v z - potential X v z) = sourceChange (v j) (X j) (Y j) :=
    funext (potential_sub_single X Y v j hXY)
  have hx : X j ∈ closure (patchDomain J hJ c d) :=
    (mem_closure_patch_iff J hJ c d (X j)).mpr ⟨η₀ j, hcell₀, hX j⟩
  have hy : Y j ∈ closure (patchDomain J hJ c d) :=
    (mem_closure_patch_iff J hJ c d (Y j)).mpr ⟨η₁ j, hcell₁, hY j⟩
  let C := Real.sqrt 5 * v j * ConditionalLawEstimates.kernelConstant / ConditionalLawEstimates.radius β₀
  have hC : 0 ≤ C := div_nonneg
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 5) (hv j)) ConditionalLawEstimates.kernelConstant_pos.le)
    (Nat.cast_nonneg _)
  have hb : ∀ᵐ z ∂μ, |sourceChange (v j) (X j) (Y j) z| ≤ C := by
    filter_upwards [ae_mem_closure_patch J hJ a b] with z hz
    exact sourceChange_bound_far hJ (ConditionalLawEstimates.radius_one_le β₀) a c b d hfar hx hy (hv j) hz
  have hwm := (lpNorm_le_of_bound (measurable_sourceChange _ _ _).aestronglyMeasurable hC hb).1
  rw [← he] at hwm hb
  have had := capped_change_admissible hJ hN hβ hβ₀ hmesh η₀ η₁ hη₀ hη₁
    X Y hX hY v hv hvc a b hwm
  have htv := setTV_interpolation_le_bound had hb
  rw [(interpolation_endpoint_laws μ X Y v).1, (interpolation_endpoint_laws μ X Y v).2] at htv
  have hNv : (0 : ℝ) < N := by exact_mod_cast hN
  have hvj : v j ≤ β₀ / N := (hvc j).trans (div_le_div_of_nonneg_right hβ₀ hNv.le)
  refine htv.trans ?_
  change Real.sqrt 5 * v j * ConditionalLawEstimates.kernelConstant /
      ConditionalLawEstimates.radius β₀ ≤ _
  calc
    _ ≤ Real.sqrt 5 * (β₀ / N) * ConditionalLawEstimates.kernelConstant /
        ConditionalLawEstimates.radius β₀ :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvj (Real.sqrt_nonneg 5))
          ConditionalLawEstimates.kernelConstant_pos.le) (Nat.cast_nonneg _)
    _ = farInfluenceConstant β₀ N := by unfold farInfluenceConstant; ring

theorem setTV_self (μ : Measure Torus) :
    NormalizedExponentialInterpolation.setTotalVariation μ μ = 0 := by
  have he : (fun s : Set Torus ↦ |(μ s).toReal - (μ s).toReal|) '' {s | MeasurableSet s} =
      ({0} : Set ℝ) := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      simp
    · intro hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      refine ⟨(∅ : Set Torus), ?_, by simp⟩
      change MeasurableSet (∅ : Set Torus)
      exact MeasurableSet.empty
  rw [NormalizedExponentialInterpolation.setTotalVariation, he, csSup_singleton]

theorem pointLaw_eq_of_zero_source {N : ℕ} (μ : Measure Torus) (X Y : Configuration N)
    (v : Fin N → ℝ) (j : Fin N) (hXY : ∀ k, k ≠ j → Y k = X k) (hvj : v j = 0) :
    pointLaw μ X v = pointLaw μ Y v := by
  have hp : potential X v = potential Y v := by
    funext z
    have h := potential_sub_single X Y v j hXY z
    rw [hvj, zero_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hw : torusWeight X v = torusWeight Y v := by
    funext z
    exact congrArg Real.exp (congrFun hp z)
  simp only [pointLaw, pointDensity, hw]

theorem source_change_zero_TV {N : ℕ} (μ : Measure Torus) (X Y : Configuration N)
    (v : Fin N → ℝ) (j : Fin N) (hXY : ∀ k, k ≠ j → Y k = X k) (hvj : v j = 0) :
    NormalizedExponentialInterpolation.setTotalVariation (pointLaw μ X v) (pointLaw μ Y v) = 0 := by
  rw [pointLaw_eq_of_zero_source μ X Y v j hXY hvj]
  exact setTV_self _

def pairInfluenceBound (J : ℕ) (hJ : 0 < J) (β₀ : ℝ) (N : ℕ)
    (a c : MeshIndex J) (b d : Patch) : ℝ := by
  classical
  exact if NearPair J hJ (ConditionalLawEstimates.radius β₀) a c b d then
    nearInfluenceConstant β₀ N else farInfluenceConstant β₀ N

theorem capped_source_change {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η₀ η₁ : LabelVector J N) (hη₀ : OccupationCap δ η₀) (hη₁ : OccupationCap δ η₁)
    (X Y : Configuration N)
    (hX : ∀ k, X k ∈ closure (meshCell J hJ (η₀ k)))
    (hY : ∀ k, Y k ∈ closure (meshCell J hJ (η₁ k)))
    (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k) (hvc : ∀ k, v k ≤ β / N)
    (j : Fin N) (hXY : ∀ k, k ≠ j → Y k = X k)
    (a c : MeshIndex J) (b d : Patch)
    (hcell₀ : η₀ j ∈ patchCells J hJ c d) (hcell₁ : η₁ j ∈ patchCells J hJ c d) :
    NormalizedExponentialInterpolation.setTotalVariation
      (pointLaw (patchMeasure J hJ a b) X v) (pointLaw (patchMeasure J hJ a b) Y v) ≤
        pairInfluenceBound J hJ β₀ N a c b d := by
  classical
  unfold pairInfluenceBound
  split_ifs with hnear
  · exact capped_source_change_near hJ hN hβ hβ₀ hmesh η₀ η₁ (hη₀.mono hδ) (hη₁.mono hδ)
      X Y hX hY v hv hvc j hXY a c b d hcell₀ hcell₁ hnear
  · exact capped_source_change_far hJ hN hβ hβ₀ hmesh η₀ η₁ (hη₀.mono hδ) (hη₁.mono hδ)
      X Y hX hY v hv hvc j hXY a c b d hcell₀ hcell₁ hnear

/-- Literal completed-label wrapper; the two caps are hypotheses before
either closed placement or the interpolation parameter is chosen. -/
theorem completed_source_change {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J N) (j : Fin N) (c₀ c₁ : MeshIndex J)
    (hadm : TwoEndpointAdmissible δ η j c₀ c₁)
    (X Y : Configuration N)
    (hX : ∀ k, X k ∈ closure (meshCell J hJ (complete η j c₀ k)))
    (hY : ∀ k, Y k ∈ closure (meshCell J hJ (complete η j c₁ k)))
    (hXY : ∀ k, k ≠ j → Y k = X k)
    (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k) (hvc : ∀ k, v k ≤ β / N)
    (a c : MeshIndex J) (b d : Patch)
    (hc₀ : c₀ ∈ patchCells J hJ c d) (hc₁ : c₁ ∈ patchCells J hJ c d) :
    NormalizedExponentialInterpolation.setTotalVariation
      (pointLaw (patchMeasure J hJ a b) X v) (pointLaw (patchMeasure J hJ a b) Y v) ≤
        pairInfluenceBound J hJ β₀ N a c b d := by
  exact capped_source_change hJ hN hβ hβ₀ hδ hmesh _ _ hadm.1 hadm.2 X Y hX hY
    v hv hvc j hXY a c b d (by simpa only [complete_self]) (by simpa only [complete_self])

/-- Endpoint labels are selected from the prescribed closed patches. At a
shared face either prescribed label may be used, and both completions are
available. This includes both source and target being the exceptional index. -/
theorem exists_capped_adjacent_labels {J N : ℕ} (hJ : 0 < J) {δ : ℝ}
    (η : LabelVector J N) (t : Fin N) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible hJ δ η t a r) (X : Configuration N)
    (hX : ∀ k, X k ∈ closure (patchDomain J hJ (Function.update η t a k)
      (OneCoordinateConditionals.adjacentShapes t r k))) :
    ∃ ζ : LabelVector J N, OccupationCap δ ζ ∧
      (∀ k, ζ k ∈ patchCells J hJ (Function.update η t a k)
        (OneCoordinateConditionals.adjacentShapes t r k)) ∧
      ∀ k, X k ∈ closure (meshCell J hJ (ζ k)) := by
  have ht : X t ∈ closure (patchDomain J hJ a (.edge r)) := by
    simpa only [Function.update_self, OneCoordinateConditionals.adjacentShapes] using hX t
  obtain ⟨c, hc, hXc⟩ := (mem_closure_patch_iff J hJ a (.edge r) (X t)).mp ht
  have hcap : OccupationCap δ (complete η t c) := by
    rcases Finset.mem_insert.mp hc with hca | hcn
    · subst c
      exact hadm.1
    · have he : c = nextCell J hJ a r := Finset.mem_singleton.mp hcn
      subst c
      exact hadm.2
  refine ⟨complete η t c, hcap, ?_, ?_⟩
  · intro k
    by_cases hkt : k = t
    · subst k
      simpa only [complete_self, Function.update_self, OneCoordinateConditionals.adjacentShapes] using hc
    · simp only [complete_of_ne η t k c hkt, Function.update_of_ne hkt,
        OneCoordinateConditionals.adjacentShapes, patchCells, Finset.mem_singleton]
  · intro k
    by_cases hkt : k = t
    · subst k
      simpa only [complete_self] using hXc
    · simpa only [complete_of_ne η t k c hkt, Function.update_of_ne hkt,
        OneCoordinateConditionals.adjacentShapes, patchDomain] using hX k

/-- Full product-of-cells point-law wrapper. Coefficients need only lie in
[0,beta/N], so the same statement covers a removed pair or zero coupling. -/
theorem cell_pointLaw_influence {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J N) (hη : OccupationCap δ η) (i j : Fin N) (_hij : i ≠ j)
    (X Y : Configuration N)
    (hX : ∀ k, X k ∈ closure (meshCell J hJ (η k)))
    (hY : ∀ k, Y k ∈ closure (meshCell J hJ (η k)))
    (hXY : ∀ k, k ≠ j → Y k = X k)
    (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k) (hvc : ∀ k, v k ≤ β / N) :
    NormalizedExponentialInterpolation.setTotalVariation
      (pointLaw (meshCellMeasure J hJ (η i)) X v) (pointLaw (meshCellMeasure J hJ (η i)) Y v) ≤
        pairInfluenceBound J hJ β₀ N (η i) (η j) .cell .cell :=
  capped_source_change hJ hN hβ hβ₀ hδ hmesh η η hη hη X Y hX hY v hv hvc j hXY
    (η i) (η j) .cell .cell (by simp [patchCells]) (by simp [patchCells])

/-- All-coordinate adjacent-product wrapper. There is no i=t or j=t
restriction; both orientations, wrap, closed seams and coincident poles are
included by the actual patch charts and the two endpoint caps. -/
theorem adjacent_pointLaw_influence {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ δ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J N) (t i j : Fin N) (_hij : i ≠ j) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible hJ δ η t a r) (X Y : Configuration N)
    (hX : ∀ k, X k ∈ closure (patchDomain J hJ (Function.update η t a k)
      (OneCoordinateConditionals.adjacentShapes t r k)))
    (hY : ∀ k, Y k ∈ closure (patchDomain J hJ (Function.update η t a k)
      (OneCoordinateConditionals.adjacentShapes t r k)))
    (hXY : ∀ k, k ≠ j → Y k = X k)
    (v : Fin N → ℝ) (hv : ∀ k, 0 ≤ v k) (hvc : ∀ k, v k ≤ β / N) :
    let A := Function.update η t a
    let B := OneCoordinateConditionals.adjacentShapes t r
    NormalizedExponentialInterpolation.setTotalVariation
      (pointLaw (patchMeasure J hJ (A i) (B i)) X v) (pointLaw (patchMeasure J hJ (A i) (B i)) Y v) ≤
        pairInfluenceBound J hJ β₀ N (A i) (A j) (B i) (B j) := by
  obtain ⟨ζ₀, hζ₀, hl₀, hplace₀⟩ := exists_capped_adjacent_labels hJ η t a r hadm X hX
  obtain ⟨ζ₁, hζ₁, hl₁, hplace₁⟩ := exists_capped_adjacent_labels hJ η t a r hadm Y hY
  exact capped_source_change hJ hN hβ hβ₀ hδ hmesh ζ₀ ζ₁ hζ₀ hζ₁ X Y hplace₀ hplace₁
    v hv hvc j hXY _ _ _ _ (hl₀ j) (hl₁ j)

/-- The missing self-interaction is represented by a literal zero, while
the optional deleted pair retains the already proved coefficient function. -/
def siteCoefficients {N : ℕ} (d : Option (DeletedPairEnsemble.Pair N)) (β : ℝ) (i : Fin N) :
    Fin N → ℝ := Function.update (DeletedPairEnsemble.coefficients d β i) i 0

@[simp] theorem siteCoefficients_self {N : ℕ} (d : Option (DeletedPairEnsemble.Pair N))
    (β : ℝ) (i : Fin N) : siteCoefficients d β i i = 0 := by
  simp only [siteCoefficients, Function.update_self]

@[simp] theorem siteCoefficients_zero {N : ℕ} (d : Option (DeletedPairEnsemble.Pair N))
    (i k : Fin N) : siteCoefficients d 0 i k = 0 := by
  by_cases hki : k = i
  · subst k
    exact siteCoefficients_self d 0 i
  · rw [siteCoefficients, Function.update_of_ne hki]
    simp only [DeletedPairEnsemble.coefficients, zero_div, ite_self]

theorem siteCoefficients_deleted {N : ℕ} (p : DeletedPairEnsemble.Pair N) (β : ℝ) :
    siteCoefficients (some p) β p.val.1 p.val.2 = 0 ∧
      siteCoefficients (some p) β p.val.2 p.val.1 = 0 := by
  constructor
  · rw [siteCoefficients, Function.update_of_ne p.property.ne.symm]
    exact (DeletedPairEnsemble.coefficients_deleted p β).1
  · rw [siteCoefficients, Function.update_of_ne p.property.ne]
    exact (DeletedPairEnsemble.coefficients_deleted p β).2

theorem siteCoefficients_bounds {N : ℕ} (d : Option (DeletedPairEnsemble.Pair N)) {β : ℝ}
    (hβ : 0 ≤ β) (i k : Fin N) :
    0 ≤ siteCoefficients d β i k ∧ siteCoefficients d β i k ≤ β / N := by
  by_cases hki : k = i
  · subst k
    simp only [siteCoefficients, Function.update_self]
    exact ⟨le_rfl, div_nonneg hβ (Nat.cast_nonneg N)⟩
  · rw [siteCoefficients, Function.update_of_ne hki]
    exact DeletedPairEnsemble.coefficients_bounds d hβ i k

theorem weight_siteCoefficients {n : ℕ} (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (β : ℝ) (i : Fin (n + 1)) (X : Configuration (n + 1)) :
    torusWeight X (siteCoefficients d β i) =
      torusWeight (OneCoordinateConditionals.removeSite i X) (DeletedPairEnsemble.sourceCoefficient d β i) := by
  funext z
  unfold torusWeight
  congr 1
  rw [Fin.sum_univ_succAbove _ i]
  simp only [siteCoefficients, Function.update_self, zero_mul, zero_add,
    Function.update_of_ne (Fin.succAbove_ne i _), DeletedPairEnsemble.coefficients_succAbove,
    OneCoordinateConditionals.removeSite]

theorem pointLaw_siteCoefficients {n : ℕ} (μ : Measure Torus)
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (β : ℝ) (i : Fin (n + 1))
    (X : Configuration (n + 1)) :
    pointLaw μ X (siteCoefficients d β i) =
      pointLaw μ (OneCoordinateConditionals.removeSite i X) (DeletedPairEnsemble.sourceCoefficient d β i) := by
  simp only [pointLaw, pointDensity, weight_siteCoefficients]

theorem ambientKernel_eq_fullPointLaw {n J : ℕ}
    {β β₀ δ : ℝ} (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (ζ : LabelVector J (n + 1)) (hζ : OccupationCap δ ζ)
    (X : Configuration (n + 1))
    (hX : ∀ k, X k ∈ closure (meshCell J (ConditionalLawEstimates.mesh_pos hmesh) (ζ k)))
    (i : Fin (n + 1)) :
    DeletedPairConditionals.ambientKernels (ConditionalLawEstimates.mesh_pos hmesh) A B d β i X =
      pointLaw (patchMeasure J (ConditionalLawEstimates.mesh_pos hmesh) (A i) (B i))
        X (siteCoefficients d β i) := by
  have hb := DeletedPairEnsemble.capped_source_bounds d hβ hβ₀ hδ hmesh ζ hζ i
    (OneCoordinateConditionals.removeSite i X) (fun k ↦ hX (i.succAbove k)) (A i) (B i)
  rw [DeletedPairConditionals.ambientKernel_eq_pointLaw _ A B d β i X hb.1 hb.2.1,
    pointLaw_siteCoefficients]

theorem patchDomain_eq_existing (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    patchDomain J hJ a b = OneCoordinateConditionals.patchDomain J hJ a b := by
  cases b <;> rfl

/-- A reusable application to actual subtype coordinate kernels. Its sole
placement premise is a capped prescribed-label selection, discharged for the
literal cell and single-adjacent products below. No conditional-law identity,
moment, total-variation estimate, or influence conclusion is a premise. -/
theorem deleted_patch_influence_of_label_selections {n J : ℕ}
    {β β₀ δ : ℝ} (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (hlabels : ∀ X : Configuration (n + 1),
      (∀ k, X k ∈ closure (patchDomain J (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k))) →
      ∃ ζ : LabelVector J (n + 1), OccupationCap δ ζ ∧
        (∀ k, ζ k ∈ patchCells J (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k)) ∧
        ∀ k, X k ∈ closure (meshCell J (ConditionalLawEstimates.mesh_pos hmesh) (ζ k)))
    (i j : Fin (n + 1)) :
    CoordinateOscillation.influence
      (DeletedPairConditionals.patchKernels (ConditionalLawEstimates.mesh_pos hmesh)
        (ConditionalLawEstimates.mesh_two_le hmesh) A B d β) i j ≤
      pairInfluenceBound J (ConditionalLawEstimates.mesh_pos hmesh) β₀ (n + 1) (A i) (A j) (B i) (B j) := by
  apply CoordinateConditionalKernels.influence_domainKernel_le
    (fun k ↦ OneCoordinateConditionals.patchDomain J (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k))
    (fun k ↦ OneCoordinateConditionals.measurableSet_patchDomain J
      (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k))
    (fun k ↦ CoordinateConditionalKernels.patchPoint (ConditionalLawEstimates.mesh_pos hmesh)
      (ConditionalLawEstimates.mesh_two_le hmesh) (A k) (B k))
    (DeletedPairConditionals.ambientKernels (ConditionalLawEstimates.mesh_pos hmesh) A B d β) i j
  intro X Y hX hY hXY
  have hXc : ∀ k, X k ∈ closure (patchDomain J (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k)) := by
    intro k
    rw [patchDomain_eq_existing]
    exact subset_closure (hX k)
  have hYc : ∀ k, Y k ∈ closure (patchDomain J (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k)) := by
    intro k
    rw [patchDomain_eq_existing]
    exact subset_closure (hY k)
  obtain ⟨ζ₀, hζ₀, hl₀, hp₀⟩ := hlabels X hXc
  obtain ⟨ζ₁, hζ₁, hl₁, hp₁⟩ := hlabels Y hYc
  rw [ambientKernel_eq_fullPointLaw d hβ hβ₀ hδ hmesh A B ζ₀ hζ₀ X hp₀ i,
    ambientKernel_eq_fullPointLaw d hβ hβ₀ hδ hmesh A B ζ₁ hζ₁ Y hp₁ i]
  exact capped_source_change (ConditionalLawEstimates.mesh_pos hmesh) (by omega)
    hβ hβ₀ hδ hmesh ζ₀ ζ₁ hζ₀ hζ₁ X Y hp₀ hp₁ (siteCoefficients d β i)
    (fun k ↦ (siteCoefficients_bounds d hβ i k).1)
    (fun k ↦ (siteCoefficients_bounds d hβ i k).2) j
    (fun k hk ↦ (hXY k hk).symm) (A i) (A j) (B i) (B j) (hl₀ j) (hl₁ j)

theorem deleted_patch_zero_influence_of_label_selections {n J : ℕ}
    {β β₀ δ : ℝ} (d : Option (DeletedPairEnsemble.Pair (n + 1)))
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (A : Fin (n + 1) → MeshIndex J) (B : Fin (n + 1) → Patch)
    (hlabels : ∀ X : Configuration (n + 1),
      (∀ k, X k ∈ closure (patchDomain J (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k))) →
      ∃ ζ : LabelVector J (n + 1), OccupationCap δ ζ ∧
        (∀ k, ζ k ∈ patchCells J (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k)) ∧
        ∀ k, X k ∈ closure (meshCell J (ConditionalLawEstimates.mesh_pos hmesh) (ζ k)))
    (i j : Fin (n + 1)) (hzero : siteCoefficients d β i j = 0) :
    CoordinateOscillation.influence
      (DeletedPairConditionals.patchKernels (ConditionalLawEstimates.mesh_pos hmesh)
        (ConditionalLawEstimates.mesh_two_le hmesh) A B d β) i j = 0 := by
  let hn : Nonempty (CoordinateConditionalKernels.PatchCoordinates
      (ConditionalLawEstimates.mesh_pos hmesh) A B) :=
    ⟨fun k ↦ CoordinateConditionalKernels.patchPoint (ConditionalLawEstimates.mesh_pos hmesh)
      (ConditionalLawEstimates.mesh_two_le hmesh) (A k) (B k)⟩
  apply le_antisymm _ (CoordinateOscillation.influence_nonneg _ i j)
  apply CoordinateConditionalKernels.influence_domainKernel_le
    (fun k ↦ OneCoordinateConditionals.patchDomain J (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k))
    (fun k ↦ OneCoordinateConditionals.measurableSet_patchDomain J
      (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k))
    (fun k ↦ CoordinateConditionalKernels.patchPoint (ConditionalLawEstimates.mesh_pos hmesh)
      (ConditionalLawEstimates.mesh_two_le hmesh) (A k) (B k))
    (DeletedPairConditionals.ambientKernels (ConditionalLawEstimates.mesh_pos hmesh) A B d β) i j
  intro X Y hX hY hXY
  have hXc : ∀ k, X k ∈ closure (patchDomain J (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k)) := by
    intro k
    rw [patchDomain_eq_existing]
    exact subset_closure (hX k)
  have hYc : ∀ k, Y k ∈ closure (patchDomain J (ConditionalLawEstimates.mesh_pos hmesh) (A k) (B k)) := by
    intro k
    rw [patchDomain_eq_existing]
    exact subset_closure (hY k)
  obtain ⟨ζ₀, hζ₀, hl₀, hp₀⟩ := hlabels X hXc
  obtain ⟨ζ₁, hζ₁, hl₁, hp₁⟩ := hlabels Y hYc
  rw [ambientKernel_eq_fullPointLaw d hβ hβ₀ hδ hmesh A B ζ₀ hζ₀ X hp₀ i,
    ambientKernel_eq_fullPointLaw d hβ hβ₀ hδ hmesh A B ζ₁ hζ₁ Y hp₁ i,
    source_change_zero_TV _ X Y _ j (fun k hk ↦ (hXY k hk).symm) hzero]

/-- Source prescribed-cell influence, for the actual normalized coordinate
kernels on the product of the half-open cells. Optional pair deletion is part
of the weight, and is not compared to a different mixing law. -/
theorem deleted_cell_kernel_influence {n J : ℕ} {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (hη : OccupationCap δ η) (i j : Fin (n + 1)) :
    CoordinateOscillation.influence
      (DeletedPairConditionals.patchKernels (ConditionalLawEstimates.mesh_pos hmesh)
        (ConditionalLawEstimates.mesh_two_le hmesh) η (fun _ ↦ .cell) d β) i j ≤
      pairInfluenceBound J (ConditionalLawEstimates.mesh_pos hmesh) β₀ (n + 1) (η i) (η j) .cell .cell ∧
    (siteCoefficients d β i j = 0 → CoordinateOscillation.influence
      (DeletedPairConditionals.patchKernels (ConditionalLawEstimates.mesh_pos hmesh)
        (ConditionalLawEstimates.mesh_two_le hmesh) η (fun _ ↦ .cell) d β) i j = 0) := by
  have hlabels (X : Configuration (n + 1))
      (hX : ∀ k, X k ∈ closure (patchDomain J (ConditionalLawEstimates.mesh_pos hmesh) (η k) .cell)) :
      ∃ ζ : LabelVector J (n + 1), OccupationCap δ ζ ∧
        (∀ k, ζ k ∈ patchCells J (ConditionalLawEstimates.mesh_pos hmesh) (η k) .cell) ∧
        ∀ k, X k ∈ closure (meshCell J (ConditionalLawEstimates.mesh_pos hmesh) (ζ k)) :=
    ⟨η, hη, fun k ↦ by simp [patchCells], hX⟩
  exact ⟨deleted_patch_influence_of_label_selections d hβ hβ₀ hδ hmesh η _ hlabels i j,
    deleted_patch_zero_influence_of_label_selections d hβ hβ₀ hδ hmesh η _ hlabels i j⟩

/-- Source adjacent-product influence, simultaneously for every target and
source coordinate. Both endpoint completions are required and no endpoint,
orientation, periodic wrap, or closed collision placement is discarded. -/
theorem deleted_adjacent_kernel_influence {n J : ℕ} {β β₀ δ : ℝ}
    (d : Option (DeletedPairEnsemble.Pair (n + 1))) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (t i j : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (ConditionalLawEstimates.mesh_pos hmesh) δ η t a r) :
    let A := Function.update η t a
    let B := OneCoordinateConditionals.adjacentShapes t r
    CoordinateOscillation.influence
      (DeletedPairConditionals.patchKernels (ConditionalLawEstimates.mesh_pos hmesh)
        (ConditionalLawEstimates.mesh_two_le hmesh) A B d β) i j ≤
      pairInfluenceBound J (ConditionalLawEstimates.mesh_pos hmesh) β₀ (n + 1) (A i) (A j) (B i) (B j) ∧
    (siteCoefficients d β i j = 0 → CoordinateOscillation.influence
      (DeletedPairConditionals.patchKernels (ConditionalLawEstimates.mesh_pos hmesh)
        (ConditionalLawEstimates.mesh_two_le hmesh) A B d β) i j = 0) := by
  have hlabels := exists_capped_adjacent_labels (ConditionalLawEstimates.mesh_pos hmesh) η t a r hadm
  exact ⟨deleted_patch_influence_of_label_selections d hβ hβ₀ hδ hmesh _ _ hlabels i j,
    deleted_patch_zero_influence_of_label_selections d hβ hβ₀ hδ hmesh _ _ hlabels i j⟩

end PeriodicAttractiveLogGas.GreenConditionalInfluence
