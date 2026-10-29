import DGRHS.Commutator.SourceLogTransportMoments
import DGRHS.CLT.SourceRawEnergy
import DGRHS.CLT.IidCanonicalNormalization

noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace DGRHS.Commutator
variable {X : Type*} [MeasurableSpace X]

def sourceTransportEnergy (μ : Measure X) (h : X × X → ℝ)
    (N : ℕ) (x : Fin N → X) : ℝ :=
  2 * DGRHS.CLT.sourceCanonicalModulatedEnergy (DGRHS.Gaussian.hoeffdingCentered μ h)
    (DGRHS.potential μ (fun a b => h (a,b)))
    (DGRHS.interactionEnergy μ (fun a b => h (a,b))) N x

def sourceTransportCorrection (μ : Measure X) (h : X × X → ℝ)
    (N : ℕ) (x : Fin N → X) : ℝ :=
  -2 * (N : ℝ)⁻¹ * ∑ i : Fin N, DGRHS.potential μ (fun a b => h (a,b)) (x i) +
    ∫ p, h p ∂μ.prod μ

/-- Literal ordered-pair, two mixed marginal and pair-mean terms of source An. -/
theorem sourceTransportEnergy_raw (μ : Measure X) (h : X × X → ℝ)
    (hs : ∀ a b, h (a,b) = h (b,a)) (N : ℕ) (hN : 0 < N) (x : Fin N → X) :
    sourceTransportEnergy μ h N x =
      ((N : ℝ)^2)⁻¹ * DGRHS.CanonicalVariance.offDiagonalSum h x -
        2 * (N : ℝ)⁻¹ * (∑ i : Fin N, DGRHS.potential μ (fun a b => h (a,b)) (x i)) +
        ∫ p, h p ∂μ.prod μ := by
  unfold sourceTransportEnergy DGRHS.Gaussian.hoeffdingCentered
  rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_raw μ (fun a b => h (a,b)) hs N hN]
  have heh : Function.uncurry (fun a b => h (a,b)) = h := by funext p; cases p; rfl
  rw [heh]
  dsimp [DGRHS.interactionEnergy]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  field_simp

lemma attractiveNormalizedStatistic_eq_neg_normalized (h : X × X → ℝ)
    (N : ℕ) (x : Fin N → X) :
    DGRHS.Attractive.attractiveNormalizedStatistic N h x =
      -DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x := by
  rw [← DGRHS.CLT.sourceStatistic_eq_normalized]
  unfold DGRHS.Attractive.attractiveNormalizedStatistic DGRHS.Gaussian.sourceKernelParticleStatistic
    DGRHS.Decoupling.offDiagonalSum
  simp only [ne_eq, ite_not]
  ring

/-- Source An differs from its canonical statistic by a genuine bounded one-body correction. -/
lemma sourceTransportEnergy_scaled (μ : Measure X) (h : X × X → ℝ)
    (N : ℕ) (hN : 0 < N) (x : Fin N → X) :
    (N : ℝ) * sourceTransportEnergy μ h N x =
      -DGRHS.Attractive.attractiveNormalizedStatistic N (DGRHS.Gaussian.hoeffdingCentered μ h) x +
      sourceTransportCorrection μ h N x := by
  have he := DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent
    (DGRHS.Gaussian.hoeffdingCentered μ h)
    (DGRHS.potential μ (fun a b => h (a,b)))
    (DGRHS.interactionEnergy μ (fun a b => h (a,b))) (-2) hN x
  rw [attractiveNormalizedStatistic_eq_neg_normalized]
  dsimp [sourceTransportEnergy, sourceTransportCorrection, DGRHS.interactionEnergy] at *
  nlinarith [he]

lemma abs_sourceTransportCorrection_le (μ : Measure X) [IsProbabilityMeasure μ]
    (h : X × X → ℝ) (hh : Measurable h) (L : ℝ) (hb : ∀ p, |h p| ≤ L)
    (N : ℕ) (hN : 0 < N) (x : Fin N → X) :
    |sourceTransportCorrection μ h N x| ≤ 3 * L := by
  have hp (a : X) : |DGRHS.potential μ (fun a b => h (a,b)) a| ≤ L :=
    abs_integral_le_bound μ (hh.comp (measurable_const.prodMk measurable_id)) (fun b => hb (a,b))
  have hm := abs_integral_le_bound (μ.prod μ) hh hb
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : |∑ i : Fin N, DGRHS.potential μ (fun a b => h (a,b)) (x i)| ≤ (N : ℝ) * L := by
    calc
      _ ≤ ∑ i : Fin N, |DGRHS.potential μ (fun a b => h (a,b)) (x i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, L := Finset.sum_le_sum (fun i _ => hp (x i))
      _ = _ := by simp
  have ha : |(N : ℝ)⁻¹ * ∑ i : Fin N, DGRHS.potential μ (fun a b => h (a,b)) (x i)| ≤ L := by
    rw [abs_mul, abs_inv, abs_of_pos hn]
    have hi := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] using hi
  unfold sourceTransportCorrection
  have he : -2 * (N : ℝ)⁻¹ * ∑ i : Fin N, DGRHS.potential μ (fun a b => h (a,b)) (x i) =
      -2 * ((N : ℝ)⁻¹ * ∑ i : Fin N, DGRHS.potential μ (fun a b => h (a,b)) (x i)) := by ring
  rw [he]
  have htri := abs_add_le (-2 * ((N : ℝ)⁻¹ * ∑ i : Fin N,
    DGRHS.potential μ (fun a b => h (a,b)) (x i))) (∫ p, h p ∂μ.prod μ)
  rw [abs_mul] at htri
  have habs : |(-2 : ℝ)| = 2 := by norm_num
  rw [habs] at htri
  linarith

/-- The correction is measurable with proper bounded sections; no improper potential is used. -/
lemma measurable_sourceTransportCorrection (μ : Measure X) [IsProbabilityMeasure μ]
    (h : X × X → ℝ) (hh : Measurable h) (N : ℕ) :
    Measurable (sourceTransportCorrection μ h N) := by
  have hp : Measurable (DGRHS.potential μ (fun a b => h (a,b))) :=
    hh.stronglyMeasurable.integral_prod_right'.measurable
  have hs : Measurable (fun x : Fin N → X =>
      ∑ i : Fin N, DGRHS.potential μ (fun a b => h (a,b)) (x i)) :=
    Finset.measurable_sum _ (fun i _ => hp.comp (measurable_pi_apply i))
  exact (hs.const_mul _).add_const _

section Physical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- Actual logarithmic An has proper uniform signed exponential moments at a fixed small parameter. -/
theorem exists_sourceLogTransport_energy_exponential (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℝ≥0} {v : E → E}, LipschitzWith K v →
      ∀ (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ),
      |t| * (DGRHS.Attractive.attractiveMomentConstant * (4 * C * (K : ℝ) ^ n)) < 1 →
      ∀ N : ℕ, 0 < N →
      Integrable (fun x : Fin N → E => Real.exp
        (t * (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, Real.exp
        (t * (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤
        Real.exp (3 * |t| * C * (K : ℝ) ^ n) *
          (2 / (1 - (t * (DGRHS.Attractive.attractiveMomentConstant *
            (4 * C * (K : ℝ) ^ n))) ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_sourceLogTransportKernel_bound (E := E) n hn
  refine ⟨C, hC, ?_⟩
  intro K v hv μ hμ t ht N hN
  let h := sourceLogTransportKernel n v
  let H := DGRHS.Gaussian.hoeffdingCentered μ h
  let L := C * (K : ℝ) ^ n
  have hL : 0 ≤ L := mul_nonneg hC (pow_nonneg K.coe_nonneg n)
  have hm : Measurable h := measurable_sourceLogTransportKernel n hv
  have hi : Integrable h (μ.prod μ) := integrable_of_abs_bound (μ.prod μ) hm (hb hv)
  have hH : Measurable H :=
    (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ h hm.stronglyMeasurable).measurable
  have hr := bounded_kernel_rowFactorial μ H hH (4 * L) (by positivity)
    (abs_hoeffdingCentered_le μ h hm L (hb hv))
  have hs : ∀ a b, h (a,b) = h (b,a) := fun a b =>
    (sourceLogTransportKernel_swap n v (a,b)).symm
  obtain ⟨hcan, hbound⟩ := DGRHS.Attractive.attractiveCanonical_uniform_exponential μ H hH
    (4 * L) hr (DGRHS.centeredKernel_symmetric μ (fun a b => h (a,b)) hs)
    (DGRHS.integral_centeredKernel_left μ (fun a b => h (a,b)) hi) (-t)
    (by simpa [L, mul_assoc] using ht) N
  let f := fun x : Fin N → E => Real.exp
    (t * (N : ℝ) * sourceTransportEnergy μ h N x)
  let B := Real.exp (3 * |t| * L)
  have hf : Measurable f := by
    have he : f = fun x => Real.exp
        ((-t) * DGRHS.Attractive.attractiveNormalizedStatistic N H x +
          t * sourceTransportCorrection μ h N x) := by
      funext x
      unfold f
      rw [mul_assoc, sourceTransportEnergy_scaled μ h N hN]
      congr 1
      dsimp [H]
      ring
    rw [he]
    exact Real.measurable_exp.comp
      (((DGRHS.Attractive.attractiveNormalizedStatistic_measurable N H hH).const_mul (-t)).add
        ((measurable_sourceTransportCorrection μ h hm N).const_mul t))
  have hpoint (x : Fin N → E) : f x ≤ B *
      Real.exp ((-t) * DGRHS.Attractive.attractiveNormalizedStatistic N H x) := by
    have hR := abs_sourceTransportCorrection_le μ h hm L (hb hv) N hN x
    have hc : t * sourceTransportCorrection μ h N x ≤ 3 * |t| * L := by
      have hprod := le_abs_self (t * sourceTransportCorrection μ h N x)
      rw [abs_mul] at hprod
      nlinarith [mul_le_mul_of_nonneg_left hR (abs_nonneg t)]
    unfold f B
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [mul_assoc, sourceTransportEnergy_scaled μ h N hN]
    linarith
  have hfi : Integrable f (Measure.pi (fun _ : Fin N => μ)) :=
    (hcan.const_mul B).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        change |Real.exp (t * (N : ℝ) * sourceTransportEnergy μ h N x)| ≤ _
        rw [abs_of_pos (Real.exp_pos _)]
        exact hpoint x)
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ ∫ x : Fin N → E, B * Real.exp
        ((-t) * DGRHS.Attractive.attractiveNormalizedStatistic N H x)
        ∂Measure.pi (fun _ : Fin N => μ) :=
      integral_mono_ae hfi (hcan.const_mul B) (Filter.Eventually.of_forall hpoint)
    _ = B * ∫ x : Fin N → E, Real.exp
        ((-t) * DGRHS.Attractive.attractiveNormalizedStatistic N H x)
        ∂Measure.pi (fun _ : Fin N => μ) := integral_const_mul _ _
    _ ≤ B * (2 / (1 - ((-t) * (DGRHS.Attractive.attractiveMomentConstant * (4 * L))) ^ 2)) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = _ := by simp [B, L, mul_assoc]
end Physical

#print axioms sourceTransportEnergy_raw
#print axioms sourceTransportEnergy_scaled
#print axioms abs_sourceTransportCorrection_le
#print axioms exists_sourceLogTransport_energy_exponential
#check @exists_sourceLogTransport_energy_exponential
end DGRHS.Commutator
