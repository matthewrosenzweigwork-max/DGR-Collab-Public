import DGRHS.Commutator.SourceLogTransportEnergy
import DGRHS.CLT.SourceLogUniform
import DGRHS.CLT.BoundedLinearWeightMoments

noncomputable section
open MeasureTheory
open scoped NNReal
namespace DGRHS.Commutator

lemma aemeasurable_of_exp_double_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable (fun x => Real.exp (2 * f x)) μ) :
    AEMeasurable f μ := by
  have hm := Real.measurable_log.comp_aemeasurable hf.aestronglyMeasurable.aemeasurable
  have hm' : AEMeasurable (fun x => 2 * f x) μ := by
    simpa only [Function.comp_def, Real.log_exp] using hm
  convert hm'.const_mul (1 / 2 : ℝ) using 1
  funext x
  ring

/-- Positive parameter, including constant velocity, chosen from the actual physical bound. -/
lemma logTransport_epsilon_small {a : ℝ} (ha : 0 ≤ a) :
    let ε := (1 + 8 * DGRHS.Attractive.attractiveMomentConstant * a)⁻¹
    0 < ε ∧ (2 * ε) * (DGRHS.Attractive.attractiveMomentConstant * (4 * a)) < 1 := by
  have hq : 0 ≤ DGRHS.Attractive.attractiveMomentConstant :=
    DGRHS.Attractive.attractiveMomentConstant_pos.le
  have hd : 0 < 1 + 8 * DGRHS.Attractive.attractiveMomentConstant * a := by positivity
  dsimp only
  constructor
  · exact inv_pos.mpr hd
  · have hr : (2 * (1 + 8 * DGRHS.Attractive.attractiveMomentConstant * a)⁻¹) *
        (DGRHS.Attractive.attractiveMomentConstant * (4 * a)) =
        (8 * DGRHS.Attractive.attractiveMomentConstant * a) /
          (1 + 8 * DGRHS.Attractive.attractiveMomentConstant * a) := by ring
    rw [hr]
    exact (div_lt_one hd).mpr (by linarith)

/-- Actual unnormalized source numerator, with the SAME repulsive energy at doubled beta.
This logarithmic proof uses bounded transport kernels and Cauchy--Schwarz, an
alternative to the manuscript's short-range absorption/Hölder bootstrap. -/
theorem exists_sourceLogTransport_unnormalized_exponential
    {ι : Type*} [Fintype ι] (n : ℕ) (hn : 0 < n)
    {K : ℝ≥0} {v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} (hv : LipschitzWith K v)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable DGRHS.Gaussian.logPhysicalPair
      ((DGRHS.Gaussian.gaussianRieszDensityMeasure ρ).prod
        (DGRHS.Gaussian.gaussianRieszDensityMeasure ρ))) :
    let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
    let W := fun a b : EuclideanSpace ℝ ι => DGRHS.Gaussian.logPhysicalPair (a,b)
    ∃ ε : ℝ, 0 < ε ∧ ∀ β : ℝ, 0 ≤ β → ∃ Cem : ℝ, 0 < Cem ∧
      ∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 0 < N →
      Integrable (fun x : Fin N → EuclideanSpace ℝ ι => Real.exp
        (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
            (DGRHS.Gaussian.hoeffdingCentered μ DGRHS.Gaussian.logPhysicalPair)
            (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x +
          σ * ε * (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x))
        (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → EuclideanSpace ℝ ι, Real.exp
        (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
            (DGRHS.Gaussian.hoeffdingCentered μ DGRHS.Gaussian.logPhysicalPair)
            (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x +
          σ * ε * (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ Cem := by
  dsimp only
  let μ := DGRHS.Gaussian.gaussianRieszDensityMeasure ρ
  let W := fun a b : EuclideanSpace ℝ ι => DGRHS.Gaussian.logPhysicalPair (a,b)
  obtain ⟨C, hC, hmoment⟩ := exists_sourceLogTransport_energy_exponential
    (E := EuclideanSpace ℝ ι) n hn
  let a := C * (K : ℝ) ^ n
  have ha : 0 ≤ a := mul_nonneg hC (pow_nonneg K.coe_nonneg n)
  let ε := (1 + 8 * DGRHS.Attractive.attractiveMomentConstant * a)⁻¹
  obtain ⟨hε, hsmall⟩ := logTransport_epsilon_small ha
  refine ⟨ε, hε, ?_⟩
  intro β hβ
  obtain ⟨Cp, hCp, hrep⟩ := DGRHS.CLT.sourceLogPartition_uniform (2 * β)
    (by positivity) hd ρ M hM hρ hpair
  let Q := DGRHS.Attractive.attractiveMomentConstant * (4 * a)
  let B := Real.exp (3 * (2 * ε) * a) * (2 / (1 - ((2 * ε) * Q) ^ 2))
  refine ⟨max (Real.sqrt Cp * Real.sqrt B) 1,
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _), ?_⟩
  intro σ hσ N hN
  have hσsq : σ ^ 2 = 1 := by nlinarith [sq_abs σ]
  have ht : |2 * (σ * ε)| = 2 * ε := by
    rw [abs_mul, abs_mul, hσ, abs_of_pos hε]
    norm_num
    rfl
  have htsmall : |2 * (σ * ε)| *
      (DGRHS.Attractive.attractiveMomentConstant * (4 * C * (K : ℝ) ^ n)) < 1 := by
    rw [ht]
    simpa [a, ε, mul_assoc] using hsmall
  obtain ⟨hc, hb⟩ := hmoment hv μ (2 * (σ * ε)) htsmall N hN
  have hBB : Real.exp (3 * |2 * (σ * ε)| * C * (K : ℝ) ^ n) *
      (2 / (1 - ((2 * (σ * ε)) *
        (DGRHS.Attractive.attractiveMomentConstant * (4 * C * (K : ℝ) ^ n))) ^ 2)) = B := by
    rw [ht]
    have he : ((2 * (σ * ε)) *
        (DGRHS.Attractive.attractiveMomentConstant * (4 * C * (K : ℝ) ^ n))) ^ 2 =
        ((2 * ε) * Q) ^ 2 := by dsimp [Q, a]; nlinarith [hσsq]
    rw [he]
    simp [B, a, mul_assoc]
  rw [hBB] at hb
  obtain ⟨hr, hbr⟩ := hrep N (by omega)
  let X := fun x : Fin N → EuclideanSpace ℝ ι => -β * (N : ℝ) *
    DGRHS.CLT.sourceCanonicalModulatedEnergy
      (DGRHS.Gaussian.hoeffdingCentered μ DGRHS.Gaussian.logPhysicalPair)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x
  let Y := fun x : Fin N → EuclideanSpace ℝ ι =>
    σ * ε * (N : ℝ) * sourceTransportEnergy μ (sourceLogTransportKernel n v) N x
  have hx : Integrable (fun x => Real.exp (2 * X x)) (Measure.pi (fun _ : Fin N => μ)) := by
    convert hr using 1
    funext x
    congr 1
    dsimp [X, μ, W]
    ring
  have hy : Integrable (fun x => Real.exp (2 * Y x)) (Measure.pi (fun _ : Fin N => μ)) := by
    convert hc using 1
    funext x
    congr 1
    dsimp [Y]
    ring
  obtain ⟨hi, hiBound⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y
    (aemeasurable_of_exp_double_integrable _ X hx)
    (aemeasurable_of_exp_double_integrable _ Y hy) hx hy
  refine ⟨hi, hiBound.trans ?_⟩
  have hxBound : (∫ x, Real.exp (2 * X x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ Cp := by
    convert hbr using 1
    congr 1
    funext x
    congr 1
    dsimp [X, μ, W]
    ring
  have hyBound : (∫ x, Real.exp (2 * Y x) ∂Measure.pi (fun _ : Fin N => μ)) ≤ B := by
    convert hb using 1
    congr 1
    funext x
    congr 1
    dsimp [Y]
    ring
  exact (mul_le_mul (Real.sqrt_le_sqrt hxBound) (Real.sqrt_le_sqrt hyBound)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans (le_max_left _ _)

#print axioms logTransport_epsilon_small
#print axioms exists_sourceLogTransport_unnormalized_exponential
#check @exists_sourceLogTransport_unnormalized_exponential
end DGRHS.Commutator
