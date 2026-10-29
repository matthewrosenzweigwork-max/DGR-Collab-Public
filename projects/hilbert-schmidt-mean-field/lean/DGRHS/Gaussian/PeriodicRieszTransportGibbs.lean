import DGRHS.Gaussian.PeriodicRieszLocalNumerator
import DGRHS.CLT.BoundedLinearWeightMoments

/-!
Packet P9h, unit 2 (part 28): the torus numerator estimate, the all-temperature Hölder bootstrap and
the transport exponential moment under the literal singular Gibbs law (torus versions of
`SourceRieszLocalNumerator`, `SourceRieszAllBetaBootstrap` and `SourceRieszTransportGibbs`).
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The signed local numerator exponent. -/
def periodicRieszNumeratorExponent (s : ℝ) (n : ℕ) (γ σ : ℝ) (K : ℝ≥0) (v : PeriodicTorus ι → E)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ)
    (ω : Fin N → PeriodicTorus ι) : ℝ :=
  σ * periodicRieszCoefficient ι s n K γ * (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω +
    periodicRieszParticleExponent s ρ γ N ω

lemma periodicRieszNumeratorExponent_eq (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (n : ℕ) (γ σ : ℝ) (K : ℝ≥0) (v : PeriodicTorus ι → E) (N : ℕ) (hN : 0 < N)
    (ω : Fin N → PeriodicTorus ι) :
    periodicRieszNumeratorExponent s n γ σ K v ρ N ω =
      periodicRieszLocalExponent s hs2 ρ M n γ σ K v N ω -
        (3 / 4 : ℝ) * γ * periodicRieszPotConst s hs2 M +
        σ * periodicRieszCoefficient ι s n K γ * periodicRieszTransportCorrection s n v ρ N ω := by
  have hE := periodicRieszTransportEnergy_scaled s n v ρ N hN ω
  unfold periodicRieszNumeratorExponent periodicRieszLocalExponent
  rw [periodicRieszParticleExponent_eq s ρ γ N hN ω]
  have h2 : σ * periodicRieszCoefficient ι s n K γ * (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω =
      σ * periodicRieszCoefficient ι s n K γ * ((N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω) := by
    ring
  rw [h2, hE]
  ring

lemma measurable_periodicRieszTransportCorrection (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) :
    Measurable (periodicRieszTransportCorrection s n v ρ N) := by
  have hκ : StronglyMeasurable (periodicRieszTransportKernel (ι := ι) n s v) :=
    (periodicRieszTransportKernel_measurable n hn s hs hs2 hv).stronglyMeasurable
  have hF : Measurable (fun x : PeriodicTorus ι =>
      ∫ y, periodicRieszTransportKernel n s v (x, y) ∂periodicCappedDensityMeasure ρ) :=
    hκ.integral_prod_right'.measurable
  have hSum : Measurable (fun ω : Fin N → PeriodicTorus ι => ∑ i : Fin N,
      ∫ y, periodicRieszTransportKernel n s v (ω i, y) ∂periodicCappedDensityMeasure ρ) :=
    Finset.measurable_sum _ (fun i _ => hF.comp (measurable_pi_apply i))
  exact (hSum.const_mul _).add_const _

lemma measurable_periodicRieszNumeratorExponent (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (n : ℕ) (hn : 1 ≤ n) (γ σ : ℝ) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) (hN : 0 < N) :
    Measurable (periodicRieszNumeratorExponent s n γ σ K v ρ N) := by
  have hm := ((measurable_periodicRieszLocalExponent s hs hs2 ρ 0 n hn γ σ hv N).sub_const
    ((3 / 4 : ℝ) * γ * periodicRieszPotConst s hs2 0)).add
      ((measurable_periodicRieszTransportCorrection n hn s hs hs2 hv ρ N).const_mul
        (σ * periodicRieszCoefficient ι s n K γ))
  convert hm using 1
  funext ω
  exact periodicRieszNumeratorExponent_eq s hs2 ρ 0 n γ σ K v N hN ω

lemma periodicRieszNumeratorExponent_le (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (n : ℕ) (hn : 1 ≤ n) (γ σ : ℝ) (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 0 < N) (ω : Fin N → PeriodicTorus ι) :
    periodicRieszNumeratorExponent s n γ σ K v ρ N ω ≤
      periodicRieszLocalExponent s hs2 ρ M n γ σ K v N ω := by
  rw [periodicRieszNumeratorExponent_eq s hs2 ρ M n γ σ K v N hN ω]
  have hb := periodicRieszTransportCorrection_scaled_bound n hn s hs hs2 γ σ hγ hσ hv ρ M hM hρ N hN ω
  linarith

/-- The local numerator estimate, uniform in every `N ≥ 1`. -/
theorem periodicRieszLocal_numerator (s : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (γ σ : ℝ) (hγ : 0 < γ) (hσ : |σ| ≤ 1) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (hγb : γ ≤ periodicRieszLocalBeta s hs2 M) :
    Integrable (fun ω => Real.exp (periodicRieszNumeratorExponent s n γ σ K v ρ N ω))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
    (∫ ω, Real.exp (periodicRieszNumeratorExponent s n γ σ K v ρ N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤
        Real.exp 1 + glzUniversalTailConstant := by
  obtain ⟨hXi, hBound⟩ := periodicRieszLocal_exponential_moment s n hn hs hs2 γ σ hγ hσ hv ρ M hM hρ N hN hγb
  have hn' : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN
  have hpoint (ω : Fin N → PeriodicTorus ι) : Real.exp (periodicRieszNumeratorExponent s n γ σ K v ρ N ω) ≤
      Real.exp (periodicRieszLocalExponent s hs2 ρ M n γ σ K v N ω) :=
    Real.exp_le_exp.mpr (periodicRieszNumeratorExponent_le s hs hs2 n hn γ σ hγ.le hσ hv ρ M hM hρ N hn' ω)
  have hi : Integrable (fun ω => Real.exp (periodicRieszNumeratorExponent s n γ σ K v ρ N ω))
      (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) :=
    hXi.mono' (Real.measurable_exp.comp
      (measurable_periodicRieszNumeratorExponent s hs hs2 n hn γ σ hv ρ N hn')).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hpoint ω))
  exact ⟨hi, (integral_mono_ae hi hXi (Filter.Eventually.of_forall hpoint)).trans hBound⟩

/-! ### All temperatures -/

/-- The piecewise transport parameter of Remark A.1. -/
def periodicRieszTransportEpsilon (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (n : ℕ)
    (K : ℝ≥0) (β : ℝ) : ℝ :=
  if β ≤ periodicRieszLocalBeta s hs2 M then periodicRieszCoefficient ι s n K β
  else periodicRieszCoefficient ι s n K (periodicRieszLocalBeta s hs2 M) / 2

lemma periodicRieszTransportEpsilon_pos (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (M : ℝ) (hM : 0 ≤ M) (n : ℕ) (K : ℝ≥0) (hK : 0 < K) (β : ℝ) (hβ : 0 < β) :
    0 < periodicRieszTransportEpsilon s hs2 M n K β := by
  have hloc := (periodicRieszLocalBeta_properties (ι := ι) s hs hs2 M hM).1
  have hC := (periodicRieszProfileC_ge (ι := ι) s hs n).2.2
  have hK' : (0 : ℝ) < (K : ℝ) := NNReal.coe_pos.mpr hK
  unfold periodicRieszTransportEpsilon periodicRieszCoefficient
  split_ifs <;> positivity

/-- The all-temperature exponent of the transport numerator. -/
def periodicRieszTransportAllBetaExponent (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ)
    (n : ℕ) (β σ : ℝ) (K : ℝ≥0) (v : PeriodicTorus ι → E) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) (ω : Fin N → PeriodicTorus ι) : ℝ :=
  σ * periodicRieszTransportEpsilon s hs2 M n K β * (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω +
    periodicRieszParticleExponent s ρ β N ω

lemma periodicRieszTransportAllBetaExponent_large (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (M : ℝ) (n : ℕ) (β σ : ℝ) (K : ℝ≥0) (v : PeriodicTorus ι → E) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ)
    (hβ : periodicRieszLocalBeta s hs2 M < β) (ω : Fin N → PeriodicTorus ι) :
    periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω =
      periodicRieszNumeratorExponent s n (periodicRieszLocalBeta s hs2 M) σ K v ρ N ω / 2 +
        periodicRieszParticleExponent s ρ (β - periodicRieszLocalBeta s hs2 M / 2) N ω := by
  simp only [periodicRieszTransportAllBetaExponent, periodicRieszTransportEpsilon,
    ite_eq_right (not_le.mpr hβ)]
  unfold periodicRieszNumeratorExponent periodicRieszParticleExponent
  ring

lemma measurable_periodicRieszTransportAllBetaExponent (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (n : ℕ) (hn : 1 ≤ n) (β σ : ℝ) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) (hN : 0 < N) :
    Measurable (periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N) := by
  have hE : Measurable (periodicRieszTransportEnergy s n v ρ N) := by
    have hm := ((measurable_physical_iidNegativeStatistic N _
      (stronglyMeasurable_hoeffdingCentered (periodicCappedDensityMeasure ρ) _
        (periodicRieszTransportKernel_measurable n hn s hs hs2 hv).stronglyMeasurable).measurable).const_mul (-2)).add
      (measurable_periodicRieszTransportCorrection n hn s hs hs2 hv ρ N)
    have hn' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have h2 := hm.const_mul (N : ℝ)⁻¹
    convert h2 using 1
    funext ω
    have := periodicRieszTransportEnergy_scaled s n v ρ N hN ω
    simp only [Pi.add_apply]
    rw [← this]
    field_simp
  exact ((hE.const_mul _).add (measurable_periodicRieszParticleExponent s hs hs2 ρ β N hN))

/-- Proper unnormalized all-temperature numerator with a constant common to all `N ≥ 1` and both
signs. -/
theorem periodicRieszTransport_allBeta_numerator (s : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, |σ| ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω)
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C := by
  have hloc := (periodicRieszLocalBeta_properties (ι := ι) s hs hs2 M hM).1
  have hL := glzUniversalTailConstant_pos
  by_cases hsmall : β ≤ periodicRieszLocalBeta s hs2 M
  · refine ⟨Real.exp 1 + glzUniversalTailConstant, by positivity, ?_⟩
    intro σ hσ N hN
    have he : periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N =
        periodicRieszNumeratorExponent s n β σ K v ρ N := by
      funext ω
      simp only [periodicRieszTransportAllBetaExponent, periodicRieszTransportEpsilon,
        ite_eq_left hsmall]
      rfl
    rw [he]
    exact periodicRieszLocal_numerator s n hn hs hs2 β σ hβ hσ hv ρ M hM hρ N hN hsmall
  · have hlarge := lt_of_not_ge hsmall
    have htemp : 0 ≤ 2 * β - periodicRieszLocalBeta s hs2 M := by linarith
    obtain ⟨Cp, hCp, hpart⟩ := periodicRieszParticleWeight_uniform s (2 * β - periodicRieszLocalBeta s hs2 M)
      hs htemp hs2 ρ M hM hρ
    refine ⟨Real.sqrt (Real.exp 1 + glzUniversalTailConstant) * Real.sqrt Cp,
      mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr hCp), ?_⟩
    intro σ hσ N hN
    have hn' : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN
    let X := fun ω : Fin N → PeriodicTorus ι =>
      periodicRieszNumeratorExponent s n (periodicRieszLocalBeta s hs2 M) σ K v ρ N ω / 2
    let Y := periodicRieszParticleExponent s ρ (β - periodicRieszLocalBeta s hs2 M / 2) N
    have hX : Measurable X :=
      (measurable_periodicRieszNumeratorExponent s hs hs2 n hn _ σ hv ρ N hn').div_const 2
    have hY : Measurable Y := measurable_periodicRieszParticleExponent s hs hs2 ρ _ N hn'
    have hXX (ω : Fin N → PeriodicTorus ι) : 2 * X ω =
        periodicRieszNumeratorExponent s n (periodicRieszLocalBeta s hs2 M) σ K v ρ N ω := by
      dsimp [X]; ring
    have hYY (ω : Fin N → PeriodicTorus ι) : 2 * Y ω =
        periodicRieszParticleExponent s ρ (2 * β - periodicRieszLocalBeta s hs2 M) N ω := by
      unfold Y periodicRieszParticleExponent
      ring
    have hx := periodicRieszLocal_numerator s n hn hs hs2 (periodicRieszLocalBeta s hs2 M) σ hloc hσ hv
      ρ M hM hρ N hN le_rfl
    have hy := hpart N hN
    have hxi : Integrable (fun ω => Real.exp (2 * X ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by
      simpa only [hXX] using hx.1
    have hyi : Integrable (fun ω => Real.exp (2 * Y ω))
        (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by
      simpa only [hYY] using hy.1
    obtain ⟨hi, hb⟩ := DGRHS.CLT.exponential_sum_integral_cs X Y hX.aemeasurable hY.aemeasurable hxi hyi
    have hSum (ω : Fin N → PeriodicTorus ι) : X ω + Y ω =
        periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω :=
      (periodicRieszTransportAllBetaExponent_large s hs2 M n β σ K v ρ N hlarge ω).symm
    simp_rw [hSum] at hi hb
    simp_rw [hXX, hYY] at hb
    exact ⟨hi, hb.trans (mul_le_mul (Real.sqrt_le_sqrt hx.2) (Real.sqrt_le_sqrt hy.2.2)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))⟩

/-! ### Constant velocity and the positive transport parameter -/

lemma periodicRieszTransportKernel_eq_zero_of_lipschitz_zero (n : ℕ) (hn : 1 ≤ n) (s : ℝ)
    {v : PeriodicTorus ι → E} (hv : LipschitzWith 0 v) (p : PeriodicTorus ι × PeriodicTorus ι) :
    periodicRieszTransportKernel n s v p = 0 := by
  unfold periodicRieszTransportKernel
  split_ifs with h
  · rfl
  · have hd := hv.dist_le_mul p.1 p.2
    have hz : v p.1 = v p.2 := by
      have : dist (v p.1) (v p.2) ≤ 0 := by simpa using hd
      exact dist_le_zero.mp this
    simp only [hz, sub_self]
    exact (iteratedFDeriv ℝ n (periodicRieszSmooth s) (periodicCenteredLift (p.1 - p.2))).map_coord_zero
      (⟨0, by omega⟩ : Fin n) rfl

lemma periodicRieszTransportEnergy_eq_zero (s : ℝ) (n : ℕ) (hn : 1 ≤ n) {v : PeriodicTorus ι → E}
    (hv : LipschitzWith 0 v) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) (ω : Fin N → PeriodicTorus ι) :
    periodicRieszTransportEnergy s n v ρ N ω = 0 := by
  have he : periodicRieszTransportKernel (ι := ι) n s v = (fun _ => 0) :=
    funext (periodicRieszTransportKernel_eq_zero_of_lipschitz_zero n hn s hv)
  simp [periodicRieszTransportEnergy, he, hoeffdingCentered, DGRHS.centeredKernel,
    DGRHS.potential, DGRHS.secondPotential, DGRHS.interactionEnergy,
    DGRHS.CLT.sourceCanonicalModulatedEnergy, DGRHS.CanonicalVariance.normalizedOffDiagonalSum,
    DGRHS.CanonicalVariance.offDiagonalSum]

/-- Positive transport parameter including constant velocity. -/
def periodicRieszPositiveTransportParameter (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ)
    (n : ℕ) (K : ℝ≥0) (β : ℝ) : ℝ :=
  if K = 0 then 1 else periodicRieszTransportEpsilon s hs2 M n K β

lemma periodicRieszPositiveTransportParameter_pos (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) (n : ℕ) (K : ℝ≥0) (β : ℝ) (hβ : 0 < β) :
    0 < periodicRieszPositiveTransportParameter s hs2 M n K β := by
  unfold periodicRieszPositiveTransportParameter
  split_ifs with hk
  · norm_num
  · exact periodicRieszTransportEpsilon_pos s hs hs2 M hM n K
      (lt_of_le_of_ne (show (0 : ℝ≥0) ≤ K from bot_le) (Ne.symm hk)) β hβ

/-- Both signs and every positive particle number under the literal singular Gibbs law. -/
theorem periodicRieszTransport_Gibbs_moment (s : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β) {K : ℝ≥0}
    {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, |σ| ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      Integrable (fun ω => Real.exp (σ * periodicRieszTransportEpsilon s hs2 M n K β * (N : ℝ) *
        periodicRieszTransportEnergy s n v ρ N ω)) (periodicRieszSingularGibbs s β hs2 ρ N) ∧
      (∫ ω, Real.exp (σ * periodicRieszTransportEpsilon s hs2 M n K β * (N : ℝ) *
        periodicRieszTransportEnergy s n v ρ N ω) ∂periodicRieszSingularGibbs s β hs2 ρ N) ≤ C := by
  obtain ⟨C, hC, hNum⟩ := periodicRieszTransport_allBeta_numerator s n hn hs hs2 M hM β hβ hv ρ hρ
  obtain ⟨Cp, hCp, hPart⟩ := periodicRieszParticleWeight_uniform s β hs hβ.le hs2 ρ M hM hρ
  refine ⟨C, hC, ?_⟩
  intro σ hσ N hN
  have hi := hNum σ hσ N hN
  have hp := hPart N hN
  rw [periodicRieszSingularGibbs_eq_particle s β hs hβ.le hs2 ρ M hM hρ N hN]
  let A := fun ω : Fin N → PeriodicTorus ι => σ * periodicRieszTransportEpsilon s hs2 M n K β * (N : ℝ) *
    periodicRieszTransportEnergy s n v ρ N ω
  have hSum (ω : Fin N → PeriodicTorus ι) :
      periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω =
        periodicRieszParticleExponent s ρ β N ω + A ω := by
    dsimp [periodicRieszTransportAllBetaExponent, A]
    ring
  have ht : Integrable (fun ω => Real.exp (A ω))
      ((Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)).tilted
        (periodicRieszParticleExponent s ρ β N)) := by
    apply (integrable_tilted_iff hp.1 _).mpr
    apply hi.1.congr
    exact ae_of_all _ fun ω => by
      change Real.exp (periodicRieszTransportAllBetaExponent s hs2 M n β σ K v ρ N ω) =
        Real.exp (periodicRieszParticleExponent s ρ β N ω) * Real.exp (A ω)
      rw [hSum, Real.exp_add]
  refine ⟨ht, ?_⟩
  change (∫ ω, Real.exp (A ω) ∂(Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)).tilted
    (periodicRieszParticleExponent s ρ β N)) ≤ C
  rw [integral_exp_tilted]
  change (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω + A ω)
    ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) /
    (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
    ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ≤ C
  simp_rw [← hSum]
  have hdpos : 0 < (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) := by linarith [hp.2.1]
  apply (div_le_iff₀ hdpos).mpr
  exact hi.2.trans (le_mul_of_one_le_right hC.le hp.2.1)

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszLocal_numerator
#print axioms DGRHS.Periodic.periodicRieszTransport_allBeta_numerator
#print axioms DGRHS.Periodic.periodicRieszTransport_Gibbs_moment
