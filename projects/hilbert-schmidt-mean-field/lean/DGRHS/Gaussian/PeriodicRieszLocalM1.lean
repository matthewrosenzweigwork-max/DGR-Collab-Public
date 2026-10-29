import DGRHS.Gaussian.PeriodicRieszLocalStats

/-!
Packet P9h, unit 2 (part 24): the torus local exponent and its physical (M1) event reduction
(TeX 3395-3440, `eq:shortAbsorb`, torus version of `SourceRieszLocalM1`/`SourceRieszLocalAbsorption`).

`periodicRieszLocalExponent` is `(3/4) γ P_c - 2 σ ε S(h̃_κ) + (physical particle exponent)`; it is
bounded above, almost surely, by `(7/4) γ P_c + (1/2) S(q_η) + C_abs γ N η^{d-s}` for every
`η ∈ (0, 1/4]`, and an exponent `≥ u` forces the cutoff statistic `S(q_η) ≥ u` at the adaptive scale.
-/

noncomputable section
open MeasureTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The one-body / transport potential constant. -/
def periodicRieszPotConst (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) : ℝ :=
  M * (∫ z, periodicRieszMajorantFun (ι := ι) s z ∂periodicHaar ι +
    2 * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι) + 1

lemma periodicRieszPotConst_ge (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ)
    (hM : 0 ≤ M) :
    M * ∫ z, periodicRieszMajorantFun (ι := ι) s z ∂periodicHaar ι ≤ periodicRieszPotConst s hs2 M ∧
    2 * (M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι) ≤ periodicRieszPotConst s hs2 M ∧
    1 ≤ periodicRieszPotConst s hs2 M := by
  have h1 : 0 ≤ ∫ z, periodicRieszMajorantFun (ι := ι) s z ∂periodicHaar ι :=
    integral_nonneg (fun z => periodicRieszShortFun_nonneg s 1 hs z)
  have h2 : 0 ≤ ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι :=
    integral_nonneg (fun z => abs_nonneg _)
  unfold periodicRieszPotConst
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg hM h1, mul_nonneg hM h2]

/-- The absorption constant. -/
def periodicRieszAbsConst (ι : Type u) [Fintype ι] [Nonempty ι] (s M : ℝ) : ℝ :=
  1 + (7 / 4 : ℝ) * (periodicRieszShortPotentialConst ι s M * (2 : ℝ) ^ ((Fintype.card ι : ℝ) - s))

lemma periodicRieszShortPotentialConst_nonneg (s M : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hM : 0 ≤ M) : 0 ≤ periodicRieszShortPotentialConst ι s M := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hF := periodicRieszMellinFactor_pos (ι := ι) s hs
  have : 0 < ((Fintype.card ι : ℝ) - s) / 2 := by linarith
  unfold periodicRieszShortPotentialConst
  positivity

lemma periodicRieszAbsConst_pos (s M : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hM : 0 ≤ M) : 0 < periodicRieszAbsConst ι s M := by
  have h := periodicRieszShortPotentialConst_nonneg (ι := ι) s M hs hs2 hM
  unfold periodicRieszAbsConst
  positivity

/-- Particle exponent identity in statistic form. -/
lemma periodic_sourceParticleExponent_eq {X : Type*} [MeasurableSpace X] (h : X × X → ℝ)
    (F : X → ℝ) (I β : ℝ) (N : ℕ) (ω : Fin N → X) :
    DGRHS.CLT.sourceParticleExponent h F I β N ω =
      β * iidNegativeStatistic N h ω + β * ((N : ℝ)⁻¹ * ∑ i : Fin N, F (ω i)) - β * I := by
  unfold DGRHS.CLT.sourceParticleExponent
  rw [periodic_energy_normalization β h N ω]

/-- The local exponent of the numerator estimate (torus), written with the pointwise smooth
representative `periodicRieszPair` of the periodic Riesz kernel (which agrees with
`periodicRieszKernel` off a Haar-null set, see `periodicRieszParticleExponent_ae`). -/
def periodicRieszLocalExponent (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (n : ℕ) (γ σ : ℝ) (K : ℝ≥0) (v : PeriodicTorus ι → E)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (N : ℕ) (ω : Fin N → PeriodicTorus ι) : ℝ :=
  (3 / 4 : ℝ) * γ * periodicRieszPotConst s hs2 M -
    2 * σ * periodicRieszCoefficient ι s n K γ * iidNegativeStatistic N
      (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszTransportKernel n s v)) ω +
    DGRHS.CLT.sourceParticleExponent
      (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszPair s))
      (DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)))
      (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) γ N ω

lemma periodicRieszPair_potential_abs_le (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (x : PeriodicTorus ι) :
    |DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) x| ≤
      M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι := by
  have hg := integrable_periodicRieszPairFun (ι := ι) s hs hs2
  have hnn := periodicDensityRow_nonnegative_bound ρ M hM hρ (fun z => |periodicRieszPairFun s z|)
    hg.abs (fun z => abs_nonneg _) x
  rw [integral_abs_periodicRieszPairFun s hs hs2] at hnn
  have hint := periodicDensityRow_integrable_of_haar ρ M hρ _ hg x
  unfold DGRHS.potential
  simp only [periodicRieszPair_eq_fun]
  calc |∫ y, periodicRieszPairFun s (x - y) ∂periodicCappedDensityMeasure ρ|
      ≤ ∫ y, |periodicRieszPairFun s (x - y)| ∂periodicCappedDensityMeasure ρ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := periodicCappedDensityMeasure ρ)
            (fun y => periodicRieszPairFun s (x - y))
    _ ≤ _ := hnn

/-- One-body bound of the physical particle exponent. -/
lemma periodicRieszLocal_oneBody_bound (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (γ : ℝ) (hγ : 0 ≤ γ) (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → PeriodicTorus ι) :
    γ * ((N : ℝ)⁻¹ * ∑ i : Fin N, DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) (ω i)) -
      γ * DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)) ≤
      γ * periodicRieszPotConst s hs2 M := by
  let μ := periodicCappedDensityMeasure ρ
  let W := fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)
  let pk := M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι
  have hn : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN)
  have hF : ∀ x, |DGRHS.potential μ W x| ≤ pk := fun x =>
    periodicRieszPair_potential_abs_le s hs hs2 ρ M hM hρ x
  have hpair : Integrable (Function.uncurry W) (μ.prod μ) := by
    have h := periodicDensityPair_integrable_of_haar ρ M hρ _ (integrable_periodicRieszPairFun (ι := ι) s hs hs2)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    exact (periodicRieszPair_eq_fun s p).symm
  have hFi : Integrable (DGRHS.potential μ W) μ := DGRHS.integrable_potential μ W hpair
  have hI := DGRHS.integral_potential μ W hpair
  have hIabs : |∫ x, DGRHS.potential μ W x ∂μ| ≤ pk := by
    calc |∫ x, DGRHS.potential μ W x ∂μ| ≤ ∫ x, |DGRHS.potential μ W x| ∂μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (DGRHS.potential μ W)
      _ ≤ ∫ _ : PeriodicTorus ι, pk ∂μ := integral_mono hFi.abs (integrable_const _) hF
      _ = pk := by simp
  have hsum : (∑ i : Fin N, DGRHS.potential μ W (ω i)) ≤ (N : ℝ) * pk := by
    calc _ ≤ ∑ _ : Fin N, pk := Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hF _)
      _ = _ := by simp
  have hmean : (N : ℝ)⁻¹ * (∑ i : Fin N, DGRHS.potential μ W (ω i)) ≤ pk := by
    have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn.le)
    simpa only [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul] using h
  have hIlow : -(pk / 2) ≤ DGRHS.interactionEnergy μ W := by
    have := (abs_le.mp hIabs).1
    linarith
  have hP := (periodicRieszPotConst_ge (ι := ι) s hs hs2 M hM).2.1
  have hmain : (N : ℝ)⁻¹ * (∑ i : Fin N, DGRHS.potential μ W (ω i)) - DGRHS.interactionEnergy μ W ≤
      periodicRieszPotConst s hs2 M := by
    have hpk : 0 ≤ pk := by
      have : 0 ≤ ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι := integral_nonneg fun z => abs_nonneg _
      exact mul_nonneg hM this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hmain hγ]

/-! ### The short absorption -/

lemma periodicRieszShortAbsorption_pointwise (s η : ℝ) (n : ℕ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (γ σ : ℝ) (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (p : PeriodicTorus ι × PeriodicTorus ι) :
    σ * periodicRieszCoefficient ι s n K γ *
        hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortTransport n s η v) p -
      γ / 2 * hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortPair s (2 * η)) p ≤
      (7 / 4 : ℝ) * γ * (periodicRieszShortPotentialConst ι s M *
        (2 * η) ^ ((Fintype.card ι : ℝ) - s)) := by
  have h2η : 0 < 2 * η := by positivity
  have hε := periodicRieszCoefficient_nonneg (ι := ι) s hs n (K := (K : ℝ)) (γ := γ) K.coe_nonneg hγ
  have hC := periodicRieszProfileC_ge (ι := ι) s hs n
  have hCn := (sourceRieszGaussianDerivativeConstant_pos n).le
  have hεK := periodicRieszCoefficient_mul_le (ι := ι) s hs n (K := (K : ℝ)) (γ := γ) K.coe_nonneg hγ
  have hKn : 0 ≤ (K : ℝ) ^ n := by positivity
  have hA : 0 ≤ sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s * (K : ℝ) ^ n := by positivity
  have hεA : 4 * periodicRieszCoefficient ι s n K γ *
      (sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s * (K : ℝ) ^ n) ≤ γ := by
    refine le_trans ?_ hεK
    have : sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s * (K : ℝ) ^ n ≤
        periodicRieszProfileC ι s n * (K : ℝ) ^ n := mul_le_mul_of_nonneg_right hC.1 hKn
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hg := periodicRieszShortFun_integrable (ι := ι) s (2 * η) hs hs2 h2η
  have hrow : ∀ x : PeriodicTorus ι, Integrable (fun y => periodicRieszShortPair s (2 * η) (x, y))
      (periodicCappedDensityMeasure ρ) := fun x => by
    have := periodicDensityRow_integrable_of_haar ρ M hρ _ hg x
    simpa only [periodicRieszShortPair_eq] using this
  have hcol : ∀ y : PeriodicTorus ι, Integrable (fun x => periodicRieszShortPair s (2 * η) (x, y))
      (periodicCappedDensityMeasure ρ) := fun y => by
    have := periodicDensityRow_integrable_of_haar ρ M hρ _ hg y
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [periodicRieszShortPair_eq]
    rw [← periodicRieszShortFun_even s (2 * η) (x - y), neg_sub]
  have hProw : ∀ x : PeriodicTorus ι, ∫ y, periodicRieszShortPair s (2 * η) (x, y)
      ∂periodicCappedDensityMeasure ρ ≤
      periodicRieszShortPotentialConst ι s M * (2 * η) ^ ((Fintype.card ι : ℝ) - s) := fun x => by
    simp only [periodicRieszShortPair_eq]
    exact periodicRieszShortFun_potential_le s (2 * η) hs hs2 h2η ρ M hM hρ x
  have hPcol : ∀ y : PeriodicTorus ι, ∫ x, periodicRieszShortPair s (2 * η) (x, y)
      ∂periodicCappedDensityMeasure ρ ≤
      periodicRieszShortPotentialConst ι s M * (2 * η) ^ ((Fintype.card ι : ℝ) - s) := fun y => by
    have h := periodicRieszShortFun_potential_le s (2 * η) hs hs2 h2η ρ M hM hρ y
    refine le_trans (le_of_eq ?_) h
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [periodicRieszShortPair_eq]
    rw [← periodicRieszShortFun_even s (2 * η) (x - y), neg_sub]
  exact centered_short_absorption (periodicCappedDensityMeasure ρ) (periodicRieszShortTransport n s η v)
    (periodicRieszShortPair s (2 * η))
    (measurable_periodicRieszShortTransport n s η hs hη hv).stronglyMeasurable
    (periodicRieszCoefficient ι s n K γ) γ
    (sourceRieszGaussianDerivativeConstant n * (2 : ℝ) ^ s * (K : ℝ) ^ n)
    (periodicRieszShortPotentialConst ι s M * (2 * η) ^ ((Fintype.card ι : ℝ) - s)) σ hε hγ hA hσ
    (fun q => by
      rw [periodicRieszShortPair_eq]
      exact periodicRieszShortTransport_bound_fun n s η hs hη hv q)
    (fun q => by
      rw [periodicRieszShortPair_eq]
      exact periodicRieszShortFun_nonneg s (2 * η) hs _)
    hεA (integrable_periodicRieszShortPair ρ M hρ s (2 * η) hs hs2 h2η) hrow hcol hProw hPcol p

lemma periodicRieszShortAbsorption_statistic (s η : ℝ) (n : ℕ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (γ σ : ℝ) (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → PeriodicTorus ι) :
    -2 * σ * periodicRieszCoefficient ι s n K γ * iidNegativeStatistic N
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortTransport n s η v)) ω +
      γ * iidNegativeStatistic N
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortPair s (2 * η))) ω ≤
      (7 / 4 : ℝ) * γ * (N : ℝ) * (periodicRieszShortPotentialConst ι s M *
        (2 * η) ^ ((Fintype.card ι : ℝ) - s)) := by
  have hP := periodicRieszShortPotentialConst_nonneg (ι := ι) s M hs hs2 hM
  have hB : 0 ≤ (7 / 4 : ℝ) * γ * (periodicRieszShortPotentialConst ι s M *
      (2 * η) ^ ((Fintype.card ι : ℝ) - s)) := by
    have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * η) ((Fintype.card ι : ℝ) - s)
    positivity
  have h := periodic_normalized_pair_le N hN
    (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortTransport n s η v))
    (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortPair s (2 * η)))
    (σ * periodicRieszCoefficient ι s n K γ) (-γ / 2) _ hB
    (fun q => by
      have := periodicRieszShortAbsorption_pointwise s η n hs hs2 hη γ σ hγ hσ hv ρ M hM hρ q
      have e : -γ / 2 * hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (periodicRieszShortPair s (2 * η)) q =
          -(γ / 2 * hoeffdingCentered (periodicCappedDensityMeasure ρ)
            (periodicRieszShortPair s (2 * η)) q) := by ring
      rw [e]
      linarith) ω
  have e2 : -2 * (σ * periodicRieszCoefficient ι s n K γ) * iidNegativeStatistic N
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortTransport n s η v)) ω -
      2 * (-γ / 2) * iidNegativeStatistic N
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortPair s (2 * η))) ω =
      -2 * σ * periodicRieszCoefficient ι s n K γ * iidNegativeStatistic N
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortTransport n s η v)) ω +
      γ * iidNegativeStatistic N
        (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszShortPair s (2 * η))) ω := by ring
  rw [e2] at h
  refine h.trans (le_of_eq ?_)
  ring

lemma periodicRieszAbsorption_scale (s η M : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (hη : 0 < η) (hM : 0 ≤ M) :
    (7 / 4 : ℝ) * (periodicRieszShortPotentialConst ι s M * (2 * η) ^ ((Fintype.card ι : ℝ) - s)) ≤
      periodicRieszAbsConst ι s M * η ^ ((Fintype.card ι : ℝ) - s) := by
  have hp : 0 ≤ η ^ ((Fintype.card ι : ℝ) - s) := Real.rpow_nonneg hη.le _
  have h2 : (2 * η) ^ ((Fintype.card ι : ℝ) - s) =
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) - s) * η ^ ((Fintype.card ι : ℝ) - s) :=
    Real.mul_rpow (by norm_num) hη.le
  rw [h2]
  unfold periodicRieszAbsConst
  nlinarith [hp]

/-- Almost-sure reduction of the local exponent to the cutoff statistic. -/
theorem ae_periodicRieszLocalExponent_cutoff_bound (s η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hη : 0 < η) (hη4 : 2 * η ≤ periodicRieszTau) (γ σ : ℝ)
    (hγ : 0 ≤ γ) (hσ : |σ| ≤ 1) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      periodicRieszLocalExponent s hs2 ρ M n γ σ K v N ω ≤
        (7 / 4 : ℝ) * γ * periodicRieszPotConst s hs2 M +
          (1 / 2 : ℝ) * iidNegativeStatistic N
            (periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s η n γ σ K v) ω +
          periodicRieszAbsConst ι s M * γ * (N : ℝ) * η ^ ((Fintype.card ι : ℝ) - s) := by
  have hητ : η ≤ periodicRieszTau := by linarith
  have hT := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) N _ _
    (ae_periodicCenteredTransport_split ρ M hρ n hn s η hs hs2 hη hητ hv)
  have hE := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) N _ _
    (ae_periodicCenteredPair_split ρ M hρ s (2 * η) hs hs2 (by positivity) hη4)
  have hQ := ae_periodicRieszCutoff_statistic ρ M hρ n hn s η hs hs2 hη hη4 γ σ hv N
  filter_upwards [hT, hE, hQ] with ω hωT hωE hωQ
  rw [physical_iidNegativeStatistic_add] at hωT hωE
  have hS := periodicRieszShortAbsorption_statistic s η n hs hs2 hη γ σ hγ hσ hv ρ M hM hρ N hN ω
  have hB := periodicRieszLocal_oneBody_bound s hs hs2 ρ M hM hρ γ hγ N hN ω
  have hA := mul_le_mul_of_nonneg_left (periodicRieszAbsorption_scale s η M hs hs2 hη hM)
    (by positivity : 0 ≤ γ * (N : ℝ))
  unfold periodicRieszLocalExponent
  rw [periodic_sourceParticleExponent_eq, hωT, hωE]
  nlinarith [hS, hB, hA, hωQ]

/-- An exponent of size `≥ u` forces a cutoff statistic of size `≥ u` at the adaptive scale. -/
theorem ae_periodicRieszLocal_event_reduction (s : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (γ σ : ℝ) (hγ : 0 < γ) (hσ : |σ| ≤ 1)
    {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N)
    (hsmall : (7 / 4 : ℝ) * γ * periodicRieszPotConst s hs2 M ≤ 1 / 4) (u : ℝ) (hu : 1 ≤ u) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      u ≤ periodicRieszLocalExponent s hs2 ρ M n γ σ K v N ω →
      u ≤ iidNegativeStatistic N (periodicRieszCenteredCutoff (periodicCappedDensityMeasure ρ) s
        (gaussianRieszAdaptiveScale (1 / 4) (4 * periodicRieszAbsConst ι s M * γ) N u
          (Fintype.card ι) s) n γ σ K v) ω := by
  let C := periodicRieszAbsConst ι s M
  let η := gaussianRieszAdaptiveScale (1 / 4) (4 * C * γ) N u (Fintype.card ι) s
  have hC : 0 < C := periodicRieszAbsConst_pos s M hs hs2 hM
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hn' : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hN)
  have hu0 : 0 < u := by linarith
  have hη := gaussianRieszAdaptiveScale_pos_le (1 / 4) (4 * C * γ) N u (Fintype.card ι) s (by norm_num)
    (by positivity) hn' hu0
  have hp := gaussianRieszAdaptiveScale_power_le (1 / 4) (4 * C * γ) N u (Fintype.card ι) s
    (by norm_num) (by positivity) hn' hu0 (by linarith)
  have hlast : C * γ * (N : ℝ) * η ^ ((Fintype.card ι : ℝ) - s) ≤ u / 4 := by
    have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ C * γ * (N : ℝ))
    change C * γ * (N : ℝ) * η ^ ((Fintype.card ι : ℝ) - s) ≤
      C * γ * (N : ℝ) * (u / (4 * C * γ * (N : ℝ))) at h
    convert h using 1
    field_simp [hC.ne', hγ.ne', hn'.ne']
  have h4 : 2 * η ≤ periodicRieszTau := by
    have := hη.2
    unfold periodicRieszTau
    linarith
  filter_upwards [ae_periodicRieszLocalExponent_cutoff_bound s η n hn hs hs2 hη.1 h4 γ σ hγ.le hσ hv
    ρ M hM hρ N hN] with ω hω
  intro hx
  nlinarith [hω, hsmall, hlast, hu]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszLocal_oneBody_bound
#print axioms DGRHS.Periodic.periodicRieszShortAbsorption_statistic
#print axioms DGRHS.Periodic.ae_periodicRieszLocalExponent_cutoff_bound
#print axioms DGRHS.Periodic.ae_periodicRieszLocal_event_reduction
