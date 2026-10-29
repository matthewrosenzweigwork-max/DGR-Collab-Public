import DGRHS.Gaussian.PeriodicRieszTransportGibbs
import DGRHS.CLT.SourceRawEnergy
import DGRHS.Entropy.GibbsEntropicTransfer
import DGRHS.Entropy.GibbsExtendedRewrite

/-!
Packet P9h, unit 2 (part 29): the torus background energy, its pointwise lower bound, the extended
(all-law) free energy, and the finite-relative-entropy transfer of the Gibbs transport moments
(torus versions of `SourceRieszEntropicTransport`, `SourceRieszExtendedFreeEnergy` and
`SourceRieszTransportFreeEnergyIdentification`).
-/

noncomputable section
open MeasureTheory InformationTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- A pointwise lower bound constant of the smooth representative of the periodic Riesz kernel. -/
def periodicRieszPairLower (ι : Type u) [Fintype ι] [Nonempty ι] (s : ℝ) : ℝ :=
  periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι * (periodicRieszTau ^ (-s) / s) +
    periodicRieszLongBound (ι := ι) s 0 + periodicRieszMeanConst ι s

lemma periodicRieszPairLower_nonneg (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    0 ≤ periodicRieszPairLower ι s := by
  have h1 := (periodicRieszSmoothCoeff_pos (ι := ι) s hs).le
  have h2 := (periodicLatticeGaussConst_pos (ι := ι)).le
  have h3 := periodicRieszLongBound_nonneg (ι := ι) s hs 0
  have h4 := periodicRieszMeanConst_nonneg (ι := ι) s hs hs2
  have h5 : 0 ≤ periodicRieszTau ^ (-s) := Real.rpow_nonneg periodicRieszTau_pos.le _
  unfold periodicRieszPairLower
  positivity

lemma periodicRieszPair_lower (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (p : PeriodicTorus ι × PeriodicTorus ι) : -periodicRieszPairLower ι s ≤ periodicRieszPair s p := by
  have h := periodicRieszPair_split s periodicRieszTau hs periodicRieszTau_pos le_rfl p
  have hS : 0 ≤ periodicRieszShortPair (ι := ι) s periodicRieszTau p := by
    rw [periodicRieszShortPair_eq]
    exact periodicRieszShortFun_nonneg s _ hs _
  have hL := periodicRieszLongPair_cap s periodicRieszTau hs hs2 periodicRieszTau_pos le_rfl p
  have := (abs_le.mp hL).1
  have e : periodicRieszPairLower ι s = periodicRieszSmoothCoeff ι s * periodicLatticeGaussConst ι *
      (periodicRieszTau ^ (-s) / s) + periodicRieszLongBound (ι := ι) s 0 +
        periodicRieszMellinFactor ι s * (periodicHeatCut periodicRieszTau) ^ (((Fintype.card ι : ℝ) - s) / 2) /
          (((Fintype.card ι : ℝ) - s) / 2) := rfl
  rw [e]
  linarith

/-- The pointwise cap constant of the physical background energy. -/
def periodicRieszBgConst (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) : ℝ :=
  periodicRieszPairLower ι s / 2 + M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι

/-- The physical background energy `N F_N`. -/
def periodicRieszTransportBackgroundEnergy (s : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) (ω : Fin N → PeriodicTorus ι) : ℝ :=
  (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered (periodicCappedDensityMeasure ρ) (periodicRieszPair s))
    (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)))
    (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicRieszPair s (a, b))) N ω

lemma periodicRieszParticleExponent_background (s : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (β : ℝ) (N : ℕ)
    (ω : Fin N → PeriodicTorus ι) :
    periodicRieszParticleExponent s ρ β N ω = -β * periodicRieszTransportBackgroundEnergy s ρ N ω := by
  unfold periodicRieszParticleExponent periodicRieszTransportBackgroundEnergy
  ring

lemma periodicRieszTransportBackgroundEnergy_lower (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → PeriodicTorus ι) :
    -(N : ℝ) * periodicRieszBgConst s hs2 M ≤ periodicRieszTransportBackgroundEnergy s ρ N ω := by
  let μ := periodicCappedDensityMeasure ρ
  let W := fun a b : PeriodicTorus ι => periodicRieszPair s (a, b)
  let w := periodicRieszPairLower ι s
  let pk := M * ∫ z, |periodicRieszKernel s hs2 z| ∂periodicHaar ι
  have hn : 0 < N := by omega
  have hn' : 0 < (N : ℝ) := by exact_mod_cast hn
  have hw := periodicRieszPairLower_nonneg (ι := ι) s hs hs2
  have hpk : 0 ≤ pk := mul_nonneg hM (integral_nonneg fun z => abs_nonneg _)
  have hraw := DGRHS.CLT.sourceCanonicalModulatedEnergy_raw μ W
    (fun a b => by
      have := periodicRieszPair_symm (ι := ι) s (a, b)
      exact this.symm) N hn ω
  change -(N : ℝ) * periodicRieszBgConst s hs2 M ≤
    (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy (fun p => DGRHS.centeredKernel μ W p.1 p.2)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N ω
  rw [hraw]
  -- the off-diagonal sum
  have hoff : -((N : ℝ) ^ 2 * w) ≤ DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ω := by
    unfold DGRHS.CanonicalVariance.offDiagonalSum
    have h1 : ∑ _p ∈ (Finset.univ : Finset (Fin N)).offDiag, (-w) ≤
        ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, Function.uncurry W (ω p.1, ω p.2) :=
      Finset.sum_le_sum fun p _ => periodicRieszPair_lower s hs hs2 _
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have hcard : (((Finset.univ : Finset (Fin N)).offDiag.card : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
      have : (Finset.univ : Finset (Fin N)).offDiag.card ≤ N * N := by
        rw [Finset.offDiag_card]
        simpa using Nat.sub_le (N * N) N
      have h2 : (((Finset.univ : Finset (Fin N)).offDiag.card : ℕ) : ℝ) ≤ ((N * N : ℕ) : ℝ) :=
        Nat.cast_le.mpr this
      push_cast at h2
      nlinarith [h2]
    nlinarith [mul_le_mul_of_nonneg_right hcard hw]
  have hF : ∀ i, |DGRHS.potential μ W (ω i)| ≤ pk := fun i =>
    periodicRieszPair_potential_abs_le s hs hs2 ρ M hM hρ (ω i)
  have hsum : (∑ i : Fin N, DGRHS.potential μ W (ω i)) ≤ (N : ℝ) * pk := by
    calc _ ≤ ∑ _ : Fin N, pk := Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hF i)
      _ = _ := by simp
  have hI : 0 ≤ DGRHS.interactionEnergy μ W := periodicRieszInteraction_nonneg s hs hs2 ρ M hM hρ
  have hlow : -(w / 2 + pk) ≤ (2 * (N : ℝ) ^ 2)⁻¹ * DGRHS.CanonicalVariance.offDiagonalSum
        (Function.uncurry W) ω - (N : ℝ)⁻¹ * (∑ i : Fin N, DGRHS.potential μ W (ω i)) +
      DGRHS.interactionEnergy μ W := by
    have h1 : -(w / 2) ≤ (2 * (N : ℝ) ^ 2)⁻¹ * DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ω := by
      have := mul_le_mul_of_nonneg_left hoff (by positivity : 0 ≤ (2 * (N : ℝ) ^ 2)⁻¹)
      refine le_trans (le_of_eq ?_) this
      field_simp
    have h2 : (N : ℝ)⁻¹ * (∑ i : Fin N, DGRHS.potential μ W (ω i)) ≤ pk := by
      have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hn'.le)
      simpa only [← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul] using h
    linarith
  have := mul_le_mul_of_nonneg_left hlow hn'.le
  unfold periodicRieszBgConst
  nlinarith [this]

/-- The genuine extended free energy (`+∞` kept) on the torus. -/
def periodicRieszTransportExtendedFreeEnergy (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (M β : ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (N : ℕ) (ν : Measure (Fin N → PeriodicTorus ι)) : EReal :=
  DGRHS.Entropy.gibbsExtendedFreeEnergy
    (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ν
    (periodicRieszParticleExponent s ρ β N)
    (β * (N : ℝ) * periodicRieszBgConst s hs2 M) * ((β * (N : ℝ))⁻¹ : ℝ)

/-- The real modulated free energy on its proper domain. -/
def periodicRieszTransportProperFreeEnergy (s : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (β : ℝ) (N : ℕ)
    (ν : Measure (Fin N → PeriodicTorus ι)) : ℝ :=
  (klDiv ν (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))).toReal / (β * (N : ℝ)) +
    (N : ℝ)⁻¹ * (∫ ω, periodicRieszTransportBackgroundEnergy s ρ N ω ∂ν)

lemma periodicRieszParticleExponent_cap (s : ℝ) (hs : 0 < s) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (M : ℝ) (hM : 0 ≤ M) (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 1 ≤ N)
    (ω : Fin N → PeriodicTorus ι) :
    periodicRieszParticleExponent s ρ β N ω ≤ β * (N : ℝ) * periodicRieszBgConst s hs2 M := by
  rw [periodicRieszParticleExponent_background]
  have h := periodicRieszTransportBackgroundEnergy_lower s hs hs2 M hM ρ hρ N hN ω
  nlinarith [mul_le_mul_of_nonpos_left h (show -β ≤ 0 by linarith)]

lemma periodicRieszTransportExtendedFreeEnergy_rewrite (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N)
    (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν] :
    periodicRieszTransportExtendedFreeEnergy s hs2 ρ M β N ν =
      ((klDiv ν (periodicRieszSingularGibbs s β hs2 ρ N) : EReal) -
        (Real.log (∫ ω, Real.exp (periodicRieszParticleExponent s ρ β N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) : ℝ)) *
        ((β * (N : ℝ))⁻¹ : ℝ) := by
  obtain ⟨Cpf, hCpf, hPart⟩ := periodicRieszParticleWeight_uniform s β hs hβ.le hs2 ρ M hM hρ
  unfold periodicRieszTransportExtendedFreeEnergy
  rw [DGRHS.Entropy.gibbsExtendedFreeEnergy_rewrite _ ν _ _
    (periodicRieszParticleExponent_cap s hs hs2 M hM ρ hρ β hβ N hN) (hPart N hN).1,
    ← periodicRieszSingularGibbs_eq_particle s β hs hβ.le hs2 ρ M hM hρ N hN]

lemma periodicRieszTransportExtendedFreeEnergy_eq_proper (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (M : ℝ) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N)
    (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (hac : ν ≪ Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))
    (he : Integrable (periodicRieszTransportBackgroundEnergy s ρ N) ν)
    (hllr : Integrable (llr ν (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) ν) :
    periodicRieszTransportExtendedFreeEnergy s hs2 ρ M β N ν =
      (periodicRieszTransportProperFreeEnergy s ρ β N ν : ℝ) := by
  let P := Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)
  let u := periodicRieszParticleExponent s ρ β N
  have hu : Integrable u ν := by
    apply (he.const_mul (-β)).congr
    exact ae_of_all _ fun ω => by
      change -β * periodicRieszTransportBackgroundEnergy s ρ N ω = periodicRieszParticleExponent s ρ β N ω
      exact (periodicRieszParticleExponent_background s ρ β N ω).symm
  obtain ⟨Cpf, hCpf, hPart⟩ := periodicRieszParticleWeight_uniform s β hs hβ.le hs2 ρ M hM hρ
  have hz : Integrable (fun ω => Real.exp (u ω)) P := (hPart N hN).1
  have hcap := periodicRieszParticleExponent_cap s hs hs2 M hM ρ hρ β hβ N hN
  have hK : klDiv ν (P.tilted u) ≠ ∞ :=
    (DGRHS.Entropy.gibbsKL_finite_domain P ν u _ hcap hz).mpr ⟨hac, hu, hllr⟩
  have hreal := (DGRHS.Entropy.gibbsEntropy_rewrite P ν u hac hu hz hllr).2
  have hQ : periodicRieszSingularGibbs s β hs2 ρ N = P.tilted u :=
    periodicRieszSingularGibbs_eq_particle s β hs hβ.le hs2 ρ M hM hρ N hN
  rw [periodicRieszTransportExtendedFreeEnergy_rewrite s hs hs2 M hM β hβ ρ hρ N hN ν, hQ,
    ← EReal.coe_ennreal_toReal hK, hreal, ← EReal.coe_sub, ← EReal.coe_mul]
  congr 1
  have hInt : (∫ ω, u ω ∂ν) = -β * (∫ ω, periodicRieszTransportBackgroundEnergy s ρ N ω ∂ν) := by
    dsimp only [u]
    simp_rw [periodicRieszParticleExponent_background]
    exact integral_const_mul _ _
  rw [hInt]
  unfold periodicRieszTransportProperFreeEnergy
  dsimp only [P, u]
  field_simp [hβ.ne', (show (N : ℝ) ≠ 0 by exact_mod_cast (by omega : N ≠ 0))]
  <;> ring

lemma measurable_periodicRieszScaledTransportEnergy (s : ℝ) (n : ℕ) (hn : 1 ≤ n) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) {K : ℝ≥0} {v : PeriodicTorus ι → E} (hv : LipschitzWith K v)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ)
    (hN : 1 ≤ N) :
    Measurable (fun ω : Fin N → PeriodicTorus ι => (N : ℝ) * periodicRieszTransportEnergy s n v ρ N ω) := by
  have hm := ((measurable_physical_iidNegativeStatistic N _
    (stronglyMeasurable_hoeffdingCentered (periodicCappedDensityMeasure ρ) _
      (periodicRieszTransportKernel_measurable n hn s hs hs2 hv).stronglyMeasurable).measurable).const_mul
        (-2)).add (measurable_periodicRieszTransportCorrection n hn s hs hs2 hv ρ N)
  convert hm using 1
  funext ω
  exact periodicRieszTransportEnergy_scaled s n v ρ N (by omega) ω

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicRieszPair_lower
#print axioms DGRHS.Periodic.periodicRieszTransportBackgroundEnergy_lower
#print axioms DGRHS.Periodic.periodicRieszTransportExtendedFreeEnergy_rewrite
#print axioms DGRHS.Periodic.periodicRieszTransportExtendedFreeEnergy_eq_proper
