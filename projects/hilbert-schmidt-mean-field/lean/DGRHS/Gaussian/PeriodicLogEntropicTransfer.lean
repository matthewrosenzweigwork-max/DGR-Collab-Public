import DGRHS.Gaussian.PeriodicLogGibbsMoments
import DGRHS.CLT.SourceRawEnergy
import DGRHS.Entropy.GibbsEntropicTransfer
import DGRHS.Entropy.GibbsExtendedRewrite

/-!
Packet P9h, unit 3 (LOG, part 12): the torus LOG background energy, its pointwise lower bound, the
genuine extended (all-law) free energy and the entropic transfer of the Gibbs transport moments to
every probability competitor (torus versions of `sourceLogEnergy_uniform_lower_bound`,
`sourceLogExtendedFreeEnergy_rewrite`, `sourceLog_entropic_all_laws`).

The smooth pointwise representative `periodicLogPair` of the spectral LOG kernel is finite on the
diagonal; the competitors with infinite relative entropy are sent to `+∞` by the extended free
energy, exactly as in the singular (collision) Euclidean definition (a competitor of finite relative
entropy is absolutely continuous with respect to the collision-free product law).
-/

noncomputable section
open MeasureTheory InformationTheory Set Metric Filter
open scoped Classical BigOperators NNReal ENNReal
namespace DGRHS.Periodic
open DGRHS.Commutator DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The pointwise cap constant of the physical LOG background energy. -/
def periodicLogBgConst (ι : Type u) [Fintype ι] [Nonempty ι] (M : ℝ) : ℝ :=
  periodicLogPairLower ι + M * ∫ z, |periodicLogKernel (ι := ι) z| ∂periodicHaar ι

/-- The physical background energy `N F_N`. -/
def periodicLogTransportBackgroundEnergy (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) (ω : Fin N → PeriodicTorus ι) : ℝ :=
  (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered (periodicCappedDensityMeasure ρ) periodicLogPair)
    (DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogPair (a, b)))
    (DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogPair (a, b))) N ω

lemma periodicLogParticleExponent_background (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (β : ℝ) (N : ℕ)
    (ω : Fin N → PeriodicTorus ι) :
    periodicLogParticleExponent ρ β N ω = -β * periodicLogTransportBackgroundEnergy ρ N ω := by
  unfold periodicLogParticleExponent periodicLogTransportBackgroundEnergy
  ring

lemma periodicLogInteraction_lower (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    -(periodicLogPairLower ι / 2) ≤ DGRHS.interactionEnergy (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogPair (a, b)) := by
  have hw := periodicLogPairLower_nonneg (ι := ι)
  unfold DGRHS.interactionEnergy
  have : -(periodicLogPairLower ι) ≤ ∫ z, periodicLogPair (z.1, z.2)
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ) := by
    by_cases hi : Integrable (fun z : PeriodicTorus ι × PeriodicTorus ι => periodicLogPair (z.1, z.2))
        ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ))
    · have := integral_mono (integrable_const (-(periodicLogPairLower ι))) hi
        (fun z => periodicLogPair_lower (z.1, z.2))
      simpa using this
    · rw [integral_undef hi]
      linarith
  linarith

lemma periodicLogTransportBackgroundEnergy_lower (M : ℝ) (hM : 0 ≤ M) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (N : ℕ) (hN : 1 ≤ N) (ω : Fin N → PeriodicTorus ι) :
    -(N : ℝ) * periodicLogBgConst ι M ≤ periodicLogTransportBackgroundEnergy ρ N ω := by
  let μ := periodicCappedDensityMeasure ρ
  let W := fun a b : PeriodicTorus ι => periodicLogPair (a, b)
  let w := periodicLogPairLower ι
  let pk := M * ∫ z, |periodicLogKernel (ι := ι) z| ∂periodicHaar ι
  have hn : 0 < N := by omega
  have hn' : 0 < (N : ℝ) := by exact_mod_cast hn
  have hw := periodicLogPairLower_nonneg (ι := ι)
  have hpk : 0 ≤ pk := mul_nonneg hM (integral_nonneg fun z => abs_nonneg _)
  have hraw := DGRHS.CLT.sourceCanonicalModulatedEnergy_raw μ W
    (fun a b => by
      have := periodicLogPair_symm (ι := ι) (a, b)
      exact this.symm) N hn ω
  change -(N : ℝ) * periodicLogBgConst ι M ≤
    (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy (fun p => DGRHS.centeredKernel μ W p.1 p.2)
      (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N ω
  rw [hraw]
  have hoff : -((N : ℝ) ^ 2 * w) ≤ DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry W) ω := by
    unfold DGRHS.CanonicalVariance.offDiagonalSum
    have h1 : ∑ _p ∈ (Finset.univ : Finset (Fin N)).offDiag, (-w) ≤
        ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag, Function.uncurry W (ω p.1, ω p.2) :=
      Finset.sum_le_sum fun p _ => periodicLogPair_lower _
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
    periodicLogPair_potential_abs_le ρ M hM hρ (ω i)
  have hsum : (∑ i : Fin N, DGRHS.potential μ W (ω i)) ≤ (N : ℝ) * pk := by
    calc _ ≤ ∑ _ : Fin N, pk := Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hF i)
      _ = _ := by simp
  have hI : -(w / 2) ≤ DGRHS.interactionEnergy μ W := periodicLogInteraction_lower ρ
  have hlow : -(w + pk) ≤ (2 * (N : ℝ) ^ 2)⁻¹ * DGRHS.CanonicalVariance.offDiagonalSum
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
  unfold periodicLogBgConst
  nlinarith [this]

/-- The genuine extended free energy (`+∞` kept) on the torus. -/
def periodicLogTransportExtendedFreeEnergy (ρ : PeriodicTorus ι → ℝ) (M β : ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (N : ℕ) (ν : Measure (Fin N → PeriodicTorus ι)) : EReal :=
  DGRHS.Entropy.gibbsExtendedFreeEnergy
    (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) ν
    (periodicLogParticleExponent ρ β N)
    (β * (N : ℝ) * periodicLogBgConst ι M) * ((β * (N : ℝ))⁻¹ : ℝ)

/-- The real modulated free energy on its proper domain. -/
def periodicLogTransportProperFreeEnergy (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (β : ℝ) (N : ℕ)
    (ν : Measure (Fin N → PeriodicTorus ι)) : ℝ :=
  (klDiv ν (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))).toReal / (β * (N : ℝ)) +
    (N : ℝ)⁻¹ * (∫ ω, periodicLogTransportBackgroundEnergy ρ N ω ∂ν)

lemma periodicLogParticleExponent_cap (M : ℝ) (hM : 0 ≤ M) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 1 ≤ N)
    (ω : Fin N → PeriodicTorus ι) :
    periodicLogParticleExponent ρ β N ω ≤ β * (N : ℝ) * periodicLogBgConst ι M := by
  rw [periodicLogParticleExponent_background]
  have h := periodicLogTransportBackgroundEnergy_lower M hM ρ hρ N hN ω
  nlinarith [mul_le_mul_of_nonpos_left h (show -β ≤ 0 by linarith)]

lemma periodicLogTransportExtendedFreeEnergy_rewrite (M : ℝ) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N)
    (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν] :
    periodicLogTransportExtendedFreeEnergy ρ M β N ν =
      ((klDiv ν (periodicLogSingularGibbs β ρ N) : EReal) -
        (Real.log (∫ ω, Real.exp (periodicLogParticleExponent ρ β N ω)
          ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)) : ℝ)) *
        ((β * (N : ℝ))⁻¹ : ℝ) := by
  obtain ⟨Cpf, hCpf, hPart⟩ := periodicLogParticleWeight_uniform β hβ.le ρ M hM hρ
  unfold periodicLogTransportExtendedFreeEnergy
  rw [DGRHS.Entropy.gibbsExtendedFreeEnergy_rewrite _ ν _ _
    (periodicLogParticleExponent_cap M hM ρ hρ β hβ N hN) (hPart N hN).1,
    ← periodicLogSingularGibbs_eq_particle β hβ.le ρ M hM hρ N hN]

lemma periodicLogTransportExtendedFreeEnergy_eq_proper (M : ℝ) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N)
    (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (hac : ν ≪ Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))
    (he : Integrable (periodicLogTransportBackgroundEnergy ρ N) ν)
    (hllr : Integrable (llr ν (Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ))) ν) :
    periodicLogTransportExtendedFreeEnergy ρ M β N ν =
      (periodicLogTransportProperFreeEnergy ρ β N ν : ℝ) := by
  let P := Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)
  let u := periodicLogParticleExponent ρ β N
  have hu : Integrable u ν := by
    apply (he.const_mul (-β)).congr
    exact ae_of_all _ fun ω => by
      change -β * periodicLogTransportBackgroundEnergy ρ N ω = periodicLogParticleExponent ρ β N ω
      exact (periodicLogParticleExponent_background ρ β N ω).symm
  obtain ⟨Cpf, hCpf, hPart⟩ := periodicLogParticleWeight_uniform β hβ.le ρ M hM hρ
  have hz : Integrable (fun ω => Real.exp (u ω)) P := (hPart N hN).1
  have hcap := periodicLogParticleExponent_cap M hM ρ hρ β hβ N hN
  have hK : klDiv ν (P.tilted u) ≠ ∞ :=
    (DGRHS.Entropy.gibbsKL_finite_domain P ν u _ hcap hz).mpr ⟨hac, hu, hllr⟩
  have hreal := (DGRHS.Entropy.gibbsEntropy_rewrite P ν u hac hu hz hllr).2
  have hQ : periodicLogSingularGibbs β ρ N = P.tilted u :=
    periodicLogSingularGibbs_eq_particle β hβ.le ρ M hM hρ N hN
  rw [periodicLogTransportExtendedFreeEnergy_rewrite M hM β hβ ρ hρ N hN ν, hQ,
    ← EReal.coe_ennreal_toReal hK, hreal, ← EReal.coe_sub, ← EReal.coe_mul]
  congr 1
  have hInt : (∫ ω, u ω ∂ν) = -β * (∫ ω, periodicLogTransportBackgroundEnergy ρ N ω ∂ν) := by
    dsimp only [u]
    simp_rw [periodicLogParticleExponent_background]
    exact integral_const_mul _ _
  rw [hInt]
  unfold periodicLogTransportProperFreeEnergy
  dsimp only [P, u]
  field_simp [hβ.ne', (show (N : ℝ) ≠ 0 by exact_mod_cast (by omega : N ≠ 0))]
  <;> ring

/-- The entropic transfer for every probability competitor and a bounded measurable observable. -/
theorem periodicLog_entropic_all_laws (M : ℝ) (hM : 0 ≤ M) (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) (hN : 1 ≤ N)
    (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν]
    (a : (Fin N → PeriodicTorus ι) → ℝ) (ha : StronglyMeasurable a) (A : ℝ) (hA : ∀ x, |a x| ≤ A)
    (ε : ℝ) (hε : 0 < ε)
    (hp : Integrable (fun x => Real.exp (ε * a x)) (periodicLogSingularGibbs β ρ N))
    (hm : Integrable (fun x => Real.exp (-(ε * a x))) (periodicLogSingularGibbs β ρ N))
    (Cpf Cem : ℝ) (hCpf : (periodicLogSingularPartition β ρ N).toReal ≤ Cpf)
    (hCp : (∫ x, Real.exp (ε * a x) ∂periodicLogSingularGibbs β ρ N) ≤ Cem)
    (hCm : (∫ x, Real.exp (-(ε * a x)) ∂periodicLogSingularGibbs β ρ N) ≤ Cem) :
    Integrable a ν ∧
      ((|∫ x, a x ∂ν| : ℝ) : EReal) ≤ (((β / ε) * (N : ℝ) : ℝ) : EReal) *
          periodicLogTransportExtendedFreeEnergy ρ M β N ν +
        ((ε⁻¹ * (Real.log Cpf + Real.log Cem) : ℝ) : EReal) := by
  have hai : Integrable a ν := (integrable_const A).mono' ha.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hA x)
  refine ⟨hai, ?_⟩
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hb : 0 < β * (N : ℝ) := mul_pos hβ hn
  have hc : 0 < (β / ε) * (N : ℝ) := mul_pos (div_pos hβ hε) hn
  by_cases hKL : klDiv ν (periodicLogSingularGibbs β ρ N) = ∞
  · rw [periodicLogTransportExtendedFreeEnergy_rewrite M hM β hβ ρ hρ N hN ν, hKL]
    simp only [EReal.coe_ennreal_top, EReal.top_sub_coe, EReal.top_mul_coe_of_pos (inv_pos.mpr hb),
      EReal.coe_mul_top_of_pos hc, EReal.top_add_coe]
    exact le_top
  · obtain ⟨Cp, hCp0, hPart⟩ := periodicLogParticleWeight_uniform β hβ.le ρ M hM hρ
    let P := Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)
    let Ebg := periodicLogTransportBackgroundEnergy ρ N
    have hQ : periodicLogSingularGibbs β ρ N = P.tilted (fun ω => -β * Ebg ω) := by
      rw [periodicLogSingularGibbs_eq_particle β hβ.le ρ M hM hρ N hN]
      congr 1
      funext ω
      exact periodicLogParticleExponent_background ρ β N ω
    have hz : Integrable (fun ω => Real.exp (-β * Ebg ω)) P := by
      simpa only [periodicLogParticleExponent_background] using (hPart N hN).1
    have hzb : (∫ ω, Real.exp (-β * Ebg ω) ∂P) ≤ Cpf := by
      have h := hCpf
      rw [periodicLogSingularPartition_toReal_eq β hβ.le ρ M hM hρ N hN] at h
      simpa only [periodicLogParticleExponent_background] using h
    rw [hQ] at hp hm hCp hCm hKL
    obtain ⟨hac, he, hllr, -, hbound⟩ := DGRHS.Entropy.gibbs_entropic_transfer P ν Ebg
      (-(N : ℝ) * periodicLogBgConst ι M) β hβ
      (periodicLogTransportBackgroundEnergy_lower M hM ρ hρ N hN) hz a ha ε hε hp hm hKL
      Cpf Cem hzb hCp hCm
    rw [periodicLogTransportExtendedFreeEnergy_eq_proper M hM β hβ ρ hρ N hN ν hac he hllr,
      ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hNreal : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have halgebra : (β / ε) * (N : ℝ) * periodicLogTransportProperFreeEnergy ρ β N ν =
        ε⁻¹ * ((klDiv ν P).toReal + β * (∫ ω, Ebg ω ∂ν)) := by
      unfold periodicLogTransportProperFreeEnergy
      dsimp only [P, Ebg]
      field_simp [hβ.ne', hε.ne', hNreal]
    rw [halgebra]
    exact hbound

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLogTransportBackgroundEnergy_lower
#print axioms DGRHS.Periodic.periodicLogTransportExtendedFreeEnergy_rewrite
#print axioms DGRHS.Periodic.periodicLogTransportExtendedFreeEnergy_eq_proper
#print axioms DGRHS.Periodic.periodicLog_entropic_all_laws
