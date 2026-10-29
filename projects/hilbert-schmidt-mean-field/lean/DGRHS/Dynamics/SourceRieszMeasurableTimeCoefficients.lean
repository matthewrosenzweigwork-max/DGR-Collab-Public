/- Theorem 2.9 (positive Riesz), measurable time coefficients.

Positive Riesz analogue of `SourceLogMeasurableTimeCoefficients`: the n=1
finite-relative-entropy entropic commutator estimate provides constants that
depend only on the scalar controls (Lipschitz bound, density cap).  Constants
are chosen once for each pair of integer ceilings and composed with `Nat.ceil`
of the measurable controls, so measurability in time is proved. -/
import DGRHS.Commutator.SourceRieszPhysicalTime
import DGRHS.Dynamics.SourceDiffusiveLocal
import Mathlib.MeasureTheory.Function.Floor
noncomputable section
open MeasureTheory InformationTheory Set Filter
open scoped NNReal ENNReal Interval
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

/-- The extended physical Riesz free energy does not depend on the auxiliary
density cap used for its normalization constant. -/
theorem sourceRieszTransportExtendedFreeEnergy_cap_independent (s : ℝ) (hs : 0 < s)
    (hd : 2 * s < (Fintype.card ι : ℝ)) (β : ℝ) (hβ : 0 < β)
    (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (M₁ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hρ₁ : ∀ᵐ x ∂volume, ρ x ≤ M₁) (hρ₂ : ∀ᵐ x ∂volume, ρ x ≤ M₂)
    (N : ℕ) (hN : 1 ≤ N) (ν : Measure (Fin N → EuclideanSpace ℝ ι))
    [IsProbabilityMeasure ν] :
    sourceRieszTransportExtendedFreeEnergy ρ s M₁ β N ν =
      sourceRieszTransportExtendedFreeEnergy ρ s M₂ β N ν := by
  have r1 := sourceRieszTransportExtendedFreeEnergy_rewrite s M₁ hs hd hM₁ β hβ ρ hρ₁ N hN ν
  have r2 := sourceRieszTransportExtendedFreeEnergy_rewrite s M₂ hs hd hM₂ β hβ ρ hρ₂ N hN ν
  rw [r1, r2]

/-- The Riesz n=1 commutator bound with constants `a b`, valid for every
velocity with Lipschitz constant at most `p`, every background with density
cap at most `q`, and every particle number and law with finite physical free
energy `e`. -/
def SourceRieszScalarControlBound (s β : ℝ) (p q : ℕ) (a b : ℝ) : Prop :=
  ∀ (v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (K : ℝ≥0),
  LipschitzWith K v → (K : ℝ) ≤ (p : ℝ) →
  ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ),
  IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) → 0 ≤ M → M ≤ (q : ℝ) →
  (∀ᵐ x ∂volume, ρ x ≤ M) →
  ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Fin N → EuclideanSpace ℝ ι),
  IsProbabilityMeasure ν → ∀ e : ℝ,
  sourceRieszTransportExtendedFreeEnergy ρ s M β N ν = (e : EReal) →
  Integrable (fun ω => (N : ℝ) * sourceRieszLocalTransportEnergy ρ s 1 v N ω) ν ∧
  |∫ ω, (N : ℝ) * sourceRieszLocalTransportEnergy ρ s 1 v N ω ∂ν| ≤
    a * (N : ℝ) * e + b

/-- Constants indexed by the integer ceilings of the scalar controls. -/
theorem exists_sourceRiesz_scalar_control_coefficients (s β : ℝ) (hs : 0 < s)
    (hd : 2 * s < (Fintype.card ι : ℝ)) (hβ : 0 < β) :
    ∃ A B : ℕ → ℕ → ℝ, (∀ p q, 0 ≤ A p q ∧ 0 ≤ B p q) ∧
      ∀ p q, SourceRieszScalarControlBound (ι := ι) s β p q (A p q) (B p q) := by
  classical
  have hp : ∀ p q : ℕ, ∃ a b : ℝ, (0 ≤ a ∧ 0 ≤ b) ∧
      SourceRieszScalarControlBound (ι := ι) s β p q a b := by
    intro p q
    obtain ⟨Cpf, Cem, hCpf, hCem, hFamily⟩ :=
      sourceRieszCommon_finiteObjective_transport (ι := ι) s (q : ℝ) 1 le_rfl hs hd
        (Nat.cast_nonneg q) β hβ
    have hε : 0 < sourceRieszPositiveTransportParameter (ι := ι) s (q : ℝ) 1 (p : ℝ≥0) β :=
      sourceRieszPositiveTransportParameter_pos s (q : ℝ) 1 (p : ℝ≥0) β hs hd
        (Nat.cast_nonneg q) hβ
    refine ⟨β / sourceRieszPositiveTransportParameter (ι := ι) s (q : ℝ) 1 (p : ℝ≥0) β,
      (sourceRieszPositiveTransportParameter (ι := ι) s (q : ℝ) 1 (p : ℝ≥0) β)⁻¹ *
        (Real.log Cpf + Real.log Cem),
      ⟨(div_pos hβ hε).le, mul_nonneg (inv_nonneg.mpr hε.le)
        (add_nonneg (Real.log_nonneg hCpf) (Real.log_nonneg hCem))⟩, ?_⟩
    intro v K hv hKp ρ M hμ hM0 hMq hρ N hN ν hν e he
    haveI := hμ
    haveI := hν
    have hKle : K ≤ (p : ℝ≥0) := by exact_mod_cast hKp
    have hv' : LipschitzWith (p : ℝ≥0) v := hv.weaken hKle
    have hρ' : ∀ᵐ x ∂volume, ρ x ≤ (q : ℝ) := hρ.mono fun x hx => hx.trans hMq
    have he' : sourceRieszTransportExtendedFreeEnergy ρ s (q : ℝ) β N ν = (e : EReal) := by
      rw [← he]
      exact (sourceRieszTransportExtendedFreeEnergy_cap_independent s hs hd β hβ ρ M (q : ℝ)
        hM0 (Nat.cast_nonneg q) hρ hρ' N hN ν).symm
    obtain ⟨hint, -, hbd⟩ := ((hFamily (p : ℝ≥0) v hv').2 ρ hμ hρ' N hN ν e he')
    exact ⟨hint, hbd⟩
  choose A B hAB using hp
  exact ⟨A, B, fun p q => (hAB p q).1, fun p q => (hAB p q).2⟩

/-- Theorem 2.9, positive Riesz, with coefficient functions that are
measurable in time.  The coefficients depend only on `s`, `β`, the dimension
and the measurable scalar controls `Λ` (Lipschitz bound of `v t`) and `M`
(density cap of `ρ t`).  The finiteness of the source factors `𝒜^t`, `ℬ^t`
remains the source hypothesis. -/
theorem exists_sourceRiesz_measurable_diffusive_bound (s β : ℝ) (hs : 0 < s)
    (hd : 2 * s < (Fintype.card ι : ℝ)) (hβ : 0 < β) (Λ M : ℝ → ℝ)
    (hΛ : Measurable Λ) (hM : Measurable M) :
    ∃ a b : ℝ → ℝ, Measurable a ∧ Measurable b ∧ (∀ t, 0 ≤ a t ∧ 0 ≤ b t) ∧
      ∀ (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
        (v : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (K : ℝ → ℝ≥0),
      (∀ t, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ t))) →
      ∀ (N : ℕ), 1 ≤ N →
      ∀ (f : ℝ → Measure (Fin N → EuclideanSpace ℝ ι)),
      (∀ t, IsProbabilityMeasure (f t)) → ∀ (e : ℝ → ℝ) (Tstar : ℝ≥0∞),
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        0 ≤ M t ∧ (∀ᵐ x ∂volume, ρ t x ≤ M t) ∧ LipschitzWith (K t) (v t) ∧
        (K t : ℝ) ≤ Λ t) →
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        sourceRieszTransportExtendedFreeEnergy (ρ t) s (M t) β N (f t) = (e t : EReal)) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → AbsolutelyContinuousOnInterval e 0 T) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceA a T ≠ ∞) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceB a b T ≠ ∞) →
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        deriv e t ≤ |∫ ω, (N : ℝ) * sourceRieszLocalTransportEnergy (ρ t) s 1 (v t) N ω
          ∂f t| / N) →
      ∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar →
        e T ≤ sourceA a T * e 0 + sourceB a b T / N := by
  classical
  obtain ⟨A, B, hAB0, hABb⟩ :=
    exists_sourceRiesz_scalar_control_coefficients (ι := ι) s β hs hd hβ
  have hmeas : ∀ F : ℕ → ℕ → ℝ, Measurable (fun t => F ⌈Λ t⌉₊ ⌈M t⌉₊) := by
    intro F
    have h2 : Measurable (fun t => (⌈Λ t⌉₊, ⌈M t⌉₊)) :=
      hΛ.nat_ceil.prodMk hM.nat_ceil
    exact (measurable_of_countable (fun x : ℕ × ℕ => F x.1 x.2)).comp h2
  refine ⟨fun t => A ⌈Λ t⌉₊ ⌈M t⌉₊, fun t => B ⌈Λ t⌉₊ ⌈M t⌉₊,
    hmeas A, hmeas B, fun t => hAB0 _ _, ?_⟩
  intro ρ v K hμ N hN f hf e Tstar hphys hrepr he hA hB hdiss
  apply source_diffusive_gronwall_local (by omega : 0 < N) he
    (hmeas A).aestronglyMeasurable (hmeas B).aestronglyMeasurable
    (Eventually.of_forall fun t => (hAB0 _ _).1)
    (Eventually.of_forall fun t => (hAB0 _ _).2) hA hB hdiss
  filter_upwards [hphys, hrepr] with t hpt hrt ht htstar
  obtain ⟨hM0, hρ, hv', hKΛ⟩ := hpt ht htstar
  letI := hμ t
  letI := hf t
  exact (hABb ⌈Λ t⌉₊ ⌈M t⌉₊ (v t) (K t) hv' (hKΛ.trans (Nat.le_ceil _)) (ρ t) (M t)
    (hμ t) hM0 (Nat.le_ceil _) hρ N hN (f t) (hf t) (e t) (hrt ht htstar)).2

end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceRieszTransportExtendedFreeEnergy_cap_independent
#check @DGRHS.Dynamics.SourceRieszScalarControlBound
#check @DGRHS.Dynamics.exists_sourceRiesz_scalar_control_coefficients
#check @DGRHS.Dynamics.exists_sourceRiesz_measurable_diffusive_bound
#print axioms DGRHS.Dynamics.sourceRieszTransportExtendedFreeEnergy_cap_independent
#print axioms DGRHS.Dynamics.SourceRieszScalarControlBound
#print axioms DGRHS.Dynamics.exists_sourceRiesz_scalar_control_coefficients
#print axioms DGRHS.Dynamics.exists_sourceRiesz_measurable_diffusive_bound
