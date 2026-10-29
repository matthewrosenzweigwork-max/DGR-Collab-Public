/- Theorem 2.9 (positive Riesz) on the flat torus (Remark 2.1), measurable time coefficients.

Torus analogue of `SourceRieszMeasurableTimeCoefficients`.  The `n = 1` finite-relative-entropy
entropic commutator estimate of the torus (`periodicRieszCommon_finiteObjective_transport`, constants
chosen before the density) provides constants that depend only on the scalar controls (Lipschitz
bound for the sup torus metric, density cap).  Constants are chosen once for each pair of integer
ceilings and composed with `Nat.ceil` of the measurable controls, so measurability in time is proved.
The Gronwall step is the kernel-generic `source_diffusive_gronwall_local`.  The uniform-in-time
physical form (Remark 2.10, constant coefficients) is also proved. -/
import DGRHS.Gaussian.PeriodicRieszCommon
import DGRHS.Dynamics.SourceDiffusiveLocal
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
open MeasureTheory InformationTheory Set Filter
open scoped NNReal ENNReal Interval
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.Commutator DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The extended torus Riesz free energy does not depend on the auxiliary density cap used for its
normalization constant. -/
theorem periodicRieszTransportExtendedFreeEnergy_cap_independent (s : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hρ₁ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M₁) (hρ₂ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M₂)
    (N : ℕ) (hN : 1 ≤ N) (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν] :
    periodicRieszTransportExtendedFreeEnergy s hs2 ρ M₁ β N ν =
      periodicRieszTransportExtendedFreeEnergy s hs2 ρ M₂ β N ν := by
  rw [periodicRieszTransportExtendedFreeEnergy_rewrite s hs hs2 M₁ hM₁ β hβ ρ hρ₁ N hN ν,
    periodicRieszTransportExtendedFreeEnergy_rewrite s hs hs2 M₂ hM₂ β hβ ρ hρ₂ N hN ν]

/-- The torus Riesz `n = 1` commutator bound with constants `a b`, valid for every velocity with
(sup-metric) Lipschitz constant at most `p`, every background with density cap at most `q`, and
every particle number and law with finite physical free energy `e`. -/
def PeriodicRieszScalarControlBound (s : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ)) (β : ℝ)
    (p q : ℕ) (a b : ℝ) : Prop :=
  ∀ (v : PeriodicTorus ι → E) (K : ℝ≥0),
  LipschitzWith K v → (K : ℝ) ≤ (p : ℝ) →
  ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
  0 ≤ M → M ≤ (q : ℝ) →
  (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
  ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Fin N → PeriodicTorus ι),
  IsProbabilityMeasure ν → ∀ e : ℝ,
  periodicRieszTransportExtendedFreeEnergy s hs2 ρ M β N ν = (e : EReal) →
  Integrable (fun ω => (N : ℝ) * periodicRieszTransportEnergy s 1 v ρ N ω) ν ∧
  |∫ ω, (N : ℝ) * periodicRieszTransportEnergy s 1 v ρ N ω ∂ν| ≤ a * (N : ℝ) * e + b

/-- Constants indexed by the integer ceilings of the scalar controls. -/
theorem exists_periodicRiesz_scalar_control_coefficients (s β : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hβ : 0 < β) :
    ∃ A B : ℕ → ℕ → ℝ, (∀ p q, 0 ≤ A p q ∧ 0 ≤ B p q) ∧
      ∀ p q, PeriodicRieszScalarControlBound (ι := ι) s hs2 β p q (A p q) (B p q) := by
  classical
  have hp : ∀ p q : ℕ, ∃ a b : ℝ, (0 ≤ a ∧ 0 ≤ b) ∧
      PeriodicRieszScalarControlBound (ι := ι) s hs2 β p q a b := by
    intro p q
    obtain ⟨Cpf, Cem, hCpf, hCem, hFamily⟩ :=
      periodicRieszCommon_finiteObjective_transport (ι := ι) s (q : ℝ) 1 le_rfl hs hs2
        (Nat.cast_nonneg q) β hβ
    have hε : 0 < periodicRieszPositiveTransportParameter s hs2 (q : ℝ) 1 (p : ℝ≥0) β :=
      periodicRieszPositiveTransportParameter_pos s hs hs2 (q : ℝ) (Nat.cast_nonneg q) 1
        (p : ℝ≥0) β hβ
    refine ⟨β / periodicRieszPositiveTransportParameter s hs2 (q : ℝ) 1 (p : ℝ≥0) β,
      (periodicRieszPositiveTransportParameter s hs2 (q : ℝ) 1 (p : ℝ≥0) β)⁻¹ *
        (Real.log Cpf + Real.log Cem),
      ⟨(div_pos hβ hε).le, mul_nonneg (inv_nonneg.mpr hε.le)
        (add_nonneg (Real.log_nonneg hCpf) (Real.log_nonneg hCem))⟩, ?_⟩
    intro v K hv hKp ρ M hμ hM0 hMq hρ N hN ν hν e he
    haveI := hν
    have hKle : K ≤ (p : ℝ≥0) := by exact_mod_cast hKp
    have hv' : LipschitzWith (p : ℝ≥0) v := hv.weaken hKle
    have hρ' : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ (q : ℝ) := hρ.mono fun x hx => hx.trans hMq
    have he' : periodicRieszTransportExtendedFreeEnergy s hs2 ρ (q : ℝ) β N ν = (e : EReal) := by
      rw [← he]
      exact (periodicRieszTransportExtendedFreeEnergy_cap_independent s hs hs2 β hβ ρ M (q : ℝ)
        hM0 (Nat.cast_nonneg q) hρ hρ' N hN ν).symm
    obtain ⟨hint, -, hbd⟩ := ((hFamily (p : ℝ≥0) v hv').2 ρ hρ' N hN ν e he')
    exact ⟨hint, hbd⟩
  choose A B hAB using hp
  exact ⟨A, B, fun p q => (hAB p q).1, fun p q => (hAB p q).2⟩

/-- Theorem 2.9 on the torus, positive Riesz kernel `0 < s < d/2`, with coefficient functions that
are measurable in time.  The coefficients depend only on `s`, `β`, the dimension and the measurable
scalar controls `Λ` (Lipschitz bound of `v t` for the sup torus metric) and `M` (density cap of
`ρ t`).  The finiteness of the source factors `𝒜^t`, `ℬ^t` remains the source hypothesis. -/
theorem exists_periodicRiesz_measurable_diffusive_bound (s β : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hβ : 0 < β) (Λ M : ℝ → ℝ)
    (hΛ : Measurable Λ) (hM : Measurable M) :
    ∃ a b : ℝ → ℝ, Measurable a ∧ Measurable b ∧ (∀ t, 0 ≤ a t ∧ 0 ≤ b t) ∧
      ∀ (ρ : ℝ → PeriodicTorus ι → ℝ) (v : ℝ → PeriodicTorus ι → E) (K : ℝ → ℝ≥0)
        [∀ t, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ t))],
      ∀ (N : ℕ), 1 ≤ N →
      ∀ (f : ℝ → Measure (Fin N → PeriodicTorus ι)),
      (∀ t, IsProbabilityMeasure (f t)) → ∀ (e : ℝ → ℝ) (Tstar : ℝ≥0∞),
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        0 ≤ M t ∧ (∀ᵐ x ∂periodicHaar ι, ρ t x ≤ M t) ∧ LipschitzWith (K t) (v t) ∧
        (K t : ℝ) ≤ Λ t) →
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        periodicRieszTransportExtendedFreeEnergy s hs2 (ρ t) (M t) β N (f t) = (e t : EReal)) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → AbsolutelyContinuousOnInterval e 0 T) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceA a T ≠ ∞) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceB a b T ≠ ∞) →
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        deriv e t ≤ |∫ ω, (N : ℝ) * periodicRieszTransportEnergy s 1 (v t) (ρ t) N ω
          ∂f t| / N) →
      ∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar →
        e T ≤ sourceA a T * e 0 + sourceB a b T / N := by
  classical
  obtain ⟨A, B, hAB0, hABb⟩ :=
    exists_periodicRiesz_scalar_control_coefficients (ι := ι) s β hs hs2 hβ
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
  letI := hf t
  exact (hABb ⌈Λ t⌉₊ ⌈M t⌉₊ (v t) (K t) hv' (hKΛ.trans (Nat.le_ceil _)) (ρ t) (M t)
    hM0 (Nat.le_ceil _) hρ N hN (f t) (hf t) (e t) (hrt ht htstar)).2

/-- Uniform-in-time propagation (Remark 2.10, `rem:uniform-generation-chaos`) on the torus, positive
Riesz kernel: under uniform scalar controls `K`, `M` the Gronwall coefficients are constants. -/
theorem exists_periodicRiesz_uniform_physical_diffusive_bound (s β : ℝ) (hs : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hβ : 0 < β) (K : ℝ≥0) (M : ℝ) (hM : 0 ≤ M) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ρ : ℝ → PeriodicTorus ι → ℝ) (v : ℝ → PeriodicTorus ι → E)
        (f : ℝ → Measure (Fin N → PeriodicTorus ι)) (e : ℝ → ℝ)
        [∀ t, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ t))],
      (∀ t, IsProbabilityMeasure (f t)) →
      (∀ᵐ t ∂volume, t ∈ Ioo 0 T →
        (∀ᵐ x ∂periodicHaar ι, ρ t x ≤ M) ∧ LipschitzWith K (v t)) →
      (∀ᵐ t ∂volume, t ∈ Ioo 0 T →
        periodicRieszTransportExtendedFreeEnergy s hs2 (ρ t) M β N (f t) = (e t : EReal)) →
      AbsolutelyContinuousOnInterval e 0 T →
      (∀ᵐ t ∂volume, t ∈ Ioo 0 T → deriv e t ≤
        |∫ ω, (N : ℝ) * periodicRieszTransportEnergy s 1 (v t) (ρ t) N ω ∂f t| / N) →
      e T ≤ sourceA (fun _ => a) T * e 0 + sourceB (fun _ => a) (fun _ => b) T / N := by
  obtain ⟨Cpf, Cem, hCpf, hCem, hFamily⟩ :=
    periodicRieszCommon_finiteObjective_transport (ι := ι) s M 1 le_rfl hs hs2 hM β hβ
  have hε : 0 < periodicRieszPositiveTransportParameter s hs2 M 1 K β :=
    periodicRieszPositiveTransportParameter_pos s hs hs2 M hM 1 K β hβ
  refine ⟨β / periodicRieszPositiveTransportParameter s hs2 M 1 K β,
    (periodicRieszPositiveTransportParameter s hs2 M 1 K β)⁻¹ * (Real.log Cpf + Real.log Cem),
    (div_pos hβ hε).le, mul_nonneg (inv_nonneg.mpr hε.le)
      (add_nonneg (Real.log_nonneg hCpf) (Real.log_nonneg hCem)), ?_⟩
  intro N hN T hT ρ v f e hμ hf hphys hrepr he hdiss
  apply source_diffusive_gronwall (by omega : 0 < N) hT he
    intervalIntegrable_const intervalIntegrable_const hdiss
  filter_upwards [hphys, hrepr] with t hpt hrt ht
  obtain ⟨hρ, hv⟩ := hpt ht
  letI := hf t
  obtain ⟨hint, -, hbd⟩ := (hFamily K (v t) hv).2 (ρ t) hρ N hN (f t) (e t) (hrt ht)
  exact hbd

end DGRHS.Dynamics
#print axioms DGRHS.Dynamics.periodicRieszTransportExtendedFreeEnergy_cap_independent
#print axioms DGRHS.Dynamics.PeriodicRieszScalarControlBound
#print axioms DGRHS.Dynamics.exists_periodicRiesz_scalar_control_coefficients
#print axioms DGRHS.Dynamics.exists_periodicRiesz_measurable_diffusive_bound
#print axioms DGRHS.Dynamics.exists_periodicRiesz_uniform_physical_diffusive_bound
