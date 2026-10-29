/- Theorem 2.9 (LOG) on the flat torus (Remark 2.1), measurable time coefficients.

Torus analogue of `SourceLogMeasurableTimeCoefficients`.  The coefficients of the source Gronwall
factors are produced from the family-uniform torus LOG entropic commutator
(`exists_periodicLog_family_entropic_commutator`), which depends only on the scalar controls
(Lipschitz bound of the velocity for the sup torus metric, density cap); the lower bound of the
logarithmic interaction energy is the universal torus constant, so no third control `J` is needed.
Constants are chosen once for each pair of integer ceilings and composed with `Nat.ceil` of the
measurable controls; measurability in time is therefore proved, not assumed.  The Gronwall step is
the kernel-generic `source_diffusive_gronwall_local`.  The uniform-in-time physical form
(Remark 2.10, constant coefficients) is also proved. -/
import DGRHS.Gaussian.PeriodicLogFamily
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

/-- The extended torus LOG free energy does not depend on the auxiliary density cap used for its
normalization constant. -/
theorem periodicLogTransportExtendedFreeEnergy_cap_independent (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hρ₁ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M₁) (hρ₂ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M₂)
    (N : ℕ) (hN : 1 ≤ N) (ν : Measure (Fin N → PeriodicTorus ι)) [IsProbabilityMeasure ν] :
    periodicLogTransportExtendedFreeEnergy ρ M₁ β N ν =
      periodicLogTransportExtendedFreeEnergy ρ M₂ β N ν := by
  rw [periodicLogTransportExtendedFreeEnergy_rewrite M₁ hM₁ β hβ ρ hρ₁ N hN ν,
    periodicLogTransportExtendedFreeEnergy_rewrite M₂ hM₂ β hβ ρ hρ₂ N hN ν]

/-- The torus LOG commutator bound with constants `a b`, valid for every velocity with (sup-metric)
Lipschitz constant at most `p`, every background with density cap at most `q`, and every particle
number and law. -/
def PeriodicLogScalarControlBound (β : ℝ≥0) (p q : ℕ) (a b : ℝ) : Prop :=
  ∀ (v : PeriodicTorus ι → E) (K : ℝ≥0),
  LipschitzWith K v → (K : ℝ) ≤ (p : ℝ) →
  ∀ (ρ : PeriodicTorus ι → ℝ) (M : ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)],
  0 ≤ M → M ≤ (q : ℝ) → (∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) →
  ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Fin N → PeriodicTorus ι),
  IsProbabilityMeasure ν →
  Integrable (fun x => (N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
    (periodicLogTransportKernel 1 v) N x) ν ∧
  ((|∫ x, (N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure ρ)
    (periodicLogTransportKernel 1 v) N x ∂ν| : ℝ) : EReal) ≤
    ((a * (N : ℝ) : ℝ) : EReal) * periodicLogTransportExtendedFreeEnergy ρ M (β : ℝ) N ν +
      ((b : ℝ) : EReal)

/-- Constants indexed by the integer ceilings of the scalar controls. -/
theorem exists_periodicLog_scalar_control_coefficients (β : ℝ≥0) (hβ : 0 < (β : ℝ)) :
    ∃ A B : ℕ → ℕ → ℝ, (∀ p q, 0 ≤ A p q ∧ 0 ≤ B p q) ∧
      ∀ p q, PeriodicLogScalarControlBound (ι := ι) β p q (A p q) (B p q) := by
  classical
  obtain ⟨Csr, hC, hfactory⟩ :=
    exists_periodicLog_family_entropic_commutator (ι := ι) 1 (by omega)
  have hp : ∀ p q : ℕ, ∃ a b : ℝ, (0 ≤ a ∧ 0 ≤ b) ∧
      PeriodicLogScalarControlBound (ι := ι) β p q a b := by
    intro p q
    have hK : (0 : ℝ) < ((((p : ℝ≥0) + 1 : ℝ≥0)) : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) p
      push_cast
      linarith
    obtain ⟨βloc, hloc, hβfactory⟩ :=
      hfactory ((p : ℝ≥0) + 1) hK (q : ℝ) (Nat.cast_nonneg q)
    obtain ⟨Cub, Cpf, hCub, hCpf, hε, hCem, hforcing, hfamily⟩ := hβfactory β hβ
    refine ⟨(β : ℝ) / sourceLogTransportEpsilon (β : ℝ) βloc Csr
        ((((p : ℝ≥0) + 1 : ℝ≥0) : ℝ) ^ 1),
      (sourceLogTransportEpsilon (β : ℝ) βloc Csr ((((p : ℝ≥0) + 1 : ℝ≥0) : ℝ) ^ 1))⁻¹ *
        (Real.log Cpf + Real.log (sourceLogTransportCem (β : ℝ) βloc
          (-(periodicLogPairLower ι / 2)) DGRHS.Concentration.glzUniversalTailConstant Cub)),
      ⟨(div_pos hβ hε).le, mul_nonneg (inv_pos.mpr hε).le hforcing⟩, ?_⟩
    intro v K hv hKp ρ M hμ hM0 hMq hρ N hN ν hν
    haveI := hν
    have hKle : K ≤ (p : ℝ≥0) + 1 := by
      have h1 : K ≤ (p : ℝ≥0) := by exact_mod_cast hKp
      exact h1.trans le_self_add
    have hv' : LipschitzWith ((p : ℝ≥0) + 1) v := hv.weaken hKle
    have hρ' : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ (q : ℝ) := hρ.mono fun x hx => hx.trans hMq
    obtain ⟨hint, hbd⟩ := hfamily hv' ρ hρ' N hN ν
    refine ⟨hint, ?_⟩
    rw [periodicLogTransportExtendedFreeEnergy_cap_independent (β : ℝ) hβ ρ M (q : ℝ) hM0
      (Nat.cast_nonneg q) hρ hρ' N hN ν]
    exact hbd
  choose A B hAB using hp
  exact ⟨A, B, fun p q => (hAB p q).1, fun p q => (hAB p q).2⟩

/-- Theorem 2.9 on the torus, LOG kernel, with coefficient functions that are measurable in time.
The coefficients depend only on `β`, the dimension and the measurable scalar controls `Λ` (Lipschitz
bound of `v t` for the sup torus metric) and `M` (density cap of `ρ t`); they are fixed before the
backgrounds, velocities, particle number, laws, energy curve and lifespan.  The finiteness of the
source factors `𝒜^t`, `ℬ^t` remains the source hypothesis. -/
theorem exists_periodicLog_measurable_diffusive_bound (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (Λ M : ℝ → ℝ) (hΛ : Measurable Λ) (hM : Measurable M) :
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
        periodicLogTransportExtendedFreeEnergy (ρ t) (M t) (β : ℝ) N (f t) = (e t : EReal)) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → AbsolutelyContinuousOnInterval e 0 T) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceA a T ≠ ∞) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceB a b T ≠ ∞) →
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        deriv e t ≤ |∫ x, (N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure (ρ t))
          (periodicLogTransportKernel 1 (v t)) N x ∂f t| / N) →
      ∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar →
        e T ≤ sourceA a T * e 0 + sourceB a b T / N := by
  classical
  obtain ⟨A, B, hAB0, hABb⟩ :=
    exists_periodicLog_scalar_control_coefficients (ι := ι) β hβ
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
  have hbound := (hABb ⌈Λ t⌉₊ ⌈M t⌉₊ (v t) (K t) hv'
    (hKΛ.trans (Nat.le_ceil _)) (ρ t) (M t) hM0 (Nat.le_ceil _) hρ N hN (f t) (hf t)).2
  rw [hrt ht htstar, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hbound
  exact hbound

/-- Uniform-in-time propagation (Remark 2.10, `rem:uniform-generation-chaos`) on the torus, LOG
kernel: under uniform scalar controls `K > 0`, `M` the Gronwall coefficients are constants. -/
theorem exists_periodicLog_uniform_physical_diffusive_bound (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (K : ℝ≥0) (hK : 0 < (K : ℝ)) (M : ℝ) (hM : 0 ≤ M) :
    ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ρ : ℝ → PeriodicTorus ι → ℝ) (v : ℝ → PeriodicTorus ι → E)
        (f : ℝ → Measure (Fin N → PeriodicTorus ι)) (e : ℝ → ℝ)
        [∀ t, IsProbabilityMeasure (periodicCappedDensityMeasure (ρ t))],
      (∀ t, IsProbabilityMeasure (f t)) →
      (∀ᵐ t ∂volume, t ∈ Ioo 0 T →
        (∀ᵐ x ∂periodicHaar ι, ρ t x ≤ M) ∧ LipschitzWith K (v t)) →
      (∀ᵐ t ∂volume, t ∈ Ioo 0 T →
        periodicLogTransportExtendedFreeEnergy (ρ t) M (β : ℝ) N (f t) = (e t : EReal)) →
      AbsolutelyContinuousOnInterval e 0 T →
      (∀ᵐ t ∂volume, t ∈ Ioo 0 T → deriv e t ≤
        |∫ x, (N : ℝ) * sourceTransportEnergy (periodicCappedDensityMeasure (ρ t))
          (periodicLogTransportKernel 1 (v t)) N x ∂f t| / N) →
      e T ≤ sourceA (fun _ => a) T * e 0 + sourceB (fun _ => a) (fun _ => b) T / N := by
  obtain ⟨Csr, hC, hfactory⟩ :=
    exists_periodicLog_family_entropic_commutator (ι := ι) 1 (by omega)
  obtain ⟨βloc, hloc, hβfactory⟩ := hfactory K hK M hM
  obtain ⟨Cub, Cpf, hCub, hCpf, hε, hCem, hforcing, hfamily⟩ := hβfactory β hβ
  refine ⟨(β : ℝ) / sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ 1),
    (sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ 1))⁻¹ *
      (Real.log Cpf + Real.log (sourceLogTransportCem (β : ℝ) βloc
        (-(periodicLogPairLower ι / 2)) DGRHS.Concentration.glzUniversalTailConstant Cub)),
    div_pos hβ hε, mul_nonneg (inv_pos.mpr hε).le hforcing, ?_⟩
  intro N hN T hT ρ v f e hμ hf hphys hrepr he hdiss
  apply source_diffusive_gronwall (by omega : 0 < N) hT he
    intervalIntegrable_const intervalIntegrable_const hdiss
  filter_upwards [hphys, hrepr] with t hpt hrt ht
  obtain ⟨hρ, hv⟩ := hpt ht
  letI := hf t
  have hbound := (hfamily hv (ρ t) hρ N hN (f t)).2
  rw [hrt ht, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hbound
  exact hbound

end DGRHS.Dynamics
#print axioms DGRHS.Dynamics.periodicLogTransportExtendedFreeEnergy_cap_independent
#print axioms DGRHS.Dynamics.PeriodicLogScalarControlBound
#print axioms DGRHS.Dynamics.exists_periodicLog_scalar_control_coefficients
#print axioms DGRHS.Dynamics.exists_periodicLog_measurable_diffusive_bound
#print axioms DGRHS.Dynamics.exists_periodicLog_uniform_physical_diffusive_bound
