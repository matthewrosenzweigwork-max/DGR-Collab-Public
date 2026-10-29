/- Theorem 2.9 (LOG), measurable time coefficients.

The coefficients of the source Gronwall factors are produced from the
family-uniform logarithmic entropic commutator, which depends only on the
scalar controls (Lipschitz bound of the velocity, density cap, lower bound of
the logarithmic interaction energy).  Constants are chosen once for each
integer triple of scalar-control ceilings, and then composed with
`Nat.ceil` of the measurable controls; measurability in time is therefore
proved, not assumed. -/
import DGRHS.Dynamics.SourceLogPhysicalTime
import DGRHS.Commutator.SourceLogFamilyEntropicCommutator
import Mathlib.MeasureTheory.Function.Floor
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Interval
namespace DGRHS.Dynamics
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy DGRHS.Commutator
variable {ι : Type*} [Fintype ι]

/-- The physical free energy of the collision-free logarithmic gas does not
depend on the auxiliary density cap used to define its energy floor. -/
theorem sourceLogCollisionFreeEnergy_cap_independent (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (M₁ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hρ₁ : ∀ᵐ x ∂volume, ρ x ≤ M₁) (hρ₂ : ∀ᵐ x ∂volume, ρ x ≤ M₂)
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (N : ℕ) (hN : 1 ≤ N) (ν : Measure (Fin N → EuclideanSpace ℝ ι))
    [IsProbabilityMeasure ν] :
    sourceLogCollisionFreeEnergy β ρ M₁ N ν = sourceLogCollisionFreeEnergy β ρ M₂ N ν := by
  have h1 := sourceLogCollisionFreeEnergy_eq β hβ hd ρ M₁ N hN ν
  have h2 := sourceLogCollisionFreeEnergy_eq β hβ hd ρ M₂ N hN ν
  have r1 := sourceLogExtendedFreeEnergy_rewrite β hβ hd ρ M₁ hM₁ hρ₁ hpair N hN ν
  have r2 := sourceLogExtendedFreeEnergy_rewrite β hβ hd ρ M₂ hM₂ hρ₂ hpair N hN ν
  rw [h1, h2, r1, r2]

/-- The commutator bound with constants `a b`, valid for every velocity with
Lipschitz constant at most `p`, every background with density cap at most `q`
and logarithmic energy at least `-r`, and every particle number and law. -/
def SourceLogScalarControlBound (β : ℝ≥0) (p q r : ℕ) (a b : ℝ) : Prop :=
  ∀ (v : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (K : ℝ≥0),
  LipschitzWith K v → (K : ℝ) ≤ (p : ℝ) →
  ∀ (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ),
  IsProbabilityMeasure (gaussianRieszDensityMeasure ρ) → 0 ≤ M → M ≤ (q : ℝ) →
  (∀ᵐ x ∂volume, ρ x ≤ M) →
  Integrable logPhysicalPair
    ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) →
  -(r : ℝ) ≤ DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
    (fun x y => logPhysicalPair (x, y)) →
  ∀ N : ℕ, 1 ≤ N → ∀ ν : Measure (Fin N → EuclideanSpace ℝ ι),
  IsProbabilityMeasure ν →
  Integrable (fun x => (N : ℝ) * sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
    (sourceLogTransportKernel 1 v) N x) ν ∧
  ((|∫ x, (N : ℝ) * sourceTransportEnergy (gaussianRieszDensityMeasure ρ)
    (sourceLogTransportKernel 1 v) N x ∂ν| : ℝ) : EReal) ≤
    ((a * (N : ℝ) : ℝ) : EReal) * sourceLogCollisionFreeEnergy β ρ M N ν +
      ((b : ℝ) : EReal)

/-- Constants indexed by the integer ceilings of the scalar controls. -/
theorem exists_sourceLog_scalar_control_coefficients (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) :
    ∃ A B : ℕ → ℕ → ℕ → ℝ, (∀ p q r, 0 ≤ A p q r ∧ 0 ≤ B p q r) ∧
      ∀ p q r, SourceLogScalarControlBound (ι := ι) β p q r (A p q r) (B p q r) := by
  classical
  obtain ⟨Csr, hC, hfactory⟩ :=
    exists_log_transport_family_entropic_commutator (ι := ι) 1 (by omega)
  have hp : ∀ p q r : ℕ, ∃ a b : ℝ, (0 ≤ a ∧ 0 ≤ b) ∧
      SourceLogScalarControlBound (ι := ι) β p q r a b := by
    intro p q r
    have hK : (0 : ℝ) < ((((p : ℝ≥0) + 1 : ℝ≥0)) : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) p
      push_cast
      linarith
    obtain ⟨βloc, hloc, hβfactory⟩ :=
      hfactory ((p : ℝ≥0) + 1) hK (q : ℝ) (Nat.cast_nonneg q) hd
    obtain ⟨Cub, Cpf, hCub, hCpf, hε, hCem, hforcing, hfamily⟩ :=
      hβfactory β hβ (r : ℝ)
    let ε := sourceLogTransportEpsilon (β : ℝ) βloc Csr
      ((((p : ℝ≥0) + 1 : ℝ≥0) : ℝ) ^ 1)
    let Cem := sourceLogTransportCem (β : ℝ) βloc (-(r : ℝ))
      DGRHS.Concentration.glzUniversalTailConstant Cub
    refine ⟨(β : ℝ) / ε, ε⁻¹ * (Real.log Cpf + Real.log Cem),
      ⟨(div_pos hβ hε).le, mul_nonneg (inv_pos.mpr hε).le hforcing⟩, ?_⟩
    intro v K hv hKp ρ M hμ hM0 hMq hρ hpair hI N hN ν hν
    haveI := hμ
    haveI := hν
    have hKle : K ≤ (p : ℝ≥0) + 1 := by
      have h1 : K ≤ (p : ℝ≥0) := by exact_mod_cast hKp
      exact h1.trans le_self_add
    have hv' : LipschitzWith ((p : ℝ≥0) + 1) v := hv.weaken hKle
    have hρ' : ∀ᵐ x ∂volume, ρ x ≤ (q : ℝ) := hρ.mono fun x hx => hx.trans hMq
    obtain ⟨hint, hbd⟩ := hfamily v hv' ρ hρ' hpair hI N hN ν
    refine ⟨hint, ?_⟩
    rw [sourceLogCollisionFreeEnergy_cap_independent β hβ hd ρ M (q : ℝ) hM0
      (Nat.cast_nonneg q) hρ hρ' hpair N hN ν]
    exact hbd
  choose A B hAB using hp
  exact ⟨A, B, fun p q r => (hAB p q r).1, fun p q r => (hAB p q r).2⟩

/-- Theorem 2.9, LOG, with coefficient functions that are measurable in time.
The coefficients depend only on `β`, the dimension and the measurable scalar
controls `Λ` (Lipschitz bound of `v t`), `M` (density cap) and `J` (lower
bound `-J t` of the logarithmic interaction energy); they are fixed before the
backgrounds, velocities, particle number, laws, energy curve and lifespan. The
finiteness of the source factors `𝒜^t`, `ℬ^t` remains the source hypothesis. -/
theorem exists_sourceLog_measurable_diffusive_bound (β : ℝ≥0) (hβ : 0 < (β : ℝ))
    (hd : 0 < (Fintype.card ι : ℝ)) (Λ M J : ℝ → ℝ)
    (hΛ : Measurable Λ) (hM : Measurable M) (hJ : Measurable J) :
    ∃ a b : ℝ → ℝ, Measurable a ∧ Measurable b ∧ (∀ t, 0 ≤ a t ∧ 0 ≤ b t) ∧
      ∀ (ρ : ℝ → EuclideanSpace ℝ ι → ℝ)
        (v : ℝ → EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) (K : ℝ → ℝ≥0),
      (∀ t, IsProbabilityMeasure (gaussianRieszDensityMeasure (ρ t))) →
      ∀ (N : ℕ), 1 ≤ N →
      ∀ (f : ℝ → Measure (Fin N → EuclideanSpace ℝ ι)),
      (∀ t, IsProbabilityMeasure (f t)) → ∀ (E : ℝ → ℝ) (Tstar : ℝ≥0∞),
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        sourceLogTimeAdmissible (ρ t) (v t) (K t) (M t) ∧ (K t : ℝ) ≤ Λ t ∧
        -J t ≤ DGRHS.interactionEnergy (gaussianRieszDensityMeasure (ρ t))
          (fun x y => logPhysicalPair (x, y))) →
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        sourceLogCollisionFreeEnergy β (ρ t) (M t) N (f t) = (E t : EReal)) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → AbsolutelyContinuousOnInterval E 0 T) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceA a T ≠ ∞) →
      (∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar → extendedSourceB a b T ≠ ∞) →
      (∀ᵐ t ∂volume, 0 < t → ENNReal.ofReal t < Tstar →
        deriv E t ≤ |∫ x, (N : ℝ) * sourceTransportEnergy (gaussianRieszDensityMeasure (ρ t))
          (sourceLogTransportKernel 1 (v t)) N x ∂f t| / N) →
      ∀ T, 0 ≤ T → ENNReal.ofReal T < Tstar →
        E T ≤ sourceA a T * E 0 + sourceB a b T / N := by
  classical
  obtain ⟨A, B, hAB0, hABb⟩ :=
    exists_sourceLog_scalar_control_coefficients (ι := ι) β hβ hd
  have hmeas : ∀ F : ℕ → ℕ → ℕ → ℝ, Measurable (fun t => F ⌈Λ t⌉₊ ⌈M t⌉₊ ⌈J t⌉₊) := by
    intro F
    have h3 : Measurable (fun t => (⌈Λ t⌉₊, ⌈M t⌉₊, ⌈J t⌉₊)) :=
      hΛ.nat_ceil.prodMk (hM.nat_ceil.prodMk hJ.nat_ceil)
    exact (measurable_of_countable (fun x : ℕ × ℕ × ℕ => F x.1 x.2.1 x.2.2)).comp h3
  refine ⟨fun t => A ⌈Λ t⌉₊ ⌈M t⌉₊ ⌈J t⌉₊, fun t => B ⌈Λ t⌉₊ ⌈M t⌉₊ ⌈J t⌉₊,
    hmeas A, hmeas B, fun t => hAB0 _ _ _, ?_⟩
  intro ρ v K hμ N hN f hf E Tstar hphys hrepr hE hA hB hdiss
  apply source_diffusive_gronwall_local (by omega : 0 < N) hE
    (hmeas A).aestronglyMeasurable (hmeas B).aestronglyMeasurable
    (Eventually.of_forall fun t => (hAB0 _ _ _).1)
    (Eventually.of_forall fun t => (hAB0 _ _ _).2) hA hB hdiss
  filter_upwards [hphys, hrepr] with t hpt hrt ht htstar
  obtain ⟨hadm, hKΛ, hI⟩ := hpt ht htstar
  obtain ⟨hv', _, hM0, hρ, hpair⟩ := hadm
  letI := hμ t
  letI := hf t
  have hbound := (hABb ⌈Λ t⌉₊ ⌈M t⌉₊ ⌈J t⌉₊ (v t) (K t) hv'
    (hKΛ.trans (Nat.le_ceil _)) (ρ t) (M t) (hμ t) hM0 (Nat.le_ceil _) hρ hpair
    ((neg_le_neg (Nat.le_ceil (J t))).trans hI) N hN (f t) (hf t)).2
  rw [hrt ht htstar, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at hbound
  exact hbound

end DGRHS.Dynamics
#check @DGRHS.Dynamics.sourceLogCollisionFreeEnergy_cap_independent
#check @DGRHS.Dynamics.SourceLogScalarControlBound
#check @DGRHS.Dynamics.exists_sourceLog_scalar_control_coefficients
#check @DGRHS.Dynamics.exists_sourceLog_measurable_diffusive_bound
#print axioms DGRHS.Dynamics.sourceLogCollisionFreeEnergy_cap_independent
#print axioms DGRHS.Dynamics.SourceLogScalarControlBound
#print axioms DGRHS.Dynamics.exists_sourceLog_scalar_control_coefficients
#print axioms DGRHS.Dynamics.exists_sourceLog_measurable_diffusive_bound
