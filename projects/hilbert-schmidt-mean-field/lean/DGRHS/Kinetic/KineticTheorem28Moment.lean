import DGRHS.Kinetic.KineticModulatedPartition
import DGRHS.Commutator.SourceT28FullRangePrinted

/-! Packet P14b, kinetic half of Remark 2.1 (`rem:torus-kinetic-variants`, TeX 495), second part:
the exponential-moment bound (2.21) of Theorem 2.8 (`thm:entropicCommutator`, TeX 691-707)
for the kinetic modulated Gibbs measure `Q_{N,β}(μ) ⊗ η` (velocity reference `η`; the
`N`-particle Maxwellian is an instance) and the spatial observable `N A_n(v, ·, μ)`, with
the printed constants of Remark A.1.  Derived from the spatial export
`exists_sourceT28_full_range_printed` and the tensorization `integral_fun_fst`. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
universe w
namespace DGRHS.Kinetic
open DGRHS.Gaussian DGRHS.CLT DGRHS.Entropy DGRHS.Concentration DGRHS.Commutator
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem sFinite_sourceT28Gibbs (s : ℝ) (β : ℝ≥0) (ρ : E → ℝ)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (N : ℕ) :
    SFinite (sourceT28Gibbs s β ρ N) := by
  unfold sourceT28Gibbs
  split_ifs
  · unfold sourceLogSingularGibbs; infer_instance
  · unfold sourceRieszSingularGibbs; infer_instance

/-- Kinetic form of the exponential moment (2.21) of Theorem 2.8, `0 ≤ s < d/2`, for a spatial
observable: for every velocity reference `η` and every `N`, `σ = ±1`,
`E_{Q_{N,β}(μ) ⊗ η}[exp(σ ε N A_n(v, x, μ))] ≤ C_em`, with the same `ε`, `C_em` (printed
constants of Remark A.1) as the spatial theorem. -/
theorem kinetic_sourceT28_exponential_moment (n : ℕ) (hn : 0 < n) (s : ℝ)
    (hs : 0 ≤ s) (hd : 2 * s < (Fintype.card ι : ℝ))
    {K : ℝ≥0} {v : E → E} (hv : LipschitzWith K v)
    (ρ : E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hlog : s = 0 → Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    ∃ βloc : ℝ, 0 < βloc ∧ ∀ β : ℝ≥0, 0 < (β : ℝ) →
      ∃ ε Cpf Cem : ℝ, 0 < ε ∧ 1 ≤ Cpf ∧ 0 < Cem ∧ 0 ≤ Real.log Cpf + Real.log Cem ∧
      (s = 0 →
        (K = 0 → ε = 1 ∧ Cem = 1) ∧
        (0 < (K : ℝ) → ∃ Csr Cub : ℝ, 0 < Csr ∧ 1 ≤ Cub ∧
          (∀ N : ℕ, 1 ≤ N → ∀ hlarge : βloc < (β : ℝ),
            (sourceLogSingularPartition
              (⟨2 * (β : ℝ) - βloc, by linarith [hlarge, β.coe_nonneg]⟩ : ℝ≥0) ρ N).toReal ≤
              Cub) ∧
          ε = sourceLogTransportEpsilon (β : ℝ) βloc Csr ((K : ℝ) ^ n) ∧
          Cem = sourceLogTransportCem (β : ℝ) βloc
            (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
              (fun a b => logPhysicalPair (a, b)))
            glzUniversalTailConstant Cub)) ∧
      (0 < s → ∃ Cub : ℝ, 1 ≤ Cub ∧
        (∀ N : ℕ, 1 ≤ N → βloc < (β : ℝ) →
          (sourceRieszSingularPartition s (2 * (β : ℝ) - βloc) ρ N).toReal ≤ Cub) ∧
        ε = sourceRieszPositiveTransportParameter (ι := ι) s M n K (β : ℝ) ∧
        Cem = sourceRieszPrintedCem (β : ℝ) βloc glzUniversalTailConstant Cub
          (DGRHS.interactionEnergy (gaussianRieszDensityMeasure ρ)
            (fun a b : E => gaussianRieszPhysicalPair s (a, b)))) ∧
      (∀ σ : ℝ, |σ| = 1 → ∀ N : ℕ, 1 ≤ N →
        ∀ (V : Type w) [MeasurableSpace V] (η : Measure V) [IsProbabilityMeasure η],
        Integrable (fun z : (Fin N → E) × V =>
          Real.exp (σ * ε * ((N : ℝ) * sourceT28Observable s n v ρ N z.1)))
          ((sourceT28Gibbs s β ρ N).prod η) ∧
        (∫ z : (Fin N → E) × V, Real.exp (σ * ε * ((N : ℝ) * sourceT28Observable s n v ρ N z.1))
          ∂(sourceT28Gibbs s β ρ N).prod η) ≤ Cem) := by
  obtain ⟨βloc, hloc, hfam⟩ := exists_sourceT28_full_range_printed n hn s hs hd hv ρ M hM hρ hlog
  refine ⟨βloc, hloc, fun β hβ => ?_⟩
  obtain ⟨ε, Cpf, Cem, h1, h2, h3, h4, h5, h6, hmom, -⟩ := hfam β hβ
  refine ⟨ε, Cpf, Cem, h1, h2, h3, h4, h5, h6, ?_⟩
  intro σ hσ N hN V _ η _
  obtain ⟨hi, hI⟩ := hmom σ hσ N hN
  have := sFinite_sourceT28Gibbs s β ρ N
  refine ⟨hi.comp_fst η, ?_⟩
  have := integral_fun_fst (μ := sourceT28Gibbs s β ρ N) (ν := η)
    (fun x => Real.exp (σ * ε * ((N : ℝ) * sourceT28Observable s n v ρ N x)))
  simp only [probReal_univ, one_smul] at this
  rw [this]
  exact hI

end DGRHS.Kinetic
#check @DGRHS.Kinetic.kinetic_sourceT28_exponential_moment
#print axioms DGRHS.Kinetic.kinetic_sourceT28_exponential_moment
