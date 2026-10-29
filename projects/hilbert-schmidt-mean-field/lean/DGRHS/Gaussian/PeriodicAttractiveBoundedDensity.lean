import DGRHS.Gaussian.PeriodicAttractiveOriginalRate

/-!
Packet P11b, unit 2 (supplement): for a bounded background density `ρ ≤ M` on the torus the printed
factorial-moment hypothesis `eq:attMomentAssumption` holds automatically, with the explicit constant
`C_mom = periodicRowConstant ι M = 16 max(1,M) Cg` (the exact attractive centered kernel has the same
uniform rows as the heat-shifted ones).  Hence the torus uniform bound and the torus quantitative
determinant rate of Theorem 2.6 hold for every bounded density with no moment hypothesis at all.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Periodic
open DGRHS.Attractive DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Factorial rows of the centered repulsive kernel for every bounded background density. -/
theorem periodicLogCentered_rows_density (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    RowFactorialMoments (periodicCappedDensityMeasure ρ)
      (periodicLogCentered (periodicCappedDensityMeasure ρ)) (periodicRowConstant ι M) := by
  set μ := periodicCappedDensityMeasure ρ with hμ
  obtain ⟨hCg, hbd⟩ := periodicLogMomentConstant_spec (ι := ι)
  set Cg := periodicLogMomentConstant ι with hCgdef
  set W : PeriodicTorus ι × PeriodicTorus ι → ℝ := fun z => periodicLogKernel (z.1 - z.2) with hW
  have hWm : Measurable W := measurable_periodicLogKernelPair
  have hWs : ∀ x y, W (x, y) = W (y, x) := by
    intro x y
    show periodicLogKernel (x - y) = periodicLogKernel (y - x)
    rw [← neg_sub y x, periodicLogKernel_even]
  have hrow : RowFactorialMoments μ W (max 1 M * Cg) := by
    refine rowFactorialMoments_of_proper_bound μ W _ (fun p hp y => ?_) (fun p hp y => ?_)
    · have hI := (hbd p hp).1
      have h1 : Integrable (fun x : PeriodicTorus ι => |periodicLogKernel (ι := ι) (x - y)| ^ p)
          (periodicHaar ι) :=
        (MeasureTheory.measurePreserving_sub_right (periodicHaar ι) y).integrable_comp_of_integrable hI
      exact h1.of_measure_le_smul (by finiteness) (periodicCappedDensityMeasure_le ρ M hρ)
    · have hI := (hbd p hp).1
      have h1 := periodicDensityColumn_nonnegative_bound ρ M hM hρ
        (fun z => |periodicLogKernel (ι := ι) z| ^ p) hI (fun z => pow_nonneg (abs_nonneg _) p) y
      have h2 := (hbd p hp).2
      have hM1 : M ≤ max 1 M ^ p :=
        (le_max_right 1 M).trans (le_self_pow₀ (le_max_left 1 M) (by omega))
      calc ∫ x, |W (x, y)| ^ p ∂μ ≤ M * ∫ z, |periodicLogKernel (ι := ι) z| ^ p ∂periodicHaar ι := h1
        _ ≤ M * (Cg ^ p * (p.factorial : ℝ)) := mul_le_mul_of_nonneg_left h2 hM
        _ ≤ max 1 M ^ p * (Cg ^ p * (p.factorial : ℝ)) :=
            mul_le_mul_of_nonneg_right hM1 (by positivity)
        _ = (max 1 M * Cg) ^ p * (p.factorial : ℝ) := by rw [mul_pow]; ring
  exact abs_centered_rowFactorial μ W hWm hWs _ hrow

/-- The printed moment hypothesis `eq:attMomentAssumption` for the attractive centered kernel holds
for every bounded background density, with `C_mom = periodicRowConstant ι M`. -/
theorem periodicAttractive_rows_density (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal (|DGRHS.centeredKernel (periodicCappedDensityMeasure ρ)
        periodicAttractiveInteraction x y| ^ p) ∂periodicCappedDensityMeasure ρ) ≤
        ENNReal.ofReal (periodicRowConstant ι M ^ p * (p.factorial : ℝ)) := by
  intro p hp y
  set μ := periodicCappedDensityMeasure ρ with hμ
  have hr := periodicLogCentered_rows_density ρ M hM hρ
  have hq := periodicCentered_eq_neg_attractive μ
  have hr' := hr.neg
  have hatt : (fun z : PeriodicTorus ι × PeriodicTorus ι =>
      DGRHS.centeredKernel μ periodicAttractiveInteraction z.1 z.2) = -periodicLogCentered μ := by
    have := congrArg Neg.neg hq
    simpa using this.symm
  have hi := hr.proper p hp y
  have hbd := hr.bound p hp y
  have hrow : RowFactorialMoments μ (fun z : PeriodicTorus ι × PeriodicTorus ι =>
      DGRHS.centeredKernel μ periodicAttractiveInteraction z.1 z.2) (periodicRowConstant ι M) := by
    rw [hatt]; exact hr'
  have hint := hrow.proper p hp y
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
    pow_nonneg (abs_nonneg _) p)]
  exact ENNReal.ofReal_le_ofReal (hrow.bound p hp y)

/-- Theorem 2.6, quantitative assertion, on the torus for every bounded background density: no moment,
pair-integrability or exponential-integrability hypothesis is needed; the threshold is
`β_q(C_mom, M, d)` with the explicit torus moment constant `C_mom = periodicRowConstant ι M`. -/
theorem exists_periodicAttractiveLog_quantitative_rate_density
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M β : ℝ) (hM : 0 ≤ M) (hβ : 0 < β) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hsmall : β < periodicAttractiveQuantitativeThreshold ι (periodicRowConstant ι M) M) :
    let μ := periodicCappedDensityMeasure ρ
    let h := fun z : PeriodicTorus ι × PeriodicTorus ι =>
      DGRHS.centeredKernel μ periodicAttractiveInteraction z.1 z.2
    let I := DGRHS.interactionEnergy μ periodicAttractiveInteraction
    ∃ (hh : MemLp h 2 (μ.prod μ)) (κ : Type u) (eig : κ → ℝ)
      (b : HilbertBasis κ ℝ (Lp ℝ 2 μ)), Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (b i) = eig i • b i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ c ≤ 1 / 4 ∧ ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp
          (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h
            (DGRHS.potential μ periodicAttractiveInteraction) I N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        periodicAttractiveLogPartition μ β N < ∞ ∧
        |(periodicAttractiveLogPartition μ β N).toReal -
          Real.exp (β * I) * (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          K * (Real.exp 1 + (N : ℝ)) ^ (-c) :=
  exists_periodicAttractiveLog_original_quantitative_rate ρ M (periodicRowConstant ι M) β hM
    (periodicRowConstant_pos M) hβ hρ (periodicAttractive_rows_density ρ M hM hρ) hsmall

/-- Theorem 2.6, uniform bound, on the torus for every bounded background density: no moment,
pair-integrability or exponential-integrability hypothesis; `C_mom = periodicRowConstant ι M`. -/
theorem periodicAttractiveLogPartition_uniform_density
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M β : ℝ) (hM : 0 ≤ M) (hβ : 0 ≤ β) (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (hsmall : β < attractiveBetaThreshold (periodicRowConstant ι M)) :
    0 < attractiveBetaThreshold (periodicRowConstant ι M) ∧ ∀ N : ℕ, 0 < N →
      periodicAttractiveLogPartition (periodicCappedDensityMeasure ρ) β N ≤
        ENNReal.ofReal (periodicAttractiveUniformConstant (periodicCappedDensityMeasure ρ)
          (periodicRowConstant ι M) β) ∧
      periodicAttractiveLogPartition (periodicCappedDensityMeasure ρ) β N < ∞ :=
  periodicAttractiveLogPartition_uniform_threshold _
    (periodicSingularAbsLog_density_finite ρ M hρ) (periodicRowConstant ι M) β
    (periodicRowConstant_pos M) (periodicAttractive_rows_density ρ M hM hρ) hβ hsmall
    (periodicAttractivePotential_exp_integrable ρ M hM hρ (2 * β))

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogCentered_rows_density
#print axioms DGRHS.Periodic.periodicAttractive_rows_density
#print axioms DGRHS.Periodic.exists_periodicAttractiveLog_quantitative_rate_density
#print axioms DGRHS.Periodic.periodicAttractiveLogPartition_uniform_density
