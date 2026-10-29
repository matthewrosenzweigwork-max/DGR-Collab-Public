import DGRHS.Gaussian.PeriodicLogMasterData
import DGRHS.Gaussian.PeriodicRieszSingularPartition

/-!
Packet P9e, units 3-4: Theorem 2.2(i) (`thm:partitionFunctionBound`, TeX 504-512,
`eq:partitionUniformBoundStatement`) for the LOG kernel on the torus (Remark 2.1, TeX 492-496), in
the shape of the Euclidean export `DGRHS.CLT.sourceLogSingularPartition_uniform`
(and of the torus Riesz export `periodicRieszSingularPartition_uniform`).

Hypotheses: exactly those of the Euclidean statement, transported to the torus class
(`0 <= beta`, a probability density `rho <= M` Haar-almost everywhere on the torus).  The Euclidean
hypothesis `hpair` (pair integrability of the logarithm) is automatic here: the kernel
`periodicLogKernel` is in `L^2(Haar)`, hence its bounded-density pair integral converges
(`periodicDensityPair_integrable_of_haar`).  The `e^{-4 beta h_mu}` tail is NOT assumed (it belongs
to part (ii), eq:logRateExtraAssumptions); a torus potential bound is recorded as a by-product.

* `periodicLogKernel_uniform_exponential`: the uniform exponential moment of the exact kernel
  (transfer from the heat-time representative at `tau = 0` via the Fourier identification);
* `periodicLogPartition_uniform`: the modulated partition integrand is integrable with a bound
  uniform in `N`;
* `periodicLogSingularWeight`/`periodicLogSingularPartition` with the literal collision convention
  (weight `0` at collisions for `beta > 0`), real identification, and
  `periodicLogSingularPartition_uniform`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicLogMellinGreen_stat_eq (τ β : ℝ) (μ : Measure (PeriodicTorus ι))
    [IsProbabilityMeasure μ] (n : ℕ) (ω : Fin n → PeriodicTorus ι) :
    β * iidNegativeStatistic n (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen τ (q.1 - q.2))) ω =
    (β * periodicLogMellinFactor ι) * iidNegativeStatistic n (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι =>
        periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2))) ω := by
  have he : hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen τ (q.1 - q.2)) =
      periodicLogMellinFactor ι • hoeffdingCentered μ
        (fun q : PeriodicTorus ι × PeriodicTorus ι =>
          periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ (q.1 - q.2)) := by
    funext p
    exact hoeffdingCentered_const_mul_pointwise μ _ (periodicLogMellinFactor ι) p
  rw [he, physical_iidNegativeStatistic_const_smul]
  ring

/-- Uniform exponential moment of the normalized heat-time LOG kernel, uniform in the heat shift. -/
theorem periodicLogMellinGreen_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen τ (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen τ (q.1 - q.2))) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  have hc := (periodicLogMellinFactor_pos (ι := ι)).le
  obtain ⟨C, hC⟩ := periodicLogMellinCutoff_uniform_exponential (ι := ι)
    (β * periodicLogMellinFactor ι) (mul_nonneg hβ hc) ρ M hM hρ
  refine ⟨C, fun τ hτ n hn => ?_⟩
  simp only [periodicLogMellinGreen_stat_eq]
  exact hC τ hτ n hn

/-- The uniform exponential moment, transferred to the actual Fourier-defined even LOG kernel
`periodicLogKernel` (torus form of `logPhysicalSource_uniform_exponential`). -/
theorem periodicLogKernel_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) ω))
        (Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) ω)
        ∂Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)) ≤ C := by
  obtain ⟨C, hC⟩ := periodicLogMellinGreen_uniform_exponential β hβ ρ M hM hρ
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨hi, hb⟩ := hC 0 le_rfl n hn
  have hpair : (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen 0 (q.1 - q.2))
      =ᵐ[(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)]
      (fun q => periodicLogKernel (q.1 - q.2)) :=
    periodicDensity_pair_ae_of_haar ρ _ periodicLogMellinGreen_ae_kernel
  have hstat := ae_physical_iidNegativeStatistic_congr (periodicCappedDensityMeasure ρ) n _ _
    (ae_hoeffdingCentered_congr (periodicCappedDensityMeasure ρ) _ _ hpair)
  have hexp : (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogMellinGreen 0 (q.1 - q.2))) ω))
      =ᵐ[Measure.pi (fun _ : Fin n => periodicCappedDensityMeasure ρ)]
      (fun ω => Real.exp (β * iidNegativeStatistic n
        (hoeffdingCentered (periodicCappedDensityMeasure ρ)
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) ω)) := by
    filter_upwards [hstat] with ω hω
    rw [hω]
  exact ⟨hi.congr hexp, by rw [← integral_congr_ae hexp]; exact hb⟩

/-- Torus form of `h_mu in L^infty` for the LOG kernel: the one-body potential of a bounded-density
law is bounded (the kernel is Haar-integrable). -/
lemma periodicLogKernel_potential_abs_le (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (x : PeriodicTorus ι) :
    |DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) x| ≤
      M * ∫ z, |periodicLogKernel z| ∂periodicHaar ι := by
  have hg := periodicLogKernel_integrable (ι := ι)
  have hnn := periodicDensityRow_nonnegative_bound ρ M hM hρ (fun z => |periodicLogKernel z|)
    hg.abs (fun z => abs_nonneg _) x
  unfold DGRHS.potential
  calc |∫ y, periodicLogKernel (x - y) ∂periodicCappedDensityMeasure ρ|
      ≤ ∫ y, |periodicLogKernel (x - y)| ∂periodicCappedDensityMeasure ρ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := periodicCappedDensityMeasure ρ)
            (fun y => periodicLogKernel (x - y))
    _ ≤ _ := hnn

/-- Torus LOG analogue of `DGRHS.CLT.sourceLogPartition_uniform`: for every probability density
`ρ ≤ M` on the torus the modulated partition integrand of the repulsive LOG gas is integrable and
bounded uniformly in `N`. -/
theorem periodicLogPartition_uniform (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun (x y : PeriodicTorus ι) => periodicLogKernel (x - y)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))
    let F := DGRHS.potential μ W
    let I := DGRHS.interactionEnergy μ W
    ∃ C : ℝ, 0 < C ∧ ∀ N, 1 ≤ N →
      Integrable (fun x : Fin N → PeriodicTorus ι =>
        Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → PeriodicTorus ι,
        Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy h F I N x)
          ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
  intro μ W h F I
  obtain ⟨C, hC⟩ := periodicLogKernel_uniform_exponential β hβ ρ M hM hρ
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ periodicLogKernel_integrable
  have hF : Integrable F μ := DGRHS.integrable_potential μ W hW
  have hK : ∀ᵐ x ∂μ, F x ≤ M * ∫ z, |periodicLogKernel z| ∂periodicHaar ι :=
    Filter.Eventually.of_forall fun x =>
      (le_abs_self _).trans (periodicLogKernel_potential_abs_le ρ M hM hρ x)
  have he (N : ℕ) : (fun x : Fin N → PeriodicTorus ι => Real.exp (β *
      iidNegativeStatistic N h x)) =
      (fun x => Real.exp (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)) := by
    funext x
    rw [DGRHS.CLT.iidCanonicalExponent_eq]
  have hProper : ∀ N, 1 ≤ N → Integrable (fun x : Fin N → PeriodicTorus ι =>
      Real.exp (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x))
      (Measure.pi (fun _ : Fin N => μ)) := by
    intro N hN
    have hi := (hC N hN).1
    rw [he N] at hi
    exact hi
  have hBound : ∀ N, 1 ≤ N → (∫ x : Fin N → PeriodicTorus ι,
      Real.exp (-β / 2 * DGRHS.CanonicalVariance.normalizedOffDiagonalSum h x)
        ∂Measure.pi (fun _ : Fin N => μ)) ≤ C := by
    intro N hN
    have hb := (hC N hN).2
    rw [he N] at hb
    exact hb
  have hmom := DGRHS.CLT.sourceWeight_of_canonical_moments h F hF _ hK I β hβ C hProper hBound
  refine ⟨max (max (Real.exp (β * ((M * ∫ z, |periodicLogKernel z| ∂periodicHaar ι) - I)) * C)
    (Real.exp (-β * I))) 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro N hN
  simp_rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_exponent _ _ _ _ (show 0 < N by omega)]
  exact ⟨(hmom N).1, ((hmom N).2).trans (le_max_left _ _)⟩

/-- By-product: the exponential of the (bounded) torus potential is integrable for every
exponent; in particular the `e^{-4 beta h_mu}` integrand of eq:logRateExtraAssumptions is
automatically integrable on the torus class. -/
lemma periodicLogPotential_exp_integrable (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (c : ℝ) :
    Integrable (fun x => Real.exp (c * DGRHS.potential (periodicCappedDensityMeasure ρ)
      (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) x))
      (periodicCappedDensityMeasure ρ) := by
  let μ := periodicCappedDensityMeasure ρ
  let W := fun (x y : PeriodicTorus ι) => periodicLogKernel (x - y)
  have hW : Integrable (Function.uncurry W) (μ.prod μ) :=
    periodicDensityPair_integrable_of_haar ρ M hρ _ periodicLogKernel_integrable
  have hF : Integrable (DGRHS.potential μ W) μ := DGRHS.integrable_potential μ W hW
  have hm : AEStronglyMeasurable (fun x => Real.exp (c * DGRHS.potential μ W x)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable (hF.aestronglyMeasurable.const_mul c)
  refine (integrable_const (Real.exp (|c| * (M * ∫ z, |periodicLogKernel z| ∂periodicHaar ι)))).mono'
    hm (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc c * DGRHS.potential μ W x ≤ |c * DGRHS.potential μ W x| := le_abs_self _
    _ = |c| * |DGRHS.potential μ W x| := abs_mul _ _
    _ ≤ |c| * (M * ∫ z, |periodicLogKernel z| ∂periodicHaar ι) :=
      mul_le_mul_of_nonneg_left (periodicLogKernel_potential_abs_le ρ M hM hρ x) (abs_nonneg c)

/-! ### Singular weight and partition function (literal collision convention) -/

/-- The literal singular Boltzmann weight of the torus LOG gas: `1` for `β = 0`; for `β ≠ 0` the
exponential of `-β N F_N` off collisions and `0` at collisions. -/
def periodicLogSingularWeight (β : ℝ) (ρ : PeriodicTorus ι → ℝ) (N : ℕ)
    (x : Fin N → PeriodicTorus ι) : ℝ≥0∞ := by
  classical
  let μ := periodicCappedDensityMeasure ρ
  let W := fun (a b : PeriodicTorus ι) => periodicLogKernel (a - b)
  exact if β = 0 then 1 else
    if ∀ i j : Fin N, i ≠ j → x i ≠ x j then
      ENNReal.ofReal (Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
    else 0

/-- The torus LOG partition function `K_{N,β}(μ)` as an extended-real lower integral. -/
def periodicLogSingularPartition (β : ℝ) (ρ : PeriodicTorus ι → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, periodicLogSingularWeight β ρ N x
    ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)

/-- The real partition integral of the modulated energy exponential. -/
def periodicLogSourcePartition (β : ℝ) (ρ : PeriodicTorus ι → ℝ) (N : ℕ) : ℝ :=
  let μ := periodicCappedDensityMeasure ρ
  let W := fun (a b : PeriodicTorus ι) => periodicLogKernel (a - b)
  ∫ x : Fin N → PeriodicTorus ι, Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)))
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
    ∂Measure.pi (fun _ : Fin N => μ)

theorem periodicLogSingularWeight_ae (β : ℝ) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun (a b : PeriodicTorus ι) => periodicLogKernel (a - b)
    periodicLogSingularWeight β ρ N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun x => ENNReal.ofReal (Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))) := by
  filter_upwards [periodic_iid_collision_free ρ N] with x hx
  by_cases hb : β = 0
  · simp [periodicLogSingularWeight, hb]
  · simp only [periodicLogSingularWeight, ite_eq_right hb, ite_eq_left hx]

lemma periodicLogEnergyWeight_integrable (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ) (M : ℝ)
    (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun (a b : PeriodicTorus ι) => periodicLogKernel (a - b)
    Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β * (N : ℝ) *
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2)))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
      (Measure.pi (fun _ : Fin N => μ)) := by
  dsimp only
  by_cases hn : N = 0
  · subst N
    simpa only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Fin 0 → PeriodicTorus ι => (1 : ℝ))
        (Measure.pi (fun _ : Fin 0 => periodicCappedDensityMeasure ρ)))
  · obtain ⟨_, _, hU⟩ := periodicLogPartition_uniform β hβ ρ M hM hρ
    exact (hU N (by omega)).1

lemma periodicLogSingularPartition_eq_integral (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    periodicLogSingularPartition β ρ N = ENNReal.ofReal (periodicLogSourcePartition β ρ N) := by
  have hi := periodicLogEnergyWeight_integrable β hβ ρ M hM hρ N
  unfold periodicLogSingularPartition periodicLogSourcePartition
  rw [lintegral_congr_ae (periodicLogSingularWeight_ae β ρ N)]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm

lemma periodicLogSingularPartition_pos_finite (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    0 < periodicLogSingularPartition β ρ N ∧ periodicLogSingularPartition β ρ N < ∞ := by
  rw [periodicLogSingularPartition_eq_integral β hβ ρ M hM hρ N]
  refine ⟨ENNReal.ofReal_pos.mpr ?_, ENNReal.ofReal_lt_top⟩
  exact integral_exp_pos (periodicLogEnergyWeight_integrable β hβ ρ M hM hρ N)

/-- Torus Theorem 2.2(i), LOG kernel, in the singular-partition form of the Euclidean endpoint
`DGRHS.CLT.sourceLogSingularPartition_uniform` (same quantifier order and constant dependence). -/
theorem periodicLogSingularPartition_uniform (β : ℝ) (hβ : 0 ≤ β) (ρ : PeriodicTorus ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N, 1 ≤ N →
      periodicLogSingularPartition β ρ N ≤ ENNReal.ofReal C ∧
      periodicLogSingularPartition β ρ N < ∞ := by
  obtain ⟨C, hC, hU⟩ := periodicLogPartition_uniform β hβ ρ M hM hρ
  refine ⟨C, hC, ?_⟩
  intro N hN
  obtain ⟨_, hb⟩ := hU N hN
  rw [periodicLogSingularPartition_eq_integral β hβ ρ M hM hρ N]
  exact ⟨ENNReal.ofReal_le_ofReal hb, ENNReal.ofReal_lt_top⟩

/-- Torus Theorem 2.2(i), LOG kernel, collision-free export (shape of
`periodicRiesz_partitionFunctionBound_collisionFree`). -/
theorem periodicLog_partitionFunctionBound_collisionFree (β : ℝ) (hβ : 0 ≤ β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (∀ N : ℕ, ∀ᵐ x : Fin N → PeriodicTorus ι
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
        ∀ i j : Fin N, i ≠ j → x i ≠ x j) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ N, 1 ≤ N →
      periodicLogSingularPartition β ρ N = ENNReal.ofReal (periodicLogSourcePartition β ρ N) ∧
      0 < periodicLogSourcePartition β ρ N ∧
      periodicLogSourcePartition β ρ N ≤ C ∧
      periodicLogSingularPartition β ρ N ≤ ENNReal.ofReal C ∧
      periodicLogSingularPartition β ρ N < ∞ := by
  refine ⟨fun N => periodic_iid_collision_free ρ N, ?_⟩
  obtain ⟨C, hC, hU⟩ := periodicLogPartition_uniform β hβ ρ M hM hρ
  refine ⟨C, hC, fun N hN => ?_⟩
  have hb : periodicLogSourcePartition β ρ N ≤ C := (hU N hN).2
  have hpos : 0 < periodicLogSourcePartition β ρ N :=
    integral_exp_pos (periodicLogEnergyWeight_integrable β hβ ρ M hM hρ N)
  have heq := periodicLogSingularPartition_eq_integral β hβ ρ M hM hρ N
  exact ⟨heq, hpos, hb, heq ▸ ENNReal.ofReal_le_ofReal hb, heq ▸ ENNReal.ofReal_lt_top⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogMellinGreen_stat_eq
#print axioms DGRHS.Periodic.periodicLogMellinGreen_uniform_exponential
#print axioms DGRHS.Periodic.periodicLogKernel_uniform_exponential
#print axioms DGRHS.Periodic.periodicLogKernel_potential_abs_le
#print axioms DGRHS.Periodic.periodicLogPartition_uniform
#print axioms DGRHS.Periodic.periodicLogPotential_exp_integrable
#print axioms DGRHS.Periodic.periodicLogSingularWeight_ae
#print axioms DGRHS.Periodic.periodicLogEnergyWeight_integrable
#print axioms DGRHS.Periodic.periodicLogSingularPartition_eq_integral
#print axioms DGRHS.Periodic.periodicLogSingularPartition_pos_finite
#print axioms DGRHS.Periodic.periodicLogSingularPartition_uniform
#print axioms DGRHS.Periodic.periodicLog_partitionFunctionBound_collisionFree
