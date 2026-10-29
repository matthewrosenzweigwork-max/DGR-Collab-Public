import DGRHS.Gaussian.PeriodicEquilibriumGeneric
import DGRHS.Gaussian.PeriodicLogTheorem22ii

/-!
Packet P9h, unit 1 (part 3): Corollary 2.3 (`cor:equilibriumFreeEnergyCorrection`, TeX 558-595) on
the torus for the LOG kernel `s = 0` (Remark 2.1, TeX 492-496), in the exact shape of the Euclidean
exports `DGRHS.CLT.sourceLog_equilibrium_macroscopic_original` and
`DGRHS.CLT.sourceLog_equilibrium_correction_original`
(`DGRHS/CLT/SourceLogEquilibriumOriginal.lean`).

The free energy is the printed separate-integral one,
`F_{β,V}(μ) = ∫ V dμ + I_μ + β⁻¹ ∫ log μ dμ` (`macroscopicFreeEnergy`, TeX 543-548).  As in the
Euclidean LOG export neither `V ∈ L¹(μ)` nor the integrability of `log μ` is assumed: both are
derived (the entropy of a bounded-density law is finite because the reference measure, normalized
Haar measure, is a probability measure: `periodic_integrable_llr`; then `V ∈ L¹(μ)` follows from the
Euler-Lagrange relation: `periodic_equilibrium_integrable_potential`).  The two extra part-(ii)
hypotheses `eq:logRateExtraAssumptions` are automatic on the torus (packet P9g), so the main
statements omit them; `_printed` restatements carry them as unused hypotheses.  The rate is the
LOG power rate `(e+N)^{-c_log}`, `0 < c_log ≤ 1/2`, of the torus Theorem 2.2(ii)
`periodicLogSingularPartition_original_rate` (packet P9g), for every dimension.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.CLT
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Corollary 2.3 on the torus (LOG), exact reduction `Z_{N,β} = e^{-β N F_{β,V}(μ_β)} K_{N,β}(μ_β)`
(`eq:equilibriumCanonicalSplitting`) with the separate-integral free energy; the entropy of the
equilibrium law is integrable (derived). -/
theorem periodicLog_equilibrium_macroscopic (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicLogKernel (a - b)) x)) = periodicCappedDensityMeasure ρ)
    (N : ℕ) (hN : 1 ≤ N) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
    (0 < canonicalSingularPartition (periodicHaar ι) W V β N ∧
      canonicalSingularPartition (periodicHaar ι) W V β N < ∞) ∧
    Integrable (llr μ (periodicHaar ι)) μ ∧
    (canonicalSingularPartition (periodicHaar ι) W V β N).toReal =
      Real.exp (-β * (N : ℝ) * macroscopicFreeEnergy (periodicHaar ι) μ W V β) *
        (periodicLogSingularPartition β ρ N).toReal ∧
    Real.log (canonicalSingularPartition (periodicHaar ι) W V β N).toReal =
      -β * (N : ℝ) * macroscopicFreeEnergy (periodicHaar ι) μ W V β +
        Real.log (periodicLogSingularPartition β ρ N).toReal := by
  intro μ W
  have hmod := periodicLogEnergyWeight_integrable β hβ.le ρ M hM hρ N
  have hV := periodic_equilibrium_integrable_potential periodicLogKernel
    periodicLogKernel_integrable ρ M hM hρ V β hβ.ne' hEL
  obtain ⟨hcan, hent, hfac⟩ := periodic_equilibrium_macroscopic_generic periodicLogKernel
    periodicLogKernel_integrable periodicLogKernel_even ρ M hρ V hV β hβ.ne' hEL N hN hmod
  have hK : (periodicLogSingularPartition β ρ N).toReal = periodicLogSourcePartition β ρ N := by
    rw [periodicLogSingularPartition_eq_integral β hβ.le ρ M hM hρ N]
    exact ENNReal.toReal_ofReal (by
      unfold periodicLogSourcePartition
      exact integral_nonneg fun x => (Real.exp_pos _).le)
  have hfac' : (canonicalSingularPartition (periodicHaar ι) W V β N).toReal =
      Real.exp (-β * (N : ℝ) * macroscopicFreeEnergy (periodicHaar ι) μ W V β) *
        (periodicLogSingularPartition β ρ N).toReal := by
    rw [hK]
    exact hfac
  have hproper := periodicLogSingularPartition_pos_finite β hβ.le ρ M hM hρ N
  have hk : 0 < (periodicLogSingularPartition β ρ N).toReal :=
    ENNReal.toReal_pos hproper.1.ne' hproper.2.ne
  refine ⟨hcan, hent, hfac', ?_⟩
  rw [hfac', Real.log_mul (Real.exp_pos _).ne' hk.ne', Real.log_exp]

/-- Corollary 2.3 on the torus (LOG): the free-energy expansion
`log Z_{N,β} = -β N F_{β,V}(μ_β) + β I_{μ_β} - ½ log det₂(Id + β T_{μ_β}) + O((e+N)^{-c_log})`
(`eq:equilibriumFreeEnergyExpansion`), for every dimension `d ≥ 1`.  Shape of
`DGRHS.CLT.sourceLog_equilibrium_correction_original`. -/
theorem periodicLog_equilibrium_correction (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicLogKernel (a - b)) x)) = periodicCappedDensityMeasure ρ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))
    ∃ (hh : MemLp h 2 (μ.prod μ)) (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      Integrable (llr μ (periodicHaar ι)) μ ∧
      Tendsto (fun N => Real.log (canonicalSingularPartition (periodicHaar ι) W V β N).toReal +
        β * (N : ℝ) * macroscopicFreeEnergy (periodicHaar ι) μ W V β) atTop
        (𝓝 (β * DGRHS.interactionEnergy μ W -
          (1 / 2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < canonicalSingularPartition (periodicHaar ι) W V β N ∧
          canonicalSingularPartition (periodicHaar ι) W V β N < ∞) ∧
        |Real.log (canonicalSingularPartition (periodicHaar ι) W V β N).toReal -
          (-β * (N : ℝ) * macroscopicFreeEnergy (periodicHaar ι) μ W V β +
            β * DGRHS.interactionEnergy μ W -
              (1 / 2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))| ≤
            C * (Real.exp 1 + (N : ℝ)) ^ (-c) := by
  intro μ W h
  obtain ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hProd, hT, hLog, c, C, hc0, hc1, hC, hRate⟩ :=
    periodicLogSingularPartition_original_rate β hβ.le ρ M hM hρ
  have hdet := log_inv_sqrt_regularizedDet eig β hD
  rw [hdet] at hLog
  simp only [neg_mul, ← sub_eq_add_neg] at hLog
  have hcanon (N : ℕ) (hN : 1 ≤ N) :=
    periodicLog_equilibrium_macroscopic β hβ ρ M hM hρ V hEL N hN
  refine ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hProd, (hcanon 1 (by norm_num)).2.1,
    hLog.congr' ((eventually_ge_atTop 1).mono fun N hN => ?_), c, C, hc0, hc1, hC, ?_⟩
  · dsimp only
    rw [(hcanon N hN).2.2.2]
    ring
  · intro N hN
    refine ⟨(hcanon N hN).1, ?_⟩
    have hr := (hRate N hN).2.2.2
    rw [hdet] at hr
    convert hr using 1
    rw [(hcanon N hN).2.2.2]
    congr 1
    ring

/-- The same theorem with the two extra hypotheses of the printed part (ii) of Theorem 2.2
(`eq:logRateExtraAssumptions`) restated literally (unused; both are automatic on the torus). -/
theorem periodicLog_equilibrium_correction_printed (β : ℝ) (hβ : 0 < β)
    (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (_htail : Integrable (fun x => Real.exp (-4 * β * DGRHS.potential
      (periodicCappedDensityMeasure ρ) (fun a b : PeriodicTorus ι => periodicLogKernel (a - b)) x))
      (periodicCappedDensityMeasure ρ))
    (_hL2 : MemLp (hoeffdingCentered (periodicCappedDensityMeasure ρ)
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))) 2
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)))
    (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicLogKernel (a - b)) x)) = periodicCappedDensityMeasure ρ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicLogKernel (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (q.1 - q.2))
    ∃ (hh : MemLp h 2 (μ.prod μ)) (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      Integrable (llr μ (periodicHaar ι)) μ ∧
      Tendsto (fun N => Real.log (canonicalSingularPartition (periodicHaar ι) W V β N).toReal +
        β * (N : ℝ) * macroscopicFreeEnergy (periodicHaar ι) μ W V β) atTop
        (𝓝 (β * DGRHS.interactionEnergy μ W -
          (1 / 2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < canonicalSingularPartition (periodicHaar ι) W V β N ∧
          canonicalSingularPartition (periodicHaar ι) W V β N < ∞) ∧
        |Real.log (canonicalSingularPartition (periodicHaar ι) W V β N).toReal -
          (-β * (N : ℝ) * macroscopicFreeEnergy (periodicHaar ι) μ W V β +
            β * DGRHS.interactionEnergy μ W -
              (1 / 2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))| ≤
            C * (Real.exp 1 + (N : ℝ)) ^ (-c) :=
  periodicLog_equilibrium_correction β hβ ρ M hM hρ V hEL

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLog_equilibrium_macroscopic
#print axioms DGRHS.Periodic.periodicLog_equilibrium_correction
#print axioms DGRHS.Periodic.periodicLog_equilibrium_correction_printed
