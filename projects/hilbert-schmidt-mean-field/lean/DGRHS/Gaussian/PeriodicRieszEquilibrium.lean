import DGRHS.Gaussian.PeriodicEquilibriumGeneric
import DGRHS.Gaussian.PeriodicRieszLowerCutTheorem22ii

/-!
Packet P9h, unit 1 (part 2): Corollary 2.3 (`cor:equilibriumFreeEnergyCorrection`, TeX 558-595) on
the torus for the Riesz kernel `0 < s < d/2` (Remark 2.1, TeX 492-496), in the exact shape of the
Euclidean exports `DGRHS.CLT.sourceRiesz_thermal_equilibrium_macroscopic` and
`DGRHS.CLT.sourceRiesz_thermal_equilibrium_correction`
(`DGRHS/CLT/SourceRieszThermalEquilibrium.lean`).

Owner convention (see `P211_COR23_CORRESPONDENCE_20261006.md`, Deviation 3): the free energy is the
combined thermal cost `I_μ + β⁻¹ ∫ (β V + log μ) dμ` (`thermalMacroscopicFreeEnergy`), whose
integrability is a CONCLUSION (from the Euler-Lagrange relation and the integrable torus pair
interaction), not a hypothesis; it agrees with the printed separate-integral free energy whenever
`V` and the entropy are separately integrable
(`DGRHS.CLT.thermalMacroscopicFreeEnergy_eq_separate`).  The rate is the printed Riesz rate
`(log (e+N))^{-(d-2s)/(2s)}` for every `0 < s < d/2`, from the full-range torus Theorem 2.2(ii)
`periodicRieszSingularPartition_original_rate_full` (packet P9f).  No hypothesis is added to the
printed statement: `0 < β`, the equilibrium law is a capped-density probability law with density
`≤ M`, and the Euler-Lagrange relation is the thermal relation `μ_β = Z⁻¹ e^{-β(V+h_μ)}`
(relative to normalized Haar measure on the torus).
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.CLT
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Corollary 2.3 on the torus (Riesz), exact reduction `Z_{N,β} = e^{-β N F_{β,V}(μ_β)} K_{N,β}(μ_β)`
(`eq:equilibriumCanonicalSplitting`) with the combined thermal free energy; the canonical partition
function is positive and finite. -/
theorem periodicRiesz_thermal_equilibrium_macroscopic (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicRieszKernel s hs2 (a - b)) x)) = periodicCappedDensityMeasure ρ)
    (N : ℕ) (hN : 1 ≤ N) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    (0 < canonicalSingularPartition (periodicHaar ι) W V β N ∧
      canonicalSingularPartition (periodicHaar ι) W V β N < ∞) ∧
    Integrable (fun x => β * V x + llr μ (periodicHaar ι) x) μ ∧
    (canonicalSingularPartition (periodicHaar ι) W V β N).toReal =
      Real.exp (-β * (N : ℝ) * thermalMacroscopicFreeEnergy (periodicHaar ι) μ W V β) *
        (periodicRieszSingularPartition s β hs2 ρ N).toReal ∧
    Real.log (canonicalSingularPartition (periodicHaar ι) W V β N).toReal =
      -β * (N : ℝ) * thermalMacroscopicFreeEnergy (periodicHaar ι) μ W V β +
        Real.log (periodicRieszSingularPartition s β hs2 ρ N).toReal := by
  intro μ W
  have hmod := periodicRieszEnergyWeight_integrable s β hs hβ.le hs2 ρ M hM hρ N
  obtain ⟨hcan, hcost, hfac⟩ := periodic_equilibrium_thermal_generic (periodicRieszKernel s hs2)
    (periodicRieszKernel_integrable s hs2) (periodicRieszKernel_even s hs2) ρ M hρ V β hβ.ne' hEL
    N hN hmod
  have hK : (periodicRieszSingularPartition s β hs2 ρ N).toReal =
      periodicRieszSourcePartition s β hs2 ρ N := by
    rw [periodicRieszSingularPartition_eq_integral s β hs hβ.le hs2 ρ M hM hρ N]
    exact ENNReal.toReal_ofReal (by
      unfold periodicRieszSourcePartition
      exact integral_nonneg fun x => (Real.exp_pos _).le)
  have hfac' : (canonicalSingularPartition (periodicHaar ι) W V β N).toReal =
      Real.exp (-β * (N : ℝ) * thermalMacroscopicFreeEnergy (periodicHaar ι) μ W V β) *
        (periodicRieszSingularPartition s β hs2 ρ N).toReal := by
    rw [hK]
    exact hfac
  have hproper := periodicRieszSingularPartition_pos_finite s β hs hβ.le hs2 ρ M hM hρ N
  have hk : 0 < (periodicRieszSingularPartition s β hs2 ρ N).toReal :=
    ENNReal.toReal_pos hproper.1.ne' hproper.2.ne
  refine ⟨hcan, hcost, hfac', ?_⟩
  rw [hfac', Real.log_mul (Real.exp_pos _).ne' hk.ne', Real.log_exp]

/-- Corollary 2.3 on the torus (Riesz): the free-energy expansion
`log Z_{N,β} = -β N F_{β,V}(μ_β) + β I_{μ_β} - ½ log det₂(Id + β T_{μ_β}) + O(r_{N,s})` with
`r_{N,s} = (log (e+N))^{-(d-2s)/(2s)}` (`eq:equilibriumFreeEnergyExpansion`), for every
`0 < s < d/2`.  Shape of `DGRHS.CLT.sourceRiesz_thermal_equilibrium_correction`. -/
theorem periodicRiesz_thermal_equilibrium_correction (s β : ℝ) (hs : 0 < s) (hβ : 0 < β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (V : PeriodicTorus ι → ℝ)
    (hEL : (periodicHaar ι).tilted (fun x => -β * (V x +
      DGRHS.potential (periodicCappedDensityMeasure ρ)
        (fun a b => periodicRieszKernel s hs2 (a - b)) x)) = periodicCappedDensityMeasure ρ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun a b : PeriodicTorus ι => periodicRieszKernel s hs2 (a - b)
    let h := hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2))
    ∃ (hh : MemLp h 2 (μ.prod μ)) (hSym : ∀ᵐ p ∂μ.prod μ, h p.swap = h p)
      (hCan : ∀ᵐ x ∂μ, (∫ y, h (x, y) ∂μ) = 0)
      (κ : Type u) (eig : κ → ℝ) (e : HilbertBasis κ ℝ (DGRHS.Kernel.meanZeroL2 μ)),
      Countable κ ∧
      (∀ i, DGRHS.Kernel.integralOperatorOnMeanZero h hh hSym hCan (e i) = eig i • e i) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      Integrable (fun x => β * V x + llr μ (periodicHaar ι) x) μ ∧
      Tendsto (fun N => Real.log (canonicalSingularPartition (periodicHaar ι) W V β N).toReal +
        β * (N : ℝ) * thermalMacroscopicFreeEnergy (periodicHaar ι) μ W V β) atTop
        (𝓝 (β * DGRHS.interactionEnergy μ W -
          (1 / 2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
        (0 < canonicalSingularPartition (periodicHaar ι) W V β N ∧
          canonicalSingularPartition (periodicHaar ι) W V β N < ∞) ∧
        |Real.log (canonicalSingularPartition (periodicHaar ι) W V β N).toReal -
          (-β * (N : ℝ) * thermalMacroscopicFreeEnergy (periodicHaar ι) μ W V β +
            β * DGRHS.interactionEnergy μ W -
              (1 / 2 : ℝ) * Real.log (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))| ≤
            C * (Real.log (Real.exp 1 + (N : ℝ))) ^
              (-(((Fintype.card ι : ℝ) - 2 * s) / (2 * s))) := by
  intro μ W h
  obtain ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hProd, hT, hLog, C, hC, hRate⟩ :=
    periodicRieszSingularPartition_original_rate_full s β hs hβ.le hs2 ρ M hM hρ
  have hdet := log_inv_sqrt_regularizedDet eig β hD
  rw [hdet] at hLog
  simp only [neg_mul, ← sub_eq_add_neg] at hLog
  have hcanon (N : ℕ) (hN : 1 ≤ N) :=
    periodicRiesz_thermal_equilibrium_macroscopic s β hs hβ hs2 ρ M hM hρ V hEL N hN
  refine ⟨hh, hSym, hCan, κ, eig, e, hκ, he, hD, hProd, (hcanon 1 (by norm_num)).2.1,
    hLog.congr' ((eventually_ge_atTop 1).mono fun N hN => ?_), C, hC, ?_⟩
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

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicRiesz_thermal_equilibrium_macroscopic
#print axioms DGRHS.Periodic.periodicRiesz_thermal_equilibrium_correction
