import DGRHS.Gaussian.PeriodicRieszPartitionUniform
import DGRHS.Decoupling.Product

/-!
Packet P9c, unit 1: the torus singular-weight wrapper for Theorem 2.2(i) (TeX 504-512) on the
torus (Remark 2.1, TeX 492-496), the periodic analogue of
`proof/DGRHS/CLT/SourceRieszRawWeight.lean` (`DGRHS.CLT.sourceRieszSingularWeight`,
`sourceRieszSingularPartition`, `density_iid_collision_free`, `sourceRieszSingularWeight_ae`,
`sourceRieszSingularPartition_uniform`) and of the real identification lemmas of
`proof/DGRHS/CLT/SourceRieszSingularIdentification.lean`.

Collision convention (pinned, recorded in the P9c return packet): the periodic Riesz kernel
`periodicRieszKernel s hs2` is an almost-everywhere class representative (finite everywhere), so the
printed convention "`g = +infinity` at collisions, hence weight `0` for `beta > 0` and `1` for
`beta = 0`" is imposed literally in the weight; collisions are `mu^{⊗N}`-null for every
capped-density law (`periodic_iid_collision_free`), so the weight is a.e. the exponential of the
canonical modulated energy (`periodicRieszSingularWeight_ae`).

The data are those of the printed theorem only: `0 < s`, `2 s < d`, `0 ≤ beta`, a probability
density `rho ≤ M` almost everywhere with respect to Haar measure on the torus.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Normalized Haar measure on the torus has no atoms (every singleton is null). -/
lemma periodicHaar_nullSingletonClass : NullSingletonClass (periodicHaar ι) := by
  have hv : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one, one_smul] using
      AddCircle.volume_eq_smul_haarAddCircle (T := 1)
  have : NullSingletonClass (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    ⟨fun x => by
      have h := AddCircle.volume_closedBall (T := 1) (x := x) 0
      rw [Metric.closedBall_zero, hv] at h
      rw [h, ENNReal.ofReal_eq_zero]
      exact (min_le_right _ _).trans (by norm_num)⟩
  unfold periodicHaar
  infer_instance

/-- A capped-density law on the torus has no atoms (it is absolutely continuous with respect to
Haar measure). -/
lemma periodicCappedDensityMeasure_nullSingletonClass (ρ : PeriodicTorus ι → ℝ) :
    NullSingletonClass (periodicCappedDensityMeasure ρ) := by
  have := periodicHaar_nullSingletonClass (ι := ι)
  unfold periodicCappedDensityMeasure
  infer_instance

/-- Torus form of `ae_gaussianRieszDensity_pair_ne`: the diagonal is null for the product of a
capped-density law with itself. -/
lemma ae_periodicCappedDensity_pair_ne (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] :
    ∀ᵐ p : PeriodicTorus ι × PeriodicTorus ι
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ), p.1 ≠ p.2 := by
  have := periodicCappedDensityMeasure_nullSingletonClass (ι := ι) ρ
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).2
  exact Filter.Eventually.of_forall (fun x => ((periodicCappedDensityMeasure ρ).ae_ne x).mono
    (fun y hy => hy.symm))

/-- The literal singular Boltzmann weight of the torus Riesz gas: `1` for `β = 0`; for `β ≠ 0`
the exponential of `-β N F_N` off collisions and `0` at collisions. -/
def periodicRieszSingularWeight (s β : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (N : ℕ) (x : Fin N → PeriodicTorus ι) : ℝ≥0∞ := by
  classical
  let μ := periodicCappedDensityMeasure ρ
  let W := fun (a b : PeriodicTorus ι) => periodicRieszKernel s hs2 (a - b)
  exact if β = 0 then 1 else
    if ∀ i j : Fin N, i ≠ j → x i ≠ x j then
      ENNReal.ofReal (Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
    else 0

/-- The torus partition function `K_{N,β}(μ)` as an extended-real lower integral of the singular
weight over `μ^{⊗N}`. -/
def periodicRieszSingularPartition (s β : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, periodicRieszSingularWeight s β hs2 ρ N x
    ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ)

/-- The real partition integral of the modulated energy exponential. -/
def periodicRieszSourcePartition (s β : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) (N : ℕ) : ℝ :=
  let μ := periodicCappedDensityMeasure ρ
  let W := fun (a b : PeriodicTorus ι) => periodicRieszKernel s hs2 (a - b)
  ∫ x : Fin N → PeriodicTorus ι, Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
    (hoeffdingCentered μ
      (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)))
    (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x)
    ∂Measure.pi (fun _ : Fin N => μ)

/-- Distinct labels of an iid sample from a capped-density law almost surely occupy distinct
points. -/
lemma periodic_iid_collision_free (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) :
    ∀ᵐ x : Fin N → PeriodicTorus ι
      ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
      ∀ i j : Fin N, i ≠ j → x i ≠ x j := by
  classical
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun x h => (h hij).elim
  · exact (DGRHS.Decoupling.pair_eval_measurePreserving
      (periodicCappedDensityMeasure ρ) i j hij).quasiMeasurePreserving.ae
      (ae_periodicCappedDensity_pair_ne ρ) |>.mono (fun x hx _ => hx)

/-- The singular weight is almost everywhere the exponential of `-β N F_N`. -/
theorem periodicRieszSingularWeight_ae (s β : ℝ) (hs2 : 2 * s < (Fintype.card ι : ℝ))
    (ρ : PeriodicTorus ι → ℝ) [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)] (N : ℕ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun (a b : PeriodicTorus ι) => periodicRieszKernel s hs2 (a - b)
    periodicRieszSingularWeight s β hs2 ρ N =ᵐ[Measure.pi (fun _ : Fin N => μ)]
      (fun x => ENNReal.ofReal (Real.exp (-β * (N : ℝ) * DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))) := by
  filter_upwards [periodic_iid_collision_free ρ N] with x hx
  by_cases hb : β = 0
  · simp [periodicRieszSingularWeight, hb]
  · simp only [periodicRieszSingularWeight, ite_eq_right hb, ite_eq_left hx]

/-- The modulated exponential is integrable for every `N` (for `N = 0` it is the constant `1`;
otherwise by the uniform bound of `periodicRieszPartition_uniform`). -/
lemma periodicRieszEnergyWeight_integrable (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    let μ := periodicCappedDensityMeasure ρ
    let W := fun (a b : PeriodicTorus ι) => periodicRieszKernel s hs2 (a - b)
    Integrable (fun x : Fin N → PeriodicTorus ι => Real.exp (-β * (N : ℝ) *
      DGRHS.CLT.sourceCanonicalModulatedEnergy
        (hoeffdingCentered μ
          (fun q : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs2 (q.1 - q.2)))
        (DGRHS.potential μ W) (DGRHS.interactionEnergy μ W) N x))
      (Measure.pi (fun _ : Fin N => μ)) := by
  dsimp only
  by_cases hn : N = 0
  · subst N
    simpa only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Fin 0 → PeriodicTorus ι => (1 : ℝ))
        (Measure.pi (fun _ : Fin 0 => periodicCappedDensityMeasure ρ)))
  · obtain ⟨_, _, hU⟩ := periodicRieszPartition_uniform s β hs hβ hs2 ρ M hM hρ
    exact (hU N (by omega)).1

/-- Real identification: the extended-real partition is the `ofReal` of the real partition integral
(properness is derived from the uniform bound, not assumed). -/
lemma periodicRieszSingularPartition_eq_integral (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    periodicRieszSingularPartition s β hs2 ρ N =
      ENNReal.ofReal (periodicRieszSourcePartition s β hs2 ρ N) := by
  have hi := periodicRieszEnergyWeight_integrable s β hs hβ hs2 ρ M hM hρ N
  unfold periodicRieszSingularPartition periodicRieszSourcePartition
  rw [lintegral_congr_ae (periodicRieszSingularWeight_ae s β hs2 ρ N)]
  exact (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)).symm

/-- The torus partition is positive and finite for every `N`. -/
lemma periodicRieszSingularPartition_pos_finite (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) (N : ℕ) :
    0 < periodicRieszSingularPartition s β hs2 ρ N ∧
      periodicRieszSingularPartition s β hs2 ρ N < ∞ := by
  rw [periodicRieszSingularPartition_eq_integral s β hs hβ hs2 ρ M hM hρ N]
  refine ⟨ENNReal.ofReal_pos.mpr ?_, ENNReal.ofReal_lt_top⟩
  exact integral_exp_pos (periodicRieszEnergyWeight_integrable s β hs hβ hs2 ρ M hM hρ N)

/-- Torus Theorem 2.2(i) in the singular-partition form of the Euclidean endpoint
`DGRHS.CLT.sourceRieszSingularPartition_uniform` (same quantifier order and constant dependence):
`∃ C > 0, ∀ N ≥ 1, K_{N,β}(μ) ≤ C ∧ K_{N,β}(μ) < ∞`. -/
theorem periodicRieszSingularPartition_uniform (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ N, 1 ≤ N →
      periodicRieszSingularPartition s β hs2 ρ N ≤ ENNReal.ofReal C ∧
      periodicRieszSingularPartition s β hs2 ρ N < ∞ := by
  obtain ⟨C, hC, hU⟩ := periodicRieszPartition_uniform s β hs hβ hs2 ρ M hM hρ
  refine ⟨C, hC, ?_⟩
  intro N hN
  obtain ⟨_, hb⟩ := hU N hN
  rw [periodicRieszSingularPartition_eq_integral s β hs hβ hs2 ρ M hM hρ N]
  exact ⟨ENNReal.ofReal_le_ofReal hb, ENNReal.ofReal_lt_top⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicHaar_nullSingletonClass
#print axioms DGRHS.Periodic.periodicCappedDensityMeasure_nullSingletonClass
#print axioms DGRHS.Periodic.ae_periodicCappedDensity_pair_ne
#print axioms DGRHS.Periodic.periodic_iid_collision_free
#print axioms DGRHS.Periodic.periodicRieszSingularWeight_ae
#print axioms DGRHS.Periodic.periodicRieszEnergyWeight_integrable
#print axioms DGRHS.Periodic.periodicRieszSingularPartition_eq_integral
#print axioms DGRHS.Periodic.periodicRieszSingularPartition_pos_finite
#print axioms DGRHS.Periodic.periodicRieszSingularPartition_uniform
