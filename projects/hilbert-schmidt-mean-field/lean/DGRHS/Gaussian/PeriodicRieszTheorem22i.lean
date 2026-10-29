import DGRHS.Gaussian.PeriodicRieszSingularPartition

/-!
Packet P9c, unit 2: collision-free export of Theorem 2.2(i) (`thm:partitionFunctionBound`,
TeX 504-512, `eq:partitionUniformBoundStatement`) on the torus (Remark 2.1, TeX 492-496), in the
shape of the Euclidean export (`DGRHS.CLT.sourceRieszSingularPartition_uniform` together with
`density_iid_collision_free` and `sourceRieszSingularPartition_eq_integral`).

One statement bundles, for the periodic Riesz kernel and any torus law `μ = ρ dx`, `ρ ≤ M`:

* the iid sample is almost surely collision-free (so the printed convention "weight `0` at
  collisions for `β > 0`" does not change the partition function);
* one constant `C > 0` such that for every `N ≥ 1` the lower-integral partition function
  `K_{N,β}(μ)` equals `ofReal` of the real partition integral, which is positive and `≤ C`, and
  `K_{N,β}(μ) ≤ ofReal C`, `K_{N,β}(μ) < ∞`.

No hypothesis beyond the printed ones (`0 < s`, `2 s < d`, `0 ≤ β`, bounded probability density).
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian DGRHS.Concentration
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Torus Theorem 2.2(i), collision-free singular-partition export. -/
theorem periodicRiesz_partitionFunctionBound_collisionFree (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    (∀ N : ℕ, ∀ᵐ x : Fin N → PeriodicTorus ι
        ∂Measure.pi (fun _ : Fin N => periodicCappedDensityMeasure ρ),
        ∀ i j : Fin N, i ≠ j → x i ≠ x j) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ N, 1 ≤ N →
      periodicRieszSingularPartition s β hs2 ρ N =
        ENNReal.ofReal (periodicRieszSourcePartition s β hs2 ρ N) ∧
      0 < periodicRieszSourcePartition s β hs2 ρ N ∧
      periodicRieszSourcePartition s β hs2 ρ N ≤ C ∧
      periodicRieszSingularPartition s β hs2 ρ N ≤ ENNReal.ofReal C ∧
      periodicRieszSingularPartition s β hs2 ρ N < ∞ := by
  refine ⟨fun N => periodic_iid_collision_free ρ N, ?_⟩
  obtain ⟨C, hC, hU⟩ := periodicRieszPartition_uniform s β hs hβ hs2 ρ M hM hρ
  refine ⟨C, hC, fun N hN => ?_⟩
  have hb : periodicRieszSourcePartition s β hs2 ρ N ≤ C := (hU N hN).2
  have hpos : 0 < periodicRieszSourcePartition s β hs2 ρ N :=
    integral_exp_pos (periodicRieszEnergyWeight_integrable s β hs hβ hs2 ρ M hM hρ N)
  have heq := periodicRieszSingularPartition_eq_integral s β hs hβ hs2 ρ M hM hρ N
  exact ⟨heq, hpos, hb, heq ▸ ENNReal.ofReal_le_ofReal hb, heq ▸ ENNReal.ofReal_lt_top⟩

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicRiesz_partitionFunctionBound_collisionFree
