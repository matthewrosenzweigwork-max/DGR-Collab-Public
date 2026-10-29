import SharpSymmetricLSI.Defs.D08_Gibbs

/-!
# The Gibbs measure on the flattened torus (Phase 1)

`flat : (𝕋^d)^N → 𝕋^{N×d}` maps `m^{⊗N}` to the Haar measure of `𝕋^{N×d}` (`map_flat_volume`).
Under (1.2), `P_N` and `m^{⊗N}` are mutually absolutely continuous, also after flattening
(`gibbs_map_flat_ac`).
-/

open MeasureTheory Set

namespace SharpLSI

variable {d : ℕ}

theorem measurable_flat {N : ℕ} : Measurable (flat : Config N d → UnitAddTorus (Fin N × Fin d)) :=
  measurable_pi_iff.mpr fun p =>
    (measurable_pi_apply (X := fun _ : Fin d => UnitAddCircle) p.2).comp
      (measurable_pi_apply (X := fun _ : Fin N => Torus d) p.1)

/-- `flat` maps `m^{⊗N}` on `(𝕋^d)^N` to the Haar measure on `𝕋^{N×d}`. -/
theorem map_flat_volume (N : ℕ) :
    (volume : Measure (Config N d)).map flat = (volume : Measure (UnitAddTorus (Fin N × Fin d))) := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_flat (MeasurableSet.univ_pi hs)]
  have : (flat : Config N d → _) ⁻¹' univ.pi s = univ.pi fun i => univ.pi fun k => s (i, k) := by
    ext X; simp [flat, Set.mem_pi, Prod.forall]
  rw [this]
  change (Measure.pi fun _ : Fin N => Measure.pi fun _ : Fin d => (volume : Measure UnitAddCircle))
    (univ.pi fun i => univ.pi fun k => s (i, k)) = _
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Fintype.prod_prod_type']

theorem continuous_hamiltonian {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) (N : ℕ) : Continuous (hamiltonian V W N) := by
  have hW : ∀ i j : Fin N, Continuous fun X : Config N d => W (X i) (X j) := fun i j =>
    hyp.continuous_W.comp ((continuous_apply i).prodMk (continuous_apply j) :
      Continuous fun X : Config N d => (X i, X j))
  unfold hamiltonian
  exact (continuous_finsetSum _ fun i _ => hyp.continuous_V.comp (continuous_apply i)).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => hW i j))

/-- Under (1.2), `P_N ≪ m^{⊗N} ≪ P_N`. -/
theorem gibbs_ac {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) (N : ℕ) :
    gibbs V W N ≪ volume ∧ (volume : Measure (Config N d)) ≪ gibbs V W N :=
  ⟨withDensity_gibbs_absolutelyContinuous volume,
    absolutelyContinuous_withDensity_gibbs volume (continuous_hamiltonian hyp N)⟩

/-- Under (1.2), `P_N ∘ flat⁻¹` and the Haar measure of `𝕋^{N×d}` are mutually absolutely
continuous. -/
theorem gibbs_map_flat_ac {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hyp : Hyp V W KV KW) (N : ℕ) :
    (gibbs V W N).map flat ≪ (volume : Measure (UnitAddTorus (Fin N × Fin d))) ∧
      (volume : Measure (UnitAddTorus (Fin N × Fin d))) ≪ (gibbs V W N).map flat := by
  rw [← map_flat_volume N]
  exact ⟨(gibbs_ac hyp N).1.map measurable_flat, (gibbs_ac hyp N).2.map measurable_flat⟩

end SharpLSI
