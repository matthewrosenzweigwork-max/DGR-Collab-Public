import DGPS.Lipschitz.T01MinimizerChart
import DGPS.Lipschitz.T01MeanFieldBridge
import DGPS.Lipschitz.T01EquilibriumBasis
import DGPS.Lipschitz.T01HessianCoercivity
import SharpSymmetricLSI.Paper.Sec42Dim

/-!
# Positive direct-Lipschitz scalar rate: unique nondegenerate equilibrium

The only legacy theorem used here is the assumption-clean topological theorem that a compact
Hausdorff contractible space with local Euclidean charts is a singleton.
-/

open MeasureTheory Set Topology

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- The minimizing probabilities form a compact weakly closed subset. -/
theorem t01_isClosed_minimizerSet (A : InteractionData d) :
    IsClosed {ν : ProbabilityMeasure (Torus d) |
      DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A} := by
  have heq : {ν : ProbabilityMeasure (Torus d) | DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A} =
      (fun ν : ProbabilityMeasure (Torus d) => DGPS.freeEnergy A ν) ⁻¹' Iic (DGPS.freeEnergyMinimum A) := by
    ext ν
    simp only [mem_setOf_eq, mem_preimage, mem_Iic]
    exact ⟨fun h => h.le, fun h => le_antisymm h (iInf_le _ ν)⟩
  rw [heq]
  exact (DGPS.lowerSemicontinuous_freeEnergy A).isClosed_preimage _

/-- The full weak minimizing space is a singleton under positive scalar rate. -/
theorem t01_subsingleton_minimizers (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (hrate : 0 < scalarRate A b) :
    Subsingleton {ν : ProbabilityMeasure (Torus d) |
      DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A} := by
  let M := {ν : ProbabilityMeasure (Torus d) | DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A}
  letI : CompactSpace M := isCompact_iff_compactSpace.mp (t01_isClosed_minimizerSet A).isCompact
  letI : ContractibleSpace M :=
    minimizer_set_contractible_of_lipschitz_positive_scalarRate A hLip b hrate
  refine SharpLSI.subsingleton_of_contractible_charts fun ν => ?_
  obtain ⟨k, φ, hφ⟩ := exists_t01_equilibriumBasis A ν.1
  obtain ⟨U, hUo, hνU, O, hOo, ⟨e⟩⟩ :=
    t01_minimizer_topological_chart hLip b hrate ν.2 hφ
  refine ⟨Subtype.val ⁻¹' U, hUo.preimage continuous_subtype_val, hνU, k, O, hOo, ⟨?_⟩⟩
  refine Homeomorph.trans ?_ e
  exact
    { toFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.2⟩, y.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

/-- The actual centered density-Hessian nullspace is trivial at any minimizer. -/
theorem t01_nullspace_eq_bot_of_positive_scalarRate (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (hrate : 0 < scalarRate A b)
    {μ : ProbabilityMeasure (Torus d)} (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A) :
    nullspace A μ = ⊥ := by
  classical
  have hs := t01_subsingleton_minimizers A hLip b hrate
  obtain ⟨k, φ, hφ⟩ := exists_t01_equilibriumBasis A μ
  have hk : k = 0 := by
    by_contra hk
    obtain ⟨U, hUo, hμU, O, hOo, ⟨e⟩⟩ :=
      t01_minimizer_topological_chart hLip b hrate hμ hφ
    have hOs : O.Subsingleton := by
      intro a ha c hc
      have hp : (e.symm ⟨a, ha⟩).1 = (e.symm ⟨c, hc⟩).1 :=
        congrArg (fun z : {ν : ProbabilityMeasure (Torus d) //
          DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A} => z.1) (hs.elim
          ⟨(e.symm ⟨a, ha⟩).1, (e.symm ⟨a, ha⟩).2.2⟩
          ⟨(e.symm ⟨c, hc⟩).1, (e.symm ⟨c, hc⟩).2.2⟩)
      exact congrArg Subtype.val (e.symm.injective (Subtype.ext hp))
    let a : O := e ⟨μ, hμU, hμ⟩
    have hOeq : O = {a.1} := hOs.eq_singleton_of_mem a.2
    haveI : Nontrivial (Par k) := by
      have hkpos := Nat.one_le_iff_ne_zero.mpr hk
      refine ⟨⟨0, EuclideanSpace.single (⟨0, hkpos⟩ : Fin k) 1, fun heq => ?_⟩⟩
      have hi := congrArg (fun v : Par k => v (⟨0, hkpos⟩ : Fin k)) heq
      simp at hi
    rw [hOeq] at hOo
    exact not_isOpen_singleton _ hOo
  subst hk
  have hspan : (nullspace A μ).map (meanZeroL2 μ).subtype = ⊥ := by
    rw [← hφ.span_eq]
    simp
  apply le_antisymm
  · intro f hf
    have hamb : ((f : meanZeroL2 μ) : Lp ℝ 2 (μ : Measure (Torus d))) ∈
        (nullspace A μ).map (meanZeroL2 μ).subtype := ⟨f, hf, rfl⟩
    rw [hspan, Submodule.mem_bot] at hamb
    change f = 0
    exact Subtype.ext hamb
  · exact bot_le

/-- Positive scalar rate yields a unique free-energy minimizer with a coercive density
Hessian, at the original direct-Lipschitz hypotheses. -/
theorem t01_unique_minimizer_and_coercive_hessian (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (hrate : 0 < scalarRate A b) :
    ∃ μ : ProbabilityMeasure (Torus d), DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A ∧
      (∀ ν : ProbabilityMeasure (Torus d),
        DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A → ν = μ) ∧
      IsCoerciveDensityHessian A μ := by
  obtain ⟨μ, hμ⟩ := DGPS.freeEnergy_minimum_exists A
  refine ⟨μ, hμ, fun ν hν => ?_, ?_⟩
  · exact congrArg Subtype.val ((t01_subsingleton_minimizers A hLip b hrate).elim
      ⟨ν, hν⟩ ⟨μ, hμ⟩)
  · exact isCoerciveDensityHessian_of_nullspace_eq_bot A μ
      (DGPS.Structural.minimizer_le A hμ)
      (t01_nullspace_eq_bot_of_positive_scalarRate A hLip b hrate hμ)

end DGPS.Lipschitz
