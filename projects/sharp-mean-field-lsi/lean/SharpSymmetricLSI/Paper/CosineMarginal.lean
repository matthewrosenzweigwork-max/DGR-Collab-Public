import SharpSymmetricLSI.Paper.CosineTest
import SharpSymmetricLSI.Infra.GibbsGeneric

/-!
# R9: one-particle marginals of the cosine Gibbs measure are `m` (Phase 1)

`H_{N,κ}` is invariant under the simultaneous translation `X ↦ (t + x_j)_j`; averaging over `t`
(Tonelli) and translation invariance of `m` give `P_{N,κ}(x_i ∈ A) = m(A)`.
-/

open MeasureTheory Set

namespace SharpLSI

theorem continuous_cosW (κ : ℝ) : Continuous (Function.uncurry (cosW κ)) := by
  simp only [Function.uncurry_def, cosW]
  exact continuous_const.mul ((continuous_gCos.comp (continuous_fst.sub continuous_snd)).sub
    continuous_const)

theorem continuous_cos_hamiltonian (κ : ℝ) (N : ℕ) :
    Continuous (hamiltonian cosV (cosW κ) N) := by
  have hW : ∀ i j : Fin N, Continuous fun X : Config N 1 => cosW κ (X i) (X j) := fun i j =>
    (continuous_cosW κ).comp ((continuous_apply i).prodMk (continuous_apply j) :
      Continuous fun X : Config N 1 => (X i, X j))
  unfold hamiltonian
  exact (continuous_finsetSum _ fun i _ => continuous_const).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => hW i j))

/-- Simultaneous translation invariance of `H_{N,κ}`. -/
theorem cos_hamiltonian_shift (κ : ℝ) (N : ℕ) (t : Torus 1) (X : Config N 1) :
    hamiltonian cosV (cosW κ) N ((fun _ => t) + X) = hamiltonian cosV (cosW κ) N X := by
  simp only [hamiltonian, cosV, Pi.add_apply, cosW, add_sub_add_left_eq_sub]

theorem cosine_marginal_aux (κ : ℝ) {N : ℕ} (i : Fin N) :
    (gibbs cosV (cosW κ) N).map (fun X => X i) = haar 1 := by
  have hinv : (volume : Measure (Config N 1)).IsAddLeftInvariant :=
    Measure.pi.isAddLeftInvariant _
  have hH := continuous_cos_hamiltonian κ N
  set ρ := gibbsDensity (volume : Measure (Config N 1)) (hamiltonian cosV (cosW κ) N) with hρdef
  have hgibbs : gibbs cosV (cosW κ) N = (volume : Measure (Config N 1)).withDensity ρ := rfl
  have hρm : Measurable ρ := measurable_gibbsDensity _ hH
  have hρs : ∀ t X, ρ ((fun _ => t) + X) = ρ X := fun t X => by
    simp only [hρdef, gibbsDensity, cos_hamiltonian_shift]
  have hmass : ∫⁻ X, ρ X = 1 := by
    have := (isProbabilityMeasure_withDensity_gibbs (volume : Measure (Config N 1)) hH).measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  have hπ : Measurable fun X : Config N 1 => X i := measurable_pi_apply i
  ext A hA
  rw [hgibbs, Measure.map_apply hπ hA, withDensity_apply _ (hπ hA),
    ← lintegral_indicator (hπ hA)]
  set G := (fun X : Config N 1 => X i) ⁻¹' A |>.indicator ρ with hG
  have hGm : Measurable G := hρm.indicator (hπ hA)
  have hshift : Measurable fun p : Torus 1 × Config N 1 => (fun _ => p.1) + p.2 :=
    (measurable_pi_iff.mpr fun _ => measurable_fst).add measurable_snd
  calc ∫⁻ X, G X
      = ∫⁻ t : Torus 1, ∫⁻ X, G ((fun _ => t) + X) := by
        simp_rw [lintegral_add_left_eq_self]
        rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ X, ∫⁻ t : Torus 1, G ((fun _ => t) + X) :=
        lintegral_lintegral_swap (f := fun (t : Torus 1) (X : Config N 1) => G ((fun _ => t) + X))
          (μ := haar 1) (ν := volume) (hGm.comp hshift).aemeasurable
    _ = ∫⁻ X, (haar 1) A * ρ X := by
        refine lintegral_congr fun X => ?_
        have : ∀ t : Torus 1, G ((fun _ => t) + X) = A.indicator 1 (X i + t) * ρ X := by
          intro t
          simp only [hG, Set.indicator, Set.mem_preimage, Pi.add_apply, Pi.one_apply]
          rw [hρs]
          have hm : ((fun _ => t) + X ∈ (fun X : Config N 1 => X i) ⁻¹' A) ↔ X i + t ∈ A := by
            simp [add_comm]
          by_cases h : X i + t ∈ A
          · simp only [hm.mpr h, h, ↓reduceIte, one_mul]
          · have h' : ¬ ((fun _ => t) + X ∈ (fun X : Config N 1 => X i) ⁻¹' A) := fun h' =>
              h (hm.mp h')
            simp only [h', h, ↓reduceIte, zero_mul]
        simp_rw [this]
        rw [lintegral_mul_const' _ _ (by simp [hρdef, gibbsDensity]),
          lintegral_add_left_eq_self (μ := haar 1) (A.indicator 1) (X i),
          lintegral_indicator_one hA]
    _ = (haar 1) A := by rw [lintegral_const_mul _ hρm, hmass, mul_one]

end SharpLSI
