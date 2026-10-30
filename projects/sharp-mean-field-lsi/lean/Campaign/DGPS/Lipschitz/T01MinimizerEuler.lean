import DGPS.Lipschitz.T01MinimizerCoordinates

/-!
# Projected Euler equation for the same minimizer coordinates

The Gibbs identity makes the Euler expression constant. Its projection onto the fixed
complement vanishes, so local implicit-function uniqueness applies to the actual Gibbs ratio.
-/

open MeasureTheory Filter

namespace DGPS.Lipschitz

variable {d : ℕ}

theorem t01_log_frozenDensity (A : InteractionData d)
    (ν : ProbabilityMeasure (Torus d)) (x : Torus d) :
    Real.log ((frozenGibbs A ν).density x) =
      -frozenPotential A (ν : Measure (Torus d)) x -
        Real.log (frozenPartition A (ν : Measure (Torus d))) := by
  change Real.log (Real.exp (-frozenPotential A (ν : Measure (Torus d)) x) /
    frozenPartition A (ν : Measure (Torus d))) = _
  rw [Real.log_div (Real.exp_pos _).ne' (frozenPartition_pos A _).ne', Real.log_exp]

/-- Centering removes the spatially constant term from a mean-zero perturbation. -/
theorem t01_centeredOperatorC_mean_zero (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (h : C(Torus d, ℝ))
    (hh : ∫ x, h x ∂(μ : Measure (Torus d)) = 0) (x : Torus d) :
    centeredOperatorC A (μ : Measure (Torus d)) h x =
      (∫ y, A.W x y * h y ∂(μ : Measure (Torus d))) -
        ∫ y, interactionConvolution A (μ : Measure (Torus d)) y * h y
          ∂(μ : Measure (Torus d)) := by
  rw [lip034_T_apply, Tfun]
  have iW : Integrable (fun y => A.W x y * h y) (μ : Measure (Torus d)) :=
    ((A.W_continuous_right x).mul h.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have ic : Integrable (fun y => interactionConvolution A (μ : Measure (Torus d)) y * h y)
      (μ : Measure (Torus d)) :=
    ((continuous_interactionConvolution A _).mul h.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have ih := integrable_cts (μ : Measure (Torus d)) h
  simp_rw [centeredKernel, add_mul, sub_mul]
  have iX := ih.const_mul (interactionConvolution A (μ : Measure (Torus d)) x)
  have iE := ih.const_mul (interactionEnergy A (μ : Measure (Torus d)))
  have hsub1 : (∫ y, A.W x y * h y -
      interactionConvolution A (μ : Measure (Torus d)) x * h y ∂(μ : Measure (Torus d))) =
      (∫ y, A.W x y * h y ∂(μ : Measure (Torus d))) -
      ∫ y, interactionConvolution A (μ : Measure (Torus d)) x * h y
        ∂(μ : Measure (Torus d)) := integral_sub iW iX
  have hsub2 : (∫ y, A.W x y * h y -
      interactionConvolution A (μ : Measure (Torus d)) x * h y -
      interactionConvolution A (μ : Measure (Torus d)) y * h y ∂(μ : Measure (Torus d))) =
      (∫ y, A.W x y * h y - interactionConvolution A (μ : Measure (Torus d)) x * h y
        ∂(μ : Measure (Torus d))) -
      ∫ y, interactionConvolution A (μ : Measure (Torus d)) y * h y
        ∂(μ : Measure (Torus d)) := integral_sub (iW.sub iX) ic
  have hadd : (∫ y, A.W x y * h y -
      interactionConvolution A (μ : Measure (Torus d)) x * h y -
      interactionConvolution A (μ : Measure (Torus d)) y * h y +
      interactionEnergy A (μ : Measure (Torus d)) * h y ∂(μ : Measure (Torus d))) =
      (∫ y, A.W x y * h y - interactionConvolution A (μ : Measure (Torus d)) x * h y -
        interactionConvolution A (μ : Measure (Torus d)) y * h y ∂(μ : Measure (Torus d))) +
      ∫ y, interactionEnergy A (μ : Measure (Torus d)) * h y
        ∂(μ : Measure (Torus d)) := integral_add ((iW.sub iX).sub ic) iE
  rw [hadd, hsub2, hsub1, integral_const_mul, integral_const_mul, hh]
  ring

/-- The Euler expression of a minimizing Gibbs ratio is spatially constant. -/
theorem t01_minimizer_euler_constant (A : InteractionData d)
    {μ ν : ProbabilityMeasure (Torus d)}
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (hν : DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A) :
    ∃ c : ℝ, ∀ x, euler A μ (t01GibbsRatio A μ ν) x = c := by
  let h := t01GibbsRatio A μ ν
  have hmean : ∫ y, h y ∂(μ : Measure (Torus d)) = 0 :=
    t01GibbsRatio_mean_zero A hμ ν
  have hconv (x : Torus d) : interactionConvolution A (ν : Measure (Torus d)) x =
      interactionConvolution A (μ : Measure (Torus d)) x +
        ∫ y, A.W x y * h y ∂(μ : Measure (Torus d)) := by
    unfold interactionConvolution
    rw [t01_integral_minimizer A hμ hν]
    have iW : Integrable (fun y => A.W x y) (μ : Measure (Torus d)) :=
      (A.W_continuous_right x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have ihW : Integrable (fun y => A.W x y * h y) (μ : Measure (Torus d)) :=
      ((A.W_continuous_right x).mul h.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [← integral_add iW ihW]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by dsimp only [h]; ring
  refine ⟨Real.log (frozenPartition A (μ : Measure (Torus d))) -
    Real.log (frozenPartition A (ν : Measure (Torus d))) -
      ∫ y, interactionConvolution A (μ : Measure (Torus d)) y * h y
        ∂(μ : Measure (Torus d)), fun x => ?_⟩
  have hμp : 0 < (frozenGibbs A μ).density x :=
    lt_of_lt_of_le (Real.exp_pos _) (frozenDensity_bounds A _ x).1
  have hνp : 0 < (frozenGibbs A ν).density x :=
    lt_of_lt_of_le (Real.exp_pos _) (frozenDensity_bounds A _ x).1
  have hratio : 1 + h x = (frozenGibbs A ν).density x / (frozenGibbs A μ).density x := by
    dsimp only [h]
    rw [t01GibbsRatio_apply]
    ring
  change nemLog h x + centeredOperatorC A (μ : Measure (Torus d)) h x = _
  rw [nemLog_apply (t01GibbsRatio_pos A μ ν), hratio,
    Real.log_div hνp.ne' hμp.ne', t01_log_frozenDensity, t01_log_frozenDensity,
    t01_centeredOperatorC_mean_zero A μ h hmean]
  have hpot : frozenPotential A (ν : Measure (Torus d)) x =
      frozenPotential A (μ : Measure (Torus d)) x +
        ∫ y, A.W x y * h y ∂(μ : Measure (Torus d)) := by
    change A.V x + interactionConvolution A (ν : Measure (Torus d)) x =
      A.V x + interactionConvolution A (μ : Measure (Torus d)) x + _
    rw [hconv]
    ring
  rw [hpot]
  ring

/-- The actual minimizer coordinates satisfy the reduced equation on the fixed complement. -/
theorem t01_minimizer_redMap {A : InteractionData d}
    {μ ν : ProbabilityMeasure (Torus d)} {k : ℕ} {φ : Fin k → C(Torus d, ℝ)}
    (hφ : IsEquilibriumBasis A μ φ)
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (hν : DGPS.freeEnergy A ν = DGPS.freeEnergyMinimum A) :
    redMap hφ (t01MinimizerCoords φ ν, t01MinimizerComplement hφ ν) = 0 := by
  obtain ⟨c, hc⟩ := t01_minimizer_euler_constant A hμ hν
  have he : euler A μ (t01GibbsRatio A μ ν) = c • (1 : C(Torus d, ℝ)) := by
    ext x
    rw [hc x]
    simp
  have hproj : projY hφ (1 : C(Torus d, ℝ)) = 0 := by
    apply Subtype.ext
    ext x
    change projRaw (μ : Measure (Torus d)) φ 1 x = 0
    rw [projRaw_apply]
    simp [hφ.integral_eq_zero]
  unfold redMap
  rw [hMap_apply, ← t01GibbsRatio_decomposition hφ hμ hν, he, map_smul, hproj, smul_zero]

end DGPS.Lipschitz
