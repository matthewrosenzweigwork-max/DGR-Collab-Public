import DGRHS.Commutator.SourceLogTransportScaling

noncomputable section
open Set Metric
open scoped NNReal
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Compact-sphere bound and genuine derivative homogeneity; no derivative estimate is a premise. -/
theorem exists_sourceLogPotential_derivative_bound (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E, z ≠ 0 →
      ‖z‖ ^ n * ‖iteratedFDeriv ℝ n sourceLogPotential z‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ n (sourceLogPotential (E := E)))
      (sphere 0 1) := by
    intro z hz
    have hz1 : ‖z‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := by intro h; simp [h] at hz1
    exact ((contDiffAt_sourceLogPotential n hz0).continuousAt_iteratedFDeriv
      le_rfl).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : E := ‖z‖⁻¹ • z
  have hu1 : ‖u‖ = 1 := by
    simp [u, norm_smul, inv_mul_cancel₀ hzpos.ne']
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu1
  have hzu : ‖z‖ • u = z := by
    simp [u, smul_smul, mul_inv_cancel₀ hzpos.ne']
  have hscale := congrArg norm
    (sourceLogPotential_iteratedFDeriv_smul hn hzpos hu0)
  rw [hzu, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg z) n)] at hscale
  rw [hscale]
  exact (hC u (by simpa [mem_sphere, dist_zero_right] using hu1)).trans (le_max_left _ _)

/-- All fixed orders of the physical logarithmic commutator are bounded by Lip(v)^n. -/
theorem exists_sourceLogTransportKernel_bound (n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : ℝ≥0} {v : E → E}, LipschitzWith K v →
      ∀ p : E × E, |sourceLogTransportKernel n v p| ≤ C * (K : ℝ) ^ n := by
  obtain ⟨C, hC, hbound⟩ := exists_sourceLogPotential_derivative_bound (E := E) n hn
  refine ⟨C, hC, ?_⟩
  intro K v hv p
  classical
  by_cases hp : p.1 = p.2
  · simp only [sourceLogTransportKernel, ite_eq_left hp, abs_zero]
    positivity
  have hz : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hp
  have hw : ‖v p.1 - v p.2‖ ≤ K * ‖p.1 - p.2‖ := by
    simpa only [dist_eq_norm] using hv.dist_le_mul p.1 p.2
  rw [sourceLogTransportKernel, ite_eq_right hp, ← Real.norm_eq_abs]
  calc
    ‖iteratedFDeriv ℝ n sourceLogPotential (p.1 - p.2) (fun _ => v p.1 - v p.2)‖
        ≤ ‖iteratedFDeriv ℝ n sourceLogPotential (p.1 - p.2)‖ * ‖v p.1 - v p.2‖ ^ n := by
          simpa using (iteratedFDeriv ℝ n sourceLogPotential (p.1 - p.2)).le_opNorm
            (fun _ => v p.1 - v p.2)
    _ ≤ ‖iteratedFDeriv ℝ n sourceLogPotential (p.1 - p.2)‖ *
        ((K : ℝ) * ‖p.1 - p.2‖) ^ n := by gcongr
    _ = (‖p.1 - p.2‖ ^ n * ‖iteratedFDeriv ℝ n sourceLogPotential (p.1 - p.2)‖) *
        (K : ℝ) ^ n := by rw [mul_pow]; ring
    _ ≤ C * (K : ℝ) ^ n :=
      mul_le_mul_of_nonneg_right (hbound _ hz) (pow_nonneg K.coe_nonneg n)

#print axioms exists_sourceLogPotential_derivative_bound
#print axioms exists_sourceLogTransportKernel_bound
#check @exists_sourceLogTransportKernel_bound
end DGRHS.Commutator
