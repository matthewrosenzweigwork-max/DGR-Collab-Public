import DGRHS.Commutator.SourceRieszTransportKernel

/-! Actual all-fixed-order Riesz derivative and Lipschitz contraction estimate.
The compact-unit-sphere route is adapted from worker A's checked native
SourceLogTransportBound, request2ab18c8d038146018736db78ab08110e.
The Riesz homogeneity factor is retained explicitly. -/
noncomputable section
open Set Metric
open scoped NNReal
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_sourceRieszPotential_derivative_bound (s : ℝ) (n : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ z : E,z≠0 →
      ‖z‖^n*‖iteratedFDeriv ℝ n (sourceRieszPotential s) z‖≤C*‖z‖^(-s) := by
  have hc : ContinuousOn (iteratedFDeriv ℝ n (sourceRieszPotential (E:=E) s)) (sphere 0 1) := by
    intro z hz
    have hz1 : ‖z‖=1 := by simpa [mem_sphere,dist_zero_right] using hz
    have hz0 : z≠0 := by intro h;simp [h] at hz1
    exact ((contDiffAt_sourceRieszPotential s n hz0).continuousAt_iteratedFDeriv le_rfl).continuousWithinAt
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:E) 1).exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro z hz
  have hzpos : 0<‖z‖ := norm_pos_iff.mpr hz
  let u : E := ‖z‖⁻¹ • z
  have hu1 : ‖u‖=1 := by
    simp [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg z),inv_mul_cancel₀ hzpos.ne']
  have hu0 : u≠0 := by intro h;simp [h] at hu1
  have hzu : ‖z‖ • u=z := by simp [u,smul_smul,mul_inv_cancel₀ hzpos.ne']
  have hscale := congrArg norm (sourceRieszPotential_iteratedFDeriv_smul s n hzpos hu0)
  rw [hzu,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg z) n),
    norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) (-s))] at hscale
  rw [hscale]
  have hb := (hC u (by simpa [mem_sphere,dist_zero_right] using hu1)).trans (le_max_left C 0)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (norm_nonneg z) (-s))

/-- The actual tensor contraction for globally Lipschitz transport, collision
zero totalized; the constant depends only on s,n and the finite-dimensional
ambient space. No derivative bound, differentiability of v or moment premise. -/
theorem exists_sourceRieszTransportKernel_bound (s : ℝ) (n : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ {K : ℝ≥0} {v : E→E},LipschitzWith K v →
      ∀ p : E×E,|sourceRieszTransportKernel n s v p|≤C*(K:ℝ)^n*‖p.1-p.2‖^(-s) := by
  obtain ⟨C,hC,hbound⟩ := exists_sourceRieszPotential_derivative_bound (E:=E) s n
  refine ⟨C,hC,?_⟩
  intro K v hv p
  classical
  by_cases hp : p.1=p.2
  · simp only [sourceRieszTransportKernel,if_pos hp,abs_zero]
    positivity
  have hz : p.1-p.2≠0 := sub_ne_zero.mpr hp
  have hw : ‖v p.1-v p.2‖≤K*‖p.1-p.2‖ := by
    simpa only [dist_eq_norm] using hv.dist_le_mul p.1 p.2
  rw [sourceRieszTransportKernel,ite_eq_right hp,←Real.norm_eq_abs]
  calc
    ‖iteratedFDeriv ℝ n (sourceRieszPotential s) (p.1-p.2) (fun _=>v p.1-v p.2)‖
      ≤ ‖iteratedFDeriv ℝ n (sourceRieszPotential s) (p.1-p.2)‖*‖v p.1-v p.2‖^n := by
        simpa using (iteratedFDeriv ℝ n (sourceRieszPotential s) (p.1-p.2)).le_opNorm (fun _=>v p.1-v p.2)
    _ ≤ ‖iteratedFDeriv ℝ n (sourceRieszPotential s) (p.1-p.2)‖*((K:ℝ)*‖p.1-p.2‖)^n := by gcongr
    _ = (‖p.1-p.2‖^n*‖iteratedFDeriv ℝ n (sourceRieszPotential s) (p.1-p.2)‖)*(K:ℝ)^n := by rw [mul_pow];ring
    _ ≤ (C*‖p.1-p.2‖^(-s))*(K:ℝ)^n := mul_le_mul_of_nonneg_right (hbound _ hz) (pow_nonneg K.coe_nonneg n)
    _ = _ := by ring
end DGRHS.Commutator
#check @DGRHS.Commutator.exists_sourceRieszPotential_derivative_bound
#print axioms DGRHS.Commutator.exists_sourceRieszPotential_derivative_bound
#check @DGRHS.Commutator.exists_sourceRieszTransportKernel_bound
#print axioms DGRHS.Commutator.exists_sourceRieszTransportKernel_bound
