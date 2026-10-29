/- Development: actual SAME-process mixed linear/quadratic Gaussian transform
at a single strict spectral margin. All zero modes are retained. -/
import DGRHS.Gaussian.HilbertTiltedLaplace
import DGRHS.Gaussian.WeakMarginChaosLaplace
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
namespace DGRHS.Gaussian
variable {ι H : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

set_option maxHeartbeats 1000000 in
/-- The power bound and uniform integrability are derived from square summability
and the single original margin; neither is a supplied proof hypothesis. -/
theorem integral_exp_hilbert_tilt_weak_margin (b : HilbertBasis ι ℝ H) (v : H)
    (β : ℝ) (a : ι → ℝ) (ha : Summable (fun i => (a i)^2))
    (hm : ∀ i, 0 < 1+β*a i) (f : ι → ℕ) (hf : Function.Injective f) :
    Integrable (fun ω => Real.exp (indexedGaussianIsometry b f hf v ω-
      (β/2)*centeredGaussianChaos a f ω)) IsonormalProcess.iidStdGaussian ∧
    (∫ ω, Real.exp (indexedGaussianIsometry b f hf v ω-
      (β/2)*centeredGaussianChaos a f ω) ∂IsonormalProcess.iidStdGaussian) =
      (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*a i)))⁻¹ *
        Real.exp ((∑' i, (b.repr v i)^2/(1+β*a i))/2) := by
  obtain ⟨p,hp,_,hpm⟩ := exists_spectral_power_above_one β a ha hm
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  obtain ⟨δ,hδ,hδm⟩ := DGRHS.Kernel.exists_uniform_spectral_margin (p*β) a ha hpm
  obtain ⟨ss,hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  let F := fun n => tiltedDiagonalPartialExp β a (fun i => b.repr v i) f (ss n)
  let G := fun ω => Real.exp (indexedGaussianIsometry b f hf v ω-
    (β/2)*centeredGaussianChaos a f ω)
  let C : ℝ≥0 := ⟨Real.exp (((∑' i, |DGRHS.Kernel.regularizedLog (p*β*a i)|)+
    (p^2/δ)*(∑' i, (b.repr v i)^2))/(2*p)), (Real.exp_pos _).le⟩
  have hq : 1 < ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_lt_ofReal_iff hp0).mpr hp
  obtain ⟨hG,hint⟩ := tendsto_integral_of_Lq_bound_and_inMeasure F G
    (ENNReal.ofReal p) hq ENNReal.ofReal_ne_top
    (fun n => (tiltedDiagonalPartial_Lq_bound β p δ hp0 hδ a (fun i => b.repr v i)
      hδm ha (summable_basis_coeff_sq b v) f hf (ss n)).1) C
    (fun n => by
      have hCeq : ENNReal.ofReal (Real.exp (((∑' i, |DGRHS.Kernel.regularizedLog (p*β*a i)|)+
          (p^2/δ)*(∑' i, (b.repr v i)^2))/(2*p))) = (C : ℝ≥0∞) :=
        ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le
      rw [← hCeq]
      exact (tiltedDiagonalPartial_Lq_bound β p δ hp0 hδ a (fun i => b.repr v i)
        hδm ha (summable_basis_coeff_sq b v) f hf (ss n)).2)
    (tendstoInMeasure_tiltedDiagonalPartial b v β a ha f hf hss)
  have hβsq : Summable (fun i => (β*a i)^2) := by
    simpa only [mul_pow] using ha.mul_left (β^2)
  have hl := ((DGRHS.Kernel.summable_regularizedLog hβsq).hasSum.comp hss).neg.div_const 2
  have ht := ((summable_tilted_basis_coeff b v β a ha hm).hasSum.comp hss).div_const 2
  have hv := Real.continuous_exp.continuousAt.tendsto.comp (hl.add ht)
  have hvals : ∀ n, (∫ ω, F n ω ∂IsonormalProcess.iidStdGaussian) =
      Real.exp (-(∑ i ∈ ss n, DGRHS.Kernel.regularizedLog (β*a i))/2 +
        (∑ i ∈ ss n, (b.repr v i)^2/(1+β*a i))/2) :=
    fun n => (tiltedDiagonalPartial_exponential β a (fun i => b.repr v i) hm f hf (ss n)).2
  have he := tendsto_nhds_unique hint (hv.congr (fun n => (hvals n).symm))
  refine ⟨hG, ?_⟩
  rw [he, Real.exp_add, DGRHS.Kernel.regularizedDet_eq_exp hβsq hm]
  have hr : Real.sqrt (Real.exp (∑' i, DGRHS.Kernel.regularizedLog (β*a i))) =
      Real.exp ((∑' i, DGRHS.Kernel.regularizedLog (β*a i))/2) := by
    calc
      _ = Real.exp (Real.log (Real.sqrt
          (Real.exp (∑' i, DGRHS.Kernel.regularizedLog (β*a i))))) :=
        (Real.exp_log (Real.sqrt_pos.mpr (Real.exp_pos _))).symm
      _ = _ := by rw [Real.log_sqrt (Real.exp_pos _).le, Real.log_exp]
  rw [hr, ← Real.exp_neg]
  congr 2
  ring
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.integral_exp_hilbert_tilt_weak_margin
#check @DGRHS.Gaussian.integral_exp_hilbert_tilt_weak_margin
