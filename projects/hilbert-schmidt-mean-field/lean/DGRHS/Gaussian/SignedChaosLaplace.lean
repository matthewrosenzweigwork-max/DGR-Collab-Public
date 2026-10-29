/- UNCHECKED outside frozen proof. Signed HS chaos Laplace transform under an
explicit doubled spectral margin. No trace or positive spectrum is assumed.
This stronger supporting margin must not replace the undoubled threshold of
any source endpoint; removal via finite exceptional modes remains separate. -/
import DGRHS.Gaussian.ChaosConvergence
import DGRHS.Gaussian.InfinitePositiveLaplace
import DGRHS.Kernel.SpectralHilbertSchmidt
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace DGRHS.Gaussian

lemma signedCenteredFactor_eq_exp (t : ℝ) (hp : 0 < 1+t) :
    Real.exp (t/2)*(Real.sqrt (1+t))⁻¹ =
      Real.exp (-DGRHS.Kernel.regularizedLog t/2) := by
  have hr : Real.sqrt (1+t) = Real.exp (Real.log (1+t)/2) := by
    rw [← Real.log_sqrt hp.le, Real.exp_log (Real.sqrt_pos.mpr hp)]
  rw [hr, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  unfold DGRHS.Kernel.regularizedLog
  ring

lemma signedFiniteCentered_exponential {j : Type*} [Fintype j]
    (β : ℝ) (a : j → ℝ) (hm : ∀ i, 0 < 1+β*a i) :
    Integrable (fun z : j → ℝ => Real.exp (∑ i, (β*a i/2)*(1-(z i)^2)))
      (finiteStandardGaussian j) ∧
    (∫ z : j → ℝ, Real.exp (∑ i, (β*a i/2)*(1-(z i)^2))
      ∂finiteStandardGaussian j) =
        Real.exp (-(∑ i, DGRHS.Kernel.regularizedLog (β*a i))/2) := by
  classical
  have hm' : ∀ i, β*(-a i)<1 := by intro i; have := hm i; nlinarith
  have heq : (fun z : j → ℝ => Real.exp (∑ i, (β*a i/2)*(1-(z i)^2))) =
      fun z => Real.exp (∑ i, β*a i/2) *
        Real.exp (∑ i, (β*(-a i)/2)*(z i)^2) := by
    funext z
    rw [← Real.exp_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [heq]
  refine ⟨(integrable_exp_pos_quadratic β (fun i => -a i) hm').const_mul _, ?_⟩
  rw [integral_const_mul, integral_exp_pos_quadratic β (fun i => -a i) hm',
    Real.exp_sum, ← Finset.prod_mul_distrib]
  have hfac : ∀ i, Real.exp (β*a i/2)*(Real.sqrt (1-β*(-a i)))⁻¹ =
      Real.exp (-DGRHS.Kernel.regularizedLog (β*a i)/2) := by
    intro i
    rw [mul_neg, sub_neg_eq_add]
    exact signedCenteredFactor_eq_exp _ (hm i)
  rw [Finset.prod_congr rfl (fun i _ => hfac i), ← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div, ← Finset.sum_neg_distrib]

variable {ι : Type*} [Countable ι]

lemma signedDiagonalPartial_exponential (β : ℝ) (a : ι → ℝ)
    (hm : ∀ i, 0 < 1+β*a i) (f : ι → ℕ) (hf : Function.Injective f) (s : Finset ι) :
    Integrable (diagonalPartialExp β a f s) IsonormalProcess.iidStdGaussian ∧
    (∫ ω, diagonalPartialExp β a f s ω ∂IsonormalProcess.iidStdGaussian) =
      Real.exp (-(∑ i ∈ s, DGRHS.Kernel.regularizedLog (β*a i))/2) := by
  let g := fun ω (i : s) => IsonormalProcess.coord (f i) ω
  have hg : Measurable g := Measurable.of_eval
    (fun i : s => IsonormalProcess.measurable_coord (f i))
  have hp : MeasurePreserving g IsonormalProcess.iidStdGaussian (finiteStandardGaussian s) :=
    ⟨hg, selectedGaussian_map f hf s⟩
  let F := fun z : s → ℝ => Real.exp (∑ i : s, (β*a i/2)*(1-(z i)^2))
  have hi := signedFiniteCentered_exponential β (fun i : s => a i) (fun i => hm i)
  have he : F ∘ g = diagonalPartialExp β a f s := by
    funext ω
    change Real.exp (∑ i : s, (β*a i/2)*(1-(ω (f i))^2)) =
      Real.exp (∑ i ∈ s, (β*a i/2)*(1-(ω (f i))^2))
    congr 1
    exact Finset.sum_coe_sort s (fun i : ι => (β*a i/2)*(1-(ω (f i))^2))
  refine ⟨by rw [← he]; exact hp.integrable_comp_of_integrable hi.1, ?_⟩
  have hmap := integral_map (μ := IsonormalProcess.iidStdGaussian) (φ := g)
    (f := F) hg.aemeasurable (by rw [hp.map_eq]; exact hi.1.aestronglyMeasurable)
  rw [hp.map_eq] at hmap
  rw [← he]
  calc
    _ = ∫ z, F z ∂finiteStandardGaussian s := by
      simpa only [Function.comp_apply] using hmap.symm
    _ = _ := by
      rw [hi.2, Finset.sum_coe_sort s (fun i => DGRHS.Kernel.regularizedLog (β*a i))]

lemma signedDiagonalPartial_sq (β : ℝ) (a : ι → ℝ) (f : ι → ℕ)
    (s : Finset ι) (ω : ℕ → ℝ) :
    (diagonalPartialExp β a f s ω)^2 = diagonalPartialExp (2*β) a f s ω := by
  unfold diagonalPartialExp
  rw [sq, ← Real.exp_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by ring)

set_option diagnostics true in
set_option maxHeartbeats 1000000 in
lemma signedDiagonalPartial_L2_bound (β : ℝ) (a : ι → ℝ)
    (hm : ∀ i, 0 < 1+2*β*a i) (ha : Summable (fun i => (a i)^2))
    (f : ι → ℕ) (hf : Function.Injective f) (s : Finset ι) :
    MemLp (diagonalPartialExp β a f s) 2 IsonormalProcess.iidStdGaussian ∧
    eLpNorm (diagonalPartialExp β a f s) 2 IsonormalProcess.iidStdGaussian ≤
      ENNReal.ofReal (Real.exp ((∑' i, |DGRHS.Kernel.regularizedLog (2*β*a i)|)/4)) := by
  have hsq : Summable (fun i => (2*β*a i)^2) := by
    have heq : (fun i => (2*β*a i)^2) = (fun i => (2*β)^2*(a i)^2) := by
      funext i
      ring
    rw [heq]
    exact ha.mul_left ((2*β)^2)
  have hlogs : Summable (fun i => |DGRHS.Kernel.regularizedLog (2*β*a i)|) := by
    simpa only [Real.norm_eq_abs] using (DGRHS.Kernel.summable_regularizedLog hsq).norm
  have hint := signedDiagonalPartial_exponential (2*β) a hm f hf s
  have hF : MemLp (diagonalPartialExp β a f s) 2 IsonormalProcess.iidStdGaussian := by
    apply (memLp_two_iff_integrable_sq
      (show AEStronglyMeasurable (diagonalPartialExp β a f s) IsonormalProcess.iidStdGaussian from
        (show Continuous (diagonalPartialExp β a f s) from by
          unfold diagonalPartialExp; fun_prop).aestronglyMeasurable)).mpr
    simpa only [signedDiagonalPartial_sq] using hint.1
  refine ⟨hF, ?_⟩
  have hsum : -(∑ i ∈ s, DGRHS.Kernel.regularizedLog (2*β*a i)) ≤
      ∑' i, |DGRHS.Kernel.regularizedLog (2*β*a i)| := by
    calc
      _ ≤ ∑ i ∈ s, |DGRHS.Kernel.regularizedLog (2*β*a i)| := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum (fun i _ => neg_le_abs _)
      _ ≤ _ := hlogs.sum_le_tsum s (fun i _ => abs_nonneg _)
  have hbound : ‖hF.toLp (diagonalPartialExp β a f s)‖ ≤
      Real.exp ((∑' i, |DGRHS.Kernel.regularizedLog (2*β*a i)|)/4) := by
    have hv := DGRHS.Kernel.norm_toLp_sq hF
    simp_rw [signedDiagonalPartial_sq] at hv
    rw [hint.2] at hv
    have hex := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hsum (by norm_num : (0:ℝ)≤2))
    have he : (Real.exp ((∑' i, |DGRHS.Kernel.regularizedLog (2*β*a i)|)/4))^2 =
        Real.exp ((∑' i, |DGRHS.Kernel.regularizedLog (2*β*a i)|)/2) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    nlinarith [norm_nonneg (hF.toLp (diagonalPartialExp β a f s)), Real.exp_pos
      ((∑' i, |DGRHS.Kernel.regularizedLog (2*β*a i)|)/4)]
  rw [← Lp.enorm_toLp hF, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hbound

set_option diagnostics true in
set_option maxHeartbeats 1000000 in
/-- Signed square-summable transform with actual L2 uniform integrability and
an explicit doubled margin. Positivity is required of the factors, not of a. -/
theorem integral_exp_signed_centeredGaussianChaos_doubled_margin
    (β : ℝ) (a : ι → ℝ) (hm : ∀ i, 0 < 1+2*β*a i)
    (ha : Summable (fun i => (a i)^2)) (f : ι → ℕ) (hf : Function.Injective f) :
    Integrable (fun ω => Real.exp (-(β/2)*centeredGaussianChaos a f ω))
      IsonormalProcess.iidStdGaussian ∧
    (∫ ω, Real.exp (-(β/2)*centeredGaussianChaos a f ω)
      ∂IsonormalProcess.iidStdGaussian) =
      (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*a i)))⁻¹ := by
  have hm1 : ∀ i, 0 < 1+β*a i := by intro i; have := hm i; linarith
  obtain ⟨ss,hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  let F := fun n => diagonalPartialExp β a f (ss n)
  let G := fun ω => Real.exp (-(β/2)*centeredGaussianChaos a f ω)
  have hFG : TendstoInMeasure IsonormalProcess.iidStdGaussian F atTop G := by
    have ht := tendstoInMeasure_continuous_real_comp
      (μ := IsonormalProcess.iidStdGaussian)
      (F := fun n (ω : ℕ → ℝ) => ∑ i ∈ ss n, a i*((ω (f i))^2-1))
      (G := (centeredGaussianChaos a f : (ℕ → ℝ) → ℝ))
      (by intro n; exact (show Continuous (fun ω : ℕ → ℝ =>
        ∑ i ∈ ss n, a i*((ω (f i))^2-1)) from by fun_prop).aestronglyMeasurable)
      (tendstoInMeasure_centeredGaussianChaos a f hf ha hss)
      (fun z => Real.exp (-(β/2)*z)) (by fun_prop)
    apply ht.congr_left
    intro n
    filter_upwards [] with ω
    unfold F diagonalPartialExp
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  let C : ℝ≥0 := ⟨Real.exp ((∑' i, |DGRHS.Kernel.regularizedLog (2*β*a i)|)/4), (Real.exp_pos _).le⟩
  obtain ⟨hG,hint⟩ := tendsto_integral_of_L2_bound_and_inMeasure F G
    (fun n => (signedDiagonalPartial_L2_bound β a hm ha f hf (ss n)).1) C
    (fun n => by
      have hCeq : ENNReal.ofReal (Real.exp ((∑' i, |DGRHS.Kernel.regularizedLog (2*β*a i)|)/4)) = (C : ℝ≥0∞) :=
        ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le
      rw [← hCeq]
      exact (signedDiagonalPartial_L2_bound β a hm ha f hf (ss n)).2) hFG
  have hβsq : Summable (fun i => (β*a i)^2) := by
    simpa only [mul_pow] using ha.mul_left (β^2)
  have hl := ((DGRHS.Kernel.summable_regularizedLog hβsq).hasSum.comp hss).neg.div_const 2
  have hv := Real.continuous_exp.continuousAt.tendsto.comp hl
  have hvals : ∀ n, (∫ ω, F n ω ∂IsonormalProcess.iidStdGaussian) =
      Real.exp (-(∑ i ∈ ss n, DGRHS.Kernel.regularizedLog (β*a i))/2) :=
    fun n => (signedDiagonalPartial_exponential β a hm1 f hf (ss n)).2
  have he := tendsto_nhds_unique hint (hv.congr (fun n => (hvals n).symm))
  refine ⟨hG, ?_⟩
  rw [he, DGRHS.Kernel.regularizedDet_eq_exp hβsq hm1]
  have hr : Real.sqrt (Real.exp (∑' i, DGRHS.Kernel.regularizedLog (β*a i))) =
      Real.exp ((∑' i, DGRHS.Kernel.regularizedLog (β*a i))/2) := by
    calc
      _ = Real.exp (Real.log (Real.sqrt
          (Real.exp (∑' i, DGRHS.Kernel.regularizedLog (β*a i))))) :=
        (Real.exp_log (Real.sqrt_pos.mpr (Real.exp_pos _))).symm
      _ = _ := by rw [Real.log_sqrt (Real.exp_pos _).le, Real.log_exp]
  rw [hr, ← Real.exp_neg]
  congr 1
  ring

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.signedFiniteCentered_exponential
#print axioms DGRHS.Gaussian.signedDiagonalPartial_L2_bound
#print axioms DGRHS.Gaussian.integral_exp_signed_centeredGaussianChaos_doubled_margin
