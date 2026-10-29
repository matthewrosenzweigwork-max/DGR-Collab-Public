/- UNCHECKED outside frozen proof. Qualitative signed HS chaos transform at
its single strict factor margin. The common power above one, finite Gaussian
moments, both UI components, integrability and actual determinant limit are
derived. The attractive quantitative rate's separate doubled margin remains.
Independent mathematical route: signed-chaos-weak-margin-review. -/
import DGRHS.Gaussian.SignedChaosLaplace
import DGRHS.Gaussian.SpectralPowerMargin
import DGRHS.Gaussian.PowerIntegrability
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace DGRHS.Gaussian
variable {ι : Type*} [Countable ι]

lemma norm_diagonalPartialExp_rpow (β p : ℝ) (a : ι → ℝ)
    (f : ι → ℕ) (s : Finset ι) (ω : ℕ → ℝ) :
    ‖diagonalPartialExp β a f s ω‖ ^ p = diagonalPartialExp (p*β) a f s ω := by
  unfold diagonalPartialExp
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- This is a genuine finite Gaussian moment, not a totalized integral or an
assumed norm bound. Its finite exponent and positivity are explicit. -/
lemma signedDiagonalPartial_Lq_exact (β p : ℝ) (hp : 0 < p) (a : ι → ℝ)
    (hm : ∀ i, 0 < 1+p*β*a i) (f : ι → ℕ) (hf : Function.Injective f)
    (s : Finset ι) :
    MemLp (diagonalPartialExp β a f s) (ENNReal.ofReal p)
        IsonormalProcess.iidStdGaussian ∧
    eLpNorm (diagonalPartialExp β a f s) (ENNReal.ofReal p)
        IsonormalProcess.iidStdGaussian =
      ENNReal.ofReal (Real.exp
        (-(∑ i ∈ s, DGRHS.Kernel.regularizedLog (p*β*a i))/(2*p))) := by
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hmeas : AEStronglyMeasurable (diagonalPartialExp β a f s)
      IsonormalProcess.iidStdGaussian :=
    (show Continuous (diagonalPartialExp β a f s) from by
      unfold diagonalPartialExp; fun_prop).aestronglyMeasurable
  have hi := signedDiagonalPartial_exponential (p*β) a hm f hf s
  have hlin : (∫⁻ ω, ‖diagonalPartialExp β a f s ω‖ₑ ^ p
      ∂IsonormalProcess.iidStdGaussian) =
      ENNReal.ofReal (Real.exp
        (-(∑ i ∈ s, DGRHS.Kernel.regularizedLog (p*β*a i))/2)) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (diagonalPartialExp (p*β) a f s ω)
          ∂IsonormalProcess.iidStdGaussian := by
        apply lintegral_congr_ae
        filter_upwards [] with ω
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
          norm_diagonalPartialExp_rpow]
      _ = ENNReal.ofReal (∫ ω, diagonalPartialExp (p*β) a f s ω
          ∂IsonormalProcess.iidStdGaussian) :=
        (ofReal_integral_eq_lintegral_ofReal hi.1
          (Eventually.of_forall (fun ω => (Real.exp_pos _).le))).symm
      _ = _ := by rw [hi.2]
  have he : eLpNorm (diagonalPartialExp β a f s) (ENNReal.ofReal p)
      IsonormalProcess.iidStdGaussian =
      ENNReal.ofReal (Real.exp
        (-(∑ i ∈ s, DGRHS.Kernel.regularizedLog (p*β*a i))/(2*p))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hmeas,
      ENNReal.toReal_ofReal hp.le, hlin, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
      ← Real.exp_mul]
    congr 2
    field_simp
  refine ⟨?_, he⟩
  unfold MemLp
  rw [he]
  exact ENNReal.ofReal_lt_top

lemma signedDiagonalPartial_Lq_bound (β p : ℝ) (hp : 0 < p) (a : ι → ℝ)
    (hm : ∀ i, 0 < 1+p*β*a i) (ha : Summable (fun i => (a i)^2))
    (f : ι → ℕ) (hf : Function.Injective f) (s : Finset ι) :
    MemLp (diagonalPartialExp β a f s) (ENNReal.ofReal p)
        IsonormalProcess.iidStdGaussian ∧
    eLpNorm (diagonalPartialExp β a f s) (ENNReal.ofReal p)
        IsonormalProcess.iidStdGaussian ≤
      ENNReal.ofReal (Real.exp
        ((∑' i, |DGRHS.Kernel.regularizedLog (p*β*a i)|)/(2*p))) := by
  have hi := signedDiagonalPartial_Lq_exact β p hp a hm f hf s
  have hsquare : Summable (fun i => (p*β*a i)^2) := by
    have heq : (fun i => (p*β*a i)^2) = (fun i => (p*β)^2*(a i)^2) := by
      funext i
      ring
    rw [heq]
    exact ha.mul_left ((p*β)^2)
  have hlogs : Summable (fun i => |DGRHS.Kernel.regularizedLog (p*β*a i)|) := by
    simpa only [Real.norm_eq_abs] using
      (DGRHS.Kernel.summable_regularizedLog hsquare).norm
  have hsum : -(∑ i ∈ s, DGRHS.Kernel.regularizedLog (p*β*a i)) ≤
      ∑' i, |DGRHS.Kernel.regularizedLog (p*β*a i)| := by
    calc
      _ ≤ ∑ i ∈ s, |DGRHS.Kernel.regularizedLog (p*β*a i)| := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum (fun i _ => neg_le_abs _)
      _ ≤ _ := hlogs.sum_le_tsum s (fun i _ => abs_nonneg _)
  refine ⟨hi.1, ?_⟩
  rw [hi.2]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right hsum (by positivity)))

set_option diagnostics true in
set_option maxHeartbeats 1000000 in
/-- Original qualitative threshold. There is no assumed UI, fourth spatial
moment, trace sum, sign or diagonal-law premise. -/
theorem integral_exp_signed_centeredGaussianChaos_weak_margin
    (β : ℝ) (a : ι → ℝ) (hm : ∀ i, 0 < 1+β*a i)
    (ha : Summable (fun i => (a i)^2)) (f : ι → ℕ) (hf : Function.Injective f) :
    Integrable (fun ω => Real.exp (-(β/2)*centeredGaussianChaos a f ω))
      IsonormalProcess.iidStdGaussian ∧
    (∫ ω, Real.exp (-(β/2)*centeredGaussianChaos a f ω)
      ∂IsonormalProcess.iidStdGaussian) =
      (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*a i)))⁻¹ := by
  obtain ⟨p,hp,hphalf,hpm⟩ := exists_spectral_power_above_one β a ha hm
  have hp0 : 0 < p := lt_trans zero_lt_one hp
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
  let C : ℝ≥0 := ⟨Real.exp
    ((∑' i, |DGRHS.Kernel.regularizedLog (p*β*a i)|)/(2*p)), (Real.exp_pos _).le⟩
  have hq : 1 < ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_lt_ofReal_iff hp0).mpr hp
  obtain ⟨hG,hint⟩ := tendsto_integral_of_Lq_bound_and_inMeasure F G
    (ENNReal.ofReal p) hq ENNReal.ofReal_ne_top
    (fun n => (signedDiagonalPartial_Lq_bound β p hp0 a hpm ha f hf (ss n)).1) C
    (fun n => by
      have hCeq : ENNReal.ofReal (Real.exp
          ((∑' i, |DGRHS.Kernel.regularizedLog (p*β*a i)|)/(2*p))) = (C : ℝ≥0∞) :=
        ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le
      rw [← hCeq]
      exact (signedDiagonalPartial_Lq_bound β p hp0 a hpm ha f hf (ss n)).2) hFG
  have hβsq : Summable (fun i => (β*a i)^2) := by
    simpa only [mul_pow] using ha.mul_left (β^2)
  have hl := ((DGRHS.Kernel.summable_regularizedLog hβsq).hasSum.comp hss).neg.div_const 2
  have hv := Real.continuous_exp.continuousAt.tendsto.comp hl
  have hvals : ∀ n, (∫ ω, F n ω ∂IsonormalProcess.iidStdGaussian) =
      Real.exp (-(∑ i ∈ ss n, DGRHS.Kernel.regularizedLog (β*a i))/2) :=
    fun n => (signedDiagonalPartial_exponential β a hm f hf (ss n)).2
  have he := tendsto_nhds_unique hint (hv.congr (fun n => (hvals n).symm))
  refine ⟨hG, ?_⟩
  rw [he, DGRHS.Kernel.regularizedDet_eq_exp hβsq hm]
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
#print axioms DGRHS.Gaussian.signedDiagonalPartial_Lq_exact
#print axioms DGRHS.Gaussian.signedDiagonalPartial_Lq_bound
#print axioms DGRHS.Gaussian.integral_exp_signed_centeredGaussianChaos_weak_margin
#check DGRHS.Gaussian.integral_exp_signed_centeredGaussianChaos_weak_margin
