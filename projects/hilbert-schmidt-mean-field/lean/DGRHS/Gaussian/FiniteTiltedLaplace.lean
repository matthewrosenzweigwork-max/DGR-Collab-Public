/- Development draft. Genuine selected-coordinate Gaussian linear/quadratic
products, including zero spectral coefficients. This supports the original
weak-margin infinite-Hilbert linear tilt; no desired transform is assumed. -/
import DGRHS.Gaussian.ScalarTiltedLaplace
import DGRHS.Gaussian.WeakMarginChaosLaplace
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace DGRHS.Gaussian

lemma finiteCenteredTilt_exponential {j : Type*} [Fintype j]
    (β : ℝ) (a t : j → ℝ) (hm : ∀ i, 0 < 1+β*a i) :
    Integrable (fun z : j → ℝ => Real.exp
      (∑ i, (t i*z i+(β*a i/2)*(1-(z i)^2)))) (finiteStandardGaussian j) ∧
    (∫ z : j → ℝ, Real.exp (∑ i, (t i*z i+(β*a i/2)*(1-(z i)^2)))
      ∂finiteStandardGaussian j) =
      Real.exp (-(∑ i, DGRHS.Kernel.regularizedLog (β*a i))/2 +
        (∑ i, (t i)^2/(1+β*a i))/2) := by
  classical
  have hfac : ∀ i, Real.exp (β*a i/2+(t i)^2/(2*(1+β*a i))) *
      (Real.sqrt (1+β*a i))⁻¹ =
      Real.exp (-DGRHS.Kernel.regularizedLog (β*a i)/2+(t i)^2/(2*(1+β*a i))) := by
    intro i
    rw [Real.exp_add]
    calc
      _ = (Real.exp (β*a i/2)*(Real.sqrt (1+β*a i))⁻¹) *
          Real.exp ((t i)^2/(2*(1+β*a i))) := by ring
      _ = _ := by rw [signedCenteredFactor_eq_exp _ (hm i), ← Real.exp_add]
  constructor
  · simp_rw [Real.exp_sum]
    exact Integrable.fintype_prod
      (fun i => (standardGaussian_centered_tilted_quadratic β (a i) (t i) (hm i)).1)
  · simp_rw [Real.exp_sum]
    rw [finiteStandardGaussian, integral_fintype_prod_eq_prod
      (fun i (x : ℝ) => Real.exp (t i*x+(β*a i/2)*(1-x^2)))]
    rw [Finset.prod_congr rfl (fun i _ =>
      (standardGaussian_centered_tilted_quadratic β (a i) (t i) (hm i)).2),
      Finset.prod_congr rfl (fun i _ => hfac i), ← Real.exp_sum]
    congr 1
    simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun i _ => by field_simp [(hm i).ne'] <;> ring)

variable {ι : Type*} [Countable ι]
def tiltedDiagonalPartialExp (β : ℝ) (a t : ι → ℝ)
    (f : ι → ℕ) (s : Finset ι) (ω : ℕ → ℝ) : ℝ :=
  Real.exp (∑ i ∈ s, (t i*ω (f i)+(β*a i/2)*(1-(ω (f i))^2)))

lemma tiltedDiagonalPartial_exponential (β : ℝ) (a t : ι → ℝ)
    (hm : ∀ i, 0 < 1+β*a i) (f : ι → ℕ) (hf : Function.Injective f) (s : Finset ι) :
    Integrable (tiltedDiagonalPartialExp β a t f s) IsonormalProcess.iidStdGaussian ∧
    (∫ ω, tiltedDiagonalPartialExp β a t f s ω ∂IsonormalProcess.iidStdGaussian) =
      Real.exp (-(∑ i ∈ s, DGRHS.Kernel.regularizedLog (β*a i))/2+
        (∑ i ∈ s, (t i)^2/(1+β*a i))/2) := by
  let g := fun ω (i : s) => IsonormalProcess.coord (f i) ω
  have hg : Measurable g := Measurable.of_eval
    (fun i : s => IsonormalProcess.measurable_coord (f i))
  have hp : MeasurePreserving g IsonormalProcess.iidStdGaussian (finiteStandardGaussian s) :=
    ⟨hg, selectedGaussian_map f hf s⟩
  let F := fun z : s → ℝ => Real.exp (∑ i : s, (t i*z i+(β*a i/2)*(1-(z i)^2)))
  have hi := finiteCenteredTilt_exponential β (fun i : s => a i) (fun i : s => t i) (fun i => hm i)
  have he : F ∘ g = tiltedDiagonalPartialExp β a t f s := by
    funext ω
    change Real.exp (∑ i : s, (t i*ω (f i)+(β*a i/2)*(1-(ω (f i))^2))) = _
    congr 1
    exact Finset.sum_coe_sort s (fun i : ι => t i*ω (f i)+(β*a i/2)*(1-(ω (f i))^2))
  refine ⟨by rw [← he]; exact hp.integrable_comp_of_integrable hi.1, ?_⟩
  have hmap := integral_map (μ := IsonormalProcess.iidStdGaussian) (φ := g)
    (f := F) hg.aemeasurable (by rw [hp.map_eq]; exact hi.1.aestronglyMeasurable)
  rw [hp.map_eq] at hmap
  rw [← he]
  calc
    _ = ∫ z, F z ∂finiteStandardGaussian s := by
      simpa only [Function.comp_apply] using hmap.symm
    _ = _ := by
      rw [hi.2, Finset.sum_coe_sort s (fun i => DGRHS.Kernel.regularizedLog (β*a i)),
        Finset.sum_coe_sort s (fun i => (t i)^2/(1+β*a i))]

lemma norm_tiltedDiagonalPartial_rpow (β p : ℝ) (a t : ι → ℝ)
    (f : ι → ℕ) (s : Finset ι) (ω : ℕ → ℝ) :
    ‖tiltedDiagonalPartialExp β a t f s ω‖ ^ p =
      tiltedDiagonalPartialExp (p*β) a (fun i => p*t i) f s ω := by
  unfold tiltedDiagonalPartialExp
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 1
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma tiltedDiagonalPartial_Lq_exact (β p : ℝ) (hp : 0 < p) (a t : ι → ℝ)
    (hm : ∀ i, 0 < 1+p*β*a i) (f : ι → ℕ) (hf : Function.Injective f)
    (s : Finset ι) :
    MemLp (tiltedDiagonalPartialExp β a t f s) (ENNReal.ofReal p) IsonormalProcess.iidStdGaussian ∧
    eLpNorm (tiltedDiagonalPartialExp β a t f s) (ENNReal.ofReal p) IsonormalProcess.iidStdGaussian =
      ENNReal.ofReal (Real.exp ((-(∑ i ∈ s, DGRHS.Kernel.regularizedLog (p*β*a i))+
        (∑ i ∈ s, (p*t i)^2/(1+p*β*a i)))/(2*p))) := by
  have hq0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
  have hqt : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hmeas : AEStronglyMeasurable (tiltedDiagonalPartialExp β a t f s)
      IsonormalProcess.iidStdGaussian :=
    (show Continuous (tiltedDiagonalPartialExp β a t f s) from by
      unfold tiltedDiagonalPartialExp; fun_prop).aestronglyMeasurable
  have hi := tiltedDiagonalPartial_exponential (p*β) a (fun i => p*t i) hm f hf s
  have hlin : (∫⁻ ω, ‖tiltedDiagonalPartialExp β a t f s ω‖ₑ ^ p
      ∂IsonormalProcess.iidStdGaussian) =
      ENNReal.ofReal (Real.exp (-(∑ i ∈ s, DGRHS.Kernel.regularizedLog (p*β*a i))/2+
        (∑ i ∈ s, (p*t i)^2/(1+p*β*a i))/2)) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (tiltedDiagonalPartialExp (p*β) a (fun i => p*t i) f s ω)
          ∂IsonormalProcess.iidStdGaussian := by
        apply lintegral_congr_ae
        filter_upwards [] with ω
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le,
          norm_tiltedDiagonalPartial_rpow]
      _ = ENNReal.ofReal (∫ ω, tiltedDiagonalPartialExp (p*β) a (fun i => p*t i) f s ω
          ∂IsonormalProcess.iidStdGaussian) :=
        (ofReal_integral_eq_lintegral_ofReal hi.1
          (Eventually.of_forall (fun ω => (Real.exp_pos _).le))).symm
      _ = _ := by rw [hi.2]
  have he : eLpNorm (tiltedDiagonalPartialExp β a t f s) (ENNReal.ofReal p)
      IsonormalProcess.iidStdGaussian =
      ENNReal.ofReal (Real.exp ((-(∑ i ∈ s, DGRHS.Kernel.regularizedLog (p*β*a i))+
        (∑ i ∈ s, (p*t i)^2/(1+p*β*a i)))/(2*p))) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqt hmeas,
      ENNReal.toReal_ofReal hp.le, hlin, ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
      ← Real.exp_mul]
    congr 2
    field_simp
    <;> ring
  refine ⟨?_, he⟩
  unfold MemLp
  rw [he]
  exact ENNReal.ofReal_lt_top

end DGRHS.Gaussian
#check @DGRHS.Gaussian.finiteCenteredTilt_exponential
#print axioms DGRHS.Gaussian.finiteCenteredTilt_exponential
#check @DGRHS.Gaussian.tiltedDiagonalPartial_exponential
#print axioms DGRHS.Gaussian.tiltedDiagonalPartial_exponential
#check @DGRHS.Gaussian.tiltedDiagonalPartial_Lq_exact
#print axioms DGRHS.Gaussian.tiltedDiagonalPartial_Lq_exact
