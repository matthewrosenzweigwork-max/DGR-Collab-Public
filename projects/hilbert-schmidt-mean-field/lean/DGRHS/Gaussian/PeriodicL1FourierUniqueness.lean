import DGRHS.Gaussian.PeriodicGaussianHeatFourier
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! L1 Fourier uniqueness proved from the native uniform density of torus
characters. Continuous tests determine an integrable function: closed-set
indicators are obtained by the explicit dominated approximation
exp(-n * distance-to-the-set). No L2 assumption is introduced. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic
universe u

lemma integrable_ae_zero_of_continuous_tests {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (μ : Measure X) (f : X → ℂ) (hf : Integrable f μ)
    (h : ∀ g : C(X,ℂ),(∫ x,g x*f x ∂μ)=0) : f=ᵐ[μ]0 := by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf
  intro s hs
  by_cases hse : s.Nonempty
  · let g : ℕ → X → ℝ := fun n x => Real.exp (-(infDist x s)*(n:ℝ))
    have hgcont (n : ℕ) : Continuous (g n) := by
      exact Real.continuous_exp.comp (((continuous_infDist_pt s).neg).mul continuous_const)
    have hgnorm (n : ℕ) (x : X) : ‖g n x‖≤1 := by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr infDist_nonneg) (Nat.cast_nonneg n))
    have hlim (x : X) : Tendsto (fun n => g n x) atTop (𝓝 (s.indicator (fun _ => (1:ℝ)) x)) := by
      by_cases hx : x∈s
      · simp only [g,infDist_zero_of_mem hx,neg_zero,zero_mul,Real.exp_zero,indicator_of_mem hx]
        exact tendsto_const_nhds
      · rw [indicator_of_notMem hx]
        have hd : 0 < infDist x s := (hs.notMem_iff_infDist_pos hse).mp hx
        exact Real.tendsto_exp_atBot.comp
          (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos hd))
    have hint : Tendsto (fun n => ∫ x,(g n x:ℂ)*f x ∂μ) atTop
        (𝓝 (∫ x,s.indicator f x ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
      · intro n
        exact (Complex.continuous_ofReal.comp (hgcont n)).aestronglyMeasurable.mul hf.aestronglyMeasurable
      · exact hf.norm
      · intro n
        exact Eventually.of_forall (fun x => by
          rw [norm_mul,Complex.norm_real]
          exact mul_le_of_le_one_left (norm_nonneg _) (hgnorm n x))
      · exact Eventually.of_forall (fun x => by
          have hh := (Complex.continuous_ofReal.continuousAt.tendsto.comp (hlim x)).mul_const (f x)
          by_cases hx : x∈s
          · simpa only [indicator_of_mem hx,Complex.ofReal_one,one_mul,Function.comp_apply] using hh
          · simpa only [indicator_of_notMem hx,Complex.ofReal_zero,zero_mul,Function.comp_apply] using hh)
    have hz (n : ℕ) : (∫ x,(g n x:ℂ)*f x ∂μ)=0 :=
      h ⟨fun x => (g n x:ℂ),Complex.continuous_ofReal.comp (hgcont n)⟩
    rw [integral_indicator hs.measurableSet] at hint
    simp only [hz,tendsto_const_nhds_iff] at hint
    exact hint.symm
  · rw [not_nonempty_iff_eq_empty.mp hse]
    simp

variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicContinuousTest_integrable {f : PeriodicTorus ι → ℂ}
    (hf : Integrable f (periodicHaar ι)) (g : C(PeriodicTorus ι,ℂ)) :
    Integrable (fun x => g x*f x) (periodicHaar ι) :=
  hf.bdd_mul g.continuous.aestronglyMeasurable
    (Eventually.of_forall (fun x => g.norm_coe_le_norm x))

def periodicContinuousTestLinear (f : PeriodicTorus ι → ℂ)
    (hf : Integrable f (periodicHaar ι)) : C(PeriodicTorus ι,ℂ) →ₗ[ℂ] ℂ where
  toFun g := ∫ x,g x*f x ∂periodicHaar ι
  map_add' g h := by
    simp only [ContinuousMap.add_apply,add_mul]
    exact integral_add (periodicContinuousTest_integrable hf g) (periodicContinuousTest_integrable hf h)
  map_smul' c g := by
    simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul,RingHom.id_apply]

lemma periodicContinuousTestLinear_norm (f : PeriodicTorus ι → ℂ)
    (hf : Integrable f (periodicHaar ι)) (g : C(PeriodicTorus ι,ℂ)) :
    ‖periodicContinuousTestLinear f hf g‖≤(∫ x,‖f x‖ ∂periodicHaar ι)*‖g‖ := by
  calc
    _ ≤ ∫ x,‖g x*f x‖ ∂periodicHaar ι := norm_integral_le_integral_norm _
    _ ≤ ∫ x,‖g‖*‖f x‖ ∂periodicHaar ι :=
      integral_mono_ae (periodicContinuousTest_integrable hf g).norm (hf.norm.const_mul ‖g‖)
        (by
          filter_upwards [] with x
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (g.norm_coe_le_norm x) (norm_nonneg _))
    _ = _ := by rw [integral_const_mul,mul_comm]

def periodicContinuousTestCLM (f : PeriodicTorus ι → ℂ)
    (hf : Integrable f (periodicHaar ι)) : C(PeriodicTorus ι,ℂ) →L[ℂ] ℂ :=
  (periodicContinuousTestLinear f hf).mkContinuous (∫ x,‖f x‖ ∂periodicHaar ι)
    (periodicContinuousTestLinear_norm f hf)

lemma periodicL1_fourier_zero (f : PeriodicTorus ι → ℂ)
    (hf : Integrable f (periodicHaar ι))
    (hc : ∀ k,UnitAddTorus.mFourierCoeff f k=0) : f=ᵐ[periodicHaar ι]0 := by
  apply integrable_ae_zero_of_continuous_tests _ f hf
  let L := periodicContinuousTestCLM f hf
  have hspan : Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := ι))) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro g ⟨k,rfl⟩
    change (∫ x,UnitAddTorus.mFourier k x*f x ∂periodicHaar ι)=0
    simpa only [periodic_mFourierCoeff_eq_integral,neg_neg] using hc (-k)
  have hall : (⊤ : Submodule ℂ C(PeriodicTorus ι,ℂ))≤L.ker := by
    rw [← UnitAddTorus.span_mFourier_closure_eq_top]
    exact Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  intro g
  exact hall (Submodule.mem_top)

/-- Actual Haar-L1 uniqueness, without any L2 hypothesis. -/
theorem periodicL1_fourier_unique (f g : PeriodicTorus ι → ℂ)
    (hf : Integrable f (periodicHaar ι)) (hg : Integrable g (periodicHaar ι))
    (hc : ∀ k,UnitAddTorus.mFourierCoeff f k=UnitAddTorus.mFourierCoeff g k) :
    f=ᵐ[periodicHaar ι]g := by
  have hz := periodicL1_fourier_zero (fun x => f x-g x) (hf.sub hg) (fun k => by
    simp only [periodic_mFourierCoeff_eq_integral,mul_sub]
    rw [integral_sub (periodicContinuousTest_integrable hf (UnitAddTorus.mFourier (-k)))
      (periodicContinuousTest_integrable hg (UnitAddTorus.mFourier (-k)))]
    exact sub_eq_zero.mpr (hc k))
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

end DGRHS.Periodic
#print axioms DGRHS.Periodic.integrable_ae_zero_of_continuous_tests
#print axioms DGRHS.Periodic.periodicL1_fourier_zero
#print axioms DGRHS.Periodic.periodicL1_fourier_unique
#check @DGRHS.Periodic.periodicL1_fourier_unique
