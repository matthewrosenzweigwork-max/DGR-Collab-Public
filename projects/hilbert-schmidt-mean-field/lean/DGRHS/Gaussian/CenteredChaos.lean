/- Unchecked preparation outside root proof. Genuine square-summable centered
Gaussian second chaos; finite trace is not assumed. -/
import DGRHS.Gaussian.FeatureProductL2
import DGRHS.Gaussian.Imported.GaussianMoments
import Mathlib.Probability.Independence.Integration
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators InnerProductSpace Topology
namespace DGRHS.Gaussian

lemma memLp_centeredSquare_stdGaussian :
    MemLp (fun x : ℝ ↦ x^2-1) 2 (gaussianReal 0 1) := by
  have h4 : MemLp (id : ℝ → ℝ) 4 (gaussianReal 0 1) :=
    memLp_id_gaussianReal' 4 (by norm_num)
  have hi4 : Integrable (fun x : ℝ ↦ x^4) (gaussianReal 0 1) := by
    simpa only [id_eq,Real.norm_eq_abs,show (4:ℕ)=2*2 by rfl,pow_mul,sq_abs]
      using h4.integrable_norm_pow (by decide : (4:ℕ) ≠ 0)
  have hs : MemLp (fun x : ℝ ↦ x^2) 2 (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 (by simpa only [← pow_mul] using hi4)
  exact hs.sub (memLp_const (1 : ℝ))

lemma integral_centeredSquare_stdGaussian :
    (∫ x : ℝ, x^2-1 ∂gaussianReal 0 1) = 0 := by
  have hs : Integrable (fun x : ℝ ↦ x^2) (gaussianReal 0 1) := by
    simpa only [id_eq] using
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).integrable_sq
  rw [integral_sub hs (integrable_const 1),
    StatLean.MultipleTesting.integral_sq_stdGaussian]
  simp

lemma memLp_centeredSquare_coord (n : ℕ) :
    MemLp (fun ω : ℕ → ℝ ↦ (ω n)^2-1) 2 IsonormalProcess.iidStdGaussian :=
  memLp_centeredSquare_stdGaussian.comp_measurePreserving
    (IsonormalProcess.measurePreserving_coord n)

def centeredSquareLp (n : ℕ) : Lp ℝ 2 IsonormalProcess.iidStdGaussian :=
  (memLp_centeredSquare_coord n).toLp (fun ω ↦ (ω n)^2-1)

lemma coeFn_centeredSquareLp (n : ℕ) :
    (centeredSquareLp n : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
      (fun ω ↦ (ω n)^2-1) := (memLp_centeredSquare_coord n).coeFn_toLp

lemma integral_centeredSquare_coord (n : ℕ) :
    (∫ ω : ℕ → ℝ, (ω n)^2-1 ∂IsonormalProcess.iidStdGaussian) = 0 := by
  calc
    _ = ∫ x : ℝ, x^2-1 ∂IsonormalProcess.iidStdGaussian.map (IsonormalProcess.coord n) :=
      (integral_map (IsonormalProcess.measurable_coord n).aemeasurable (by fun_prop)).symm
    _ = ∫ x : ℝ, x^2-1 ∂gaussianReal 0 1 := by rw [IsonormalProcess.map_coord]
    _ = 0 := integral_centeredSquare_stdGaussian

lemma norm_centeredSquareLp_sq (n : ℕ) : ‖centeredSquareLp n‖^2 = 2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  calc
    _ = ∫ ω : ℕ → ℝ, ((ω n)^2-1)^2 ∂IsonormalProcess.iidStdGaussian := by
      apply integral_congr_ae
      filter_upwards [coeFn_centeredSquareLp n] with ω hω
      rw [hω]
      simp only [RCLike.inner_apply',conj_trivial,← sq]
    _ = ∫ x : ℝ, (x^2-1)^2
        ∂IsonormalProcess.iidStdGaussian.map (IsonormalProcess.coord n) :=
      (integral_map (μ := IsonormalProcess.iidStdGaussian)
        (IsonormalProcess.measurable_coord n).aemeasurable
        (show AEStronglyMeasurable (fun x : ℝ ↦ (x^2-1)^2)
          (IsonormalProcess.iidStdGaussian.map (IsonormalProcess.coord n)) from by fun_prop)).symm
    _ = ∫ x : ℝ, (x^2-1)^2 ∂gaussianReal 0 1 := by rw [IsonormalProcess.map_coord]
    _ = 2 := StatLean.MultipleTesting.variance_sq_stdGaussian

lemma pairwise_inner_centeredSquareLp :
    Pairwise (fun m n ↦ inner ℝ (centeredSquareLp m) (centeredSquareLp n) = 0) := by
  intro m n hmn
  rw [L2.inner_def]
  calc
    _ = ∫ ω : ℕ → ℝ, ((ω n)^2-1)*((ω m)^2-1)
        ∂IsonormalProcess.iidStdGaussian := by
      apply integral_congr_ae
      filter_upwards [coeFn_centeredSquareLp m,coeFn_centeredSquareLp n] with ω hm hn
      rw [hm,hn]
      rfl
    _ = (∫ ω : ℕ → ℝ, (ω n)^2-1 ∂IsonormalProcess.iidStdGaussian) *
        (∫ ω : ℕ → ℝ, (ω m)^2-1 ∂IsonormalProcess.iidStdGaussian) := by
      exact ((IsonormalProcess.iIndepFun_coord.indepFun hmn.symm).comp
        (show Measurable (fun x : ℝ ↦ x^2-1) from by fun_prop)
        (show Measurable (fun x : ℝ ↦ x^2-1) from by fun_prop)).integral_mul_eq_mul_integral
          (memLp_centeredSquare_coord n).aestronglyMeasurable
          (memLp_centeredSquare_coord m).aestronglyMeasurable
    _ = 0 := by rw [integral_centeredSquare_coord,zero_mul]

variable {ι : Type*}
def centeredChaosTerm (a : ι → ℝ) (f : ι → ℕ) (i : ι) :
    Lp ℝ 2 IsonormalProcess.iidStdGaussian := a i • centeredSquareLp (f i)

lemma norm_centeredChaosTerm_sq (a : ι → ℝ) (f : ι → ℕ) (i : ι) :
    ‖centeredChaosTerm a f i‖^2 = 2*(a i)^2 := by
  rw [centeredChaosTerm,norm_smul,mul_pow,norm_centeredSquareLp_sq]
  simp only [Real.norm_eq_abs,sq_abs]
  ring

lemma pairwise_inner_centeredChaosTerm (a : ι → ℝ) (f : ι → ℕ)
    (hf : Function.Injective f) :
    Pairwise (fun i j ↦ inner ℝ (centeredChaosTerm a f i) (centeredChaosTerm a f j) = 0) := by
  intro i j hij
  rw [centeredChaosTerm,centeredChaosTerm,inner_smul_left,inner_smul_right,
    pairwise_inner_centeredSquareLp (hf.ne hij)]
  simp

/-- Actual centered quadratic convergence requires only the source HS square
sum, not trace summability or an assumed Gaussian-chaos limit. -/
theorem summable_centeredChaosTerm (a : ι → ℝ) (f : ι → ℕ)
    (hf : Function.Injective f) (ha : Summable (fun i ↦ (a i)^2)) :
    Summable (centeredChaosTerm a f) := by
  apply summable_of_pairwise_inner_eq_zero _ (pairwise_inner_centeredChaosTerm a f hf)
  simpa only [norm_centeredChaosTerm_sq] using ha.mul_left 2

def centeredGaussianChaos (a : ι → ℝ) (f : ι → ℕ) :
    Lp ℝ 2 IsonormalProcess.iidStdGaussian := ∑' i, centeredChaosTerm a f i

lemma coeFn_centeredChaosTerm (a : ι → ℝ) (f : ι → ℕ) (i : ι) :
    (centeredChaosTerm a f i : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
      (fun ω ↦ a i*((ω (f i))^2-1)) := by
  filter_upwards [Lp.coeFn_smul (a i) (centeredSquareLp (f i)),
    coeFn_centeredSquareLp (f i)] with ω h1 h2
  change (a i • centeredSquareLp (f i) : Lp ℝ 2 IsonormalProcess.iidStdGaussian) ω = _
  rw [h1,Pi.smul_apply,h2,smul_eq_mul]

lemma coeFn_centeredChaos_sum (a : ι → ℝ) (f : ι → ℕ) (s : Finset ι) :
    (∑ i ∈ s, centeredChaosTerm a f i : Lp ℝ 2 IsonormalProcess.iidStdGaussian)
      =ᵐ[IsonormalProcess.iidStdGaussian]
        (fun ω ↦ ∑ i ∈ s, a i*((ω (f i))^2-1)) := by
  classical
  refine (IsonormalProcess.coeFn_lp_finset_sum (centeredChaosTerm a f) s).trans ?_
  filter_upwards [ae_all_iff.mpr (fun i : s ↦ coeFn_centeredChaosTerm a f i)] with ω hω
  apply Finset.sum_congr rfl
  intro i hi
  exact hω ⟨i,hi⟩

/-- Cofinal finite chaos sums converge to the constructed L2 random variable. -/
theorem tendsto_Lp_centeredGaussianChaos (a : ι → ℝ) (f : ι → ℕ)
    (hf : Function.Injective f) (ha : Summable (fun i ↦ (a i)^2))
    {ss : ℕ → Finset ι} (hss : Tendsto ss atTop atTop) :
    Tendsto (fun n ↦ ∑ i ∈ ss n, centeredChaosTerm a f i) atTop
      (𝓝 (centeredGaussianChaos a f)) :=
  (summable_centeredChaosTerm a f hf ha).hasSum.comp hss

/-- The actual polynomial sums converge in probability to that same L2 limit. -/
theorem tendstoInMeasure_centeredGaussianChaos (a : ι → ℝ) (f : ι → ℕ)
    (hf : Function.Injective f) (ha : Summable (fun i ↦ (a i)^2))
    {ss : ℕ → Finset ι} (hss : Tendsto ss atTop atTop) :
    TendstoInMeasure IsonormalProcess.iidStdGaussian
      (fun n ω ↦ ∑ i ∈ ss n, a i*((ω (f i))^2-1)) atTop
      (centeredGaussianChaos a f : (ℕ → ℝ) → ℝ) :=
  (tendstoInMeasure_of_tendsto_Lp (tendsto_Lp_centeredGaussianChaos a f hf ha hss)).congr_left
    (fun n ↦ coeFn_centeredChaos_sum a f (ss n))

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.norm_centeredSquareLp_sq
#print axioms DGRHS.Gaussian.pairwise_inner_centeredSquareLp
#print axioms DGRHS.Gaussian.summable_centeredChaosTerm
#print axioms DGRHS.Gaussian.tendsto_Lp_centeredGaussianChaos
#print axioms DGRHS.Gaussian.tendstoInMeasure_centeredGaussianChaos
