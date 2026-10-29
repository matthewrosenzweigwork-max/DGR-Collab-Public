import DGRHS.Gaussian.FiniteLaplace
import DGRHS.Gaussian.Imported.IsonormalProcess
import DGRHS.Kernel.RegularizedDeterminant
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Actual countable positive diagonal quadratic form on the existing iid Gaussian
coordinate space. Genuine trace summability is an explicit hypothesis. No
physical feature/kernel eigenvalue identification or limiting law is assumed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology

namespace DGRHS.Gaussian
noncomputable section
variable {ι : Type*} [Countable ι]

/-- Actual positive diagonal coordinate series; not a physical-kernel identification. -/
def diagonalQuadratic (a : ι → ℝ) (f : ι → ℕ) (ω : ℕ → ℝ) : ℝ :=
  ∑' i, a i * IsonormalProcess.coord (f i) ω ^ 2

theorem selectedGaussian_map (f : ι → ℕ) (hf : Function.Injective f) (s : Finset ι) :
    IsonormalProcess.iidStdGaussian.map (fun ω (i : s) => IsonormalProcess.coord (f i) ω) =
      finiteStandardGaussian s := by
  have hI : iIndepFun (fun i : s => IsonormalProcess.coord (f i))
      IsonormalProcess.iidStdGaussian :=
    IsonormalProcess.iIndepFun_coord.precomp (hf.comp Subtype.val_injective)
  rw [hI.map_fun_eq_pi_map (fun i : s => (IsonormalProcess.measurable_coord (f i)).aemeasurable)]
  simp only [IsonormalProcess.map_coord, finiteStandardGaussian]

private theorem integrable_diagonalTerm (a : ι → ℝ) (f : ι → ℕ) (i : ι) :
    Integrable (fun ω => a i * IsonormalProcess.coord (f i) ω ^ 2)
      IsonormalProcess.iidStdGaussian :=
  ((IsonormalProcess.memLp_coord (f i)).integrable_sq).const_mul _

private theorem integral_diagonalTerm (a : ι → ℝ) (f : ι → ℕ) (i : ι) :
    (∫ ω, a i * IsonormalProcess.coord (f i) ω ^ 2 ∂IsonormalProcess.iidStdGaussian) = a i := by
  rw [integral_const_mul]
  simp only [pow_two, IsonormalProcess.integral_coord_sq, mul_one]

private def diagonalTermL1 (a : ι → ℝ) (f : ι → ℕ) (i : ι) :
    Lp ℝ 1 IsonormalProcess.iidStdGaussian :=
  (integrable_diagonalTerm a f i).toL1 (fun ω => a i * IsonormalProcess.coord (f i) ω ^ 2)

private theorem coeFn_diagonalTermL1 (a : ι → ℝ) (f : ι → ℕ) (i : ι) :
    (diagonalTermL1 a f i : (ℕ → ℝ) → ℝ) =ᵐ[IsonormalProcess.iidStdGaussian]
      (fun ω => a i * IsonormalProcess.coord (f i) ω ^ 2) :=
  (integrable_diagonalTerm a f i).coeFn_toL1

private theorem norm_diagonalTermL1 (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : ι → ℕ) (i : ι) : ‖diagonalTermL1 a f i‖ = a i := by
  rw [L1.norm_eq_integral_norm]
  calc
    _ = ∫ ω, a i * IsonormalProcess.coord (f i) ω ^ 2 ∂IsonormalProcess.iidStdGaussian := by
      apply integral_congr_ae
      filter_upwards [coeFn_diagonalTermL1 a f i] with ω hω
      rw [hω, Real.norm_of_nonneg (mul_nonneg (ha i) (sq_nonneg _))]
    _ = a i := integral_diagonalTerm a f i

private theorem ae_hasSum_diagonalTermL1 (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) (f : ι → ℕ) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, HasSum
      (fun i => a i * IsonormalProcess.coord (f i) ω ^ 2)
      ((∑' i, diagonalTermL1 a f i) ω) := by
  have hen : (∑' i, ‖diagonalTermL1 a f i‖ₑ) ≠ ∞ := by
    simpa only [← ofReal_norm, norm_diagonalTermL1 a ha f] using hs.tsum_ofReal_ne_top
  filter_upwards [Lp.hasSum_coeFn_tsum hen,
    ae_all_iff.2 (fun i => coeFn_diagonalTermL1 a f i)] with ω hsum heq
  exact hsum.congr_fun (fun i => (heq i).symm)

theorem ae_summable_diagonalQuadratic (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) (f : ι → ℕ) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
      Summable (fun i => a i * IsonormalProcess.coord (f i) ω ^ 2) :=
  (ae_hasSum_diagonalTermL1 a ha hs f).mono (fun _ h => h.summable)

theorem integrable_diagonalQuadratic (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) (f : ι → ℕ) :
    Integrable (diagonalQuadratic a f) IsonormalProcess.iidStdGaussian := by
  have heq : ((∑' i, diagonalTermL1 a f i : Lp ℝ 1 IsonormalProcess.iidStdGaussian) : (ℕ → ℝ) → ℝ)
      =ᵐ[IsonormalProcess.iidStdGaussian] diagonalQuadratic a f := by
    filter_upwards [ae_hasSum_diagonalTermL1 a ha hs f] with ω hω
    exact hω.tsum_eq.symm
  exact ((Lp.memLp (∑' i, diagonalTermL1 a f i)).integrable (by norm_num)).congr heq

theorem integral_diagonalQuadratic (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) (f : ι → ℕ) :
    (∫ ω, diagonalQuadratic a f ω ∂IsonormalProcess.iidStdGaussian) = ∑' i, a i := by
  have hn : Summable (fun i => ∫ ω, ‖a i * IsonormalProcess.coord (f i) ω ^ 2‖
      ∂IsonormalProcess.iidStdGaussian) := by
    simpa only [Real.norm_of_nonneg (mul_nonneg (ha _) (sq_nonneg _)),
      integral_diagonalTerm] using hs
  calc
    _ = ∑' i, ∫ ω, a i * IsonormalProcess.coord (f i) ω ^ 2
        ∂IsonormalProcess.iidStdGaussian :=
      (integral_tsum_of_summable_integral_norm (fun i => integrable_diagonalTerm a f i) hn).symm
    _ = ∑' i, a i := by simp_rw [integral_diagonalTerm]

theorem ae_tendsto_diagonalQuadratic (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) (f : ι → ℕ) {ss : ℕ → Finset ι}
    (hss : Tendsto ss atTop atTop) :
    ∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Tendsto
      (fun n => ∑ i ∈ ss n, a i * IsonormalProcess.coord (f i) ω ^ 2)
      atTop (𝓝 (diagonalQuadratic a f ω)) := by
  filter_upwards [ae_summable_diagonalQuadratic a ha hs f] with ω hω
  exact hω.hasSum.comp hss


/-- Centered actual finite-coordinate exponential truncation. -/
def diagonalPartialExp (β : ℝ) (a : ι → ℝ) (f : ι → ℕ)
    (s : Finset ι) (ω : ℕ → ℝ) : ℝ :=
  Real.exp (∑ i ∈ s, (β * a i / 2) * (1 - IsonormalProcess.coord (f i) ω ^ 2))

/-- Centered exponential of the constructed actual countable quadratic form. -/
def diagonalCenteredExp (β : ℝ) (a : ι → ℝ) (f : ι → ℕ) (ω : ℕ → ℝ) : ℝ :=
  Real.exp (β * ((∑' i, a i) - diagonalQuadratic a f ω) / 2)

private theorem diagonalPartialExponent (β : ℝ) (a : ι → ℝ) (f : ι → ℕ)
    (s : Finset ι) (ω : ℕ → ℝ) :
    (∑ i ∈ s, (β * a i / 2) * (1 - IsonormalProcess.coord (f i) ω ^ 2)) =
      β * ((∑ i ∈ s, a i) - ∑ i ∈ s, a i * IsonormalProcess.coord (f i) ω ^ 2) / 2 := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem integrable_diagonalPartialExp (β : ℝ) (hβ : 0 ≤ β) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (f : ι → ℕ) (hf : Function.Injective f) (s : Finset ι) :
    Integrable (diagonalPartialExp β a f s) IsonormalProcess.iidStdGaussian := by
  let g := fun ω (i : s) => IsonormalProcess.coord (f i) ω
  have hg : Measurable g := Measurable.of_eval
    (fun i : s => IsonormalProcess.measurable_coord (f i))
  have hp : MeasurePreserving g IsonormalProcess.iidStdGaussian (finiteStandardGaussian s) :=
    ⟨hg, selectedGaussian_map f hf s⟩
  have hcomp := hp.integrable_comp_of_integrable
      (integrable_exp_centered_neg_quadratic β (fun i : s => a i) hβ (fun i => ha i))
  apply hcomp.congr
  filter_upwards [] with ω
  change Real.exp (∑ i : s, (β * a i / 2) *
    (1 - IsonormalProcess.coord (f i) ω ^ 2)) = diagonalPartialExp β a f s ω
  congr 1
  exact Finset.sum_coe_sort s
    (fun i => (β * a i / 2) * (1 - IsonormalProcess.coord (f i) ω ^ 2))

theorem integral_diagonalPartialExp (β : ℝ) (hβ : 0 ≤ β) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (f : ι → ℕ) (hf : Function.Injective f) (s : Finset ι) :
    (∫ ω, diagonalPartialExp β a f s ω ∂IsonormalProcess.iidStdGaussian) =
      ∏ i ∈ s, Real.exp (β * a i / 2) * (Real.sqrt (1 + β * a i))⁻¹ := by
  let g := fun ω (i : s) => IsonormalProcess.coord (f i) ω
  have hg : Measurable g := Measurable.of_eval
    (fun i : s => IsonormalProcess.measurable_coord (f i))
  have hm := integral_map (μ := IsonormalProcess.iidStdGaussian) (φ := g)
    (f := fun z : s → ℝ => Real.exp (∑ i : s, (β * a i / 2) * (1 - z i ^ 2)))
    hg.aemeasurable (show AEStronglyMeasurable _ _ from
      (show Continuous (fun z : s → ℝ => Real.exp (∑ i : s, (β * a i / 2) * (1 - z i ^ 2)))
        from by fun_prop).aestronglyMeasurable)
  rw [selectedGaussian_map f hf s,
    integral_exp_centered_neg_quadratic β (fun i : s => a i) hβ (fun i => ha i)] at hm
  rw [Finset.prod_coe_sort s (fun i : ι =>
    Real.exp (β * a i / 2) * (Real.sqrt (1 + β * a i))⁻¹)] at hm
  calc
    _ = ∫ ω, Real.exp (∑ i : s, (β * a i / 2) *
        (1 - IsonormalProcess.coord (f i) ω ^ 2)) ∂IsonormalProcess.iidStdGaussian := by
      apply integral_congr_ae
      filter_upwards [] with ω
      change Real.exp (∑ i ∈ s, (β * a i / 2) *
        (1 - IsonormalProcess.coord (f i) ω ^ 2)) =
        Real.exp (∑ i : s, (β * a i / 2) * (1 - IsonormalProcess.coord (f i) ω ^ 2))
      apply congrArg Real.exp
      exact (Finset.sum_coe_sort s
        (fun i => (β * a i / 2) * (1 - IsonormalProcess.coord (f i) ω ^ 2))).symm
    _ = _ := hm.symm

theorem diagonalPartialExp_bound (β : ℝ) (hβ : 0 ≤ β) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (f : ι → ℕ) (s : Finset ι) (ω : ℕ → ℝ) :
    ‖diagonalPartialExp β a f s ω‖ ≤ Real.exp (β * (∑' i, a i) / 2) := by
  rw [diagonalPartialExp, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp,
    diagonalPartialExponent]
  have hq : 0 ≤ ∑ i ∈ s, a i * IsonormalProcess.coord (f i) ω ^ 2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (sq_nonneg _))
  have ht := hs.sum_le_tsum s (fun i _ => ha i)
  have hm := mul_le_mul_of_nonneg_left ht hβ
  nlinarith

theorem integrable_diagonalCenteredExp (β : ℝ) (hβ : 0 ≤ β) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (f : ι → ℕ) :
    Integrable (diagonalCenteredExp β a f) IsonormalProcess.iidStdGaussian := by
  have hm : AEStronglyMeasurable (diagonalCenteredExp β a f)
      IsonormalProcess.iidStdGaussian := by
    unfold diagonalCenteredExp
    exact (show Continuous (fun r : ℝ => Real.exp (β * ((∑' i, a i) - r) / 2))
      from by fun_prop).comp_aestronglyMeasurable
      (integrable_diagonalQuadratic a ha hs f).aestronglyMeasurable
  apply (integrable_const (Real.exp (β * (∑' i, a i) / 2))).mono' hm
  filter_upwards [] with ω
  rw [diagonalCenteredExp, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
  have hq : 0 ≤ diagonalQuadratic a f ω := tsum_nonneg (fun i => mul_nonneg (ha i) (sq_nonneg _))
  have hm := mul_nonneg hβ hq
  nlinarith

theorem tendsto_integral_diagonalPartialExp (β : ℝ) (hβ : 0 ≤ β) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (f : ι → ℕ)
    {ss : ℕ → Finset ι} (hss : Tendsto ss atTop atTop) :
    Tendsto (fun n => ∫ ω, diagonalPartialExp β a f (ss n) ω
      ∂IsonormalProcess.iidStdGaussian) atTop
      (𝓝 (∫ ω, diagonalCenteredExp β a f ω ∂IsonormalProcess.iidStdGaussian)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ => Real.exp (β * (∑' i, a i) / 2))
  · intro n
    exact (show Continuous (diagonalPartialExp β a f (ss n)) from by
      unfold diagonalPartialExp IsonormalProcess.coord
      fun_prop).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall (diagonalPartialExp_bound β hβ a ha hs f (ss n))
  · filter_upwards [ae_tendsto_diagonalQuadratic a ha hs f hss] with ω hω
    have ht := (hs.hasSum.comp hss).sub hω
    have he := Real.continuous_exp.continuousAt.tendsto.comp ((ht.const_mul β).div_const 2)
    simpa only [diagonalPartialExp, diagonalCenteredExp, diagonalPartialExponent, Function.comp_def] using he

private theorem summable_sq_of_nonneg (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hs : Summable a) : Summable (fun i => a i ^ 2) := by
  apply (hs.mul_left (∑' i, a i)).of_norm_bounded
  intro i
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (hs.le_tsum i (fun j _ => ha j)) (ha i)

private theorem centeredFactor_eq_exp_regularizedLog {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (t / 2) * (Real.sqrt (1 + t))⁻¹ =
      Real.exp (-(DGRHS.Kernel.regularizedLog t) / 2) := by
  have hp : 0 < 1 + t := by linarith
  have hr : Real.sqrt (1 + t) = Real.exp (Real.log (1 + t) / 2) := by
    rw [← Real.log_sqrt hp.le, Real.exp_log (Real.sqrt_pos.2 hp)]
  rw [hr, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  unfold DGRHS.Kernel.regularizedLog
  ring

private theorem inv_sqrt_regularizedDet_eq (β : ℝ) (hβ : 0 ≤ β) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) :
    (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * a i)))⁻¹ =
      Real.exp (-(∑' i, DGRHS.Kernel.regularizedLog (β * a i)) / 2) := by
  have hb : ∀ i, 0 ≤ β * a i := fun i => mul_nonneg hβ (ha i)
  have hsq := summable_sq_of_nonneg (fun i => β * a i) hb (hs.mul_left β)
  have hp : ∀ i, 0 < 1 + β * a i := fun i => by have := hb i; linarith
  have hd := DGRHS.Kernel.regularizedDet_pos hsq hp
  have hr : Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * a i)) =
      Real.exp ((∑' i, DGRHS.Kernel.regularizedLog (β * a i)) / 2) := by
    calc
      _ = Real.exp (Real.log (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * a i)))) :=
        (Real.exp_log (Real.sqrt_pos.2 hd)).symm
      _ = _ := by rw [Real.log_sqrt hd.le, DGRHS.Kernel.log_regularizedDet hsq hp]; rfl
  rw [hr, ← Real.exp_neg]
  congr 1
  ring

/-- Actual positive trace-summable infinite coordinate Laplace identity.
It includes beta zero and empty/finite index without dividing by variance. -/
theorem integral_diagonalCenteredExp (β : ℝ) (hβ : 0 ≤ β) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : Summable a) (f : ι → ℕ) (hf : Function.Injective f) :
    (∫ ω, diagonalCenteredExp β a f ω ∂IsonormalProcess.iidStdGaussian) =
      (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * a i)))⁻¹ := by
  classical
  obtain ⟨ss, hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  have hb : ∀ i, 0 ≤ β * a i := fun i => mul_nonneg hβ (ha i)
  have hlog := DGRHS.Kernel.summable_regularizedLog
    (summable_sq_of_nonneg (fun i => β * a i) hb (hs.mul_left β))
  have hell : Summable (fun i => -(DGRHS.Kernel.regularizedLog (β * a i)) / 2) := by
    convert (hlog.div_const 2).neg using 1
    funext i
    ring
  have he := Real.continuous_exp.continuousAt.tendsto.comp (hell.hasSum.comp hss)
  simp only [Function.comp_def] at he
  have hfinite (n : ℕ) : (∫ ω, diagonalPartialExp β a f (ss n) ω
      ∂IsonormalProcess.iidStdGaussian) =
      Real.exp (∑ i ∈ ss n, -(DGRHS.Kernel.regularizedLog (β * a i)) / 2) := by
    rw [integral_diagonalPartialExp β hβ a ha f hf]
    simp_rw [centeredFactor_eq_exp_regularizedLog (hb _)]
    rw [Real.exp_sum]
  have htarget : Real.exp (∑' i, -(DGRHS.Kernel.regularizedLog (β * a i)) / 2) =
      (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * a i)))⁻¹ := by
    rw [inv_sqrt_regularizedDet_eq β hβ a ha hs, tsum_div_const, tsum_neg]
  have hlim : Tendsto (fun n => ∫ ω, diagonalPartialExp β a f (ss n) ω
      ∂IsonormalProcess.iidStdGaussian) atTop
      (𝓝 (Real.exp (∑' i, -(DGRHS.Kernel.regularizedLog (β * a i)) / 2))) :=
    he.congr' (Filter.Eventually.of_forall (fun n => (hfinite n).symm))
  rw [htarget] at hlim
  exact tendsto_nhds_unique (tendsto_integral_diagonalPartialExp β hβ a ha hs f hss) hlim

end
end DGRHS.Gaussian

#check DGRHS.Gaussian.selectedGaussian_map
#print axioms DGRHS.Gaussian.selectedGaussian_map
#check DGRHS.Gaussian.diagonalQuadratic
#print axioms DGRHS.Gaussian.diagonalQuadratic
#check DGRHS.Gaussian.ae_summable_diagonalQuadratic
#print axioms DGRHS.Gaussian.ae_summable_diagonalQuadratic
#check DGRHS.Gaussian.integrable_diagonalQuadratic
#print axioms DGRHS.Gaussian.integrable_diagonalQuadratic
#check DGRHS.Gaussian.integral_diagonalQuadratic
#print axioms DGRHS.Gaussian.integral_diagonalQuadratic
#check DGRHS.Gaussian.ae_tendsto_diagonalQuadratic
#print axioms DGRHS.Gaussian.ae_tendsto_diagonalQuadratic

#check DGRHS.Gaussian.diagonalPartialExp
#print axioms DGRHS.Gaussian.diagonalPartialExp
#check DGRHS.Gaussian.diagonalCenteredExp
#print axioms DGRHS.Gaussian.diagonalCenteredExp
#check DGRHS.Gaussian.integrable_diagonalPartialExp
#print axioms DGRHS.Gaussian.integrable_diagonalPartialExp
#check DGRHS.Gaussian.integral_diagonalPartialExp
#print axioms DGRHS.Gaussian.integral_diagonalPartialExp
#check DGRHS.Gaussian.diagonalPartialExp_bound
#print axioms DGRHS.Gaussian.diagonalPartialExp_bound
#check DGRHS.Gaussian.integrable_diagonalCenteredExp
#print axioms DGRHS.Gaussian.integrable_diagonalCenteredExp
#check DGRHS.Gaussian.tendsto_integral_diagonalPartialExp
#print axioms DGRHS.Gaussian.tendsto_integral_diagonalPartialExp
#check DGRHS.Gaussian.integral_diagonalCenteredExp
#print axioms DGRHS.Gaussian.integral_diagonalCenteredExp
