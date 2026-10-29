import DGRHS.Gaussian.WeakMarginChaosLaplace
import DGRHS.Gaussian.GenericPositiveLaplace

/-! Signed transform of the actual trace-centered quadratic form. This adapts
root WeakMargin's Lq/UI argument to the already constructed AE trace limit.
Trace summability is supplied by the genuine feature spectral factory, not an
ambient trace-class hypothesis. Full-family law transport follows existing
GenericPositiveLaplace. Both root predecessor bodies remain unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 1000000 in
lemma integral_traceCenteredExp_weak_margin (β : ℝ) (a : ι → ℝ)
    (ha : ∀ i,0≤a i) (hs : Summable a) (hm : ∀ i,0<1+β*a i)
    (f : ι → ℕ) (hf : Function.Injective f) :
    Integrable (diagonalCenteredExp β a f) IsonormalProcess.iidStdGaussian ∧
    (∫ ω,diagonalCenteredExp β a f ω ∂IsonormalProcess.iidStdGaussian)=
      (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*a i)))⁻¹ := by
  have hsq : Summable (fun i => (a i)^2) := by
    apply (hs.mul_left (∑' i,a i)).of_norm_bounded
    intro i
    rw [Real.norm_of_nonneg (sq_nonneg _),pow_two]
    exact mul_le_mul_of_nonneg_right (hs.le_tsum i (fun j _ => ha j)) (ha i)
  obtain ⟨p,hp,hphalf,hpm⟩ := exists_spectral_power_above_one β a hsq hm
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  obtain ⟨ss,hss⟩ : ∃ ss : ℕ → Finset ι, Tendsto ss atTop atTop :=
    exists_seq_tendsto (atTop : Filter (Finset ι))
  let F := fun n => diagonalPartialExp β a f (ss n)
  let G := diagonalCenteredExp β a f
  have hFG : TendstoInMeasure IsonormalProcess.iidStdGaussian F atTop G := by
    apply tendstoInMeasure_of_tendsto_ae (fun n =>
      (show Continuous (F n) from by unfold F diagonalPartialExp; fun_prop).aestronglyMeasurable)
    filter_upwards [ae_tendsto_diagonalQuadratic a ha hs f hss] with ω hω
    have ht := (hs.hasSum.comp hss).sub hω
    have he := Real.continuous_exp.continuousAt.tendsto.comp ((ht.const_mul β).div_const 2)
    have hpartial (n : ℕ) : F n ω = Real.exp
        (β*((∑ i ∈ ss n,a i)-∑ i ∈ ss n,a i*IsonormalProcess.coord (f i) ω^2)/2) := by
      unfold F diagonalPartialExp
      congr 1
      rw [←Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    simpa only [hpartial, G, diagonalCenteredExp, Function.comp_def] using he
  let C : ℝ≥0 := ⟨Real.exp
    ((∑' i, |DGRHS.Kernel.regularizedLog (p*β*a i)|)/(2*p)), (Real.exp_pos _).le⟩
  have hq : 1 < ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_lt_ofReal_iff hp0).mpr hp
  obtain ⟨hG,hint⟩ := tendsto_integral_of_Lq_bound_and_inMeasure F G
    (ENNReal.ofReal p) hq ENNReal.ofReal_ne_top
    (fun n => (signedDiagonalPartial_Lq_bound β p hp0 a hpm hsq f hf (ss n)).1) C
    (fun n => by
      have hCeq : ENNReal.ofReal (Real.exp
          ((∑' i, |DGRHS.Kernel.regularizedLog (p*β*a i)|)/(2*p))) = (C : ℝ≥0∞) :=
        ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le
      rw [← hCeq]
      exact (signedDiagonalPartial_Lq_bound β p hp0 a hpm hsq f hf (ss n)).2) hFG
  have hβsq : Summable (fun i => (β*a i)^2) := by
    simpa only [mul_pow] using hsq.mul_left (β^2)
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

lemma integral_familyCenteredExp_weak_margin (β : ℝ) (a : ι → ℝ)
    (ha : ∀ i,0≤a i) (hs : Summable a) (hm : ∀ i,0<1+β*a i)
    (Y : ι → Ω → ℝ) (hY : ∀ i,AEMeasurable (Y i) P) (hI : iIndepFun Y P)
    (hLaw : ∀ i,P.map (Y i)=gaussianReal 0 1) :
    Integrable (fun ω => familyCenteredExp β a (fun i => Y i ω)) P ∧
    (∫ ω,familyCenteredExp β a (fun i => Y i ω) ∂P)=
      (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*a i)))⁻¹ := by
  let f : ι → ℕ := countableGaussianIndex
  have hf : Function.Injective f := countableGaussianIndex.injective
  have hC : AEMeasurable (fun ω i => IsonormalProcess.coord (f i) ω)
      IsonormalProcess.iidStdGaussian := aemeasurable_pi_iff.2
    (fun i => (IsonormalProcess.measurable_coord (f i)).aemeasurable)
  obtain ⟨hi,he⟩ := integral_traceCenteredExp_weak_margin β a ha hs hm f hf
  have hp : Integrable (familyCenteredExp β a)
      (Measure.infinitePi (fun _ : ι => gaussianReal 0 1)) := by
    rw [← map_selectedGaussian_family f hf]
    exact (integrable_map_measure (measurable_familyCenteredExp β a).aestronglyMeasurable hC).2 hi
  have hproper : Integrable (fun ω => familyCenteredExp β a (fun i => Y i ω)) P := by
    rw [← map_standardGaussian_family Y hY hI hLaw] at hp
    exact (integrable_map_measure (measurable_familyCenteredExp β a).aestronglyMeasurable
      (aemeasurable_pi_iff.2 hY)).1 hp
  refine ⟨hproper,?_⟩
  calc
    _ = ∫ z,familyCenteredExp β a z ∂(P.map (fun ω i => Y i ω)) :=
      (integral_map (aemeasurable_pi_iff.2 hY)
        (measurable_familyCenteredExp β a).aestronglyMeasurable).symm
    _ = ∫ z,familyCenteredExp β a z ∂(IsonormalProcess.iidStdGaussian.map
        (fun ω i => IsonormalProcess.coord (f i) ω)) := by
      rw [map_standardGaussian_family Y hY hI hLaw,map_selectedGaussian_family f hf]
    _ = ∫ ω,diagonalCenteredExp β a f ω ∂IsonormalProcess.iidStdGaussian :=
      integral_map hC (measurable_familyCenteredExp β a).aestronglyMeasurable
    _ = _ := he

end DGRHS.Attractive
#check DGRHS.Attractive.integral_traceCenteredExp_weak_margin
#print axioms DGRHS.Attractive.integral_traceCenteredExp_weak_margin
#check DGRHS.Attractive.integral_familyCenteredExp_weak_margin
#print axioms DGRHS.Attractive.integral_familyCenteredExp_weak_margin
