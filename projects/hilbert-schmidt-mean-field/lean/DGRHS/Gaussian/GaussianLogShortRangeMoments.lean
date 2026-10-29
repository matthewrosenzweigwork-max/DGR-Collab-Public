/- Actual all-order logarithmic short-range moments from pinned Gaussian
integration and probability Jensen. No desired moment is assumed. -/
import DGRHS.Gaussian.GaussianLogShortRange
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
noncomputable section
open MeasureTheory Real Set
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianLogNormalizedScale (p : ℕ) (t : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  |t|^(-(Fintype.card ι:ℝ)/(p:ℝ))*Real.exp (-‖x‖^2/(2*t^2))

lemma gaussianLogNormalizedScale_nonneg (p : ℕ) (t : ℝ)
    (x : EuclideanSpace ℝ ι) : 0≤gaussianLogNormalizedScale p t x := by
  unfold gaussianLogNormalizedScale
  exact mul_nonneg (Real.rpow_nonneg (abs_nonneg t) _) (Real.exp_pos _).le

lemma measurable_gaussianLogNormalizedScale (p : ℕ) :
    Measurable (fun z : ℝ×EuclideanSpace ℝ ι => gaussianLogNormalizedScale p z.1 z.2) := by
  unfold gaussianLogNormalizedScale
  fun_prop

lemma gaussianLogNormalizedScale_power (p : ℕ) (hp : 1≤p) (t : ℝ) (ht : 0<t)
    (x : EuclideanSpace ℝ ι) :
    gaussianLogNormalizedScale p t x^p =
      t^(-(Fintype.card ι:ℝ))*Real.exp (-((p:ℝ)/(2*t^2))*‖x‖^2) := by
  have hp0 : (p:ℝ)≠0 := by exact_mod_cast (by omega : p≠0)
  unfold gaussianLogNormalizedScale
  rw [abs_of_pos ht,mul_pow,←Real.rpow_natCast,←Real.rpow_mul ht.le,←Real.exp_nat_mul]
  have he : (-(Fintype.card ι:ℝ)/(p:ℝ))*(p:ℝ)=-(Fintype.card ι:ℝ) := by field_simp
  rw [he]
  congr 2
  ring

lemma integrable_gaussianLogNormalizedScale_pow (p : ℕ) (hp : 1≤p) (t : ℝ) (ht : 0<t) :
    Integrable (fun x : EuclideanSpace ℝ ι => gaussianLogNormalizedScale p t x^p) := by
  have hp0 : 0<(p:ℝ) := by exact_mod_cast (by omega : 0<p)
  simp_rw [gaussianLogNormalizedScale_power p hp t ht]
  exact (integrable_gaussianEuclidean_neg_norm_sq ((p:ℝ)/(2*t^2)) (by positivity)).const_mul _

lemma integral_gaussianLogNormalizedScale_pow (p : ℕ) (hp : 1≤p) (t : ℝ) (ht : 0<t) :
    (∫ x : EuclideanSpace ℝ ι,gaussianLogNormalizedScale p t x^p) =
      (2*Real.pi/(p:ℝ))^((Fintype.card ι:ℝ)/2) := by
  have hp0 : 0<(p:ℝ) := by exact_mod_cast (by omega : 0<p)
  simp_rw [gaussianLogNormalizedScale_power p hp t ht]
  rw [integral_const_mul,integral_gaussianEuclidean_neg_norm_sq _ (by positivity)]
  have hb : Real.pi/((p:ℝ)/(2*t^2)) = (2*Real.pi/(p:ℝ))*t^2 := by field_simp <;> ring
  rw [hb,Real.mul_rpow (by positivity : 0≤2*Real.pi/(p:ℝ)) (sq_nonneg t),
    ←Real.rpow_two,←Real.rpow_mul ht.le]
  have he : (2:ℝ)*((Fintype.card ι:ℝ)/2)=(Fintype.card ι:ℝ) := by ring
  rw [he]
  calc
    _ = (2*Real.pi/(p:ℝ))^((Fintype.card ι:ℝ)/2)*
      (t^(-(Fintype.card ι:ℝ))*t^(Fintype.card ι:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add ht,neg_add_cancel,Real.rpow_zero,mul_one]

lemma integrable_gaussianLogNormalizedScale_pow_product (p : ℕ) (hp : 1≤p)
    (a η : ℝ) (ha : 0<a) (hη : 0<η) :
    Integrable (fun z : ℝ×EuclideanSpace ℝ ι => gaussianLogNormalizedScale p z.1 z.2^p)
      ((gaussianShortRangeScaleMeasure a η).prod volume) := by
  letI := probability_gaussianShortRangeScaleMeasure a η ha hη
  apply (integrable_prod_iff ((measurable_gaussianLogNormalizedScale p).pow_const p).aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_pos_gaussianShortRangeScaleMeasure a η] with t ht
    exact integrable_gaussianLogNormalizedScale_pow p hp t ht
  · apply (integrable_const ((2*Real.pi/(p:ℝ))^((Fintype.card ι:ℝ)/2))).congr
    filter_upwards [ae_pos_gaussianShortRangeScaleMeasure a η] with t ht
    simp_rw [Real.norm_of_nonneg (pow_nonneg (gaussianLogNormalizedScale_nonneg p t _) p)]
    exact (integral_gaussianLogNormalizedScale_pow p hp t ht).symm

lemma probability_mean_nonneg_pow_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (f : Ω→ℝ) (p : ℕ) (hp : 1≤p)
    (hm : AEStronglyMeasurable f ν) (hn : ∀ ω,0≤f ω)
    (hi : Integrable (fun ω => f ω^p) ν) :
    (∫ ω,f ω ∂ν)^p ≤ ∫ ω,f ω^p ∂ν := by
  have hnorm : Integrable (fun ω => ‖f ω‖^p) ν := by
    simpa only [Real.norm_of_nonneg (hn _)] using hi
  have hf : Integrable f ν := by
    simpa only [pow_one,Real.norm_of_nonneg (hn _)] using
      (integrable_norm_pow_of_le hm hp hnorm)
  have hpR : 1≤(p:ℝ) := by exact_mod_cast hp
  have hg := (convexOn_rpow hpR).map_integral_le
    (Real.continuous_rpow_const (by positivity : (0:ℝ)≤(p:ℝ))).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hn) hf
    (by simpa only [Function.comp_def,Real.rpow_natCast] using hi)
  simpa only [Real.rpow_natCast] using hg

lemma integral_gaussianLogShortRange_pow_le (p : ℕ) (hp : 1≤p)
    (η : ℝ) (hη : 0<η) (hd : 0<(Fintype.card ι:ℝ)) :
    Integrable (fun x : EuclideanSpace ℝ ι => gaussianLogShortRange η x^p) ∧
    (∫ x : EuclideanSpace ℝ ι,gaussianLogShortRange η x^p) ≤
      (η^((Fintype.card ι:ℝ)/(p:ℝ))/((Fintype.card ι:ℝ)/(p:ℝ)))^p *
      (2*Real.pi/(p:ℝ))^((Fintype.card ι:ℝ)/2) := by
  have hp0 : 0<(p:ℝ) := by exact_mod_cast (by omega : 0<p)
  let a := (Fintype.card ι:ℝ)/(p:ℝ)
  have ha : 0<a := div_pos hd hp0
  let ν := gaussianShortRangeScaleMeasure a η
  letI := probability_gaussianShortRangeScaleMeasure a η ha hη
  let F := gaussianLogNormalizedScale (ι:=ι) p
  let m := fun x => ∫ t,F t x ∂ν
  have hprod := integrable_gaussianLogNormalizedScale_pow_product (ι:=ι) p hp a η ha hη
  have hm : StronglyMeasurable m := (measurable_gaussianLogNormalizedScale p).stronglyMeasurable.integral_prod_left'
  have hbound : ∀ᵐ x ∂volume,m x^p≤∫ t,F t x^p ∂ν := by
    filter_upwards [hprod.prod_left_ae] with x hx
    exact probability_mean_nonneg_pow_le ν (fun t => F t x) p hp
      ((measurable_gaussianLogNormalizedScale p).comp
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (fun t => gaussianLogNormalizedScale_nonneg p t x) hx
  have hmi : Integrable (fun x => m x^p) := hprod.integral_prod_right.mono'
    (hm.pow p).aestronglyMeasurable (by
      filter_upwards [hbound] with x hx
      have hn : 0≤m x := integral_nonneg (fun t => gaussianLogNormalizedScale_nonneg p t x)
      simpa only [Real.norm_of_nonneg (pow_nonneg hn p)] using hx)
  have he : ∀ x : EuclideanSpace ℝ ι,gaussianLogShortRange η x=(η^a/a)*m x := fun x =>
    gaussianLogShortRange_eq_scaleMean a η ha hη a rfl x F (fun t ht => by
      simp only [F,gaussianLogNormalizedScale,a,abs_of_pos ht,neg_div])
  simp_rw [he,mul_pow]
  refine ⟨hmi.const_mul _,?_⟩
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∫ x,m x^p) ≤ ∫ x,∫ t,F t x^p ∂ν := integral_mono_ae hmi hprod.integral_prod_right hbound
    _ = ∫ t,(∫ x,F t x^p) ∂ν := (integral_integral_swap hprod).symm
    _ = _ := by
      rw [integral_congr_ae (show (fun t => ∫ x,F t x^p)=ᵐ[ν]
        (fun _ => (2*Real.pi/(p:ℝ))^((Fintype.card ι:ℝ)/2)) from by
          filter_upwards [ae_pos_gaussianShortRangeScaleMeasure a η] with t ht
          exact integral_gaussianLogNormalizedScale_pow p hp t ht)]
      simp

end DGRHS.Gaussian
#check @DGRHS.Gaussian.integral_gaussianLogShortRange_pow_le
#print axioms DGRHS.Gaussian.gaussianLogNormalizedScale_power
#print axioms DGRHS.Gaussian.integrable_gaussianLogNormalizedScale_pow_product
#print axioms DGRHS.Gaussian.probability_mean_nonneg_pow_le
#print axioms DGRHS.Gaussian.integral_gaussianLogShortRange_pow_le
