import DGRHS.Gaussian.PeriodicPhysicalGreenIdentification

/-! Uniform exponentially decaying bound for the genuine centered torus heat
kernel in the usual heat-time variable. This is a proved lattice-gap estimate,
not a pointwise Green or regularization assumption. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicHeatTailMass (ι : Type u) [Fintype ι] : ℝ :=
  ∑' k : PeriodicFrequency ι,Real.exp (-(1/2:ℝ)*‖periodicFrequencyVector k‖^2)

lemma periodicHeatTailMass_nonneg : 0≤periodicHeatTailMass ι :=
  tsum_nonneg (fun _ => (Real.exp_pos _).le)

def periodicCenteredHeatTerm (s : ℝ) (x : PeriodicTorus ι) (k : PeriodicFrequency ι) : ℂ :=
  if k=0 then 0 else (Real.exp (-s*‖periodicFrequencyVector k‖^2):ℂ)*UnitAddTorus.mFourier k x

lemma periodicCenteredHeatTerm_norm_bound (s : ℝ) (x : PeriodicTorus ι) (k : PeriodicFrequency ι) :
    ‖periodicCenteredHeatTerm s x k‖≤Real.exp (-s*‖periodicFrequencyVector k‖^2) := by
  unfold periodicCenteredHeatTerm
  split_ifs
  · simpa using (Real.exp_pos _).le
  · simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,
      periodic_mFourier_norm_apply,mul_one,le_refl]

lemma periodicCenteredHeatTerm_summable (s : ℝ) (hs : 0<s) (x : PeriodicTorus ι) :
    Summable (periodicCenteredHeatTerm s x) :=
  Summable.of_norm ((summable_periodicGaussian s hs).of_nonneg_of_le (fun k => norm_nonneg _)
    (periodicCenteredHeatTerm_norm_bound s x))

lemma periodicGaussianHeat_centered_series (s : ℝ) (hs : 0<s) (x : PeriodicTorus ι) :
    periodicGaussianHeat s x-1=∑' k : PeriodicFrequency ι,periodicCenteredHeatTerm s x k := by
  have hzero : Summable (fun k : PeriodicFrequency ι => if k=0 then (1:ℂ) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : PeriodicFrequency ι)).subset
    intro k hk
    by_contra hn
    have hz : k≠0 := by simpa only [Set.mem_singleton_iff] using hn
    simpa only [Function.mem_support,hz,↓reduceIte,ne_self_iff_false] using hk
  have he (k : PeriodicFrequency ι) :
      (Real.exp (-s*‖periodicFrequencyVector k‖^2):ℂ)*UnitAddTorus.mFourier k x=
      (if k=0 then 1 else 0)+periodicCenteredHeatTerm s x k := by
    by_cases hk : k=0
    · subst k
      simp [periodicCenteredHeatTerm,periodicFrequencyVector_zero,UnitAddTorus.mFourier_zero,ContinuousMap.one_apply]
    · simp [periodicCenteredHeatTerm,hk]
  simp only [periodicGaussianHeat,he,hzero.tsum_add (periodicCenteredHeatTerm_summable s hs x),tsum_ite_eq]
  ring

lemma periodicHeatTime_gap_bound (s : ℝ) (hs : 1≤s) (k : PeriodicFrequency ι) (hk : k≠0) :
    Real.exp (-s*‖periodicFrequencyVector k‖^2)≤
      Real.exp (-s/2)*Real.exp (-(1/2:ℝ)*‖periodicFrequencyVector k‖^2) := by
  rw [← Real.exp_add,Real.exp_le_exp]
  have h := periodicFrequency_norm_sq_ge_one hk
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr h)]

lemma periodicGaussianHeat_centered_time_bound (s : ℝ) (hs : 1≤s) (x : PeriodicTorus ι) :
    ‖periodicGaussianHeat s x-1‖≤Real.exp (-s/2)*periodicHeatTailMass ι := by
  have hs0 : 0<s := zero_lt_one.trans_le hs
  let B := fun k : PeriodicFrequency ι =>
    Real.exp (-s/2)*Real.exp (-(1/2:ℝ)*‖periodicFrequencyVector k‖^2)
  have hb : Summable B := (summable_periodicGaussian (ι := ι) (1/2) (by norm_num)).mul_left _
  have hle (k : PeriodicFrequency ι) : ‖periodicCenteredHeatTerm s x k‖≤B k := by
    by_cases hk : k=0
    · simp only [periodicCenteredHeatTerm,hk,ite_true,norm_zero]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    · exact (periodicCenteredHeatTerm_norm_bound s x k).trans (periodicHeatTime_gap_bound s hs k hk)
  have hn := hb.of_nonneg_of_le (fun k => norm_nonneg _) hle
  rw [periodicGaussianHeat_centered_series s hs0]
  exact (norm_tsum_le_tsum_norm hn).trans (by
    simpa only [B,tsum_mul_left,periodicHeatTailMass] using Summable.tsum_le_tsum hle hn hb)

lemma periodicGaussianHeat_real_centered_time_bound (s : ℝ) (hs : 1≤s) (x : PeriodicTorus ι) :
    |(periodicGaussianHeat s x).re-1|≤Real.exp (-s/2)*periodicHeatTailMass ι := by
  have h := Complex.abs_re_le_norm (periodicGaussianHeat s x-1)
  simpa only [Complex.sub_re,Complex.one_re] using h.trans (periodicGaussianHeat_centered_time_bound s hs x)

lemma periodicHeatTime_rpow_exp_integrable (p a : ℝ) (hp : -1<p) (ha : 0<a) :
    IntegrableOn (fun s : ℝ => s^p*Real.exp (-a*s)) (Ioi 0) := by
  simpa only [Real.rpow_one] using integrableOn_rpow_mul_exp_neg_mul_rpow hp (by norm_num : (0:ℝ)<1) ha

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicGaussianHeat_centered_time_bound
#print axioms DGRHS.Periodic.periodicGaussianHeat_real_centered_time_bound
#print axioms DGRHS.Periodic.periodicHeatTime_rpow_exp_integrable
#check @DGRHS.Periodic.periodicGaussianHeat_centered_time_bound
