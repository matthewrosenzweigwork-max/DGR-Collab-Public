import DGRHS.Gaussian.PeriodicHeatScaleNormalization

/-! Proper spatial lattice sums and their actual small-scale heat integral.
The zero image is isolated explicitly. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodic_zero_spike_summable (c : ℝ) :
    Summable (fun k : PeriodicFrequency ι => if k=0 then c else 0) := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_singleton (0 : PeriodicFrequency ι)).subset
  intro k hk
  by_contra hn
  have hz : k≠0 := by simpa only [Set.mem_singleton_iff] using hn
  simpa only [Function.mem_support,hz,↓reduceIte,ne_self_iff_false] using hk

lemma periodic_short_gaussian_spatial_bound (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    Summable (fun k : PeriodicFrequency ι => Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2))) ∧
    (∑' k : PeriodicFrequency ι,Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2))) ≤
      Real.exp (-‖x‖^2/(2*t^2))+Real.exp (-1/(16*t^2))*
        ∑' k : PeriodicFrequency ι,Real.exp (-‖periodicFrequencyVector k‖^2/16) := by
  have hs : Summable (fun k : PeriodicFrequency ι => Real.exp (-‖periodicFrequencyVector k‖^2/16)) :=
    (summable_periodicGaussian (ι := ι) (1/16) (by norm_num)).congr (fun k => by congr 1; ring)
  let D := fun k : PeriodicFrequency ι =>
    (if k=0 then Real.exp (-‖x‖^2/(2*t^2)) else 0)+
      Real.exp (-1/(16*t^2))*Real.exp (-‖periodicFrequencyVector k‖^2/16)
  have hd : Summable D := (periodic_zero_spike_summable _).add (hs.mul_left _)
  have hb (k : PeriodicFrequency ι) : Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2)) ≤ D k := by
    by_cases hk : k=0
    · subst k
      simp only [D,ite_true,periodicFrequencyVector_zero,add_zero,norm_zero,zero_pow (by norm_num : 2≠0),
        neg_zero,zero_div,Real.exp_zero,mul_one]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · simpa only [D,hk,↓reduceIte,zero_add] using periodic_nonzero_lattice_gaussian_bound x hx k hk t ht ht1
  have hf := hd.of_nonneg_of_le (fun k => (Real.exp_pos _).le) hb
  refine ⟨hf,?_⟩
  have h := Summable.tsum_le_tsum hb hf hd
  simpa only [D,(periodic_zero_spike_summable _).tsum_add (hs.mul_left _),tsum_ite_eq,tsum_mul_left] using h

lemma periodic_lattice_core_summable (x : EuclideanSpace ℝ ι) (hx : ∀ i,|x i|≤1/2) :
    Summable (fun k : PeriodicFrequency ι => periodicLocalLogCore ‖x+periodicFrequencyVector k‖) := by
  have h := (periodic_zero_spike_summable (ι := ι) (periodicLocalLogCore ‖x‖)).add
    (summable_periodicNonzeroImageTerm x hx)
  apply h.congr
  intro k
  by_cases hk : k=0 <;> simp [hk,periodicNonzeroImageTerm]

lemma periodic_lattice_core_sum (x : EuclideanSpace ℝ ι) (hx : ∀ i,|x i|≤1/2) :
    (∑' k : PeriodicFrequency ι,periodicLocalLogCore ‖x+periodicFrequencyVector k‖) =
      periodicLocalLogCore ‖x‖+periodicNonzeroImageRemainder x := by
  have he : (fun k : PeriodicFrequency ι => periodicLocalLogCore ‖x+periodicFrequencyVector k‖) =
      fun k => (if k=0 then periodicLocalLogCore ‖x‖ else 0)+periodicNonzeroImageTerm x k := by
    funext k
    by_cases hk : k=0 <;> simp [hk,periodicNonzeroImageTerm]
  rw [he,(periodic_zero_spike_summable _).tsum_add (summable_periodicNonzeroImageTerm x hx),tsum_ite_eq]
  rfl

lemma periodic_short_lattice_integral_norm (x : EuclideanSpace ℝ ι) (k : PeriodicFrequency ι) :
    (∫ t : ℝ in Ioc 0 1,‖t⁻¹*Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2))‖) =
      periodicLocalLogCore ‖x+periodicFrequencyVector k‖ := by
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr ht.1.le) (Real.exp_pos _).le)

/-- The actual small-scale physical Gaussian integral equals the zero-image
logarithmic core plus the genuine bounded image remainder. -/
theorem periodic_short_lattice_integral (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (hx0 : x≠0) :
    (∫ t : ℝ in Ioc 0 1,t⁻¹*∑' k : PeriodicFrequency ι,
      Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2))) =
        periodicLocalLogCore ‖x‖+periodicNonzeroImageRemainder x := by
  have hi (k : PeriodicFrequency ι) : IntegrableOn (fun t : ℝ =>
      t⁻¹*Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2))) (Ioc 0 1) := by
    apply periodicLocalLogCore_integrable
    by_cases hk : k=0
    · simpa [hk] using norm_pos_iff.mpr hx0
    · exact periodic_nonzero_image_norm_pos x hx k hk
  have hs : Summable (fun k : PeriodicFrequency ι =>
      ∫ t : ℝ in Ioc 0 1,‖t⁻¹*Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2))‖) := by
    simpa only [periodic_short_lattice_integral_norm] using periodic_lattice_core_summable x hx
  simp only [← tsum_mul_left]
  rw [← integral_tsum_of_summable_integral_norm hi hs]
  exact periodic_lattice_core_sum x hx

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_short_gaussian_spatial_bound
#print axioms DGRHS.Periodic.periodic_lattice_core_summable
#print axioms DGRHS.Periodic.periodic_short_lattice_integral
#check @DGRHS.Periodic.periodic_short_lattice_integral
