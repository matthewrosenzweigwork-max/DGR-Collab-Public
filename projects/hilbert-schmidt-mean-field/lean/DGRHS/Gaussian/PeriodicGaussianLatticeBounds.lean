import DGRHS.Gaussian.PeriodicLogFourier

/-! Gaussian summability and uniform lattice-image separation on the actual
centered fundamental cube. These estimates construct the domination needed
for the physical periodic heat representation. -/
noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicFrequency_norm_pos {k : PeriodicFrequency ι} (hk : k≠0) :
    0<‖periodicFrequencyVector k‖ := by
  apply norm_pos_iff.mpr
  intro h
  apply hk
  exact periodicFrequencyVector_injective (h.trans periodicFrequencyVector_zero.symm)

lemma periodicFrequency_norm_sq_ge_one {k : PeriodicFrequency ι} (hk : k≠0) :
    1≤‖periodicFrequencyVector k‖^2 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hk
  have hz : k i≠0 := hi
  have ha : (1:ℝ)≤|(k i:ℝ)| := by
    have hz' : k i≤-1 ∨ 1≤k i := by omega
    rcases hz' with h | h
    · have hr : (k i:ℝ)≤-1 := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hr : (1:ℝ)≤k i := by exact_mod_cast h
      exact hr.trans (le_abs_self _)
  have hs : (k i:ℝ)^2≤∑ j : ι,(k j:ℝ)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (k j:ℝ)) (Finset.mem_univ i)
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [periodicFrequencyVector_apply]
  nlinarith [sq_abs (k i:ℝ)]

lemma periodic_gaussian_inverse_power_bound (a r : ℝ) (ha : 0<a) (hr : 0<r) (n : ℕ) :
    Real.exp (-a*r^2) ≤ (n.factorial:ℝ)/a^n*r⁻¹^(2*n) := by
  have hf : (0:ℝ)<n.factorial := by positivity
  have h := Real.pow_div_factorial_le_exp (a*r^2) (by positivity) n
  have hi := one_div_le_one_div_of_le (div_pos (pow_pos (mul_pos ha (sq_pos_of_pos hr)) _) hf) h
  rw [one_div,←Real.exp_neg] at hi
  calc
    _ = Real.exp (-(a*r^2)) := by congr 1;ring
    _ ≤ ((a*r^2)^n/(n.factorial:ℝ))⁻¹ := by simpa only [one_div] using hi
    _ = _ := by
      simp only [inv_div,mul_pow,inv_pow,←pow_mul]
      field_simp
      <;> ring

lemma summable_periodicGaussian (a : ℝ) (ha : 0<a) :
    Summable (fun k : PeriodicFrequency ι => Real.exp (-a*‖periodicFrequencyVector k‖^2)) := by
  let C : ℝ := (Fintype.card ι).factorial/a^(Fintype.card ι)
  have hs := (summable_periodicFrequency_inv_doubleDimension (ι := ι)).mul_left C
  have h0 : Summable (fun k : PeriodicFrequency ι => if k=0 then (1:ℝ) else 0) := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_singleton (0 : PeriodicFrequency ι)).subset
    intro k hk
    by_contra hn
    have hz : k≠0 := by simpa only [Set.mem_singleton_iff] using hn
    simpa only [Function.mem_support,hz,↓reduceIte,ne_self_iff_false] using hk
  apply (h0.add hs).of_nonneg_of_le (fun k => (Real.exp_pos _).le)
  intro k
  by_cases hk : k=0
  · subst k
    simp [periodicFrequencyVector_zero,C]
  · simp only [hk,↓reduceIte,zero_add]
    exact periodic_gaussian_inverse_power_bound a _ ha (periodicFrequency_norm_pos hk) _

lemma periodic_integer_shift_square (m : ℤ) (x : ℝ) (hx : |x|≤1/2) :
    (m:ℝ)^2/4≤(x+(m:ℝ))^2 := by
  by_cases hm : m=0
  · subst m;simp only [Int.cast_zero,zero_pow (by omega : 2≠0),zero_div,add_zero];positivity
  have hm' : m≤-1 ∨ 1≤m := by omega
  have hxx := abs_le.mp hx
  rcases hm' with h | h
  · have hr : (m:ℝ)≤-1 := by exact_mod_cast h
    have hp : (x+(m:ℝ))≤(m:ℝ)/2 := by linarith
    nlinarith [sq_nonneg (x+(m:ℝ)/2)]
  · have hr : (1:ℝ)≤m := by exact_mod_cast h
    have hp : (m:ℝ)/2≤x+(m:ℝ) := by linarith
    nlinarith [sq_nonneg (x+(m:ℝ)/2)]

lemma periodic_lattice_shift_norm_square (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (k : PeriodicFrequency ι) :
    ‖periodicFrequencyVector k‖^2/4 ≤ ‖x+periodicFrequencyVector k‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.add_apply,periodicFrequencyVector_apply]
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun i _ => periodic_integer_shift_square (k i) (x i) (hx i))

/-- Uniform small-scale domination of every nonzero lattice image on the
whole centered fundamental cube, including its boundary. -/
lemma periodic_nonzero_lattice_gaussian_bound (x : EuclideanSpace ℝ ι)
    (hx : ∀ i,|x i|≤1/2) (k : PeriodicFrequency ι) (hk : k≠0)
    (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    Real.exp (-‖x+periodicFrequencyVector k‖^2/(2*t^2)) ≤
      Real.exp (-(1:ℝ)/(16*t^2))*Real.exp (-‖periodicFrequencyVector k‖^2/16) := by
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hn := periodicFrequency_norm_sq_ge_one hk
  have hs := periodic_lattice_shift_norm_square x hx k
  have ht2 : 0<t^2 := sq_pos_of_pos ht
  have ht2' : t^2≤1 := by nlinarith
  apply (div_le_iff₀ (by positivity : 0<2*t^2)).mpr
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left ht2' (sq_nonneg ‖periodicFrequencyVector k‖)]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicFrequency_norm_sq_ge_one
#print axioms DGRHS.Periodic.periodic_gaussian_inverse_power_bound
#print axioms DGRHS.Periodic.summable_periodicGaussian
#print axioms DGRHS.Periodic.periodic_integer_shift_square
#print axioms DGRHS.Periodic.periodic_lattice_shift_norm_square
#print axioms DGRHS.Periodic.periodic_nonzero_lattice_gaussian_bound
#check @DGRHS.Periodic.periodic_nonzero_lattice_gaussian_bound
