import DGRHS.Gaussian.PeriodicD1AbelFourier

/-! UNCOMPILED REPAIRED COPY (Claude complete physical d1 return, 2026-10-03).
Repairs: radius limit uses `tendsto_atTop_add_const_right` (`Tendsto.add_const` needs
an nhds limit) and an explicit `congr`; the two boundary-coefficient statements now
carry an inner `:ℝ` ascription so the value is a single cast `↑(1/(j+1)/2)`, matching
the limit form (previously leaf-wise casts, not defeq). Mathematical content unchanged;
consumer CircleKernel adjusted accordingly. Original header follows.
 Draft actual radial removal for each circle-log Fourier coefficient. The
concrete radius sequence stays above one half and below one. The single
collision is Haar-null and the domination is the proved logarithmic bound. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.Periodic

def periodicD1Radius (n : ℕ) : ℝ := 1-1/((n:ℝ)+2)

lemma periodicD1Radius_bounds (n : ℕ) : (1:ℝ)/2≤periodicD1Radius n ∧ periodicD1Radius n<1 := by
  have hn : (0:ℝ)≤n := Nat.cast_nonneg n
  have hp : (0:ℝ)<(n:ℝ)+2 := by linarith
  have hl : 1/((n:ℝ)+2)≤(1:ℝ)/2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hh := one_div_pos.mpr hp
  unfold periodicD1Radius
  constructor <;> linarith

lemma periodicD1Radius_tendsto : Tendsto periodicD1Radius atTop (𝓝 1) := by
  have hi : Tendsto (fun n : ℕ => ((n:ℝ)+2)⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right (C := (2:ℝ))
      (hf := tendsto_natCast_atTop_atTop))
  have h : Tendsto (fun n : ℕ => 1-((n:ℝ)+2)⁻¹) atTop (𝓝 ((1:ℝ)-0)) :=
    tendsto_const_nhds.sub hi
  rw [sub_zero] at h
  exact h.congr fun n => by rw [periodicD1Radius,one_div]

lemma periodicD1AbelCircle_coefficient_tendsto (m : ℤ) :
    Tendsto (fun n : ℕ => fourierCoeff
      (fun x : UnitAddCircle => (periodicD1AbelCircle (periodicD1Radius n) x:ℂ)) m)
      atTop (𝓝 (fourierCoeff (fun x : UnitAddCircle => (periodicD1AbelCircle 1 x:ℂ)) m)) := by
  simp only [fourierCoeff,smul_eq_mul]
  apply tendsto_integral_of_dominated_convergence
    (fun x : UnitAddCircle => Real.log 2+|periodicD1AbelCircle 1 x|)
  · intro n
    exact (fourier (-m)).continuous.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.measurable.comp
        (periodicD1AbelCircle_measurable (periodicD1Radius n))).aestronglyMeasurable
  · exact (integrable_const (Real.log 2)).add (periodicD1AbelCircle_integrable 1).abs
  · intro n
    filter_upwards [periodicD1_fourier_one_ne_one_ae] with x hx
    rw [norm_mul,show ‖fourier (-m) x‖=1 by simp [fourier_apply],one_mul,
      Complex.norm_real,Real.norm_eq_abs]
    exact periodicD1AbelCircle_domination _ (periodicD1Radius_bounds n).1
      (periodicD1Radius_bounds n).2.le x hx
  · filter_upwards [periodicD1_fourier_one_ne_one_ae] with x hx
    have ht := (periodicD1AbelCircle_boundary_tendsto x hx).comp periodicD1Radius_tendsto
    exact tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp ht)

lemma periodicD1_boundary_fourier_zero :
    fourierCoeff (fun x : UnitAddCircle => (periodicD1AbelCircle 1 x:ℂ)) 0=0 := by
  have h := periodicD1AbelCircle_coefficient_tendsto 0
  have he (n : ℕ) : fourierCoeff
      (fun x : UnitAddCircle => (periodicD1AbelCircle (periodicD1Radius n) x:ℂ)) 0=0 :=
    periodicD1AbelCircle_fourier_zero _ (by have := (periodicD1Radius_bounds n).1; linarith)
      (periodicD1Radius_bounds n).2
  simp only [he,tendsto_const_nhds_iff] at h
  exact h.symm

lemma periodicD1_boundary_fourier_positive (j : ℕ) :
    fourierCoeff (fun x : UnitAddCircle => (periodicD1AbelCircle 1 x:ℂ)) ((j:ℤ)+1)=
      (((1:ℝ)/((j:ℝ)+1)/2:ℝ):ℂ) := by
  have h := periodicD1AbelCircle_coefficient_tendsto ((j:ℤ)+1)
  have he (n : ℕ) : fourierCoeff
      (fun x : UnitAddCircle => (periodicD1AbelCircle (periodicD1Radius n) x:ℂ)) ((j:ℤ)+1)=
      (((periodicD1Radius n)^(j+1)/((j:ℝ)+1)/2:ℝ):ℂ) :=
    periodicD1AbelCircle_fourier_positive _ (by have := (periodicD1Radius_bounds n).1; linarith)
      (periodicD1Radius_bounds n).2 j
  simp only [he] at h
  have hl := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (((periodicD1Radius_tendsto.pow (j+1)).div_const ((j:ℝ)+1)).div_const 2)
  simp only [one_pow] at hl
  exact tendsto_nhds_unique h hl

lemma periodicD1_boundary_fourier_negative (j : ℕ) :
    fourierCoeff (fun x : UnitAddCircle => (periodicD1AbelCircle 1 x:ℂ)) (-((j:ℤ)+1))=
      (((1:ℝ)/((j:ℝ)+1)/2:ℝ):ℂ) := by
  have h := periodicD1AbelCircle_coefficient_tendsto (-((j:ℤ)+1))
  have he (n : ℕ) : fourierCoeff
      (fun x : UnitAddCircle => (periodicD1AbelCircle (periodicD1Radius n) x:ℂ)) (-((j:ℤ)+1))=
      (((periodicD1Radius n)^(j+1)/((j:ℝ)+1)/2:ℝ):ℂ) :=
    periodicD1AbelCircle_fourier_negative _ (by have := (periodicD1Radius_bounds n).1; linarith)
      (periodicD1Radius_bounds n).2 j
  simp only [he] at h
  have hl := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (((periodicD1Radius_tendsto.pow (j+1)).div_const ((j:ℝ)+1)).div_const 2)
  simp only [one_pow] at hl
  exact tendsto_nhds_unique h hl

end DGRHS.Periodic
