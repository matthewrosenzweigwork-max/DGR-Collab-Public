import DGRHS.Gaussian.PeriodicD1ParticleCoordinates
import DGRHS.Gaussian.PeriodicD1CircleMellin
import DGRHS.Gaussian.PeriodicSupercriticalPartition

/-! UNCOMPILED REPAIRED COPY (Claude complete physical d1 return, 2026-10-03):
`field_simp; ring` made robust to the new field_simp normal form; the
`(1 - a/b) = (b-a)/b` step proved by `sub_div, div_self`; explicit measurability
fallback added. Statements unchanged. Original header follows.
RECORDS-ONLY UNCOMPILED DRAFT. Actual ordered source Green energy is
converted to the squared circle Vandermonde, then the genuine proper Mellin
formula is transported to the original ENNReal partition. The imported circle
kernel, pairing, Beta/Gamma and Mellin successors are themselves uncompiled.
No desired integral formula is an explicit hypothesis. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical ENNReal
namespace DGRHS.Periodic

lemma periodicD1_directed_norm_product {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (z : ι → ℂ) :
    (∏p∈(s×ˢs).filter (fun p => p.1≠p.2),‖z p.1-z p.2‖)=
      periodicD1VandermondeSquared s z := by
  rw [periodicD1_directed_pair_product]
  apply Finset.prod_congr rfl
  intro p hp
  change ‖z p.1-z p.2‖*‖z p.2-z p.1‖=‖z p.1-z p.2‖^2
  rw [norm_sub_rev (z p.2) (z p.1)]
  ring

lemma periodicD1VandermondeSquared_pos {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (z : ι → ℂ) (hz : Function.Injective z) :
    0<periodicD1VandermondeSquared s z := by
  apply Finset.prod_pos
  intro p hp
  have hlt := (Finset.mem_filter.mp hp).2
  exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hz.ne hlt.ne))) 2

lemma periodicD1_log_vandermonde_ordered (N : ℕ) (z : Fin N → ℂ)
    (hz : Function.Injective z) :
    Real.log (periodicD1VandermondeSquared Finset.univ z)=
      ∑i : Fin N,∑j : Fin N,Real.log ‖z i-z j‖ := by
  have hn (p : Fin N × Fin N)
      (hp : p∈((Finset.univ : Finset (Fin N))×ˢFinset.univ).filter (fun p => p.1≠p.2)) :
      ‖z p.1-z p.2‖≠0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hz.ne (Finset.mem_filter.mp hp).2))
  rw [←periodicD1_directed_norm_product,Real.log_prod hn]
  calc
    _ = ∑i : Fin N,∑j∈(Finset.univ : Finset (Fin N)).erase i,Real.log ‖z i-z j‖ := by
      exact Finset.sum_finset_product'
        (((Finset.univ : Finset (Fin N))×ˢFinset.univ).filter (fun p => p.1≠p.2))
        Finset.univ (fun i => Finset.univ.erase i)
        (f := fun i j => Real.log ‖z i-z j‖) (by
          intro p
          simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_erase,Finset.mem_univ,
            true_and,and_true]
          exact ne_comm)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_erase _ (by simp)

lemma periodicD1_circle_difference_norm (x y : PeriodicTorus (Fin 1)) :
    ‖(1:ℂ)-fourier 1 ((x-y) 0)‖=‖fourier 1 (x 0)-fourier 1 (y 0)‖ := by
  have hy : ‖fourier 1 (y 0)‖=1 := by simp [fourier_apply]
  have hy0 : fourier 1 (y 0)≠0 := by
    intro h
    simp only [h,norm_zero] at hy
    exact zero_ne_one hy
  have hs := periodic_mFourier_argument_sub (periodicFirstFrequency (0:Fin 1)) x y
  simp only [periodic_mFourier_first] at hs
  have hd : (1:ℂ)-fourier 1 (x 0)/fourier 1 (y 0)=
      (fourier 1 (y 0)-fourier 1 (x 0))/fourier 1 (y 0) := by
    rw [sub_div,div_self hy0]
  rw [hs,←Complex.inv_eq_conj hy,←div_eq_mul_inv,hd,norm_div,hy,div_one,norm_sub_rev]

lemma periodicD1CircleKernel_sub (x y : PeriodicTorus (Fin 1)) :
    periodicD1CircleKernel (x-y)= -Real.log ‖fourier 1 (x 0)-fourier 1 (y 0)‖ := by
  unfold periodicD1CircleKernel periodicD1AbelCircle
  rw [Complex.ofReal_one,one_mul,periodicD1_circle_difference_norm]

lemma periodicD1_circle_ordered_sum (N : ℕ) (x : Fin N → PeriodicTorus (Fin 1))
    (hx : Function.Injective (periodicD1GoodNodes (periodicD1ParticleCoordinates N x))) :
    (∑i : Fin N,∑j : Fin N,if i=j then 0 else periodicD1CircleKernel (x i-x j))=
      -Real.log (periodicD1CircleVandermonde N (periodicD1ParticleCoordinates N x)) := by
  have hh := periodicD1_log_vandermonde_ordered N
    (periodicD1GoodNodes (periodicD1ParticleCoordinates N x)) hx
  calc
    _ = ∑i : Fin N,∑j : Fin N,
        -Real.log ‖periodicD1GoodNodes (periodicD1ParticleCoordinates N x) i-
          periodicD1GoodNodes (periodicD1ParticleCoordinates N x) j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i=j
      · simp only [hij,if_true,sub_self,norm_zero,Real.log_zero,neg_zero]
      · simp only [hij,if_false]
        exact periodicD1CircleKernel_sub (x i) (x j)
    _ = _ := by
      simp only [Finset.sum_neg_distrib,←hh,periodicD1CircleVandermonde]

/-- Literal source Gibbs density agrees AE with the actual Vandermonde power. -/
theorem periodicD1_particle_density_vandermonde_ae (β : ℝ) (N : ℕ) :
    (fun x => Real.exp (periodicParticleExponent (ι := Fin 1) β N x))=ᵐ[
      Measure.pi (fun _ : Fin N => periodicHaar (Fin 1))]
      fun x => (periodicD1CircleVandermonde N (periodicD1ParticleCoordinates N x))^
        (-β/(2*(N:ℝ))) := by
  filter_upwards [periodicD1_particle_exponent_circle_ae β N,
    periodicD1ParticleCoordinates_distinct_ae N] with x he hx
  have hp : 0<periodicD1CircleVandermonde N (periodicD1ParticleCoordinates N x) :=
    periodicD1VandermondeSquared_pos _ _ hx
  rw [he,periodicD1_circle_ordered_sum N x hx,Real.rpow_def_of_pos hp]
  congr 1
  ring

/-- Source exact Dyson partition, retaining the extended nonnegative integral.
Properness is derived from the explicit Beta-product Mellin theorem. -/
theorem periodicD1_attractive_partition_exact (β : ℝ) (hβ0 : 0≤β) (hβ : β<2)
    (N : ℕ) (hN : 0<N) :
    periodicAttractivePartition (ι := Fin 1) β N=
      ENNReal.ofReal (Real.Gamma (1-β/2)/(Real.Gamma (1-β/(2*(N:ℝ))))^N) := by
  let s : ℝ := -β/(2*(N:ℝ))
  have hn : (N:ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  have hs : 1+(N:ℝ)*s=1-β/2 := by
    dsimp [s]
    field_simp [hn] <;> ring
  have hm := periodicD1CircleVandermonde_real_moment N hN s (by rw [hs];linarith)
  have hp (x : Fin N → UnitAddCircle) : 0≤(periodicD1CircleVandermonde N x)^s :=
    Real.rpow_nonneg (periodicD1CircleVandermonde_bounds N x).1 s
  have hF : Measurable (fun x : Fin N → UnitAddCircle =>
      ENNReal.ofReal ((periodicD1CircleVandermonde N x)^s)) := by
    have hc := (periodicD1CircleVandermonde_continuous N).measurable
    first
    | exact (hc.pow_const s).ennreal_ofReal
    | fun_prop
  calc
    _ = ∫⁻x : Fin N → PeriodicTorus (Fin 1),
        ENNReal.ofReal ((periodicD1CircleVandermonde N (periodicD1ParticleCoordinates N x))^s)
        ∂Measure.pi (fun _ : Fin N => periodicHaar (Fin 1)) := by
      apply lintegral_congr_ae
      exact (periodicD1_particle_density_vandermonde_ae β N).mono
        (fun x h => congrArg ENNReal.ofReal h)
    _ = ∫⁻x : Fin N → UnitAddCircle,ENNReal.ofReal ((periodicD1CircleVandermonde N x)^s)
        ∂periodicHaar (Fin N) :=
      (periodicD1ParticleCoordinates_measurePreserving N).lintegral_comp hF
    _ = ENNReal.ofReal (∫x,(periodicD1CircleVandermonde N x)^s ∂periodicHaar (Fin N)) :=
      (ofReal_integral_eq_lintegral_ofReal hm.1 (Eventually.of_forall hp)).symm
    _ = _ := by
      rw [hm.2,hs]
      congr 2
      dsimp [s]
      rw [neg_div,←sub_eq_add_neg]

end DGRHS.Periodic
