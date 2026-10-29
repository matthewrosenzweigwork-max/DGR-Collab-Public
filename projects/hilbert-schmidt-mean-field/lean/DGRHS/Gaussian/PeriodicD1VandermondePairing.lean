import DGRHS.Gaussian.PeriodicD1GoodNormalization
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.Complex.Basic

/-! Uncompiled candidate. Pair the directed Good factors into the
literal nonnegative squared Vandermonde. The identity holds at collisions too;
only the nonzero unit-modulus circle coordinates are used in the algebra. -/
noncomputable section
open scoped BigOperators Classical
namespace DGRHS.Periodic
universe u v
variable {ι : Type u} [LinearOrder ι]

lemma periodicD1_directed_pair_product {M : Type v} [CommMonoid M]
    (s : Finset ι) (f : ι × ι → M) :
    (∏ p∈(s×ˢs).filter (fun p => p.1≠p.2),f p)=
      ∏ p∈(s×ˢs).filter (fun p => p.1<p.2),f p*f p.swap := by
  let d := (s×ˢs).filter (fun p => p.1≠p.2)
  let t := (s×ˢs).filter (fun p => p.1<p.2)
  have ht : d.filter (fun p => p.1<p.2)=t := by
    ext p
    simp only [d,t,Finset.mem_filter,Finset.mem_product]
    constructor
    · rintro ⟨⟨h,hne⟩,hp⟩
      exact ⟨h,hp⟩
    · rintro ⟨h,hp⟩
      exact ⟨⟨h,ne_of_lt hp⟩,hp⟩
  have hs : (∏ p∈d.filter (fun p => ¬p.1<p.2),f p)=∏ p∈t,f p.swap := by
    apply Finset.prod_equiv (Equiv.prodComm ι ι)
    · intro p
      simp only [d,t,Finset.mem_filter,Finset.mem_product,Equiv.prodComm_apply]
      constructor
      · rintro ⟨⟨⟨hi,hj⟩,hne⟩,hnot⟩
        exact ⟨⟨hj,hi⟩,lt_of_le_of_ne (le_of_not_gt hnot) hne.symm⟩
      · rintro ⟨⟨hj,hi⟩,hp⟩
        exact ⟨⟨⟨hi,hj⟩,hp.ne'⟩,not_lt_of_ge hp.le⟩
    · intro p hp
      rfl
  change (∏p∈d,f p)=∏p∈t,f p*f p.swap
  rw [←Finset.prod_filter_mul_prod_filter_not d (fun p => p.1<p.2) f,ht,hs,
    Finset.prod_mul_distrib]

lemma periodicD1_circle_pair_factor (z w : ℂ) (hz : ‖z‖=1) (hw : ‖w‖=1) :
    (1-z/w)*(1-w/z)=(‖z-w‖^2:ℝ) := by
  have hw0 : w≠0 := by intro h;simpa [h] using hw
  have hn : ‖z/w‖=1 := by simp [norm_div,hz,hw]
  have he : 1-w/z=starRingEnd ℂ (1-z/w) := by
    rw [map_sub,map_one,←Complex.inv_eq_conj hn,inv_div]
  have hd : 1-z/w=(w-z)/w := by field_simp [hw0]
  rw [he,Complex.mul_conj',hd,norm_div,hw,div_one,norm_sub_rev]
  norm_cast

def periodicD1VandermondeSquared (s : Finset ι) (z : ι → ℂ) : ℝ :=
  ∏ p∈(s×ˢs).filter (fun p => p.1<p.2),‖z p.1-z p.2‖^2

lemma periodicD1VandermondeSquared_nonneg (s : Finset ι) (z : ι → ℂ) :
    0≤periodicD1VandermondeSquared s z := by
  exact Finset.prod_nonneg (fun _ _ => sq_nonneg _)

lemma periodicD1GoodWeight_constant_directed (s : Finset ι) (z : ι → ℂ) (m : ℕ) :
    periodicD1GoodWeight s (fun _ => m) z=
      (∏ p∈(s×ˢs).filter (fun p => p.1≠p.2),(1-z p.1/z p.2))^m := by
  rw [periodicD1GoodWeight,Finset.prod_pow]
  congr 1
  symm
  exact Finset.prod_finset_product' ((s×ˢs).filter (fun p => p.1≠p.2))
    s (fun i => s.erase i) (f := fun i j => (1:ℂ)-z i/z j) (by
    intro p
    simp only [Finset.mem_filter,Finset.mem_product,Finset.mem_erase]
    constructor
    · rintro ⟨⟨hi,hj⟩,hne⟩
      exact ⟨hi,hne.symm,hj⟩
    · rintro ⟨hi,hne,hj⟩
      exact ⟨⟨hi,hj⟩,hne.symm⟩)

/-- Actual nonnegative squared-Vandermonde power; no injectivity assumption. -/
theorem periodicD1GoodWeight_eq_vandermonde (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i∈s,‖z i‖=1) (m : ℕ) :
    periodicD1GoodWeight s (fun _ => m) z=(periodicD1VandermondeSquared s z:ℂ)^m := by
  rw [periodicD1GoodWeight_constant_directed,periodicD1_directed_pair_product]
  congr 1
  rw [periodicD1VandermondeSquared,Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro p hp
  have hm := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
  exact periodicD1_circle_pair_factor _ _ (hz _ hm.1) (hz _ hm.2)

end DGRHS.Periodic
