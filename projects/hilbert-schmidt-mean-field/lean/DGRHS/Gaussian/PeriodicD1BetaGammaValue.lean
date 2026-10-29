import DGRHS.Gaussian.PeriodicD1BetaProduct
import DGRHS.Gaussian.PeriodicD1GammaMultiplication
import Mathlib.Algebra.BigOperators.Fin

/-! RECORDS-ONLY UNCOMPILED DRAFT. Derive the actual Beta-product Gamma quotient
by cancellation in the normalized Gamma multiplication theorem. Both imported
successors are themselves uncompiled records-only drafts. No circle-integral
identity or desired Mellin formula is supplied as a theorem hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
namespace DGRHS.Periodic

lemma periodicD1Beta_range_split (N : ℕ) (hN : 0<N) (f : ℝ → ℝ) :
    (∏j∈Finset.range N,f (((j:ℝ)+1)/(N:ℝ)))=
      (∏j : Fin (N-1),f (periodicD1BetaShape N j))*f 1 := by
  have he : N-1+1=N := Nat.sub_add_cancel hN
  have hr : (((N-1:ℕ):ℝ)+1)/(N:ℝ)=1 := by
    have hcast : ((N-1:ℕ):ℝ)+1=(N:ℝ) := by exact_mod_cast he
    rw [hcast,div_self (Nat.cast_pos.mpr hN).ne']
  calc
    _ = ∏j∈Finset.range (N-1+1),f (((j:ℝ)+1)/(N:ℝ)) := by rw [he]
    _ = (∏j∈Finset.range (N-1),f (((j:ℝ)+1)/(N:ℝ)))*
        f ((((N-1:ℕ):ℝ)+1)/(N:ℝ)) := Finset.prod_range_succ _ _
    _ = _ := by rw [hr,Finset.prod_range];rfl

lemma periodicD1Beta_one_add_pos (N : ℕ) (hN : 0<N) (s : ℝ)
    (hs : 0<1+(N:ℝ)*s) : 0<1+s := by
  by_cases hs0 : 0≤s
  · linarith
  · have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
    have hm := mul_le_mul_of_nonpos_right hN1 (le_of_not_ge hs0)
    simp only [one_mul] at hm
    linarith

lemma periodicD1Beta_gamma_denominator_ne_zero (N : ℕ) (hN : 0<N) :
    (∏j : Fin (N-1),Real.Gamma (periodicD1BetaShape N j))≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact (Real.Gamma_pos_of_pos (periodicD1BetaShape_bounds N hN j).1).ne'

/-- All omitted j=N factors and their Gamma(1+s) multiplicities are explicit. -/
lemma periodicD1Beta_gamma_product_value (N : ℕ) (hN : 0<N) (s : ℝ)
    (hs : 0<1+(N:ℝ)*s) :
    ((N:ℝ)^N)^s*(∏j : Fin (N-1),
      Real.Gamma (periodicD1BetaShape N j+s)/
        (Real.Gamma (periodicD1BetaShape N j)*Real.Gamma (1+s)))=
      Real.Gamma (1+(N:ℝ)*s)/(Real.Gamma (1+s))^N := by
  have hg := periodicD1_Gamma_multiplication_normalized N hN s hs
  rw [periodicD1Beta_range_split N hN (fun t => Real.Gamma (s+t)),
    periodicD1Beta_range_split N hN Real.Gamma,Real.Gamma_one,mul_one] at hg
  have hn : (∏j : Fin (N-1),Real.Gamma (s+periodicD1BetaShape N j))=
      ∏j : Fin (N-1),Real.Gamma (periodicD1BetaShape N j+s) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [add_comm]
  rw [hn,show s+1=1+s by ring] at hg
  have hg0 := (Real.Gamma_pos_of_pos (periodicD1Beta_one_add_pos N hN s hs)).ne'
  have hb0 := periodicD1Beta_gamma_denominator_ne_zero N hN
  have hp : (Real.Gamma (1+s))^N=(Real.Gamma (1+s))^(N-1)*Real.Gamma (1+s) := by
    calc
      _ = (Real.Gamma (1+s))^(N-1+1) := by rw [Nat.sub_add_cancel hN]
      _ = _ := pow_succ _ _
  rw [←Real.rpow_natCast_mul (Nat.cast_nonneg N) N s,
    Finset.prod_div_distrib,Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [←hg,hp]
  field_simp [hg0,hb0] <;> ring

/-- Proper real moments of the concrete complementary Beta product on the source domain. -/
theorem periodicD1BetaProductVariable_gamma_moment (N : ℕ) (hN : 0<N) (s : ℝ)
    (hs : 0<1+(N:ℝ)*s) :
    Integrable (fun x => (periodicD1BetaProductVariable N x)^s) (periodicD1BetaProductLaw N) ∧
      (∫x,(periodicD1BetaProductVariable N x)^s ∂periodicD1BetaProductLaw N)=
        Real.Gamma (1+(N:ℝ)*s)/(Real.Gamma (1+s))^N := by
  have h := periodicD1BetaProductVariable_moment N hN s hs
  exact ⟨h.1,h.2.trans (periodicD1Beta_gamma_product_value N hN s hs)⟩

end DGRHS.Periodic
