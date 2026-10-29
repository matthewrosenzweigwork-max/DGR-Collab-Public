import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Tactic

/-! RECORDS-ONLY UNCOMPILED DRAFT. Normalized integer Gamma multiplication,
following the exact native Bohr-Mollerup doubling argument. The normalization
at1 removes the need for a Stirling/pi prefactor. No multiplication formula
is assumed. Native source/pin/license retained in the D1 Gamma records. -/
noncomputable section
open Set
open scoped BigOperators
namespace DGRHS.Periodic

def periodicD1GammaMultiplicationProduct (N : ℕ) (x : ℝ) : ℝ :=
  ∏ j∈Finset.range N,Real.Gamma ((x+(j:ℝ))/(N:ℝ))

def periodicD1NormalizedGammaMultiplication (N : ℕ) (x : ℝ) : ℝ :=
  (N:ℝ)^(x-1)*periodicD1GammaMultiplicationProduct N x /
    periodicD1GammaMultiplicationProduct N 1

lemma periodicD1GammaMultiplication_argument_pos (N : ℕ) (hN : 0<N)
    (x : ℝ) (hx : 0<x) (j : ℕ) : 0<(x+(j:ℝ))/(N:ℝ) :=
  div_pos (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg _)) (Nat.cast_pos.mpr hN)

lemma periodicD1GammaMultiplicationProduct_pos (N : ℕ) (hN : 0<N)
    (x : ℝ) (hx : 0<x) : 0<periodicD1GammaMultiplicationProduct N x := by
  exact Finset.prod_pos (fun j _ => Real.Gamma_pos_of_pos
    (periodicD1GammaMultiplication_argument_pos N hN x hx j))

lemma periodicD1GammaMultiplicationProduct_add_one (N : ℕ) (hN : 0<N)
    (x : ℝ) (hx : 0<x) : periodicD1GammaMultiplicationProduct N (x+1)=
      (x/(N:ℝ))*periodicD1GammaMultiplicationProduct N x := by
  have hN0 : (N:ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  have hshift : (∏j∈Finset.range N,Real.Gamma ((x+((j+1:ℕ):ℝ))/(N:ℝ)))=
      periodicD1GammaMultiplicationProduct N (x+1) := by
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    push_cast
    ring
  have h := Finset.prod_range_succ' (fun j : ℕ => Real.Gamma ((x+(j:ℝ))/(N:ℝ))) N
  rw [Finset.prod_range_succ,hshift] at h
  have h0 : 0<x/(N:ℝ) := div_pos hx (Nat.cast_pos.mpr hN)
  have he : (x+(N:ℝ))/(N:ℝ)=x/(N:ℝ)+1 := by field_simp [hN0]
  rw [he,Real.Gamma_add_one h0.ne'] at h
  simp only [Nat.cast_zero,add_zero] at h
  apply mul_right_cancel₀ (Real.Gamma_pos_of_pos h0).ne'
  calc
    _ = periodicD1GammaMultiplicationProduct N x *
        (x/(N:ℝ)*Real.Gamma (x/(N:ℝ))) := h.symm
    _ = _ := by ring

lemma periodicD1NormalizedGammaMultiplication_one (N : ℕ) (hN : 0<N) :
    periodicD1NormalizedGammaMultiplication N 1=1 := by
  simp [periodicD1NormalizedGammaMultiplication,
    (periodicD1GammaMultiplicationProduct_pos N hN 1 zero_lt_one).ne']

lemma periodicD1NormalizedGammaMultiplication_pos (N : ℕ) (hN : 0<N)
    (x : ℝ) (hx : 0<x) : 0<periodicD1NormalizedGammaMultiplication N x := by
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _)
    (periodicD1GammaMultiplicationProduct_pos N hN x hx))
      (periodicD1GammaMultiplicationProduct_pos N hN 1 zero_lt_one)

lemma periodicD1NormalizedGammaMultiplication_add_one (N : ℕ) (hN : 0<N)
    (x : ℝ) (hx : 0<x) : periodicD1NormalizedGammaMultiplication N (x+1)=
      x*periodicD1NormalizedGammaMultiplication N x := by
  unfold periodicD1NormalizedGammaMultiplication
  rw [periodicD1GammaMultiplicationProduct_add_one N hN x hx,
    show x+1-1=(x-1)+1 by ring,Real.rpow_add (Nat.cast_pos.mpr hN),Real.rpow_one]
  field_simp [(Nat.cast_pos.mpr hN).ne']

lemma periodicD1NormalizedGammaMultiplication_log (N : ℕ) (hN : 0<N)
    (x : ℝ) (hx : 0<x) :
    Real.log (periodicD1NormalizedGammaMultiplication N x)=
      (x-1)*Real.log (N:ℝ) +
        (∑j∈Finset.range N,Real.log (Real.Gamma ((x+(j:ℝ))/(N:ℝ))))-
          Real.log (periodicD1GammaMultiplicationProduct N 1) := by
  rw [periodicD1NormalizedGammaMultiplication,
    Real.log_div (mul_ne_zero (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _).ne'
      (periodicD1GammaMultiplicationProduct_pos N hN x hx).ne')
      (periodicD1GammaMultiplicationProduct_pos N hN 1 zero_lt_one).ne',
    Real.log_mul (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _).ne'
      (periodicD1GammaMultiplicationProduct_pos N hN x hx).ne',
    Real.log_rpow (Nat.cast_pos.mpr hN)]
  congr 1
  congr 1
  exact Real.log_prod (fun j _ => (Real.Gamma_pos_of_pos
    (periodicD1GammaMultiplication_argument_pos N hN x hx j)).ne')

lemma periodicD1NormalizedGammaMultiplication_log_convex (N : ℕ) (hN : 0<N) :
    ConvexOn ℝ (Ioi 0) (Real.log ∘ periodicD1NormalizedGammaMultiplication N) := by
  refine convexOn_iff_forall_pos.mpr ⟨convex_Ioi _,?_⟩
  intro x hx y hy a b ha hb hab
  have hxy : 0<a*x+b*y := add_pos (mul_pos ha hx) (mul_pos hb hy)
  have hterm (j : ℕ) :
      Real.log (Real.Gamma (((a*x+b*y)+(j:ℝ))/(N:ℝ)))≤
        a*Real.log (Real.Gamma ((x+(j:ℝ))/(N:ℝ)))+
        b*Real.log (Real.Gamma ((y+(j:ℝ))/(N:ℝ))) := by
    have hconv := (convexOn_iff_forall_pos.mp Real.convexOn_log_Gamma).2
    have hh := hconv
      (periodicD1GammaMultiplication_argument_pos N hN x hx j)
      (periodicD1GammaMultiplication_argument_pos N hN y hy j) ha hb hab
    simp only [Function.comp_apply,smul_eq_mul] at hh
    convert hh using 1
    congr 2
    have hb' : b=1-a := by linarith
    rw [hb']
    ring
  have hsum := Finset.sum_le_sum (fun j (_ : j∈Finset.range N) => hterm j)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  simp only [Function.comp_apply,smul_eq_mul]
  rw [periodicD1NormalizedGammaMultiplication_log N hN _ hxy,
    periodicD1NormalizedGammaMultiplication_log N hN x hx,
    periodicD1NormalizedGammaMultiplication_log N hN y hy]
  have hb' : b=1-a := by linarith
  rw [hb'] at hsum ⊢
  nlinarith only [hsum]

/-- Actual normalized Gamma multiplication, by native Bohr-Mollerup uniqueness. -/
theorem periodicD1NormalizedGammaMultiplication_eq_Gamma (N : ℕ) (hN : 0<N)
    (x : ℝ) (hx : 0<x) : periodicD1NormalizedGammaMultiplication N x=Real.Gamma x := by
  exact Real.eq_Gamma_of_log_convex
    (periodicD1NormalizedGammaMultiplication_log_convex N hN)
    (fun {y} hy => periodicD1NormalizedGammaMultiplication_add_one N hN y hy)
    (fun {y} hy => periodicD1NormalizedGammaMultiplication_pos N hN y hy)
    (periodicD1NormalizedGammaMultiplication_one N hN) hx

/-- The form used in the Beta-product moment, with sharp positive Gamma arguments. -/
theorem periodicD1_Gamma_multiplication_normalized (N : ℕ) (hN : 0<N)
    (s : ℝ) (hs : 0<1+(N:ℝ)*s) :
    (N:ℝ)^((N:ℝ)*s)*
      (∏j∈Finset.range N,Real.Gamma (s+((j:ℝ)+1)/(N:ℝ)))/
      (∏j∈Finset.range N,Real.Gamma (((j:ℝ)+1)/(N:ℝ)))=
        Real.Gamma (1+(N:ℝ)*s) := by
  have h := periodicD1NormalizedGammaMultiplication_eq_Gamma N hN
    (1+(N:ℝ)*s) hs
  unfold periodicD1NormalizedGammaMultiplication periodicD1GammaMultiplicationProduct at h
  have hnum (j : ℕ) : (1+(N:ℝ)*s+(j:ℝ))/(N:ℝ)=s+((j:ℝ)+1)/(N:ℝ) := by
    field_simp [(Nat.cast_pos.mpr hN).ne'] <;> ring
  have hden (j : ℕ) : (1+(j:ℝ))/(N:ℝ)=((j:ℝ)+1)/(N:ℝ) := by ring
  rw [show 1+(N:ℝ)*s-1=(N:ℝ)*s by ring] at h
  simp_rw [hnum,hden] at h
  exact h

end DGRHS.Periodic
