import DGRHS.Gaussian.PeriodicD1AbelIntegrable

/-! UNCOMPILED REPAIRED COPY (Claude complete physical d1 return, 2026-10-03).
Repairs: nonexistent `tsum_eq_zero` replaced by termwise zero + `tsum_zero`; all
if-branches decided by explicit `if_pos`/`if_neg` (simp's `neg_add_rev` would break
the hypothesis forms). Statements unchanged. Original header follows.
 Draft termwise Fourier integration of the actual Abel circle logarithm.
The series is derived from native log, and absolute integrated summability is
proved. The explicit positive/negative mode series is not a supplied premise. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical
namespace DGRHS.Periodic

lemma periodicD1AbelCircle_fourier_expansion (r : ℝ) (hr0 : 0≤r) (hr : r<1) (m : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (periodicD1AbelCircle r x:ℂ)) m=
      ∑' n : ℕ, ((r^(n+1)/((n:ℝ)+1)/2:ℝ):ℂ)*
        ((if (n:ℤ)+1=m then 1 else 0)+(if -((n:ℤ)+1)=m then 1 else 0)) := by
  let F := fun (n : ℕ) (x : UnitAddCircle) =>
    fourier (-m) x*(((((r:ℂ)*fourier 1 x)^(n+1)/((n:ℂ)+1)).re:ℝ):ℂ)
  have hi (n : ℕ) : Integrable (F n) AddCircle.haarAddCircle := by
    have hc : Continuous (F n) := by unfold F; fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn (n : ℕ) (x : UnitAddCircle) : ‖F n x‖≤r^(n+1)/((n:ℝ)+1) := by
    dsimp only [F]
    rw [norm_mul,show ‖fourier (-m) x‖=1 by simp [fourier_apply],one_mul]
    exact periodicD1_abel_real_term_norm_le r hr0 n x
  have hs : Summable (fun n : ℕ => ∫ x,‖F n x‖ ∂AddCircle.haarAddCircle) := by
    apply (periodicD1_abel_coeff_summable r hr0 hr).of_nonneg_of_le
    · intro n
      exact integral_nonneg (fun x => norm_nonneg _)
    · intro n
      have h := integral_mono_ae (hi n).norm
        (integrable_const (r^(n+1)/((n:ℝ)+1))) (Eventually.of_forall (hn n))
      simpa only [integral_const,probReal_univ,one_smul] using h
  have he (n : ℕ) : (∫ x,F n x ∂AddCircle.haarAddCircle)=
      ((r^(n+1)/((n:ℝ)+1)/2:ℝ):ℂ)*
        ((if (n:ℤ)+1=m then 1 else 0)+(if -((n:ℤ)+1)=m then 1 else 0)) := by
    have hip : Integrable (fourier ((n:ℤ)+1) : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
      (fourier ((n:ℤ)+1)).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hin : Integrable (fourier (-((n:ℤ)+1)) : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
      (fourier (-((n:ℤ)+1))).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc
      _ = ((r^(n+1)/((n:ℝ)+1)/2:ℝ):ℂ)*
          fourierCoeff ((fun x : UnitAddCircle => fourier ((n:ℤ)+1) x)+
            (fun x => fourier (-((n:ℤ)+1)) x)) m := by
        simp only [F,periodicD1_abel_term_re,fourierCoeff,Pi.add_apply,smul_eq_mul,
          ←integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = _ := by
        rw [fourierCoeff.add hip hin]
        simp [fourierCoeff_fourier,Pi.single_apply,eq_comm]
  rw [fourierCoeff]
  simp only [smul_eq_mul,periodicD1AbelCircle_series r hr0 hr,Complex.ofReal_tsum,←tsum_mul_left]
  change (∫ x,∑' n,F n x ∂AddCircle.haarAddCircle)=_
  rw [←integral_tsum_of_summable_integral_norm hi hs]
  exact tsum_congr he

lemma periodicD1AbelCircle_fourier_zero (r : ℝ) (hr0 : 0≤r) (hr : r<1) :
    fourierCoeff (fun x : UnitAddCircle => (periodicD1AbelCircle r x:ℂ)) 0=0 := by
  rw [periodicD1AbelCircle_fourier_expansion r hr0 hr]
  have he (n : ℕ) : ((r^(n+1)/((n:ℝ)+1)/2:ℝ):ℂ)*
      ((if (n:ℤ)+1=0 then 1 else 0)+(if -((n:ℤ)+1)=0 then 1 else 0))=0 := by
    have hp : (n:ℤ)+1≠0 := by omega
    have hn : -((n:ℤ)+1)≠0 := by omega
    rw [if_neg hp,if_neg hn,add_zero,mul_zero]
  simp only [he,tsum_zero]

lemma periodicD1AbelCircle_fourier_positive (r : ℝ) (hr0 : 0≤r) (hr : r<1) (j : ℕ) :
    fourierCoeff (fun x : UnitAddCircle => (periodicD1AbelCircle r x:ℂ)) ((j:ℤ)+1)=
      ((r^(j+1)/((j:ℝ)+1)/2:ℝ):ℂ) := by
  rw [periodicD1AbelCircle_fourier_expansion r hr0 hr]
  have he (n : ℕ) : ((r^(n+1)/((n:ℝ)+1)/2:ℝ):ℂ)*
      ((if (n:ℤ)+1=(j:ℤ)+1 then 1 else 0)+(if -((n:ℤ)+1)=(j:ℤ)+1 then 1 else 0))=
      if n=j then ((r^(j+1)/((j:ℝ)+1)/2:ℝ):ℂ) else 0 := by
    have hn : -((n:ℤ)+1)≠(j:ℤ)+1 := by omega
    by_cases h : n=j
    · subst n
      rw [if_pos rfl,if_neg hn,if_pos rfl,add_zero,mul_one]
    · have hp : (n:ℤ)+1≠(j:ℤ)+1 := by omega
      rw [if_neg hp,if_neg hn,if_neg h,add_zero,mul_zero]
  simp only [he,tsum_ite_eq]

lemma periodicD1AbelCircle_fourier_negative (r : ℝ) (hr0 : 0≤r) (hr : r<1) (j : ℕ) :
    fourierCoeff (fun x : UnitAddCircle => (periodicD1AbelCircle r x:ℂ)) (-((j:ℤ)+1))=
      ((r^(j+1)/((j:ℝ)+1)/2:ℝ):ℂ) := by
  rw [periodicD1AbelCircle_fourier_expansion r hr0 hr]
  have he (n : ℕ) : ((r^(n+1)/((n:ℝ)+1)/2:ℝ):ℂ)*
      ((if (n:ℤ)+1=-((j:ℤ)+1) then 1 else 0)+(if -((n:ℤ)+1)=-((j:ℤ)+1) then 1 else 0))=
      if n=j then ((r^(j+1)/((j:ℝ)+1)/2:ℝ):ℂ) else 0 := by
    have hp : (n:ℤ)+1≠-((j:ℤ)+1) := by omega
    by_cases h : n=j
    · subst n
      rw [if_neg hp,if_pos rfl,if_pos rfl,zero_add,mul_one]
    · have hn : -((n:ℤ)+1)≠-((j:ℤ)+1) := by omega
      rw [if_neg hp,if_neg hn,if_neg h,add_zero,mul_zero]
  simp only [he,tsum_ite_eq]

end DGRHS.Periodic
