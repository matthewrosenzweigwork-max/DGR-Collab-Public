import DGRHS.Gaussian.PeriodicHeatMellinWeight

/-! Exact Laplace transform of the translated, cut-off Mellin weight.
Translation is justified against actual Lebesgue measure; the Gamma integral
uses the pinned native proper integral theorem. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace DGRHS.Periodic

lemma periodic_integral_Ioi_translate (f : ℝ → ℝ) (τ : ℝ) :
    (∫ s : ℝ in Ioi τ,f s) = ∫ s : ℝ in Ioi 0,f (s+τ) := by
  calc
    _ = ∫ s : ℝ,(Ioi τ).indicator f s := (integral_indicator measurableSet_Ioi).symm
    _ = ∫ s : ℝ,(Ioi τ).indicator f (s+τ) := (integral_add_right_eq_self _ τ).symm
    _ = ∫ s : ℝ,(Ioi 0).indicator (fun s => f (s+τ)) s := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun s => by
        dsimp only
        by_cases hs : 0<s
        · rw [indicator_of_mem (show s+τ∈Ioi τ by change τ<s+τ;linarith),indicator_of_mem (show s∈Ioi 0 from hs)]
        · rw [indicator_of_notMem (show s+τ∉Ioi τ by change ¬τ<s+τ;linarith),indicator_of_notMem (show s∉Ioi 0 from hs)])
    _ = _ := integral_indicator measurableSet_Ioi

lemma periodicHeatMellinWeight_laplace (p τ q : ℝ) (hp : -1<p) (hτ : 0≤τ) (hq : 0<q) :
    (∫ s : ℝ in Ioi 0,periodicHeatMellinWeight p τ s*Real.exp (-(q*s))) =
      Real.exp (-(q*τ))*((1/q)^(p+1)*Real.Gamma (p+1)) := by
  have he : (fun s : ℝ => periodicHeatMellinWeight p τ s*Real.exp (-(q*s))) =
      (Ioi τ).indicator (fun s : ℝ => (s-τ)^p*Real.exp (-(q*s))) := by
    funext s
    by_cases hs : s∈Ioi τ <;> simp only [periodicHeatMellinWeight,
      indicator_apply,hs,ite_true,ite_false,zero_mul]
  rw [he,integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hτ),periodic_integral_Ioi_translate]
  calc
    _ = ∫ s : ℝ in Ioi 0,Real.exp (-(q*τ))*(s^p*Real.exp (-(q*s))) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun s => by
        dsimp only
        rw [add_sub_cancel_right,show -(q*(s+τ))=-(q*τ)+-(q*s) by ring,Real.exp_add]
        ring)
    _ = Real.exp (-(q*τ))*(∫ s : ℝ in Ioi 0,s^p*Real.exp (-(q*s))) := integral_const_mul _ _
    _ = _ := by
      congr 1
      simpa only [add_sub_cancel_right] using
        Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p+1) (r := q) (by linarith) hq

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeatMellinWeight_laplace
#check @DGRHS.Periodic.periodicHeatMellinWeight_laplace
