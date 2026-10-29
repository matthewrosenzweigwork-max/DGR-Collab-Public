/- Source2710--2744: construct proper good-set logarithmic second moment
from actual Taylor coefficients and fourth deviation, before applying CS.
These are supporting implications; the source field construction supplies
the coefficient and remainder properness in the original theorem. -/
import DGRHS.Attractive.FeatureGoodSet
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive

lemma source_good_set_delta_sq (A B R E n : ℝ) (hn : 0<n)
    (htaylor : A=1+B/n+R/(n*Real.sqrt n)+E/n^2)
    (hgood : |A-1|≤1/2) :
    (n*Real.log A-B)^2 ≤
      3*(R^2/n+E^2/n^2+4*n^2*(A-1)^4) := by
  have hd := source_good_set_delta A B R E n hn htaylor hgood
  have hs : 0<Real.sqrt n := Real.sqrt_pos.mpr hn
  have hpow := pow_le_pow_left₀ (abs_nonneg _) hd 2
  have hsum : (|R|/Real.sqrt n+|E|/n+2*n*(A-1)^2)^2 ≤
      3*((|R|/Real.sqrt n)^2+(|E|/n)^2+(2*n*(A-1)^2)^2) := by
    nlinarith [sq_nonneg (|R|/Real.sqrt n-|E|/n),
      sq_nonneg (|E|/n-2*n*(A-1)^2),
      sq_nonneg (2*n*(A-1)^2-|R|/Real.sqrt n)]
  rw [sq_abs] at hpow
  apply hpow.trans
  convert hsum using 1
  simp only [div_pow,mul_pow,sq_abs,Real.sq_sqrt hn.le]
  ring

lemma source_good_set_delta_proper_and_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (A B R E : Ω → ℝ) (n : ℝ) (hn : 0<n)
    (hA : Measurable A) (hB : Measurable B)
    (hR : Integrable (fun ω => R ω^2) ν)
    (hE : Integrable (fun ω => E ω^2) ν)
    (hD : Integrable (fun ω => (A ω-1)^4) ν)
    (htaylor : ∀ᵐ ω ∂ν,A ω=1+B ω/n+R ω/(n*Real.sqrt n)+E ω/n^2) :
    let G : Set Ω := {ω | |A ω-1|≤1/2}
    let δ := G.indicator (fun ω => n*Real.log (A ω)-B ω)
    MemLp δ 2 ν ∧
      (∫ ω,δ ω^2 ∂ν) ≤ 3*((∫ ω,R ω^2 ∂ν)/n+
        (∫ ω,E ω^2 ∂ν)/n^2+4*n^2*(∫ ω,(A ω-1)^4 ∂ν)) := by
  classical
  dsimp only
  let G : Set Ω := {ω | |A ω-1|≤1/2}
  let δ := G.indicator (fun ω => n*Real.log (A ω)-B ω)
  let S := fun ω => 3*(R ω^2/n+E ω^2/n^2+4*n^2*(A ω-1)^4)
  have hG : MeasurableSet G :=
    measurableSet_le (continuous_abs.measurable.comp
      (hA.sub (measurable_const : Measurable (fun _ : Ω => (1:ℝ))))) measurable_const
  have hm : AEStronglyMeasurable δ ν :=
    (((hA.log.const_mul n).sub hB).indicator hG).aestronglyMeasurable
  have hi : Integrable S ν :=
    (((hR.div_const n).add (hE.div_const (n^2))).add
      (hD.const_mul (4*n^2))).const_mul 3
  have hd : ∀ᵐ ω ∂ν,δ ω^2≤S ω := by
    filter_upwards [htaylor] with ω ht
    by_cases hg : ω∈G
    · simpa only [δ,S,Set.indicator_of_mem hg] using
        source_good_set_delta_sq (A ω) (B ω) (R ω) (E ω) n hn ht hg
    · simp only [δ,Set.indicator_of_notMem hg,zero_pow,ne_eq,OfNat.ofNat_ne_zero,
        not_false_eq_true]
      dsimp only [S]
      positivity
  have hdi : Integrable (fun ω => δ ω^2) ν :=
    hi.mono' (hm.pow 2) (by
      filter_upwards [hd] with ω hω
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (δ ω))] using hω)
  refine ⟨(memLp_two_iff_integrable_sq hm).mpr hdi,?_⟩
  have hl := integral_mono_ae hdi hi hd
  have hsum := integral_add ((hR.div_const n).add (hE.div_const (n^2)))
    (hD.const_mul (4*n^2))
  change (∫ ω,R ω^2/n+E ω^2/n^2+4*n^2*(A ω-1)^4 ∂ν) =
    (∫ ω,R ω^2/n+E ω^2/n^2 ∂ν)+(∫ ω,4*n^2*(A ω-1)^4 ∂ν) at hsum
  have hpair := integral_add (hR.div_const n) (hE.div_const (n^2))
  change (∫ ω,R ω^2/n+E ω^2/n^2 ∂ν) =
    (∫ ω,R ω^2/n ∂ν)+(∫ ω,E ω^2/n^2 ∂ν) at hpair
  change (∫ ω,δ ω^2 ∂ν) ≤ (∫ ω,3*(R ω^2/n+E ω^2/n^2+
    4*n^2*(A ω-1)^4) ∂ν) at hl
  rw [integral_const_mul,hsum,hpair,integral_div,integral_div,integral_const_mul] at hl
  exact hl

end DGRHS.Attractive
#check @DGRHS.Attractive.source_good_set_delta_proper_and_bound
#print axioms DGRHS.Attractive.source_good_set_delta_sq
#print axioms DGRHS.Attractive.source_good_set_delta_proper_and_bound
