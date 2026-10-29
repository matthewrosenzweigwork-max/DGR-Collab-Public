/- Source2705–2744 moment arithmetic, genuine Markov probability and proper
CS from the already checked native L2 product interface. Concrete source
Taylor/field moments must instantiate these supporting inequalities. -/
import DGRHS.Attractive.FeatureGoodSet
import DGRHS.Concentration.MomentTail
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive

lemma sum_three_fourth_le (a b c : ℝ) :
    (a+b+c)^4 ≤ 27*(a^4+b^4+c^4) := by
  have h1 : (a+b+c)^2 ≤ 3*(a^2+b^2+c^2) := by
    nlinarith [sq_nonneg (a-b),sq_nonneg (b-c),sq_nonneg (c-a)]
  have h2 : (a^2+b^2+c^2)^2 ≤ 3*(a^4+b^4+c^4) := by
    nlinarith [sq_nonneg (a^2-b^2),sq_nonneg (b^2-c^2),sq_nonneg (c^2-a^2)]
  have h3 := pow_le_pow_left₀ (sq_nonneg (a+b+c)) h1 2
  nlinarith

lemma source_taylor_fourth_deviation (A B R E n : ℝ) (hn : 1≤n)
    (htaylor : A=1+B/n+R/(n*Real.sqrt n)+E/n^2) :
    |A-1|^4 ≤ 27/n^4*(B^4+R^4+E^4) := by
  have hn0 : 0<n := by linarith
  have hs : 1≤Real.sqrt n := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn
  have he : A-1 = B/n+R/(n*Real.sqrt n)+E/n^2 := by linarith
  rw [he,show |B/n+R/(n*Real.sqrt n)+E/n^2|^4 =
      (B/n+R/(n*Real.sqrt n)+E/n^2)^4 by
        rw [show (4:ℕ)=2*2 by rfl,pow_mul,sq_abs,pow_mul]]
  have h := sum_three_fourth_le (B/n) (R/(n*Real.sqrt n)) (E/n^2)
  have hs0 : 0<Real.sqrt n := by linarith
  have hR : (R/(n*Real.sqrt n))^4 ≤ R^4/n^4 := by
    rw [div_pow,mul_pow]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    simpa only [one_pow,mul_one] using mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hs 4) (pow_nonneg hn0.le 4)
  have hE : (E/n^2)^4 ≤ E^4/n^4 := by
    rw [div_pow]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact pow_le_pow_left₀ hn0.le (show n≤n^2 by nlinarith) 4
  rw [div_pow] at h
  apply h.trans
  calc
    _ ≤ 27*(B^4/n^4+R^4/n^4+E^4/n^4) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hR) hE) (by norm_num)
    _ = _ := by ring

lemma source_bad_set_probability {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (A : Ω → ℝ)
    (hi : Integrable (fun ω => |A ω-1|^4) ν) :
    ν.real {ω | 1/2 < |A ω-1|} ≤ 16*(∫ ω,|A ω-1|^4 ∂ν) := by
  have hm : ν.real {ω | 1/2 < |A ω-1|} ≤ ν.real {ω | 1/2 ≤ |A ω-1|} :=
    measureReal_mono (by
      intro ω h
      exact (show 1/2 < |A ω-1| from h).le)
  have h := DGRHS.Concentration.absolute_moment_markov ν (fun ω => A ω-1) 4 hi
    (1/2) (by norm_num)
  norm_num [div_eq_mul_inv] at h
  exact hm.trans (by simpa only [mul_comm] using h)

end DGRHS.Attractive
#print axioms DGRHS.Attractive.sum_three_fourth_le
#print axioms DGRHS.Attractive.source_taylor_fourth_deviation
#print axioms DGRHS.Attractive.source_bad_set_probability
