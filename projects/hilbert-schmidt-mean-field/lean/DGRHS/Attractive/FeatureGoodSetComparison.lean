/- Source2718–2746: proper good/bad-set CS comparison. Actual Taylor fourth
moments instantiate delta properness and the bad-set probability downstream. -/
import DGRHS.Attractive.FeatureGoodSet
import DGRHS.CLT.PartitionComparison
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive

lemma positive_power_good_bad_comparison {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (A B : Ω → ℝ) (N : ℕ)
    (G : Set Ω) (hG : MeasurableSet G)
    (hA : ∀ᵐ ω ∂ν,0<A ω)
    (hpow : MemLp (fun ω => A ω^N) 2 ν)
    (hB : MemLp (fun ω => Real.exp (B ω)) 2 ν)
    (hδ : MemLp (G.indicator (fun ω => (N:ℝ)*Real.log (A ω)-B ω)) 2 ν) :
    |(∫ ω,A ω^N ∂ν)-(∫ ω,Real.exp (B ω) ∂ν)| ≤
      (Real.sqrt (∫ ω,(G.indicator (fun ω => (N:ℝ)*Real.log (A ω)-B ω) ω)^2 ∂ν)+
        Real.sqrt (ν.real Gᶜ))*
      (Real.sqrt (∫ ω,(A ω^N)^2 ∂ν)+Real.sqrt (∫ ω,Real.exp (B ω)^2 ∂ν)) := by
  classical
  let δ := G.indicator (fun ω => (N:ℝ)*Real.log (A ω)-B ω)
  let J : Ω → ℝ := Gᶜ.indicator (fun _ => 1)
  have hd : MemLp (fun ω => |δ ω|) 2 ν := by
    simpa only [Real.norm_eq_abs] using hδ.norm
  have hj : MemLp J 2 ν := memLp_indicator_const 2 hG.compl 1 (Or.inr (measure_ne_top _ _))
  let H := fun ω => |δ ω|+J ω
  let F := fun ω => A ω^N
  let Q := fun ω => Real.exp (B ω)
  have hH : MemLp H 2 ν := hd.add hj
  have hFQ : MemLp (fun ω => F ω+Q ω) 2 ν := hpow.add hB
  have hprod := hH.integrable_mul hFQ
  have hpoint : ∀ᵐ ω ∂ν,|F ω-Q ω|≤H ω*(F ω+Q ω) := by
    filter_upwards [hA] with ω ha
    by_cases hg : ω∈G
    · simpa only [H,δ,J,F,Q,Set.indicator_of_mem hg,
        Set.indicator_of_notMem (show ω∉Gᶜ by simpa using hg),add_zero] using
        source_good_set_power_difference (A ω) (B ω) N ha
    · have hb : |F ω-Q ω| ≤ |F ω|+|Q ω| := by
        simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (F ω) (-Q ω)
      have hf : 0≤F ω := pow_nonneg ha.le _
      have hq : 0≤Q ω := (Real.exp_pos _).le
      simpa only [H,δ,J,Set.indicator_of_notMem hg,
        Set.indicator_of_mem (show ω∈Gᶜ from hg),abs_zero,zero_add,one_mul,
        abs_of_nonneg hf,abs_of_nonneg hq] using hb
  have hInt : |(∫ ω,F ω ∂ν)-(∫ ω,Q ω ∂ν)| ≤
      ‖hH.toLp H‖*‖hFQ.toLp (fun ω => F ω+Q ω)‖ := by
    calc
      _ = |∫ ω,F ω-Q ω ∂ν| := by
        rw [integral_sub (hpow.integrable (by norm_num)) (hB.integrable (by norm_num))]
      _ ≤ ∫ ω,|F ω-Q ω| ∂ν := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun ω => F ω-Q ω) (μ := ν)
      _ ≤ ∫ ω,H ω*(F ω+Q ω) ∂ν :=
        integral_mono_ae ((hpow.integrable (by norm_num)).sub
          (hB.integrable (by norm_num))).norm hprod hpoint
      _ ≤ _ := DGRHS.CLT.integral_mul_le_toLp_norms hH hFQ
  have hhn : ‖hH.toLp H‖ ≤ ‖hd.toLp (fun ω => |δ ω|)‖+‖hj.toLp J‖ := by
    rw [show hH.toLp H=hd.toLp (fun ω => |δ ω|)+hj.toLp J by
      exact MemLp.toLp_add hd hj]
    exact norm_add_le _ _
  have hqn : ‖hFQ.toLp (fun ω => F ω+Q ω)‖ ≤
      ‖hpow.toLp F‖+‖hB.toLp Q‖ := by
    rw [show hFQ.toLp (fun ω => F ω+Q ω)=hpow.toLp F+hB.toLp Q by
      exact MemLp.toLp_add hpow hB]
    exact norm_add_le _ _
  have hji : (∫ ω,J ω^2 ∂ν)=ν.real Gᶜ := by
    have he : (fun ω => J ω^2)=J := by
      funext ω
      by_cases hg : ω∈Gᶜ <;> simp [J,hg]
    rw [he]
    exact integral_indicator_one hG.compl
  have hf := mul_le_mul hhn hqn (norm_nonneg _) (by positivity)
  apply hInt.trans
  apply hf.trans_eq
  rw [DGRHS.CLT.toLp_norm_eq_sqrt_second_moment hd,
    DGRHS.CLT.toLp_norm_eq_sqrt_second_moment hj,
    DGRHS.CLT.toLp_norm_eq_sqrt_second_moment hpow,
    DGRHS.CLT.toLp_norm_eq_sqrt_second_moment hB,hji]
  simp only [sq_abs]
  rfl

end DGRHS.Attractive
#print axioms DGRHS.Attractive.positive_power_good_bad_comparison
#check @DGRHS.Attractive.positive_power_good_bad_comparison
