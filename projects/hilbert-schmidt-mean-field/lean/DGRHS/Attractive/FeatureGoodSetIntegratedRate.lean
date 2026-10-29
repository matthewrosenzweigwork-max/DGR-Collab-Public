/- Source2705–2746: combine the genuine Taylor fourth-deviation, Markov,
good-set logarithmic moment and CS bounds. This supporting estimate uses
actual coefficient moments and actual second moments. The true source field
must instantiate them; this is not an original paper theorem by itself. -/
import DGRHS.Attractive.FeatureGoodSetComparison
import DGRHS.Attractive.FeatureGoodSetDeltaMoments
import DGRHS.Attractive.FeatureGoodSetMoments
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive

lemma source_taylor_fourth_deviation_integrable {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (A B R E : Ω → ℝ) (n : ℝ) (hn : 1≤n)
    (hA : Measurable A)
    (hB4 : Integrable (fun ω => B ω^4) ν)
    (hR4 : Integrable (fun ω => R ω^4) ν)
    (hE4 : Integrable (fun ω => E ω^4) ν)
    (htaylor : ∀ᵐ ω ∂ν,A ω=1+B ω/n+R ω/(n*Real.sqrt n)+E ω/n^2) :
    Integrable (fun ω => |A ω-1|^4) ν ∧
      (∫ ω,|A ω-1|^4 ∂ν) ≤
        27/n^4*((∫ ω,B ω^4 ∂ν)+(∫ ω,R ω^4 ∂ν)+(∫ ω,E ω^4 ∂ν)) := by
  let S := fun ω => 27/n^4*(B ω^4+R ω^4+E ω^4)
  have hi : Integrable S ν := ((hB4.add hR4).add hE4).const_mul _
  have hd : ∀ᵐ ω ∂ν,|A ω-1|^4≤S ω := by
    filter_upwards [htaylor] with ω ht
    exact source_taylor_fourth_deviation (A ω) (B ω) (R ω) (E ω) n hn ht
  have hm : AEStronglyMeasurable (fun ω => |A ω-1|^4) ν :=
    ((continuous_abs.measurable.comp (hA.sub measurable_const)).stronglyMeasurable.pow 4).aestronglyMeasurable
  have hproper : Integrable (fun ω => |A ω-1|^4) ν := hi.mono' hm (by
    filter_upwards [hd] with ω hω
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg (A ω-1)) 4)]
    exact hω)
  refine ⟨hproper,?_⟩
  have hb := integral_mono_ae hproper hi hd
  change (∫ ω,|A ω-1|^4 ∂ν) ≤ (∫ ω,27/n^4*(B ω^4+R ω^4+E ω^4) ∂ν) at hb
  have hsum := integral_add (hB4.add hR4) hE4
  change (∫ ω,B ω^4+R ω^4+E ω^4 ∂ν) =
    (∫ ω,B ω^4+R ω^4 ∂ν)+(∫ ω,E ω^4 ∂ν) at hsum
  have hpair := integral_add hB4 hR4
  change (∫ ω,B ω^4+R ω^4 ∂ν) =
    (∫ ω,B ω^4 ∂ν)+(∫ ω,R ω^4 ∂ν) at hpair
  rw [integral_const_mul,hsum,hpair] at hb
  exact hb

lemma source_taylor_good_bad_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (A B R E : Ω → ℝ)
    (N : ℕ) (hN : 1≤N) (hA : Measurable A) (hB : Measurable B)
    (hApos : ∀ᵐ ω ∂ν,0<A ω)
    (hpow : MemLp (fun ω => A ω^N) 2 ν)
    (hexp : MemLp (fun ω => Real.exp (B ω)) 2 ν)
    (hR2 : Integrable (fun ω => R ω^2) ν)
    (hE2 : Integrable (fun ω => E ω^2) ν)
    (hB4 : Integrable (fun ω => B ω^4) ν)
    (hR4 : Integrable (fun ω => R ω^4) ν)
    (hE4 : Integrable (fun ω => E ω^4) ν)
    (htaylor : ∀ᵐ ω ∂ν,A ω=1+B ω/(N:ℝ)+R ω/((N:ℝ)*Real.sqrt N)+E ω/(N:ℝ)^2) :
    let M := (∫ ω,B ω^4 ∂ν)+(∫ ω,R ω^4 ∂ν)+(∫ ω,E ω^4 ∂ν)
    |(∫ ω,A ω^N ∂ν)-(∫ ω,Real.exp (B ω) ∂ν)| ≤
      (Real.sqrt (3*((∫ ω,R ω^2 ∂ν)/(N:ℝ)+
          (∫ ω,E ω^2 ∂ν)/(N:ℝ)^2+108*M/(N:ℝ)^2))+
        Real.sqrt (432*M/(N:ℝ)^4))*
      (Real.sqrt (∫ ω,(A ω^N)^2 ∂ν)+Real.sqrt (∫ ω,Real.exp (B ω)^2 ∂ν)) := by
  classical
  dsimp only
  let M := (∫ ω,B ω^4 ∂ν)+(∫ ω,R ω^4 ∂ν)+(∫ ω,E ω^4 ∂ν)
  let G : Set Ω := {ω | |A ω-1|≤1/2}
  let δ := G.indicator (fun ω => (N:ℝ)*Real.log (A ω)-B ω)
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have hd := source_taylor_fourth_deviation_integrable ν A B R E N hn hA hB4 hR4 hE4 htaylor
  have hD : Integrable (fun ω => (A ω-1)^4) ν := by
    simpa only [show (4:ℕ)=2*2 by rfl,pow_mul,sq_abs] using hd.1
  have hdelta := source_good_set_delta_proper_and_bound ν A B R E N hn0 hA hB hR2 hE2 hD htaylor
  have hG : MeasurableSet G :=
    measurableSet_le (continuous_abs.measurable.comp (hA.sub measurable_const)) measurable_const
  have hcompare := positive_power_good_bad_comparison ν A B N G hG hApos hpow hexp hdelta.1
  have hbad := source_bad_set_probability ν A hd.1
  have hGc : Gᶜ = {ω | 1/2 < |A ω-1|} := by
    ext ω
    simp only [G,Set.mem_compl_iff,Set.mem_setOf_eq,not_le]
  have hbad' : ν.real Gᶜ≤432*M/(N:ℝ)^4 := by
    rw [hGc]
    calc
      _ ≤ 16*(∫ ω,|A ω-1|^4 ∂ν) := hbad
      _ ≤ 16*(27/(N:ℝ)^4*M) := mul_le_mul_of_nonneg_left hd.2 (by norm_num)
      _ = _ := by ring
  have hdev : (∫ ω,(A ω-1)^4 ∂ν)≤27/(N:ℝ)^4*M := by
    simpa only [M,show (4:ℕ)=2*2 by rfl,pow_mul,sq_abs] using hd.2
  have hdelta' : (∫ ω,δ ω^2 ∂ν)≤
      3*((∫ ω,R ω^2 ∂ν)/(N:ℝ)+(∫ ω,E ω^2 ∂ν)/(N:ℝ)^2+
        108*M/(N:ℝ)^2) := by
    apply hdelta.2.trans
    have hh := mul_le_mul_of_nonneg_left hdev (show 0≤4*(N:ℝ)^2 by positivity)
    have he : 4*(N:ℝ)^2*(27/(N:ℝ)^4*M)=108*M/(N:ℝ)^2 := by
      field_simp [hn0.ne']
      <;> ring
    rw [he] at hh
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hh) (by norm_num)
  apply hcompare.trans
  apply mul_le_mul_of_nonneg_right
    (add_le_add (Real.sqrt_le_sqrt hdelta') (Real.sqrt_le_sqrt hbad'))
    (by positivity)

end DGRHS.Attractive
#check @DGRHS.Attractive.source_taylor_fourth_deviation_integrable
#check @DGRHS.Attractive.source_taylor_good_bad_integral_bound
#print axioms DGRHS.Attractive.source_taylor_fourth_deviation_integrable
#print axioms DGRHS.Attractive.source_taylor_good_bad_integral_bound
