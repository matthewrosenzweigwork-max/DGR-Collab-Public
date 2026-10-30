import DGPS.Examples.PolynomialSpeciesScaledQuartic
import DGPS.Examples.PolynomialSpeciesScaledFactorOriginJets
import DGPS.Examples.PolynomialSpeciesScaledDeficitExpansion

/-! Identification of the actual fourth integral factor at zero, followed by
TRUE coefficient C2 convergence. Only positive-field value estimates are used
to identify the zero slice; no value error is differentiated. All statements
retain the supplied SAME Common graph, including any envelope held by callers. -/

noncomputable section
open Filter Topology NormedSpace Set
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem zero_slice_from_positive_values
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters)∈U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0=0)
    (hgraph : ∀ p∈U, polynomialRangeMap (p,ψ p)=0)
    (hzero : ∀ h s γ : ℝ, ((0,0,(h,s),γ) : PolynomialRangeParameters)∈U → ψ (0,0,(h,s),γ)=0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1,x.2,(0,0),0)) 0=0)
    {O : Set (ℝ × PolynomialScaledCoefficients)} (hO : IsOpen O)
    (h0O : ∀ c, ((0:ℝ),c)∈O) (hC : ContDiffOn ℝ ∞ (polynomialScaledDeficitFactor ψ) O)
    (hfactor : ∀ h c, (h,c)∈O → polynomialScaledDeficit ψ (h,c)=h^4*polynomialScaledDeficitFactor ψ (h,c))
    (c : PolynomialScaledCoefficients) :
    polynomialScaledDeficitFactor ψ (0,c)=polynomialScaledQuartic c := by
  let M := 1+|c.1|+|c.2.1|+|c.2.2.1|+|c.2.2.2|
  have hM : 1≤M := by dsimp only [M]; linarith [abs_nonneg c.1,abs_nonneg c.2.1,abs_nonneg c.2.2.1,abs_nonneg c.2.2.2]
  have hcA : |c.1|≤M := by dsimp only [M]; linarith [abs_nonneg c.2.1,abs_nonneg c.2.2.1,abs_nonneg c.2.2.2]
  have hcB : |c.2.1|≤M := by dsimp only [M]; linarith [abs_nonneg c.1,abs_nonneg c.2.2.1,abs_nonneg c.2.2.2]
  have hcα : |c.2.2.1|≤M := by dsimp only [M]; linarith [abs_nonneg c.1,abs_nonneg c.2.1,abs_nonneg c.2.2.2]
  have hcσ : |c.2.2.2|≤M := by dsimp only [M]; linarith [abs_nonneg c.1,abs_nonneg c.2.1,abs_nonneg c.2.2.1]
  obtain ⟨δ,K,hδ,hK,hvalue⟩ := polynomial_range_graph_scaled_deficit_expansion
    hU h0U hψ hψ0 hgraph hzero hfirst M hM
  have hcont : ContinuousAt (fun h : ℝ => polynomialScaledDeficitFactor ψ (h,c)) 0 := by
    have hi : ContinuousAt (fun h : ℝ => (h,c)) 0 := continuousAt_id.prodMk continuousAt_const
    have hf : ContinuousAt (polynomialScaledDeficitFactor ψ) ((0 : ℝ),c) :=
      (hC.contDiffAt (hO.mem_nhds (h0O c))).continuousAt
    have ht := hf.comp (f := fun h : ℝ => (h,c)) (x := (0 : ℝ)) hi
    exact ht
  have hmem : ∀ᶠ h : ℝ in 𝓝 0, (h,c)∈O :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto.eventually (hO.mem_nhds (h0O c))
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.1 hmem
  let r := min δ d/2
  have hr : 0<r := div_pos (lt_min hδ hd) (by norm_num)
  have hrδ : r≤δ := by dsimp only [r]; linarith [min_le_left δ d,lt_min hδ hd]
  have hrd : r<d := by dsimp only [r]; linarith [min_le_right δ d]
  let h := fun n : ℕ => r/((n:ℝ)+1)
  have hp (n : ℕ) : 0<h n := div_pos hr (by positivity)
  have hle (n : ℕ) : h n≤r := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).2
    nlinarith [mul_nonneg hr.le ((show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n))]
  have hsmall (n : ℕ) : (h n,c)∈O := hball (by
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (hp n)] using (hle n).trans_lt hrd)
  have hlim : Tendsto h atTop (𝓝 (0:ℝ)) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul r
    simpa only [h,mul_zero,div_eq_mul_inv,one_mul] using ht
  have hb (n : ℕ) : |polynomialScaledDeficitFactor ψ (h n,c)-polynomialScaledQuartic c|≤K*h n := by
    have he := hvalue c.1 c.2.1 c.2.2.2 c.2.2.1 (h n) hcA hcB hcσ hcα (hp n).le ((hle n).trans hrδ)
    change |polynomialScaledDeficit ψ (h n,c)-polynomialScaledQuartic c*(h n)^4|≤K*(h n)^5 at he
    rw [hfactor (h n) c (hsmall n)] at he
    have habs : |(h n)^4*polynomialScaledDeficitFactor ψ (h n,c)-polynomialScaledQuartic c*(h n)^4|=
        (h n)^4*|polynomialScaledDeficitFactor ψ (h n,c)-polynomialScaledQuartic c| := by
      calc
        _ = |(h n)^4*(polynomialScaledDeficitFactor ψ (h n,c)-polynomialScaledQuartic c)| := by congr 1 <;> ring
        _ = _ := by rw [abs_mul,abs_of_pos (pow_pos (hp n) 4)]
    rw [habs] at he
    have he' : (h n)^4*|polynomialScaledDeficitFactor ψ (h n,c)-polynomialScaledQuartic c|≤(h n)^4*(K*h n) :=
      he.trans_eq (by ring)
    exact (mul_le_mul_iff_right₀ (pow_pos (hp n) 4)).1 he'
  have hbLim : Tendsto (fun n => K*h n) atTop (𝓝 (0:ℝ)) := by simpa only [mul_zero] using hlim.const_mul K
  have hdiff : Tendsto (fun n => |polynomialScaledDeficitFactor ψ (h n,c)-polynomialScaledQuartic c|)
      atTop (𝓝 (0:ℝ)) := squeeze_zero (fun _ => abs_nonneg _) hb hbLim
  have hq : Tendsto (fun n => polynomialScaledDeficitFactor ψ (h n,c)) atTop (𝓝 (polynomialScaledQuartic c)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [Real.norm_eq_abs] using hdiff
  exact tendsto_nhds_unique (hcont.tendsto.comp hlim) hq

/-- ACTUAL explicit zero slice and uniform coefficient C2 limits on the SAME
supplied graph. Every hypothesis is factual Common data. There is NO jet,
coefficient, value-expansion, smooth factor or convergence premise. Callers
may retain every other property (in particular the envelope) of this ψ. -/
theorem polynomialScaledDeficitFactor_identified
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters)∈U) (hN : IsOpen N) (h0N : (0 : E_STR02969)∈N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0=0) (hψN : ∀ p∈U, ψ p∈N)
    (hgraph : ∀ p∈U, ∀ w∈N, polynomialRangeMap (p,w)=0 ↔ ψ p=w)
    (hzero : ∀ h s γ : ℝ, ((0,0,(h,s),γ) : PolynomialRangeParameters)∈U → ψ (0,0,(h,s),γ)=0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1,x.2,(0,0),0)) 0=0) :
    ∃ O : Set (ℝ × PolynomialScaledCoefficients), IsOpen O ∧ (∀ c, ((0:ℝ),c)∈O) ∧
      O⊆polynomialScaledParameters ⁻¹' U ∧ ContDiffOn ℝ ∞ (polynomialScaledDeficitFactor ψ) O ∧
      (∀ h c, (h,c)∈O → polynomialScaledDeficit ψ (h,c)=h^4*polynomialScaledDeficitFactor ψ (h,c)) ∧
      (∀ c, polynomialScaledDeficitFactor ψ (0,c)=polynomialScaledQuartic c) ∧
      ∀ K : Set PolynomialScaledCoefficients, IsCompact K →
        TendstoUniformlyOn (fun h c => polynomialScaledDeficitFactor ψ (h,c)) polynomialScaledQuartic (𝓝 (0:ℝ)) K ∧
        TendstoUniformlyOn (fun h c => fderiv ℝ (fun z => polynomialScaledDeficitFactor ψ (h,z)) c)
          (fderiv ℝ polynomialScaledQuartic) (𝓝 (0:ℝ)) K ∧
        TendstoUniformlyOn (fun h c => fderiv ℝ (fderiv ℝ (fun z => polynomialScaledDeficitFactor ψ (h,z))) c)
          (fderiv ℝ (fderiv ℝ polynomialScaledQuartic)) (𝓝 (0:ℝ)) K := by
  obtain ⟨O,hO,h0O,hC,hfactor,_,hlim⟩ := polynomialScaledDeficit_factor_of_origin_jets hU h0U hψ
    (polynomialScaledDeficit_origin_jets hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst)
  have hR : ∀ p∈U, polynomialRangeMap (p,ψ p)=0 := fun p hp => (hgraph p hp _ (hψN p hp)).2 rfl
  have hz : ∀ c, polynomialScaledDeficitFactor ψ (0,c)=polynomialScaledQuartic c :=
    zero_slice_from_positive_values hU h0U hψ hψ0 hR hzero hfirst hO h0O hC hfactor
  have hzfun : (fun c => polynomialScaledDeficitFactor ψ (0,c))=polynomialScaledQuartic := funext hz
  have hΩ : IsOpen (polynomialScaledParameters ⁻¹' U) := hU.preimage (by unfold polynomialScaledParameters; fun_prop)
  have h0Ω : ∀ c, ((0:ℝ),c)∈polynomialScaledParameters ⁻¹' U := by
    intro c
    simpa [polynomialScaledParameters, (show (0 : PolynomialRangeParameters) = (0,0,(0,0),0) from rfl)] using h0U
  refine ⟨O∩polynomialScaledParameters ⁻¹' U,hO.inter hΩ,
    fun c => ⟨h0O c,h0Ω c⟩,Set.inter_subset_right,hC.mono Set.inter_subset_left,
    fun h c hp => hfactor h c hp.1,hz,?_⟩
  intro K hK
  simpa only [hzfun] using hlim K hK

/-- Pointwise zero-slice identification, without reselecting the caller's graph. -/
theorem polynomialScaledDeficitFactor_zero
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters)∈U) (hN : IsOpen N) (h0N : (0 : E_STR02969)∈N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0=0) (hψN : ∀ p∈U, ψ p∈N)
    (hgraph : ∀ p∈U, ∀ w∈N, polynomialRangeMap (p,w)=0 ↔ ψ p=w)
    (hzero : ∀ h s γ : ℝ, ((0,0,(h,s),γ) : PolynomialRangeParameters)∈U → ψ (0,0,(h,s),γ)=0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1,x.2,(0,0),0)) 0=0)
    (c : PolynomialScaledCoefficients) : polynomialScaledDeficitFactor ψ (0,c)=polynomialScaledQuartic c := by
  obtain ⟨_,_,_,_,_,_,hz,_⟩ := polynomialScaledDeficitFactor_identified
    hU h0U hN h0N hψ hψ0 hψN hgraph hzero hfirst
  exact hz c

end DGPS.Examples.PolynomialSpecies
