import DGPS.Examples.PolynomialSpeciesScaledFactor
import DGPS.Examples.PolynomialSpeciesOriginDeficitHessian
import DGPS.Examples.PolynomialSpeciesRangeCommon
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! ACTUAL lower field jets for the same graph's scaled physical deficit.
Amplitude Taylor's exact integral plus the actual zero origin amplitude
Hessian yields little-o of h squared. Genuine joint half-turn supplies the odd
jets. No fourth coefficient, value-error derivative or selected-root derivative
is assumed. -/

noncomputable section
open Filter Topology NormedSpace Set MeasureTheory
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private abbrev Amp := ℝ × ℝ
private abbrev Theta := (ℝ × ℝ) × ℝ
private abbrev Joint := Theta × Amp

local instance : NormedAddCommGroup (Amp →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (Amp →L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (Amp →L[ℝ] Amp →L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (Amp →L[ℝ] Amp →L[ℝ] ℝ) := inferInstance

private def jointValue (ψ : PolynomialRangeParameters → E_STR02969) (z : Joint) : ℝ :=
  polynomialReducedDeficit ψ (polynomialGapSlice z.1 z.2)
private def amplitudeHessian (ψ : PolynomialRangeParameters → E_STR02969) (z : Joint) :
    Amp →L[ℝ] Amp →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ (fun x => jointValue ψ (z.1,x))) z.2
private def jointParameters (z : Joint) : PolynomialRangeParameters := polynomialGapSlice z.1 z.2

private theorem jointParameters_smooth : ContDiff ℝ ∞ jointParameters := by
  exact contDiff_snd.fst.prodMk (contDiff_snd.snd.prodMk
    (contDiff_fst.fst.prodMk contDiff_fst.snd))

private theorem amplitudeHessian_continuousOn {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContinuousOn (amplitudeHessian ψ) (jointParameters ⁻¹' U) := by
  have hW : IsOpen (jointParameters ⁻¹' U) := hU.preimage jointParameters_smooth.continuous
  have hJ : ContDiffOn ℝ ∞ (jointValue ψ) (jointParameters ⁻¹' U) :=
    (polynomialReducedDeficit_smooth hψ).comp jointParameters_smooth.contDiffOn (fun _ hz => hz)
  intro z hz
  have hj : ContDiffAt ℝ ∞ (jointValue ψ) z := hJ.contDiffAt (hW.mem_nhds hz)
  let q := fun p : Joint × Amp => (p.1.1,p.2)
  have hq : ContDiff ℝ ∞ q := by dsimp only [q]; fun_prop
  have huncurry : ContDiffAt ℝ ∞ (Function.uncurry
      (fun (p : Joint) (x : Amp) => jointValue ψ (p.1,x))) (z,z.2) :=
    hj.comp (z,z.2) hq.contDiffAt
  have hD : ContDiffAt ℝ ∞ (fun p : Joint =>
      fderiv ℝ (fun x => jointValue ψ (p.1,x)) p.2) z :=
    ContDiffAt.fderiv huncurry contDiffAt_snd (by simp)
  have huncurryD : ContDiffAt ℝ ∞ (Function.uncurry
      (fun (p : Joint) (x : Amp) => fderiv ℝ (fun y => jointValue ψ (p.1,y)) x)) (z,z.2) :=
    by
    have ht := hD.comp (z,z.2) hq.contDiffAt
    exact ht
  have hh : ContDiffAt ℝ ∞ (amplitudeHessian ψ) z :=
    ContDiffAt.fderiv huncurryD contDiffAt_snd (by simp)
  exact hh.continuousAt.continuousWithinAt

/-- Genuine evenness on a local field neighborhood for EVERY fixed literal
coefficient, from the SAME graph's actual joint half-turn. -/
theorem polynomialScaledDeficit_even_near_origin
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters)∈U) (hN : IsOpen N) (h0N : (0 : E_STR02969)∈N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0=0) (hψN : ∀ p∈U, ψ p∈N)
    (hgraph : ∀ p∈U, ∀ w∈N, polynomialRangeMap (p,w)=0 ↔ ψ p=w)
    (c : PolynomialScaledCoefficients) :
    (fun h : ℝ => polynomialScaledDeficit ψ (-h,c)) =ᶠ[𝓝 (0:ℝ)]
      fun h => polynomialScaledDeficit ψ (h,c) := by
  obtain ⟨δ,hδ,heq⟩ := polynomial_reduced_deficit_half_turn hU h0U hN h0N hψ hψ0 hψN hgraph
  have hp : Continuous (fun h : ℝ => polynomialScaledParameters (h,c)) := by
    unfold polynomialScaledParameters
    fun_prop
  have hp0 : polynomialScaledParameters (0,c)=0 := by simp [polynomialScaledParameters]
  have hn : ∀ᶠ h : ℝ in 𝓝 0, ‖polynomialScaledParameters (h,c)‖<δ := by
    have ht := (hp.tendsto 0).norm
    rw [hp0,norm_zero] at ht
    exact ht.eventually (gt_mem_nhds hδ)
  filter_upwards [hn] with h hh
  have he := heq (h*c.1) (h*c.2.1) h (h^4*c.2.2.2) (h^2*c.2.2.1) hh
  simpa only [polynomialScaledDeficit, polynomialScaledParameters, neg_mul,
    (show Even (4:ℕ) by norm_num).neg_pow, even_two.neg_pow] using he

private theorem scaled_littleO_two
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters)∈U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0=0)
    (hzero : ∀ h s γ : ℝ, ((0,0,(h,s),γ) : PolynomialRangeParameters)∈U → ψ (0,0,(h,s),γ)=0)
    (hamp : fderiv ℝ (fun x : Amp => ψ (x.1,x.2,(0,0),0)) 0=0)
    (c : PolynomialScaledCoefficients) :
    (fun h : ℝ => polynomialScaledDeficit ψ (h,c)) =o[𝓝 (0:ℝ)] fun h => h^2 := by
  let a : Amp := (c.1,c.2.1)
  let q := fun h t : ℝ => ((((h,h^4*c.2.2.2),h^2*c.2.2.1),t • (h • a)) : Joint)
  have hW : IsOpen (jointParameters ⁻¹' U) := hU.preimage jointParameters_smooth.continuous
  have h0W : (0 : Joint)∈jointParameters ⁻¹' U := h0U
  have hA := amplitudeHessian_continuousOn hU hψ
  have hAc : ContinuousAt (amplitudeHessian ψ) (0 : Joint) := hA.continuousAt (hW.mem_nhds h0W)
  have hA0 : amplitudeHessian ψ 0=0 := by
    simpa only [amplitudeHessian,jointValue,polynomialReducedDeficit,polynomialGapSlice,
      Prod.fst_zero, Prod.snd_zero, zero_add,add_zero,mul_one, (show (0 : ℝ × ℝ) = (0,0) from rfl)] using
      polynomialReducedDeficit_amplitude_hessian_origin_zero hU h0U hψ hψ0 hamp
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  let d := ε/(1+‖a‖^2)
  have hd : 0<d := div_pos hε (by positivity)
  have hnear : ∀ᶠ z : Joint in 𝓝 0, z∈jointParameters ⁻¹' U ∧ ‖amplitudeHessian ψ z‖<d := by
    apply Filter.Eventually.and (hW.mem_nhds h0W)
    have hn := hAc.norm.tendsto
    rw [hA0,norm_zero] at hn
    exact hn.eventually (gt_mem_nhds hd)
  have hev : ∀ᶠ h : ℝ in 𝓝 0, ∀ t∈Icc (0:ℝ) 1,
      q h t∈jointParameters ⁻¹' U ∧ ‖amplitudeHessian ψ (q h t)‖<d := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t _
    have hq : Continuous (fun p : ℝ × ℝ => q p.1 p.2) := by dsimp only [q]; fun_prop
    have hq0 : q 0 t=0 := by simp [q]
    have ht : Tendsto (fun p : ℝ × ℝ => q p.1 p.2) (𝓝 ((0:ℝ),t)) (𝓝 (0:Joint)) := by
      simpa only [hq0] using hq.tendsto ((0:ℝ),t)
    exact ht.eventually hnear
  filter_upwards [hev] with h hh
  let θ : Theta := ((h,h^4*c.2.2.2),h^2*c.2.2.1)
  let x : Amp := h • a
  have hseg : ∀ t∈Icc (0:ℝ) 1, polynomialGapSlice θ (t • x)∈U := fun t ht => (hh t ht).1
  have hT := (polynomialReducedDeficit_quadratic_factor hU hψ hzero θ x hseg).2.2
  have hcont : ContinuousOn (fun t : ℝ => (1-t)*amplitudeHessian ψ (θ,t • x) x x) (Icc (0:ℝ) 1) := by
    have hc := hA.comp (by fun_prop : ContinuousOn (fun t : ℝ => (θ,t • x)) (Icc (0:ℝ) 1))
      (fun t ht => hseg t ht)
    exact (continuousOn_const.sub continuousOn_id).mul ((hc.clm_apply continuousOn_const).clm_apply continuousOn_const)
  have hb : ∀ t∈Set.uIoc (0:ℝ) 1,
      ‖(1-t)*amplitudeHessian ψ (θ,t • x) x x‖≤d*‖x‖^2 := by
    intro t ht
    have ht' : t∈Icc (0:ℝ) 1 := by
      have ht' : t∈Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
      exact ⟨ht'.1.le,ht'.2⟩
    have hm : ‖amplitudeHessian ψ (θ,t • x) x x‖≤d*‖x‖^2 := by
      calc
        _ ≤ ‖amplitudeHessian ψ (θ,t • x) x‖*‖x‖ := (amplitudeHessian ψ (θ,t • x) x).le_opNorm x
        _ ≤ (‖amplitudeHessian ψ (θ,t • x)‖*‖x‖)*‖x‖ :=
          mul_le_mul_of_nonneg_right ((amplitudeHessian ψ (θ,t • x)).le_opNorm x) (norm_nonneg x)
        _ ≤ (d*‖x‖)*‖x‖ := by gcongr; exact (hh t ht').2.le
        _ = _ := by ring
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht'.2)]
    exact (mul_le_mul_of_nonneg_right (by linarith [ht'.1] : 1-t≤1) (norm_nonneg _)).trans (by simpa using hm)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hb
  have he : polynomialScaledDeficit ψ (h,c)=polynomialReducedDeficit ψ (polynomialGapSlice θ x) := rfl
  dsimp only at hT
  rw [he,hT]
  change ‖∫ t in (0:ℝ)..1, (1-t)*amplitudeHessian ψ (θ,t • x) x x‖≤ε*‖h^2‖
  calc
    _ ≤ d*‖x‖^2 := by simpa only [sub_zero,abs_one,mul_one] using hbound
    _ = (d*‖a‖^2)*‖h^2‖ := by dsimp only [x]; rw [norm_smul,norm_pow]; ring
    _ ≤ ε*‖h^2‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      dsimp only [d]
      have hp : 0<1+‖a‖^2 := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hp).2
      nlinarith

private theorem second_jet_zero (f : ℝ → ℝ) (hf : ContDiffAt ℝ ∞ f 0)
    (hf0 : f 0=0) (hf1 : iteratedDeriv 1 f 0=0)
    (ho : f =o[𝓝 (0:ℝ)] fun h => h^2) : iteratedDeriv 2 f 0=0 := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.1
    ((hf.of_le (show (2:ℕ∞ω)≤∞ by simp)).eventually (by simp))
  have hfs : ContDiffOn ℝ (2:ℕ) f (Metric.ball 0 r) := fun h hh => (show ContDiffAt ℝ (2:ℕ) f h from hball hh).contDiffWithinAt
  have hT := taylor_isLittleO (f:=f) (x₀:=0) (n:=2) (s:=Metric.ball 0 r)
    (convex_ball 0 r) (Metric.mem_ball_self hr) hfs
  rw [nhdsWithin_eq_nhds.2 (Metric.ball_mem_nhds 0 hr)] at hT
  have he : (fun h => taylorWithinEval f 2 (Metric.ball 0 r) 0 h)=
      fun h : ℝ => ((1/2:ℝ)*iteratedDeriv 2 f 0)*h^2 := by
    funext h
    rw [taylor_within_apply]
    simp only [iteratedDerivWithin_of_isOpen Metric.isOpen_ball (Metric.mem_ball_self hr)]
    norm_num [Finset.sum_range_succ,iteratedDeriv_zero,hf0,hf1]
    ring
  have hT' : (fun h : ℝ => f h-taylorWithinEval f 2 (Metric.ball 0 r) 0 h)
      =o[𝓝 (0:ℝ)] fun h => h^2 := by simpa only [sub_zero] using hT
  have hcoef : (fun h : ℝ => ((1/2:ℝ)*iteratedDeriv 2 f 0)*h^2) =o[𝓝 (0:ℝ)] fun h => h^2 := by
    have ht := ho.sub hT'
    have hcancel : (fun h : ℝ => f h-(f h-taylorWithinEval f 2 (Metric.ball 0 r) 0 h)) =
        fun h : ℝ => ((1/2:ℝ)*iteratedDeriv 2 f 0)*h^2 := by
      funext h
      rw [show taylorWithinEval f 2 (Metric.ball 0 r) 0 h =
        ((1/2:ℝ)*iteratedDeriv 2 f 0)*h^2 from congrFun he h]
      ring
    rw [hcancel] at ht
    exact ht
  have ht := (hcoef.mono (show (𝓝[≠] (0:ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)).tendsto_div_nhds_zero
  have hev : (fun h : ℝ => (((1/2:ℝ)*iteratedDeriv 2 f 0)*h^2)/h^2) =ᶠ[𝓝[≠] (0:ℝ)]
      fun _ => (1/2:ℝ)*iteratedDeriv 2 f 0 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_div_cancel_right₀ _ (pow_ne_zero 2 hh)
  have hz := tendsto_nhds_unique (ht.congr' hev) tendsto_const_nhds
  linarith

/-- All lower field jets of the actual scaled physical deficit vanish for
EVERY literal independent coefficient, from actual graph and Hessian facts. -/
theorem polynomialScaledDeficit_origin_jets
    {U : Set PolynomialRangeParameters} {N : Set E_STR02969}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters)∈U) (hN : IsOpen N) (h0N : (0 : E_STR02969)∈N)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0=0) (hψN : ∀ p∈U, ψ p∈N)
    (hgraph : ∀ p∈U, ∀ w∈N, polynomialRangeMap (p,w)=0 ↔ ψ p=w)
    (hzero : ∀ h s γ : ℝ, ((0,0,(h,s),γ) : PolynomialRangeParameters)∈U → ψ (0,0,(h,s),γ)=0)
    (hamp : fderiv ℝ (fun x : Amp => ψ (x.1,x.2,(0,0),0)) 0=0) :
    ∀ c : PolynomialScaledCoefficients, ∀ j : ℕ, j≤3 →
      iteratedDeriv j (fun h : ℝ => polynomialScaledDeficit ψ (h,c)) 0=0 := by
  intro c
  let f := fun h : ℝ => polynomialScaledDeficit ψ (h,c)
  have hp : ContDiff ℝ ∞ (fun h : ℝ => (h,c)) := contDiff_id.prodMk contDiff_const
  have hΩ : IsOpen (polynomialScaledParameters ⁻¹' U) := hU.preimage (by unfold polynomialScaledParameters; fun_prop)
  have hmem : ((0:ℝ),c)∈polynomialScaledParameters ⁻¹' U := by
    simpa [polynomialScaledParameters] using (show ((0,0,(0,0),0) : PolynomialRangeParameters) ∈ U from h0U)
  have hf : ContDiffAt ℝ ∞ f 0 := by
    have ht := ((polynomialScaledDeficit_smooth hψ).contDiffAt (hΩ.mem_nhds hmem)).comp 0 hp.contDiffAt
    exact ht
  have he := polynomialScaledDeficit_even_near_origin hU h0U hN h0N hψ hψ0 hψN hgraph c
  have hf0 : f 0=0 := by
    simp only [f,polynomialScaledDeficit,polynomialScaledParameters,zero_mul,zero_pow (by norm_num : (4:ℕ)≠0),
      zero_pow (by norm_num : (2:ℕ)≠0),polynomialReducedDeficit, (show ψ (0,0,(0,0),0)=0 from hψ0),zero_smul,ZeroMemClass.coe_zero,
      zero_add,add_zero,mul_one,polynomialRangeDeficit_zero]
  have hodd (j : ℕ) (hj : Odd j) : iteratedDeriv j f 0=0 := by
    have hd := he.iteratedDeriv_eq j
    change iteratedDeriv j (fun h => f (-h)) 0 = iteratedDeriv j f 0 at hd
    rw [iteratedDeriv_comp_neg] at hd
    have hsign : (-1:ℝ)^j = -1 := hj.neg_one_pow
    simp only [neg_zero,hsign,smul_eq_mul,neg_one_mul] at hd
    change iteratedDeriv j f 0=0
    linarith
  have hf1 : iteratedDeriv 1 f 0=0 := hodd 1 (by norm_num)
  have hf2 : iteratedDeriv 2 f 0=0 :=
    second_jet_zero f hf hf0 hf1 (scaled_littleO_two hU h0U hψ hψ0 hzero hamp c)
  intro j hj
  interval_cases j
  · simpa only [iteratedDeriv_zero] using hf0
  · exact hf1
  · exact hf2
  · exact hodd 3 (by norm_num)

/-- ACTUAL smooth fourth-power factor and uniform C2 coefficient limits.
The SAME graph is supplied by the genuine Common producer. There is NO jet,
factor, coefficient, value-remainder, or derivative-remainder premise. The
explicit physical fourth coefficient is still a separate identification. -/
theorem exists_polynomial_common_graph_scaled_factor :
    ∃ (U : Set PolynomialRangeParameters) (N : Set E_STR02969)
      (ψ : PolynomialRangeParameters → E_STR02969),
      IsOpen U ∧ (0 : PolynomialRangeParameters)∈U ∧ IsOpen N ∧ (0 : E_STR02969)∈N ∧
      ContDiffOn ℝ ∞ ψ U ∧ (∀ p∈U, ψ p∈N) ∧
      (∀ p∈U, ∀ w∈N, polynomialRangeMap (p,w)=0 ↔ ψ p=w) ∧
      (∀ h s γ : ℝ, ((0,0,(h,s),γ) : PolynomialRangeParameters)∈U → ψ (0,0,(h,s),γ)=0) ∧
      fderiv ℝ (fun x : Amp => ψ (x.1,x.2,(0,0),0)) 0=0 ∧
      ∃ O : Set (ℝ × PolynomialScaledCoefficients), IsOpen O ∧
        (∀ c, ((0:ℝ),c)∈O) ∧ ContDiffOn ℝ ∞ (polynomialScaledDeficitFactor ψ) O ∧
        (∀ h c, (h,c)∈O → polynomialScaledDeficit ψ (h,c)=h^4*polynomialScaledDeficitFactor ψ (h,c)) ∧
        (∀ c, polynomialScaledDeficitFactor ψ (0,c)=
          iteratedDeriv 4 (fun h : ℝ => polynomialScaledDeficit ψ (h,c)) 0 / (Nat.factorial 4 : ℝ)) ∧
        ∀ K : Set PolynomialScaledCoefficients, IsCompact K →
          TendstoUniformlyOn (fun h c => polynomialScaledDeficitFactor ψ (h,c))
            (fun c => polynomialScaledDeficitFactor ψ (0,c)) (𝓝 (0:ℝ)) K ∧
          TendstoUniformlyOn (fun h c => fderiv ℝ (fun z => polynomialScaledDeficitFactor ψ (h,z)) c)
            (fderiv ℝ (fun z => polynomialScaledDeficitFactor ψ (0,z))) (𝓝 (0:ℝ)) K ∧
          TendstoUniformlyOn (fun h c => fderiv ℝ (fderiv ℝ (fun z => polynomialScaledDeficitFactor ψ (h,z))) c)
            (fderiv ℝ (fderiv ℝ (fun z => polynomialScaledDeficitFactor ψ (0,z)))) (𝓝 (0:ℝ)) K := by
  obtain ⟨U,N,ψ,δ,K,hU,h0U,hN,h0N,hψ,hψN,hgraph,hzero,hamp,_⟩ :=
    exists_polynomial_common_range_graph
  have hψ0 : ψ (0 : PolynomialRangeParameters)=0 := hzero 0 0 0 h0U
  refine ⟨U,N,ψ,hU,h0U,hN,h0N,hψ,hψN,hgraph,hzero,hamp,?_⟩
  exact polynomialScaledDeficit_factor_of_origin_jets hU h0U hψ
    (polynomialScaledDeficit_origin_jets hU h0U hN h0N hψ hψ0 hψN hgraph hzero hamp)

end DGPS.Examples.PolynomialSpecies
