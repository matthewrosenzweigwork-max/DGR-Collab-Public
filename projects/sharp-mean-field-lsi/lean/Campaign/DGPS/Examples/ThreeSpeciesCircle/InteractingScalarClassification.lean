import DGPS.Examples.ThreeSpeciesCircle.InteractingMinimizerGraphEntry
import DGPS.Examples.ThreeSpeciesCircle.InteractingBranchRotation
import DGPS.Examples.ThreeSpeciesCircle.InteractingChartLogEuler
import DGPS.Examples.ThreeSpeciesCircle.InteractingChartDistinctness
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarAttainment
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarSmooth

/-! Actual exact-three GLOBAL scalar classification. ONE retained interacting
C3 packet is selected before coupling and drift. Positive candidate gaps come
from actual seed entropy/continuity. An actual attained minimum identifies the
common production rate; no candidate minimum is a premise. -/

noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem classified_chart_law (h : ℝ) (u : PeriodicC2_STR02969) (ρ : AbsoluteDensity 1)
    (hae : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ)=rhoT_STR02901 h u.val (angSec θ)) :
    densityMeasure ρ=densityMeasure (interactingChartAbsolute h u) := by
  apply Subtype.ext
  apply (densityMeasure_eq_iff_STR02901 _ _).2
  have he := (ae_comp_angEquiv_iff (p:=fun θ =>
    ρ.density (angEquiv.symm θ)=rhoT_STR02901 h u.val (angSec θ))).2 hae
  filter_upwards [he] with x hx
  have hc := interactingChartAbsolute_density h u (angEquiv x)
  simpa only [MeasurableEquiv.symm_apply_apply] using hx.trans hc.symm

private theorem classified_candidate_quotient {h ε : ℝ} (hh : 0<h) (hε : 0<ε)
    (he : ε<epsMax h) (b : AbsoluteDrift (modelData h ε)) (u : PeriodicC2_STR02969)
    (γ : ℝ) (q : ENNReal) (hq : q≠⊤) (hparam : a0*(1+γ)=q.toReal)
    (hF : interactingChartDeficit h (ε,γ,u)=0)
    (hG : 0<scalarGap (modelData h ε) (interactingChartAbsolute h u)) :
    scalarQuotient (modelData h ε) b (interactingChartAbsolute h u)=q := by
  let ξ := interactingChartAbsolute h u
  have hn := interactingChartAbsolute_deficit hh γ ε u
  rw [hF,mul_zero,hparam] at hn
  have hd := elementaryModel_scalar_deficit_real hh hε he b ξ q.toReal
  rw [←hn] at hd
  have hD : (scalarDissipation (modelData h ε) b ξ).toReal=
      2*q.toReal*(scalarGap (modelData h ε) ξ:ℝ) := by linarith
  have hdfin := (elementaryModel_scalarDissipation_real h ε b ξ).1
  have hden0 : 2*(scalarGap (modelData h ε) ξ:ENNReal)≠0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast hG.ne')
  have hqfin : scalarQuotient (modelData h ε) b ξ≠⊤ :=
    ENNReal.div_ne_top hdfin hden0
  suffices hr : (scalarQuotient (modelData h ε) b ξ).toReal = q.toReal by
    rw [← ENNReal.ofReal_toReal hqfin, ← ENNReal.ofReal_toReal hq, hr]
  unfold scalarQuotient
  rw [ENNReal.toReal_div,ENNReal.toReal_mul,ENNReal.toReal_ofNat,ENNReal.coe_toReal,hD]
  have hgreal : 0<(scalarGap (modelData h ε) ξ:ℝ) := by exact_mod_cast hG
  field_simp [hgreal.ne']
  <;> ring

/-- One threshold at fixed h precedes EVERY drift and EVERY original scalar
minimizer. Exactly three distinct actual probability laws attain the global
positive-gap infimum, with genuine smooth positive canonical representatives
and the actual third-turn relation. The reverse classification covers every
original H1 representative of each law, including arbitrary null-set values. -/
theorem elementaryModel_scalar_exact_three_of_graph (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0<δ ∧ δ≤D.radius ∧ ∀ h : ℝ, 0<h → h<δ →
      ∃ ε0 : ℝ, 0<ε0 ∧ ε0≤epsMax h ∧ ∀ ε : ℝ, 0<ε → ε<ε0 →
        ∀ b : AbsoluteDrift (modelData h ε), ∃ ξ : Fin 3 → AbsoluteDensity 1,
          (∀ j, IsSmoothPeriodic (ξ j).sqrt ∧ ∀ x, 0<(ξ j).sqrt x) ∧
          Pairwise (fun i j => densityMeasure (ξ i)≠densityMeasure (ξ j)) ∧
          (∀ j x, (ξ j).density x=(ξ 0).density (x-pt ((j:ℕ)/3))) ∧
          (∀ j, 0<scalarGap (modelData h ε) (ξ j) ∧
            scalarQuotient (modelData h ε) b (ξ j)=scalarRate (modelData h ε) b) ∧
          ∀ ρ : AbsoluteDensity 1,
            (0<scalarGap (modelData h ε) ρ ∧
              scalarQuotient (modelData h ε) b ρ=scalarRate (modelData h ε) b) ↔
            ∃ j : Fin 3, densityMeasure ρ=densityMeasure (ξ j) := by
  classical
  obtain ⟨δB,hδB,hδBr,hbranches⟩ := interactingChart_same_witness_C3_branches D
  obtain ⟨δE,hδE,hδEr,hentry⟩ := elementaryModel_scalarMinimizer_retained_graph_entry D
  obtain ⟨δG,hδG,hδGr,hgradient⟩ := elementaryModel_scalarMinimizer_chartGradient_zero D
  obtain ⟨δA,hδA,hδAr,hattain⟩ := elementaryModel_scalar_attainment_of_graph D
  obtain ⟨δS,hδS,hδSr,hsmooth⟩ := elementaryModel_scalarMinimizer_smooth_representative D
  let δ := min δB (min δE (min δG (min δA δS)))
  have hδ : 0<δ := lt_min hδB (lt_min hδE (lt_min hδG (lt_min hδA hδS)))
  have hδr : δ≤D.radius := (min_le_left _ _).trans hδBr
  refine ⟨δ,hδ,hδr,fun h hh hsmall => ?_⟩
  have hhB : h<δB := hsmall.trans_le (min_le_left _ _)
  have hhE : h<δE := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhG : h<δG := hsmall.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hhA : h<δA := hsmall.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hhS : h<δS := hsmall.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨U,V,ψ,Z,η,r,hpacket,ρC3,hρC3,hC3⟩ := hbranches h hh hhB
  have hfields := hpacket
  simp only [forall_and] at hfields
  rcases hfields with ⟨hU,hV,hw0,hη,hr,hZ0,hψ,hZ,hψ0,hψV,hgraph,hbranch,hunique⟩
  have hbranch := fun j => (hpacket j).2.2.2.2.2.2.2.2.2.2.2.1
  have hunique := fun j => (hpacket j).2.2.2.2.2.2.2.2.2.2.2.2
  let p := fun j ε => (ε,h*Z j ε 0,h*Z j ε 1,h^2*Z j ε 2)
  let curve := fun j ε => (h*Z j ε 0) • cosC2_STR02915+(h*Z j ε 1) • sinC2_STR02915+
    (ψ j (p j ε) : PeriodicC2_STR02969)
  have hp0 (j : Fin 3) : (0,h*D.Z j h 0,h*D.Z j h 1,h^2*D.Z j h 2)∈U j := by
    have ht := (hbranch j 0 (by simpa using hη j)).1
    simpa only [hZ0 j] using ht
  have hcurve0 (j : Fin 3) : curve j 0=ordinaryHolderCaptureSeed D h j := by
    dsimp only [curve,p]
    rw [hZ0 j,hψ0 j]
    rfl
  have hcurveCont (j : Fin 3) : ContinuousAt (curve j) 0 := by
    have hzc : ContinuousAt (Z j) 0 := (hZ j).continuousOn.continuousAt
      (Ioo_mem_nhds (by linarith [hη j]) (hη j))
    have hc (i : Fin 3) : ContinuousAt (fun ε => Z j ε i) 0 :=
      (continuous_apply i).continuousAt.comp hzc
    have hpc : ContinuousAt (p j) 0 := by dsimp only [p]; fun_prop
    have hpsic : ContinuousAt (fun ε => ψ j (p j ε)) 0 :=
      ((hψ j).continuousOn.continuousAt ((hU j).mem_nhds
        (by simpa only [p,hZ0 j] using hp0 j))).comp hpc
    dsimp only [curve]
    exact ((((continuousAt_const.mul (hc 0)).smul continuousAt_const).add
      ((continuousAt_const.mul (hc 1)).smul continuousAt_const))).add
        (E_STR02969.subtypeL.continuous.continuousAt.comp hpsic)
  have hcurveMean (j : Fin 3) (ε : ℝ) : meanT_STR02901 (curve j ε).val=0 := by
    dsimp only [curve]
    rw [paramMap_val_STR02915]
    exact (meanT_uT_STR02924 _ _ (continuous_val_STR02924 _) (inE_of_mem_STR02924 _)).1
  obtain ⟨σ,hσ,hσpos,_,_,_,_⟩ := D.roots h hh (hsmall.trans_le hδr)
  have hseedVal (j : Fin 3) : (ordinaryHolderCaptureSeed D h j).val=
      chartU_STR02924 D.ψ h (D.Z j h) := by
    unfold ordinaryHolderCaptureSeed Lamp_STR02956 iota_STR02956
    rw [paramMap_val_STR02915]
    rfl
  have hseed (j : Fin 3) : ∀ᵐ θ ∂angHaar, (σ j).density (angEquiv.symm θ)=
      rhoT_STR02901 h (curve j 0).val (angSec θ) :=
    Eventually.of_forall fun θ => by rw [hcurve0 j,hseedVal j]; exact hσ j θ
  choose εGap hεGap hεGapMax hgap using fun j =>
    interactingChart_curve_positive_gap hh (σ j) (hσpos j) (curve j) (hcurveCont j) (hseed j)
  have hseedNE : Pairwise (fun i j => curve i 0≠curve j 0) := by
    intro i j hij
    rw [hcurve0 i,hcurve0 j]
    exact ordinaryHolderCaptureSeed_distinct D h hh (hsmall.trans_le hδr) hij
  obtain ⟨εD,hεD,hdistinct⟩ := interactingChart_curves_distinct curve h hcurveCont hseedNE hcurveMean
  obtain ⟨εE,hεE,hεEMax,henter⟩ := hentry h hh hhE U V r hU hp0 hV hw0 hr
  obtain ⟨εG,hεG,hεGMax,hgrad⟩ := hgradient h hh hhG
  obtain ⟨εA,hεA,hεAMax,ha⟩ := hattain h hh hhA
  obtain ⟨εS,mS,hεS,hεSMax,hmS,hs⟩ := hsmooth h hh hhS
  let εB := min (εGap 0) (min (εGap 1) (εGap 2))
  have hεB : 0<εB := lt_min (hεGap 0) (lt_min (hεGap 1) (hεGap 2))
  have hBGap (j : Fin 3) : εB≤εGap j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  let εR := min εD ρC3
  have hεR : 0<εR := lt_min hεD hρC3
  let ε0 := min εA (min εE (min εG (min εS (min εB εR))))
  have hε0 : 0<ε0 := lt_min hεA (lt_min hεE (lt_min hεG (lt_min hεS (lt_min hεB hεR))))
  have hε0Max : ε0≤epsMax h := (min_le_left _ _).trans hεAMax
  refine ⟨ε0,hε0,hε0Max,fun ε hε he b => ?_⟩
  have heA : ε<εA := he.trans_le (min_le_left _ _)
  have heRest := he.trans_le (min_le_right εA (min εE (min εG (min εS (min εB εR)))))
  have heE : ε<εE := heRest.trans_le (min_le_left _ _)
  have heRest2 := heRest.trans_le (min_le_right _ _)
  have heG : ε<εG := heRest2.trans_le (min_le_left _ _)
  have heRest3 := heRest2.trans_le (min_le_right _ _)
  have heS : ε<εS := heRest3.trans_le (min_le_left _ _)
  have heRest4 := heRest3.trans_le (min_le_right _ _)
  have heB : ε<εB := heRest4.trans_le (min_le_left _ _)
  have heR : ε<εR := heRest4.trans_le (min_le_right _ _)
  have heD : |ε|<εD := by rw [abs_of_pos hε]; exact heR.trans_le (min_le_left _ _)
  have heC3 : |ε|<ρC3 := by rw [abs_of_pos hε]; exact heR.trans_le (min_le_right _ _)
  have heMax : ε<epsMax h := he.trans_le hε0Max
  let ξ := fun j => interactingChartAbsolute h (curve j ε)
  have hGap (j : Fin 3) : 0<scalarGap (modelData h ε) (ξ j) :=
    hgap j ε hε (heB.trans_le (hBGap j))
  have hBranchF (j : Fin 3) : interactingChartDeficit h (ε,h^2*Z j ε 2,curve j ε)=0 :=
    (hbranch j ε (hC3 j ε heC3).1).2.2
  have hIdentify (ρ : AbsoluteDensity 1) (hρG : 0<scalarGap (modelData h ε) ρ)
      (hρmin : scalarQuotient (modelData h ε) b ρ=scalarRate (modelData h ε) b) :
      ∃ j : Fin 3, densityMeasure ρ=densityMeasure (ξ j) ∧
        (scalarRate (modelData h ε) b).toReal/a0-1=h^2*Z j ε 2 := by
    obtain ⟨j,u,hm,hu,hentryFacts⟩ := henter ε hε heE b ρ hρG hρmin
    let γ := (scalarRate (modelData h ε) b).toReal/a0-1
    let z : Fin 3 → ℝ := ![interactingChartCos u/h,interactingChartSin u/h,γ/h^2]
    let w := interactingChartComplement u hm
    obtain ⟨hpU,hwV,hzBall⟩ := hentryFacts
    have hz0 : h*z 0=interactingChartCos u := by change h*(interactingChartCos u/h)=_; field_simp [hh.ne']
    have hz1 : h*z 1=interactingChartSin u := by change h*(interactingChartSin u/h)=_; field_simp [hh.ne']
    have hz2 : h^2*z 2=γ := by change h^2*(γ/h^2)=_; field_simp [pow_ne_zero 2 hh.ne']
    have hrec : (h*z 0) • cosC2_STR02915+(h*z 1) • sinC2_STR02915+(w:PeriodicC2_STR02969)=u := by
      rw [hz0,hz1]
      exact interactingChart_reconstruct u hm
    have hG0 : interactingChartGradient h (ε,h^2*z 2,
        (h*z 0) • cosC2_STR02915+(h*z 1) • sinC2_STR02915+(w:PeriodicC2_STR02969))=0 := by
      rw [hrec,hz2]
      exact hgrad ε hε heG b ρ hρG hρmin u hu
    have hF0 : interactingChartDeficit h (ε,h^2*z 2,
        (h*z 0) • cosC2_STR02915+(h*z 1) • sinC2_STR02915+(w:PeriodicC2_STR02969))=0 := by
      rw [hrec,hz2]
      have ht := interactingChartDeficit_native hh γ ε u ρ hu
      have hrate : a0*(1+γ)=(scalarRate (modelData h ε) b).toReal := by
        dsimp only [γ]
        field_simp [a0_pos.ne']
        <;> ring
      rw [hrate,elementaryModel_scalarMinimizer_deficit_zero hh hε heMax b ρ hρG hρmin] at ht
      exact (mul_eq_zero.mp ht).resolve_left a0_pos.ne'
    obtain ⟨hzZ,hwψ⟩ := hunique j ε z w hpU hwV hzBall hG0 hF0
    have huCurve : u=curve j ε := by
      calc
        _=(h*z 0) • cosC2_STR02915+(h*z 1) • sinC2_STR02915+(w:PeriodicC2_STR02969) := hrec.symm
        _=curve j ε := by rw [hzZ,hwψ]
    refine ⟨j,?_,?_⟩
    · have hμ := classified_chart_law h u ρ hu
      rw [huCurve] at hμ
      exact hμ
    · change γ=h^2*Z j ε 2
      calc γ=h^2*z 2 := hz2.symm
           _=h^2*Z j ε 2 := by rw [hzZ]
  obtain ⟨ρmin,hminGap,hminQ⟩ := ha ε hε heA b
  obtain ⟨jmin,_,hminGamma⟩ := hIdentify ρmin hminGap hminQ
  have hrateFin : scalarRate (modelData h ε) b≠⊤ := by
    rw [←hminQ]
    exact ENNReal.div_ne_top (elementaryModel_scalarDissipation_real h ε b ρmin).1
      (mul_ne_zero (by norm_num) (by exact_mod_cast hminGap.ne'))
  have hRateParam (j : Fin 3) : a0*(1+h^2*Z j ε 2)=(scalarRate (modelData h ε) b).toReal := by
    have hcommon (i : Fin 3) := (hC3 i ε heC3).2.1
    have hminRate : a0*(1+h^2*Z jmin ε 2)=(scalarRate (modelData h ε) b).toReal := by
      rw [←hminGamma]
      field_simp [a0_pos.ne']
      <;> ring
    calc
      _=a0*(1+h^2*Z 0 ε 2) := by rw [hcommon j]
      _=a0*(1+h^2*Z jmin ε 2) := by rw [hcommon jmin]
      _=_ := hminRate
  have hMin (j : Fin 3) : scalarQuotient (modelData h ε) b (ξ j)=scalarRate (modelData h ε) b :=
    classified_candidate_quotient hh hε heMax b (curve j ε) (h^2*Z j ε 2)
      (scalarRate (modelData h ε) b) hrateFin (hRateParam j) (hBranchF j) (hGap j)
  have hSmooth (j : Fin 3) : IsSmoothPeriodic (ξ j).sqrt ∧ ∀ x, 0<(ξ j).sqrt x := by
    obtain ⟨v,hv,hae,_,_⟩ := hs ε hε heS b (ξ j) (hGap j) (hMin j)
    have hc := interactingChartAbsolute_positive_continuous h (curve j ε)
    have heq : (ξ j).sqrt=v := Measure.eq_of_ae_eq hae hc.1 hv.continuous_torus
    refine ⟨?_,hc.2⟩
    rw [heq]
    exact hv
  refine ⟨ξ,hSmooth,hdistinct ε heD,?_,fun j => ⟨hGap j,hMin j⟩,?_⟩
  · intro j x
    have hrot := (hC3 j ε heC3).2.2
    change (interactingChartAbsolute h (curve j ε)).density x=(interactingChartAbsolute h (curve 0 ε)).density _
    change curve j ε = interactingC2Translate (2 * Real.pi * ((j : ℕ) / 3)) (curve 0 ε) at hrot
    rw [hrot]
    exact interactingChartAbsolute_thirdTurn_density h j (curve 0 ε) x
  · intro ρ
    constructor
    · rintro ⟨hg,hq⟩
      obtain ⟨j,hμ,_⟩ := hIdentify ρ hg hq
      exact ⟨j,hμ⟩
    · rintro ⟨j,hμ⟩
      have hc := elementaryModel_scalar_measure_congr h ε b ρ (ξ j)
        (congrArg (fun μ : ProbabilityMeasure (Torus 1) => (μ:Measure (Torus 1))) hμ)
      exact ⟨by rw [hc.1]; exact hGap j,by rw [hc.2.2]; exact hMin j⟩

end DGPS.Examples.ThreeSpeciesCircle
