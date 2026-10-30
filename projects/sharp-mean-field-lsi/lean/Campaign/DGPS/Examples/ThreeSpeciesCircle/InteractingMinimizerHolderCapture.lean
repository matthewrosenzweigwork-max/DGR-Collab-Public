import DGPS.Examples.ThreeSpeciesCircle.InteractingMinimizerUniformLocalization
import DGPS.Examples.ThreeSpeciesCircle.InteractingLogDerivativeUpgrade
import DGPS.Examples.ThreeSpeciesCircle.InteractingPhysicalChartNorm
import DGPS.Examples.ThreeSpeciesCircle.InteractingChartLogProfile
import DGPS.Examples.ThreeSpeciesCircle.InteractingSmoothChart
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarRateLimit

/-! Uniform full-Holder capture of EVERY original H1 scalar minimizer at the
SAME retained ordinary graph. All root, rate, representative and differential
inputs come from actual model producers. There is no convergence, nearness,
regularity, or interacting graph-entry premise on the final factory. -/

noncomputable section
open MeasureTheory Filter Topology Set Function
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization DGPS.Analysis.PeriodicHolder

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Literal seed used by the retained interacting range/reduced graph. -/
def ordinaryHolderCaptureSeed (D : OrdinaryRootGraphData) (h : ℝ) (j : Fin 3) :
    PeriodicC2_STR02969 :=
  Lamp_STR02956 D.ψ (h,h^2*D.Z j h 2) (h*D.Z j h 0,h*D.Z j h 1)

private theorem capture_seed_val (D : OrdinaryRootGraphData) (h : ℝ) (j : Fin 3) :
    (ordinaryHolderCaptureSeed D h j).val = chartU_STR02924 D.ψ h (D.Z j h) := by
  unfold ordinaryHolderCaptureSeed Lamp_STR02956 iota_STR02956
  rw [paramMap_val_STR02915]
  rfl

private theorem capture_seed_mean (D : OrdinaryRootGraphData) (h : ℝ) (j : Fin 3) :
    meanT_STR02901 (ordinaryHolderCaptureSeed D h j).val=0 := by
  rw [capture_seed_val]
  unfold chartU_STR02924
  exact (meanT_uT_STR02924 _ _ (continuous_val_STR02924 _) (inE_of_mem_STR02924 _)).1

private theorem capture_mean_sub (u v : PeriodicC2_STR02969)
    (hu : meanT_STR02901 u.val=0) (hv : meanT_STR02901 v.val=0) :
    meanT_STR02901 (u-v).val=0 := by
  have he : (u-v).val = fun t => 1*u.val t+(-1)*v.val t+0*(0:ℝ) := by
    funext t
    simp only [PeriodicC2_STR02969.val_sub, Pi.sub_apply]
    ring
  rw [he, meanT_comb3_STR02924 (continuous_val_STR02924 u) (continuous_val_STR02924 v)
    continuous_const, hu, hv]
  ring

private theorem capture_smooth_profile (h : ℝ) {v : Torus 1 → ℝ}
    (hv : IsSmoothPeriodic v) (hp : ∀ x, 0 < v x) :
    ContDiff ℝ ∞ (elementaryPhysicalLogProfile h v) :=
  ((hv.comp (contDiff_pi.mpr fun _ => contDiff_id)).pow 2 |>.log
    (fun t => pow_ne_zero 2 (hp (pt t)).ne')).sub
      ((isSmoothPeriodic_ellT h).comp (contDiff_pi.mpr fun _ => contDiff_id))

private theorem capture_common_root_bounds (u : Fin 3 → Torus 1 → ℝ)
    (hu : ∀ j, Continuous (u j)) (hp : ∀ j x, 0 < u j x) :
    ∃ m B : ℝ, 0 < m ∧ 0 < B ∧ ∀ j x, m ≤ u j x ∧ |u j x| ≤ B := by
  let lo := fun x => min (u 0 x) (min (u 1 x) (u 2 x))
  let hi := fun x => max |u 0 x| (max |u 1 x| |u 2 x|)
  have hlc : Continuous lo := (hu 0).min ((hu 1).min (hu 2))
  have hhc : Continuous hi := (hu 0).abs.max ((hu 1).abs.max (hu 2).abs)
  obtain ⟨xmin,_,hmin⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hlc.continuousOn
  obtain ⟨xmax,_,hmax⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hhc.continuousOn
  have hlow (j : Fin 3) (x : Torus 1) : lo x ≤ u j x := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hhigh (j : Fin 3) (x : Torus 1) : |u j x| ≤ hi x := by
    fin_cases j
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨lo xmin,1+|hi xmax|,lt_min (hp 0 _) (lt_min (hp 1 _) (hp 2 _)),by positivity,?_⟩
  intro j x
  have hlo : lo xmin ≤ lo x := hmin (mem_univ x)
  have hhi : hi x ≤ hi xmax := hmax (mem_univ x)
  refine ⟨hlo.trans (hlow j x),(hhigh j x).trans (hhi.trans ?_)⟩
  exact (le_abs_self _).trans (by linarith)

private theorem capture_constant_label_subsequence (j : ℕ → Fin 3) :
    ∃ k : Fin 3, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, j (φ n)=k := by
  obtain ⟨k,ψ,hψ,hlim⟩ := CompactSpace.tendsto_subseq j
  have he : ∀ᶠ n in atTop, j (ψ n)=k := by
    have hm : ({k} : Set (Fin 3))∈𝓝 k := (isOpen_discrete ({k} : Set (Fin 3))).mem_nhds (by simp)
    filter_upwards [hlim.eventually hm] with n hn
    exact Set.mem_singleton_iff.mp hn
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  refine ⟨k,fun n => ψ (n+N),hψ.comp (fun i j hij => Nat.add_lt_add_right hij N),fun n => ?_⟩
  exact hN (n+N) (Nat.le_add_left _ _)

/-- Strong physical log-profile convergence enters the exact mean-zero
angular chart carrier, with its actual density and reference normalization. -/
private theorem capture_chart_limit (h : ℝ) (σ : AbsoluteDensity 1)
    (ρ : ℕ → AbsoluteDensity 1) (u0 : PeriodicC2_STR02969)
    (U : ℕ → PeriodicC2_STR02969) (w : Torus 1 → ℝ) (v : ℕ → Torus 1 → ℝ)
    (hw : IsSmoothPeriodic w) (hv : ∀ n, IsSmoothPeriodic (v n))
    (hwp : ∀ x, 0 < w x) (hvp : ∀ n x, 0 < v n x)
    (hσw : σ.sqrt =ᵐ[haar 1] w) (hρv : ∀ n, (ρ n).sqrt =ᵐ[haar 1] v n)
    (hσ : ∀ᵐ θ ∂angHaar, σ.density (angEquiv.symm θ)=rhoT_STR02901 h u0.val (angSec θ))
    (hU : ∀ n, ∀ᵐ θ ∂angHaar, (ρ n).density (angEquiv.symm θ)=rhoT_STR02901 h (U n).val (angSec θ))
    (hm0 : meanT_STR02901 u0.val=0) (hmU : ∀ n, meanT_STR02901 (U n).val=0)
    (h0 : USmall (fun n t => elementaryPhysicalLogProfile h (v n) t-elementaryPhysicalLogProfile h w t))
    (h1 : USmall (fun n t => deriv (elementaryPhysicalLogProfile h (v n)) t-deriv (elementaryPhysicalLogProfile h w) t))
    (h2 : USmall (fun n t => deriv (deriv (elementaryPhysicalLogProfile h (v n))) t-
      deriv (deriv (elementaryPhysicalLogProfile h w)) t))
    (h3 : USmall (fun n t => deriv (deriv (deriv (elementaryPhysicalLogProfile h (v n)))) t-
      deriv (deriv (deriv (elementaryPhysicalLogProfile h w))) t)) :
    Tendsto (fun n => ‖U n-u0‖) atTop (𝓝 0) := by
  let L := fun n => elementaryPhysicalLogProfile h (v n)
  let L0 := elementaryPhysicalLogProfile h w
  let F := fun n t => L n t-L0 t
  have hc := fun n => capture_smooth_profile h (hv n) (hvp n)
  have hc0 := capture_smooth_profile h hw hwp
  have hc1 := fun n => (contDiff_infty_iff_deriv.mp (hc n)).2
  have hc01 := (contDiff_infty_iff_deriv.mp hc0).2
  have hc2 := fun n => (contDiff_infty_iff_deriv.mp (hc1 n)).2
  have hc02 := (contDiff_infty_iff_deriv.mp hc01).2
  have e1 (n : ℕ) : deriv (F n)=fun t => deriv (L n) t-deriv L0 t := by
    funext t
    exact deriv_sub ((hc n).differentiable (by simp) t) (hc0.differentiable (by simp) t)
  have e2 (n : ℕ) : deriv (deriv (F n))=fun t => deriv (deriv (L n)) t-deriv (deriv L0) t := by
    rw [e1]
    funext t
    exact deriv_sub ((hc1 n).differentiable (by simp) t) (hc01.differentiable (by simp) t)
  have e3 (n : ℕ) : deriv (deriv (deriv (F n)))=fun t =>
      deriv (deriv (deriv (L n))) t-deriv (deriv (deriv L0)) t := by
    rw [e2]
    funext t
    exact deriv_sub ((hc2 n).differentiable (by simp) t) (hc02.differentiable (by simp) t)
  let C := fun n => elementaryChartLogConstant h u0-elementaryChartLogConstant h (U n)
  have e0 (n : ℕ) : (U n-u0).val=fun t => F n ((2*Real.pi)⁻¹*t)+C n := by
    have hn := interactingChart_continuous_logProfile h (U n) (ρ n) (hv n).continuous_torus (hρv n) (hU n)
    have hb := interactingChart_continuous_logProfile h u0 σ hw.continuous_torus hσw hσ
    funext t
    have hn' := congrFun hn t
    have hb' := congrFun hb t
    dsimp only [F,L,L0,elementaryPhysicalLogProfile,C]
    simp only [PeriodicC2_STR02969.val_sub,Pi.sub_apply]
    simp only [div_eq_inv_mul] at hn' hb'
    linarith
  apply physicalLog_chart_norm_tendsto_of_usmall (fun n => U n-u0) F C
    (fun n => (hc n).sub hc0)
    (fun n => (circ_periodic_pt (fun x => Real.log (v n x^2)-ellT h x)).sub
      (circ_periodic_pt (fun x => Real.log (w x^2)-ellT h x)))
    (fun n => capture_mean_sub (U n) u0 (hmU n) hm0) e0 h0
  · exact USmall.congr (fun n t => congrFun (e1 n) t) h1
  · exact USmall.congr (fun n t => congrFun (e2 n) t) h2
  · exact USmall.congr (fun n t => congrFun (e3 n) t) h3

/-- Every actual original-H1 scalar minimizer has a normalized actual density
chart arbitrarily close in the FULL retained C2 Holder norm to one of the SAME
ordinary seeds. One coupling threshold precedes every drift and minimizer.
The actual rate and scaled angular rate parameter are captured simultaneously. -/
theorem elementaryModel_scalarMinimizer_fullHolder_capture (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ η : ℝ, 0 < η → ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ=scalarRate (modelData h ε) b →
            ∃ (j : Fin 3) (U : PeriodicC2_STR02969), meanT_STR02901 U.val=0 ∧
              (∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ)=rhoT_STR02901 h U.val (angSec θ)) ∧
              ‖U-ordinaryHolderCaptureSeed D h j‖ < η ∧
              |(scalarRate (modelData h ε) b).toReal-(ordinaryLSRate (ordinaryReference h)).toReal| < η ∧
              |(scalarRate (modelData h ε) b).toReal/a0-1-h^2*D.Z j h 2| < η := by
  classical
  obtain ⟨δL,hδL,hδLr,hlocal⟩ := elementaryModel_minimizer_uniform_threeRoot_localization D
  obtain ⟨δC,hδC,hδCr,hclassical⟩ := elementaryModel_scalarMinimizer_classicalScore D
  obtain ⟨δQ,hδQ,hδQr,hsqueeze⟩ := elementaryModel_scalarRate_coupling_squeeze D
  obtain ⟨δR,hδR,hδRr,hrateLimit⟩ := elementaryModel_scalarRate_tendsto_ordinary D
  let δ := min δL (min δC (min δQ δR))
  have hδ : 0 < δ := lt_min hδL (lt_min hδC (lt_min hδQ hδR))
  have hδr : δ ≤ D.radius := (min_le_left _ _).trans hδLr
  refine ⟨δ,hδ,hδr,fun h hh hsmall => ?_⟩
  have hhL : h < δL := hsmall.trans_le (min_le_left _ _)
  have hhC : h < δC := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhQ : h < δQ := hsmall.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hhR : h < δR := hsmall.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨σ,u,εL,mL,K,hσ,hu,hεL,hεLmax,hmL,hK,hnear⟩ := hlocal h hh hhL
  obtain ⟨εC,mC,hεC,hεCmax,hmC,hminScore⟩ := hclassical h hh hhC
  obtain ⟨εQ,KQ,hεQ,hεQmax,hKQ,hQ⟩ := hsqueeze h hh hhQ
  obtain ⟨τ,hτ,hτpos,hτquot,hτmin,_,_,hfinite,hcanonical⟩ :=
    D.roots h hh (hsmall.trans_le hδr)
  have hLaw (j : Fin 3) : (densityMeasure (σ j) : Measure (Torus 1))=densityMeasure (τ j) := by
    apply (densityMeasure_eq_iff_STR02901 _ _).2
    exact Eventually.of_forall fun x => by
      have hs := hσ j (angEquiv x)
      have ht := hτ j (angEquiv x)
      simpa only [MeasurableEquiv.symm_apply_apply] using hs.trans ht.symm
  have hHsame (j : Fin 3) : ordinaryEntropy h (σ j)=ordinaryEntropy h (τ j) := by
    unfold ordinaryEntropy
    rw [hLaw j]
  have hIsame (j : Fin 3) : ordinaryFisher h (σ j)=ordinaryFisher h (τ j) := by
    unfold ordinaryFisher
    rw [hLaw j]
  have hQsame (j : Fin 3) : str025_quot h (σ j)=str025_quot h (τ j) := by
    unfold str025_quot
    rw [hHsame j,hIsame j]
  have hσpos (j : Fin 3) : 0 < ordinaryEntropy h (σ j) := by rw [hHsame]; exact hτpos j
  have hσmin (j : Fin 3) (ρ : AbsoluteDensity 1) (hp : 0 < ordinaryEntropy h ρ) :
      str025_quot h (σ j) ≤ str025_quot h ρ := by rw [hQsame]; exact hτmin j ρ hp
  choose S0 husm hS0sm hS0ae hud hS0d using fun j =>
    ordinaryOptimizer_classicalScore h (σ j) (hσpos j) (hσmin j) (hu j).1 (hu j).2.2 (hu j).2.1
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hS0da (j : Fin 3) (t : ℝ) : HasDerivAt (fun s => S0 j (pt s))
      (-(S0 j (pt t)*sigT h (pt t))/2-a*interactingLogNonlinearity h (pt t) (u j (pt t))) t := by
    simpa only [hQsame j,hτquot j,interactingLogNonlinearity,a] using hS0d j t
  obtain ⟨mB,B,hmB,hB,hbounds⟩ := capture_common_root_bounds u (fun j => (hu j).1)
    (fun j => (hu j).2.1)
  let m := min mC mB
  let M := B+K+2
  have hm : 0 < m := lt_min hmC hmB
  have hmM : m ≤ M := by
    have hmb := (hbounds 0 (0 : Torus 1)).1
    have hub := (le_abs_self (u 0 0)).trans (hbounds 0 (0 : Torus 1)).2
    have hmm := min_le_right mC mB
    dsimp only [m,M]
    linarith
  have hub (j : Fin 3) (x : Torus 1) : u j x∈Icc m M := by
    refine ⟨(min_le_right _ _).trans (hbounds j x).1,?_⟩
    have ht := (le_abs_self (u j x)).trans (hbounds j x).2
    dsimp only [M]
    linarith
  let R := a+KQ+1
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  let εB := min εL (min εC (min εQ 1))
  have hεB : 0 < εB := lt_min hεL (lt_min hεC (lt_min hεQ one_pos))
  have hεBmax : εB ≤ epsMax h := (min_le_left _ _).trans hεLmax
  intro η hη
  let Capture := fun (ε : ℝ) (b : AbsoluteDrift (modelData h ε)) (ρ : AbsoluteDensity 1) =>
    ∃ (j : Fin 3) (U : PeriodicC2_STR02969), meanT_STR02901 U.val=0 ∧
      (∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ)=rhoT_STR02901 h U.val (angSec θ)) ∧
      ‖U-ordinaryHolderCaptureSeed D h j‖ < η ∧
      |(scalarRate (modelData h ε) b).toReal-a| < η ∧
      |(scalarRate (modelData h ε) b).toReal/a0-1-h^2*D.Z j h 2| < η
  have hcapture : ∃ e : ℝ, 0 < e ∧ ∀ ε : ℝ, 0 < ε → ε < e →
      ∀ b : AbsoluteDrift (modelData h ε), ∀ ρ : AbsoluteDensity 1,
        0 < scalarGap (modelData h ε) ρ →
        scalarQuotient (modelData h ε) b ρ=scalarRate (modelData h ε) b → Capture ε b ρ := by
    by_contra hnone
    have hfail (e : ℝ) (he : 0 < e) : ∃ ε : ℝ, 0 < ε ∧ ε < e ∧
        ∃ b : AbsoluteDrift (modelData h ε), ∃ ρ : AbsoluteDensity 1,
          0 < scalarGap (modelData h ε) ρ ∧
          scalarQuotient (modelData h ε) b ρ=scalarRate (modelData h ε) b ∧ ¬Capture ε b ρ := by
      have hn : ¬(∀ ε : ℝ, 0 < ε → ε < e → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ=scalarRate (modelData h ε) b → Capture ε b ρ) :=
        fun hh => hnone ⟨e,he,hh⟩
      push_neg at hn
      exact hn
    let cap := fun n : ℕ => min εB (1/((n:ℝ)+1))
    have hcap (n : ℕ) : 0 < cap n := lt_min hεB (by positivity)
    choose ε hε hecap b ρ hG hmin hbad using fun n => hfail (cap n) (hcap n)
    have heB (n : ℕ) : ε n < εB := (hecap n).trans_le (min_le_left _ _)
    have heL (n : ℕ) : ε n < εL := (heB n).trans_le (min_le_left _ _)
    have heC (n : ℕ) : ε n < εC := (heB n).trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have heQ (n : ℕ) : ε n < εQ := (heB n).trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
    have he1 (n : ℕ) : ε n ≤ 1 := ((heB n).trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))).le
    have heps : Tendsto ε atTop (𝓝 0) := by
      have hz : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0) := by
        simpa only [Function.comp_def,one_div] using tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
      exact squeeze_zero (fun n => (hε n).le)
        (fun n => ((hecap n).trans_le (min_le_right _ _)).le) hz
    let r := fun n => (scalarRate (modelData h (ε n)) (b n)).toReal
    have hr : Tendsto r atTop (𝓝 a) := (hrateLimit h hh hhR ε hε heps b).2.2
    have hrb (n : ℕ) : |r n| ≤ R := by
      have he := (hQ (ε n) (hε n) (heQ n) (b n)).2
      have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
      rw [ENNReal.toReal_ofReal (add_nonneg ha (mul_nonneg hKQ.le (hε n).le))] at ht
      change r n ≤ a+KQ*ε n at ht
      rw [abs_of_nonneg (ENNReal.toReal_nonneg : 0 ≤ r n)]
      have hmul := mul_le_mul_of_nonneg_left (he1 n) hKQ.le
      dsimp only [R]
      linarith
    choose v S hv hS hρv hvmin hvd hSd using fun n =>
      hminScore (ε n) (hε n) (heC n) (b n) (ρ n) (hG n) (hmin n)
    have hvp (n : ℕ) (x : Torus 1) : 0 < v n x := hmC.trans_le (hvmin n x)
    have hsm (n : ℕ) := elementary_classicalScore_smooth h (ε n) (r n) (ρ n)
      (hv n) (hS n) (hvp n) (hvd n) (hSd n)
    have hnearest (n : ℕ) : ∃ j : Fin 3,
        ordinaryRootH1Deviation (σ j) (ρ n) (u j)^2 ≤ K*ε n ∧
          ∀ x, |v n x-u j x|^2 ≤ K*ε n := by
      obtain ⟨w,hw,hae,_,j,hd,hp⟩ := hnear (ε n) (hε n) (heL n) (b n) (ρ n) (hG n) (hmin n)
      have heq : w=v n := Measure.eq_of_ae_eq (hae.symm.trans (hρv n)) hw (hv n)
      exact ⟨j,hd,fun x => by simpa only [heq] using hp x⟩
    choose label hdev hpoint using hnearest
    have hvb (n : ℕ) (x : Torus 1) : v n x∈Icc m M := by
      refine ⟨(min_le_left _ _).trans (hvmin n x),?_⟩
      have hsq := (hpoint n x).trans (mul_le_mul_of_nonneg_left (he1 n) hK.le)
      have hdif : |v n x-u (label n) x| ≤ K+1 := by
        rw [mul_one] at hsq
        nlinarith [sq_nonneg (|v n x-u (label n) x|-1),sq_abs (v n x-u (label n) x)]
      have ht := (le_abs_self (u (label n) x)).trans (hbounds (label n) x).2
      have hl := le_abs_self (v n x-u (label n) x)
      dsimp only [M]
      linarith
    choose U hmU hU using fun n => positiveSmoothRoot_exists_meanZero_chart h (ρ n)
      (hsm n).1 (hvp n) (hρv n)
    obtain ⟨j,φ,hφ,hlabel⟩ := capture_constant_label_subsequence label
    have hd : Tendsto (fun n => ordinaryRootH1Deviation (σ j) (ρ (φ n)) (u j)) atTop (𝓝 0) := by
      have hsq : Tendsto (fun n => ordinaryRootH1Deviation (σ j) (ρ (φ n)) (u j)^2) atTop (𝓝 0) := by
        apply squeeze_zero (fun _ => sq_nonneg _) (fun n => ?_)
          (by simpa using (heps.comp hφ.tendsto_atTop).const_mul K)
        simpa only [hlabel n] using hdev (φ n)
      have habs := (Real.continuous_sqrt.tendsto 0).comp hsq
      have hnonneg (n : ℕ) : 0 ≤ ordinaryRootH1Deviation (σ j) (ρ (φ n)) (u j) := by
        unfold ordinaryRootH1Deviation
        positivity
      have heq (n : ℕ) : Real.sqrt (ordinaryRootH1Deviation (σ j) (ρ (φ n)) (u j)^2)=
          ordinaryRootH1Deviation (σ j) (ρ (φ n)) (u j) := Real.sqrt_sq (hnonneg n)
      simpa only [Function.comp_def,heq,Real.sqrt_zero] using habs
    obtain ⟨h0,h1,h2,h3⟩ := elementaryLogProfile_derivatives_small hh a R m M hR hm hmM
      (σ j) (fun n => ρ (φ n)) (u j) (S0 j) (fun n => v (φ n)) (fun n => S (φ n))
      (fun n => ε (φ n)) (fun n => r (φ n)) (husm j) (hS0sm j)
      (fun n => (hsm (φ n)).1) (fun n => (hsm (φ n)).2.1)
      (hu j).2.2 (fun n => hρv (φ n)) (hub j) (fun n => hvb (φ n))
      (hud j) (hS0da j) (fun n => hvd (φ n)) (fun n => hSd (φ n))
      (fun n => hrb (φ n)) (fun n => ⟨(hε (φ n)).le,he1 (φ n)⟩) hd
      (hr.comp hφ.tendsto_atTop) (heps.comp hφ.tendsto_atTop)
    have hσseed : ∀ᵐ θ ∂angHaar, (σ j).density (angEquiv.symm θ)=
        rhoT_STR02901 h (ordinaryHolderCaptureSeed D h j).val (angSec θ) :=
      Eventually.of_forall fun θ => by rw [capture_seed_val]; exact hσ j θ
    have hnorm := capture_chart_limit h (σ j) (fun n => ρ (φ n))
      (ordinaryHolderCaptureSeed D h j) (fun n => U (φ n)) (u j) (fun n => v (φ n))
      (husm j) (fun n => (hsm (φ n)).1) (hu j).2.1 (fun n => hvp (φ n))
      (hu j).2.2 (fun n => hρv (φ n)) hσseed (fun n => hU (φ n))
      (capture_seed_mean D h j) (fun n => hmU (φ n)) h0 h1 h2 h3
    have hrate : ∀ᶠ n in atTop, |r (φ n)-a| < η := by
      have ht := (hr.comp hφ.tendsto_atTop).sub_const a
      have hh0 : Tendsto (fun n => |r (φ n)-a|) atTop (𝓝 0) := by
        simpa using ht.abs
      exact hh0.eventually (gt_mem_nhds hη)
    have hgamma : ∀ᶠ n in atTop, |r (φ n)/a0-1-h^2*D.Z j h 2| < η := by
      have ha0 : a/a0-1=h^2*D.Z j h 2 := by
        have hc : a=a0*(1+h^2*D.Z j h 2) := hcanonical j
        rw [hc]
        field_simp [a0_pos.ne']
        <;> ring
      have ht := ((hr.comp hφ.tendsto_atTop).div_const a0).sub_const 1
      rw [ha0] at ht
      have hz : Tendsto (fun n => |r (φ n)/a0-1-h^2*D.Z j h 2|) atTop (𝓝 0) := by
        have hz0 := (ht.sub_const (h^2*D.Z j h 2)).abs
        rw [sub_self, abs_zero] at hz0
        exact hz0
      exact hz.eventually (gt_mem_nhds hη)
    have hg : ∀ᶠ n in atTop, Capture (ε (φ n)) (b (φ n)) (ρ (φ n)) := by
      filter_upwards [hnorm.eventually (gt_mem_nhds hη),hrate,hgamma] with n hn hrn hgn
      exact ⟨j,U (φ n),hmU (φ n),hU (φ n),hn,hrn,hgn⟩
    obtain ⟨n,hn⟩ := hg.exists
    exact hbad (φ n) hn
  obtain ⟨e,he,hgood⟩ := hcapture
  refine ⟨min e εB,lt_min he hεB,(min_le_right _ _).trans hεBmax,
    fun ε hε he b ρ hG hmin => ?_⟩
  exact hgood ε hε (he.trans_le (min_le_left _ _)) b ρ hG hmin

end DGPS.Examples.ThreeSpeciesCircle
