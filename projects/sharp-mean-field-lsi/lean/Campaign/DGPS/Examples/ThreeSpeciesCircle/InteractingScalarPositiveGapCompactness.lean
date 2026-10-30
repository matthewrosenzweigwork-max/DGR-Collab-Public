import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarTrial
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryFisherStrongConvergence

/-! Actual positive-gap compactness below a concrete scalar trial. A zero-gap limit
is excluded by deriving strong original H1 convergence to the reference and applying
the actual strict quotient barrier. No positive-gap compactness premise is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Actual below-trial scalar sublevels have a positive-gap subsequential limit. The
trial is selected internally from the same retained ordinary graph before the coupling. -/
theorem elementaryModel_scalar_sublevel_positiveGap_compactness (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ (σ : AbsoluteDensity 1) (ε0 : ℝ), 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          0 < scalarGap (modelData h ε) σ ∧
          ∀ ρ : ℕ → AbsoluteDensity 1,
            (∀ n, 0 < scalarGap (modelData h ε) (ρ n)) →
            (∀ n, scalarQuotient (modelData h ε) b (ρ n) ≤ scalarQuotient (modelData h ε) b σ) →
            ∃ B : ℝ, 0 ≤ B ∧
              (∀ n, DGPS.Analysis.circleFisherInformation (ρ n) ≤ B ∧
                DGPS.Analysis.circleEntropy (ρ n) ≤ B) ∧
              ∃ (φ : ℕ → ℕ) (ρL : AbsoluteDensity 1) (η : ℕ → ℝ),
                StrictMono φ ∧ Tendsto η atTop (𝓝 0) ∧
                (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x - ρL.sqrt x| ≤ η n) ∧
                Tendsto (fun n => ordinaryEntropy h (ρ (φ n))) atTop (𝓝 (ordinaryEntropy h ρL)) ∧
                0 < scalarGap (modelData h ε) ρL := by
  obtain ⟨δ, hδ, hδr, htrial⟩ := elementaryModel_scalar_trial_below_reference_barrier D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨σ, r, εT, ηB, _, hεT, hεTmax, hηB, hT⟩ := htrial h hh hhd
  obtain ⟨εX, hεX, _, htransfer⟩ := elementaryModel_scalar_boundedQuotient_transfer hh
  obtain ⟨εG, hεG, _, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  let ε0 := min εT (min εX εG)
  refine ⟨σ, ε0, lt_min hεT (lt_min hεX hεG), (min_le_left _ _).trans hεTmax,
    fun ε hε hεε0 b => ?_⟩
  have heT : ε < εT := hεε0.trans_le (min_le_left _ _)
  have heX : ε < εX := hεε0.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heG : ε < εG := hεε0.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨⟨hσG, hσQ⟩, hbarrier⟩ := hT ε hε heT b
  refine ⟨hσG, fun ρ hpos hq => ?_⟩
  have hσDfin := (elementaryModel_scalarDissipation_real h ε b σ).1
  have hσQfin : scalarQuotient (modelData h ε) b σ ≠ ⊤ :=
    ((scalarQuotient_lt_top_iff (modelData h ε) b σ hσG).2 (lt_top_iff_ne_top.mpr hσDfin)).ne
  let M := (scalarQuotient (modelData h ε) b σ).toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hqM (n : ℕ) : scalarQuotient (modelData h ε) b (ρ n) ≤ ENNReal.ofReal M := by
    rw [ENNReal.ofReal_toReal hσQfin]
    exact hq n
  obtain ⟨L, hL⟩ := htransfer ε hε heX b M hM
  have hHp n := (hL (ρ n) (hpos n) (hqM n)).1
  have hQp n := (hL (ρ n) (hpos n) (hqM n)).2
  obtain ⟨B, hB, hBn, φ, ρL, η, hφ, hη, hae, _, hHconv, _, _⟩ :=
    circle_boundedQuotient_compactness (abs_nonneg h) L h le_rfl ρ hHp hQp
  refine ⟨B, hB, hBn, φ, ρL, η, hφ, hη, hae, hHconv, ?_⟩
  by_contra hn
  have hGzero : scalarGap (modelData h ε) ρL = 0 := le_antisymm (not_lt.mp hn) zero_le
  have hHlower : (1 / 2 : ℝ) * (ordinaryEntropy h ρL).toReal ≤ 0 := by
    have hg := (hgap ε hε heG (SpeciesFamily.single ρL)).1
    simpa only [speciesGap_single, hGzero, NNReal.coe_zero, sum_single_count,
      SpeciesFamily.single_weight, SpeciesFamily.single_density, one_mul] using hg
  have hHzeroReal : (ordinaryEntropy h ρL).toReal = 0 := by
    nlinarith [show 0 ≤ (ordinaryEntropy h ρL).toReal from ENNReal.toReal_nonneg]
  have hHzero : ordinaryEntropy h ρL = 0 := by
    rw [← ENNReal.ofReal_toReal (str025_entropy_ne_top h ρL), hHzeroReal, ENNReal.ofReal_zero]
  have hHr : Tendsto (fun n => (ordinaryEntropy h (ρ (φ n))).toReal) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal (str025_entropy_ne_top h ρL)).comp hHconv
    change Tendsto (fun n : ℕ => (ordinaryEntropy h (ρ (φ n))).toReal) atTop
      (𝓝 (ordinaryEntropy h ρL).toReal) at ht
    rw [hHzeroReal] at ht
    exact ht
  have hIbound n : (ordinaryFisher h (ρ (φ n))).toReal ≤
      2 * (L : ℝ) * (ordinaryEntropy h (ρ (φ n))).toReal := by
    have hqOrd := hQp (φ n)
    change ordinaryFisher h (ρ (φ n)) / (2 * ordinaryEntropy h (ρ (φ n))) ≤ (L : ℝ≥0∞) at hqOrd
    have hden0 : 2 * ordinaryEntropy h (ρ (φ n)) ≠ 0 :=
      mul_ne_zero (by norm_num) (hHp (φ n)).ne'
    have hdent : 2 * ordinaryEntropy h (ρ (φ n)) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (str025_entropy_ne_top h (ρ (φ n)))
    have hm := (ENNReal.div_le_iff hden0 hdent).1 hqOrd
    have hr := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hdent) hm
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_mul,
      ENNReal.toReal_ofNat] at hr
    nlinarith
  have hIr : Tendsto (fun n => (ordinaryFisher h (ρ (φ n))).toReal) atTop (𝓝 0) := by
    refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) hIbound ?_
    simpa using hHr.const_mul (2 * (L : ℝ))
  have hIe : Tendsto (fun n => ordinaryFisher h (ρ (φ n))) atTop (𝓝 0) := by
    have ht := ENNReal.tendsto_ofReal hIr
    simpa only [ENNReal.ofReal_toReal (str025_fisher_ne_top h _), ENNReal.ofReal_zero] using ht
  have hIL := ordinaryFisher_le_liminf h (fun n => ρ (φ n)) ρL hη hae
  rw [hIe.liminf_eq] at hIL
  have hILzero : ordinaryFisher h ρL = 0 := le_antisymm hIL zero_le
  have hIstrong : Tendsto (fun n => (ordinaryFisher h (ρ (φ n))).toReal) atTop
      (𝓝 (ordinaryFisher h ρL).toReal) := by simpa only [hILzero, ENNReal.toReal_zero] using hIr
  have hstrong := ordinaryFisher_strong_h1_of_uniform h (fun n => ρ (φ n)) ρL hη hae hIstrong
  have hs := str025_sqrt_eq_of_entropy_zero h ρL hHzero
  have hg := (isWeakGradient_weakGradient ρL.sqrt_mem).ae_eq
    ((isWeakGradient_weakGradient (ordinaryReferenceAbsolute h).sqrt_mem).congr_ae
      hs.symm (EventuallyEq.refl _ _))
  have hmetric (n : ℕ) :
      ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) (ρ (φ n)) (str025_w h) =
        ordinaryRootH1Deviation ρL (ρ (φ n)) ρL.sqrt := by
    unfold ordinaryRootH1Deviation
    have he : (fun x => (ρ (φ n)).sqrt x - str025_w h x) =ᵐ[haar 1]
        fun x => (ρ (φ n)).sqrt x - ρL.sqrt x := by
      filter_upwards [hs] with x hx
      rw [hx]
    have heG : (fun x => weakGradient (ρ (φ n)).sqrt (ρ (φ n)).sqrt_mem x -
        weakGradient (ordinaryReferenceAbsolute h).sqrt (ordinaryReferenceAbsolute h).sqrt_mem x)
        =ᵐ[haar 1] fun x => weakGradient (ρ (φ n)).sqrt (ρ (φ n)).sqrt_mem x -
          weakGradient ρL.sqrt ρL.sqrt_mem x := by
      filter_upwards [hg] with x hx
      rw [hx]
    rw [eLpNorm_congr_ae he, eLpNorm_congr_ae heG]
  have hnear : ∀ᶠ n in atTop,
      ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) (ρ (φ n)) (str025_w h) ≤ ηB := by
    have ht : Tendsto (fun n => ordinaryRootH1Deviation ρL (ρ (φ n)) ρL.sqrt) atTop (𝓝 0) := hstrong
    filter_upwards [ht.eventually (gt_mem_nhds hηB)] with n hn
    rw [hmetric]
    exact hn.le
  obtain ⟨n, hn⟩ := hnear.exists
  have hl := hbarrier (ρ (φ n)) (hpos (φ n)) hn
  exact (not_lt_of_ge hl) ((hq (φ n)).trans_lt hσQ)

end DGPS.Examples.ThreeSpeciesCircle
