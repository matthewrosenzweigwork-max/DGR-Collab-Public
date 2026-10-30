import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData
import DGPS.Examples.ThreeSpeciesCircle.InteractingDeficitExpansion
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryFisherStrongConvergence

/-! Fixed-field compactness for vanishing ordinary deficit on the full absolute
H1 domain. The information bound is derived, never assumed. The retained graph
determines the three nontrivial limiting roots before the sequence is chosen. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Every fixed-field entropy has an arbitrarily small information coefficient,
with its constant chosen before every full absolute-density competitor. -/
theorem ordinaryEntropy_information_bound (h η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : AbsoluteDensity 1,
      (ordinaryEntropy h ρ).toReal ≤ η * (ordinaryFisher h ρ).toReal + C := by
  let s := η / 12
  have hs : 0 < s := by dsimp [s]; positivity
  let B := 6 * (s * (2 + 2 * logGradBound h ^ 2) - 1 - Real.log s) + 2 * |h|
  refine ⟨max B 0, le_max_right _ _, fun ρ => ?_⟩
  have hI0 : 0 ≤ (ordinaryFisher h ρ).toReal := ENNReal.toReal_nonneg
  have hIm0 := circleFisherInformation_nonneg ρ
  have h2fin : 2 * ordinaryFisher h ρ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (str025_fisher_ne_top h ρ)
  have hRfin : 2 * ordinaryFisher h ρ + ENNReal.ofReal (2 * logGradBound h ^ 2) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h2fin, ENNReal.ofReal_ne_top⟩
  have hIm := ENNReal.toReal_mono hRfin (fisher_le_two_ordinary h ρ)
  rw [ENNReal.toReal_ofReal hIm0,
    ENNReal.toReal_add h2fin ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by positivity)] at hIm
  have hH : (ordinaryEntropy h ρ).toReal ≤ DGPS.Analysis.circleEntropy ρ + 2 * |h| := by
    rw [ordinaryEntropy_eq, ENNReal.toReal_ofReal']
    apply max_le
    · linarith [(abs_le.mp (abs_integral_density_mul_log_reference_le h ρ)).1]
    · exact add_nonneg (circleEntropy_nonneg ρ) (by positivity)
  let X := 2 + 2 * (ordinaryFisher h ρ).toReal + 2 * logGradBound h ^ 2
  have hX : 0 < X := by dsimp [X]; positivity
  have hHlog : (ordinaryEntropy h ρ).toReal ≤ 6 * Real.log X + 2 * |h| := by
    have hm := Real.log_le_log (by linarith : 0 < 2 + DGPS.Analysis.circleFisherInformation ρ)
      (show 2 + DGPS.Analysis.circleFisherInformation ρ ≤ X by dsimp [X]; linarith)
    linarith [circleEntropy_le_log_information ρ]
  have ht := Real.log_le_sub_one_of_pos (mul_pos hs hX)
  rw [Real.log_mul hs.ne' hX.ne'] at ht
  have hbound : (ordinaryEntropy h ρ).toReal ≤ η * (ordinaryFisher h ρ).toReal + B := by
    dsimp only [X, B, s] at *
    nlinarith
  exact hbound.trans (add_le_add le_rfl (le_max_left _ _))

/-- The actual fixed-field canonical deficit controls half the ordinary Fisher
information up to one competitor-independent constant. -/
theorem ordinaryDeficit_large_information (h : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : AbsoluteDensity 1,
      (ordinaryFisher h ρ).toReal / 2 - C ≤
        (ordinaryFisher h ρ).toReal -
          2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h ρ).toReal := by
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  let η := 1 / (4 * (a + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨B, hB, hbound⟩ := ordinaryEntropy_information_bound h η hη
  refine ⟨2 * a * B, by positivity, fun ρ => ?_⟩
  have hcoef : 2 * a * η ≤ 1 / 2 := by
    dsimp [η]
    rw [mul_one_div, div_le_iff₀ (by positivity : 0 < 4 * (a + 1))]
    linarith
  have hH := mul_le_mul_of_nonneg_left (hbound ρ) (by positivity : 0 ≤ 2 * a)
  have hI := mul_le_mul_of_nonneg_right hcoef
    (show 0 ≤ (ordinaryFisher h ρ).toReal from ENNReal.toReal_nonneg)
  change _ ≤ (ordinaryFisher h ρ).toReal - 2 * a * (ordinaryEntropy h ρ).toReal
  nlinarith

/-- Vanishing actual deficit itself supplies the uniform original Haar Fisher
bound needed by the existing one-dimensional compactness producer. -/
theorem ordinaryDeficit_sequence_information_bound (h : ℝ)
    (ρ : ℕ → AbsoluteDensity 1)
    (hD : Tendsto (fun n => (ordinaryFisher h (ρ n)).toReal -
      2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h (ρ n)).toReal)
      atTop (𝓝 0)) :
    ∃ B : ℝ, ∀ n, DGPS.Analysis.circleFisherInformation (ρ n) ≤ B := by
  obtain ⟨C, hC, hcoerc⟩ := ordinaryDeficit_large_information h
  obtain ⟨M, hM⟩ := hD.isBoundedUnder_le.bddAbove_range
  refine ⟨4 * (M + C) + 2 * logGradBound h ^ 2, fun n => ?_⟩
  have hDn := hM ⟨n, rfl⟩
  have hI := hcoerc (ρ n)
  have h2fin : 2 * ordinaryFisher h (ρ n) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (str025_fisher_ne_top h (ρ n))
  have hRfin : 2 * ordinaryFisher h (ρ n) + ENNReal.ofReal (2 * logGradBound h ^ 2) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h2fin, ENNReal.ofReal_ne_top⟩
  have hIm := ENNReal.toReal_mono hRfin (fisher_le_two_ordinary h (ρ n))
  rw [ENNReal.toReal_ofReal (circleFisherInformation_nonneg (ρ n)),
    ENNReal.toReal_add h2fin ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by positivity)] at hIm
  linarith

/-- Vanishing ordinary deficit is compact in the genuine original square-root
H1 topology. The three actual nontrivial roots come from the same retained graph
and are fixed before all sequences. No global stability estimate is asserted. -/
theorem ordinaryDeficit_compactness_same_graph (D : OrdinaryRootGraphData)
    (h : ℝ) (hh : 0 < h) (hsmall : h < D.radius) :
    ∃ σ : Fin 3 → AbsoluteDensity 1,
      (∀ j θ, (σ j).density (DGPS.Circle.AngularNormalization.angEquiv.symm θ) =
        rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h))
          (DGPS.Circle.AngularNormalization.angSec θ)) ∧
      (∀ j, 0 < ordinaryEntropy h (σ j)) ∧
      (∀ j (τ : AbsoluteDensity 1), 0 < ordinaryEntropy h τ →
        str025_quot h (σ j) ≤ str025_quot h τ) ∧
      ∀ ρ : ℕ → AbsoluteDensity 1,
        Tendsto (fun n => (ordinaryFisher h (ρ n)).toReal -
          2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h (ρ n)).toReal)
          atTop (𝓝 0) →
        ∃ (φ : ℕ → ℕ) (ρL : AbsoluteDensity 1) (ε : ℕ → ℝ),
          StrictMono φ ∧ Tendsto ε atTop (𝓝 0) ∧
          (∀ n, ∀ᵐ x ∂haar 1, |(ρ (φ n)).sqrt x - ρL.sqrt x| ≤ ε n) ∧
          ((densityMeasure ρL : Measure (Torus 1)) = threefoldReference h ∨
            ∃ j : Fin 3, (densityMeasure ρL : Measure (Torus 1)) =
              (densityMeasure (σ j) : Measure (Torus 1))) ∧
          Tendsto (fun n =>
            (eLpNorm (fun x => (ρ (φ n)).sqrt x - ρL.sqrt x) 2 (haar 1)).toReal +
            (eLpNorm (fun x => weakGradient (ρ (φ n)).sqrt (ρ (φ n)).sqrt_mem x -
              weakGradient ρL.sqrt ρL.sqrt_mem x) 2 (haar 1)).toReal) atTop (𝓝 0) := by
  obtain ⟨σ, hσ, hpos, hquot, hmin, hdist, hexact, hfinite, hrate⟩ := D.roots h hh hsmall
  refine ⟨σ, hσ, hpos, hmin, fun ρ hD => ?_⟩
  obtain ⟨B, hB⟩ := ordinaryDeficit_sequence_information_bound h ρ hD
  obtain ⟨φ, ρL, ε, R, hφ, hε, hae, hub, hLb, hhaarLSC⟩ :=
    exists_limit_of_bounded_fisher ρ hB
  have hpt : ∀ᵐ x ∂haar 1,
      Tendsto (fun n => (ρ (φ n)).sqrt x) atTop (𝓝 (ρL.sqrt x)) := by
    filter_upwards [ae_all_iff.mpr hae] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => by
      rw [Real.norm_eq_abs]
      exact hx n) hε
  have hH := tendsto_ordinaryEntropy h hub hpt
  have hHr := (ENNReal.tendsto_toReal (str025_entropy_ne_top h ρL)).comp hH
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hIs : Tendsto (fun n => (ordinaryFisher h (ρ (φ n))).toReal) atTop
      (𝓝 (2 * a * (ordinaryEntropy h ρL).toReal)) := by
    have ht := (hD.comp hφ.tendsto_atTop).add (hHr.const_mul (2 * a))
    convert ht using 1
    · funext n
      dsimp only [a, Function.comp_apply]
      ring
    · simp
  have hback (τ : AbsoluteDensity 1) :
      ENNReal.ofReal (ordinaryFisher h τ).toReal = ordinaryFisher h τ :=
    ENNReal.ofReal_toReal (str025_fisher_ne_top h τ)
  have hIe : Tendsto (fun n => ordinaryFisher h (ρ (φ n))) atTop
      (𝓝 (ENNReal.ofReal (2 * a * (ordinaryEntropy h ρL).toReal))) := by
    simpa only [hback] using ENNReal.tendsto_ofReal hIs
  have hLSC := ordinaryFisher_le_liminf h (fun n => ρ (φ n)) ρL hε hae
  rw [hIe.liminf_eq] at hLSC
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hLSC
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * a * (ordinaryEntropy h ρL).toReal)] at hle
  have hnonneg := elementary_ordinary_deficit_nonneg h ρL
  change 0 ≤ (ordinaryFisher h ρL).toReal - 2 * a * (ordinaryEntropy h ρL).toReal at hnonneg
  have heq : (ordinaryFisher h ρL).toReal = 2 * a * (ordinaryEntropy h ρL).toReal :=
    le_antisymm hle (by linarith)
  have hzero : ZeroDeficit_STR02901 h a (densityMeasure ρL : Measure (Torus 1)) :=
    (zeroDeficit_iff_abs_STR02901 h a _).2 ⟨ρL, rfl, by rw [heq]; ring⟩
  have hclass := (str029_32_zero_deficit_roots_of_data h σ hpos hmin hexact
    (densityMeasure ρL : Measure (Torus 1))).1 hzero
  have hI : Tendsto (fun n => (ordinaryFisher h (ρ (φ n))).toReal) atTop
      (𝓝 (ordinaryFisher h ρL).toReal) := by
    rw [heq]
    exact hIs
  exact ⟨φ, ρL, ε, hφ, hε, hae, hclass,
    ordinaryFisher_strong_h1_of_uniform h (fun n => ρ (φ n)) ρL hε hae hI⟩

end DGPS.Examples.ThreeSpeciesCircle
