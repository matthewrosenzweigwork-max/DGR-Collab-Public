import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarTrial

/-! An actual linear coupling bound for the scalar trial. Constants precede epsilon
and the weak drift provider; no limiting quotient or optimizer approximation is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual ordinary equality root is an interacting trial with quotient at most
its ordinary value plus K*epsilon, uniformly throughout one coupling interval. -/
theorem ordinaryRoot_interacting_scalar_trial_linear {h : ℝ} (hh : 0 < h)
    (σ : AbsoluteDensity 1) (hH : 0 < ordinaryEntropy h σ)
    (hquot : str025_quot h σ = ordinaryLSRate (ordinaryReference h)) :
    ∃ ε0 K : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < K ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
        0 < scalarGap (modelData h ε) σ ∧
          scalarQuotient (modelData h ε) b σ ≤
            ENNReal.ofReal ((ordinaryLSRate (ordinaryReference h)).toReal + K * ε) := by
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let H := (ordinaryEntropy h σ).toReal
  let I := (ordinaryFisher h σ).toReal
  have hHreal : 0 < H := ENNReal.toReal_pos hH.ne' (str025_entropy_ne_top h σ)
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hq := congrArg ENNReal.toReal hquot
  change (ordinaryFisher h σ / (2 * ordinaryEntropy h σ)).toReal = a at hq
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hq
  change I / (2 * H) = a at hq
  have hI : I = 2 * a * H := by
    have hm := (div_eq_iff (by positivity : 2 * H ≠ 0)).mp hq
    nlinarith
  obtain ⟨εG, hεG, hεGmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  let P := |elementaryC h a σ| + elementaryJ h σ + 1
  have hP : 0 < P := by dsimp only [P]; nlinarith [abs_nonneg (elementaryC h a σ), elementaryJ_nonneg h σ]
  let K := P / H
  have hK : 0 < K := div_pos hP hHreal
  have hKH : K * H = P := by dsimp only [K]; field_simp [hHreal.ne']
  refine ⟨min εG 1, K, lt_min hεG one_pos, (min_le_left _ _).trans hεGmax, hK,
    fun ε hε hεsmall b => ?_⟩
  have heG : ε < εG := hεsmall.trans_le (min_le_left _ _)
  have he1 : ε ≤ 1 := (hεsmall.trans_le (min_le_right _ _)).le
  let G : ℝ := scalarGap (modelData h ε) σ
  let D := (scalarDissipation (modelData h ε) b σ).toReal
  have hGlo : H / 2 ≤ G := by
    have hg := (hgap ε hε heG (SpeciesFamily.single σ)).1
    have he : (1 / 2 : ℝ) * H ≤ G := by
      simpa only [speciesGap_single, sum_single_count, SpeciesFamily.single_weight,
        SpeciesFamily.single_density, one_mul] using hg
    linarith
  have hG : 0 < G := (half_pos hHreal).trans_le hGlo
  have hGpos : 0 < scalarGap (modelData h ε) σ := hG
  have hD := elementaryModel_scalar_deficit_real hh hε (heG.trans_le hεGmax) b σ a
  have hDzero : D - 2 * a * G = ε * elementaryC h a σ + ε ^ 2 * elementaryJ h σ := by
    change D - 2 * a * G = I - 2 * a * H + ε * elementaryC h a σ + ε ^ 2 * elementaryJ h σ at hD
    rw [hI] at hD
    nlinarith
  have hC := mul_le_mul_of_nonneg_left (le_abs_self (elementaryC h a σ)) hε.le
  have hJ := mul_le_mul_of_nonneg_right (show ε ^ 2 ≤ ε by nlinarith) (elementaryJ_nonneg h σ)
  have hmass := mul_le_mul_of_nonneg_left
    (show H ≤ 2 * G by linarith) (mul_nonneg hε.le hK.le)
  have heK := congrArg (fun t : ℝ => ε * t) hKH
  have hDupper : D ≤ 2 * (a + K * ε) * G := by
    dsimp only [P] at heK
    nlinarith
  have hDfin := (elementaryModel_scalarDissipation_real h ε b σ).1
  have hden0 : 2 * (scalarGap (modelData h ε) σ : ℝ≥0∞) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast hGpos.ne')
  have hdent : 2 * (scalarGap (modelData h ε) σ : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
  refine ⟨hGpos, ?_⟩
  unfold scalarQuotient
  apply (ENNReal.div_le_iff hden0 hdent).2
  rw [← ENNReal.ofReal_toReal hDfin]
  have hden : 2 * (scalarGap (modelData h ε) σ : ℝ≥0∞) = ENNReal.ofReal (2 * G) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_coe_nnreal]
  rw [hden, ← ENNReal.ofReal_mul (show 0 ≤ a + K * ε by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [hDupper])

end DGPS.Examples.ThreeSpeciesCircle
