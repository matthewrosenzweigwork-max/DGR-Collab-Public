import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesMerging
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesAddition
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesFeedbackLipschitz
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootDensitySegmentStability
import DGPS.Examples.ThreeSpeciesCircle.OrdinarySignedRootMomentBound

/-! Relative profile comparison at one SAME ordinary-root triple. Genuine
fixed-field global minimality, actual field Lipschitz control and strong Jensen
supply the relative error; no desired contraction estimate is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private def family3 (p : Fin 3 → ℝ) (hp : ∀ j, 0 < p j) (hs : ∑ j, p j = 1)
    (ρ : Fin 3 → AbsoluteDensity 1) : SpeciesFamily 1 := SpeciesFamily.ofData 3 p hp hs ρ

private theorem moment_density_bound (ρ σ : AbsoluteDensity 1) {g : Torus 1 → ℝ}
    (hg : Continuous g) {M : ℝ} (hM : 0 ≤ M) (hgM : ∀ x, |g x| ≤ M) :
    |(∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1))) -
      ∫ x, g x ∂(densityMeasure σ : Measure (Torus 1))| ≤
        M * ∫ x, |ρ.density x - σ.density x| ∂haar 1 := by
  have hi (τ : AbsoluteDensity 1) : Integrable (fun x => τ.density x * g x) (haar 1) :=
    τ.integrable_density.mul_bdd hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hgM x)
  rw [Structural.budget_integral_densityMeasure, Structural.budget_integral_densityMeasure,
    ← integral_sub (hi _) (hi _)]
  calc _ ≤ ∫ x, |ρ.density x * g x - σ.density x * g x| ∂haar 1 := abs_integral_le_integral_abs
    _ ≤ ∫ x, M * |ρ.density x - σ.density x| ∂haar 1 := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
        ((ρ.integrable_density.sub σ.integrable_density).abs.const_mul M)
      exact Filter.Eventually.of_forall fun x => by
        dsimp only [Pi.sub_apply]
        rw [← sub_mul, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hgM x) (abs_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

private theorem barycenter_l1_bound (p q : Fin 3 → ℝ) (hp : ∀ j, 0 < p j)
    (hq : ∀ j, 0 < q j) (hps : ∑ j, p j = 1) (hqs : ∑ j, q j = 1)
    (ρ ν : Fin 3 → AbsoluteDensity 1) :
    let F := family3 p hp hps ρ
    let G := family3 q hq hqs ν
    (∫ x, |(barycenter F).density x - (barycenter G).density x| ∂haar 1) ≤
      (∑ j, |p j - q j|) + ∑ j, q j * ∫ x, |(ρ j).density x - (ν j).density x| ∂haar 1 := by
  dsimp only
  let F := family3 p hp hps ρ
  let G := family3 q hq hqs ν
  let f := fun j x => |p j - q j| * (ρ j).density x + q j * |(ρ j).density x - (ν j).density x|
  have hi (j : Fin 3) : Integrable (f j) (haar 1) :=
    ((ρ j).integrable_density.const_mul _).add
      (((ρ j).integrable_density.sub (ν j).integrable_density).abs.const_mul _)
  have hx (x : Torus 1) : |(barycenter F).density x - (barycenter G).density x| ≤ ∑ j, f j x := by
    rw [SpeciesFamily.barycenter_density_apply, SpeciesFamily.barycenter_density_apply]
    change |(∑ j : Fin 3, p j * (ρ j).density x) - ∑ j : Fin 3, q j * (ν j).density x| ≤ _
    have he : (∑ j, p j * (ρ j).density x) - (∑ j, q j * (ν j).density x) =
        ∑ j, ((p j - q j) * (ρ j).density x + q j * ((ρ j).density x - (ν j).density x)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    exact (abs_add_le _ _).trans (by
      simp only [abs_mul, abs_of_nonneg ((ρ j).density_nonneg x), abs_of_pos (hq j)]
      exact le_rfl)
  have he := integral_mono ((barycenter F).integrable_density.sub (barycenter G).integrable_density).abs
    (integrable_finsetSum _ (fun j _ => hi j)) hx
  rw [integral_finsetSum _ (fun j _ => hi j)] at he
  have hv (j : Fin 3) : (∫ x, f j x ∂haar 1) =
      |p j - q j| + q j * ∫ x, |(ρ j).density x - (ν j).density x| ∂haar 1 := by
    have he := integral_add ((ρ j).integrable_density.const_mul (|p j - q j|))
      (((ρ j).integrable_density.sub (ν j).integrable_density).abs.const_mul (q j))
    simp only [Pi.sub_apply] at he
    dsimp only [f]
    rw [he, integral_const_mul, integral_const_mul, (ρ j).integral_density, mul_one]
  simp_rw [hv] at he
  rw [Finset.sum_add_distrib] at he
  exact he

private theorem moment_comparison (p q : Fin 3 → ℝ) (hq : ∀ j, 0 ≤ q j)
    (hqs : ∑ j, q j = 1) (x y z : Fin 3 → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : ∀ j, |x j - z j| ≤ a) (hy : ∀ j, |x j - y j| ≤ b) :
    |((∑ j, p j * x j) - ∑ j, q j * y j) - ∑ j, (p j - q j) * z j| ≤
      a * (∑ j, |p j - q j|) + b := by
  have he : ((∑ j, p j * x j) - ∑ j, q j * y j) - ∑ j, (p j - q j) * z j =
      ∑ j, ((p j - q j) * (x j - z j) + q j * (x j - y j)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  calc _ ≤ ∑ j, |(p j - q j) * (x j - z j) + q j * (x j - y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (|p j - q j| * a + q j * b) := by
      apply Finset.sum_le_sum
      intro j _
      apply (abs_add_le _ _).trans
      simp only [abs_mul, abs_of_nonneg (hq j)]
      exact add_le_add (mul_le_mul_of_nonneg_left (hx j) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hy j) (hq j))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hqs]; ring


/-- Relative comparison of actual three-species minimizers assigned to one
SAME ordinary-root triple. The field and strong-Jensen estimates are discharged
internally. Constants precede both weight vectors, including arbitrarily small
positive weights. -/
theorem elementaryModel_three_minimizers_profile_comparison (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ σ : Fin 3 → AbsoluteDensity 1,
      (∀ j θ, (σ j).density (angEquiv.symm θ) =
        rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
      ∀ A : ℝ, 0 < A → ∃ K ε0 : ℝ, 0 < K ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
        ∀ p q : Fin 3 → ℝ, ∀ hp : ∀ j, 0 < p j, ∀ hq : ∀ j, 0 < q j,
        ∀ hps : ∑ j, p j = 1, ∀ hqs : ∑ j, q j = 1,
        ∀ ρ ν : Fin 3 → AbsoluteDensity 1,
        let F := SpeciesFamily.ofData 3 p hp hps ρ
        let G := SpeciesFamily.ofData 3 q hq hqs ν
        0 < speciesGap (modelData h ε) F →
        speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
        0 < speciesGap (modelData h ε) G →
        speciesQuotient (modelData h ε) b G = speciesRate (modelData h ε) b →
        (∀ j, ordinaryRootH1Deviation (σ j) (ρ j) (σ j).sqrt ≤ A * ε) →
        (∀ j, ordinaryRootH1Deviation (σ j) (ν j) (σ j).sqrt ≤ A * ε) →
        (∫ x, |(barycenter F).density x - (barycenter G).density x| ∂haar 1) ≤
            2 * ∑ j, |p j - q j| ∧
          (∀ j, (∫ x, |(ρ j).density x - (ν j).density x| ∂haar 1) ≤
            K * ε * ∑ j, |p j - q j|) ∧
          ∀ i : Fin 6,
            |((∫ x, elementarySixObservable h i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) -
              ∫ x, elementarySixObservable h i x ∂(densityMeasure (barycenter G) : Measure (Torus 1))) -
                ordinarySignedRootMoment h σ (fun j => p j - q j) i| ≤
              K * ε * ∑ j, |p j - q j| := by
  obtain ⟨δS, hδS, hδSr, hStability⟩ := ordinaryGraph_globalMin_density_stability D
  obtain ⟨δT, hδT, _, hTrial⟩ := elementaryModel_speciesRate_linear_trial_margin D
  let δ := min δS δT
  refine ⟨δ, lt_min hδS hδT, (min_le_left _ _).trans hδSr,
    fun h hh hhd σ hσ A hA => ?_⟩
  obtain ⟨w, z, c, hw, hwp, hrep, hz, hzu, hc, hStable⟩ :=
    hStability h hh (hhd.trans_le (min_le_left _ _)) σ hσ
  obtain ⟨d, εT, hd, hεT, hεTmax, hMargin⟩ :=
    hTrial h hh (hhd.trans_le (min_le_right _ _))
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  obtain ⟨L, hL, hLip⟩ := elementaryEulerCorrection_density_lipschitz h (a + 1) (by dsimp [a]; positivity)
  obtain ⟨M, hM, hObs⟩ := elementaryCorrection_coordinates_bound h
  classical
  choose η hη hTube using fun j : Fin 3 =>
    ordinaryRoot_near_density_tube (σ j) (w j) (hw j) (hwp j) (hrep j) hz hzu
  let η0 := min (η 0) (min (η 1) (η 2))
  have hη0 : 0 < η0 := lt_min (hη 0) (lt_min (hη 1) (hη 2))
  have hηle (j : Fin 3) : η0 ≤ η j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  let T := L / c
  let B := 2 * T + 1
  let E := 2 * M * A + M * B + 1
  let K := B + E + 1
  let ε0 := min εT (min 1 (min (η0 / (A + 1)) (1 / (2 * (T + 1)))))
  have hT : 0 < T := div_pos hL hc
  have hB : 0 < B := by dsimp only [B]; positivity
  have hE : 0 < E := by dsimp only [E]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  have hε0 : 0 < ε0 := lt_min hεT
    (lt_min one_pos (lt_min (div_pos hη0 (by positivity)) (by positivity)))
  refine ⟨K, ε0, hK, hε0, (min_le_left _ _).trans hεTmax,
    fun ε hε hεsmall b p q hp hq hps hqs ρ ν hF hFm hG hGm hρ hν => ?_⟩
  let F := family3 p hp hps ρ
  let G := family3 q hq hqs ν
  let r := (speciesRate (modelData h ε) b).toReal
  let N := ∫ x, |(barycenter F).density x - (barycenter G).density x| ∂haar 1
  let S := ∑ j, |p j - q j|
  have hN : 0 ≤ N := integral_nonneg fun x => abs_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  have heT : ε < εT := hεsmall.trans_le (min_le_left _ _)
  have he1 : ε ≤ 1 := (hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have heA : ε < η0 / (A + 1) := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heTsmall : ε < 1 / (2 * (T + 1)) := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hAε : A * ε ≤ η0 := by
    have he := (lt_div_iff₀ (by positivity : 0 < A + 1)).1 heA
    nlinarith only [he, hε]
  have hTε : T * ε ≤ 1 / 2 := by
    have he := (lt_div_iff₀ (by positivity : 0 < 2 * (T + 1))).1 heTsmall
    nlinarith only [he, hε]
  have heMax : ε < epsMax h := heT.trans_le hεTmax
  obtain ⟨_, hrmargin⟩ := hMargin ε hε heT b
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hra : r ≤ a := by
    change r ≤ a - d * ε at hrmargin
    nlinarith only [hrmargin, mul_pos hd hε]
  have hrR : |r| ≤ a + 1 := by rw [abs_of_nonneg hr]; linarith
  have hVL (x : Torus 1) :
      |elementaryEulerCorrection h ε r (barycenter F) x -
        elementaryEulerCorrection h ε r (barycenter G) x| ≤ L * ε * N :=
    hLip r hrR ε hε.le he1 (barycenter F) (barycenter G) x
  have hBranch (j : Fin 3) :
      (∫ x, |(ρ j).density x - (ν j).density x| ∂haar 1) ≤ T * ε * N := by
    obtain ⟨u, hu, hup, hru, hulo, huhi⟩ := hTube j (ρ j) ((hρ j).trans (hAε.trans (hηle j)))
    obtain ⟨v, hv, hvp, hnv, hvlo, hvhi⟩ := hTube j (ν j) ((hν j).trans (hAε.trans (hηle j)))
    have hminF (τ : AbsoluteDensity 1) :=
      elementaryModel_speciesRate_active_global_minimum hh hε heMax b F hF hFm j τ
    have hminG (τ : AbsoluteDensity 1) :=
      elementaryModel_speciesRate_active_global_minimum hh hε heMax b G hG hGm j τ
    have hs := hStable r hr hra j (ρ j) (ν j) u v hu hv hup hvp hru hnv
      hulo huhi hvlo hvhi
      (elementaryEulerCorrection h ε r (barycenter F))
      (elementaryEulerCorrection h ε r (barycenter G))
      (isSmooth_elementaryEulerCorrection h ε r (barycenter F)).continuous_torus
      (isSmooth_elementaryEulerCorrection h ε r (barycenter G)).continuous_torus
      (L * ε * N) (by positivity) hVL hminF hminG
    have he : (∫ x, |(ν j).density x - (ρ j).density x| ∂haar 1) =
        ∫ x, |(ρ j).density x - (ν j).density x| ∂haar 1 := by
      congr 1
      funext x
      exact abs_sub_comm _ _
    rw [he] at hs
    exact hs.2.2.trans_eq (by dsimp only [T]; ring)
  have hSum : (∑ j, q j * ∫ x, |(ρ j).density x - (ν j).density x| ∂haar 1) ≤ T * ε * N := by
    calc _ ≤ ∑ j, q j * (T * ε * N) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hBranch j) (hq j).le
      _ = _ := by rw [← Finset.sum_mul, hqs, one_mul]
  have hNb := barycenter_l1_bound p q hp hq hps hqs ρ ν
  have hN2 : N ≤ 2 * S := by
    have hm := mul_le_mul_of_nonneg_right hTε hN
    change N ≤ S + _ at hNb
    nlinarith only [hNb, hSum, hm]
  have hBranchS (j : Fin 3) :
      (∫ x, |(ρ j).density x - (ν j).density x| ∂haar 1) ≤ B * ε * S := by
    have hm := mul_le_mul_of_nonneg_left hN2 (mul_pos hT hε).le
    have he : T * ε * N ≤ B * ε * S := by dsimp only [B]; nlinarith only [hm, mul_nonneg hε.le hS]
    exact (hBranch j).trans he
  have hBK : B ≤ K := by dsimp only [K]; linarith
  have hEK : E ≤ K := by dsimp only [K]; linarith
  refine ⟨hN2, fun j => (hBranchS j).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBK hε.le) hS), fun i => ?_⟩
  let g := elementarySixObservable h i
  have hg := continuous_elementarySixObservable h i
  have hgM : ∀ x, |g x| ≤ M := hObs (.inl i)
  have hRoot (j : Fin 3) :
      |(∫ x, g x ∂(densityMeasure (ρ j) : Measure (Torus 1))) -
        ∫ x, g x ∂(densityMeasure (σ j) : Measure (Torus 1))| ≤ 2 * M * A * ε := by
    have hd : Real.sqrt (rootDistanceSq (ρ j) (σ j)) ≤ A * ε := by
      have hs := Real.sqrt_le_sqrt (rootDistanceSq_le_originalH1 (σ j) (ρ j))
      have hdev : 0 ≤ ordinaryRootH1Deviation (σ j) (ρ j) (σ j).sqrt :=
        add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hdev] at hs
      exact hs.trans (hρ j)
    exact (absolute_moment_error_le_root_distance (ρ j) (σ j) hg hM.le hgM).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2 * M))
  have hPair (j : Fin 3) :
      |(∫ x, g x ∂(densityMeasure (ρ j) : Measure (Torus 1))) -
        ∫ x, g x ∂(densityMeasure (ν j) : Measure (Torus 1))| ≤ M * B * ε * S :=
    (moment_density_bound (ρ j) (ν j) hg hM.le hgM).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hBranchS j) hM.le)
  have he := moment_comparison p q (fun j => (hq j).le) hqs
    (fun j => ∫ x, g x ∂(densityMeasure (ρ j) : Measure (Torus 1)))
    (fun j => ∫ x, g x ∂(densityMeasure (ν j) : Measure (Torus 1)))
    (fun j => ∫ x, g x ∂(densityMeasure (σ j) : Measure (Torus 1)))
    (2 * M * A * ε) (M * B * ε * S) (by positivity) (by positivity) hRoot hPair
  rw [Structural.budget_integral_barycenter _ hg, Structural.budget_integral_barycenter _ hg]
  change |((∑ j : Fin 3, p j * _) - ∑ j : Fin 3, q j * _) - ∑ j : Fin 3, (p j - q j) * _| ≤ _
  calc _ ≤ (2 * M * A * ε) * S + M * B * ε * S := he
    _ ≤ E * ε * S := by dsimp only [E]; nlinarith only [mul_nonneg hε.le hS]
    _ ≤ K * ε * S := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hEK hε.le) hS

end DGPS.Examples.ThreeSpeciesCircle
