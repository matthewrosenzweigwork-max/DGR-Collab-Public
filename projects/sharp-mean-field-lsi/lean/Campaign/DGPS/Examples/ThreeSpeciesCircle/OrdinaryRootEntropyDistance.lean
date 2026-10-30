import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData
import DGPS.Examples.ThreeSpeciesCircle.NearestRootMomentError
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferenceLocalStability
import DGPS.Structural.HarmonicRateComparison

/-! Entropy at an actual positive ordinary root is controlled by entropy at
an arbitrary original absolute competitor and its true square-root distance.
The supporting-plane inequality is derived from nonnegative relative entropy. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem entropy_real_identity (h : ℝ) (ρ : AbsoluteDensity 1) :
    (ordinaryEntropy h ρ).toReal = DGPS.Analysis.circleEntropy ρ -
      ∫ x, ρ.density x * Real.log (referenceDensity h x) ∂haar 1 := by
  have he := (Structural.relativeEntropy_reference (ordinaryReference h) ρ).2
  rw [← circleEntropy_eq_relativeEntropy] at he
  exact he

/-- The genuine entropy supporting plane at a continuous positive absolute law.
The competitor may vanish and has only the original absolute H1 regularity. -/
theorem ordinaryEntropy_supporting_plane (h : ℝ) (σ ρ : AbsoluteDensity 1)
    (hσc : Continuous σ.density) (hσp : ∀ x, 0 < σ.density x) :
    (ordinaryEntropy h σ).toReal +
      (∫ x, (Real.log (σ.density x) - Real.log (referenceDensity h x))
        ∂(densityMeasure ρ : Measure (Torus 1))) -
      (∫ x, (Real.log (σ.density x) - Real.log (referenceDensity h x))
        ∂(densityMeasure σ : Measure (Torus 1))) ≤
      (ordinaryEntropy h ρ).toReal := by
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hσc.continuousOn
  obtain ⟨x1, _, hx1⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hσc.continuousOn
  let P : BoundedPositiveReference 1 := {
    density := σ.density
    measurable_density := hσc.measurable
    lower := σ.density x0
    upper := σ.density x1
    lower_pos := hσp x0
    lower_le := Eventually.of_forall fun x => hx0 (Set.mem_univ x)
    le_upper := Eventually.of_forall fun x => hx1 (Set.mem_univ x)
    mass_one := σ.integral_density }
  have hKL := (Structural.relativeEntropy_reference P ρ).2
  rw [← circleEntropy_eq_relativeEntropy] at hKL
  change (relativeEntropy (densityMeasure ρ : Measure (Torus 1)) P.measure).toReal =
    DGPS.Analysis.circleEntropy ρ - ∫ x, ρ.density x * Real.log (σ.density x) ∂haar 1 at hKL
  have hnn : 0 ≤ DGPS.Analysis.circleEntropy ρ -
      ∫ x, ρ.density x * Real.log (σ.density x) ∂haar 1 := by
    rw [← hKL]
    exact ENNReal.toReal_nonneg
  have hi (τ : AbsoluteDensity 1) :
      Integrable (fun x => τ.density x * Real.log (σ.density x)) (haar 1) :=
    Structural.integrable_density_mul_log_reference P τ
  have he (τ : AbsoluteDensity 1) :
      (∫ x, (Real.log (σ.density x) - Real.log (referenceDensity h x))
        ∂(densityMeasure τ : Measure (Torus 1))) =
      (∫ x, τ.density x * Real.log (σ.density x) ∂haar 1) -
        ∫ x, τ.density x * Real.log (referenceDensity h x) ∂haar 1 := by
    rw [Structural.budget_integral_densityMeasure]
    simp_rw [mul_sub]
    rw [integral_sub (hi τ) (integrable_density_mul_log_reference h τ)]
  rw [he ρ, he σ, entropy_real_identity h σ, entropy_real_identity h ρ, circleEntropy_eq σ]
  linarith

/-- The supporting plane and true Hellinger estimate give a constant fixed
before every original absolute competitor. -/
theorem ordinaryEntropy_positive_root_distance (h : ℝ) (σ : AbsoluteDensity 1)
    (hσc : Continuous σ.density) (hσp : ∀ x, 0 < σ.density x) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ : AbsoluteDensity 1,
      (ordinaryEntropy h σ).toReal ≤ (ordinaryEntropy h ρ).toReal +
        K * Real.sqrt (rootDistanceSq ρ σ) := by
  let L : Torus 1 → ℝ := fun x => Real.log (σ.density x) - Real.log (referenceDensity h x)
  have hLc : Continuous L := (hσc.log (fun x => (hσp x).ne')).sub
    ((continuous_referenceDensity h).log (fun x => (referenceDensity_pos (h := h) x).ne'))
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hLc.continuousOn
  let M := |B| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hLM : ∀ x, |L x| ≤ M := by
    intro x
    have hb := hB x (Set.mem_univ x)
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (by dsimp [M]; linarith [le_abs_self B])
  refine ⟨2 * M, by positivity, fun ρ => ?_⟩
  have hplane := ordinaryEntropy_supporting_plane h σ ρ hσc hσp
  have hdist := absolute_moment_error_le_root_distance ρ σ hLc hM.le hLM
  have hdiff := (abs_le.mp hdist).1
  change (ordinaryEntropy h σ).toReal + (∫ x, L x ∂(densityMeasure ρ : Measure (Torus 1))) -
    (∫ x, L x ∂(densityMeasure σ : Measure (Torus 1))) ≤ (ordinaryEntropy h ρ).toReal at hplane
  linarith

/-- Pointwise actual ordinary charts supply genuine continuous positive native
densities. No regularity of the stored representative is silently assumed. -/
theorem ordinaryRoot_density_continuous_positive (D : OrdinaryRootGraphData) (h : ℝ)
    (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) (j : Fin 3) :
    Continuous (σ j).density ∧ ∀ x, 0 < (σ j).density x := by
  have hv := chartU_isC2_STR02924 D.ψ h (D.Z j h)
  have hp := periodic_rho_STR02950 h hv.1
  have hc : Continuous (fun θ : AngCircle =>
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) := by
    change Continuous (AddCircle.liftIoc (2 * Real.pi) 0
      (rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h))))
    exact AddCircle.liftIoc_zero_continuous (by simpa using (hp 0).symm)
      (continuous_rho_STR02950 h hv.2.1.continuous).continuousOn
  have ha : Continuous (angEquiv : Torus 1 → AngCircle) := by
    change Continuous (fun x : Torus 1 => angHomeo (x 0))
    exact angHomeo.continuous.comp (continuous_apply 0)
  have hd : (σ j).density = fun x =>
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec (angEquiv x)) := by
    funext x
    simpa only [angEquiv.symm_apply_apply] using hσ j (angEquiv x)
  constructor
  · rw [hd]
    exact hc.comp ha
  · intro x
    rw [hd]
    exact rhoT_pos_STR02901 h hv.2.1.continuous _


private theorem same_chart_entropy_positive (D : OrdinaryRootGraphData) {h : ℝ}
    (hh : 0 < h) (hhr : h < D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) :
    ∀ j, 0 < (ordinaryEntropy h (σ j)).toReal := by
  obtain ⟨τ, hτ, hτpos, _⟩ := D.roots h hh hhr
  intro j
  have he : (σ j).density = (τ j).density := by
    funext x
    have hs := (hσ j (angEquiv x)).trans (hτ j (angEquiv x)).symm
    simpa only [angEquiv.symm_apply_apply] using hs
  have hμ : (densityMeasure (σ j) : Measure (Torus 1)) = densityMeasure (τ j) :=
    (densityMeasure_eq_iff_STR02901 _ _).2 (Eventually.of_forall fun x => congrFun he x)
  have hp : 0 < ordinaryEntropy h (σ j) := by
    unfold ordinaryEntropy
    rw [hμ]
    exact hτpos j
  exact ENNReal.toReal_pos hp.ne' (str025_entropy_ne_top h (σ j))

private theorem weighted_sqrt_budget (F : SpeciesFamily 1) (R : Fin 4 → AbsoluteDensity 1)
    (label : Fin F.count → Fin 4) :
    (∑ s, F.weight s * Real.sqrt (rootDistanceSq (F.density s) (R (label s)))) ≤
      Real.sqrt (rootDistanceBudget F R label) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin F.count))
    (fun s => Real.sqrt (F.weight s))
    (fun s => Real.sqrt (F.weight s) * Real.sqrt (rootDistanceSq (F.density s) (R (label s))))
  have hleft : (∑ s, Real.sqrt (F.weight s) *
      (Real.sqrt (F.weight s) * Real.sqrt (rootDistanceSq (F.density s) (R (label s))))) =
      ∑ s, F.weight s * Real.sqrt (rootDistanceSq (F.density s) (R (label s))) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [← mul_assoc, ← sq, Real.sq_sqrt (F.weight_nonneg s)]
  have h1 : (∑ s, Real.sqrt (F.weight s) ^ 2) = 1 := by
    calc _ = ∑ s, F.weight s := Finset.sum_congr rfl fun s _ => Real.sq_sqrt (F.weight_nonneg s)
      _ = 1 := F.weight_sum
  have h2 : (∑ s, (Real.sqrt (F.weight s) *
      Real.sqrt (rootDistanceSq (F.density s) (R (label s)))) ^ 2) = rootDistanceBudget F R label := by
    unfold rootDistanceBudget
    apply Finset.sum_congr rfl
    intro s hs
    rw [mul_pow, Real.sq_sqrt (F.weight_nonneg s), Real.sq_sqrt (rootDistanceSq_nonneg _ _)]
  rw [hleft, h1, h2] at hcs
  simpa using hcs

/-- Actual positive entropy at the SAME roots controls assigned nonreference
mass by actual family entropy and the true square-root distance budget. Both
constants precede all species counts, positive weights, densities and assignments. -/
theorem ordinaryRoot_family_entropy_distance (D : OrdinaryRootGraphData) {h : ℝ}
    (hh : 0 < h) (hhr : h < D.radius) (σ : Fin 3 → AbsoluteDensity 1)
    (hσ : ∀ j θ, (σ j).density (angEquiv.symm θ) =
      rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) :
    ∃ Hmin K : ℝ, 0 < Hmin ∧ 0 < K ∧ ∀ (F : SpeciesFamily 1) (label : Fin F.count → Fin 4),
      Hmin * nonreferenceRootWeight F label ≤
        (∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal) +
          K * Real.sqrt (rootDistanceBudget F (Fin.cases (ordinaryReferenceAbsolute h) σ) label) := by
  classical
  have hpos := same_chart_entropy_positive D hh hhr σ hσ
  choose Kj hKj hbound using fun j : Fin 3 =>
    ordinaryEntropy_positive_root_distance h (σ j)
      (ordinaryRoot_density_continuous_positive D h σ hσ j).1
      (ordinaryRoot_density_continuous_positive D h σ hσ j).2
  let Hmin := min (ordinaryEntropy h (σ 0)).toReal
    (min (ordinaryEntropy h (σ 1)).toReal (ordinaryEntropy h (σ 2)).toReal)
  let K := 1 + ∑ j, Kj j
  have hH : 0 < Hmin := lt_min (hpos 0) (lt_min (hpos 1) (hpos 2))
  have hKs : 0 ≤ ∑ j, Kj j := Finset.sum_nonneg fun j _ => (hKj j).le
  have hK : 0 < K := by dsimp [K]; linarith
  have hKle (j : Fin 3) : Kj j ≤ K := by
    have he := Finset.single_le_sum (fun i _ => (hKj i).le) (Finset.mem_univ j)
    dsimp only [K]
    linarith
  have hHle (j : Fin 3) : Hmin ≤ (ordinaryEntropy h (σ j)).toReal := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Hmin, K, hH, hK, fun F label => ?_⟩
  let R : Fin 4 → AbsoluteDensity 1 := Fin.cases (ordinaryReferenceAbsolute h) σ
  have hpoint (i : Fin 4) (ρ : AbsoluteDensity 1) :
      Hmin * (if i = 0 then 0 else 1) ≤ (ordinaryEntropy h ρ).toReal +
        K * Real.sqrt (rootDistanceSq ρ (R i)) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [if_pos rfl, mul_zero]
      exact add_nonneg ENNReal.toReal_nonneg (mul_nonneg hK.le (Real.sqrt_nonneg _))
    · simp only [Fin.succ_ne_zero, ite_false, mul_one]
      change Hmin ≤ (ordinaryEntropy h ρ).toReal + K * Real.sqrt (rootDistanceSq ρ (σ j))
      exact ((hHle j).trans (hbound j ρ)).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hKle j) (Real.sqrt_nonneg _)))
  have hw := Finset.sum_le_sum fun s (_ : s ∈ (Finset.univ : Finset (Fin F.count))) =>
    mul_le_mul_of_nonneg_left (hpoint (label s) (F.density s)) (F.weight_nonneg s)
  have hl : (∑ s, F.weight s * (Hmin * (if label s = 0 then 0 else 1))) =
      Hmin * nonreferenceRootWeight F label := by
    unfold nonreferenceRootWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    split_ifs <;> ring
  have hr : (∑ s, F.weight s * ((ordinaryEntropy h (F.density s)).toReal +
      K * Real.sqrt (rootDistanceSq (F.density s) (R (label s))))) =
      (∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal) +
        K * ∑ s, F.weight s * Real.sqrt (rootDistanceSq (F.density s) (R (label s))) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    ring
  rw [hl, hr] at hw
  exact hw.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (weighted_sqrt_budget F R label) hK.le))

end DGPS.Examples.ThreeSpeciesCircle
