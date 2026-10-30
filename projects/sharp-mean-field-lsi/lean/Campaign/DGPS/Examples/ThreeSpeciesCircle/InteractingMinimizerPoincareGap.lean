import DGPS.Examples.ThreeSpeciesCircle.InteractingMinimizerPositivity
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarRateSqueeze
import DGPS.Analysis.WeightedRateComparison

/-! Native Poincare gaps for every actual scalar minimizer. The full original
weak-H1 test domain is transported by bounded positive densities. No Euler,
regularity, branch classification or minimizer-nearness premise is imposed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual bounded-density comparison on all native weak-H1 tests. -/
theorem boundedReference_poincare_sandwich (P Q : BoundedPositiveReference 1)
    {l L : ℝ} (hl : 0 < l) (hL : 0 < L)
    (hlo : ∀ᵐ x ∂haar 1, l * P.density x ≤ Q.density x)
    (hhi : ∀ᵐ x ∂haar 1, Q.density x ≤ L * P.density x) :
    ENNReal.ofReal (l / L) *
        poincareRate (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) ≤
      poincareRate (⟨Q.measure, Q.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) := by
  have ht (f : WeakH1Test
      (⟨Q.measure, Q.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1))) :
      IsMeasureWeakGradient
        (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) f.fn f.grad :=
    (isMeasureWeakGradient_iff P).2 ((isWeightedWeakGradient_iff P).2
      ((isWeightedWeakGradient_iff Q).1 ((isMeasureWeakGradient_iff Q).1 f.isWeak)))
  have hc := DGPS.Examples.ex007_poincareRateOn_core (fun _ => True) hl hL
    (DGPS.Examples.ex007_le_measure P Q hl hlo)
    (DGPS.Examples.ex007_measure_le P Q hhi) ht
  rw [DGPS.Examples.ex007_poincareRate_eq_on
      (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)),
    DGPS.Examples.ex007_poincareRate_eq_on
      (⟨Q.measure, Q.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1))]
  exact hc

/-- Original-H1 nearness to a positive continuous root preserves any strict
subrate of its native Poincare rate. Arbitrary null-set representatives are allowed. -/
theorem ordinaryRoot_near_poincare_lower (σ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hup : ∀ x, 0 < u x)
    (hrep : σ.sqrt =ᵐ[haar 1] u) {r p : ℝ} (hr : 0 ≤ r) (hrp : r < p)
    (hPC : ENNReal.ofReal p ≤ poincareRate (densityMeasure σ)) :
    ∃ η : ℝ, 0 < η ∧ ∀ ρ : AbsoluteDensity 1,
      ordinaryRootH1Deviation σ ρ u ≤ η →
      ENNReal.ofReal r < poincareRate (densityMeasure ρ) := by
  have hp : 0 < p := hr.trans_lt hrp
  let q := min (1 / 4 : ℝ) ((p - r) / (8 * (p + 1)))
  have hq : 0 < q := lt_min (by norm_num) (div_pos (sub_pos.mpr hrp) (by positivity))
  have hq4 : q ≤ 1 / 4 := min_le_left _ _
  have hqp : q * (p + 1) ≤ (p - r) / 8 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 8 * (p + 1))).1
      (min_le_right (1 / 4 : ℝ) ((p - r) / (8 * (p + 1))))
    change q * (8 * (p + 1)) ≤ p - r at ht
    nlinarith
  have hprod : 2 * q * (p + r) ≤ (p - r) / 2 := by
    nlinarith [mul_nonneg hq.le (show 0 ≤ p - r + 2 by linarith)]
  have hstrict : r < ((1 - q) ^ 2 / (1 + q) ^ 2) * p := by
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 1 + q))).2
    nlinarith [mul_nonneg (sub_pos.mpr hrp).le (sq_nonneg q)]
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hu.continuousOn
  let m := u x0
  have hm : 0 < m := hup x0
  obtain ⟨ηp, mp, hηp, hmp, hpositive⟩ := ordinaryRoot_near_positive_representative σ u hu hup hrep
  obtain ⟨P, hPμ, hPd⟩ := ordinaryRoot_boundedReference σ u hu hup hrep
  have hPprob : (⟨P.measure, P.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) =
      densityMeasure σ := ProbabilityMeasure.toMeasure_injective hPμ
  refine ⟨min ηp (m * q), lt_min hηp (mul_pos hm hq), fun ρ hnear => ?_⟩
  obtain ⟨v, hv, hvrep, hvl⟩ := hpositive ρ (hnear.trans (min_le_left _ _))
  have hvp : ∀ x, 0 < v x := fun x => hmp.trans_le (hvl x)
  obtain ⟨Q, hQμ, hQd⟩ := ordinaryRoot_boundedReference ρ v hv hvp hvrep
  have hQprob : (⟨Q.measure, Q.isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) =
      densityMeasure ρ := ProbabilityMeasure.toMeasure_injective hQμ
  have hclose := ordinaryRoot_relative_ae_near σ ρ u hu hup hrep hm
    (fun x => hx0 (Set.mem_univ x)) hq.le (hnear.trans (min_le_right _ _))
  have hlo : ∀ᵐ x ∂haar 1, (1 - q) ^ 2 * P.density x ≤ Q.density x := by
    filter_upwards [hclose, hvrep] with x hx he
    have hratio : 1 - q ≤ ρ.sqrt x / u x := by linarith [(abs_le.mp hx).1]
    have hl : (1 - q) * u x ≤ v x := by
      rw [← he]
      exact (le_div_iff₀ (hup x)).1 hratio
    rw [hPd, hQd]
    calc (1 - q) ^ 2 * u x ^ 2 = ((1 - q) * u x) ^ 2 := by ring
      _ ≤ v x ^ 2 := pow_le_pow_left₀ (mul_nonneg (by linarith) (hup x).le) hl 2
  have hhi : ∀ᵐ x ∂haar 1, Q.density x ≤ (1 + q) ^ 2 * P.density x := by
    filter_upwards [hclose, hvrep] with x hx he
    have hratio : ρ.sqrt x / u x ≤ 1 + q := by linarith [(abs_le.mp hx).2]
    have hl : v x ≤ (1 + q) * u x := by
      rw [← he]
      exact (div_le_iff₀ (hup x)).1 hratio
    rw [hPd, hQd]
    calc v x ^ 2 ≤ ((1 + q) * u x) ^ 2 := pow_le_pow_left₀ (hvp x).le hl 2
      _ = (1 + q) ^ 2 * u x ^ 2 := by ring
  have hc := boundedReference_poincare_sandwich P Q
    (sq_pos_of_pos (by linarith : 0 < 1 - q))
    (sq_pos_of_pos (by positivity : 0 < 1 + q)) hlo hhi
  rw [hPprob, hQprob] at hc
  have he := (mul_le_mul' (le_refl (ENNReal.ofReal ((1 - q) ^ 2 / (1 + q) ^ 2))) hPC).trans hc
  rw [← ENNReal.ofReal_mul (div_nonneg (sq_nonneg _) (sq_nonneg _))] at he
  exact (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hstrict, hr.trans_lt hstrict⟩).trans_le he

private theorem deviation_change_rep_pc (σ ρ : AbsoluteDensity 1) (u : Torus 1 → ℝ)
    (hu : σ.sqrt =ᵐ[haar 1] u) :
    ordinaryRootH1Deviation σ ρ σ.sqrt = ordinaryRootH1Deviation σ ρ u := by
  unfold ordinaryRootH1Deviation
  rw [eLpNorm_congr_ae (hu.mono fun x hx => by
    change ρ.sqrt x - σ.sqrt x = ρ.sqrt x - u x
    rw [hx])]

/-- Every actual scalar minimizer has a uniform strict native Poincare gap.
The same ordinary graph is retained, but no nearness, positivity, Euler or
classification conclusion is assumed. Constants precede coupling and minimizer. -/
theorem elementaryModel_minimizer_poincare_gap_of_graph (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 κ : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < κ ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            ENNReal.ofReal ((scalarRate (modelData h ε) b).toReal + κ) ≤
                poincareRate (densityMeasure ρ) ∧
              scalarRate (modelData h ε) b < poincareRate (densityMeasure ρ) := by
  classical
  obtain ⟨k, δP, hk, hδP, hδPr, hPC⟩ := ordinaryRoot_native_poincare_lower D
  obtain ⟨δL, hδL, hδLr, hlocal⟩ := elementaryModel_minimizer_fourRoot_localization D
  obtain ⟨δB, hδB, _, hbarrier⟩ := elementaryModel_scalar_trial_below_reference_barrier D
  refine ⟨min δP (min δL δB), lt_min hδP (lt_min hδL hδB),
    (min_le_left _ _).trans hδPr, fun h hh hhd => ?_⟩
  have hhP := hhd.trans_le (min_le_left _ _)
  have hhL := hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhB := hhd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hhD : h < D.radius := hhP.trans_le hδPr
  obtain ⟨σ, εL, KL, hσ, hεL, hεLmax, hKL, hloc⟩ := hlocal h hh hhL
  obtain ⟨τ, rB, εB, ηB, _, hεB, _, hηB, hB⟩ := hbarrier h hh hhB
  obtain ⟨σT, _, hposT, hquotT, _, _, _, _, hrate⟩ := D.roots h hh hhD
  obtain ⟨εS, KS, hεS, _, hKS, hTrial⟩ :=
    ordinaryRoot_interacting_scalar_trial_linear hh (σT 0) (hposT 0) (hquotT 0)
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let gap := DGPS.Circle.AngularNormalization.a0 * (4 * k / 5) * h ^ 2
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hgap : 0 < gap := by
    dsimp only [gap]
    have ha0 : 0 < DGPS.Circle.AngularNormalization.a0 := by
      unfold DGPS.Circle.AngularNormalization.a0
      positivity
    positivity
  choose u hu hup hrep using fun j => ordinaryChart_positiveContinuousRoot h
    (chartU_isC2_STR02924 D.ψ h (D.Z j h)) (σ j) (hσ j)
  have hPj (j : Fin 3) : ENNReal.ofReal (a + gap) ≤ poincareRate (densityMeasure (σ j)) := by
    have ht := hPC h hh hhP j (σ j) (hσ j)
    convert ht using 1
    congr 1
    dsimp only [a, gap]
    rw [hrate j]
    ring
  choose ηj hηj hnear using fun j => ordinaryRoot_near_poincare_lower
    (σ j) (u j) (hu j) (hup j) (hrep j)
    (show 0 ≤ a + gap / 2 by positivity)
    (show a + gap / 2 < a + gap by linarith) (hPj j)
  let η := min ηB (min (ηj 0) (min (ηj 1) (ηj 2)))
  have hη : 0 < η := lt_min hηB (lt_min (hηj 0) (lt_min (hηj 1) (hηj 2)))
  have hηjle (j : Fin 3) : η ≤ ηj j := by
    fin_cases j
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let ε0 := min εL (min εB (min εS (min (η ^ 2 / KL) (gap / (4 * KS)))))
  have hε0 : 0 < ε0 := lt_min hεL (lt_min hεB (lt_min hεS
    (lt_min (div_pos (sq_pos_of_pos hη) hKL) (div_pos hgap (by positivity)))))
  refine ⟨ε0, gap / 4, hε0, (min_le_left _ _).trans hεLmax, by positivity,
    fun ε hε hεsmall b ρ hG hmin => ?_⟩
  have heL : ε < εL := hεsmall.trans_le (min_le_left _ _)
  have heB : ε < εB := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heS : ε < εS := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heK : KL * ε < η ^ 2 := by
    have he := hεsmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))
    have ht := (lt_div_iff₀ hKL).1 he
    nlinarith
  have heRate : KS * ε < gap / 4 := by
    have he := hεsmall.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))
    have ht := (lt_div_iff₀ (by positivity : 0 < 4 * KS)).1 he
    nlinarith
  have hdist := (hloc ε hε heL b ρ hG hmin).trans_lt heK
  obtain ⟨i, hi⟩ := ordinaryFourRootH1Distance_attained h σ ρ
  have hclose : ordinaryFourRootH1Distance h σ ρ ≤ η := by
    nlinarith [sq_nonneg (ordinaryFourRootH1Distance h σ ρ + η)]
  have hcase (i : Fin 4) :
      ordinaryRootH1Deviation (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1)
        (ordinaryReferenceAbsolute h) σ i) ρ
        (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1)
          (ordinaryReferenceAbsolute h) σ i).sqrt ≤ η →
      ENNReal.ofReal (a + gap / 2) < poincareRate (densityMeasure ρ) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hn
      obtain ⟨htrial, hb⟩ := hB ε hε heB b
      have hlo := hb ρ hG (hn.trans (min_le_left _ _))
      have hhi : scalarQuotient (modelData h ε) b ρ < ENNReal.ofReal rB := by
        rw [hmin]
        exact (scalarRate_le_quotient (modelData h ε) b τ htrial.1).trans_lt htrial.2
      exact False.elim ((not_lt_of_ge hlo) hhi)
    · intro hn
      change ordinaryRootH1Deviation (σ j) ρ (σ j).sqrt ≤ η at hn
      rw [deviation_change_rep_pc (σ j) ρ (u j) (hrep j)] at hn
      exact hnear j ρ (hn.trans (hηjle j))
  have hPCρ := hcase i (hi.le.trans hclose)
  obtain ⟨hTG, hTQ⟩ := hTrial ε hε heS b
  have hR : scalarRate (modelData h ε) b ≤ ENNReal.ofReal (a + gap / 4) :=
    ((scalarRate_le_quotient (modelData h ε) b (σT 0) hTG).trans hTQ).trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  have hRreal : (scalarRate (modelData h ε) b).toReal ≤ a + gap / 4 := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hR
    rwa [ENNReal.toReal_ofReal (by positivity : 0 ≤ a + gap / 4)] at ht
  constructor
  · exact (ENNReal.ofReal_le_ofReal (by linarith :
      (scalarRate (modelData h ε) b).toReal + gap / 4 ≤ a + gap / 2)).trans hPCρ.le
  · exact hR.trans_lt ((ENNReal.ofReal_le_ofReal (by linarith :
      a + gap / 4 ≤ a + gap / 2)).trans_lt hPCρ)

/-- Actual public factory, with the ordinary graph selected internally. -/
theorem elementaryModel_minimizer_poincare_gap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 κ : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < κ ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            ENNReal.ofReal ((scalarRate (modelData h ε) b).toReal + κ) ≤
                poincareRate (densityMeasure ρ) ∧
              scalarRate (modelData h ε) b < poincareRate (densityMeasure ρ) := by
  obtain ⟨D⟩ := exists_ordinaryRootGraphData
  obtain ⟨δ, hδ, _, hmain⟩ := elementaryModel_minimizer_poincare_gap_of_graph D
  exact ⟨δ, hδ, hmain⟩

end DGPS.Examples.ThreeSpeciesCircle
