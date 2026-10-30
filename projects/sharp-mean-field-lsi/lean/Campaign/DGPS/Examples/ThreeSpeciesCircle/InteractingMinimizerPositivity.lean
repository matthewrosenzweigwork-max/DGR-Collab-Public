import DGPS.Examples.ThreeSpeciesCircle.InteractingMinimizerLocalization
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitMomentError

/-! Every actual scalar minimizer has a positive continuous square-root
representative for small coupling. Nearness, reference exclusion and the lower
bound are derived from actual producers on the full original absolute H1 domain. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Near a fixed positive continuous H1 root, genuine one-dimensional embedding
gives a positive continuous representative of every original absolute H1 root.
The stored representative is only changed almost everywhere. -/
theorem ordinaryRoot_near_positive_representative (σ : AbsoluteDensity 1)
    (u : Torus 1 → ℝ) (hu : Continuous u) (hupos : ∀ x, 0 < u x)
    (hurep : σ.sqrt =ᵐ[haar 1] u) :
    ∃ η m : ℝ, 0 < η ∧ 0 < m ∧ ∀ ρ : AbsoluteDensity 1,
      ordinaryRootH1Deviation σ ρ u ≤ η →
      ∃ v : Torus 1 → ℝ, Continuous v ∧ ρ.sqrt =ᵐ[haar 1] v ∧
        ∀ x, m ≤ v x := by
  obtain ⟨x0, _, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hu.continuousOn
  let m := u x0
  have hm : 0 < m := hupos x0
  refine ⟨m / 2, m / 2, half_pos hm, half_pos hm, fun ρ hnear => ?_⟩
  have hclose := ordinaryRoot_relative_ae_near σ ρ u hu hupos hurep hm
    (fun x => hx0 (Set.mem_univ x)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by simpa only [div_eq_mul_inv, one_mul] using hnear)
  have hlower : ∀ᵐ x ∂haar 1, m / 2 ≤ ρ.sqrt x := by
    filter_upwards [hclose] with x hx
    have hxlo := (abs_le.mp hx).1
    have hratio : (1 / 2 : ℝ) ≤ ρ.sqrt x / u x := by linarith
    have hmul := (le_div_iff₀ (hupos x)).mp hratio
    have hmin := hx0 (Set.mem_univ x)
    change m ≤ u x at hmin
    nlinarith
  obtain ⟨v, hvc, hvae, _, _⟩ := exists_continuous_rep_one
    (isWeakGradient_weakGradient ρ.sqrt_mem)
  have hmax : (fun x => max (v x) (m / 2)) =ᵐ[haar 1] v := by
    filter_upwards [hlower, hvae] with x hx he
    rw [he]
    exact max_eq_left hx
  have heq := MeasureTheory.Measure.eq_of_ae_eq hmax
    (hvc.max continuous_const) hvc
  refine ⟨v, hvc, hvae.symm, fun x => ?_⟩
  have hx := congrFun heq x
  exact (le_max_right (v x) (m / 2)).trans_eq hx

private theorem deviation_change_rep (σ ρ : AbsoluteDensity 1) (u : Torus 1 → ℝ)
    (hurep : σ.sqrt =ᵐ[haar 1] u) :
    ordinaryRootH1Deviation σ ρ σ.sqrt = ordinaryRootH1Deviation σ ρ u := by
  unfold ordinaryRootH1Deviation
  have he : (fun x => ρ.sqrt x - σ.sqrt x) =ᵐ[haar 1] fun x => ρ.sqrt x - u x :=
    hurep.mono fun x hx => by
      change ρ.sqrt x - σ.sqrt x = ρ.sqrt x - u x
      rw [hx]
  rw [eLpNorm_congr_ae he]

/-- For each fixed small field, a common positive lower bound is chosen before
the coupling, drift and EVERY actual scalar minimizer. The conclusion concerns
a genuine continuous representative, not arbitrary null-set values of the stored
root. No localization, barrier, positivity or regularity premise is supplied. -/
theorem elementaryModel_minimizer_positive_representative (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 m : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < m ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
            ∃ v : Torus 1 → ℝ, Continuous v ∧ ρ.sqrt =ᵐ[haar 1] v ∧
              ∀ x, m ≤ v x := by
  classical
  obtain ⟨δL, hδL, hδLr, hlocal⟩ := elementaryModel_minimizer_fourRoot_localization D
  obtain ⟨δB, hδB, _, hbarrier⟩ := elementaryModel_scalar_trial_below_reference_barrier D
  refine ⟨min δL δB, lt_min hδL hδB, (min_le_left _ _).trans hδLr,
    fun h hh hhd => ?_⟩
  obtain ⟨σ, εL, K, hσ, hεL, hεLmax, hK, hloc⟩ :=
    hlocal h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨τ, r, εB, ηB, _, hεB, _, hηB, hB⟩ :=
    hbarrier h hh (hhd.trans_le (min_le_right _ _))
  choose u hu hup hrep using fun j => ordinaryChart_positiveContinuousRoot h
    (chartU_isC2_STR02924 D.ψ h (D.Z j h)) (σ j) (hσ j)
  choose ηs ms hηs hms hpositive using fun j =>
    ordinaryRoot_near_positive_representative (σ j) (u j) (hu j) (hup j) (hrep j)
  let η := min ηB (min (ηs 0) (min (ηs 1) (ηs 2)))
  let m := min (ms 0) (min (ms 1) (ms 2))
  have hη : 0 < η := lt_min hηB (lt_min (hηs 0) (lt_min (hηs 1) (hηs 2)))
  have hm : 0 < m := lt_min (hms 0) (lt_min (hms 1) (hms 2))
  have hηroot : ∀ j : Fin 3, η ≤ ηs j := by
    intro j
    fin_cases j
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hmroot : ∀ j : Fin 3, m ≤ ms j := by
    intro j
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min εL (min εB (η ^ 2 / K)), m,
    lt_min hεL (lt_min hεB (div_pos (sq_pos_of_pos hη) hK)),
    (min_le_left _ _).trans hεLmax, hm, fun ε hε hεsmall b ρ hG hmin => ?_⟩
  have heL : ε < εL := hεsmall.trans_le (min_le_left _ _)
  have heB : ε < εB := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heK : K * ε < η ^ 2 := by
    have he := hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have ht := (lt_div_iff₀ hK).mp he
    nlinarith
  have hdist := hloc ε hε heL b ρ hG hmin
  obtain ⟨i, hi⟩ := ordinaryFourRootH1Distance_attained h σ ρ
  have hnear : ordinaryFourRootH1Distance h σ ρ ≤ η := by
    have hstrict := hdist.trans_lt heK
    nlinarith [sq_nonneg (ordinaryFourRootH1Distance h σ ρ + η)]
  have hcase : ∀ i : Fin 4,
      ordinaryRootH1Deviation
        (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i)
        ρ (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ i).sqrt ≤ η →
      ∃ v : Torus 1 → ℝ, Continuous v ∧ ρ.sqrt =ᵐ[haar 1] v ∧ ∀ x, m ≤ v x := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hn
      change ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ≤ η at hn
      obtain ⟨htrial, hb⟩ := hB ε hε heB b
      have hlo := hb ρ hG (hn.trans (min_le_left _ _))
      have hhi : scalarQuotient (modelData h ε) b ρ < ENNReal.ofReal r := by
        rw [hmin]
        exact (scalarRate_le_quotient (modelData h ε) b τ htrial.1).trans_lt htrial.2
      exact False.elim ((not_lt_of_ge hlo) hhi)
    · intro hn
      change ordinaryRootH1Deviation (σ j) ρ (σ j).sqrt ≤ η at hn
      rw [deviation_change_rep (σ j) ρ (u j) (hrep j)] at hn
      obtain ⟨v, hvc, hvrep, hvpos⟩ := hpositive j ρ (hn.trans (hηroot j))
      exact ⟨v, hvc, hvrep, fun x => (hmroot j).trans (hvpos x)⟩
  exact hcase i (hi.le.trans hnear)

end DGPS.Examples.ThreeSpeciesCircle
