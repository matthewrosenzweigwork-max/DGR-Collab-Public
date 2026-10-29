import LeanResearch.PeriodicAttractiveLogGas.StationaryLevelCircles
import LeanResearch.PeriodicAttractiveLogGas.StationaryCurveLength
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! Closed regular level curves in the proof of source Lemma `lem:iso`.
Positive return times are derived from the actual physical length formula
and the finite physical length of the level, not assumed as ODE data. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal NNReal
namespace PeriodicAttractiveLogGas.StationaryClosedCurves
open StationaryLevelCircles StationaryCurveLength StationaryCoarea StationarySard

/-- A regular trajectory cannot remain injective on arbitrarily long
intervals: its physical length grows at least linearly, whereas the entire
level has finite physical length. -/
theorem exists_positive_period_of_regular_trajectory {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {γ : ℝ → PlanarSpace}
    (hγ : ∀ s, HasDerivAt γ (tangentField v (γ s)) s)
    (hlevel : ∀ s, v (torusQuotient (γ s)) = t)
    {ε : ℝ} (hε : 0 < ε) (hspeed : ∀ s, ε ≤ ‖tangentField v (γ s)‖) :
    ∃ P : ℝ, 0 < P ∧ Function.Periodic (fun s => torusQuotient (γ s)) P := by
  classical
  by_contra hperiod
  have hinj : Function.Injective (fun s => torusQuotient (γ s)) := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hperiod ⟨b - a, sub_pos.mpr hlt, tangent_trajectory_periodic_of_eq hv hγ hab⟩
    · exact hperiod ⟨a - b, sub_pos.mpr hgt, tangent_trajectory_periodic_of_eq hv hγ hab.symm⟩
  let L := physicalCurveMeasure {z : Torus | v z = t}
  have hL : L < (∞ : ℝ≥0∞) := physicalCurveMeasure_level_lt_top (hv.of_le (by norm_num)) ht
  let T : ℝ := (L.toReal + 1) / ε
  have hT : 0 < T := by dsimp only [T]; positivity
  have hlen := length_Icc (a := 0) (b := T)
    (fun s _ => (hγ s).hasDerivWithinAt)
    (fun s _ => by
      intro hz
      have hh := hspeed s
      rw [hz, norm_zero] at hh
      linarith)
    (hinj.injOn (s := Icc 0 T))
  have hh : ENNReal.ofReal ε * ENNReal.ofReal T ≤ L := by
    calc
      _ = ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal ε := by
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
          univ_inter, Real.volume_Icc, sub_zero]
      _ ≤ ∫⁻ s in Icc (0 : ℝ) T, ENNReal.ofReal ‖tangentField v (γ s)‖ :=
        lintegral_mono fun s => ENNReal.ofReal_le_ofReal (hspeed s)
      _ = physicalCurveMeasure ((fun s => torusQuotient (γ s)) '' Icc (0 : ℝ) T) := hlen.symm
      _ ≤ L := measure_mono (by rintro z ⟨s, _, rfl⟩; exact hlevel s)
  have hr := ENNReal.toReal_mono hL.ne hh
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε.le, ENNReal.toReal_ofReal hT.le] at hr
  have hid : ε * T = L.toReal + 1 := by dsimp only [T]; field_simp
  rw [hid] at hr
  linarith

/-- Every nonempty regular level carries the original periodic tangent
trajectory through each specified point, with a genuine positive period. -/
theorem exists_periodic_regular_trajectory {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {a : PlanarSpace} (ha : v (torusQuotient a) = t) :
    ∃ γ : ℝ → PlanarSpace, γ 0 = a ∧
      (∀ s, HasDerivAt γ (tangentField v (γ s)) s) ∧
      (∀ s, v (torusQuotient (γ s)) = t) ∧
      ∃ P : ℝ, 0 < P ∧ Function.Periodic (fun s => torusQuotient (γ s)) P := by
  obtain ⟨γ, hγ0, hγ, hlevel, ε, hε, hspeed, _, _⟩ :=
    exists_global_regular_tangent_trajectory hv ht ha
  exact ⟨γ, hγ0, hγ, hlevel, exists_positive_period_of_regular_trajectory hv ht hγ hlevel hε hspeed⟩


/-- A nonzero velocity gives a genuine gap before the first possible return
to the same torus point. Local injectivity of the physical quotient is
used before passing to the punctured-neighborhood derivative estimate. -/
theorem quotient_return_gap {γ : ℝ → PlanarSpace} {w : PlanarSpace}
    (hγ : HasDerivAt γ w 0) (hw : w ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
      torusQuotient (γ s) ≠ torusQuotient (γ 0) := by
  have hb : ∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ Metric.ball (γ 0) (1 / 8 : ℝ) :=
    hγ.continuousAt.eventually_mem (Metric.ball_mem_nhds _ (by norm_num))
  have hn : ∀ᶠ s in 𝓝[≠] (0 : ℝ), torusQuotient (γ s) ≠ torusQuotient (γ 0) := by
    filter_upwards [hγ.eventually_ne (c := γ 0) hw, hb.filter_mono nhdsWithin_le_nhds]
      with s hs hbs
    intro he
    have hi := (physicalQuotient_isometry_ball (γ 0)).injective
    have hh : (⟨γ s, hbs⟩ : Metric.ball (γ 0) (1 / 8 : ℝ)) =
        ⟨γ 0, Metric.mem_ball_self (by norm_num)⟩ := by
      apply hi
      exact congrArg physicalEquiv he
    exact hs (congrArg Subtype.val hh)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hn)
  refine ⟨δ, hδ, fun s hs hsmall => ?_⟩
  exact hball (by simpa only [Real.dist_eq, sub_zero] using hsmall)
    (by simpa only [mem_compl_iff, mem_singleton_iff] using (abs_pos.mp hs))

/-- The least positive return exists and gives one injective traversal.
The compact minimization avoids assuming either a period lattice or a
circle classification for the level. -/
theorem exists_least_period_and_injective {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x)))
    {γ : ℝ → PlanarSpace}
    (hγ : ∀ s, HasDerivAt γ (tangentField v (γ s)) s)
    (hn : tangentField v (γ 0) ≠ 0)
    (hperiod : ∃ P : ℝ, 0 < P ∧ Function.Periodic (fun s => torusQuotient (γ s)) P) :
    ∃ P : ℝ, 0 < P ∧ Function.Periodic (fun s => torusQuotient (γ s)) P ∧
      (∀ s : ℝ, 0 < s → torusQuotient (γ s) = torusQuotient (γ 0) → P ≤ s) ∧
      InjOn (fun s => torusQuotient (γ s)) (Ico 0 P) := by
  obtain ⟨δ, hδ, hgap⟩ := quotient_return_gap (hγ 0) hn
  obtain ⟨P, hP, hp⟩ := hperiod
  have hreturn (s : ℝ) (hs : 0 < s) (he : torusQuotient (γ s) = torusQuotient (γ 0)) :
      δ ≤ s := by
    by_contra hlt
    have habs : |s| = s := abs_of_pos hs
    exact hgap s (by rwa [habs]) (by rw [habs]; exact lt_of_not_ge hlt) he
  let S : Set ℝ := Icc δ P ∩ {s | torusQuotient (γ s) = torusQuotient (γ 0)}
  have hc : Continuous (fun s => torusQuotient (γ s)) :=
    isOpenQuotientMap_torusQuotient.continuous.comp
      (continuous_iff_continuousAt.mpr fun s => (hγ s).continuousAt)
  have hSc : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hc continuous_const)
  obtain ⟨q, hq⟩ := hSc.exists_isLeast ⟨P, ⟨⟨hreturn P hP hp.eq, le_rfl⟩, hp.eq⟩⟩
  have hq0 : 0 < q := hδ.trans_le hq.1.1.1
  have hqp := tangent_trajectory_periodic_of_eq hv hγ hq.1.2.symm
  have hmin (s : ℝ) (hs : 0 < s) (he : torusQuotient (γ s) = torusQuotient (γ 0)) : q ≤ s := by
    by_cases hsP : s ≤ P
    · exact hq.2 ⟨⟨hreturn s hs he, hsP⟩, he⟩
    · exact hq.1.1.2.trans (le_of_not_ge hsP)
  refine ⟨q, hq0, by simpa only [sub_zero] using hqp, hmin, ?_⟩
  intro a ha b hb he
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hh := hmin (b - a) (sub_pos.mpr hlt) (tangent_trajectory_periodic_of_eq hv hγ he).eq
    linarith only [hh, ha.1, hb.2]
  · have hh := hmin (a - b) (sub_pos.mpr hgt) (tangent_trajectory_periodic_of_eq hv hγ he.symm).eq
    linarith only [hh, hb.1, ha.2]

/-- Actual simple periodic regular-level trajectories through every point.
Nonzero speed, existence of a positive return, and minimality of the
positive period are all derived from smoothness and regularity. -/
theorem exists_simple_periodic_regular_trajectory {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {a : PlanarSpace} (ha : v (torusQuotient a) = t) :
    ∃ γ : ℝ → PlanarSpace, γ 0 = a ∧
      (∀ s, HasDerivAt γ (tangentField v (γ s)) s) ∧
      (∀ s, v (torusQuotient (γ s)) = t) ∧
      ∃ P : ℝ, 0 < P ∧ Function.Periodic (fun s => torusQuotient (γ s)) P ∧
        InjOn (fun s => torusQuotient (γ s)) (Ico 0 P) := by
  obtain ⟨γ, hγ0, hγ, hlevel, ε, hε, hspeed, _, _⟩ :=
    exists_global_regular_tangent_trajectory hv ht ha
  have hn : tangentField v (γ 0) ≠ 0 := by
    intro hz
    have hh := hspeed 0
    rw [hz, norm_zero] at hh
    linarith
  obtain ⟨P, hP, hp, _, hi⟩ := exists_least_period_and_injective hv hγ hn
    (exists_positive_period_of_regular_trajectory hv ht hγ hlevel hε hspeed)
  exact ⟨γ, hγ0, hγ, hlevel, P, hP, hp, hi⟩


/-- An injective traversal on one half-open period descends to an actual
closed embedding of the additive circle. Its values on every real lift
agree with the original curve, not merely on a selected representative. -/
theorem circle_embedding_of_simple_periodic {P : ℝ} (hP : 0 < P)
    {φ : ℝ → Torus} (hc : Continuous φ) (hp : Function.Periodic φ P)
    (hi : InjOn φ (Ico 0 P)) :
    ∃ c : C(AddCircle P, Torus), Topology.IsClosedEmbedding c ∧
      (∀ s : ℝ, c (s : AddCircle P) = φ s) ∧ Set.range c = Set.range φ := by
  let : Fact (0 < P) := ⟨hP⟩
  let c : C(AddCircle P, Torus) :=
    ⟨AddCircle.liftIco P 0 φ, AddCircle.liftIco_zero_continuous hp.eq.symm hc.continuousOn⟩
  have hl : AddCircle.liftIco P 0 φ = hp.lift := by
    funext z
    obtain ⟨s, hs, rfl⟩ := AddCircle.eq_coe_Ico z
    rw [AddCircle.liftIco_zero_coe_apply hs, Function.Periodic.lift_coe]
  have he (s : ℝ) : c (s : AddCircle P) = φ s := by
    change AddCircle.liftIco P 0 φ (s : AddCircle P) = φ s
    rw [hl, Function.Periodic.lift_coe]
  have hci : Function.Injective c := by
    intro x y hxy
    obtain ⟨s, hs, rfl⟩ := AddCircle.eq_coe_Ico x
    obtain ⟨r, hr, rfl⟩ := AddCircle.eq_coe_Ico y
    rw [he, he] at hxy
    exact congrArg (fun a : ℝ => (a : AddCircle P)) (hi hs hr hxy)
  refine ⟨c, c.continuous.isClosedEmbedding hci, he, ?_⟩
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨s, _, rfl⟩ := AddCircle.eq_coe_Ico a
    exact ⟨s, (he s).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(s : AddCircle P), he s⟩

/-- A literal embedded circle through each point of a regular level,
together with its original nonvanishing tangent-field parametrization.
Identification with the whole connected component is a separate obligation. -/
theorem exists_embedded_regular_level_circle {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {a : PlanarSpace} (ha : v (torusQuotient a) = t) :
    ∃ γ : ℝ → PlanarSpace, γ 0 = a ∧
      (∀ s, HasDerivAt γ (tangentField v (γ s)) s) ∧
      (∀ s, v (torusQuotient (γ s)) = t) ∧
      ∃ P : ℝ, 0 < P ∧ ∃ c : C(AddCircle P, Torus), Topology.IsClosedEmbedding c ∧
        (∀ s : ℝ, c (s : AddCircle P) = torusQuotient (γ s)) ∧
        Set.range c = Set.range (fun s => torusQuotient (γ s)) := by
  obtain ⟨γ, hγ0, hγ, hlevel, P, hP, hp, hi⟩ := exists_simple_periodic_regular_trajectory hv ht ha
  have hc := isOpenQuotientMap_torusQuotient.continuous.comp
    (continuous_iff_continuousAt.mpr fun s => (hγ s).continuousAt)
  exact ⟨γ, hγ0, hγ, hlevel, P, hP, circle_embedding_of_simple_periodic hP hc hp hi⟩

end PeriodicAttractiveLogGas.StationaryClosedCurves
