import LeanResearch.PeriodicAttractiveLogGas.OccupationDrift
import LeanResearch.PeriodicAttractiveLogGas.OccupationCentralRates
import LeanResearch.PeriodicAttractiveLogGas.OccupationMassCutoff
import LeanResearch.PeriodicAttractiveLogGas.IntegerBoxMassGeometry
import LeanResearch.PeriodicAttractiveLogGas.FiniteFibreEntropyBound

/-! Source2295–2338: finite boundary energy, concentration/counting and
specified-label comparison mechanisms for absolute occupation masses.
The quadratic drift and central increment inputs remain explicit. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationAbsoluteMass
open FiniteGraph FiniteEntropyLocalization
open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions
open DiscreteOccupationIdentities LabelGroundState OccupationProbability LabelRatioTransport

/-- Finite-graph indicators require no continuous differentiation. -/
def indicator {α : Type*} (B : Finset α) (x : α) : ℝ := by
  classical
  exact if x ∈ B then 1 else 0

theorem indicator_energy_eq_exterior {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (r : α → α → ℝ) (B : Finset α)
    (hb : ∀ x y, w x * r x y = w y * r y x) :
    energy w r (indicator B) = ∑ x, if x ∉ B then ∑ y ∈ B, w x * r x y else 0 := by
  classical
  have hswap : (∑ x, ∑ y, if x ∈ B ∧ y ∉ B then w x * r x y else 0) =
      ∑ x, ∑ y, if x ∉ B ∧ y ∈ B then w x * r x y else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [hx, hy, hb y x]
  have hp (x y : α) : w x * r x y * (indicator B y-indicator B x)^2 =
      (if x ∈ B ∧ y ∉ B then w x * r x y else 0) +
      (if x ∉ B ∧ y ∈ B then w x * r x y else 0) := by
    by_cases hx : x ∈ B <;> by_cases hy : y ∈ B <;> simp [indicator, hx, hy]
  have he : (∑ x, ∑ y, if x ∉ B ∧ y ∈ B then w x * r x y else 0) =
      ∑ x, if x ∉ B then ∑ y ∈ B, w x * r x y else 0 := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ B
    · simp [hx]
    · simp only [hx, not_false_eq_true, true_and, ite_true]
      rw [← Finset.sum_filter]
      simp
  simp_rw [energy, hp]
  simp only [Finset.sum_add_distrib]
  rw [hswap, he]
  ring

theorem indicator_energy_le_exterior {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (r : α → α → ℝ) (B : Finset α)
    (hw : ∀ x, 0 ≤ w x) (hr : ∀ x y, 0 ≤ r x y)
    (hb : ∀ x y, w x * r x y = w y * r y x)
    {R : ℝ} (hout : ∀ x, (∑ y, r x y) ≤ R) :
    energy w r (indicator B) ≤ R * (∑ x, if x ∉ B then w x else 0) := by
  classical
  rw [indicator_energy_eq_exterior w r B hb, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ B
  · simp [hx]
  · simp only [hx, not_false_eq_true, ite_true]
    calc
      _ ≤ ∑ y, w x * r x y := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun y _ _ => mul_nonneg (hw x) (hr x y))
      _ = w x * ∑ y, r x y := (Finset.mul_sum _ _ _).symm
      _ ≤ w x * R := mul_le_mul_of_nonneg_left (hout x) (hw x)
      _ = _ := mul_comm _ _

/-- Ground-state coercivity applied to the actual finite indicator gives
its truncated moment from a pointwise coercive drift, without a moment premise. -/
theorem truncated_moment_of_drift {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (r : α → α → ℝ) (V H : α → ℝ) (B : Finset α)
    (hw : ∀ x, 0 ≤ w x) (hr : ∀ x y, 0 ≤ r x y)
    (hb : ∀ x y, w x * r x y = w y * r y x) (hV : ∀ x, 0 < V x)
    {a b R δ : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b) (hR : 0 ≤ R)
    (hmass : (∑ x, w x) ≤ 1)
    (hout : ∀ x, (∑ y, r x y) ≤ R)
    (hext : (∑ x, if x ∉ B then w x else 0) ≤ δ)
    (hdrift : ∀ x ∈ B, a*H x-b ≤ groundStatePotential r V x) :
    (∑ x ∈ B, w x * H x) ≤ (R*δ+b)/a := by
  classical
  have hgs := groundState_coercivity w r hw hr hb V hV (indicator B)
  have he := (indicator_energy_le_exterior w r B hw hr hb hout).trans
    (mul_le_mul_of_nonneg_left hext hR)
  have hlow : a*(∑ x ∈ B, w x*H x)-b*(∑ x ∈ B, w x) ≤
      ∑ x, w x * indicator B x^2 * groundStatePotential r V x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have heq : (∑ x, w x * indicator B x^2 * groundStatePotential r V x) =
        ∑ x ∈ B, w x * groundStatePotential r V x := by
      simp only [indicator]
      simp_rw [ite_pow, one_pow, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_ite, mul_one, mul_zero,
        ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      simp
    rw [heq]
    apply Finset.sum_le_sum
    intro x hx
    have hh := mul_le_mul_of_nonneg_left (hdrift x hx) (hw x)
    nlinarith only [hh]
  have hBmass : (∑ x ∈ B, w x) ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hw x)).trans hmass
  apply (le_div_iff₀ ha).mpr
  have hbb := mul_le_mul_of_nonneg_left hBmass hb₀
  nlinarith only [hlow, hgs, he, hbb]

/-- Finite Markov counting and the missing outer mass are both explicit.
The central moment is supplied by the preceding coercivity mechanism. -/
theorem central_mass_ge_half {α : Type*} [Fintype α] [DecidableEq α]
    (w H : α → ℝ) (B C : Finset α) (hw : ∀ x, 0 ≤ w x)
    (hH : ∀ x ∈ B, 0 ≤ H x) (hmass : (3/4:ℝ) ≤ ∑ x ∈ B, w x)
    {K T : ℝ} (hT : 0 < T) (hKT : 4*K ≤ T)
    (hmoment : (∑ x ∈ B, w x*H x) ≤ K)
    (htail : ∀ x ∈ B, x ∉ C → T ≤ H x) :
    (1/2:ℝ) ≤ ∑ x ∈ C, w x := by
  classical
  have htailmass : T*(∑ x ∈ B \ C, w x) ≤ K := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ x ∈ B \ C, w x*H x := by
        apply Finset.sum_le_sum
        intro x hx
        have hp := mul_le_mul_of_nonneg_left (htail x (Finset.mem_sdiff.mp hx).1
          (Finset.mem_sdiff.mp hx).2) (hw x)
        nlinarith only [hp]
      _ ≤ ∑ x ∈ B, w x*H x := Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun x hx _ => mul_nonneg (hw x) (hH x hx))
      _ ≤ K := hmoment
  have hsplit : (∑ x ∈ B, w x) = (∑ x ∈ B ∩ C, w x)+(∑ x ∈ B \ C, w x) := by
    rw [← Finset.sum_union (Finset.disjoint_left.mpr (by
      intro x hx hy; exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp hx).2))]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hinter : (∑ x ∈ B ∩ C, w x) ≤ ∑ x ∈ C, w x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun x _ _ => hw x)
  have hsmall : (∑ x ∈ B \ C, w x) ≤ 1/4 := by nlinarith only [htailmass, hKT, hT]
  linarith only [hsplit, hmass, hinter, hsmall]



theorem occupationRate_le_source {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) {m m' : OccupationState J N t} {a b : MeshIndex J}
    (h : PermittedMove hJ m m' a b) : occupationRate hJ β m m' ≤ m.val a := by
  rw [occupationRate_of_move hJ hJ2 β h]
  have hq : 0 ≤ qWeight hJ β m := ENNReal.toReal_nonneg
  have hq' : 0 ≤ qWeight hJ β m' := ENNReal.toReal_nonneg
  by_cases hz : qWeight hJ β m + qWeight hJ β m' = 0
  · simp only [hz, div_zero]
    exact Nat.cast_nonneg _
  · apply (div_le_iff₀ (lt_of_le_of_ne (add_nonneg hq hq') (Ne.symm hz))).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg (m.val a) : (0:ℝ) ≤ m.val a) hq]

/-- The actual suppressed occupation chain has at most four source-count
 contributions per cell. Invalid moves and empty source cells contribute zero. -/
theorem occupation_outgoing_le {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (β : ℝ) (m : OccupationState J N t) :
    (∑ m', occupationRate hJ β m m') ≤ 4*(N:ℝ) := by
  classical
  have hnon (m' : OccupationState J N t) (a b : MeshIndex J) :
      0 ≤ (if PermittedMove hJ m m' a b then (m.val a : ℝ) else 0) := by positivity
  have hpoint (m' : OccupationState J N t) : occupationRate hJ β m m' ≤
      ∑ a, ∑ b, if PermittedMove hJ m m' a b then (m.val a : ℝ) else 0 := by
    by_cases he : ∃ a b, PermittedMove hJ m m' a b
    · obtain ⟨a,b,h⟩ := he
      have h1 := Finset.single_le_sum (fun b _ => hnon m' a b) (Finset.mem_univ b)
      have h2 := Finset.single_le_sum (fun a _ => Finset.sum_nonneg (s := Finset.univ) (fun b _ => hnon m' a b))
        (Finset.mem_univ a)
      simp only [h, ite_true] at h1
      exact (occupationRate_le_source hJ (by omega) β h).trans (h1.trans h2)
    · rw [occupationRate_eq_zero hJ β he]
      exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => hnon m' a b))
  have hdir (a b : MeshIndex J) :
      (∑ m' : OccupationState J N t, if PermittedMove hJ m m' a b then (m.val a : ℝ) else 0) ≤
        if EdgeAdjacent J hJ a b then (m.val a : ℝ) else 0 := by
    by_cases he : ∃ m' : OccupationState J N t, PermittedMove hJ m m' a b
    · obtain ⟨z,hz⟩ := he
      rw [Finset.sum_eq_single z]
      · simp only [hz, hz.1, ite_true, le_refl]
      · intro v _ hv
        have hn : ¬ PermittedMove hJ m v a b := by
          intro hh
          apply hv
          exact Subtype.ext (hh.2.2.symm.trans hz.2.2)
        simp only [hn, ite_false]
      · simp
    · have hn : ∀ v : OccupationState J N t, ¬ PermittedMove hJ m v a b :=
        fun v hv => he ⟨v,hv⟩
      simp only [hn, ite_false, Finset.sum_const_zero]
      split <;> positivity
  have hcard (a : MeshIndex J) :
      (∑ b : MeshIndex J, if EdgeAdjacent J hJ a b then (1:ℝ) else 0) = 4 := by
    have hh := congrArg (fun k : ℕ => (k:ℝ)) (BoundaryEdgeSummation.card_cellNeighbors hJ hJ3 a)
    simpa only [BoundaryEdgeSummation.cellNeighbors, Finset.card_filter, Nat.cast_sum,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Nat.cast_ofNat] using hh
  calc
    _ ≤ ∑ m' : OccupationState J N t, ∑ a, ∑ b,
        if PermittedMove hJ m m' a b then (m.val a : ℝ) else 0 :=
      Finset.sum_le_sum (fun m' _ => hpoint m')
    _ = ∑ a, ∑ b, ∑ m' : OccupationState J N t,
        if PermittedMove hJ m m' a b then (m.val a : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ ≤ ∑ a, ∑ b, if EdgeAdjacent J hJ a b then (m.val a : ℝ) else 0 :=
      Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hdir a b))
    _ = ∑ a : MeshIndex J, (m.val a : ℝ)*4 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← hcard a, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split <;> simp
    _ = 4*(N:ℝ) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, m.property.1]
      ring

/-- Actual occupation boundary energy, retaining the original subprobability weights. -/
theorem occupation_indicator_energy {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (β : ℝ) (B : Finset (OccupationState J N t)) :
    occupationEnergy hJ β (indicator B) ≤
      4*(N:ℝ)*(∑ m, if m ∉ B then occupationWeight hJ β m else 0) := by
  classical
  exact indicator_energy_le_exterior (occupationWeight hJ β) (occupationRate hJ β) B
    (fun _ => ENNReal.toReal_nonneg) (occupationRate_nonneg hJ β)
    (occupation_detailed_balance hJ (by omega) β) (occupation_outgoing_le hJ hJ3 β)



/-- Smaller occupations are embedded in the original outer state space. -/
def innerProfiles {J N : ℕ} (t u : ℝ) : Finset (OccupationState J N t) := by
  classical
  exact Finset.univ.filter (fun m => m.val ∈ cappedOccupations J N u)

def liftOccupation {J N : ℕ} {t u : ℝ} (htu : u ≤ t)
    (m : OccupationState J N u) : OccupationState J N t :=
  ⟨m.val, m.property.1, fun a => (m.property.2 a).trans
    (mul_le_mul_of_nonneg_right htu (Nat.cast_nonneg N))⟩

theorem liftOccupation_image {J N : ℕ} {t u : ℝ} (htu : u ≤ t) :
    Finset.univ.image (liftOccupation (J:=J) (N:=N) htu) = innerProfiles (J:=J) (N:=N) t u := by
  classical
  ext m
  constructor
  · intro h
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, z.property⟩
  · intro h
    have hm := (Finset.mem_filter.mp h).2
    exact Finset.mem_image.mpr ⟨⟨m.val, hm⟩, Finset.mem_univ _, Subtype.ext rfl⟩

theorem inner_mass_eq {J N : ℕ} {t u : ℝ} (htu : u ≤ t) (hJ : 0 < J) (β : ℝ) :
    (∑ m ∈ innerProfiles (J:=J) (N:=N) t u, occupationWeight hJ β m) =
      occupationCapMass (N:=N) (t:=u) hJ β := by
  classical
  rw [← liftOccupation_image htu, Finset.sum_image]
  · rfl
  · intro a _ b _ h
    exact Subtype.ext (congrArg (fun m : OccupationState J N t => m.val) h)

theorem occupation_mass_le_one {J N : ℕ} {t β : ℝ} (hJ : 0 < J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) : occupationCapMass (N:=N) (t:=t) hJ β ≤ 1 := by
  let hprob := isProbabilityMeasure_greenGibbs N hN hβ hsub
  rw [← capMass_eq, labelCapMass_eq_actual hJ hN hβ hsub]
  have hh := ENNReal.toReal_mono (by simp :
      gibbsMeasure greenRealRepresentative N β Set.univ ≠ ⊤)
    (MeasureTheory.measure_mono (Set.subset_univ
      {X : Configuration N | OccupationCap t (configurationMeshLabel N J hJ X)}))
  simpa only [MeasureTheory.measure_univ, ENNReal.toReal_one] using hh

theorem occupation_inner_mass_complement {J N : ℕ} {t u β : ℝ}
    (htu : u ≤ t) (hJ : 0 < J) (hN : 2 ≤ N) (hβ : 0 ≤ β) (hsub : β < 4) :
    (∑ m ∈ innerProfiles (J:=J) (N:=N) t u, occupationWeight hJ β m) +
      (gibbsMeasure greenRealRepresentative N β
        (OccupationMassCutoff.badLabelEvent N J hJ u)).toReal = 1 := by
  let hprob := isProbabilityMeasure_greenGibbs N hN hβ hsub
  rw [inner_mass_eq htu hJ β, ← capMass_eq, labelCapMass_eq_actual hJ hN hβ hsub]
  exact MeasureTheory.probReal_add_probReal_compl
    (OccupationMassCutoff.measurableSet_goodLabelEvent N J hJ u)

theorem exterior_mass_le_bad {J N : ℕ} {t u β : ℝ}
    (htu : u ≤ t) (hJ : 0 < J) (hN : 2 ≤ N) (hβ : 0 ≤ β) (hsub : β < 4) :
    (by classical exact ∑ m : OccupationState J N t,
      if m ∉ innerProfiles t u then occupationWeight hJ β m else 0) ≤
      (gibbsMeasure greenRealRepresentative N β
        (OccupationMassCutoff.badLabelEvent N J hJ u)).toReal := by
  classical
  have hm := occupation_mass_le_one (t:=t) hJ hN hβ hsub
  have hc := occupation_inner_mass_complement (t:=t) htu hJ hN hβ hsub
  have he : (∑ m ∈ innerProfiles (J:=J) (N:=N) t u, occupationWeight hJ β m) +
      (∑ m : OccupationState J N t, if m ∉ innerProfiles t u then occupationWeight hJ β m else 0) =
      occupationCapMass (N:=N) (t:=t) hJ β := by
    have hi : (∑ m ∈ innerProfiles (J:=J) (N:=N) t u, occupationWeight hJ β m) =
        ∑ m : OccupationState J N t,
          if m ∈ innerProfiles t u then occupationWeight hJ β m else 0 := by
      rw [← Finset.sum_filter]
      simp
    rw [hi, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hx : m ∈ innerProfiles (J:=J) (N:=N) t u <;> simp [hx]
  linarith only [hm,hc,he]

/-- Actual source cutoff and original ground state give the truncated central
moment once the still-separate pointwise quadratic drift is supplied. -/
theorem occupation_moment_from_cutoff {β₀ lo u t : ℝ}
    (hβ₀ : 0 ≤ β₀) (hβ4 : β₀ < 4) (hlo : 0 < lo) (hgap : lo < u) (hu : u < 1)
    (htu : u ≤ t) {N J : ℕ}
    (hJ : HeavyScales.sourceResolution β₀ lo ≤ J)
    (hN : HeavyCoercivityConstants.particleThreshold β₀ lo ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hβle : β ≤ β₀)
    (H : OccupationState J N t → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hdrift : ∀ m ∈ innerProfiles (J:=J) (N:=N) t u,
      a*H m-b ≤ occupationW (SeparatedRadius.source_mesh_pos hJ) β m) :
    (∑ m ∈ innerProfiles (J:=J) (N:=N) t u,
      occupationWeight (SeparatedRadius.source_mesh_pos hJ) β m * H m) ≤
      (4*N*(72*HeavyCoercivityConstants.coercivityConstant β₀ lo /
        ((N:ℝ)^2*(u-lo)^2))+b)/a := by
  classical
  have hNt := OccupationMassCutoff.threshold_two hlo (hgap.trans hu) hN
  have hJ3 := SeparatedRadius.source_mesh_ge_three hJ
  have hbad := OccupationMassCutoff.bad_label_mass_bound hβ₀ hβ4 hlo hgap hu hJ hN hβ hβle
  exact truncated_moment_of_drift _ _ (occupationV _ β) H (innerProfiles t u)
    (fun _ => ENNReal.toReal_nonneg) (occupationRate_nonneg _ β)
    (occupation_detailed_balance _ (by omega) β)
    (occupationV_pos _ hNt hβ (hβle.trans_lt hβ4)) ha hb (by positivity)
    (occupation_mass_le_one _ hNt hβ (hβle.trans_lt hβ4))
    (occupation_outgoing_le _ hJ3 β)
    ((exterior_mass_le_bad htu _ hNt hβ (hβle.trans_lt hβ4)).trans hbad) hdrift



/-- The literal closed coordinate-sup ball, restricted to the actual finite states. -/
def coordinateBall {α : Type*} [Fintype α] {D : ℕ}
    (e : α → Fin D → ℤ) (y₀ : Fin D → ℤ) (R : ℝ) : Finset α := by
  classical
  exact Finset.univ.filter (fun x => ∀ i, |((e x i-y₀ i : ℤ) : ℝ)| ≤ R)

theorem coordinateBall_card {α : Type*} [Fintype α] {D : ℕ}
    (e : α → Fin D → ℤ) (he : Function.Injective e) (y₀ : Fin D → ℤ)
    {R : ℝ} (hR : 0 ≤ R) :
    (coordinateBall e y₀ R).card ≤ (2*⌊R⌋₊+1)^D := by
  classical
  let s := ⌊R⌋₊+1
  have hsub : (coordinateBall e y₀ R).image e ⊆
      IntegerBoxMassGeometry.containingBox s y₀ (fun _ => 0) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    apply (IntegerBoxMassGeometry.mem_containingBox_iff (by dsimp [s]; omega) y₀ _ _).mpr
    intro i
    have hxi := (Finset.mem_filter.mp hx).2 i
    have habs := congrArg (fun a : ℤ => (a:ℝ)) (Int.natCast_natAbs (e x i-y₀ i))
    simp only [Int.cast_natCast, Int.cast_abs] at habs
    have hn : (e x i-y₀ i).natAbs ≤ ⌊R⌋₊ :=
      (Nat.le_floor_iff hR).mpr (by rw [habs]; exact hxi)
    have hni : |e x i-y₀ i| ≤ (⌊R⌋₊:ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hn
    simpa only [mul_zero, sub_zero, s, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hni
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn (fun _ _ _ _ h => he h),
    IntegerBoxMassGeometry.card_containingBox (by dsimp [s]; omega)] at hc
  simpa only [s, show 2*(⌊R⌋₊+1)-1 = 2*⌊R⌋₊+1 by omega] using hc

theorem coordinateBall_card_scaled {α : Type*} [Fintype α] {D N : ℕ}
    (hN : 1 ≤ N) (e : α → Fin D → ℤ) (he : Function.Injective e) (y₀ : Fin D → ℤ)
    {M : ℝ} (hM : 0 ≤ M) :
    ((coordinateBall e y₀ (M*Real.sqrt N)).card : ℝ) ≤
      (2*M+1)^D * (N:ℝ)^((D:ℝ)/2) := by
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hS : 1 ≤ Real.sqrt (N:ℝ) := by simpa using Real.sqrt_le_sqrt hNr
  have hc : ((coordinateBall e y₀ (M*Real.sqrt N)).card : ℝ) ≤
      (2*(⌊M*Real.sqrt (N:ℝ)⌋₊:ℝ)+1)^D := by
    exact_mod_cast coordinateBall_card e he y₀ (mul_nonneg hM (Real.sqrt_nonneg _))
  have hf := Nat.floor_le (mul_nonneg hM (Real.sqrt_nonneg (N:ℝ)))
  have hside : 2*(⌊M*Real.sqrt (N:ℝ)⌋₊:ℝ)+1 ≤ (2*M+1)*Real.sqrt N := by nlinarith
  have hp : (2*(⌊M*Real.sqrt (N:ℝ)⌋₊:ℝ)+1)^D ≤ ((2*M+1)*Real.sqrt N)^D := by
    gcongr
  have hs := Real.rpow_div_two_eq_sqrt (D:ℝ) (Nat.cast_nonneg N)
  simp only [Real.rpow_natCast] at hs
  exact hc.trans (hp.trans_eq (by rw [mul_pow, ← hs]))

/-- Actual local log increments, rather than a density-oscillation premise,
compare every point of the true central ball with its center. -/
theorem point_le_center_of_increments {D N : ℕ} (hN : 0 < N)
    (y₀ y : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ) {M C T : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hMT : M*Real.sqrt N ≤ T)
    (hy : ∀ i, |((y i-y₀ i : ℤ):ℝ)| ≤ M*Real.sqrt N)
    (hw : 0 < w y) (hw₀ : 0 < w y₀)
    (hinc : IntegerBoxMassGeometry.LogIncrementBound y₀ T N C w) :
    w y ≤ Real.exp (4*D*C*(1+M^2))*w y₀ := by
  have hh := (IntegerBoxMassGeometry.central_log_difference_real hN y₀ y hC
    (mul_nonneg hM (Real.sqrt_nonneg _)) hMT hy w hinc).trans
      (IntegerBoxMassGeometry.radial_path_cost hN hC)
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have he : (M*Real.sqrt (N:ℝ))^2/N = M^2 := by
    rw [mul_pow, Real.sq_sqrt hNr.le, mul_div_cancel_right₀ _ hNr.ne']
  rw [he] at hh
  have hu := (abs_le.mp hh).2
  calc
    w y = Real.exp (Real.log (w y)) := (Real.exp_log hw).symm
    _ ≤ Real.exp (4*D*C*(1+M^2)+Real.log (w y₀)) := Real.exp_le_exp.mpr (by linarith only [hu])
    _ = _ := by rw [Real.exp_add, Real.exp_log hw₀]

/-- Counting every actual integer point cancels the power of N in the
central lower bound. The half-mass input is proved by the drift/Markov block. -/
theorem center_mass_from_ball {α : Type*} [Fintype α] {D N : ℕ}
    (hN : 1 ≤ N) (e : α → Fin D → ℤ) (he : Function.Injective e)
    (y₀ : Fin D → ℤ) (w : (Fin D → ℤ) → ℝ) {M C T : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hMT : M*Real.sqrt N ≤ T)
    (hw : ∀ x, 0 < w (e x)) (hw₀ : 0 < w y₀)
    (hinc : IntegerBoxMassGeometry.LogIncrementBound y₀ T N C w)
    (hmass : (1/2:ℝ) ≤ ∑ x ∈ coordinateBall e y₀ (M*Real.sqrt N), w (e x)) :
    (2*(2*M+1)^D*Real.exp (4*D*C*(1+M^2)))⁻¹ * (N:ℝ)^(-(D:ℝ)/2) ≤ w y₀ := by
  classical
  have hsum : (∑ x ∈ coordinateBall e y₀ (M*Real.sqrt N), w (e x)) ≤
      ((coordinateBall e y₀ (M*Real.sqrt N)).card:ℝ)*
        (Real.exp (4*D*C*(1+M^2))*w y₀) := by
    calc
      _ ≤ ∑ _x ∈ coordinateBall e y₀ (M*Real.sqrt N), Real.exp (4*D*C*(1+M^2))*w y₀ := by
        apply Finset.sum_le_sum
        intro x hx
        exact point_le_center_of_increments (by omega) y₀ (e x) w hM hC hMT
          (Finset.mem_filter.mp hx).2 (hw x) hw₀ hinc
      _ = _ := by simp
  have hc := mul_le_mul_of_nonneg_right (coordinateBall_card_scaled hN e he y₀ hM)
    (mul_pos (Real.exp_pos (4*(D:ℝ)*C*(1+M^2))) hw₀).le
  have htot := hmass.trans (hsum.trans hc)
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hnp : 0 < (N:ℝ)^((D:ℝ)/2) := Real.rpow_pos_of_pos hNr _
  have hdp : 0 < (2*M+1)^D := pow_pos (by linarith) _
  rw [show -(D:ℝ)/2 = -((D:ℝ)/2) by ring, Real.rpow_neg hNr.le]
  have hquot : 1/(2*(2*M+1)^D*Real.exp (4*D*C*(1+M^2))*(N:ℝ)^((D:ℝ)/2)) ≤ w y₀ := by
    apply (div_le_iff₀ (show 0 < 2*(2*M+1)^D*Real.exp (4*D*C*(1+M^2))*
      (N:ℝ)^((D:ℝ)/2) by positivity)).mpr
    nlinarith only [htot]
  simpa only [one_div, mul_inv_rev, mul_comm] using hquot


/-- The number of particles still in surplus relative to the destination profile. -/
def surplus {J : ℕ} (m n : MeshIndex J → ℕ) : ℕ := ∑ a, (m a-n a)

theorem surplus_le_total {J N : ℕ} {m n : MeshIndex J → ℕ}
    (hm : ∑ a, m a=N) : surplus m n ≤ N := by
  unfold surplus
  rw [← hm]
  exact Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)

theorem profile_eq_of_le {J N : ℕ} {m n : MeshIndex J → ℕ}
    (hm : ∑ a, m a=N) (hn : ∑ a, n a=N) (hle : ∀ a, m a≤n a) : m=n := by
  classical
  have hz : (∑ a, (n a-m a))=0 := by
    rw [Finset.sum_tsub_distrib Finset.univ (fun a _ => hle a), hm, hn, Nat.sub_self]
  funext a
  have hh : n a-m a≤0 := by
    rw [← hz]
    exact Finset.single_le_sum (fun x _ => Nat.zero_le (n x-m x)) (Finset.mem_univ a)
  exact Nat.le_antisymm (hle a) (by omega)

theorem surplus_zero_iff {J N : ℕ} {m n : MeshIndex J → ℕ}
    (hm : ∑ a, m a=N) (hn : ∑ a, n a=N) : surplus m n=0 ↔ m=n := by
  classical
  constructor
  · intro hz
    apply profile_eq_of_le hm hn
    intro a
    have hh : m a-n a≤0 := by
      rw [← hz]
      unfold surplus
      exact Finset.single_le_sum (fun x _ => Nat.zero_le (m x-n x)) (Finset.mem_univ a)
    omega
  · rintro rfl
    simp [surplus]

theorem surplus_deficit_cells {J N : ℕ} {m n : MeshIndex J → ℕ}
    (hm : ∑ a, m a=N) (hn : ∑ a, n a=N) (hne : m≠n) :
    ∃ a b, n a<m a ∧ m b<n b ∧ a≠b := by
  classical
  have ha : ∃ a, n a<m a := by
    by_contra h
    push Not at h
    exact hne (profile_eq_of_le hm hn h)
  have hb : ∃ b, m b<n b := by
    by_contra h
    push Not at h
    exact hne (profile_eq_of_le hn hm h).symm
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := hb
  exact ⟨a,b,ha,hb,by rintro rfl; omega⟩

/-- A genuine particle transfer decreases the remaining surplus by exactly one. -/
theorem surplus_move {J : ℕ} (m n : MeshIndex J → ℕ) {a b : MeshIndex J}
    (ha : n a<m a) (hb : m b<n b) (hab : a≠b) :
    surplus (moveOccupation m a b) n+1=surplus m n := by
  classical
  have hp : ∀ c, (moveOccupation m a b c-n c)+(if c=a then 1 else 0)=m c-n c := by
    intro c
    by_cases hc : c=a
    · subst c
      rw [moveOccupation_source m hab]
      simp only [ite_true]
      omega
    · by_cases hd : c=b
      · subst c
        rw [moveOccupation_target m hab]
        simp only [ite_eq_right hc]
        omega
      · rw [moveOccupation_other m (Ne.symm hc) (Ne.symm hd)]
        simp [hc]
  have hh := congrArg (fun f : MeshIndex J → ℕ => ∑ c, f c) (funext hp)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, surplus] using hh

theorem move_between {J : ℕ} (m n : MeshIndex J → ℕ) {a b : MeshIndex J}
    (ha : n a<m a) (hb : m b<n b) (hab : a≠b) (c : MeshIndex J) :
    min (m c) (n c) ≤ moveOccupation m a b c ∧
      moveOccupation m a b c ≤ max (m c) (n c) := by
  by_cases hc : a=c
  · subst c
    rw [moveOccupation_source m hab]
    omega
  · by_cases hd : b=c
    · subst c
      rw [moveOccupation_target m hab]
      omega
    · rw [moveOccupation_other m hc hd]
      exact ⟨min_le_left _ _, le_max_left _ _⟩

/-- The supplied surplus-to-deficit path uses actual transfers, has length at
most N, and never leaves the coordinate interval between its endpoints.
Its moves need not be mesh edges; they are used only for the Q-ratio estimate. -/
theorem profile_transfer_path {J N : ℕ} (m n : MeshIndex J → ℕ)
    (hm : ∑ a, m a=N) (hn : ∑ a, n a=N) :
    ∃ (l : ℕ) (γ : ℕ → MeshIndex J → ℕ), l≤N ∧ γ 0=m ∧ γ l=n ∧
      (∀ k, k≤l → (∑ a, γ k a)=N ∧
        ∀ a, min (m a) (n a)≤γ k a ∧ γ k a≤max (m a) (n a)) ∧
      (∀ k, k<l → ∃ a b, 1≤γ k a ∧ a≠b ∧ moveOccupation (γ k) a b=γ (k+1)) := by
  classical
  suffices h : ∀ d (m : MeshIndex J → ℕ), (∑ a,m a)=N → surplus m n=d →
      ∃ (l : ℕ) (γ : ℕ → MeshIndex J → ℕ), l≤d ∧ γ 0=m ∧ γ l=n ∧
        (∀ k, k≤l → (∑ a,γ k a)=N ∧
          ∀ a, min (m a) (n a)≤γ k a ∧ γ k a≤max (m a) (n a)) ∧
        (∀ k, k<l → ∃ a b, 1≤γ k a ∧ a≠b ∧ moveOccupation (γ k) a b=γ (k+1)) by
    obtain ⟨l,γ,hl,h0,he,hstay,hstep⟩ := h (surplus m n) m hm rfl
    exact ⟨l,γ,hl.trans (surplus_le_total hm),h0,he,hstay,hstep⟩
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro m hm hd
    by_cases he : m=n
    · subst m
      refine ⟨0,fun _ => n,Nat.zero_le _,rfl,rfl,?_,?_⟩
      · intro k _
        exact ⟨hn,fun a => by simp⟩
      · intro k hk
        omega
    obtain ⟨a,b,ha,hb,hab⟩ := surplus_deficit_cells hm hn he
    let m' := moveOccupation m a b
    have hm' : (∑ c,m' c)=N := by
      obtain ⟨η,i,_,_,hmove⟩ := exists_label_move m hm a b (by omega)
      change (∑ c,moveOccupation m a b c)=N
      rw [← hmove]
      exact sum_occupation _
    have hd' : surplus m' n<d := by
      have hh := surplus_move m n ha hb hab
      change surplus m' n+1=surplus m n at hh
      omega
    obtain ⟨l,γ,hl,h0,he',hstay,hstep⟩ := ih (surplus m' n) hd' m' hm' rfl
    let γ' : ℕ → MeshIndex J → ℕ := fun k => if k=0 then m else γ (k-1)
    refine ⟨l+1,γ',by omega,by simp [γ'],by simpa [γ'] using he',?_,?_⟩
    · intro k hk
      by_cases hk0 : k=0
      · subst k
        exact ⟨by simpa [γ'] using hm,fun c => by simp [γ']⟩
      · have hs := hstay (k-1) (by omega)
        refine ⟨by simpa [γ',hk0] using hs.1,?_⟩
        intro c
        have hc := hs.2 c
        have hc' := move_between m n ha hb hab c
        change min (m c) (n c)≤(if k=0 then m else γ (k-1)) c ∧
          (if k=0 then m else γ (k-1)) c≤max (m c) (n c)
        rw [ite_eq_right hk0]
        change min (m c) (n c)≤m' c ∧ m' c≤max (m c) (n c) at hc'
        omega
    · intro k hk
      by_cases hk0 : k=0
      · subst k
        refine ⟨a,b,by simpa [γ'] using (show 1≤m a by omega),hab,?_⟩
        simpa [γ'] using h0.symm
      · obtain ⟨c,e,hc,hce,hmv⟩ := hstep (k-1) (by omega)
        refine ⟨c,e,by simpa [γ',hk0] using hc,hce,?_⟩
        simpa [γ',hk0,show k-1+1=k by omega] using hmv


/-- Every intermediate profile stays in the original cap, including zero counts. -/
theorem transfer_path_capped {J N : ℕ} {t : ℝ} {m n : MeshIndex J → ℕ}
    (hm : m∈cappedOccupations J N t) (hn : n∈cappedOccupations J N t) :
    ∃ (l : ℕ) (γ : ℕ → MeshIndex J → ℕ), l≤N ∧ γ 0=m ∧ γ l=n ∧
      (∀ k, k≤l → γ k∈cappedOccupations J N t) ∧
      (∀ k, k<l → ∃ a b, 1≤γ k a ∧ a≠b ∧ moveOccupation (γ k) a b=γ (k+1)) := by
  obtain ⟨l,γ,hl,h0,he,hstay,hstep⟩ := profile_transfer_path m n hm.1 hn.1
  refine ⟨l,γ,hl,h0,he,?_,hstep⟩
  intro k hk
  refine ⟨(hstay k hk).1,?_⟩
  intro a
  have hh : (γ k a:ℝ)≤max (m a:ℝ) (n a:ℝ) := by
    exact_mod_cast (hstay k hk).2 a |>.2
  exact hh.trans (max_le (hm.2 a) (hn.2 a))

/-- Scalar telescoping is applied to the original Q, never to a newly normalized law. -/
theorem ratio_path_lower {q : ℕ → ℝ} {κ : ℝ} (hκ : 0≤κ) (l : ℕ)
    (hstep : ∀ k, k<l → κ*q k≤q (k+1)) : κ^l*q 0≤q l := by
  suffices h : ∀ k, k≤l → κ^k*q 0≤q k from h l le_rfl
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hh := mul_le_mul_of_nonneg_left (ih (by omega)) hκ
    calc
      κ^(k+1)*q 0 = κ*(κ^k*q 0) := by rw [pow_succ]; ring
      _ ≤ κ*q k := hh
      _ ≤ q (k+1) := hstep k (by omega)

/-- Actual specified-label comparison along a constructed cap-preserving path. -/
theorem profileWeight_path_lower {N J : ℕ} (hN : 2≤N) {β β₀ t Cg : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤ConditionalLawEstimates.occupationBound β₀)
    (hCg : 0≤Cg) (hg : ∀ z : Torus, -Cg≤regularGreenRepresentative z)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (m n : OccupationState J N t) :
    let κ := CellNormalizerBounds.kappaConstant β₀ Cg ConditionalLawEstimates.kernelConstant J
      (ConditionalLawEstimates.radius β₀)
    ∃ l≤N, 0<κ ∧ κ≤1 ∧ κ^l*qWeight (ConditionalLawEstimates.mesh_pos hmesh) β m ≤
      qWeight (ConditionalLawEstimates.mesh_pos hmesh) β n := by
  classical
  obtain ⟨l,γ,hl,h0,he,hcap,hstep⟩ := transfer_path_capped m.property n.property
  let κ := CellNormalizerBounds.kappaConstant β₀ Cg ConditionalLawEstimates.kernelConstant J
    (ConditionalLawEstimates.radius β₀)
  have hR := ConditionalLawEstimates.radius_one_le β₀
  have hk : 0<κ ∧ κ≤1 := by
    exact ⟨CellNormalizerBounds.kappaConstant_pos β₀ Cg ConditionalLawEstimates.kernelConstant
      (ConditionalLawEstimates.mesh_pos hmesh) (by omega),
      CellNormalizerBounds.kappaConstant_le_one (hβ.trans hβ₀) hCg
        ConditionalLawEstimates.kernelConstant_pos.le hR (by omega)⟩
  let q : ℕ → ℝ := fun k => (profileWeight (N:=N)
    (ConditionalLawEstimates.mesh_pos hmesh) (γ k) β).toReal
  have hs : ∀ k, k<l → κ*q k≤q (k+1) := by
    intro k hkl
    obtain ⟨a,b,ha,_,hmv⟩ := hstep k hkl
    have hr := arbitrary_profile_ratio hN hβ hβ₀ hsub ht htC hCg hg hmesh (γ k) a b ha
      (hcap k (by omega)) (by rw [hmv]; exact hcap (k+1) (by omega))
    have hp := qWeight_pos (ConditionalLawEstimates.mesh_pos hmesh) hN hβ
      (hβ₀.trans_lt hsub) (⟨γ k,hcap k (by omega)⟩ : OccupationState J N t)
    change 0<q k at hp
    change 0<κ ∧ κ≤1 ∧ κ≤(profileWeight (N:=N)
      (ConditionalLawEstimates.mesh_pos hmesh) (moveOccupation (γ k) a b) β).toReal/q k ∧ _ at hr
    have hh := (le_div_iff₀ hp).mp hr.2.2.1
    simpa only [hmv] using hh
  have hh := ratio_path_lower hk.1.le l hs
  refine ⟨l,hl,hk.1,hk.2,?_⟩
  simpa only [q,h0,he,qWeight] using hh


/-- The actual multinomial multiplicity is counted by the fibre of label vectors. -/
theorem multiplicity_upper {J N : ℕ} {t : ℝ} (m : OccupationState J N t) :
    multiplicity m≤(J^2)^N := by
  rw [← card_profile_fiber]
  exact FiniteFibreEntropyBound.fibre_card_le m

/-- Source global comparison for the original, unnormalized occupation masses. -/
theorem occupation_global_comparison {N J : ℕ} (hN : 2≤N) {β β₀ t Cg : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤ConditionalLawEstimates.occupationBound β₀)
    (hCg : 0≤Cg) (hg : ∀ z : Torus, -Cg≤regularGreenRepresentative z)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (m n : OccupationState J N t) :
    let κ := CellNormalizerBounds.kappaConstant β₀ Cg ConditionalLawEstimates.kernelConstant J
      (ConditionalLawEstimates.radius β₀)
    occupationWeight (ConditionalLawEstimates.mesh_pos hmesh) β m *
      (κ/(J:ℝ)^2)^N ≤ occupationWeight (ConditionalLawEstimates.mesh_pos hmesh) β n := by
  let hJ := ConditionalLawEstimates.mesh_pos hmesh
  let κ := CellNormalizerBounds.kappaConstant β₀ Cg ConditionalLawEstimates.kernelConstant J
    (ConditionalLawEstimates.radius β₀)
  obtain ⟨l,hl,hκ,hκ1,hq⟩ := profileWeight_path_lower hN hβ hβ₀ hsub ht htC hCg hg hmesh m n
  change κ^l*qWeight hJ β m≤qWeight hJ β n at hq
  have hp := qWeight_pos hJ hN hβ (hβ₀.trans_lt hsub) m
  have hp' := qWeight_pos hJ hN hβ (hβ₀.trans_lt hsub) n
  have hn : (1:ℝ)≤multiplicity n := by exact_mod_cast OccupationCentralRates.multiplicity_pos n
  have hm : (multiplicity m:ℝ)≤((J:ℝ)^2)^N := by exact_mod_cast multiplicity_upper m
  have hqN : κ^N*qWeight hJ β m≤qWeight hJ β n :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hκ.le hκ1 hl) hp.le).trans hq
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  change occupationWeight hJ β m*(κ/(J:ℝ)^2)^N≤occupationWeight hJ β n
  rw [occupationWeight_eq, occupationWeight_eq, div_pow]
  calc
    _ ≤ ((J:ℝ)^2)^N*qWeight hJ β m*(κ^N/((J:ℝ)^2)^N) := by gcongr
    _ = κ^N*qWeight hJ β m := by field_simp
    _ ≤ qWeight hJ β n := hqN
    _ ≤ (multiplicity n:ℝ)*qWeight hJ β n := by nlinarith only [hn,hp']

/-- The same literal comparison in exponential form, with a coefficient
independent of N and beta for fixed source parameters. -/
theorem occupation_global_exponential {N J : ℕ} (hN : 2≤N) {β β₀ t Cg : ℝ}
    (hβ : 0≤β) (hβ₀ : β≤β₀) (hsub : β₀<4)
    (ht : 0<t) (htC : t≤ConditionalLawEstimates.occupationBound β₀)
    (hCg : 0≤Cg) (hg : ∀ z : Torus, -Cg≤regularGreenRepresentative z)
    (hmesh : 8*(ConditionalLawEstimates.radius β₀+4)≤J)
    (m n : OccupationState J N t) :
    let κ := CellNormalizerBounds.kappaConstant β₀ Cg ConditionalLawEstimates.kernelConstant J
      (ConditionalLawEstimates.radius β₀)
    occupationWeight (ConditionalLawEstimates.mesh_pos hmesh) β m *
      Real.exp (-(-Real.log (κ/(J:ℝ)^2))*(N:ℝ)) ≤
        occupationWeight (ConditionalLawEstimates.mesh_pos hmesh) β n := by
  have hR := ConditionalLawEstimates.radius_one_le β₀
  have hJ := ConditionalLawEstimates.mesh_pos hmesh
  have hp := CellNormalizerBounds.kappaConstant_pos β₀ Cg ConditionalLawEstimates.kernelConstant
    hJ (show 0<ConditionalLawEstimates.radius β₀ by omega)
  have hJr : (0:ℝ)<J := by exact_mod_cast hJ
  dsimp only
  rw [neg_neg, mul_comm (Real.log _), Real.exp_nat_mul, Real.exp_log (by positivity)]
  exact occupation_global_comparison hN hβ hβ₀ hsub ht htC hCg hg hmesh m n


/-- Actual free integer coordinates, with no alternate occupation representation. -/
def stateCoordinates {J N : ℕ} {t : ℝ} (m : OccupationState J N t) :
    OccupationCoordinates.Interior J := (OccupationCoordinates.occupationInteriorEquiv J N t m).val

theorem stateCoordinates_injective {J N : ℕ} {t : ℝ} :
    Function.Injective (stateCoordinates (J:=J) (N:=N) (t:=t)) := by
  intro m n h
  apply (OccupationCoordinates.occupationInteriorEquiv J N t).injective
  exact Subtype.ext h

/-- Literal actual occupation weight in the free-coordinate chart, extended by
zero only outside the valid original state space. -/
def coordinateWeight {J N : ℕ} {t : ℝ} (hJ : 0<J) (β : ℝ)
    (y : OccupationCoordinates.Interior J) : ℝ := by
  classical
  exact if h : OccupationCoordinates.ValidCoordinates J N t (OccupationCoordinates.extend J N y)
    then occupationWeight hJ β ((OccupationCoordinates.occupationInteriorEquiv J N t).symm ⟨y,h⟩)
    else 0

theorem coordinateWeight_state {J N : ℕ} {t : ℝ} (hJ : 0<J) (β : ℝ)
    (m : OccupationState J N t) : coordinateWeight (N:=N) (t:=t) hJ β (stateCoordinates m)=
      occupationWeight hJ β m := by
  classical
  have hv := (OccupationCoordinates.occupationInteriorEquiv J N t m).property
  unfold coordinateWeight stateCoordinates
  rw [dite_eq_left hv]
  exact congrArg (occupationWeight hJ β) ((OccupationCoordinates.occupationInteriorEquiv J N t).symm_apply_apply m)

/-- The actual truncated squared sup-radius appearing in the source drift. -/
def truncatedRadius {J N : ℕ} {t : ℝ} (m₀ m : OccupationState J N t) : ℝ :=
  min ((DyadicShellPartition.radius N (stateCoordinates m₀) (stateCoordinates m))^2) (N:ℝ)

theorem truncatedRadius_nonneg {J N : ℕ} {t : ℝ} (m₀ m : OccupationState J N t) :
    0≤truncatedRadius m₀ m := le_min (sq_nonneg _) (Nat.cast_nonneg _)

theorem truncatedRadius_outside {J N : ℕ} {t M : ℝ} (hN : 0<N)
    (hM : 0≤M) (hMN : M^2≤N) (m₀ m : OccupationState J N t)
    (hm : m∉coordinateBall (stateCoordinates (N:=N) (t:=t)) (stateCoordinates m₀) (M*Real.sqrt N)) :
    M^2≤truncatedRadius m₀ m := by
  classical
  have hMr : M≤DyadicShellPartition.radius N (stateCoordinates m₀) (stateCoordinates m) := by
    by_contra hh
    apply hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro i
    exact (DyadicShellPartition.coordinate_le_radius hN (stateCoordinates m₀) (stateCoordinates m) i).trans
      (mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hh)) (Real.sqrt_nonneg _))
  apply le_min _ hMN
  have hr := DyadicShellPartition.radius_nonneg N (stateCoordinates m₀) (stateCoordinates m)
  nlinarith only [hMr,hM,hr]

/-- Explicit N-independent simplification of the cutoff/indicator moment. -/
theorem cutoff_moment_uniform {N : ℕ} (hN : 1≤N) {K g a b : ℝ}
    (hK : 0≤K) (hg : 0<g) (ha : 0<a) :
    (4*N*(72*K/((N:ℝ)^2*g^2))+b)/a≤(288*K/g^2+b)/a := by
  have hNr : (1:ℝ)≤N := by exact_mod_cast hN
  have hp : (0:ℝ)<N := by linarith
  have he : 4*N*(72*K/((N:ℝ)^2*g^2))=(288*K/g^2)/(N:ℝ) := by field_simp; ring
  rw [he]
  apply div_le_div_of_nonneg_right _ ha.le
  simpa only [add_comm] using add_le_add_right (div_le_self (by positivity : 0≤288*K/g^2) hNr) b

/-- Half the actual occupation mass lies in the literal lattice ball. The
moment, inner mass, and tail threshold are all derived; only the primitive
coercive drift and explicit scalar large-N gates remain as inputs. -/
theorem occupation_ball_mass {β₀ lo u t : ℝ}
    (hβ₀ : 0≤β₀) (hβ4 : β₀<4) (hlo : 0<lo) (hgap : lo<u) (hu : u<1)
    (htu : u≤t) {N J : ℕ}
    (hJ : HeavyScales.sourceResolution β₀ lo≤J)
    (hN : HeavyCoercivityConstants.particleThreshold β₀ lo≤N)
    {β : ℝ} (hβ : 0≤β) (hβle : β≤β₀)
    (m₀ : OccupationState J N t) {a b M : ℝ} (ha : 0<a) (hb : 0≤b)
    (hM : 0<M) (hMN : M^2≤N)
    (hbad : 72*HeavyCoercivityConstants.coercivityConstant β₀ lo /
      ((N:ℝ)^2*(u-lo)^2)≤1/4)
    (hMK : 4*((288*HeavyCoercivityConstants.coercivityConstant β₀ lo/(u-lo)^2+b)/a)≤M^2)
    (hdrift : ∀ m∈innerProfiles (J:=J) (N:=N) t u,
      a*truncatedRadius m₀ m-b≤occupationW (SeparatedRadius.source_mesh_pos hJ) β m) :
    (1/2:ℝ)≤∑ m∈coordinateBall (stateCoordinates (N:=N) (t:=t)) (stateCoordinates m₀) (M*Real.sqrt N),
      occupationWeight (SeparatedRadius.source_mesh_pos hJ) β m := by
  classical
  have hNt := OccupationMassCutoff.threshold_two hlo (hgap.trans hu) hN
  have hsub := hβle.trans_lt hβ4
  have hcut := OccupationMassCutoff.bad_label_mass_bound hβ₀ hβ4 hlo hgap hu hJ hN hβ hβle
  have hcomp := occupation_inner_mass_complement (t:=t) htu
    (SeparatedRadius.source_mesh_pos hJ) hNt hβ hsub
  have hmass : (3/4:ℝ)≤∑ m∈innerProfiles (J:=J) (N:=N) t u,
      occupationWeight (SeparatedRadius.source_mesh_pos hJ) β m := by
    linarith only [hcut,hbad,hcomp]
  have hmom := occupation_moment_from_cutoff hβ₀ hβ4 hlo hgap hu htu hJ hN hβ hβle
    (truncatedRadius m₀) ha hb hdrift
  have hK : 0≤HeavyCoercivityConstants.coercivityConstant β₀ lo :=
    (HeavyCoercivityConstants.coercivityConstant_pos hβ4 hlo).le
  have huni := cutoff_moment_uniform (show 1≤N by omega) hK (sub_pos.mpr hgap) ha (b:=b)
  exact central_mass_ge_half _ _ (innerProfiles t u) _
    (fun _ => ENNReal.toReal_nonneg) (fun m _ => truncatedRadius_nonneg m₀ m)
    hmass (sq_pos_of_pos hM) hMK (hmom.trans huni)
    (fun m _ hnot => truncatedRadius_outside (by omega) hM.le hMN m₀ m hnot)

/-- The source central point-mass lower bound, with original actual weights.
Quadratic coercivity and local logarithmic increments are the two deliberately
explicit occupation inputs still to be discharged by their separate units. -/
theorem occupation_center_lower {β₀ lo u t : ℝ}
    (hβ₀ : 0≤β₀) (hβ4 : β₀<4) (hlo : 0<lo) (hgap : lo<u) (hu : u<1)
    (htu : u≤t) {N J : ℕ}
    (hJ : HeavyScales.sourceResolution β₀ lo≤J)
    (hN : HeavyCoercivityConstants.particleThreshold β₀ lo≤N)
    {β : ℝ} (hβ : 0≤β) (hβle : β≤β₀)
    (m₀ : OccupationState J N t) {a b M C T : ℝ} (ha : 0<a) (hb : 0≤b)
    (hM : 0<M) (hMN : M^2≤N) (hC : 0≤C) (hMT : M*Real.sqrt N≤T)
    (hbad : 72*HeavyCoercivityConstants.coercivityConstant β₀ lo /
      ((N:ℝ)^2*(u-lo)^2)≤1/4)
    (hMK : 4*((288*HeavyCoercivityConstants.coercivityConstant β₀ lo/(u-lo)^2+b)/a)≤M^2)
    (hdrift : ∀ m∈innerProfiles (J:=J) (N:=N) t u,
      a*truncatedRadius m₀ m-b≤occupationW (SeparatedRadius.source_mesh_pos hJ) β m)
    (hinc : IntegerBoxMassGeometry.LogIncrementBound (stateCoordinates m₀) T N C
      (coordinateWeight (N:=N) (t:=t) (SeparatedRadius.source_mesh_pos hJ) β)) :
    (2*(2*M+1)^(J^2-1)*Real.exp (4*(J^2-1:ℕ)*C*(1+M^2)))⁻¹ *
      (N:ℝ)^(-((J^2-1:ℕ):ℝ)/2) ≤ occupationWeight (SeparatedRadius.source_mesh_pos hJ) β m₀ := by
  have hNt := OccupationMassCutoff.threshold_two hlo (hgap.trans hu) hN
  have hp := occupationWeight_pos (t:=t) (SeparatedRadius.source_mesh_pos hJ) hNt hβ (hβle.trans_lt hβ4)
  have hmass := occupation_ball_mass hβ₀ hβ4 hlo hgap hu htu hJ hN hβ hβle m₀ ha hb
    hM hMN hbad hMK hdrift
  have hh := center_mass_from_ball (show 1≤N by omega) (stateCoordinates (N:=N) (t:=t)) stateCoordinates_injective
    (stateCoordinates m₀) (coordinateWeight (N:=N) (t:=t) (SeparatedRadius.source_mesh_pos hJ) β)
    hM.le hC hMT (fun m => by rw [coordinateWeight_state]; exact hp m)
    (by rw [coordinateWeight_state]; exact hp m₀) hinc
    (by simpa only [coordinateWeight_state] using hmass)
  simpa only [coordinateWeight_state] using hh

end PeriodicAttractiveLogGas.OccupationAbsoluteMass
