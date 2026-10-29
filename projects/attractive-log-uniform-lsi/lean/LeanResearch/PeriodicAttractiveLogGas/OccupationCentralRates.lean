import LeanResearch.PeriodicAttractiveLogGas.OccupationCoordinates
import LeanResearch.PeriodicAttractiveLogGas.LabelGroundState

/-! Actual central occupation rates and the factorial part of logarithmic
increments, source 2063–2104. The log-Q second-difference and functional
inequality inputs remain separate. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationCentralRates
open MeshCells MeshAdjacentCells LabelOccupations LabelRatioTransport
  DiscreteOccupationIdentities OccupationCoordinates ConditionalLawEstimates
  FibreProjection LabelGroundState

/-- Actual positive multiplicity, from the nonempty occupation fibre. -/
theorem multiplicity_pos {J N : ℕ} {t : ℝ} (m : OccupationState J N t) : 0 < multiplicity m := by
  rw [← card_profile_fiber]
  exact fibre_card_pos m

/-- Literal logarithmic factorial increment for a true occupation move. -/
theorem multiplicity_log_increment {J N : ℕ} {t : ℝ} {hJ : 0 < J} (hJ2 : 2 ≤ J)
    {m m' : OccupationState J N t} {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) :
    Real.log (multiplicity m' : ℝ) - Real.log (multiplicity m : ℝ) =
      Real.log (m.val a : ℝ) - Real.log ((m.val b : ℝ) + 1) := by
  have hp : (0 : ℝ) < multiplicity m := by exact_mod_cast multiplicity_pos m
  have hp' : (0 : ℝ) < multiplicity m' := by exact_mod_cast multiplicity_pos m'
  have ha : (0 : ℝ) < m.val a := by exact_mod_cast (show 0 < m.val a by have := h.2.1; omega)
  have hb : (0 : ℝ) < (m.val b : ℝ) + 1 := by positivity
  have hm : (multiplicity m : ℝ) * m.val a = (multiplicity m' : ℝ) * ((m.val b : ℝ) + 1) := by
    exact_mod_cast multiplicity_move hJ2 h
  have hl := congrArg Real.log hm
  rw [Real.log_mul hp.ne' ha.ne', Real.log_mul hp'.ne' hb.ne'] at hl
  linarith only [hl]

/-- The original physical occupation-event weight has precisely the source
count-ratio correction to the log-Q increment. -/
theorem occupation_log_increment {J N : ℕ} {t β : ℝ}
    (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ N) (hβ : 0 ≤ β) (hsub : β < 4)
    {m m' : OccupationState J N t} {a b : MeshIndex J} (h : PermittedMove hJ m m' a b) :
    Real.log (occupationWeight hJ β m') - Real.log (occupationWeight hJ β m) =
      Real.log ((m.val a : ℝ) / ((m.val b : ℝ) + 1)) +
        Real.log (qWeight hJ β m' / qWeight hJ β m) := by
  have hp : (0 : ℝ) < multiplicity m := by exact_mod_cast multiplicity_pos m
  have hp' : (0 : ℝ) < multiplicity m' := by exact_mod_cast multiplicity_pos m'
  have hq := qWeight_pos hJ hN hβ hsub m
  have hq' := qWeight_pos hJ hN hβ hsub m'
  have ha : (0 : ℝ) < m.val a := by exact_mod_cast (show 0 < m.val a by have := h.2.1; omega)
  have hb : (0 : ℝ) < (m.val b : ℝ) + 1 := by positivity
  rw [occupationWeight_eq, occupationWeight_eq, Real.log_mul hp'.ne' hq'.ne',
    Real.log_mul hp.ne' hq.ne', Real.log_div ha.ne' hb.ne', Real.log_div hq'.ne' hq.ne']
  have hh := multiplicity_log_increment hJ2 h
  linarith only [hh]

/-- The original adjacent label-ratio theorem bounds the actual mixing factor. -/
theorem occupation_mixing_lower {J N : ℕ} {t β β₀ : ℝ}
    (hN : 2 ≤ N) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    {m m' : OccupationState J N t} {a b : MeshIndex J}
    (h : PermittedMove (mesh_pos hmesh) m m' a b) :
    lowerBound β₀ / 2 ≤ qWeight (mesh_pos hmesh) β m' /
      (qWeight (mesh_pos hmesh) β m + qWeight (mesh_pos hmesh) β m') := by
  have hm' : moveOccupation m.val a b ∈ cappedOccupations J N t := by rw [h.2.2]; exact m'.property
  have hr := adjacent_profile_ratio hN hβ hβ₀ hsub ht htC hmesh m.val a b h.2.1 m.property hm' h.1
  change lowerBound β₀ ≤ 1 ∧ lowerBound β₀ / (2 - lowerBound β₀) ≤
      (OccupationProbability.profileWeight (N := N) (mesh_pos hmesh) (moveOccupation m.val a b) β).toReal /
      (OccupationProbability.profileWeight (N := N) (mesh_pos hmesh) m.val β).toReal ∧ _ at hr
  rw [h.2.2] at hr
  have hp := qWeight_pos (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) m
  have hq := qWeight_pos (mesh_pos hmesh) hN hβ (hβ₀.trans_lt hsub) m'
  have hc := lowerBound_pos β₀
  have hlo := (div_le_div_iff₀ (show 0 < 2 - lowerBound β₀ by linarith [hr.1]) hp).mp hr.2.1
  apply (le_div_iff₀ (add_pos hp hq)).mpr
  dsimp only [qWeight] at hp hq hlo ⊢
  nlinarith only [hlo]

/-- Uniform actual rate bound on every permitted central edge. -/
theorem central_rate_lower {J N : ℕ} {t β β₀ : ℝ}
    (hN : 2 ≤ N) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    {m m' : OccupationState J N t} {a b : MeshIndex J}
    (h : PermittedMove (mesh_pos hmesh) m m' a b)
    (hcount : (N : ℝ) / (2 * (J ^ 2 : ℕ)) ≤ (m.val a : ℝ)) :
    (lowerBound β₀ / (4 * (J ^ 2 : ℕ))) * N ≤ occupationRate (mesh_pos hmesh) β m m' := by
  have hc := lowerBound_pos β₀
  have hh := occupation_mixing_lower hN hβ hβ₀ hsub ht htC hmesh h
  rw [occupationRate_of_move (mesh_pos hmesh) (mesh_two_le hmesh) β h]
  calc
    _ = ((N : ℝ) / (2 * (J ^ 2 : ℕ))) * (lowerBound β₀ / 2) := by ring
    _ ≤ (m.val a : ℝ) * (lowerBound β₀ / 2) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ ≤ (m.val a : ℝ) * (qWeight (mesh_pos hmesh) β m' /
        (qWeight (mesh_pos hmesh) β m + qWeight (mesh_pos hmesh) β m')) :=
      mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Positive logarithms vary by at most inverse lower scale under a unit count change. -/
theorem log_sub_le_of_gap {x y κ : ℝ} (hκ : 0 < κ) (hx : κ ≤ x) (hy : κ ≤ y)
    (hgap : x - y ≤ 1) : Real.log x - Real.log y ≤ 1 / κ := by
  have hxp := hκ.trans_le hx
  have hyp := hκ.trans_le hy
  have hl := Real.log_le_sub_one_of_pos (div_pos hxp hyp)
  rw [Real.log_div hxp.ne' hyp.ne'] at hl
  have he : x / y - 1 = (x - y) / y := by field_simp
  rw [he] at hl
  exact hl.trans ((div_le_div_of_nonneg_right hgap hyp.le).trans (one_div_le_one_div_of_le hκ hy))

theorem abs_log_sub_le_of_unit {x y κ : ℝ} (hκ : 0 < κ) (hx : κ ≤ x) (hy : κ ≤ y)
    (hgap : |x - y| ≤ 1) : |Real.log x - Real.log y| ≤ 1 / κ := by
  have hu := log_sub_le_of_gap hκ hx hy (abs_le.mp hgap).2
  have hl := log_sub_le_of_gap hκ hy hx (show y - x ≤ 1 by linarith [(abs_le.mp hgap).1])
  exact abs_le.mpr ⟨by linarith only [hl], hu⟩

/-- Actual natural occupation moves change each count by at most one, including overlapping cells. -/
theorem move_count_change {J N : ℕ} {t : ℝ} {hJ : 0 < J}
    {m m' : OccupationState J N t} {a b : MeshIndex J}
    (h : PermittedMove hJ m m' a b) (c : MeshIndex J) :
    |(m'.val c : ℝ) - m.val c| ≤ 1 := by
  have he := move_cast m.val a b c h.2.1
  rw [h.2.2] at he
  have hi : |(m'.val c : ℤ) - m.val c| ≤ 1 := by
    rw [he, abs_le]
    split <;> split <;> constructor <;> omega
  exact_mod_cast hi

/-- Factorial mixed second difference on an actual two-move rectangle.
No distinctness across the two directions is imposed. Reverse and overlapping moves are included. -/
theorem factorial_mixed_difference {J N : ℕ} {t κ : ℝ} {hJ : 0 < J}
    (hJ2 : 2 ≤ J) (hκ : 0 < κ)
    {m ma mc mac : OccupationState J N t} {a b c d : MeshIndex J}
    (hab : PermittedMove hJ m ma a b) (hcd : PermittedMove hJ m mc c d)
    (hab' : PermittedMove hJ mc mac a b)
    (hm : ∀ e, κ ≤ (m.val e : ℝ)) (hmc : ∀ e, κ ≤ (mc.val e : ℝ)) :
    |Real.log (multiplicity mac : ℝ) - Real.log (multiplicity mc : ℝ) -
      Real.log (multiplicity ma : ℝ) + Real.log (multiplicity m : ℝ)| ≤ 2 / κ := by
  have h0 := multiplicity_log_increment hJ2 hab
  have h1 := multiplicity_log_increment hJ2 hab'
  have ha := abs_log_sub_le_of_unit hκ (hmc a) (hm a) (move_count_change hcd a)
  have hb := abs_log_sub_le_of_unit hκ
    (show κ ≤ (mc.val b : ℝ) + 1 by linarith [hmc b])
    (show κ ≤ (m.val b : ℝ) + 1 by linarith [hm b])
    (show |((mc.val b : ℝ) + 1) - ((m.val b : ℝ) + 1)| ≤ 1 by
      have he : ((mc.val b : ℝ) + 1) - ((m.val b : ℝ) + 1) = (mc.val b : ℝ) - m.val b := by ring
      rw [he]
      exact move_count_change hcd b)
  have he : Real.log (multiplicity mac : ℝ) - Real.log (multiplicity mc : ℝ) -
      Real.log (multiplicity ma : ℝ) + Real.log (multiplicity m : ℝ) =
      (Real.log (mc.val a : ℝ) - Real.log (m.val a : ℝ)) -
        (Real.log ((mc.val b : ℝ) + 1) - Real.log ((m.val b : ℝ) + 1)) := by
    linarith only [h0, h1]
  rw [he]
  calc
    _ ≤ |Real.log (mc.val a : ℝ) - Real.log (m.val a : ℝ)| +
        |Real.log ((mc.val b : ℝ) + 1) - Real.log ((m.val b : ℝ) + 1)| := abs_sub _ _
    _ ≤ 1 / κ + 1 / κ := add_le_add ha hb
    _ = 2 / κ := by ring

/-- The actual central-coordinate cube supplies the count lower bound. -/
theorem central_counts {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hN : 8 * J ^ 2 ≤ N)
    (ht : 1 / (J ^ 2 : ℕ) < t / 8) (m : OccupationState J N t)
    (hm : ∀ i, |((interior (cumulative m.val) i - interior (cumulative (rounded J N)) i : ℤ) : ℝ)| ≤
      2 * centralEpsilon J * N) :
    ∀ a, (N : ℝ) / (2 * (J ^ 2 : ℕ)) ≤ (m.val a : ℝ) := by
  have hh := (central_box hJ hN ht (interior (cumulative m.val)) hm).2
  rw [extend_interior _ (cumulative_zero _) (cumulative_total _ m.property.1), recover_cumulative] at hh
  exact hh

/-- Source-facing coordinate-neighbor lower rates, in both directions, on the actual central cube. -/
theorem central_coordinate_rates {J N : ℕ} {t β β₀ : ℝ}
    (hN : 2 ≤ N) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) (hlarge : 8 * J ^ 2 ≤ N)
    (hsmall : 1 / (J ^ 2 : ℕ) < t / 8)
    (m m' : OccupationState J N t) (i : Fin (J ^ 2 - 1))
    (hm : ∀ k, |((interior (cumulative m.val) k - interior (cumulative (rounded J N)) k : ℤ) : ℝ)| ≤
      2 * centralEpsilon J * N)
    (hm' : ∀ k, |((interior (cumulative m'.val) k - interior (cumulative (rounded J N)) k : ℤ) : ℝ)| ≤
      2 * centralEpsilon J * N)
    (he : interior (cumulative m'.val) = fun l => interior (cumulative m.val) l - if l = i then 1 else 0) :
    (lowerBound β₀ / (4 * (J ^ 2 : ℕ))) * N ≤ occupationRate (mesh_pos hmesh) β m m' ∧
    (lowerBound β₀ / (4 * (J ^ 2 : ℕ))) * N ≤ occupationRate (mesh_pos hmesh) β m' m := by
  have hp := interior_neighbor_is_permitted (mesh_pos hmesh) m m' i he
  exact ⟨central_rate_lower hN hβ hβ₀ hsub ht htC hmesh hp
      (central_counts (mesh_pos hmesh) hlarge hsmall m hm _),
    central_rate_lower hN hβ hβ₀ hsub ht htC hmesh (hp.reverse (mesh_two_le hmesh))
      (central_counts (mesh_pos hmesh) hlarge hsmall m' hm' _)⟩

/-- The safe factorial mixed-difference constant is uniform in beta and N. -/
theorem central_factorial_mixed_difference {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (hN : 2 ≤ N) (hlarge : 8 * J ^ 2 ≤ N) (hsmall : 1 / (J ^ 2 : ℕ) < t / 8)
    {m ma mc mac : OccupationState J N t} {a b c d : MeshIndex J}
    (hab : PermittedMove hJ m ma a b) (hcd : PermittedMove hJ m mc c d)
    (hab' : PermittedMove hJ mc mac a b)
    (hm : ∀ i, |((interior (cumulative m.val) i - interior (cumulative (rounded J N)) i : ℤ) : ℝ)| ≤
      2 * centralEpsilon J * N)
    (hmc : ∀ i, |((interior (cumulative mc.val) i - interior (cumulative (rounded J N)) i : ℤ) : ℝ)| ≤
      2 * centralEpsilon J * N) :
    |Real.log (multiplicity mac : ℝ) - Real.log (multiplicity mc : ℝ) -
      Real.log (multiplicity ma : ℝ) + Real.log (multiplicity m : ℝ)| ≤ 4 * (J ^ 2 : ℕ) / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hJr : (0 : ℝ) < (J ^ 2 : ℕ) := by exact_mod_cast pow_pos hJ 2
  have hh := factorial_mixed_difference hJ2 (div_pos hNr (by positivity)) hab hcd hab'
    (central_counts hJ hlarge hsmall m hm) (central_counts hJ hlarge hsmall mc hmc)
  have he : 2 / ((N : ℝ) / (2 * (J ^ 2 : ℕ))) = 4 * (J ^ 2 : ℕ) / N := by
    field_simp
    norm_num
  rwa [he] at hh

end PeriodicAttractiveLogGas.OccupationCentralRates
