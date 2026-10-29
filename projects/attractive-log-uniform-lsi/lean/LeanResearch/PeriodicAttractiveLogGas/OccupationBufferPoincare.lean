import LeanResearch.PeriodicAttractiveLogGas.OccupationAbsoluteMass
import LeanResearch.PeriodicAttractiveLogGas.FiniteBoxPoincare

/-! Source2100–2120: the actual occupation cutoff and the buffered
Poincare argument on the original outer graph. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.OccupationBufferPoincare
open FiniteGraph FiniteEntropyLocalization DyadicShellPartition
open MeshCells LabelOccupations DiscreteOccupationIdentities OccupationProbability LabelGroundState
open OccupationAbsoluteMass

/-- The full outgoing squared difference, with no boundary-edge suppression. -/
def cutoffCost {α : Type*} [Fintype α] (r : α → α → ℝ) (ζ : α → ℝ) (x : α) : ℝ :=
  ∑ y, r x y * (ζ y - ζ x)^2

theorem energy_sub_const {α : Type*} [Fintype α]
    (w : α → ℝ) (r : α → α → ℝ) (F : α → ℝ) (c : ℝ) :
    energy w r (fun x => F x - c) = energy w r F := by
  simp only [energy, sub_sub_sub_cancel_right]

/-- The error is exactly the full outgoing cutoff cost at the starting endpoint. -/
theorem energy_product_le {α : Type*} [Fintype α]
    (w : α → ℝ) (r : α → α → ℝ) (ζ F : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hr : ∀ x y, 0 ≤ r x y)
    (hζ : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1) :
    energy w r (fun x => ζ x * F x) ≤
      2 * energy w r F + ∑ x, w x * F x^2 * cutoffCost r ζ x := by
  have hp (x y : α) : (ζ y * F y - ζ x * F x)^2 ≤
      2*(F y-F x)^2 + 2*F x^2*(ζ y-ζ x)^2 := by
    have hz : (ζ y)^2 ≤ 1 := by nlinarith [(hζ y).1, (hζ y).2]
    have hm := mul_nonneg (sub_nonneg.mpr hz) (sq_nonneg (F y-F x))
    nlinarith [sq_nonneg (ζ y*(F y-F x)-F x*(ζ y-ζ x))]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun x _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun y _ =>
      mul_le_mul_of_nonneg_left (hp x y) (mul_nonneg (hw x) (hr x y))))
  have he : (∑ x, ∑ y, w x*r x y*(2*(F y-F x)^2+2*F x^2*(ζ y-ζ x)^2)) =
      2*(∑ x, ∑ y, w x*r x y*(F y-F x)^2) +
      2*(∑ x, w x*F x^2*cutoffCost r ζ x) := by
    simp only [cutoffCost, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro x _ <;>
      apply Finset.sum_congr rfl <;> intro y _ <;> ring
  rw [he] at hh
  unfold energy
  linarith

/-- The literal maximum occupation count. -/
def maxCount {J N : ℕ} {t : ℝ} (m : OccupationState J N t) : ℕ :=
  Finset.univ.sup m.val

theorem count_le_max {J N : ℕ} {t : ℝ} (m : OccupationState J N t) (a : MeshIndex J) :
    m.val a ≤ maxCount m := Finset.le_sup (Finset.mem_univ a)

theorem cast_sup_le {α : Type*} (s : Finset α) (f : α → ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ a ∈ s, (f a : ℝ) ≤ B) : ((s.sup f : ℕ) : ℝ) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hB
  | @insert a s ha ih =>
    rw [Finset.sup_insert, Nat.cast_max]
    exact max_le (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem maxCount_le_of_cap {J N : ℕ} {t u : ℝ} (m : OccupationState J N t)
    (hu : 0 ≤ u) (hm : m.val ∈ cappedOccupations J N u) :
    (maxCount m : ℝ) ≤ u*N :=
  cast_sup_le _ _ (mul_nonneg hu (Nat.cast_nonneg _)) (fun a _ => hm.2 a)

theorem maxCount_move {J N : ℕ} {t : ℝ} {hJ : 0 < J}
    {m m' : OccupationState J N t} {a b : MeshIndex J}
    (h : PermittedMove hJ m m' a b) : |(maxCount m' : ℝ) - maxCount m| ≤ 1 := by
  have hu : maxCount m' ≤ maxCount m + 1 := by
    apply Finset.sup_le
    intro c _
    have hh := (abs_le.mp (OccupationCentralRates.move_count_change h c)).2
    have hc := count_le_max m c
    have hc' : m'.val c ≤ m.val c + 1 := by exact_mod_cast (show (m'.val c : ℝ) ≤ m.val c + 1 by linarith)
    omega
  have hl : maxCount m ≤ maxCount m' + 1 := by
    apply Finset.sup_le
    intro c _
    have hh := (abs_le.mp (OccupationCentralRates.move_count_change h c)).1
    have hc := count_le_max m' c
    have hc' : m.val c ≤ m'.val c + 1 := by exact_mod_cast (show (m.val c : ℝ) ≤ m'.val c + 1 by linarith)
    omega
  have hu' : (maxCount m' : ℝ) ≤ maxCount m + 1 := by exact_mod_cast hu
  have hl' : (maxCount m : ℝ) ≤ maxCount m' + 1 := by exact_mod_cast hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Affine between 5t/8 and 3t/4; equal to one and zero beyond the endpoints. -/
def cutoff {J N : ℕ} {t : ℝ} (m : OccupationState J N t) : ℝ :=
  ramp ((3*t/4 - (maxCount m : ℝ)/N)/(t/8))

theorem cutoff_bounds {J N : ℕ} {t : ℝ} (m : OccupationState J N t) :
    0 ≤ cutoff m ∧ cutoff m ≤ 1 := ⟨ramp_nonneg _, ramp_le_one _⟩

theorem cutoff_one {J N : ℕ} {t : ℝ} (ht : 0 < t) (hN : 0 < N)
    (m : OccupationState J N t) (hm : m.val ∈ cappedOccupations J N (5*t/8)) :
    cutoff m = 1 := by
  apply ramp_eq_one
  have hh := maxCount_le_of_cap m (by positivity : 0 ≤ 5*t/8) hm
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  apply (le_div_iff₀ (by positivity : 0 < t/8)).mpr
  have hh' : (maxCount m : ℝ)/N ≤ 5*t/8 := (div_le_iff₀ hn).mpr hh
  linarith

theorem cutoff_zero {J N : ℕ} {t : ℝ} (ht : 0 < t) (hN : 0 < N)
    (m : OccupationState J N t) (hm : m.val ∉ cappedOccupations J N (3*t/4)) :
    cutoff m = 0 := by
  apply ramp_eq_zero
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hbad : ¬ ∀ a, (m.val a : ℝ) ≤ (3*t/4)*N := fun hh => hm ⟨m.property.1, hh⟩
  push Not at hbad
  obtain ⟨a,ha⟩ := hbad
  have hc : (m.val a : ℝ) ≤ maxCount m := Nat.cast_le.mpr (count_le_max m a)
  have hx : 3*t/4 ≤ (maxCount m : ℝ)/N := (le_div_iff₀ hn).mpr (by linarith)
  linarith


/-- The slope is 8/t; the occupation fraction changes by at most 1/N. -/
theorem cutoff_move {J N : ℕ} {t : ℝ} {hJ : 0 < J}
    (ht : 0 < t) (hN : 0 < N) {m m' : OccupationState J N t} {a b : MeshIndex J}
    (h : PermittedMove hJ m m' a b) : |cutoff m' - cutoff m| ≤ 8/(t*N) := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have he : (3*t/4-(maxCount m' : ℝ)/N)/(t/8) -
      (3*t/4-(maxCount m : ℝ)/N)/(t/8) =
      -((maxCount m' : ℝ)-maxCount m) * (8/(t*N)) := by field_simp; ring
  have hh := ramp_change ((3*t/4-(maxCount m' : ℝ)/N)/(t/8))
    ((3*t/4-(maxCount m : ℝ)/N)/(t/8))
  rw [he, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 8/(t*N))] at hh
  exact hh.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (maxCount_move h) (by positivity : 0 ≤ 8/(t*(N:ℝ))))

/-- Every boundary-crossing edge is included in the outgoing cost estimate. -/
theorem cutoff_cost_bound {J N : ℕ} {t : ℝ} (hJ : 0 < J) (hJ3 : 3 ≤ J)
    (ht : 0 < t) (hN : 0 < N) (β : ℝ) (m : OccupationState J N t) :
    cutoffCost (occupationRate hJ β) cutoff m ≤ 256/t^2/N := by
  classical
  have hp (m' : OccupationState J N t) :
      occupationRate hJ β m m' * (cutoff m'-cutoff m)^2 ≤
      occupationRate hJ β m m' * (8/(t*N))^2 := by
    by_cases he : ∃ a b, PermittedMove hJ m m' a b
    · obtain ⟨a,b,hab⟩ := he
      apply mul_le_mul_of_nonneg_left _ (occupationRate_nonneg hJ β m m')
      have hh := cutoff_move ht hN hab
      nlinarith [sq_abs (cutoff m'-cutoff m), abs_nonneg (cutoff m'-cutoff m)]
    · simp only [occupationRate_eq_zero hJ β he, zero_mul]
      exact le_rfl
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun m' _ => hp m')
  rw [← Finset.sum_mul] at hh
  have ho := mul_le_mul_of_nonneg_right (occupation_outgoing_le hJ hJ3 β m)
    (sq_nonneg (8/(t*N)))
  have he : 4*(N:ℝ)*(8/(t*N))^2 = 256/t^2/N := by
    field_simp
    ring
  exact hh.trans (he ▸ ho)

/-- On the smaller cap both endpoints of every permitted move lie below 5t/8. -/
theorem cutoff_cost_zero_inner {J N : ℕ} {t : ℝ} (hJ : 0 < J)
    (ht : 0 < t) (hN : 0 < N) (hgap : 8 ≤ t*N)
    (β : ℝ) (m : OccupationState J N t)
    (hm : m.val ∈ cappedOccupations J N (t/2)) :
    cutoffCost (occupationRate hJ β) cutoff m = 0 := by
  classical
  have hself : cutoff m = 1 := cutoff_one ht hN m
    ⟨m.property.1, fun a => (hm.2 a).trans (by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])⟩
  apply Finset.sum_eq_zero
  intro m' _
  by_cases he : ∃ a b, PermittedMove hJ m m' a b
  · obtain ⟨a,b,hab⟩ := he
    have hnext : cutoff m' = 1 := cutoff_one ht hN m' ⟨m'.property.1, by
      intro c
      have hh := (abs_le.mp (OccupationCentralRates.move_count_change hab c)).2
      have hc := hm.2 c
      nlinarith⟩
    simp only [hself, hnext, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
  · simp only [occupationRate_eq_zero hJ β he, zero_mul]


/-- Finite ground-state/product assembly. The only local functional input is
an internal-box Poincare estimate, with the same fixed center c. -/
theorem buffer_from_local {α : Type*} [Fintype α] [DecidableEq α]
    (w : α → ℝ) (r : α → α → ℝ) (W ζ F : α → ℝ)
    (B C S : Finset α) (c b K g : ℝ)
    (hw : ∀ x, 0 ≤ w x) (hr : ∀ x y, 0 ≤ r x y)
    (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hζ : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (hζC : ∀ x ∈ C, ζ x = 1) (hζS : ∀ x ∉ S, ζ x = 0)
    (hW : ∀ x ∈ S, -b ≤ W x)
    (hWB : ∀ x ∈ S, x ∉ B → 1 ≤ W x)
    (hcost : ∀ x, cutoffCost r ζ x ≤ if x ∈ C then 0 else g)
    (hground : (∑ x, w x*(ζ x*(F x-c))^2*W x) ≤
      energy w r (fun x => ζ x*(F x-c)))
    (hlocal : (∑ x ∈ B, w x*(F x-c)^2) ≤
      K*energy (restrictedWeight w B) (restrictedRates r B) F) :
    (∑ x, w x*(F x-c)^2) ≤ (2+(b+1)*K)*energy w r F +
      (1+g)*(∑ x, if x ∈ C then 0 else w x*(F x-c)^2) := by
  have hnorm (x : α) : w x*(F x-c)^2 ≤ w x*(ζ x*(F x-c))^2 +
      (if x ∈ C then 0 else w x*(F x-c)^2) := by
    by_cases hx : x ∈ C
    · simp only [hx, ite_true, hζC x hx, one_mul, add_zero, le_refl]
    · simp only [hx, ite_false]
      nlinarith [mul_nonneg (hw x) (sq_nonneg (ζ x*(F x-c)))]
  have hpoint (x : α) : w x*(ζ x*(F x-c))^2 ≤
      w x*(ζ x*(F x-c))^2*W x +
      (b+1)*(if x ∈ B then w x*(F x-c)^2 else 0) := by
    have hz : (ζ x)^2 ≤ 1 := by nlinarith [(hζ x).1, (hζ x).2]
    have hsq : (ζ x*(F x-c))^2 ≤ (F x-c)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hz) (sq_nonneg (F x-c))]
    by_cases hxS : x ∈ S
    · by_cases hxB : x ∈ B
      · simp only [hxB, ite_true]
        have h1 := mul_nonneg (hw x) (sq_nonneg (ζ x*(F x-c)))
        have h2 := mul_nonneg h1 (show 0 ≤ W x+b by linarith [hW x hxS])
        have h3 := mul_nonneg (show 0 ≤ b+1 by linarith)
          (mul_nonneg (hw x) (sub_nonneg.mpr hsq))
        nlinarith
      · simp only [hxB, ite_false, mul_zero, add_zero]
        exact le_mul_of_one_le_right (mul_nonneg (hw x) (sq_nonneg _)) (hWB x hxS hxB)
    · rw [hζS x hxS]
      simp only [zero_mul, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add]
      split_ifs
      · exact mul_nonneg (by linarith) (mul_nonneg (hw x) (sq_nonneg _))
      · simp
  have hcostsum : (∑ x, w x*(F x-c)^2*cutoffCost r ζ x) ≤
      g*(∑ x, if x ∈ C then 0 else w x*(F x-c)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have hh := mul_le_mul_of_nonneg_left (hcost x) (mul_nonneg (hw x) (sq_nonneg (F x-c)))
    by_cases hx : x ∈ C <;> simpa only [hx, ite_true, ite_false, mul_zero, mul_comm] using hh
  have hn := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hnorm x)
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hpoint x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hn hp
  have heB : (∑ x, if x ∈ B then w x*(F x-c)^2 else 0) = ∑ x ∈ B, w x*(F x-c)^2 := by
    rw [← Finset.sum_filter]
    simp
  rw [heB] at hp
  have hprod := energy_product_le w r ζ (fun x => F x-c) hw hr hζ
  rw [energy_sub_const] at hprod
  have hl := hlocal.trans (mul_le_mul_of_nonneg_left (restricted_energy_le w r F hw hr B) hK)
  have hbl := mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ b+1)
  nlinarith


/-- A sufficient particle threshold depending only on the fixed positive cap. -/
def bufferThreshold (t : ℝ) : ℕ := max ⌈8/t⌉₊ ⌈256/t^2⌉₊

theorem bufferThreshold_gates {t : ℝ} (ht : 0 < t) {N : ℕ}
    (hN : bufferThreshold t ≤ N) : 8 ≤ t*N ∧ 256 ≤ t^2*N := by
  have h1 : ⌈8/t⌉₊ ≤ N := (le_max_left _ _).trans hN
  have h2 : ⌈256/t^2⌉₊ ≤ N := (le_max_right _ _).trans hN
  have hh1 := (Nat.le_ceil (8/t)).trans (Nat.cast_le.mpr h1 : (⌈8/t⌉₊ : ℝ) ≤ N)
  have hh2 := (Nat.le_ceil (256/t^2)).trans (Nat.cast_le.mpr h2 : (⌈256/t^2⌉₊ : ℝ) ≤ N)
  constructor
  · have hh := (div_le_iff₀ ht).mp hh1
    nlinarith
  · have hh := (div_le_iff₀ (sq_pos_of_pos ht)).mp hh2
    nlinarith

local instance {J N : ℕ} {t u : ℝ} :
    DecidablePred (fun m : OccupationState J N t => m.val ∈ cappedOccupations J N u) :=
  fun _ => Classical.propDecidable _

/-- The source buffer estimate for the actual original occupation graph.
The central PI and the two genuine W bounds remain explicit upstream inputs;
all cutoff, transition, ground-state and absorption facts are proved here. -/
theorem occupation_buffer_poincare {J N : ℕ} {t β : ℝ}
    (hJ : 0 < J) (hJ3 : 3 ≤ J) (hN : 2 ≤ N)
    (hβ : 0 ≤ β) (hsub : β < 4) (ht : 0 < t)
    (hlarge : bufferThreshold t ≤ N)
    (B : Finset (OccupationState J N t)) (F : OccupationState J N t → ℝ)
    {b K : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K)
    (hW : ∀ m : OccupationState J N t,
      m.val ∈ cappedOccupations J N (3*t/4) → -b ≤ occupationW hJ β m)
    (hWB : ∀ m : OccupationState J N t,
      m.val ∈ cappedOccupations J N (3*t/4) → m ∉ B → 1 ≤ occupationW hJ β m)
    (hlocal : let c := FiniteBoxPoincare.mean (conditionalWeight (occupationWeight hJ β) B) F
      (∑ m ∈ B, occupationWeight hJ β m*(F m-c)^2) ≤
        K*energy (restrictedWeight (occupationWeight hJ β) B)
          (restrictedRates (occupationRate hJ β) B) F) :
    let c := FiniteBoxPoincare.mean (conditionalWeight (occupationWeight hJ β) B) F
    (∑ m, occupationWeight hJ β m*(F m-c)^2) ≤
      (2+(b+1)*K)*occupationEnergy hJ β F +
        2*(∑ m, if m.val ∈ cappedOccupations J N (t/2) then 0
          else occupationWeight hJ β m*(F m-c)^2) := by
  classical
  let c := FiniteBoxPoincare.mean (conditionalWeight (occupationWeight hJ β) B) F
  let C := innerProfiles (J := J) (N := N) t (t/2)
  let S := innerProfiles (J := J) (N := N) t (3*t/4)
  have hC (m : OccupationState J N t) : m ∈ C ↔ m.val ∈ cappedOccupations J N (t/2) := by
    simp [C, innerProfiles]
  have hS (m : OccupationState J N t) : m ∈ S ↔ m.val ∈ cappedOccupations J N (3*t/4) := by
    simp [S, innerProfiles]
  have hgates := bufferThreshold_gates ht hlarge
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcost (m : OccupationState J N t) :
      cutoffCost (occupationRate hJ β) cutoff m ≤ if m ∈ C then 0 else 256/t^2/N := by
    by_cases hm : m ∈ C
    · simp only [hm, ite_true]
      rw [cutoff_cost_zero_inner hJ ht (by omega) hgates.1 β m ((hC m).mp hm)]
    · simp only [hm, ite_false]
      exact cutoff_cost_bound hJ hJ3 ht (by omega) β m
  have hh := buffer_from_local (occupationWeight hJ β) (occupationRate hJ β)
    (occupationW hJ β) cutoff F B C S c b K (256/t^2/N)
    (fun m => (occupationWeight_pos hJ hN hβ hsub m).le)
    (occupationRate_nonneg hJ β) hb hK
    cutoff_bounds (fun m hm => cutoff_one ht (by omega) m
      ⟨m.property.1, fun a => (((hC m).mp hm).2 a).trans (by nlinarith [hn])⟩)
    (fun m hm => cutoff_zero ht (by omega) m (fun h => hm ((hS m).mpr h)))
    (fun m hm => hW m ((hS m).mp hm)) (fun m hm hB => hWB m ((hS m).mp hm) hB)
    hcost (occupation_ground_state_coercivity hJ (by omega) hN hβ hsub
      (fun m => cutoff m*(F m-c))) hlocal
  have hg : 256/t^2/N ≤ 1 := by
    apply (div_le_iff₀ hn).mpr
    simp only [one_mul]
    apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
    nlinarith [hgates.2]
  have hout : 0 ≤ ∑ m, if m ∈ C then 0 else occupationWeight hJ β m*(F m-c)^2 := by
    apply Finset.sum_nonneg
    intro m _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (occupationWeight_pos hJ hN hβ hsub m).le (sq_nonneg _)
  have hfinal := hh.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right (show 1+256/t^2/N ≤ 2 by linarith) hout))
  simpa only [hC, c, occupationEnergy] using! hfinal

end PeriodicAttractiveLogGas.OccupationBufferPoincare
