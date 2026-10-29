import LeanResearch.PeriodicAttractiveLogGas.LabelExchangeability

/-! Exact factorial multiplicity of a specified occupation profile and
its probability under the actual Green ensemble. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.OccupationProbability

open MeshCells CellRestrictions LabelOccupations LabelExchangeability

def profileEquiv {J N : ℕ} (n : MeshIndex J → ℕ) (hn : ∑ a, n a = N) :
    (Σ a : MeshIndex J, Fin (n a)) ≃ Fin N :=
  Fintype.equivOfCardEq (by simpa using hn)

def labelOfProfile {J N : ℕ} (n : MeshIndex J → ℕ) (hn : ∑ a, n a = N) : LabelVector J N :=
  fun i ↦ ((profileEquiv n hn).symm i).1

theorem occupation_labelOfProfile {J N : ℕ} (n : MeshIndex J → ℕ) (hn : ∑ a, n a = N) :
    occupation (labelOfProfile n hn) = n := by
  classical
  funext a
  have h := Equiv.sum_comp (profileEquiv n hn)
    (fun i ↦ if labelOfProfile n hn i = a then (1 : ℕ) else 0)
  simp only [labelOfProfile, Equiv.symm_apply_apply] at h
  rw [Fintype.sum_sigma] at h
  have hleft : (∑ b : MeshIndex J, ∑ _k : Fin (n b), if b = a then (1 : ℕ) else 0) = n a := by
    simp
  rw [hleft] at h
  change (Finset.univ.filter fun i ↦ labelOfProfile n hn i = a).card = n a
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact h.symm

def sameOccupation {J N : ℕ} (η : LabelVector J N) : Finset (LabelVector J N) :=
  Finset.univ.filter fun ζ ↦ occupation ζ = occupation η

@[simp] theorem mem_sameOccupation {J N : ℕ} (η ζ : LabelVector J N) :
    ζ ∈ sameOccupation η ↔ occupation ζ = occupation η := by simp [sameOccupation]

def permutationFiberEquiv {J N : ℕ} (η ζ : LabelVector J N)
    (τ : Equiv.Perm (Fin N)) (hτ : η ∘ τ = ζ) :
    {σ : Equiv.Perm (Fin N) // η ∘ σ = ζ} ≃ {ρ : Equiv.Perm (Fin N) // η ∘ ρ = η} where
  toFun σ := ⟨τ.symm.trans σ.val, by
    funext i
    change η (σ.val (τ.symm i)) = η i
    calc
      _ = ζ (τ.symm i) := congrFun σ.property _
      _ = η i := by rw [← hτ]; simp⟩
  invFun ρ := ⟨τ.trans ρ.val, by
    funext i
    change η (ρ.val (τ i)) = ζ i
    exact (congrFun ρ.property (τ i)).trans (congrFun hτ i)⟩
  left_inv σ := by
    apply Subtype.ext
    ext i
    simp
  right_inv ρ := by
    apply Subtype.ext
    ext i
    simp

theorem card_sameOccupation_mul_factorials {J N : ℕ} (η : LabelVector J N) :
    (sameOccupation η).card * (∏ a : MeshIndex J, (occupation η a).factorial) = N.factorial := by
  classical
  let V := {ζ : LabelVector J N // occupation ζ = occupation η}
  let F : Equiv.Perm (Fin N) → V := fun σ ↦ ⟨η ∘ σ, occupation_permute σ η⟩
  have hc (ζ : V) : Fintype.card {σ : Equiv.Perm (Fin N) // F σ = ζ} =
      ∏ a : MeshIndex J, (occupation η a).factorial := by
    obtain ⟨τ, hτ⟩ := exists_permutation_of_occupation_eq ζ.property.symm
    let e : {σ : Equiv.Perm (Fin N) // F σ = ζ} ≃
        {σ : Equiv.Perm (Fin N) // η ∘ σ = ζ.val} :=
      Equiv.subtypeEquivRight fun σ ↦ Subtype.ext_iff
    rw [Fintype.card_congr (e.trans (permutationFiberEquiv η ζ.val τ hτ)),
      DomMulAct.stabilizer_card]
    apply Finset.prod_congr rfl
    intro a _
    congr 1
    simp [occupation, Fintype.card_subtype]
  have htotal := Fintype.card_congr (Equiv.sigmaFiberEquiv F)
  rw [Fintype.card_sigma] at htotal
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_perm, Fintype.card_fin] at htotal
  simpa only [V, Fintype.card_subtype, sameOccupation] using! htotal

theorem card_sameOccupation {J N : ℕ} (η : LabelVector J N) :
    (sameOccupation η).card = N.factorial / ∏ a : MeshIndex J, (occupation η a).factorial := by
  have hp : 0 < ∏ a : MeshIndex J, (occupation η a).factorial :=
    Finset.prod_pos fun a _ ↦ Nat.factorial_pos _
  exact Nat.eq_div_of_mul_eq_right hp.ne' (by
    simpa only [mul_comm] using card_sameOccupation_mul_factorials η)

def occupationEvent {J N : ℕ} (hJ : 0 < J) (n : MeshIndex J → ℕ) : Set (Configuration N) :=
  {X | occupation (configurationMeshLabel N J hJ X) = n}

theorem occupationEvent_eq_union {J N : ℕ} (hJ : 0 < J) (η : LabelVector J N) :
    occupationEvent hJ (occupation η) = ⋃ ζ ∈ sameOccupation η, labelFiber hJ ζ := by
  ext X
  simp only [occupationEvent, Set.mem_ofPred_eq, Set.mem_iUnion, mem_sameOccupation]
  constructor
  · intro h
    refine ⟨configurationMeshLabel N J hJ X, h, ?_⟩
    rw [labelFiber_eq_label_preimage]
    rfl
  · rintro ⟨ζ, hζ, hX⟩
    rw [labelFiber_eq_label_preimage] at hX
    change configurationMeshLabel N J hJ X = ζ at hX
    rwa [hX]

theorem occupationProbability_eq {J N : ℕ} (hJ : 0 < J) (η : LabelVector J N) (β : ℝ) :
    gibbsMeasure greenRealRepresentative N β (occupationEvent hJ (occupation η)) =
      ((N.factorial / ∏ a : MeshIndex J, (occupation η a).factorial : ℕ) : ℝ≥0∞) *
        labelProbability hJ η β := by
  rw [occupationEvent_eq_union, measure_biUnion_finset]
  · calc
      _ = ∑ ζ ∈ sameOccupation η, labelProbability hJ η β := by
        apply Finset.sum_congr rfl
        intro ζ hζ
        exact labelProbability_eq_of_occupation_eq hJ ((mem_sameOccupation η ζ).mp hζ) β
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, card_sameOccupation]
  · intro ζ _ ξ _ hne
    exact disjoint_labelFiber hJ hne
  · intro ζ _
    exact measurableSet_labelFiber hJ ζ

/-- Q(n) is the mass of one specified labeling. Invalid total profiles
are assigned zero; all source uses have total N. -/
def profileWeight {J N : ℕ} (hJ : 0 < J) (n : MeshIndex J → ℕ) (β : ℝ) : ℝ≥0∞ :=
  if hn : ∑ a, n a = N then labelProbability hJ (labelOfProfile n hn) β else 0

theorem labelProbability_eq_profileWeight {J N : ℕ} (hJ : 0 < J)
    (η : LabelVector J N) (β : ℝ) :
    labelProbability hJ η β = profileWeight (N := N) hJ (occupation η) β := by
  rw [profileWeight, dite_eq_left (sum_occupation η)]
  exact labelProbability_eq_of_occupation_eq hJ (occupation_labelOfProfile _ _).symm β

theorem occupationProbability_profile {J N : ℕ} (hJ : 0 < J) (n : MeshIndex J → ℕ)
    (hn : ∑ a, n a = N) (β : ℝ) :
    gibbsMeasure greenRealRepresentative N β (occupationEvent hJ n) =
      ((N.factorial / ∏ a : MeshIndex J, (n a).factorial : ℕ) : ℝ≥0∞) *
        profileWeight (N := N) hJ n β := by
  have h := occupationProbability_eq hJ (labelOfProfile n hn) β
  rw [occupation_labelOfProfile] at h
  simpa only [profileWeight, dite_eq_left hn] using h

end PeriodicAttractiveLogGas.OccupationProbability
