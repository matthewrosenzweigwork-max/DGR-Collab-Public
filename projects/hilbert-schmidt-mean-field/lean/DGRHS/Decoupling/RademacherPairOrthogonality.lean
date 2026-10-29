import DGRHS.Decoupling.RademacherSupportProduct

noncomputable section
open MeasureTheory ProbabilityTheory

namespace DGRHS.Decoupling

/-- Walsh character indexed by a finite coordinate support. -/
def rademacherCharacter {n : ℕ} (s : Finset (Fin n)) (ω : Fin n → Bool) : ℝ :=
  ∏ i ∈ s, rademacherSign (ω i)

/-- Finite symmetric difference, represented by the disjoint union of the two set differences. -/
def rademacherSupportSymmDiff {α : Type*} [DecidableEq α]
    (s t : Finset α) : Finset α := (s \ t) ∪ (t \ s)

/-- Multiplying two cube characters cancels the common coordinates. -/
lemma rademacherCharacter_mul_symmDiff {n : ℕ}
    (s t : Finset (Fin n)) (ω : Fin n → Bool) :
    rademacherCharacter s ω * rademacherCharacter t ω =
      rademacherCharacter (rademacherSupportSymmDiff s t) ω := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty => simp [rademacherCharacter, rademacherSupportSymmDiff]
  | @insert a s ha ih =>
    by_cases hat : a ∈ t
    · have hsymm : rademacherSupportSymmDiff (insert a s) t = rademacherSupportSymmDiff s (t.erase a) := by
        ext x
        by_cases hxa : x = a
        · subst x
          simp [rademacherSupportSymmDiff, Finset.mem_sdiff, ha, hat]
        · simp [rademacherSupportSymmDiff, Finset.mem_sdiff, hxa, ha, hat]
      have hIH := ih (t.erase a)
      change (∏ i ∈ s, rademacherSign (ω i)) *
          (∏ i ∈ t.erase a, rademacherSign (ω i)) =
        ∏ i ∈ rademacherSupportSymmDiff s (t.erase a), rademacherSign (ω i) at hIH
      change (∏ i ∈ insert a s, rademacherSign (ω i)) *
          (∏ i ∈ t, rademacherSign (ω i)) =
        ∏ i ∈ rademacherSupportSymmDiff (insert a s) t, rademacherSign (ω i)
      rw [Finset.prod_insert ha,
        ← Finset.prod_erase_mul t (fun i ↦ rademacherSign (ω i)) hat, hsymm]
      calc
        _ = (rademacherSign (ω a) * rademacherSign (ω a)) *
            ((∏ i ∈ s, rademacherSign (ω i)) *
              (∏ i ∈ t.erase a, rademacherSign (ω i))) := by ring
        _ = (∏ i ∈ s, rademacherSign (ω i)) *
            (∏ i ∈ t.erase a, rademacherSign (ω i)) := by
              rw [← pow_two, rademacherSign_sq, one_mul]
        _ = ∏ i ∈ rademacherSupportSymmDiff s (t.erase a), rademacherSign (ω i) := hIH
    · have hsymm : rademacherSupportSymmDiff (insert a s) t = insert a (rademacherSupportSymmDiff s t) := by
        ext x
        by_cases hxa : x = a
        · subst x
          simp [rademacherSupportSymmDiff, Finset.mem_sdiff, ha, hat]
        · simp [rademacherSupportSymmDiff, Finset.mem_sdiff, hxa, ha, hat]
      have hIH := ih t
      change (∏ i ∈ s, rademacherSign (ω i)) *
          (∏ i ∈ t, rademacherSign (ω i)) =
        ∏ i ∈ rademacherSupportSymmDiff s t, rademacherSign (ω i) at hIH
      change (∏ i ∈ insert a s, rademacherSign (ω i)) *
          (∏ i ∈ t, rademacherSign (ω i)) =
        ∏ i ∈ rademacherSupportSymmDiff (insert a s) t, rademacherSign (ω i)
      have hnot : a ∉ rademacherSupportSymmDiff s t := by
        simp [rademacherSupportSymmDiff, Finset.mem_sdiff, ha, hat]
      rw [Finset.prod_insert ha, hsymm, Finset.prod_insert hnot]
      calc
        _ = rademacherSign (ω a) *
            ((∏ i ∈ s, rademacherSign (ω i)) *
              (∏ i ∈ t, rademacherSign (ω i))) := by ring
        _ = rademacherSign (ω a) *
            (∏ i ∈ rademacherSupportSymmDiff s t, rademacherSign (ω i)) := by rw [hIH]

/-- Increasing coordinate pairs provide canonical supports for degree-two characters. -/
def RademacherIndexPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

def rademacherPairSupport {n : ℕ} (p : RademacherIndexPair n) : Finset (Fin n) :=
  {p.1.1, p.1.2}

def rademacherPairCharacter {n : ℕ} (p : RademacherIndexPair n)
    (ω : Fin n → Bool) : ℝ :=
  rademacherSign (ω p.1.1) * rademacherSign (ω p.1.2)

lemma rademacherPairCharacter_eq_character {n : ℕ}
    (p : RademacherIndexPair n) (ω : Fin n → Bool) :
    rademacherPairCharacter p ω = rademacherCharacter (rademacherPairSupport p) ω := by
  simp [rademacherPairCharacter, rademacherPairSupport, rademacherCharacter,
    Finset.prod_insert, ne_of_lt p.2]

/-- Distinct pair supports are orthogonal under the selector product law. -/
lemma integral_rademacherPairCharacter_mul {n : ℕ}
    (p q : RademacherIndexPair n) :
    ∫ ω, rademacherPairCharacter p ω * rademacherPairCharacter q ω
      ∂selectorLaw (Fin n) =
        if rademacherPairSupport p = rademacherPairSupport q then 1 else 0 := by
  classical
  have hpoint (ω : Fin n → Bool) :
      rademacherPairCharacter p ω * rademacherPairCharacter q ω =
        rademacherCharacter (rademacherSupportSymmDiff (rademacherPairSupport p) (rademacherPairSupport q)) ω := by
    rw [rademacherPairCharacter_eq_character, rademacherPairCharacter_eq_character,
      rademacherCharacter_mul_symmDiff]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  by_cases h : rademacherPairSupport p = rademacherPairSupport q
  · simp [h, rademacherCharacter, rademacherSupportSymmDiff]
  · have hne : (rademacherSupportSymmDiff (rademacherPairSupport p) (rademacherPairSupport q)).Nonempty := by
      by_contra hne
      have hempty : rademacherSupportSymmDiff
          (rademacherPairSupport p) (rademacherPairSupport q) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      have hsub : rademacherPairSupport p ⊆ rademacherPairSupport q := by
        intro i hi
        by_contra hnot
        have hmem : i ∈ rademacherSupportSymmDiff
            (rademacherPairSupport p) (rademacherPairSupport q) := by
          simp [rademacherSupportSymmDiff, hi, hnot]
        rw [hempty] at hmem
        simp at hmem
      have hsub' : rademacherPairSupport q ⊆ rademacherPairSupport p := by
        intro i hi
        by_contra hnot
        have hmem : i ∈ rademacherSupportSymmDiff
            (rademacherPairSupport p) (rademacherPairSupport q) := by
          simp [rademacherSupportSymmDiff, hi, hnot]
        rw [hempty] at hmem
        simp at hmem
      apply h
      exact Finset.Subset.antisymm hsub hsub'
    rw [show (∫ ω, rademacherCharacter
        (rademacherSupportSymmDiff (rademacherPairSupport p) (rademacherPairSupport q)) ω
          ∂selectorLaw (Fin n)) = 0 from
      integral_selector_sign_prod_eq_zero _ hne]
    simp [h]

#print axioms DGRHS.Decoupling.rademacherCharacter_mul_symmDiff
#print axioms DGRHS.Decoupling.integral_rademacherPairCharacter_mul

end DGRHS.Decoupling
