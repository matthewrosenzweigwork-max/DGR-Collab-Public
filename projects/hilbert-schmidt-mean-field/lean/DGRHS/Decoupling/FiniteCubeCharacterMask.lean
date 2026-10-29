import DGRHS.Decoupling.RademacherPairOrthogonality

noncomputable section
open MeasureTheory ProbabilityTheory

namespace DGRHS.Decoupling.FiniteCube
open DGRHS.Decoupling

abbrev Cube (n : ℕ) := Fin n → Bool

def cubeTail {n : ℕ} (ω : Cube (n+1)) : Cube n := fun i => ω i.succ

def boolMaskSupport {n : ℕ} (s : Cube n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => s i = true)

def boolMaskCharacter {n : ℕ} (s : Cube n) (ω : Cube n) : ℝ :=
  rademacherCharacter (boolMaskSupport s) ω

def cubeWalsh : (n : ℕ) → Cube n → Cube n → ℝ
  | 0, _, _ => 1
  | n+1, s, ω =>
      (if s 0 then rademacherSign (ω 0) else 1) *
        cubeWalsh n (cubeTail s) (cubeTail ω)

def cubeWalshDegree : (n : ℕ) → Cube n → ℕ
  | 0, _ => 0
  | n+1, s => (if s 0 then 1 else 0) + cubeWalshDegree n (cubeTail s)

lemma finSucc_injective {n : ℕ} :
    Function.Injective (fun i : Fin n => i.succ : Fin n → Fin (n+1)) := by
  intro i j hij
  apply Fin.ext
  exact Nat.succ.inj (by simpa using congrArg Fin.val hij)

lemma mem_boolMaskSupport {n : ℕ} (s : Cube n) (i : Fin n) :
    i ∈ boolMaskSupport s ↔ s i = true := by
  simp [boolMaskSupport]

lemma finSucc_image_mem_iff {n : ℕ} (t : Finset (Fin n)) (i : Fin n) :
    i.succ ∈ t.image Fin.succ ↔ i ∈ t := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    have h : j = i := finSucc_injective hji
    simpa [h] using hj
  · intro hi
    exact ⟨i, hi, rfl⟩

lemma boolMaskSupport_split {n : ℕ} (s : Cube (n+1)) :
    boolMaskSupport s =
      (if s 0 then ({0} : Finset (Fin (n+1))) else ∅) ∪
        (boolMaskSupport (cubeTail s)).image Fin.succ := by
  classical
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · cases hzero : s 0 <;>
      simp [boolMaskSupport, cubeTail, hzero, Finset.mem_filter]
  · rw [mem_boolMaskSupport, Finset.mem_union, finSucc_image_mem_iff]
    by_cases hs : s 0 = true <;>
      simp [hs, mem_boolMaskSupport, Fin.succ_ne_zero]
    all_goals rfl

lemma finSucc_image_disjoint_zero {n : ℕ} (t : Finset (Fin n)) :
    Disjoint ({0} : Finset (Fin (n+1))) (t.image Fin.succ) := by
  apply Finset.disjoint_left.mpr
  intro i hi him
  rcases Finset.mem_image.mp him with ⟨j, hj, hji⟩
  subst i
  simp at hi

lemma boolMaskSupport_card_split {n : ℕ} (s : Cube (n+1)) :
    (boolMaskSupport s).card =
      (if s 0 then 1 else 0) + (boolMaskSupport (cubeTail s)).card := by
  classical
  rw [boolMaskSupport_split]
  by_cases hs : s 0 = true
  · rw [if_pos hs, Finset.card_union_of_disjoint
      (finSucc_image_disjoint_zero (boolMaskSupport (cubeTail s))),
      Finset.card_singleton,
      Finset.card_image_of_injective _ finSucc_injective]
    simpa using hs
  · rw [if_neg hs, Finset.empty_union,
      Finset.card_image_of_injective _ finSucc_injective]
    have hs' : s 0 = false := Bool.eq_false_iff.mpr hs
    simp [hs']

lemma rademacherCharacter_cons_support {n : ℕ}
    (s : Cube (n+1)) (b : Bool) (x : Cube n) :
    rademacherCharacter (boolMaskSupport s) (Fin.cons b x) =
      (if s 0 then rademacherSign b else 1) *
        rademacherCharacter (boolMaskSupport (cubeTail s)) x := by
  classical
  rw [boolMaskSupport_split]
  cases hzero : s 0
  · simp only [hzero, Bool.false_eq_true, if_false, Finset.empty_union]
    unfold rademacherCharacter
    rw [Finset.prod_image (fun i hi j hj hij => finSucc_injective hij)]
    simp only [Fin.cons_succ, cubeTail, one_mul]
  · have hdisj := finSucc_image_disjoint_zero (boolMaskSupport (cubeTail s))
    simp [hzero]
    unfold rademacherCharacter
    have hzero_not_mem : (0 : Fin (n + 1)) ∉
        (boolMaskSupport (cubeTail s)).image Fin.succ := by
      intro hmem
      have hsingleton : (0 : Fin (n + 1)) ∈ ({0} : Finset (Fin (n + 1))) := by simp
      exact (Finset.disjoint_left.mp hdisj hsingleton) hmem
    rw [Finset.prod_insert hzero_not_mem,
      Finset.prod_image (fun i hi j hj hij => finSucc_injective hij)]
    simp only [Fin.cons_zero, Fin.cons_succ, cubeTail]

theorem cubeWalsh_eq_boolMaskCharacter :
    ∀ n (s : Cube n) (ω : Cube n),
      cubeWalsh n s ω = boolMaskCharacter s ω := by
  intro n
  induction n with
  | zero =>
      intro s ω
      simp [cubeWalsh, boolMaskCharacter, boolMaskSupport, rademacherCharacter]
  | succ n ih =>
      intro s ω
      simp only [cubeWalsh, boolMaskCharacter]
      have hω : Fin.cons (ω 0) (cubeTail ω) = ω := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      have hchar := rademacherCharacter_cons_support s (ω 0) (cubeTail ω)
      rw [hω] at hchar
      rw [hchar, ih (cubeTail s) (cubeTail ω)]
      rfl

theorem cubeWalshDegree_eq_support_card :
    ∀ n (s : Cube n), cubeWalshDegree n s = (boolMaskSupport s).card := by
  intro n
  induction n with
  | zero =>
      intro s
      simp [cubeWalshDegree, boolMaskSupport]
  | succ n ih =>
      intro s
      rw [cubeWalshDegree, boolMaskSupport_card_split]
      simp [ih]

def sourceSupportMask {n : ℕ} (I : Finset (Fin n)) : Cube n :=
  fun i => decide (i ∈ I)

lemma boolMaskSupport_sourceSupportMask {n : ℕ} (I : Finset (Fin n)) :
    boolMaskSupport (sourceSupportMask I) = I := by
  classical
  ext i
  simp [boolMaskSupport, sourceSupportMask]

theorem boolMaskCharacter_sourceSupportMask {n : ℕ}
    (I : Finset (Fin n)) (ω : Cube n) :
    boolMaskCharacter (sourceSupportMask I) ω = rademacherCharacter I ω := by
  rw [boolMaskCharacter, boolMaskSupport_sourceSupportMask]

theorem cubeWalsh_sourceSupportMask {n : ℕ}
    (I : Finset (Fin n)) (ω : Cube n) :
    cubeWalsh n (sourceSupportMask I) ω = rademacherCharacter I ω := by
  rw [cubeWalsh_eq_boolMaskCharacter, boolMaskCharacter_sourceSupportMask]

theorem cubeWalshDegree_sourceSupportMask {n : ℕ}
    (I : Finset (Fin n)) :
    cubeWalshDegree n (sourceSupportMask I) = I.card := by
  rw [cubeWalshDegree_eq_support_card, boolMaskSupport_sourceSupportMask]

/-- Distinct Boolean masks are orthogonal under the fair product law. -/
theorem integral_boolMaskCharacter_mul {n : ℕ} (s t : Cube n) :
    ∫ ω, boolMaskCharacter s ω * boolMaskCharacter t ω ∂selectorLaw (Fin n) =
      if s = t then 1 else 0 := by
  classical
  have hpoint (ω : Cube n) :
      boolMaskCharacter s ω * boolMaskCharacter t ω =
        rademacherCharacter
          (rademacherSupportSymmDiff (boolMaskSupport s) (boolMaskSupport t)) ω := by
    change rademacherCharacter (boolMaskSupport s) ω *
      rademacherCharacter (boolMaskSupport t) ω = _
    exact rademacherCharacter_mul_symmDiff _ _ _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  by_cases hst : s = t
  · subst t
    simp [rademacherCharacter, rademacherSupportSymmDiff]
  · have hmask : boolMaskSupport s ≠ boolMaskSupport t := by
      intro h
      apply hst
      funext i
      have hm : i ∈ boolMaskSupport s ↔ i ∈ boolMaskSupport t :=
        Finset.ext_iff.mp h i
      cases hs : s i <;> cases ht : t i <;>
        simp [boolMaskSupport, hs, ht] at hm ⊢
    have hne :
        (rademacherSupportSymmDiff (boolMaskSupport s) (boolMaskSupport t)).Nonempty := by
      by_contra hne
      have hempty : rademacherSupportSymmDiff
          (boolMaskSupport s) (boolMaskSupport t) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      have hstSub : boolMaskSupport s ⊆ boolMaskSupport t := by
        intro i hi
        by_contra hnot
        have hmem : i ∈ rademacherSupportSymmDiff
            (boolMaskSupport s) (boolMaskSupport t) := by
          simp [rademacherSupportSymmDiff, hi, hnot]
        rw [hempty] at hmem
        simp at hmem
      have htsSub : boolMaskSupport t ⊆ boolMaskSupport s := by
        intro i hi
        by_contra hnot
        have hmem : i ∈ rademacherSupportSymmDiff
            (boolMaskSupport s) (boolMaskSupport t) := by
          simp [rademacherSupportSymmDiff, hi, hnot]
        rw [hempty] at hmem
        simp at hmem
      exact hmask (Finset.Subset.antisymm hstSub htsSub)
    have hzero :
        ∫ ω, rademacherCharacter
          (rademacherSupportSymmDiff (boolMaskSupport s) (boolMaskSupport t)) ω
          ∂selectorLaw (Fin n) = 0 :=
      integral_selector_sign_prod_eq_zero _ hne
    rw [hzero]
    simp [hst]

def finiteBoolWalshPolynomial {n : ℕ} (c : Cube n → ℝ) (ω : Cube n) : ℝ :=
  ∑ s : Cube n, c s * boolMaskCharacter s ω

theorem integral_finiteBoolWalshPolynomial_sq {n : ℕ} (c : Cube n → ℝ) :
    ∫ ω, finiteBoolWalshPolynomial c ω ^ 2 ∂selectorLaw (Fin n) =
      ∑ s : Cube n, c s ^ 2 := by
  classical
  have hi (s t : Cube n) :
      Integrable (fun ω => boolMaskCharacter s ω * boolMaskCharacter t ω)
        (selectorLaw (Fin n)) := Integrable.of_finite
  have hpoint (ω : Cube n) :
      finiteBoolWalshPolynomial c ω ^ 2 =
        ∑ s : Cube n, ∑ t : Cube n,
          (c s * c t) * (boolMaskCharacter s ω * boolMaskCharacter t ω) := by
    unfold finiteBoolWalshPolynomial
    calc
      (∑ s : Cube n, c s * boolMaskCharacter s ω) ^ 2 =
          (∑ s : Cube n, c s * boolMaskCharacter s ω) *
            (∑ t : Cube n, c t * boolMaskCharacter t ω) := by rw [pow_two]
      _ = ∑ s : Cube n,
          (c s * boolMaskCharacter s ω) *
            (∑ t : Cube n, c t * boolMaskCharacter t ω) := by rw [Finset.sum_mul]
      _ = ∑ s : Cube n, ∑ t : Cube n,
          (c s * c t) * (boolMaskCharacter s ω * boolMaskCharacter t ω) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
  calc
    ∫ ω, finiteBoolWalshPolynomial c ω ^ 2 ∂selectorLaw (Fin n) =
        ∫ ω, ∑ s : Cube n, ∑ t : Cube n,
          (c s * c t) * (boolMaskCharacter s ω * boolMaskCharacter t ω)
          ∂selectorLaw (Fin n) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∑ s : Cube n, ∑ t : Cube n,
        (c s * c t) *
          (∫ ω, boolMaskCharacter s ω * boolMaskCharacter t ω ∂selectorLaw (Fin n)) := by
          rw [integral_finsetSum _ (fun s _ =>
            integrable_finsetSum _ (fun t _ => (hi s t).const_mul _))]
          simp_rw [integral_finsetSum _ (fun t _ => (hi _ t).const_mul _),
            integral_const_mul]
    _ = ∑ s : Cube n, c s ^ 2 := by
          simp only [integral_boolMaskCharacter_mul, mul_ite, mul_one, mul_zero,
            Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
          apply Finset.sum_congr rfl
          intro s hs
          ring

end DGRHS.Decoupling.FiniteCube

#print axioms DGRHS.Decoupling.FiniteCube.finSucc_injective
#print axioms DGRHS.Decoupling.FiniteCube.boolMaskSupport_split
#print axioms DGRHS.Decoupling.FiniteCube.finSucc_image_disjoint_zero
#print axioms DGRHS.Decoupling.FiniteCube.boolMaskSupport_card_split
#print axioms DGRHS.Decoupling.FiniteCube.rademacherCharacter_cons_support
#print axioms DGRHS.Decoupling.FiniteCube.cubeWalsh_eq_boolMaskCharacter
#print axioms DGRHS.Decoupling.FiniteCube.cubeWalshDegree_eq_support_card
#print axioms DGRHS.Decoupling.FiniteCube.boolMaskSupport_sourceSupportMask
#print axioms DGRHS.Decoupling.FiniteCube.boolMaskCharacter_sourceSupportMask
#print axioms DGRHS.Decoupling.FiniteCube.cubeWalsh_sourceSupportMask
#print axioms DGRHS.Decoupling.FiniteCube.cubeWalshDegree_sourceSupportMask
#print axioms DGRHS.Decoupling.FiniteCube.integral_boolMaskCharacter_mul
#print axioms DGRHS.Decoupling.FiniteCube.integral_finiteBoolWalshPolynomial_sq
