import FullLabeledLSI.Defs.F04_Reveal
import FullLabeledLSI.Infra.RevealCount

/-!
# Section 5 infrastructure, part 4: the uniform averages of the random reveal

* `avg1 N j F = E_S (N-j)⁻¹ ∑_{i ∈ Sᶜ} F S i` (uniform `j`-subset `S`, uniform `i ∈ Sᶜ`),
* `avgK N j k F = E_S (N-j)_k⁻¹ ∑_{I ∈ distinctTuples S k} F S I` (uniform ordered distinct
  `k`-tuple in `Sᶜ`),
all in `ℝ≥0∞`. `hRev` and `dRev` of F04 are these averages of the integrands.
-/

open Finset
open scoped ENNReal Nat

namespace SharpLSI.FL

variable {d N : ℕ}

/-- Uniform `j`-subset `S`, uniform label `i ∈ Sᶜ`. -/
noncomputable def avg1 (N j : ℕ) (F : Finset (Fin N) → Fin N → ℝ≥0∞) : ℝ≥0∞ :=
  ((Nat.choose N j : ℝ≥0∞)⁻¹) * ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
    ((N - j : ℕ) : ℝ≥0∞)⁻¹ * ∑ i ∈ Sᶜ, F S i

/-- Uniform `j`-subset `S`, uniform ordered distinct `k`-tuple in `Sᶜ`. -/
noncomputable def avgK (N j k : ℕ) (F : Finset (Fin N) → (Fin k → Fin N) → ℝ≥0∞) : ℝ≥0∞ :=
  ((Nat.choose N j : ℝ≥0∞)⁻¹) * ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
    ((Nat.descFactorial (N - j) k : ℝ≥0∞)⁻¹) * ∑ I ∈ distinctTuples S k, F S I

/-! ### Auxiliary lemmas -/

private theorem natCast_ne_top' (n : ℕ) : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n

private theorem natCast_ne_zero' {n : ℕ} (h : n ≠ 0) : (n : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast h

/-- Normalization lemma: `a⁻¹ * (e • T) = R⁻¹ * T` when `a = R * e`, `e ≠ 0`. -/
theorem inv_nsmul_eq_inv (a R e : ℕ) (he : e ≠ 0) (h : a = R * e) (T : ℝ≥0∞) :
    (a : ℝ≥0∞)⁻¹ * (e • T) = (R : ℝ≥0∞)⁻¹ * T := by
  subst h
  push_cast
  rw [ENNReal.mul_inv (Or.inr (natCast_ne_top' _)) (Or.inl (natCast_ne_top' _)), nsmul_eq_mul]
  calc (R : ℝ≥0∞)⁻¹ * (e : ℝ≥0∞)⁻¹ * ((e : ℝ≥0∞) * T)
      = (R : ℝ≥0∞)⁻¹ * (((e : ℝ≥0∞)⁻¹ * (e : ℝ≥0∞)) * T) := by ring
    _ = (R : ℝ≥0∞)⁻¹ * T := by
      rw [ENNReal.inv_mul_cancel (natCast_ne_zero' he) (natCast_ne_top' _), one_mul]

/-- `avgK` as a single normalizing constant times a double sum. -/
theorem avgK_eq (N j k : ℕ) (F : Finset (Fin N) → (Fin k → Fin N) → ℝ≥0∞) :
    avgK N j k F = ((Nat.choose N j * (N - j).descFactorial k : ℕ) : ℝ≥0∞)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∑ I ∈ distinctTuples S k, F S I := by
  unfold avgK
  rw [← Finset.mul_sum, ← mul_assoc,
    ← ENNReal.mul_inv (Or.inr (natCast_ne_top' _)) (Or.inl (natCast_ne_top' _))]
  push_cast
  rfl

/-- `avg1` as a single normalizing constant times a double sum. -/
theorem avg1_eq (N j : ℕ) (F : Finset (Fin N) → Fin N → ℝ≥0∞) :
    avg1 N j F = ((Nat.choose N j * (N - j) : ℕ) : ℝ≥0∞)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∑ i ∈ Sᶜ, F S i := by
  unfold avg1
  rw [← Finset.mul_sum, ← mul_assoc,
    ← ENNReal.mul_inv (Or.inr (natCast_ne_top' _)) (Or.inl (natCast_ne_top' _))]
  push_cast
  rfl

/-- Distinct `1`-tuples in `Sᶜ` are the elements of `Sᶜ`. -/
theorem sum_distinctTuples_one {M : Type*} [AddCommMonoid M] (S : Finset (Fin N))
    (G : Fin N → M) : ∑ J ∈ distinctTuples S 1, G (J 0) = ∑ i ∈ Sᶜ, G i := by
  refine Finset.sum_nbij' (fun J => J 0) (fun i _ => i) ?_ ?_ ?_ ?_ ?_
  · intro J hJ
    simp only [distinctTuples, mem_filter, mem_univ, true_and] at hJ
    exact mem_compl.2 (hJ.2 0)
  · intro i hi
    simp only [distinctTuples, mem_filter, mem_univ, true_and]
    exact ⟨fun a b _ => Subsingleton.elim a b, fun _ => mem_compl.1 hi⟩
  · intro J _
    funext l
    rw [Subsingleton.elim l 0]
  · intro i _
    rfl
  · intro J _
    rfl

theorem preSet_comp_castLE {k a : ℕ} (hk : a + 1 ≤ k) (S : Finset (Fin N)) (I : Fin k → Fin N) :
    preSet S (I ∘ Fin.castLE hk) a = preSet S I a := by
  unfold preSet
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨Fin.castLE hk l, by simpa using hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l.val, by omega⟩, hl, rfl⟩

theorem descFactorial_eq_mul {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    n.descFactorial k = n * (n - 1).descFactorial (k - 1) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Nat.succ_descFactorial_succ]
  simp

theorem choose_descFactorial_glob {N j k : ℕ} (hjk : j + k ≤ N) :
    Nat.choose N j * (N - j).descFactorial k = N.descFactorial k * Nat.choose (N - k) j := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := N) (k := j) (by omega)
  have h2 := Nat.factorial_mul_descFactorial (n := N - j) (k := k) (by omega)
  have h3 := Nat.factorial_mul_descFactorial (n := N) (k := k) (by omega)
  have h4 := Nat.choose_mul_factorial_mul_factorial (n := N - k) (k := j) (by omega)
  rw [show N - j - k = N - k - j by omega] at h2
  have hpos : 0 < j ! * (N - k - j)! := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.choose N j * (N - j).descFactorial k * (j ! * (N - k - j)!)
      = Nat.choose N j * j ! * ((N - k - j)! * (N - j).descFactorial k) := by ring
    _ = N ! := by rw [h2]; exact h1
    _ = (N - k)! * N.descFactorial k := h3.symm
    _ = N.descFactorial k * (Nat.choose (N - k) j * j ! * (N - k - j)!) := by rw [h4]; ring
    _ = N.descFactorial k * Nat.choose (N - k) j * (j ! * (N - k - j)!) := by ring

theorem choose_descFactorial_pre {N j k a : ℕ} (hjk : j + k ≤ N) (ha : a < k) :
    Nat.choose N j * (N - j).descFactorial k =
      Nat.choose N (j + a) * (N - (j + a)) *
        ((N - j - (a + 1)).descFactorial (k - (a + 1)) * (j + a).descFactorial a) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (n := N) (k := j) (by omega)
  have h2 := Nat.factorial_mul_descFactorial (n := N - j) (k := k) (by omega)
  have h3 := Nat.choose_mul_factorial_mul_factorial (n := N) (k := j + a) (by omega)
  have h5 := Nat.factorial_mul_descFactorial (n := j + a) (k := a) (by omega)
  rw [show j + a - a = j by omega] at h5
  have h6 := Nat.succ_descFactorial_succ (N - j - (a + 1)) (k - (a + 1))
  have h7 := Nat.factorial_mul_descFactorial (n := N - j - (a + 1) + 1) (k := k - (a + 1) + 1)
    (by omega)
  rw [h6, show N - j - (a + 1) + 1 - (k - (a + 1) + 1) = N - j - k by omega,
    show N - j - (a + 1) + 1 = N - (j + a) by omega] at h7
  have hpos : 0 < j ! * (N - j - k)! := Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.choose N j * (N - j).descFactorial k * (j ! * (N - j - k)!)
      = Nat.choose N j * j ! * ((N - j - k)! * (N - j).descFactorial k) := by ring
    _ = N ! := by rw [h2]; exact h1
    _ = Nat.choose N (j + a) * (j + a)! * (N - (j + a))! := h3.symm
    _ = Nat.choose N (j + a) * (j ! * (j + a).descFactorial a) *
          ((N - j - k)! * ((N - (j + a)) * (N - j - (a + 1)).descFactorial (k - (a + 1)))) := by
      rw [h5, h7]
    _ = Nat.choose N (j + a) * (N - (j + a)) *
        ((N - j - (a + 1)).descFactorial (k - (a + 1)) * (j + a).descFactorial a) *
        (j ! * (N - j - k)!) := by ring

/-- The number of ordered distinct `k`-tuples in the complement of a `j`-subset. -/
theorem card_distinctTuples {S : Finset (Fin N)} {j : ℕ} (hS : S.card = j) (k : ℕ) :
    (distinctTuples S k).card = (N - j).descFactorial k := by
  have hinj : Function.Injective
      (fun (e : Fin k ↪ ↥(Sᶜ)) (l : Fin k) => ((e l : ↥(Sᶜ)) : Fin N)) := by
    intro e1 e2 h
    exact Function.Embedding.ext fun l => Subtype.ext (congrFun h l)
  have hset : distinctTuples S k = (Finset.univ : Finset (Fin k ↪ ↥(Sᶜ))).image
      (fun (e : Fin k ↪ ↥(Sᶜ)) (l : Fin k) => ((e l : ↥(Sᶜ)) : Fin N)) := by
    ext I
    simp only [distinctTuples, mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨hI, hS'⟩
      exact ⟨⟨fun l => ⟨I l, mem_compl.2 (hS' l)⟩, fun a b h => hI (by simpa using h)⟩, rfl⟩
    · rintro ⟨e, rfl⟩
      exact ⟨fun a b h => e.injective (Subtype.ext h), fun l => mem_compl.1 (e l).2⟩
  rw [hset, card_image_of_injective _ hinj, card_univ, Fintype.card_embedding_eq,
    Fintype.card_fin, Fintype.card_coe, card_compl, Fintype.card_fin, hS]

/-- The average of a constant. -/
theorem avgK_const {j k : ℕ} (hjk : j + k ≤ N) (c : ℝ≥0∞) :
    avgK N j k (fun _ _ => c) = c := by
  have hD : ((N - j).descFactorial k : ℝ≥0∞) ≠ 0 :=
    natCast_ne_zero' (Nat.descFactorial_pos.2 (by omega)).ne'
  have hC : (Nat.choose N j : ℝ≥0∞) ≠ 0 :=
    natCast_ne_zero' (Nat.choose_pos (by omega)).ne'
  unfold avgK
  have h1 : ∀ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      ((Nat.descFactorial (N - j) k : ℝ≥0∞)⁻¹) * ∑ I ∈ distinctTuples S k, c = c := by
    intro S hS
    rw [Finset.sum_const, card_distinctTuples (mem_powersetCard.1 hS).2, nsmul_eq_mul,
      ← mul_assoc, ENNReal.inv_mul_cancel hD (natCast_ne_top' _), one_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, card_powersetCard, card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hC (natCast_ne_top' _), one_mul]

/-- A single coordinate `I_l` of the uniform distinct tuple is uniform in `Sᶜ`. -/
theorem avgK_marg {j k : ℕ} (hjk : j + k ≤ N) (l : Fin k) (F : Finset (Fin N) → Fin N → ℝ≥0∞) :
    avgK N j k (fun S I => F S (I l)) = avg1 N j F := by
  have hk : 1 ≤ k := Nat.succ_le_of_lt (Fin.pos l)
  have step := sum_sum_distinctTuples_sub (N := N) j k 1 (fun _ => l)
    (fun a b _ => Subsingleton.elim a b) hk hjk (fun S J => F S (J 0))
  have h : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      ∑ J ∈ distinctTuples S 1, F S (J 0)) =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∑ i ∈ Sᶜ, F S i :=
    Finset.sum_congr rfl (fun S _ => sum_distinctTuples_one S (F S))
  rw [h] at step
  have step' : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      ∑ I ∈ distinctTuples S k, F S (I l)) =
      (N - j - 1).descFactorial (k - 1) •
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∑ i ∈ Sᶜ, F S i := step
  rw [avgK_eq, avg1_eq, step']
  refine inv_nsmul_eq_inv _ _ _ ?_ ?_ _
  · exact (Nat.descFactorial_pos.2 (by omega)).ne'
  · rw [descFactorial_eq_mul hk (by omega), mul_assoc]

/-- The pair `(S ∪ {I_l : l < a}, I_a)` is a uniform `(j+a)`-subset with a uniform label outside. -/
theorem avgK_pre {j k : ℕ} (hjk : j + k ≤ N) {a : ℕ} (ha : a < k)
    (F : Finset (Fin N) → Fin N → ℝ≥0∞) :
    avgK N j k (fun S I => F (preSet S I a) (I ⟨a, ha⟩)) = avg1 N (j + a) F := by
  have hja : j + a < N := by omega
  have hk : a + 1 ≤ k := ha
  have step := sum_sum_distinctTuples_sub (N := N) j k (a + 1) (Fin.castLE hk)
    (Fin.castLE_injective hk) hk hjk (fun S J => F (preSet S J a) (J (Fin.last a)))
  have step2 := sum_sum_preSet j a hja F
  have hL : (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j,
      ∑ I ∈ distinctTuples S k, F (preSet S I a) (I ⟨a, ha⟩)) =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard j, ∑ I ∈ distinctTuples S k,
        F (preSet S (I ∘ Fin.castLE hk) a) ((I ∘ Fin.castLE hk) (Fin.last a)) := by
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun I _ => ?_
    rw [preSet_comp_castLE hk]
    rfl
  rw [avgK_eq, avg1_eq, hL, step, step2, smul_smul]
  refine inv_nsmul_eq_inv _ _ _ ?_ ?_ _
  · exact mul_ne_zero (Nat.descFactorial_pos.2 (by omega)).ne'
      (Nat.descFactorial_pos.2 (by omega)).ne'
  · exact choose_descFactorial_pre hjk ha

/-- The tuple `I` is uniform among the injective tuples of `Fin N`. -/
theorem avgK_glob {j k : ℕ} (hjk : j + k ≤ N) (H : (Fin k → Fin N) → ℝ≥0∞) :
    avgK N j k (fun _ I => H I) =
      ((Nat.descFactorial N k : ℝ≥0∞)⁻¹) * ∑ J ∈ injTuples N k, H J := by
  rw [avgK_eq, sum_sum_distinctTuples j k H]
  refine inv_nsmul_eq_inv _ _ _ ?_ ?_ _
  · exact (Nat.choose_pos (by omega)).ne'
  · exact choose_descFactorial_glob hjk

section Unfold

variable (ν : MeasureTheory.Measure (Config N d)) [MeasureTheory.IsFiniteMeasure ν]
  (μ : MeasureTheory.Measure (Torus d))

/-- `h_j` of F04 as an `avg1`. -/
theorem hRev_eq_avg1 {j : ℕ} (hj : j < N) :
    hRev ν μ j = avg1 N j (fun S i => ∫⁻ X, InformationTheory.klDiv
      (condLawS ν S i (restrictS S X)) μ ∂ν) := by
  unfold hRev avg1
  simp only [hj, ↓reduceIte]
  refine congrArg _ (Finset.sum_congr rfl ?_)
  intro S hS
  rw [Finset.card_compl, Fintype.card_fin, (mem_powersetCard.1 hS).2]

/-- `d_{j,k}` of F04 as an `avgK`. -/
theorem dRev_eq_avgK {j k : ℕ} (hjk : j + k ≤ N) :
    dRev ν j k = avgK N j k (fun S I => ∫⁻ X, InformationTheory.klDiv
      (condJointS ν S I (restrictS S X))
      (MeasureTheory.Measure.pi fun l => condLawS ν S (I l) (restrictS S X)) ∂ν) := by
  unfold dRev avgK
  simp only [hjk, ↓reduceIte]

end Unfold

end SharpLSI.FL
