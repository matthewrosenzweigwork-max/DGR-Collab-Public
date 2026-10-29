import LeanResearch.PeriodicAttractiveLogGas.CanonicalPairCounts
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Basic

/-! Exact finite word-fiber enumeration. The factorial identity is proved by
an actual equivalence between labelled-slot bijections and decorated words. -/

noncomputable section
open Finset
open scoped BigOperators

namespace PeriodicAttractiveLogGas.CanonicalWordEnumeration
open CanonicalPairCounts

variable {m k : ℕ}

/-- Actual words with the prescribed multiplicity of every symbol. -/
def wordFiber (a : Fin m → ℕ) : Finset (Fin (2 * k) → Fin m) :=
  Finset.univ.filter (fun w => ∀ i, wordMultiplicity w i = a i)

@[simp] theorem mem_wordFiber {a : Fin m → ℕ} {w : Fin (2 * k) → Fin m} :
    w ∈ wordFiber (k := k) a ↔ ∀ i, wordMultiplicity w i = a i := by
  simp [wordFiber]

theorem card_rowFiber (w : Fin (2 * k) → Fin m) (i : Fin m) :
    Fintype.card {ℓ // w ℓ = i} = wordMultiplicity w i := by
  rw [Fintype.card_subtype]
  rfl

/-- Reconstruct a bijection of all labelled slots from a word and its row bijections. -/
def assemble (a : Fin m → ℕ) (w : wordFiber (k := k) a)
    (g : ∀ i, Fin (a i) ≃ {ℓ // w.val ℓ = i}) :
    (Σ i, Fin (a i)) ≃ Fin (2 * k) :=
  (Equiv.sigmaCongrRight g).trans (Equiv.sigmaFiberEquiv w.val)

@[simp] theorem assemble_apply (a : Fin m → ℕ) (w : wordFiber (k := k) a)
    (g : ∀ i, Fin (a i) ≃ {ℓ // w.val ℓ = i}) (i : Fin m) (j : Fin (a i)) :
    assemble a w g ⟨i, j⟩ = (g i j).val := rfl

theorem assemble_label (a : Fin m → ℕ) (w : wordFiber (k := k) a)
    (g : ∀ i, Fin (a i) ≃ {ℓ // w.val ℓ = i}) (s : Σ i, Fin (a i)) :
    w.val (assemble a w g s) = s.1 := (g s.1 s.2).prop

/-- A bijection labels each target slot by the row of its inverse image. -/
def wordOfEquiv {a : Fin m → ℕ} (e : (Σ i, Fin (a i)) ≃ Fin (2 * k)) :
    Fin (2 * k) → Fin m := fun ℓ => (e.symm ℓ).1

/-- Restriction of a slot bijection to one row, with both directions explicit
through subtype equivalences. -/
def fiberEquivOfEquiv {a : Fin m → ℕ} (e : (Σ i, Fin (a i)) ≃ Fin (2 * k)) (i : Fin m) :
    Fin (a i) ≃ {ℓ // wordOfEquiv e ℓ = i} :=
  (Equiv.sigmaSubtype i).symm.trans
    (e.subtypeEquiv (fun s => by simp [wordOfEquiv]))

@[simp] theorem fiberEquivOfEquiv_apply {a : Fin m → ℕ}
    (e : (Σ i, Fin (a i)) ≃ Fin (2 * k)) (i : Fin m) (j : Fin (a i)) :
    (fiberEquivOfEquiv e i j).val = e ⟨i, j⟩ := rfl

theorem wordOfEquiv_mem {a : Fin m → ℕ} (e : (Σ i, Fin (a i)) ≃ Fin (2 * k)) :
    wordOfEquiv e ∈ wordFiber (k := k) a := by
  rw [mem_wordFiber]
  intro i
  rw [← card_rowFiber]
  exact (Fintype.card_congr (fiberEquivOfEquiv e i)).symm.trans (Fintype.card_fin (a i))

/-- All slot bijections are assembled, and a slot bijection determines its
word and every row bijection uniquely. -/
theorem assemble_bijective (a : Fin m → ℕ) :
    Function.Bijective (fun z : Σ w : wordFiber (k := k) a,
      ∀ i, Fin (a i) ≃ {ℓ // w.val ℓ = i} => assemble a z.1 z.2) := by
  constructor
  · rintro ⟨w, g⟩ ⟨v, h⟩ he
    change assemble a w g = assemble a v h at he
    have hw : w = v := by
      apply Subtype.ext
      funext ℓ
      obtain ⟨s, rfl⟩ := (assemble a w g).surjective ℓ
      rw [assemble_label, he, assemble_label]
    subst v
    have hg : g = h := by
      funext i
      apply Equiv.ext
      intro j
      apply Subtype.ext
      exact congrArg (fun e : (Σ i, Fin (a i)) ≃ Fin (2 * k) => e ⟨i, j⟩) he
    subst h
    rfl
  · intro e
    refine ⟨⟨⟨wordOfEquiv e, wordOfEquiv_mem e⟩, fiberEquivOfEquiv e⟩, ?_⟩
    apply Equiv.ext
    rintro ⟨i, j⟩
    rfl

/-- The finite equivalence used to count words, with no multinomial premise. -/
def decoratedWordsEquiv (a : Fin m → ℕ) :
    (Σ w : wordFiber (k := k) a, ∀ i, Fin (a i) ≃ {ℓ // w.val ℓ = i}) ≃
      ((Σ i, Fin (a i)) ≃ Fin (2 * k)) :=
  Equiv.ofBijective _ (assemble_bijective a)

/-- Actual word-fiber cardinality, written without division. This includes zero
multiplicities and the empty word/alphabet whenever the total-count premise permits them. -/
theorem card_wordFiber_mul_factorials (a : Fin m → ℕ) (ha : (∑ i, a i) = 2 * k) :
    (wordFiber (k := k) a).card * (∏ i, (a i).factorial) = (2 * k).factorial := by
  classical
  have hΓ : Fintype.card (Σ i, Fin (a i)) = 2 * k := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using ha
  let e : (Σ i, Fin (a i)) ≃ Fin (2 * k) :=
    Fintype.equivOfCardEq (hΓ.trans (Fintype.card_fin (2 * k)).symm)
  have hrow (w : wordFiber (k := k) a) (i : Fin m) :
      Fintype.card (Fin (a i) ≃ {ℓ // w.val ℓ = i}) = (a i).factorial := by
    let ei : Fin (a i) ≃ {ℓ // w.val ℓ = i} := Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, card_rowFiber, (mem_wordFiber.mp w.prop) i])
    simpa only [Fintype.card_fin] using Fintype.card_equiv ei
  have hdecor (w : wordFiber (k := k) a) :
      Fintype.card (∀ i, Fin (a i) ≃ {ℓ // w.val ℓ = i}) = ∏ i, (a i).factorial := by
    simp only [Fintype.card_pi, hrow]
  have he : Fintype.card ((Σ i, Fin (a i)) ≃ Fin (2 * k)) = (2 * k).factorial := by
    rw [Fintype.card_equiv e, hΓ]
  have hc := Fintype.card_congr (decoratedWordsEquiv (k := k) a)
  simpa only [Fintype.card_sigma, hdecor, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, Nat.cast_id, he] using hc

/-- The actual word counts as a finitely supported multiplicity vector. -/
def wordCounts (w : Fin (2 * k) → Fin m) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (wordMultiplicity w)

@[simp] theorem wordCounts_apply (w : Fin (2 * k) → Fin m) (i : Fin m) :
    wordCounts w i = wordMultiplicity w i := rfl

theorem wordCounts_mem {w : Fin (2 * k) → Fin m} (hw : w ∈ singletonFreeWords m k) :
    wordCounts w ∈ multiplicityVectors m k := by
  rw [mem_multiplicityVectors]
  exact ⟨sum_wordMultiplicity w, mem_singletonFreeWords.mp hw⟩

/-- Fiberwise summation over the existing multiplicity vectors uses exactly the
same actual word fibers; singleton freedom introduces no additional multiplicity. -/
theorem filter_wordCounts_eq_wordFiber {a : Fin m →₀ ℕ} (ha : a ∈ multiplicityVectors m k) :
    (singletonFreeWords m k).filter (fun w => wordCounts w = a) =
      wordFiber (k := k) (fun i => a i) := by
  ext w
  rw [Finset.mem_filter, mem_wordFiber]
  constructor
  · rintro ⟨_, he⟩ i
    exact congrArg (fun b : Fin m →₀ ℕ => b i) he
  · intro he
    constructor
    · rw [mem_singletonFreeWords]
      intro i
      rw [he i]
      exact (mem_multiplicityVectors.mp ha).2 i
    · ext i
      exact he i

/-- Each multiplicity fiber contributes exactly the total-slot factorial to the
weighted row-word sum. -/
theorem sum_factorials_wordFiber {a : Fin m →₀ ℕ} (ha : a ∈ multiplicityVectors m k) :
    (∑ w ∈ wordFiber (k := k) (fun i => a i), ∏ i, (wordMultiplicity w i).factorial) =
      (2 * k).factorial := by
  calc
    _ = ∑ _w ∈ wordFiber (k := k) (fun i => a i), ∏ i, (a i).factorial := by
      apply Finset.sum_congr rfl
      intro w hw
      apply Finset.prod_congr rfl
      intro i _
      rw [(mem_wordFiber.mp hw) i]
    _ = (wordFiber (k := k) (fun i => a i)).card * ∏ i, (a i).factorial := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ = (2 * k).factorial :=
      card_wordFiber_mul_factorials (fun i => a i) (mem_multiplicityVectors.mp ha).1

/-- Exact division-free weighted count of all singleton-free row words. -/
theorem sum_factorials_singletonFreeWords (m k : ℕ) :
    (∑ w ∈ singletonFreeWords m k, ∏ i, (wordMultiplicity w i).factorial) =
      (2 * k).factorial * A m k := by
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s := singletonFreeWords m k) (t := multiplicityVectors m k) (g := wordCounts)
    (fun w hw => wordCounts_mem hw) (fun w => ∏ i, (wordMultiplicity w i).factorial)
  rw [← hsum]
  calc
    _ = ∑ _a ∈ multiplicityVectors m k, (2 * k).factorial := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [filter_wordCounts_eq_wordFiber ha]
      exact sum_factorials_wordFiber ha
    _ = (2 * k).factorial * A m k := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, A, Nat.mul_comm]

/-- Real-valued form for direct use in the integrated moment estimate. -/
theorem sum_factorials_singletonFreeWords_real (m k : ℕ) :
    (∑ w ∈ singletonFreeWords m k, ∏ i, ((wordMultiplicity w i).factorial : ℝ)) =
      ((2 * k).factorial : ℝ) * (A m k : ℝ) := by
  exact_mod_cast sum_factorials_singletonFreeWords m k

end PeriodicAttractiveLogGas.CanonicalWordEnumeration
