import DGPS.Foundations.AbsoluteDensity

/-!
# Finite species and arbitrary positive weights (DEF011)

INTERFACES/definitions.md §3. A `SpeciesFamily d` consists of a species count `count : ℕ+`, real
weights `θ_s > 0` with `∑ θ_s = 1`, and for each species an `AbsoluteDensity d` (a mass-one
density `u_s²` with `u_s ∈ H¹(m)`, `u_s ≥ 0`). The count is a field, not a global parameter, and
there is no bound on it and no lower bound on the weights. Barycenter and chain rule belong to
DEF012.
-/

namespace DGPS

/-- A finite species family (DEF011). -/
structure SpeciesFamily (d : ℕ) where
  count : ℕ+
  weight : Fin count → ℝ
  weight_pos : ∀ s, 0 < weight s
  weight_sum : ∑ s, weight s = 1
  density : Fin count → AbsoluteDensity d

end DGPS

namespace DGPS.SpeciesFamily

variable {d : ℕ}

theorem weight_nonneg (F : SpeciesFamily d) (s : Fin F.count) : 0 ≤ F.weight s :=
  (F.weight_pos s).le

theorem weight_le_one (F : SpeciesFamily d) (s : Fin F.count) : F.weight s ≤ 1 := by
  rw [← F.weight_sum]
  exact Finset.single_le_sum (fun i _ => F.weight_nonneg i) (Finset.mem_univ s)

theorem weight_lt_one_of_one_lt_count (F : SpeciesFamily d) (h : 1 < (F.count : ℕ))
    (s : Fin F.count) : F.weight s < 1 := by
  obtain ⟨t, hts⟩ : ∃ t : Fin F.count, t ≠ s := by
    by_contra hc
    push Not at hc
    have : Fintype.card (Fin F.count) ≤ 1 := Fintype.card_le_one_iff.2 fun a b => by
      rw [hc a, hc b]
    simp at this; omega
  have hsum : F.weight s + F.weight t ≤ 1 := by
    rw [← F.weight_sum, ← Finset.sum_pair (f := F.weight) hts.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => F.weight_nonneg i)
  linarith [F.weight_pos t]

/-- Construction from raw data: every count, all positive weights summing to one, and any
absolute densities are admitted. -/
def ofData (q : ℕ+) (θ : Fin q → ℝ) (hpos : ∀ s, 0 < θ s) (hsum : ∑ s, θ s = 1)
    (ρ : Fin q → AbsoluteDensity d) : SpeciesFamily d :=
  ⟨q, θ, hpos, hsum, ρ⟩

/-- One-species family: the scalar case, weight `1`. -/
def single (ρ : AbsoluteDensity d) : SpeciesFamily d where
  count := 1
  weight := fun _ => 1
  weight_pos := fun _ => one_pos
  weight_sum := by
    show ∑ _ : Fin 1, (1 : ℝ) = 1
    simp
  density := fun _ => ρ

@[simp] theorem single_count (ρ : AbsoluteDensity d) : (single ρ).count = 1 := rfl

theorem single_weight (ρ : AbsoluteDensity d) (s : Fin (single ρ).count) :
    (single ρ).weight s = 1 := rfl

theorem single_density (ρ : AbsoluteDensity d) (s : Fin (single ρ).count) :
    (single ρ).density s = ρ := rfl

theorem subsingleton_of_count_eq_one (F : SpeciesFamily d) (h : F.count = 1)
    (t s : Fin F.count) : t = s := by
  have hc : Fintype.card (Fin F.count) = 1 := by simp [h]
  exact Fintype.card_le_one_iff.1 hc.le t s

/-- A family with one species has weight `1`. -/
theorem weight_eq_one_of_count_eq_one (F : SpeciesFamily d) (h : F.count = 1)
    (s : Fin F.count) : F.weight s = 1 := by
  have := F.weight_sum
  rwa [Finset.sum_eq_single s
    (fun t _ ht => absurd (F.subsingleton_of_count_eq_one h t s) ht) (by simp)] at this

/-- Reduction to the scalar case: every one-species family is `single` of its density. -/
theorem eq_single_of_count_eq_one (F : SpeciesFamily d) (h : F.count = 1) :
    ∃ ρ : AbsoluteDensity d, ∀ s : Fin F.count, F.weight s = 1 ∧ F.density s = ρ := by
  have h0 : 0 < (F.count : ℕ) := F.count.pos
  refine ⟨F.density ⟨0, h0⟩, fun s => ⟨F.weight_eq_one_of_count_eq_one h s, ?_⟩⟩
  rw [F.subsingleton_of_count_eq_one h s ⟨0, h0⟩]

/-- Uniform weights `1/q` on `q` given densities: every count is realised. -/
noncomputable def uniform (q : ℕ+) (ρ : Fin q → AbsoluteDensity d) : SpeciesFamily d where
  count := q
  weight := fun _ => 1 / (q : ℝ)
  weight_pos := fun _ => by positivity
  weight_sum := by
    have : (q : ℝ) ≠ 0 := by positivity
    simp [Finset.sum_const, Finset.card_univ]
  density := ρ

/-- Every count `q ≥ 1` occurs (no maximum count). -/
theorem exists_count (q : ℕ+) (ρ : AbsoluteDensity d) :
    ∃ F : SpeciesFamily d, F.count = q :=
  ⟨uniform q fun _ => ρ, rfl⟩

/-- Species with arbitrarily small weight occur (no uniform positive lower bound):
two species with weights `ε, 1-ε` for any `0 < ε < 1`. -/
noncomputable def twoSpecies (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (ρ₀ ρ₁ : AbsoluteDensity d) : SpeciesFamily d where
  count := 2
  weight := fun s => if s.val = 0 then ε else 1 - ε
  weight_pos := fun s => by split_ifs <;> linarith
  weight_sum := by
    change ∑ s : Fin 2, (if s.val = 0 then ε else 1 - ε) = 1
    simp [Fin.sum_univ_two]
  density := fun s => if s.val = 0 then ρ₀ else ρ₁

theorem exists_small_weight (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (ρ : AbsoluteDensity d) :
    ∃ F : SpeciesFamily d, ∃ s, F.weight s = ε :=
  ⟨twoSpecies ε hε0 hε1 ρ ρ, ⟨0, Nat.two_pos⟩, by simp [twoSpecies]⟩

end DGPS.SpeciesFamily

namespace DGPS

end DGPS
