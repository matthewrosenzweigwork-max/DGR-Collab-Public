import DGPS.Examples.PolynomialSpeciesOptimizerAssembly

noncomputable section
namespace DGPS.Examples.PolynomialSpecies

/-- Two chart classes with law uniqueness within each class admit at most two
laws. The labels need not have any additional smoothness or choice coherence. -/
theorem three_laws_collision_of_two_classes
    {D L : Type*} (P : D → Prop) (law : D → L) (C : D → Fin 2 → Prop)
    (hcover : ∀ d, P d → ∃ j, C d j)
    (hunique : ∀ d e j, P d → P e → C d j → C e j → law d = law e) :
    ∀ d e f, P d → P e → P f →
      law d = law e ∨ law d = law f ∨ law e = law f := by
  intro d e f hd he hf
  obtain ⟨i, hi⟩ := hcover d hd
  obtain ⟨j, hj⟩ := hcover e he
  obtain ⟨k, hk⟩ := hcover f hf
  have hpigeon : i = j ∨ i = k ∨ j = k := by omega
  rcases hpigeon with hij | hik | hjk
  · subst j
    exact Or.inl (hunique d e i hd he hi hj)
  · subst k
    exact Or.inr (Or.inl (hunique d f i hd hf hi hk))
  · subst k
    exact Or.inr (Or.inr (hunique e f j he hf hj hk))

/-- Attainment and a law-distinct preserving reflection turn the at-most-two
statement into an exact classification. No critical point is declared to be a
minimizer by this argument. -/
theorem exactly_two_laws_of_three_collision
    {D L : Type*} (P : D → Prop) (law : D → L) (R : D → D)
    (hex : ∃ d, P d) (hR : ∀ d, P d → P (R d))
    (hneq : ∀ d, P d → law d ≠ law (R d))
    (hthree : ∀ d e f, P d → P e → P f →
      law d = law e ∨ law d = law f ∨ law e = law f) :
    ∃ d e, P d ∧ P e ∧ law d ≠ law e ∧ e = R d ∧
      ∀ f, P f → law f = law d ∨ law f = law e := by
  obtain ⟨d, hd⟩ := hex
  refine ⟨d, R d, hd, hR d hd, hneq d hd, rfl, ?_⟩
  intro f hf
  rcases hthree d (R d) f hd (hR d hd) hf with he | he | he
  · exact False.elim (hneq d hd he)
  · exact Or.inl he.symm
  · exact Or.inr he.symm

end DGPS.Examples.PolynomialSpecies
