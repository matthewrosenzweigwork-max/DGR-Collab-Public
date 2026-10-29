import LeanResearch.PeriodicAttractiveLogGas.FiniteBoxPoincare

/-! Exact finite equivalence transport for the original unnormalized forms.
There are no analytic estimates or normalization assumptions in these identities. -/
noncomputable section
open scoped BigOperators
namespace PeriodicAttractiveLogGas.FiniteGraphTransport
open FiniteGraph FiniteEntropyLocalization FiniteBoxPoincare FibreEntropy

variable {α β : Type*} [Fintype α] [Fintype β]

omit [Fintype β] in
/-- The explicit filtered preimage supplies the membership correspondence below. -/
theorem filter_corresponds [DecidableEq α] [DecidableEq β] (e : α ≃ β) (B : Finset β) (x : α) :
    x ∈ Finset.univ.filter (fun x => e x ∈ B) ↔ e x ∈ B := by
  classical
  simp

theorem sum_eq (e : α ≃ β) (f : α → ℝ) (g : β → ℝ)
    (hf : ∀ x, g (e x) = f x) : (∑ x, f x) = ∑ y, g y :=
  Fintype.sum_equiv e f g (fun x => (hf x).symm)

theorem mean_eq (e : α ≃ β) (wα Fα : α → ℝ) (wβ Fβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x) (hF : ∀ x, Fβ (e x) = Fα x) :
    mean wα Fα = mean wβ Fβ := by
  apply sum_eq e
  intro x
  rw [hw, hF]

/-- Totalized finite entropy is preserved even for zero means or subprobabilities. -/
theorem finiteEntropy_eq (e : α ≃ β) (wα Fα : α → ℝ) (wβ Fβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x) (hF : ∀ x, Fβ (e x) = Fα x) :
    finiteEntropy wα Fα = finiteEntropy wβ Fβ := by
  have hm := mean_eq e wα Fα wβ Fβ hw hF
  unfold mean at hm
  unfold finiteEntropy
  rw [hm]
  congr 1
  apply sum_eq e
  intro x
  rw [hw, hF]

/-- The factor one half and all directed edges are preserved exactly. -/
theorem energy_eq (e : α ≃ β) (wα : α → ℝ) (wβ : β → ℝ)
    (rα : α → α → ℝ) (rβ : β → β → ℝ) (Fα : α → ℝ) (Fβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x)
    (hr : ∀ x y, rβ (e x) (e y) = rα x y) (hF : ∀ x, Fβ (e x) = Fα x) :
    energy wα rα Fα = energy wβ rβ Fβ := by
  unfold energy
  congr 1
  apply sum_eq e
  intro x
  symm
  apply sum_eq e
  intro y
  rw [hw, hr, hF, hF]

theorem outgoing_sum_eq (e : α ≃ β) (rα : α → α → ℝ) (rβ : β → β → ℝ)
    (hr : ∀ x y, rβ (e x) (e y) = rα x y) (x : α) :
    (∑ y, rα x y) = ∑ z, rβ (e x) z := sum_eq e _ _ (hr x)

theorem generator_eq (e : α ≃ β) (rα : α → α → ℝ) (rβ : β → β → ℝ)
    (Fα : α → ℝ) (Fβ : β → ℝ)
    (hr : ∀ x y, rβ (e x) (e y) = rα x y) (hF : ∀ x, Fβ (e x) = Fα x) (x : α) :
    generator rα Fα x = generator rβ Fβ (e x) := by
  apply sum_eq e
  intro y
  rw [hr, hF, hF]

theorem groundStatePotential_eq (e : α ≃ β) (rα : α → α → ℝ) (rβ : β → β → ℝ)
    (Vα : α → ℝ) (Vβ : β → ℝ)
    (hr : ∀ x y, rβ (e x) (e y) = rα x y) (hV : ∀ x, Vβ (e x) = Vα x) (x : α) :
    groundStatePotential rα Vα x = groundStatePotential rβ Vβ (e x) := by
  unfold groundStatePotential
  rw [generator_eq e rα rβ Vα Vβ hr hV, hV]


theorem sum_on_eq (e : α ≃ β) (Bα : Finset α) (Bβ : Finset β)
    (hB : ∀ x, x ∈ Bα ↔ e x ∈ Bβ) (f : α → ℝ) (g : β → ℝ)
    (hf : ∀ x, g (e x) = f x) : (∑ x ∈ Bα, f x) = ∑ y ∈ Bβ, g y := by
  classical
  have hh := sum_eq e (fun x => if x ∈ Bα then f x else 0)
    (fun y => if y ∈ Bβ then g y else 0) (fun x => by simp only [← hB x, hf x])
  have ha : (∑ x, if x ∈ Bα then f x else 0) = ∑ x ∈ Bα, f x := by
    rw [← Finset.sum_filter]
    simp
  have hb : (∑ y, if y ∈ Bβ then g y else 0) = ∑ y ∈ Bβ, g y := by
    rw [← Finset.sum_filter]
    simp
  rw [ha, hb] at hh
  exact hh

omit [Fintype α] [Fintype β] in
theorem restrictedWeight_eq (e : α ≃ β) (Bα : Finset α) (Bβ : Finset β)
    (hB : ∀ x, x ∈ Bα ↔ e x ∈ Bβ) (wα : α → ℝ) (wβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x) (x : α) :
    restrictedWeight wβ Bβ (e x) = restrictedWeight wα Bα x := by
  classical
  simp only [restrictedWeight, hB x, hw x]

theorem setMass_eq (e : α ≃ β) (Bα : Finset α) (Bβ : Finset β)
    (hB : ∀ x, x ∈ Bα ↔ e x ∈ Bβ) (wα : α → ℝ) (wβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x) : setMass wα Bα = setMass wβ Bβ :=
  sum_eq e _ _ (restrictedWeight_eq e Bα Bβ hB wα wβ hw)

/-- No nonzero-mass premise: the existing totalized conditional weights agree. -/
theorem conditionalWeight_eq (e : α ≃ β) (Bα : Finset α) (Bβ : Finset β)
    (hB : ∀ x, x ∈ Bα ↔ e x ∈ Bβ) (wα : α → ℝ) (wβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x) (x : α) :
    conditionalWeight wβ Bβ (e x) = conditionalWeight wα Bα x := by
  unfold conditionalWeight
  rw [setMass_eq e Bα Bβ hB wα wβ hw, restrictedWeight_eq e Bα Bβ hB wα wβ hw]

theorem conditional_mean_eq (e : α ≃ β) (Bα : Finset α) (Bβ : Finset β)
    (hB : ∀ x, x ∈ Bα ↔ e x ∈ Bβ) (wα Fα : α → ℝ) (wβ Fβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x) (hF : ∀ x, Fβ (e x) = Fα x) :
    mean (conditionalWeight wα Bα) Fα = mean (conditionalWeight wβ Bβ) Fβ :=
  mean_eq e _ _ _ _ (conditionalWeight_eq e Bα Bβ hB wα wβ hw) hF

theorem subset_variance_eq (e : α ≃ β) (Bα : Finset α) (Bβ : Finset β)
    (hB : ∀ x, x ∈ Bα ↔ e x ∈ Bβ) (wα Fα : α → ℝ) (wβ Fβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x) (hF : ∀ x, Fβ (e x) = Fα x) :
    (∑ x ∈ Bα, wα x*(Fα x-mean (conditionalWeight wα Bα) Fα)^2) =
      ∑ y ∈ Bβ, wβ y*(Fβ y-mean (conditionalWeight wβ Bβ) Fβ)^2 := by
  rw [conditional_mean_eq e Bα Bβ hB wα Fα wβ Fβ hw hF]
  apply sum_on_eq e Bα Bβ hB
  intro x
  rw [hw, hF]

omit [Fintype α] [Fintype β] in
theorem restrictedRates_eq (e : α ≃ β) (Bα : Finset α) (Bβ : Finset β)
    (hB : ∀ x, x ∈ Bα ↔ e x ∈ Bβ) (rα : α → α → ℝ) (rβ : β → β → ℝ)
    (hr : ∀ x y, rβ (e x) (e y) = rα x y) (x y : α) :
    restrictedRates rβ Bβ (e x) (e y) = restrictedRates rα Bα x y := by
  classical
  simp only [restrictedRates, hB x, hB y, hr x y]

theorem restricted_energy_eq (e : α ≃ β) (Bα : Finset α) (Bβ : Finset β)
    (hB : ∀ x, x ∈ Bα ↔ e x ∈ Bβ) (wα : α → ℝ) (wβ : β → ℝ)
    (rα : α → α → ℝ) (rβ : β → β → ℝ) (Fα : α → ℝ) (Fβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x)
    (hr : ∀ x y, rβ (e x) (e y) = rα x y) (hF : ∀ x, Fβ (e x) = Fα x) :
    energy (restrictedWeight wα Bα) (restrictedRates rα Bα) Fα =
      energy (restrictedWeight wβ Bβ) (restrictedRates rβ Bβ) Fβ :=
  energy_eq e _ _ _ _ Fα Fβ (restrictedWeight_eq e Bα Bβ hB wα wβ hw)
    (restrictedRates_eq e Bα Bβ hB rα rβ hr) hF

/-- A known internal Poincare inequality transfers with its identical constant
and exact conditional mean. No positivity or additional normalization is needed. -/
theorem internal_poincare_transport (e : α ≃ β) (Bα : Finset α) (Bβ : Finset β)
    (hB : ∀ x, x ∈ Bα ↔ e x ∈ Bβ) (wα : α → ℝ) (wβ : β → ℝ)
    (rα : α → α → ℝ) (rβ : β → β → ℝ) (Fα : α → ℝ) (Fβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x)
    (hr : ∀ x y, rβ (e x) (e y) = rα x y) (hF : ∀ x, Fβ (e x) = Fα x)
    (K : ℝ)
    (hPI : (∑ y ∈ Bβ, wβ y*(Fβ y-mean (conditionalWeight wβ Bβ) Fβ)^2) ≤
      K*energy (restrictedWeight wβ Bβ) (restrictedRates rβ Bβ) Fβ) :
    (∑ x ∈ Bα, wα x*(Fα x-mean (conditionalWeight wα Bα) Fα)^2) ≤
      K*energy (restrictedWeight wα Bα) (restrictedRates rα Bα) Fα := by
  rw [subset_variance_eq e Bα Bβ hB wα Fα wβ Fβ hw hF,
    restricted_energy_eq e Bα Bβ hB wα wβ rα rβ Fα Fβ hw hr hF]
  exact hPI

/-- The full unnormalized entropy inequality is unchanged by reindexing. -/
theorem entropy_energy_transport (e : α ≃ β) (wα : α → ℝ) (wβ : β → ℝ)
    (rα : α → α → ℝ) (rβ : β → β → ℝ) (Fα : α → ℝ) (Fβ : β → ℝ)
    (hw : ∀ x, wβ (e x) = wα x)
    (hr : ∀ x y, rβ (e x) (e y) = rα x y) (hF : ∀ x, Fβ (e x) = Fα x)
    (A B : ℝ)
    (hLSI : finiteEntropy wβ (fun y => Fβ y^2) ≤ A*energy wβ rβ Fβ + B*mean wβ (fun y => Fβ y^2)) :
    finiteEntropy wα (fun x => Fα x^2) ≤ A*energy wα rα Fα + B*mean wα (fun x => Fα x^2) := by
  have hsq : ∀ x, Fβ (e x)^2 = Fα x^2 := fun x => by rw [hF]
  rw [finiteEntropy_eq e wα (fun x => Fα x^2) wβ (fun y => Fβ y^2) hw hsq,
    energy_eq e wα wβ rα rβ Fα Fβ hw hr hF,
    mean_eq e wα (fun x => Fα x^2) wβ (fun y => Fβ y^2) hw hsq]
  exact hLSI

end PeriodicAttractiveLogGas.FiniteGraphTransport
