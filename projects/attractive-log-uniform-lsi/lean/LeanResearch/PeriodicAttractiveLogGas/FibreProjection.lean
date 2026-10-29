import LeanResearch.PeriodicAttractiveLogGas.DiscreteOccupationIdentities

/-! Source lines 2790–2839: the actual uniform occupation-fibre projection
on the outer label graph, with weighted L2 and energy orthogonality.
No multislice functional inequality or label Poincare conclusion is assumed. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace PeriodicAttractiveLogGas.FibreProjection

open MeshCells LabelOccupations CellRestrictions LabelExchangeability OccupationProbability
open DiscreteOccupationIdentities

variable {J N : ℕ} {t : ℝ}

abbrev Fibre (m : OccupationState J N t) := {η : LabelState J N t // profile η = m}

@[simp] theorem profile_fibre {m : OccupationState J N t} (η : Fibre m) : profile η.val = m :=
  η.property

theorem fibre_card_pos (m : OccupationState J N t) : 0 < Fintype.card (Fibre m) := by
  let : Nonempty (Fibre m) := ⟨⟨labelOfState m, profile_labelOfState m⟩⟩
  exact Fintype.card_pos

/-- Literal uniform average over the actual occupation fibre. -/
def fibreAverage (F : LabelState J N t → ℝ) (m : OccupationState J N t) : ℝ :=
  (∑ η : Fibre m, F η.val) / Fintype.card (Fibre m)

def projection (F : LabelState J N t → ℝ) (η : LabelState J N t) : ℝ :=
  fibreAverage F (profile η)

def remainder (F : LabelState J N t → ℝ) (η : LabelState J N t) : ℝ :=
  F η - projection F η

theorem sum_by_fibres (F : LabelState J N t → ℝ) :
    (∑ η, F η) = ∑ m, ∑ η : Fibre m, F η.val := by
  have hh := Equiv.sum_comp (Equiv.sigmaFiberEquiv (profile : LabelState J N t → OccupationState J N t)) F
  rw [Fintype.sum_sigma] at hh
  exact hh.symm

theorem fibreAverage_profile (F : OccupationState J N t → ℝ) (m : OccupationState J N t) :
    fibreAverage (fun η => F (profile η)) m = F m := by
  have hc : (Fintype.card (Fibre m) : ℝ) ≠ 0 := by exact_mod_cast (fibre_card_pos m).ne'
  simp only [fibreAverage, profile_fibre, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem projection_idempotent (F : LabelState J N t → ℝ) :
    projection (projection F) = projection F := by
  funext η
  exact fibreAverage_profile (fibreAverage F) (profile η)

theorem sum_fibre_remainder (F : LabelState J N t → ℝ) (m : OccupationState J N t) :
    (∑ η : Fibre m, remainder F η.val) = 0 := by
  have hc : (Fintype.card (Fibre m) : ℝ) ≠ 0 := by exact_mod_cast (fibre_card_pos m).ne'
  have he : (fun η : Fibre m => remainder F η.val) =
      fun η => F η.val - fibreAverage F m := by
    funext η
    simp only [remainder, projection, profile_fibre]
  rw [he, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold fibreAverage
  field_simp
  ring

theorem projection_remainder (F : LabelState J N t → ℝ) :
    projection (remainder F) = 0 := by
  funext η
  simp only [projection, fibreAverage, sum_fibre_remainder, zero_div, Pi.zero_apply]

/-- Every profile-dependent coefficient is orthogonal to the actual
zero-mean fibre remainder, before imposing any probability normalization. -/
theorem weighted_remainder_sum (F : LabelState J N t → ℝ) (A : OccupationState J N t → ℝ) :
    (∑ η, A (profile η) * remainder F η) = 0 := by
  rw [sum_by_fibres]
  simp only [profile_fibre, ← Finset.mul_sum, sum_fibre_remainder, mul_zero, Finset.sum_const_zero]

/-- The squared norm identity on any union of complete occupation classes,
with the actual unconditioned label weights and an arbitrary real center. -/
theorem weighted_l2_decomposition (hJ : 0 < J) (β : ℝ)
    (F : LabelState J N t → ℝ) (c : ℝ) (S : Finset (OccupationState J N t)) :
    (∑ η, if profile η ∈ S then labelWeight hJ β η * (F η - c) ^ 2 else 0) =
      (∑ η, if profile η ∈ S then labelWeight hJ β η * (projection F η - c) ^ 2 else 0) +
      ∑ η, if profile η ∈ S then labelWeight hJ β η * remainder F η ^ 2 else 0 := by
  classical
  have hz := weighted_remainder_sum F (fun m => if m ∈ S then 2 * qWeight hJ β m *
    (fibreAverage F m - c) else 0)
  have he : (∑ η, if profile η ∈ S then labelWeight hJ β η * (F η - c) ^ 2 else 0) =
      (∑ η, if profile η ∈ S then labelWeight hJ β η * (projection F η - c) ^ 2 else 0) +
      (∑ η, if profile η ∈ S then labelWeight hJ β η * remainder F η ^ 2 else 0) +
      ∑ η, (if profile η ∈ S then 2 * qWeight hJ β (profile η) *
        (fibreAverage F (profile η) - c) else 0) * remainder F η := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro η _
    rw [labelWeight_eq_qWeight]
    by_cases hs : profile η ∈ S
    · simp only [ite_eq_left hs, projection, remainder]
      ring
    · simp only [ite_eq_right hs, zero_mul, add_zero]
  rw [he, hz, add_zero]

/-- Actual particle permutation on the capped outer state space. -/
def permutedLabel (σ : Equiv.Perm (Fin N)) (η : LabelState J N t) : LabelState J N t :=
  ⟨η.val ∘ σ, by
    intro a
    rw [occupation_permute]
    exact η.property a⟩

def particlePermutation (σ : Equiv.Perm (Fin N)) : LabelState J N t ≃ LabelState J N t where
  toFun := permutedLabel σ
  invFun := permutedLabel σ.symm
  left_inv η := by apply Subtype.ext; funext i; simp [permutedLabel]
  right_inv η := by apply Subtype.ext; funext i; simp [permutedLabel]

@[simp] theorem profile_permutedLabel (σ : Equiv.Perm (Fin N)) (η : LabelState J N t) :
    profile (permutedLabel σ η) = profile η := by
  apply Subtype.ext
  exact occupation_permute σ η.val

theorem labelWeight_permutedLabel (hJ : 0 < J) (β : ℝ)
    (σ : Equiv.Perm (Fin N)) (η : LabelState J N t) :
    labelWeight hJ β (permutedLabel σ η) = labelWeight hJ β η :=
  congrArg ENNReal.toReal (labelProbability_permute hJ σ η.val β)

@[simp] theorem particlePermutation_apply (σ : Equiv.Perm (Fin N)) (η : LabelState J N t) :
    particlePermutation σ η = permutedLabel σ η := rfl

@[simp] theorem permutedLabel_symm (σ : Equiv.Perm (Fin N)) (η : LabelState J N t) :
    permutedLabel σ.symm (permutedLabel σ η) = η := (particlePermutation σ).left_inv η

@[simp] theorem permutedLabel_apply_symm (σ : Equiv.Perm (Fin N)) (η : LabelState J N t) :
    permutedLabel σ (permutedLabel σ.symm η) = η := (particlePermutation σ).right_inv η

/-- Each actual permutation fibre has the factorial stabilizer cardinality.
This proves the orbit multiplicity used in averaging, including zero counts. -/
theorem card_permutation_fibre (η ζ : LabelState J N t) (h : profile ζ = profile η) :
    Fintype.card {σ : Equiv.Perm (Fin N) // permutedLabel σ η = ζ} =
      ∏ a : MeshIndex J, (occupation η.val a).factorial := by
  classical
  have hp : occupation η.val = occupation ζ.val := (congrArg Subtype.val h).symm
  obtain ⟨τ, hτ⟩ := exists_permutation_of_occupation_eq hp
  let e : {σ : Equiv.Perm (Fin N) // permutedLabel σ η = ζ} ≃
      {σ : Equiv.Perm (Fin N) // η.val ∘ σ = ζ.val} :=
    Equiv.subtypeEquivRight fun σ => Subtype.ext_iff
  rw [Fintype.card_congr (e.trans (permutationFiberEquiv η.val ζ.val τ hτ)),
    DomMulAct.stabilizer_card]
  apply Finset.prod_congr rfl
  intro a _
  congr 1
  simp [occupation, Fintype.card_subtype]

def orbitMap (η : LabelState J N t) (σ : Equiv.Perm (Fin N)) : Fibre (profile η) :=
  ⟨permutedLabel σ η, profile_permutedLabel σ η⟩

theorem orbitMap_fibre_card (η : LabelState J N t) (ζ : Fibre (profile η)) :
    Fintype.card {σ : Equiv.Perm (Fin N) // orbitMap η σ = ζ} =
      ∏ a : MeshIndex J, (occupation η.val a).factorial := by
  classical
  let e : {σ : Equiv.Perm (Fin N) // orbitMap η σ = ζ} ≃
      {σ : Equiv.Perm (Fin N) // permutedLabel σ η = ζ.val} :=
    Equiv.subtypeEquivRight fun σ => Subtype.ext_iff
  rw [Fintype.card_congr e]
  exact card_permutation_fibre η ζ.val ζ.property

theorem sum_permutations (F : LabelState J N t → ℝ) (η : LabelState J N t) :
    (∑ σ : Equiv.Perm (Fin N), F (permutedLabel σ η)) =
      ((∏ a : MeshIndex J, (occupation η.val a).factorial : ℕ) : ℝ) *
        ∑ ζ : Fibre (profile η), F ζ.val := by
  classical
  have hh := Equiv.sum_comp (Equiv.sigmaFiberEquiv (orbitMap η))
    (fun σ => F (permutedLabel σ η))
  rw [Fintype.sum_sigma] at hh
  rw [← hh, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ζ _
  have he (σ : {σ : Equiv.Perm (Fin N) // orbitMap η σ = ζ}) :
      F (permutedLabel σ.val η) = F ζ.val :=
    congrArg F (congrArg Subtype.val σ.property)
  change (∑ σ : {σ : Equiv.Perm (Fin N) // orbitMap η σ = ζ},
    F (permutedLabel σ.val η)) = _
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, orbitMap_fibre_card]

/-- Uniform averaging over the literal occupation fibre is exactly finite
particle-permutation averaging, by actual cardinalities and exchangeability. -/
theorem projection_eq_permutation_average (F : LabelState J N t → ℝ)
    (η : LabelState J N t) :
    projection F η = (∑ σ : Equiv.Perm (Fin N), F (permutedLabel σ η)) /
      Fintype.card (Equiv.Perm (Fin N)) := by
  have hf : (Fintype.card (Fibre (profile η)) : ℝ) ≠ 0 := by
    exact_mod_cast (fibre_card_pos (profile η)).ne'
  have hp : (∏ a : MeshIndex J, (occupation η.val a).factorial : ℕ) ≠ 0 :=
    (Finset.prod_pos fun _ _ => Nat.factorial_pos _).ne'
  have hp' : ((∏ a : MeshIndex J, (occupation η.val a).factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hp
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ) =
      (Fintype.card (Fibre (profile η)) : ℝ) *
        ((∏ a : MeshIndex J, (occupation η.val a).factorial : ℕ) : ℝ) := by
    rw [Fintype.card_perm, Fintype.card_fin, card_profile_fiber]
    exact_mod_cast (multiplicity_mul_factorials (profile η)).symm
  rw [sum_permutations, hc]
  unfold projection fibreAverage
  field_simp

theorem labelAdjacent_permuted (hJ : 0 < J) (σ : Equiv.Perm (Fin N))
    {η ζ : LabelState J N t} (h : LabelAdjacent hJ η ζ) :
    LabelAdjacent hJ (permutedLabel σ η) (permutedLabel σ ζ) := by
  classical
  obtain ⟨i, he, hu⟩ := h
  refine ⟨σ.symm i, ?_, ?_⟩
  · simpa only [permutedLabel, Function.comp_apply, Equiv.apply_symm_apply] using he
  · funext k
    by_cases hk : k = σ.symm i
    · subst k
      simp only [Function.update_self]
    · have hki : σ k ≠ i := fun hh => hk (σ.injective (hh.trans (σ.apply_symm_apply i).symm))
      have hh := congrFun hu (σ k)
      simpa only [Function.update_of_ne hk, permutedLabel, Function.comp_apply,
        Function.update_of_ne hki] using hh

theorem labelAdjacent_permuted_iff (hJ : 0 < J) (σ : Equiv.Perm (Fin N))
    (η ζ : LabelState J N t) :
    LabelAdjacent hJ (permutedLabel σ η) (permutedLabel σ ζ) ↔ LabelAdjacent hJ η ζ := by
  constructor
  · intro h
    simpa only [permutedLabel_symm] using labelAdjacent_permuted hJ σ.symm h
  · exact fun h => labelAdjacent_permuted hJ σ h

/-- Permuting particles preserves the actual outer graph and each original
conductance, not merely an abstract comparison graph. -/
theorem labelConductance_permutedLabel (hJ : 0 < J) (β : ℝ)
    (σ : Equiv.Perm (Fin N)) (η ζ : LabelState J N t) :
    labelConductance hJ β (permutedLabel σ η) (permutedLabel σ ζ) = labelConductance hJ β η ζ := by
  classical
  simp only [labelConductance, labelAdjacent_permuted_iff, labelWeight_permutedLabel]

/-- Polarization of the actual outer label energy. -/
def bilinear (hJ : 0 < J) (β : ℝ) (F H : LabelState J N t → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ η, ∑ ζ, labelConductance hJ β η ζ *
    (F ζ - F η) * (H ζ - H η)

theorem bilinear_self (hJ : 0 < J) (β : ℝ) (F : LabelState J N t → ℝ) :
    bilinear hJ β F F = labelEnergy hJ β F := by
  rw [labelEnergy_eq_directed]
  simp only [bilinear, FiniteGraph.energy, labelWeight_mul_rate, pow_two, mul_assoc]

theorem bilinear_symm (hJ : 0 < J) (β : ℝ) (F H : LabelState J N t → ℝ) :
    bilinear hJ β F H = bilinear hJ β H F := by
  unfold bilinear
  congr 1
  apply Finset.sum_congr rfl
  intro η _
  apply Finset.sum_congr rfl
  intro ζ _
  ring

theorem bilinear_add_right (hJ : 0 < J) (β : ℝ) (F H K : LabelState J N t → ℝ) :
    bilinear hJ β F (H + K) = bilinear hJ β F H + bilinear hJ β F K := by
  simp only [bilinear, Pi.add_apply]
  simp_rw [show ∀ η ζ, H ζ + K ζ - (H η + K η) =
    (H ζ - H η) + (K ζ - K η) by intros; ring]
  simp only [mul_add, Finset.sum_add_distrib]

theorem bilinear_add_left (hJ : 0 < J) (β : ℝ) (F H K : LabelState J N t → ℝ) :
    bilinear hJ β (F + H) K = bilinear hJ β F K + bilinear hJ β H K := by
  rw [bilinear_symm, bilinear_add_right, bilinear_symm hJ β K F, bilinear_symm hJ β K H]

theorem bilinear_smul_right (hJ : 0 < J) (β : ℝ) (F H : LabelState J N t → ℝ) (c : ℝ) :
    bilinear hJ β F (fun η => c * H η) = c * bilinear hJ β F H := by
  simp only [bilinear, ← mul_sub]
  simp_rw [show ∀ η ζ, labelConductance hJ β η ζ * (F ζ - F η) *
    (c * (H ζ - H η)) = c * (labelConductance hJ β η ζ * (F ζ - F η) *
      (H ζ - H η)) by intros; ring]
  simp only [← Finset.mul_sum]
  ring

theorem bilinear_sum_right {ι : Type*} [Fintype ι] (hJ : 0 < J) (β : ℝ)
    (F : LabelState J N t → ℝ) (H : ι → LabelState J N t → ℝ) :
    bilinear hJ β F (fun η => ∑ i, H i η) = ∑ i, bilinear hJ β F (H i) := by
  simp only [bilinear, ← Finset.sum_sub_distrib, Finset.mul_sum]
  let T (η ζ : LabelState J N t) (i : ι) : ℝ := (1 / 2 : ℝ) *
    (labelConductance hJ β η ζ * (F ζ - F η) * (H i ζ - H i η))
  change (∑ η, ∑ ζ, ∑ i, T η ζ i) = ∑ i, ∑ η, ∑ ζ, T η ζ i
  calc
    (∑ η, ∑ ζ, ∑ i, T η ζ i) = ∑ η, ∑ i, ∑ ζ, T η ζ i := by
      apply Finset.sum_congr rfl
      intro η _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Actual simultaneous particle permutation preserves the polarized form. -/
theorem bilinear_permuted (hJ : 0 < J) (β : ℝ) (F H : LabelState J N t → ℝ)
    (σ : Equiv.Perm (Fin N)) :
    bilinear hJ β (fun η => F (permutedLabel σ η))
      (fun η => H (permutedLabel σ η)) = bilinear hJ β F H := by
  have hh := Equiv.sum_comp ((particlePermutation σ).prodCongr (particlePermutation σ))
    (fun z : LabelState J N t × LabelState J N t =>
      labelConductance hJ β z.1 z.2 * (F z.2 - F z.1) * (H z.2 - H z.1))
  simp only [Fintype.sum_prod_type, Equiv.prodCongr_apply, Prod.map, particlePermutation_apply,
    labelConductance_permutedLabel] at hh
  exact congrArg (fun x : ℝ => (1 / 2 : ℝ) * x) hh

theorem bilinear_projection_right (hJ : 0 < J) (β : ℝ) (F H : LabelState J N t → ℝ) :
    bilinear hJ β F (projection H) =
      (∑ σ : Equiv.Perm (Fin N), bilinear hJ β F (fun η => H (permutedLabel σ η))) /
        Fintype.card (Equiv.Perm (Fin N)) := by
  have he : projection H = fun η => (Fintype.card (Equiv.Perm (Fin N)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), H (permutedLabel σ η) := by
    funext η
    rw [projection_eq_permutation_average, div_eq_mul_inv, mul_comm]
  rw [he, bilinear_smul_right, bilinear_sum_right, div_eq_mul_inv, mul_comm]

/-- The projection is constant on the genuine particle-permutation orbits. -/
@[simp] theorem projection_permuted (F : LabelState J N t → ℝ)
    (σ : Equiv.Perm (Fin N)) (η : LabelState J N t) :
    projection F (permutedLabel σ η) = projection F η := by
  simp only [projection, profile_permutedLabel]

theorem bilinear_projected_permuted (hJ : 0 < J) (β : ℝ)
    (F H : LabelState J N t → ℝ) (σ : Equiv.Perm (Fin N)) :
    bilinear hJ β (projection F) (fun η => H (permutedLabel σ η)) =
      bilinear hJ β (projection F) H := by
  simpa only [projection_permuted] using bilinear_permuted hJ β (projection F) H σ

theorem bilinear_projected_projection (hJ : 0 < J) (β : ℝ)
    (F H : LabelState J N t → ℝ) :
    bilinear hJ β (projection F) (projection H) = bilinear hJ β (projection F) H := by
  have hc : (Fintype.card (Equiv.Perm (Fin N)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Equiv.Perm (Fin N))).ne'
  rw [bilinear_projection_right]
  simp only [bilinear_projected_permuted, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Source self-adjointness of the uniform fibre projection in the actual
outer energy form, derived from the finite particle-permutation average. -/
theorem bilinear_projection_selfadjoint (hJ : 0 < J) (β : ℝ)
    (F H : LabelState J N t → ℝ) :
    bilinear hJ β (projection F) H = bilinear hJ β F (projection H) := by
  rw [← bilinear_projected_projection hJ β F H, bilinear_symm,
    bilinear_projected_projection, bilinear_symm]

theorem bilinear_projection_remainder (hJ : 0 < J) (β : ℝ)
    (F : LabelState J N t → ℝ) :
    bilinear hJ β (projection F) (remainder F) = 0 := by
  rw [bilinear_projection_selfadjoint, projection_remainder]
  simp only [bilinear, Pi.zero_apply, sub_self, mul_zero, Finset.sum_const_zero]

/-- Exact source decomposition on the full original outer graph. -/
theorem labelEnergy_decomposition (hJ : 0 < J) (β : ℝ)
    (F : LabelState J N t → ℝ) :
    labelEnergy hJ β F = labelEnergy hJ β (projection F) + labelEnergy hJ β (remainder F) := by
  have he : F = projection F + remainder F := by funext η; simp [remainder]
  calc
    labelEnergy hJ β F = bilinear hJ β (projection F + remainder F)
        (projection F + remainder F) := by rw [← he, bilinear_self]
    _ = labelEnergy hJ β (projection F) + labelEnergy hJ β (remainder F) := by
      rw [bilinear_add_right, bilinear_add_left, bilinear_add_left,
        bilinear_projection_remainder, bilinear_symm hJ β (remainder F) (projection F),
        bilinear_projection_remainder, zero_add, add_zero, bilinear_self, bilinear_self]

/-- Whole-graph weighted L2 orthogonality, retaining an arbitrary real center. -/
theorem weighted_l2_decomposition_univ (hJ : 0 < J) (β : ℝ)
    (F : LabelState J N t → ℝ) (c : ℝ) :
    (∑ η, labelWeight hJ β η * (F η - c) ^ 2) =
      (∑ η, labelWeight hJ β η * (projection F η - c) ^ 2) +
      ∑ η, labelWeight hJ β η * remainder F η ^ 2 := by
  simpa only [Finset.mem_univ, ite_true] using weighted_l2_decomposition hJ β F c Finset.univ

end PeriodicAttractiveLogGas.FibreProjection
