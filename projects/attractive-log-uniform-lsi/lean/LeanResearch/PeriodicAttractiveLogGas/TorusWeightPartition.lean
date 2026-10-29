import LeanResearch.PeriodicAttractiveLogGas.CubeProbability
import LeanResearch.PeriodicAttractiveLogGas.SmallCubeGeometry

/-! Complete torus pair products split into their two internal products
and their cross product, retaining the original unordered-pair convention. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace PeriodicAttractiveLogGas.TorusWeightPartition

def restrictedWeight (k : ℕ) (a : ℝ) (S : Finset (Fin k)) (X : Configuration k) : ℝ :=
  ∏ ij ∈ planarRestrictedPairs k S, torusEuclideanDist (X ij.1) (X ij.2) ^ (-a)

def crossWeight (k : ℕ) (a : ℝ) (S : Finset (Fin k)) (X : Configuration k) : ℝ :=
  ∏ ij ∈ planarCrossPairs k S, torusEuclideanDist (X ij.1) (X ij.2) ^ (-a)

theorem restrictedWeight_nonneg (k : ℕ) (a : ℝ) (S : Finset (Fin k)) (X : Configuration k) :
    0 ≤ restrictedWeight k a S X :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (torusEuclideanDist_nonneg _ _) _

theorem crossWeight_nonneg (k : ℕ) (a : ℝ) (S : Finset (Fin k)) (X : Configuration k) :
    0 ≤ crossWeight k a S X :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (torusEuclideanDist_nonneg _ _) _

theorem measurable_restrictedWeight (k : ℕ) (a : ℝ) (S : Finset (Fin k)) :
    Measurable (restrictedWeight k a S) := by
  unfold restrictedWeight
  apply Finset.measurable_prod
  intro ij _
  exact (measurable_torusEuclideanNorm.comp
    ((measurable_pi_apply ij.1).sub (measurable_pi_apply ij.2))).pow_const (-a)

theorem weight_partition (k : ℕ) (a : ℝ) (S : Finset (Fin k))
    (w : Fin k → Torus) :
    torusPairWeight k a w =
      restrictedWeight k a S w * restrictedWeight k a Sᶜ w *
        crossWeight k a S w := by
  have hcover : planarOrderedPairs k =
      (planarRestrictedPairs k S ∪ planarRestrictedPairs k Sᶜ) ∪ planarCrossPairs k S := by
    ext ij
    simp only [Finset.mem_union, mem_planarOrderedPairs, mem_planarRestrictedPairs,
      mem_planarCrossPairs, Finset.mem_compl]
    tauto
  have hwithin : Disjoint (planarRestrictedPairs k S) (planarRestrictedPairs k Sᶜ) := by
    apply Finset.disjoint_left.mpr
    intro ij hi hj
    have h₁ := ((mem_planarRestrictedPairs S ij).mp hi).2.1
    have h₂ := ((mem_planarRestrictedPairs Sᶜ ij).mp hj).2.1
    exact (Finset.mem_compl.mp h₂) h₁
  have hcross : Disjoint (planarRestrictedPairs k S ∪ planarRestrictedPairs k Sᶜ)
      (planarCrossPairs k S) := by
    apply Finset.disjoint_left.mpr
    intro ij hi hj
    simp only [Finset.mem_union, mem_planarRestrictedPairs, mem_planarCrossPairs,
      Finset.mem_compl] at hi hj
    tauto
  unfold torusPairWeight restrictedWeight crossWeight
  rw [hcover, Finset.prod_union hcross, Finset.prod_union hwithin]

theorem restricted_reindex {k m : ℕ} (a : ℝ) (S : Finset (Fin k))
    (hS : S.card = m) (w : Fin k → Torus) :
    restrictedWeight k a S w =
      torusPairWeight m a (fun i ↦ w (S.orderEmbOfFin hS i)) := by
  let e := S.orderEmbOfFin hS
  symm
  unfold torusPairWeight restrictedWeight
  apply Finset.prod_bij (fun ij _ ↦ (e ij.1, e ij.2))
  · intro ij hij
    exact (mem_planarRestrictedPairs S _).mpr
      ⟨e.strictMono ((mem_planarOrderedPairs ij).mp hij),
        S.orderEmbOfFin_mem hS ij.1, S.orderEmbOfFin_mem hS ij.2⟩
  · intro ij hij pq hpq heq
    apply Prod.ext
    · exact e.injective (congrArg Prod.fst heq)
    · exact e.injective (congrArg Prod.snd heq)
  · intro ij hij
    rcases (mem_planarRestrictedPairs S ij).mp hij with ⟨hlt, hi, hj⟩
    obtain ⟨i, hi'⟩ := (S.orderIsoOfFin hS).surjective ⟨ij.1, hi⟩
    obtain ⟨j, hj'⟩ := (S.orderIsoOfFin hS).surjective ⟨ij.2, hj⟩
    have hei : e i = ij.1 := congrArg Subtype.val hi'
    have hej : e j = ij.2 := congrArg Subtype.val hj'
    refine ⟨(i, j), (mem_planarOrderedPairs _).mpr ?_, ?_⟩
    · exact e.lt_iff_lt.mp (by simpa only [hei, hej] using hlt)
    · exact Prod.ext hei hej
  · intro ij hij
    rfl



open CubeProbability

/-- Exact independence of the two internal products under the original
product cube law. The coordinate split retains both original centers. -/
theorem integral_restricted_product {k : ℕ} (a : ℝ) (S : Finset (Fin k))
    (c : Fin k → PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ X, restrictedWeight k a S (planarConfigurationQuotient k X) *
      restrictedWeight k a Sᶜ (planarConfigurationQuotient k X) ∂productLaw k c ℓ) =
      (∫ X, torusPairWeight S.card a (planarConfigurationQuotient S.card X)
        ∂productLaw S.card (fun i => c (S.orderEmbOfFin rfl i)) ℓ) *
      (∫ X, torusPairWeight Sᶜ.card a (planarConfigurationQuotient Sᶜ.card X)
        ∂productLaw Sᶜ.card (fun i => c (Sᶜ.orderEmbOfFin rfl i)) ℓ) := by
  have hpoint (X : Fin k → PlanarSpace) :
      restrictedWeight k a S (planarConfigurationQuotient k X) *
        restrictedWeight k a Sᶜ (planarConfigurationQuotient k X) =
      torusPairWeight S.card a (planarConfigurationQuotient S.card (clusterCoordinateSplit S X).1) *
        torusPairWeight Sᶜ.card a (planarConfigurationQuotient Sᶜ.card (clusterCoordinateSplit S X).2) := by
    rw [restricted_reindex a S rfl, restricted_reindex a Sᶜ rfl]
    rfl
  letI := productLaw_probability S.card (fun i => c (S.orderEmbOfFin rfl i)) hℓ
  letI := productLaw_probability Sᶜ.card (fun i => c (Sᶜ.orderEmbOfFin rfl i)) hℓ
  calc
    _ = ∫ X, torusPairWeight S.card a (planarConfigurationQuotient S.card (clusterCoordinateSplit S X).1) *
        torusPairWeight Sᶜ.card a (planarConfigurationQuotient Sᶜ.card (clusterCoordinateSplit S X).2)
          ∂productLaw k c ℓ := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ p, torusPairWeight S.card a (planarConfigurationQuotient S.card p.1) *
        torusPairWeight Sᶜ.card a (planarConfigurationQuotient Sᶜ.card p.2)
          ∂(productLaw S.card (fun i => c (S.orderEmbOfFin rfl i)) ℓ).prod
            (productLaw Sᶜ.card (fun i => c (Sᶜ.orderEmbOfFin rfl i)) ℓ) := by
      simpa only [] using! (split_productLaw S c hℓ).integral_comp'
        (fun p : (Fin S.card → PlanarSpace) × (Fin Sᶜ.card → PlanarSpace) =>
          torusPairWeight S.card a (planarConfigurationQuotient S.card p.1) *
            torusPairWeight Sᶜ.card a (planarConfigurationQuotient Sᶜ.card p.2))
    _ = _ := by
      simpa only [] using! (integral_prod_mul
        (μ := productLaw S.card (fun i => c (S.orderEmbOfFin rfl i)) ℓ)
        (ν := productLaw Sᶜ.card (fun i => c (Sᶜ.orderEmbOfFin rfl i)) ℓ)
        (fun X : Fin S.card → PlanarSpace =>
          torusPairWeight S.card a (planarConfigurationQuotient S.card X))
        (fun X : Fin Sᶜ.card → PlanarSpace =>
          torusPairWeight Sᶜ.card a (planarConfigurationQuotient Sᶜ.card X)))

theorem subcritical_of_le {k m : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hsub : a * (k : ℝ) < 4) (hm : m ≤ k) : a * (m : ℝ) < 4 :=
  (mul_le_mul_of_nonneg_left (by exact_mod_cast hm) ha).trans_lt hsub

/-- The two internal factors are genuinely integrable, not merely objects
for which the totalized Bochner-integral product identity can be written. -/
theorem integrable_restricted_product {k : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hsub : a * (k : ℝ) < 4) (S : Finset (Fin k)) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (c : Fin k → PlanarSpace) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Integrable (fun X => restrictedWeight k a S (planarConfigurationQuotient k X) *
      restrictedWeight k a Sᶜ (planarConfigurationQuotient k X)) (productLaw k c ℓ) := by
  letI := productLaw_probability S.card (fun i => c (S.orderEmbOfFin rfl i)) hℓ
  letI := productLaw_probability Sᶜ.card (fun i => c (Sᶜ.orderEmbOfFin rfl i)) hℓ
  have hA := integrable_torusWeight_productLaw S.card hS.card_pos
    (fun i => c (S.orderEmbOfFin rfl i)) ha
    (subcritical_of_le ha hsub (by simpa only [Fintype.card_fin] using S.card_le_univ)) hℓ
  have hB := integrable_torusWeight_productLaw Sᶜ.card hSc.card_pos
    (fun i => c (Sᶜ.orderEmbOfFin rfl i)) ha
    (subcritical_of_le ha hsub (by simpa only [Fintype.card_fin] using Sᶜ.card_le_univ)) hℓ
  have hh := (split_productLaw S c hℓ).integrable_comp_of_integrable (hA.mul_prod hB)
  apply hh.congr
  filter_upwards [] with X
  rw [restricted_reindex a S rfl, restricted_reindex a Sᶜ rfl]
  rfl

/-- Comparison of two positive distances before taking their negative
powers. This includes the zero-exponent endpoint. -/
theorem negative_power_le_of_mul_bound {a x y K : ℝ} (ha : 0 ≤ a)
    (hx : 0 < x) (hy : 0 < y) (hK : 0 < K) (hxy : y ≤ K * x) :
    x ^ (-a) ≤ K ^ a * y ^ (-a) := by
  have hh := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hy hxy (neg_nonpos.mpr ha))
    (Real.rpow_nonneg hK.le a)
  calc
    x ^ (-a) = K ^ a * (K * x) ^ (-a) := by
      rw [Real.mul_rpow hK.le hx.le, ← mul_assoc, ← Real.rpow_add hK,
        add_neg_cancel, Real.rpow_zero, one_mul]
    _ ≤ _ := hh

/-- Every cross pair incurs at most one common multiplicative factor.
The original cross-pair count, not a doubled directed count, is used. -/
theorem crossWeight_comparison {k : ℕ} {a D : ℝ} (ha : 0 ≤ a)
    (S : Finset (Fin k)) (X Y : Configuration k) (hD : (3 : ℝ) ^ a ≤ D)
    (hX : ∀ ij ∈ planarCrossPairs k S, 0 < torusEuclideanDist (X ij.1) (X ij.2))
    (hY : ∀ ij ∈ planarCrossPairs k S, 0 < torusEuclideanDist (Y ij.1) (Y ij.2))
    (hxy : ∀ ij ∈ planarCrossPairs k S,
      torusEuclideanDist (Y ij.1) (Y ij.2) ≤ 3 * torusEuclideanDist (X ij.1) (X ij.2)) :
    crossWeight k a S X ≤ D ^ (S.card * Sᶜ.card) * crossWeight k a S Y := by
  calc
    _ ≤ ∏ ij ∈ planarCrossPairs k S, D * torusEuclideanDist (Y ij.1) (Y ij.2) ^ (-a) := by
      apply Finset.prod_le_prod₀ (fun _ _ => Real.rpow_nonneg (torusEuclideanDist_nonneg _ _) _)
      intro ij hij
      exact (negative_power_le_of_mul_bound ha (hX ij hij) (hY ij hij) (by norm_num) (hxy ij hij)).trans
        (mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg (torusEuclideanDist_nonneg _ _) _))
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, card_planarCrossPairs]
      rfl

end PeriodicAttractiveLogGas.TorusWeightPartition
