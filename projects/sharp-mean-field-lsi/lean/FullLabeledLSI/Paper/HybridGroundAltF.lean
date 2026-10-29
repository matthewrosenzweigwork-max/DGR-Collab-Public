import FullLabeledLSI.Paper.HybridGroundAltE

/-!
# Hybrid inequality (7.17), alternative route, part F: the energy identity

`∫ (Ex0 + Σ_k λ_k (∂_k a)²) dW = Σ_j (Σ_i λ_{j_i}) c_j²` for `a = Σ_j c_j X_j(x) Y_j(g)`, the
hybrid energy of the orthonormal monomials (manuscript (7.15)).
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI SharpLSI.FL.Gross

theorem integral_double_sum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] {P : Measure α}
    {Q : Measure β} [SFinite P] [SFinite Q] [Fintype ι] (cc : ι → ι → ℝ) (a : ι → ι → α → ℝ)
    (b : ι → ι → β → ℝ) (ha : ∀ i i', Integrable (a i i') P) (hb : ∀ i i', Integrable (b i i') Q) :
    ∫ z, ∑ i, ∑ i', cc i i' * (a i i' z.1 * b i i' z.2) ∂(P.prod Q) =
      ∑ i, ∑ i', cc i i' * ((∫ x, a i i' x ∂P) * ∫ y, b i i' y ∂Q) := by
  have hint : ∀ i i', Integrable (fun z : α × β => cc i i' * (a i i' z.1 * b i i' z.2)) (P.prod Q) :=
    fun i i' => ((ha i i').mul_prod (hb i i')).const_mul _
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ => hint i i']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun i' _ => hint i i']
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [integral_const_mul, integral_prod_mul]

section energyid
variable {N d J : ℕ} {mu : Measure (Torus d)} [IsProbabilityMeasure mu] {e e' : ℕ → Torus d → ℝ}
  {lam : ℕ → ℝ}

/-- The Gaussian energy kernel. -/
def GY (lam : ℕ → ℝ) (B : Finset (Fin N)) (j j' : Fin N → Fin (J + 1)) (g : Fin (N * J) → ℝ) : ℝ :=
  ∑ k, lam ((flatMode k : ℕ) + 1) * (fderiv ℝ (Yf B j) g (Pi.single k 1) *
    fderiv ℝ (Yf B j') g (Pi.single k 1))

theorem integrable_Yf_mul (B : Finset (Fin N)) (j j' : Fin N → Fin (J + 1)) :
    Integrable (fun g => Yf B j g * Yf B j' g) (gpi (N * J)) :=
  integrable_slice_PBu (f := fun (_ : Unit) (g : Fin (N * J) → ℝ) => Yf B j g * Yf B j' g)
    (fun _ => ((tg_Yf B j).1.continuous.mul (tg_Yf B j').1.continuous).aestronglyMeasurable)
    ((PBu.of_tg (tg_Yf B j)).mul (PBu.of_tg (tg_Yf B j'))) ()

theorem integrable_dYf_mul (B : Finset (Fin N)) (j j' : Fin N → Fin (J + 1)) (k : Fin (N * J)) :
    Integrable (fun g : Fin (N * J) → ℝ => fderiv ℝ (Yf B j) g (Pi.single k 1) *
      fderiv ℝ (Yf B j') g (Pi.single k 1)) (gpi (N * J)) := by
  have hc : ∀ (i : Fin N → Fin (J + 1)) (k : Fin (N * J)),
      Continuous fun g : Fin (N * J) → ℝ => fderiv ℝ (Yf B i) g (Pi.single k 1) :=
    fun i k => ((tg_Yf B i).1.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integrable_slice_PBu (f := fun (_ : Unit) (g : Fin (N * J) → ℝ) =>
    fderiv ℝ (Yf B j) g (Pi.single k 1) * fderiv ℝ (Yf B j') g (Pi.single k 1))
    (fun _ => ((hc j k).mul (hc j' k)).aestronglyMeasurable)
    ((PBu.of_fderiv (tg_Yf B j) k).mul (PBu.of_fderiv (tg_Yf B j') k)) ()

theorem integrable_GY (lam : ℕ → ℝ) (B : Finset (Fin N)) (j j' : Fin N → Fin (J + 1)) :
    Integrable (GY lam B j j') (gpi (N * J)) := by
  have hc : ∀ (i : Fin N → Fin (J + 1)) (k : Fin (N * J)),
      Continuous fun g : Fin (N * J) → ℝ => fderiv ℝ (Yf B i) g (Pi.single k 1) :=
    fun i k => ((tg_Yf B i).1.continuous_fderiv (by simp)).clm_apply continuous_const
  unfold GY
  refine integrable_slice_PBu (f := fun (_ : Unit) (g : Fin (N * J) → ℝ) =>
    ∑ k, lam ((flatMode k : ℕ) + 1) * (fderiv ℝ (Yf B j) g (Pi.single k 1) *
      fderiv ℝ (Yf B j') g (Pi.single k 1))) (fun _ => ?_) ?_ ()
  · exact (continuous_finsetSum _ fun k _ => continuous_const.mul ((hc j k).mul (hc j' k))).aestronglyMeasurable
  · exact PBu.sum _ fun k _ =>
      (((PBu.of_fderiv (tg_Yf B j) k).mul (PBu.of_fderiv (tg_Yf B j') k)).const_mul _)

variable (hac : mu ≪ volume) (hca : volume ≪ mu) (hb : IsRefEigenbasis mu e lam)
  (hC1 : ∀ j, C1T (e' j)) (hae : ∀ j, e' j =ᵐ[mu] e j) (he0 : e' 0 = fun _ => 1)
  (hlam0 : lam 0 = 0) (B : Finset (Fin N)) (c : (Fin N → Fin (J + 1)) → ℝ)

include hac hca hb hC1 hae he0 hlam0 in
theorem energy_identity :
    ∫ z, Ex0 c (fun j => Yf B j) (fun j => Xf e' B j) z.1 z.2
        ∂((Measure.pi fun _ : Fin N => mu).prod (gpi (N * J))) +
      ∫ z, ∑ k, lam ((flatMode k : ℕ) + 1) *
          daF c (fun j => Yf B j) (fun j => Xf e' B j) z.1 z.2 k ^ 2
        ∂((Measure.pi fun _ : Fin N => mu).prod (gpi (N * J))) =
      ∑ j, (∑ i, lam (j i)) * c j ^ 2 := by
  set P : Measure (Config N d) := Measure.pi fun _ : Fin N => mu with hP
  have hX : ∀ j : Fin N → Fin (J + 1), C1C (Xf e' B j) := fun j => C1C_Xf hC1 B j
  -- the integrable pieces
  have iA1 : ∀ j j' : Fin N → Fin (J + 1), Integrable (gradPair (Xf e' B j) (Xf e' B j')) P := fun j j' => by
    obtain ⟨K, hK⟩ := bounded_gradPair (hX j) (hX j')
    exact integrable_of_bdd (measurable_gradPair (hX j) (hX j')) hK
  have iA2 : ∀ j j' : Fin N → Fin (J + 1), Integrable (fun x => Xf e' B j x * Xf e' B j' x) P := fun j j' =>
    ((hX j).mul (hX j')).integrable
  -- pointwise expansions
  have hEx : ∀ z : Config N d × (Fin (N * J) → ℝ),
      Ex0 c (fun j => Yf B j) (fun j => Xf e' B j) z.1 z.2 =
        ∑ j, ∑ j', (c j * c j') * (gradPair (Xf e' B j) (Xf e' B j') z.1 * (Yf B j z.2 * Yf B j' z.2)) := by
    intro z
    unfold Ex0 gradPair dXj
    calc ∑ p, (∑ j, (c j * Yf B j z.2) * dT (Xf e' B j ∘ SharpLSI.unflat) p (flat z.1)) ^ 2
        = ∑ p, ∑ j, ∑ j', ((c j * Yf B j z.2) * dT (Xf e' B j ∘ SharpLSI.unflat) p (flat z.1)) *
            ((c j' * Yf B j' z.2) * dT (Xf e' B j' ∘ SharpLSI.unflat) p (flat z.1)) := by
          simp_rw [sq, Finset.sum_mul_sum]
      _ = ∑ j, ∑ p, ∑ j', ((c j * Yf B j z.2) * dT (Xf e' B j ∘ SharpLSI.unflat) p (flat z.1)) *
            ((c j' * Yf B j' z.2) * dT (Xf e' B j' ∘ SharpLSI.unflat) p (flat z.1)) :=
          Finset.sum_comm
      _ = ∑ j, ∑ j', ∑ p, ((c j * Yf B j z.2) * dT (Xf e' B j ∘ SharpLSI.unflat) p (flat z.1)) *
            ((c j' * Yf B j' z.2) * dT (Xf e' B j' ∘ SharpLSI.unflat) p (flat z.1)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ => by ring
  have hEy : ∀ z : Config N d × (Fin (N * J) → ℝ),
      ∑ k, lam ((flatMode k : ℕ) + 1) * daF c (fun j => Yf B j) (fun j => Xf e' B j) z.1 z.2 k ^ 2 =
        ∑ j, ∑ j', (c j * c j') * ((Xf e' B j z.1 * Xf e' B j' z.1) * GY lam B j j' z.2) := by
    intro z
    unfold daF GY
    calc ∑ k, lam ((flatMode k : ℕ) + 1) * (∑ j, (c j * Xf e' B j z.1) *
            fderiv ℝ (Yf B j) z.2 (Pi.single k 1)) ^ 2
        = ∑ k, ∑ j, ∑ j', lam ((flatMode k : ℕ) + 1) *
            (((c j * Xf e' B j z.1) * fderiv ℝ (Yf B j) z.2 (Pi.single k 1)) *
              ((c j' * Xf e' B j' z.1) * fderiv ℝ (Yf B j') z.2 (Pi.single k 1))) := by
          simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      _ = ∑ j, ∑ k, ∑ j', lam ((flatMode k : ℕ) + 1) *
            (((c j * Xf e' B j z.1) * fderiv ℝ (Yf B j) z.2 (Pi.single k 1)) *
              ((c j' * Xf e' B j' z.1) * fderiv ℝ (Yf B j') z.2 (Pi.single k 1))) :=
          Finset.sum_comm
      _ = ∑ j, ∑ j', ∑ k, lam ((flatMode k : ℕ) + 1) *
            (((c j * Xf e' B j z.1) * fderiv ℝ (Yf B j) z.2 (Pi.single k 1)) *
              ((c j' * Xf e' B j' z.1) * fderiv ℝ (Yf B j') z.2 (Pi.single k 1))) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
  have hX1 : ∀ j j' : Fin N → Fin (J + 1), ∫ x, gradPair (Xf e' B j) (Xf e' B j') x ∂P =
      if ∀ i, i ∈ B → j i = j' i then ∑ i, (if i ∈ B then lam (j i) else 0) else 0 :=
    fun j j' => integral_gradPair_Xf hac hca hb hC1 hae he0 hlam0 B j j'
  have hX2 : ∀ j j' : Fin N → Fin (J + 1), ∫ x, Xf e' B j x * Xf e' B j' x ∂P =
      if ∀ i, i ∈ B → j i = j' i then 1 else 0 :=
    fun j j' => integral_Xf_mul hb hae he0 B j j'
  have hY1 := integral_Yf_mul B (J := J)
  have hY2 : ∀ j j' : Fin N → Fin (J + 1), ∫ g, GY lam B j j' g ∂gpi (N * J) =
      if ∀ i, i ∉ B → j i = j' i then ∑ i, (if i ∈ B then 0 else lam (j i)) else 0 := by
    intro j j'
    unfold GY
    rw [integral_finsetSum _ fun k _ => ?_]
    · rw [← sum_energy_Yf lam hlam0 B j j']
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul]
    · exact (integrable_dYf_mul B j j' k).const_mul _
  simp_rw [hEx, hEy]
  rw [integral_double_sum (fun j j' => c j * c j') (fun j j' x => gradPair (Xf e' B j) (Xf e' B j') x)
      (fun j j' g => Yf B j g * Yf B j' g) iA1 (fun j j' => integrable_Yf_mul B j j'),
    integral_double_sum (fun j j' => c j * c j') (fun j j' x => Xf e' B j x * Xf e' B j' x)
      (fun j j' g => GY lam B j j' g) iA2 (fun j j' => integrable_GY lam B j j'),
    ← Finset.sum_add_distrib]
  rw [show ∑ j, (∑ i, lam (j i)) * c j ^ 2 = ∑ j, ∑ j', if j' = j then c j ^ 2 * ∑ i, lam (j i) else 0 from
    Finset.sum_congr rfl fun j _ => by rw [Finset.sum_ite_eq']; simp [mul_comm]]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [hX1, hX2, hY1, hY2]
  by_cases hB : ∀ i, i ∈ B → j i = j' i <;> by_cases hC : ∀ i, i ∉ B → j i = j' i
  · have hjj : j' = j := by
      funext i
      by_cases hi : i ∈ B
      · exact (hB i hi).symm
      · exact (hC i hi).symm
    simp only [if_pos hB, if_pos hC, if_pos hjj]
    subst hjj
    have : ∑ i, (if i ∈ B then lam (j' i) else 0) + ∑ i, (if i ∈ B then 0 else lam (j' i)) =
        ∑ i, lam (j' i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by by_cases hi : i ∈ B <;> simp [hi]
    rw [show c j' * c j' * ((∑ i, if i ∈ B then lam (j' i) else 0) * 1) +
        c j' * c j' * (1 * ∑ i, if i ∈ B then 0 else lam (j' i)) =
        c j' * c j' * ((∑ i, if i ∈ B then lam (j' i) else 0) +
          ∑ i, if i ∈ B then 0 else lam (j' i)) by ring, this]
    simp [sq]
  · have hne : ¬ (j' = j) := fun h => hC (fun i _ => by rw [h])
    simp [hB, hC, hne]
  · have hne : ¬ (j' = j) := fun h => hB (fun i _ => by rw [h])
    simp [hB, hC, hne]
  · have hne : ¬ (j' = j) := fun h => hB (fun i _ => by rw [h])
    simp [hB, hC, hne]

end energyid

end SharpLSI.FL.HLA

end
