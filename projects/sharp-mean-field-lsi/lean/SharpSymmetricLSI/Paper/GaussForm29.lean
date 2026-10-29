import SharpSymmetricLSI.Paper.GaussForm28
import SharpSymmetricLSI.Paper.Occ4

/-!
# R32 (G4): Hermite completeness in the variables `ξ`

* `exists_measurable_inverse_xi`: there is a measurable `G` with `G(ξ(z)) = z` for `γ`-a.e. `z`
  (each `z_i` is an a.e. limit along a subsequence of `∑_{j<N} c_{ij}ξ_j`).
* `map_xi_eq_gammaRef`: `γ.map ξ = gammaRef = N(0,1)^{⊗ℕ}` (finite marginals, `eq_infinitePi`).
* `hermite_complete_xi`: if `F ∈ L²(γ)` is orthogonal to every `h_α(ξ)` then `F = 0` `γ`-a.e.
  (transfer to `gammaRef` through `G` and `hermiteBasis_complete`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped InnerProductSpace ENNReal NNReal

namespace SharpLSI

theorem measurable_hermiteBasis (α : ℕ →₀ ℕ) : Measurable (hermiteBasis α) := by
  unfold hermiteBasis
  refine Finset.measurable_prod _ fun n _ => ?_
  exact (((Polynomial.continuous_aeval (Polynomial.hermite (α n))).comp
    (continuous_apply (A := fun _ : ℕ => ℝ) n)).measurable).div_const _

section herm
variable {T : ℕ → ℕ → ℝ} (hT : ∀ i j, T i j = T j i)
  (hS : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2) {σ : ℝ} (hσ0 : 0 < σ)
  (hσ : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
  {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus T C) (hCs : ∀ a b, C a b = C b a)
  {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ C)
  {v : ℕ → ℕ → ℝ} (hv2 : ∀ j, Summable fun i => v j i ^ 2)
  (hvC : ∀ i j, ∑' a, v i a * ∑' b, C a b * v j b = if i = j then 1 else 0)
  {ξ : ℕ → (ℕ → ℝ) → ℝ} (hξ : ∀ j, IsRowVariable v γ j (ξ j))
  (hP : ∀ i, HasSum (fun j => (∑' b, C i b * v j b) ^ 2) (C i i))
include hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ hP

/-- **The coordinates are measurable functions of `ξ`, `γ`-a.e.** -/
theorem exists_measurable_inverse_xi :
    ∃ G : (ℕ → ℝ) → (ℕ → ℝ), Measurable G ∧ ∀ᵐ z ∂γ, G (fun j => ξ j z) = z := by
  have hseq : ∀ i, ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ z ∂γ, Tendsto
      (fun k => ∑ j ∈ Finset.range (ns k), (∑' b, C i b * v j b) * ξ j z) atTop (𝓝 (z i)) := by
    intro i
    have h := tendsto_coord_approx hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ hP i
    have hm : TendstoInMeasure γ
        (fun N z => ∑ j ∈ Finset.range N, (∑' b, C i b * v j b) * ξ j z) atTop (fun z => z i) :=
      tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) h
    exact hm.exists_seq_tendsto_ae
  choose ns hns hae using hseq
  set g : ℕ → (ℕ → ℝ) → ℝ := fun i x => limsup (fun k =>
    ∑ j ∈ Finset.range (ns i k), (∑' b, C i b * v j b) * x j) atTop
  refine ⟨fun x i => g i x, measurable_pi_iff.2 fun i => ?_, ?_⟩
  · exact Measurable.limsup fun k => Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).const_mul _
  · have : ∀ᵐ z ∂γ, ∀ i, Tendsto (fun k => ∑ j ∈ Finset.range (ns i k),
        (∑' b, C i b * v j b) * ξ j z) atTop (𝓝 (z i)) := ae_all_iff.2 hae
    filter_upwards [this] with z hz
    funext i
    exact (hz i).limsup_eq

omit hP in
/-- **`γ.map ξ = gammaRef`.** -/
theorem map_xi_eq_gammaRef : γ.map (fun z => fun j => ξ j z) = gammaRef := by
  have := hγ.1
  have hΞ : AEMeasurable (fun z => fun j => ξ j z) γ :=
    aemeasurable_pi_iff.2 fun j => (hξ j).1.aestronglyMeasurable.aemeasurable
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  set J := s.sup id + 1
  have hsJ : ∀ i ∈ s, i < J := fun i hi => Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
  set t' : Fin J → Set ℝ := fun k => if (k : ℕ) ∈ s then t k else univ
  have hpre : (fun z => fun j => ξ j z) ⁻¹' Set.pi s t =
      (fun z => fun k : Fin J => ξ k z) ⁻¹' Set.pi univ t' := by
    ext z
    simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, mem_univ, forall_const, t']
    constructor
    · intro h k
      by_cases hk : (k : ℕ) ∈ s
      · simp only [hk, ite_true]; exact h _ hk
      · simp [hk]
    · intro h i hi
      have := h ⟨i, hsJ i hi⟩
      simpa [hi] using this
  have hmeas : MeasurableSet (Set.pi (s : Set ℕ) t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.map_apply_of_aemeasurable hΞ hmeas, hpre]
  have hΞJ : AEMeasurable (fun z => fun k : Fin J => ξ k z) γ :=
    aemeasurable_pi_iff.2 fun k => (hξ k).1.aestronglyMeasurable.aemeasurable
  have hmeas' : MeasurableSet (Set.pi univ t') :=
    MeasurableSet.univ_pi fun k => by
      simp only [t']; split_ifs
      · exact ht _
      · exact MeasurableSet.univ
  rw [← Measure.map_apply_of_aemeasurable hΞJ hmeas',
    map_xi_eq_pi hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ J, Measure.pi_pi]
  rw [Fin.prod_univ_eq_prod_range (fun k => gaussianReal 0 1
    (if k ∈ s then t k else univ)) J]
  · rw [← Finset.prod_subset (s₁ := s) (s₂ := Finset.range J)
      (fun i hi => Finset.mem_range.2 (hsJ i hi)) (fun i _ hi => by simp [hi])]
    exact Finset.prod_congr rfl fun i hi => by simp [hi]

/-- **Hermite completeness in `ξ`**: `F ⊥ h_α(ξ)` for all `α` implies `F = 0` `γ`-a.e. -/
theorem hermite_complete_xi {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    (horth : ∀ α : ℕ →₀ ℕ, ∫ z, F z * hermiteBasis α (fun j => ξ j z) ∂γ = 0) :
    F =ᵐ[γ] 0 := by
  have := hγ.1
  obtain ⟨G, hGm, hG⟩ := exists_measurable_inverse_xi hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ hP
  have hmap := map_xi_eq_gammaRef hT hS hσ0 hσ hC hCs hγ hv2 hvC hξ
  have hΞ : AEMeasurable (fun z => fun j => ξ j z) γ :=
    aemeasurable_pi_iff.2 fun j => (hξ j).1.aestronglyMeasurable.aemeasurable
  set F' := hF.aestronglyMeasurable.mk F
  have hFF : F =ᵐ[γ] F' := hF.aestronglyMeasurable.ae_eq_mk
  have hF'm : Measurable F' := hF.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  set H : (ℕ → ℝ) → ℝ := fun x => F' (G x)
  have hHm : Measurable H := hF'm.comp hGm
  have hHΞ : ∀ᵐ z ∂γ, H (fun j => ξ j z) = F z := by
    filter_upwards [hG, hFF] with z h1 h2
    simp only [H, h1, h2]
  have hH2 : MemLp H 2 gammaRef := by
    rw [← hmap, memLp_map_measure_iff hHm.aestronglyMeasurable hΞ]
    exact hF.ae_eq (hHΞ.mono fun z hz => hz.symm)
  have hHorth : ∀ α : ℕ →₀ ℕ, ∫ x, H x * hermiteBasis α x ∂gammaRef = 0 := fun α => by
    rw [← hmap, integral_map (f := fun x => H x * hermiteBasis α x) hΞ
      (by exact (hHm.mul (measurable_hermiteBasis α)).aestronglyMeasurable), ← horth α]
    exact integral_congr_ae (hHΞ.mono fun z hz => by simp only [hz])
  have h0 := hermiteBasis_complete hH2 hHorth
  rw [← hmap] at h0
  have h1 := ae_of_ae_map hΞ h0
  filter_upwards [h1, hHΞ] with z hz1 hz2
  rw [← hz2]; exact hz1

end herm

end SharpLSI
