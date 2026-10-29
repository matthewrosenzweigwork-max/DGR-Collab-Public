import FullLabeledLSI.Paper.Lindeberg1

/-!
# Lemma 7.1, part 2: passing from a reference eigenbasis to a measurable bounded representative

The frozen statements evaluate the eigenfunctions `e j` pointwise, while `IsRefEigenbasis` only gives
`e j` up to `μ`-null sets. Here we show that the two integrals of S26 and the interface
`HybridPolyMoment` are unchanged when `e` is replaced by an a.e.-equal basis, and that a reference
eigenbasis has an a.e.-equal `GoodBasis` representative (the `C¹` representatives of `ref_spectrum`).
-/

open MeasureTheory ProbabilityTheory

namespace SharpLSI.FL

variable {d : ℕ}

theorem ae_pi_eq {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e e' : ℕ → Torus d → ℝ}
    (h : ∀ j, e j =ᵐ[μ] e' j) (N : ℕ) :
    ∀ᵐ X ∂Measure.pi (fun _ : Fin N => μ), ∀ l j, e j (X l) = e' j (X l) := by
  refine ae_all_iff.2 fun l => ae_all_iff.2 fun j => ?_
  exact (measurePreserving_eval (fun _ : Fin N => μ) l).quasiMeasurePreserving.ae_eq_comp (h j)

theorem ae_hyb_eq {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {e e' : ℕ → Torus d → ℝ}
    (h : ∀ j, e j =ᵐ[μ] e' j) (N J : ℕ) :
    ∀ᵐ ω ∂hybMeasure μ N J, ∀ l j, e j (ω.1 l) = e' j (ω.1 l) := by
  have hfst : MeasurePreserving (Prod.fst : Config N d × (Fin N → Fin J → ℝ) → Config N d)
      (hybMeasure μ N J) (Measure.pi fun _ : Fin N => μ) := by
    unfold hybMeasure
    exact measurePreserving_fst
  exact hfst.quasiMeasurePreserving.ae (ae_pi_eq h N)

theorem polyEval_congr {e e' : ℕ → Torus d → ℝ} {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (X : Config N d) (h : ∀ l j, e j (X l) = e' j (X l)) : polyEval e c X = polyEval e' c X := by
  unfold polyEval
  exact Finset.sum_congr rfl fun j _ => by
    rw [Finset.prod_congr rfl fun l _ => h l (j l)]

theorem Zlow_congr {e e' : ℕ → Torus d → ℝ} {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ)
    (X : Config N d) (h : ∀ l j, e j (X l) = e' j (X l)) (m : Fin J) :
    Zlow e c δ X m = Zlow e' c δ X m := by
  unfold Zlow
  rw [Finset.sum_congr rfl fun l _ => h l _]

theorem polyB_congr {e e' : ℕ → Torus d → ℝ} {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ)
    (B : Finset (Fin N)) (ω : Config N d × (Fin N → Fin J → ℝ))
    (h : ∀ l j, e j (ω.1 l) = e' j (ω.1 l)) : polyB e c B ω = polyB e' c B ω := by
  unfold polyB
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [hybFactor]
  split_ifs <;> simp [h]

/-- The first S26 integral is unchanged under a.e.-equal replacement of `e`. -/
theorem integral_orig_congr {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {e e' : ℕ → Torus d → ℝ} (h : ∀ j, e j =ᵐ[μ] e' j) {N J JR : ℕ}
    (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ) :
    ∫ X, Φ (polyEval e c X, fun m => Zlow e c δ X (Fin.castLE hJ m))
        ∂Measure.pi (fun _ : Fin N => μ) =
      ∫ X, Φ (polyEval e' c X, fun m => Zlow e' c δ X (Fin.castLE hJ m))
        ∂Measure.pi (fun _ : Fin N => μ) := by
  refine integral_congr_ae ((ae_pi_eq h N).mono fun X hX => ?_)
  simp only [polyEval_congr c X hX, Zlow_congr c δ X hX]

/-- The second S26 integral is unchanged under a.e.-equal replacement of `e`. -/
theorem integral_hyb_congr {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {e e' : ℕ → Torus d → ℝ} (h : ∀ j, e j =ᵐ[μ] e' j) {N J JR : ℕ}
    (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) (hJ : JR ≤ J) (Φ : ℝ × (Fin JR → ℝ) → ℝ) :
    ∫ w, Φ (hybEval e c δ w, fun m => Glow c δ w (Fin.castLE hJ m)) ∂hybMeasure μ N J =
      ∫ w, Φ (hybEval e' c δ w, fun m => Glow c δ w (Fin.castLE hJ m)) ∂hybMeasure μ N J := by
  refine integral_congr_ae ((ae_hyb_eq h N J).mono fun ω hω => ?_)
  simp only [hybEval_eq_polyB, polyB_congr c (retained c δ) ω hω]

/-- The interface is invariant under a.e.-equal replacement of `e`. -/
theorem HybridPolyMoment.of_ae_eq {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {e e' : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} {J : ℕ} (hm : HybridPolyMoment μ e lam J)
    (h : ∀ j, e j =ᵐ[μ] e' j) : HybridPolyMoment μ e' lam J := by
  intro L q
  obtain ⟨K, hK, hKb⟩ := hm L q
  refine ⟨K, hK, fun N B c hc => ?_⟩
  have heq : ∫⁻ ω, ENNReal.ofReal (|polyB e' c B ω| ^ q) ∂hybMeasure μ N J =
      ∫⁻ ω, ENNReal.ofReal (|polyB e c B ω| ^ q) ∂hybMeasure μ N J := by
    refine lintegral_congr_ae ((ae_hyb_eq h N J).mono fun ω hω => ?_)
    simp only [(polyB_congr c B ω hω).symm]
  rw [heq]
  exact hKb N B c hc

/-! ### A measurable bounded representative of the reference eigenbasis -/

theorem exists_goodBasis {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    ∃ e' : ℕ → Torus d → ℝ, GoodBasis (μ : Measure (Torus d)) e' ∧
      ∀ j, e' j =ᵐ[(μ : Measure (Torus d))] e j := by
  obtain ⟨-, -, -, C, q, hC⟩ := (ref_spectrum hd hyp hr hμ).2 e lam he
  choose eC hc using hC
  have hcont : ∀ j, Continuous (eC j) := fun j =>
    (isOpenQuotientMap_liftT (d := d)).isQuotientMap.continuous_iff.mpr (hc j).1.continuous
  set e' : ℕ → Torus d → ℝ := fun j => if j = 0 then fun _ => 1 else eC j with he'
  have hae : ∀ j, e' j =ᵐ[(μ : Measure (Torus d))] e j := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [he', ite_true]
      rw [he.zero]
    · simp only [he', hj, ite_false]
      exact (hc j).2.1
  refine ⟨e', ⟨?_, ?_, ?_, ?_⟩, hae⟩
  · simp [he']
  · intro j
    by_cases hj : j = 0
    · simp [he', hj]
    · simp only [he', hj, ite_false]; exact (hcont j).measurable
  · intro j
    by_cases hj : j = 0
    · exact ⟨1, fun x => by simp [he', hj]⟩
    · refine ⟨C * (1 + lam j) ^ q, fun x => ?_⟩
      simp only [he', hj, ite_false]
      exact le_trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)) ((hc j).2.2.1 x)
  · intro i j
    rw [← he.orthonormal i j]
    exact integral_congr_ae ((hae i).mul (hae j))

/-- The spectral facts of a reference eigenbasis used in Lemma 7.1. -/
theorem lam_facts {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ}
    (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam) :
    lam 0 = 0 ∧ (∀ k, 0 ≤ lam k) ∧ Monotone lam ∧ 0 < lam 1 :=
  ⟨SharpLSI.lam_zero hyp hμ he, fun k => he.lam_nonneg' k, he.mono,
    ((ref_spectrum hd hyp hr hμ).2 e lam he).1 1 le_rfl⟩

end SharpLSI.FL
