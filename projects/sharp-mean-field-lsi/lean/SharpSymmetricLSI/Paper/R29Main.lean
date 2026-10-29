import SharpSymmetricLSI.Paper.R29Joint3

/-!
# R29 assembly: Lemma 7.1 (Phase 3, lane D)
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace SharpLSI

/-- Convergence in `ℓ²` gives convergence of the squared norms. -/
theorem tendsto_tsum_sq_of_l2 {A : Type*} {a : ℕ → A → ℝ} {b : A → ℝ}
    (ha : ∀ k, Summable fun i => a k i ^ 2) (hb : Summable fun i => b i ^ 2)
    (h : Tendsto (fun k => ∑' i, ENNReal.ofReal ((a k i - b i) ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun k => ∑' i, a k i ^ 2) atTop (𝓝 (∑' i, b i ^ 2)) := by
  have hmem : ∀ f : A → ℝ, Summable (fun i => f i ^ 2) → Memℓp f 2 := fun f hf => by
    refine memℓp_gen ?_
    simpa [Real.norm_eq_abs, sq_abs] using hf
  have hnorm : ∀ (f : A → ℝ) (hf : Memℓp f 2),
      ‖(⟨f, hf⟩ : lp (fun _ : A => ℝ) 2)‖ ^ 2 = ∑' i, f i ^ 2 := fun f hf => by
    have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (⟨f, hf⟩ : lp (fun _ : A => ℝ) 2)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
    rw [this]
    congr 1; funext i
    simp [Real.norm_eq_abs, sq_abs]
  set v : ℕ → lp (fun _ : A => ℝ) 2 := fun k => ⟨a k, hmem _ (ha k)⟩
  set w : lp (fun _ : A => ℝ) 2 := ⟨b, hmem _ hb⟩
  have hdiff : ∀ k, Summable fun i => (a k i - b i) ^ 2 := fun k =>
    ((ha k).add hb |>.mul_left 2).of_nonneg_of_le (fun i => sq_nonneg _) fun i => by
      nlinarith [sq_nonneg (a k i + b i)]
  have hvw : ∀ k, ‖v k - w‖ ^ 2 = ∑' i, (a k i - b i) ^ 2 := fun k => by
    have : v k - w = ⟨fun i => a k i - b i, hmem _ (hdiff k)⟩ := by
      ext i; simp [v, w]; rfl
    rw [this, hnorm]
  have hD : Tendsto (fun k => ‖v k - w‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => ∑' i, (a k i - b i) ^ 2) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
      refine this.congr fun k => ?_
      simp only [Function.comp]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) (hdiff k),
        ENNReal.toReal_ofReal (tsum_nonneg fun i => sq_nonneg _)]
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    refine h2.congr fun k => ?_
    simp only [Function.comp]
    rw [← hvw, Real.sqrt_sq (norm_nonneg _)]
  have hN : Tendsto (fun k => ‖v k‖) atTop (𝓝 ‖w‖) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => by
      rw [Real.norm_eq_abs]; exact abs_norm_sub_norm_le _ _) hD
  have := hN.pow 2
  simp only [v, w, hnorm] at this
  exact this

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section main
variable (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
  {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
include hyp hμ he

/-- **Lemma 7.1.** -/
theorem reference_compactness_aux
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (Ψ : (k : ℕ) → Config (Ns k) d → ℝ)
    (hΨ : ∀ k, IsSymmetric (Ψ k) ∧
      MemH1C (Measure.pi fun _ : Fin (Ns k) => (μ : Measure (Torus d))) (Ψ k))
    (hB : ∃ B : NNReal, ∀ k, ∫⁻ X, ENNReal.ofReal (Ψ k X ^ 2 + gradSqC (Ψ k) X)
      ∂Measure.pi (fun _ : Fin (Ns k) => (μ : Measure (Torus d))) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Ψinf : (ℕ → ℝ) → ℝ, MemLp Ψinf 2 gammaRef ∧
      Tendsto (fun k => ∑' α : ℕ →₀ ℕ, ENNReal.ofReal
          ((∫ X, Ψ (φ k) X * occBasis e α (Ns (φ k)) X
              ∂Measure.pi (fun _ : Fin (Ns (φ k)) => (μ : Measure (Torus d))) -
            ∫ z, Ψinf z * hermiteBasis α z ∂gammaRef) ^ 2)) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ X, Ψ (φ k) X ^ 2
          ∂Measure.pi (fun _ : Fin (Ns (φ k)) => (μ : Measure (Torus d)))) atTop
        (𝓝 (∫ z, Ψinf z ^ 2 ∂gammaRef)) ∧
      (∀ Q, IsSecondChaos (Tmat W μ e) Q → ∀ (J : ℕ) (g : ℝ × ℝ × (Fin J → ℝ) →ᵇ ℝ),
        Tendsto (fun k => ∫ X, g (Ψ (φ k) X, Ucentered W μ (Ns (φ k)) X,
            fun n => fluct e (Ns (φ k)) n X)
            ∂Measure.pi (fun _ : Fin (Ns (φ k)) => (μ : Measure (Torus d)))) atTop
          (𝓝 (∫ z, g (Ψinf z, Uinf W μ Q z, fun n => z n) ∂gammaRef))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ k,
        ∫⁻ X in {X | M < Ψ (φ k) X ^ 2}, ENNReal.ofReal (Ψ (φ k) X ^ 2)
          ∂Measure.pi (fun _ : Fin (Ns (φ k)) => (μ : Measure (Torus d))) ≤ ENNReal.ofReal ε := by
  obtain ⟨Bn, hBn⟩ := hB
  set B : ℝ := (Bn : ℝ)
  have hB0 : 0 ≤ B := Bn.2
  set μm := (μ : Measure (Torus d))
  set PN : (k : ℕ) → Measure (Config (Ns k) d) := fun k => Measure.pi fun _ : Fin (Ns k) => μm
  have hΨL : ∀ k, MemLp (Ψ k) 2 (PN k) := fun k =>
    (measurableEmbedding_flat.memLp_map_measure_iff).mp (hΨ k).2.2.1
  have hgI : ∀ k, Integrable (gradSqC (Ψ k)) (PN k) := fun k =>
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k' _ =>
      (memLp_weakGradC hyp hμ (hΨ k).2 i k').integrable_sq
  have hsum : ∀ k, ∫ X, Ψ k X ^ 2 ∂PN k + ∫ X, gradSqC (Ψ k) X ∂PN k ≤ B := fun k => by
    have hnn : 0 ≤ᵐ[PN k] fun X => Ψ k X ^ 2 + gradSqC (Ψ k) X :=
      Eventually.of_forall fun X => add_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hi : Integrable (fun X => Ψ k X ^ 2 + gradSqC (Ψ k) X) (PN k) :=
      (hΨL k).integrable_sq.add (hgI k)
    have h := hBn k
    have e1 := ofReal_integral_eq_lintegral_ofReal hi hnn
    change (∫⁻ X, ENNReal.ofReal (Ψ k X ^ 2 + gradSqC (Ψ k) X) ∂PN k) ≤ _ at h
    rw [← e1, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff hB0] at h
    rwa [integral_add (hΨL k).integrable_sq (hgI k)] at h
  have hg0 : ∀ k, 0 ≤ ∫ X, gradSqC (Ψ k) X ∂PN k := fun k =>
    integral_nonneg fun X => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ∀ k, ∫ X, Ψ k X ^ 2 ∂PN k ≤ B := fun k => by
    linarith [hsum k, hg0 k]
  have h2 : ∀ k, ∫ X, gradSqC (Ψ k) X ∂PN k ≤ B := fun k => by
    have : 0 ≤ ∫ X, Ψ k X ^ 2 ∂PN k := integral_nonneg fun X => sq_nonneg (Ψ k X)
    linarith [hsum k]
  -- the coefficients
  set x : ℕ → (ℕ →₀ ℕ) → ℝ := fun k α => ∫ X, Ψ k X * occBasis e α (Ns k) X ∂PN k
  have hx0 : ∀ k α, Ns k < occSize α → x k α = 0 := fun k α h => by
    simp only [x, occBasis_zero_of_lt h, Pi.zero_apply, mul_zero, integral_zero]
  have hfilt : ∀ k (S : Finset (ℕ →₀ ℕ)) (f : (ℕ →₀ ℕ) → ℝ), (∀ α, Ns k < occSize α → f α = 0) →
      ∑ α ∈ S, f α = ∑ α ∈ S.filter (fun α => occSize α ≤ Ns k), f α := fun k S f hf => by
    refine (Finset.sum_subset (Finset.filter_subset _ S) fun α hα hα' => ?_).symm
    exact hf α (by by_contra h; exact hα' (Finset.mem_filter.mpr ⟨hα, by omega⟩))
  have hx1 : ∀ k (S : Finset (ℕ →₀ ℕ)), ∑ α ∈ S, x k α ^ 2 ≤ B := fun k S => by
    rw [hfilt k S (fun α => x k α ^ 2) fun α h => by rw [hx0 k α h]; ring]
    exact (bessel_occ_L2 hyp hμ he (hΨL k) _ fun α hα => (Finset.mem_filter.mp hα).2).trans (h1 k)
  have hx2 : ∀ k (S : Finset (ℕ →₀ ℕ)), ∑ α ∈ S, occEnergy lam α * x k α ^ 2 ≤ B := fun k S => by
    rw [hfilt k S (fun α => occEnergy lam α * x k α ^ 2) fun α h => by rw [hx0 k α h]; ring]
    exact (bessel_occ_energy hyp hμ he (hΨ k).2 _ fun α hα => (Finset.mem_filter.mp hα).2).trans
      (h2 k)
  obtain ⟨φ, hφ, x0, hx01, hx02, hpt, hl2⟩ := exists_l2_subseq (occEnergy_nonneg hyp hμ he)
    (finite_occEnergy_le hyp hμ he) hB0 hx1 hx2
  obtain ⟨Ψinf, hΨinfL, hcoef, hpar⟩ := exists_hermite_synthesis hx01
  refine ⟨φ, hφ, Ψinf, hΨinfL, ?_, ?_, ?_, ?_⟩
  · simp only [hcoef]; exact hl2
  · have hP : ∀ k, HasSum (fun α => x (φ k) α ^ 2) (∫ X, Ψ (φ k) X ^ 2 ∂PN (φ k)) := fun k =>
      hasSum_sq_occ_ref hyp hμ he (hΨL (φ k)) (hΨ (φ k)).1
    rw [← hpar.tsum_eq]
    refine (tendsto_tsum_sq_of_l2 (fun k => (hP k).summable) hpar.summable hl2).congr fun k => ?_
    exact (hP k).tsum_eq
  · intro Q hQ J g
    set S : ℕ → Finset (ℕ →₀ ℕ) := fun R => (finite_occEnergy_le hyp hμ he ((R : ℝ) + 1)).toFinset
    have hS : ∀ (R : ℕ) α, occEnergy lam α ≤ (R : ℝ) + 1 → α ∈ S R := fun R α h => by simp [S, h]
    have hεt : Tendsto (fun R : ℕ => B / ((R : ℝ) + 1)) atTop (𝓝 0) := by
      have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul B
      rw [mul_zero] at h
      exact h.congr fun R => by rw [mul_one_div]
    have htail : ∀ R k, ∫ X, (Ψ (φ k) X - ∑ α ∈ S R, (∫ Y, Ψ (φ k) Y * occBasis e α (Ns (φ k)) Y
        ∂PN (φ k)) * occBasis e α (Ns (φ k)) X) ^ 2 ∂PN (φ k) ≤ B / ((R : ℝ) + 1) := fun R k =>
      integral_sub_proj_sq_le hyp hμ he (hΨ (φ k)).2 (hΨ (φ k)).1 (h2 _) (by positivity) (S R)
        (hS R)
    have hEt : ∑' α, occEnergy lam α * x0 α ^ 2 ≤ B :=
      Real.tsum_le_of_sum_le (fun α => mul_nonneg (occEnergy_nonneg hyp hμ he α) (sq_nonneg _)) hx02
    have hEs : Summable fun α => occEnergy lam α * x0 α ^ 2 :=
      summable_of_sum_le (fun α => mul_nonneg (occEnergy_nonneg hyp hμ he α) (sq_nonneg _)) hx02
    have htailInf : ∀ R, ∫ z, (Ψinf z - ∑ α ∈ S R, x0 α * hermiteBasis α z) ^ 2 ∂gammaRef ≤
        B / ((R : ℝ) + 1) := fun R => by
      have hL : (0 : ℝ) < (R : ℝ) + 1 := by positivity
      rw [integral_sub_sum_sq (S R) x0 hΨinfL memLp_hermiteBasis]
      simp_rw [hcoef, integral_hermiteBasis_mul]
      have h3 : ∑ α ∈ S R, ∑ β ∈ S R, x0 α * x0 β * (if α = β then (1 : ℝ) else 0) =
          ∑ α ∈ S R, x0 α ^ 2 := by
        refine Finset.sum_congr rfl fun α hα => ?_
        simp [Finset.sum_ite_eq, hα, sq]
      rw [h3, ← hpar.tsum_eq]
      have hsplit : ∑' α, x0 α ^ 2 - ∑ α ∈ S R, x0 α ^ 2 =
          ∑' α, (if α ∈ S R then 0 else x0 α ^ 2) := by
        have : ∀ α, x0 α ^ 2 = (if α ∈ S R then x0 α ^ 2 else 0) +
            (if α ∈ S R then 0 else x0 α ^ 2) := fun α => by split_ifs <;> simp
        rw [tsum_congr this, Summable.tsum_add (summable_of_ne_finset_zero (s := S R)
          fun α hα => by simp [hα]) (hpar.summable.of_nonneg_of_le
            (fun α => by split_ifs <;> positivity)
            fun α => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl),
          tsum_eq_sum (s := S R) fun α hα => by simp [hα]]
        simp only [Finset.sum_ite_mem, Finset.inter_self]
        ring
      have hle : ∑' α, (if α ∈ S R then 0 else x0 α ^ 2) ≤
          ∑' α, occEnergy lam α * x0 α ^ 2 / ((R : ℝ) + 1) := by
        refine Summable.tsum_le_tsum (fun α => ?_) (hpar.summable.of_nonneg_of_le
          (fun α => by split_ifs <;> positivity)
          fun α => by split_ifs <;> first | exact sq_nonneg _ | exact le_rfl) (hEs.div_const _)
        split_ifs with h
        · exact div_nonneg (mul_nonneg (occEnergy_nonneg hyp hμ he α) (sq_nonneg _)) hL.le
        · have hΛ : (R : ℝ) + 1 < occEnergy lam α := by
            by_contra h'; exact h (hS R α (by linarith))
          rw [le_div_iff₀ hL]
          nlinarith [sq_nonneg (x0 α)]
      rw [tsum_div_const] at hle
      have : ∑' α, x0 α ^ 2 - 2 * ∑ α ∈ S R, x0 α * x0 α + ∑ α ∈ S R, x0 α ^ 2 =
          ∑' α, x0 α ^ 2 - ∑ α ∈ S R, x0 α ^ 2 := by
        simp only [← sq]; ring
      rw [this, hsplit]
      exact hle.trans (div_le_div_of_nonneg_right hEt hL.le)
    exact joint_law_occ hyp hμ he hQ J (hNs.comp hφ.tendsto_atTop) (fun k => Ψ (φ k))
      (fun k => hΨL (φ k)) x0 hΨinfL hpt S hεt htail htailInf g
  · intro ε hε
    obtain ⟨M, -, hui⟩ := ui_occ hyp hμ he hB0 hε
    exact ⟨M, fun k => hui _ _ (hΨ (φ k)).2 (hΨ (φ k)).1 (h1 _) (h2 _)⟩

end main

end SharpLSI
