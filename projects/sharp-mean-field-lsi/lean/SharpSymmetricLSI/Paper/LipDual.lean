import SharpSymmetricLSI.Infra.Torus
import SharpSymmetricLSI.Paper.AscoliSeq

/-!
# The dual Lipschitz distance metrizes weak convergence (D19 sanity lemma)

Weak convergence implies uniform convergence of the integrals over the flat-`1`-Lipschitz
functions vanishing at `0` (Arzelà–Ascoli), and conversely bounded Lipschitz test functions
suffice (Portmanteau).
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ}

/-- A copy of `dLip` (D19), to avoid an import cycle. -/
noncomputable def dLipAux (ν η : ProbabilityMeasure (Torus d)) : ℝ :=
  sSup {s | ∃ φ : Torus d → ℝ, FlatLipschitzWith 1 φ ∧ φ 0 = 0 ∧
    s = |∫ x, φ x ∂(ν : Measure (Torus d)) - ∫ x, φ x ∂(η : Measure (Torus d))|}

theorem dLipAux_metrizes (ν : ℕ → ProbabilityMeasure (Torus d)) (η : ProbabilityMeasure (Torus d)) :
    Tendsto ν atTop (nhds η) ↔ Tendsto (fun n => dLipAux (ν n) η) atTop (nhds 0) := by
  -- bounds for flat-1-Lipschitz functions vanishing at `0`
  have hbd : ∀ φ : Torus d → ℝ, FlatLipschitzWith 1 φ → φ 0 = 0 → ∀ x, |φ x| ≤ Real.sqrt d := by
    intro φ hφ h0 x
    have := hφ x 0
    rw [h0, sub_zero, one_mul] at this
    refine this.trans ?_
    unfold flatDist
    refine Real.sqrt_le_sqrt ?_
    calc ∑ k, ‖x k - (0 : Torus d) k‖ ^ 2 ≤ ∑ _k : Fin d, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
          have h1 : ‖x k - (0 : Torus d) k‖ ≤ 1 / 2 := by
            have := AddCircle.norm_le_half_period (p := (1 : ℝ)) (x := x k - (0 : Torus d) k)
              one_ne_zero
            simpa using this
          have h2 : 0 ≤ ‖x k - (0 : Torus d) k‖ := norm_nonneg _
          nlinarith
      _ = d := by simp
  have hlip : ∀ φ : Torus d → ℝ, FlatLipschitzWith 1 φ →
      LipschitzWith ⟨Real.sqrt d, Real.sqrt_nonneg _⟩ φ := by
    intro φ hφ
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq]
    refine (hφ x y).trans ?_
    rw [one_mul]
    exact (flatDist_comparison x y).2.trans (le_of_eq (by rw [Fintype.card_fin]; rfl))
  have hint : ∀ (ρ : ProbabilityMeasure (Torus d)) (φ : Torus d → ℝ), FlatLipschitzWith 1 φ →
      φ 0 = 0 → Integrable φ (ρ : Measure (Torus d)) := fun ρ φ hφ h0 =>
    Integrable.of_bound (hlip φ hφ).continuous.aestronglyMeasurable (Real.sqrt d)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbd φ hφ h0 x)
  have hS : ∀ ρ σ : ProbabilityMeasure (Torus d), BddAbove {s | ∃ φ : Torus d → ℝ,
      FlatLipschitzWith 1 φ ∧ φ 0 = 0 ∧ s = |∫ x, φ x ∂(ρ : Measure (Torus d)) -
        ∫ x, φ x ∂(σ : Measure (Torus d))|} := by
    intro ρ σ
    refine ⟨2 * Real.sqrt d, ?_⟩
    rintro s ⟨φ, hφ, h0, rfl⟩
    have h1 : ∀ τ : ProbabilityMeasure (Torus d), |∫ x, φ x ∂(τ : Measure (Torus d))| ≤ Real.sqrt d :=
      fun τ => by
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ x, |φ x| ∂(τ : Measure (Torus d)) ≤ ∫ _x, Real.sqrt d ∂(τ : Measure (Torus d)) :=
              integral_mono (hint τ φ hφ h0).abs (integrable_const _) fun x => hbd φ hφ h0 x
          _ = Real.sqrt d := by simp
    have := abs_sub _ _ |>.trans (add_le_add (h1 ρ) (h1 σ))
    linarith
  have hmem : ∀ ρ σ : ProbabilityMeasure (Torus d), ∀ φ, FlatLipschitzWith 1 φ → φ 0 = 0 →
      |∫ x, φ x ∂(ρ : Measure (Torus d)) - ∫ x, φ x ∂(σ : Measure (Torus d))| ≤ dLipAux ρ σ :=
    fun ρ σ φ hφ h0 => le_csSup (hS ρ σ) ⟨φ, hφ, h0, rfl⟩
  have hnn : ∀ ρ σ : ProbabilityMeasure (Torus d), 0 ≤ dLipAux ρ σ := fun ρ σ =>
    (abs_nonneg _).trans (hmem ρ σ (fun _ => 0) (fun x y => by
      simp only [sub_self, abs_zero, one_mul]; exact Real.sqrt_nonneg _) rfl)
  constructor
  · intro hW
    rw [Metric.tendsto_atTop]
    by_contra hcon
    push_neg at hcon
    obtain ⟨ε, hε, hfreq⟩ := hcon
    have hfr : ∃ᶠ n in atTop, ε ≤ dLipAux (ν n) η := Filter.frequently_atTop.mpr fun N => by
      obtain ⟨n, hn, h⟩ := hfreq N
      refine ⟨n, hn, ?_⟩
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hnn _ _)] at h
    obtain ⟨m, hm, hmε⟩ := Filter.extraction_of_frequently_atTop hfr
    have hex : ∀ k, ∃ φ : Torus d → ℝ, FlatLipschitzWith 1 φ ∧ φ 0 = 0 ∧
        ε / 2 < |∫ x, φ x ∂(ν (m k) : Measure (Torus d)) - ∫ x, φ x ∂(η : Measure (Torus d))| := by
      intro k
      have hlt : ε / 2 < dLipAux (ν (m k)) η := by have := hmε k; linarith
      have hne : ({s | ∃ φ : Torus d → ℝ, FlatLipschitzWith 1 φ ∧ φ 0 = 0 ∧
          s = |∫ x, φ x ∂(ν (m k) : Measure (Torus d)) - ∫ x, φ x ∂(η : Measure (Torus d))|} :
            Set ℝ).Nonempty :=
        ⟨_, fun _ => 0, fun x y => by
          simp only [sub_self, abs_zero, one_mul]; exact Real.sqrt_nonneg _, rfl, rfl⟩
      obtain ⟨s, ⟨φ, hφ, h0, rfl⟩, hs⟩ := exists_lt_of_lt_csSup hne hlt
      exact ⟨φ, hφ, h0, hs⟩
    choose φ hφ h0 hφε using hex
    obtain ⟨ψ, hψ, v, hv, hunif⟩ := exists_subseq_unif φ (C := Real.sqrt d)
      (L := ⟨Real.sqrt d, Real.sqrt_nonneg _⟩) (fun k x => hbd _ (hφ k) (h0 k) x)
      (fun k => hlip _ (hφ k))
    set v' : Torus d →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨v, hv⟩
    have hconv := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (hW.comp (hm.comp hψ).tendsto_atTop)) v'
    obtain ⟨K1, hK1⟩ := Metric.tendsto_atTop.mp hconv (ε / 8) (by positivity)
    obtain ⟨K2, hK2⟩ := (hunif (ε / 8) (by positivity)).exists_forall_of_atTop
    set k := max K1 K2
    have h1 := hK1 k (le_max_left _ _)
    have h2 := hK2 k (le_max_right _ _)
    have hclose : ∀ ρ : ProbabilityMeasure (Torus d),
        |∫ x, φ (ψ k) x ∂(ρ : Measure (Torus d)) - ∫ x, v x ∂(ρ : Measure (Torus d))| ≤ ε / 8 := by
      intro ρ
      rw [← integral_sub (f := φ (ψ k)) (g := v) (hint ρ _ (hφ _) (h0 _))
        (v'.integrable (ρ : Measure (Torus d)))]
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ x, |φ (ψ k) x - v x| ∂(ρ : Measure (Torus d)) ≤ ∫ _x, ε / 8 ∂(ρ : Measure (Torus d)) :=
            integral_mono ((hint ρ _ (hφ _) (h0 _)).sub (v'.integrable _)).abs (integrable_const _)
              fun x => h2 x
        _ = ε / 8 := by simp
    have hv1 : |∫ x, v x ∂(ν (m (ψ k)) : Measure (Torus d)) - ∫ x, v x ∂(η : Measure (Torus d))| <
        ε / 8 := by
      rw [← Real.dist_eq]; exact h1
    have := hφε (ψ k)
    have e1 := hclose (ν (m (ψ k)))
    have e2 := hclose η
    have : |∫ x, φ (ψ k) x ∂(ν (m (ψ k)) : Measure (Torus d)) - ∫ x, φ (ψ k) x ∂(η : Measure (Torus d))|
        ≤ ε / 8 + ε / 8 + ε / 8 := by
      calc _ = |(∫ x, φ (ψ k) x ∂(ν (m (ψ k)) : Measure (Torus d)) -
              ∫ x, v x ∂(ν (m (ψ k)) : Measure (Torus d))) +
            (∫ x, v x ∂(ν (m (ψ k)) : Measure (Torus d)) - ∫ x, v x ∂(η : Measure (Torus d))) -
            (∫ x, φ (ψ k) x ∂(η : Measure (Torus d)) - ∫ x, v x ∂(η : Measure (Torus d)))| := by
            ring_nf
        _ ≤ _ := by
            refine (abs_sub _ _).trans ?_
            refine add_le_add ((abs_add_le _ _).trans (add_le_add e1 hv1.le)) e2
    linarith
  · intro hR
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    rintro f ⟨C, hC⟩ ⟨L, hL⟩
    have hfc := hL.continuous
    have hbf : ∀ x, |f x| ≤ |f 0| + C := fun x => by
      have := hC x 0; rw [Real.dist_eq] at this
      have := abs_sub_abs_le_abs_sub (f x) (f 0); linarith
    have hfi : ∀ ρ : ProbabilityMeasure (Torus d), Integrable f (ρ : Measure (Torus d)) := fun ρ =>
      Integrable.of_bound hfc.aestronglyMeasurable (|f 0| + C)
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hbf x)
    set c : ℝ := (L : ℝ) + 1
    have hc : 0 < c := by positivity
    set φ : Torus d → ℝ := fun x => (f x - f 0) / c
    have hφ : FlatLipschitzWith 1 φ := fun x y => by
      simp only [φ, one_mul]
      rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hc, div_le_iff₀ hc]
      have h1 := hL.dist_le_mul x y
      rw [Real.dist_eq] at h1
      have h2 := (flatDist_comparison x y).1
      have h3 : (0 : ℝ) ≤ flatDist x y := le_trans dist_nonneg h2
      have h4 : (L : ℝ) * dist x y ≤ L * flatDist x y := mul_le_mul_of_nonneg_left h2 L.2
      nlinarith
    have hφ0 : φ 0 = 0 := by simp [φ]
    have hrep : ∀ ρ : ProbabilityMeasure (Torus d), ∫ x, f x ∂(ρ : Measure (Torus d)) =
        c * ∫ x, φ x ∂(ρ : Measure (Torus d)) + f 0 := fun ρ => by
      simp only [φ]
      rw [integral_div, integral_sub (hfi ρ) (integrable_const _)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      field_simp
      ring
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hR.const_mul c)
    rw [hrep, hrep, Real.norm_eq_abs]
    have := hmem (ν n) η φ hφ hφ0
    calc |c * ∫ x, φ x ∂(ν n : Measure (Torus d)) + f 0 - (c * ∫ x, φ x ∂(η : Measure (Torus d)) + f 0)|
        = c * |∫ x, φ x ∂(ν n : Measure (Torus d)) - ∫ x, φ x ∂(η : Measure (Torus d))| := by
          rw [← abs_of_pos hc, ← abs_mul, abs_of_pos hc]; ring_nf
      _ ≤ c * dLipAux (ν n) η := mul_le_mul_of_nonneg_left this hc.le
end SharpLSI
