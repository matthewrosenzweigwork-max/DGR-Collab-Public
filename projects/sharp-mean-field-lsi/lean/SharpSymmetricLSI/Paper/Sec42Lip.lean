import SharpSymmetricLSI.Paper.AppAWeak5
import SharpSymmetricLSI.Paper.AppAEvol2
import SharpSymmetricLSI.Paper.DensMeasure

/-!
# Section 4.2 (lane s42; R15): the dual Lipschitz distance

Elementary properties of `d_Lip` (D19) used in the contraction argument: it is a metric on
`𝒫(𝕋^d)` (`dLip_comm`, `dLip_triangle`, `eq_of_dLip_eq_zero`), and it is bounded by `√d`
times the `L¹` distance of densities (`dLip_le_L1`).
-/

open MeasureTheory Filter Topology

namespace SharpLSI

variable {d : ℕ}

theorem abs_le_sqrt_of_flatLip {φ : Torus d → ℝ} (hφ : FlatLipschitzWith 1 φ) (h0 : φ 0 = 0)
    (x : Torus d) : |φ x| ≤ Real.sqrt d := by
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

theorem lipschitz_of_flatLip {φ : Torus d → ℝ} (hφ : FlatLipschitzWith 1 φ) :
    LipschitzWith ⟨Real.sqrt d, Real.sqrt_nonneg _⟩ φ := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq]
  refine (hφ x y).trans ?_
  rw [one_mul]
  exact (flatDist_comparison x y).2.trans (le_of_eq (by rw [Fintype.card_fin]; rfl))

theorem integrable_flatLip (ρ : Measure (Torus d)) [IsFiniteMeasure ρ] {φ : Torus d → ℝ}
    (hφ : FlatLipschitzWith 1 φ) (h0 : φ 0 = 0) : Integrable φ ρ :=
  Integrable.of_bound (lipschitz_of_flatLip hφ).continuous.aestronglyMeasurable (Real.sqrt d)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_le_sqrt_of_flatLip hφ h0 x)

theorem abs_integral_flatLip_le (ρ : ProbabilityMeasure (Torus d)) {φ : Torus d → ℝ}
    (hφ : FlatLipschitzWith 1 φ) (h0 : φ 0 = 0) :
    |∫ x, φ x ∂(ρ : Measure (Torus d))| ≤ Real.sqrt d := by
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ x, |φ x| ∂(ρ : Measure (Torus d)) ≤ ∫ _x, Real.sqrt d ∂(ρ : Measure (Torus d)) :=
        integral_mono (integrable_flatLip _ hφ h0).abs (integrable_const _)
          fun x => abs_le_sqrt_of_flatLip hφ h0 x
    _ = Real.sqrt d := by simp

theorem bddAbove_dLip (ν η : ProbabilityMeasure (Torus d)) :
    BddAbove {s | ∃ φ : Torus d → ℝ, FlatLipschitzWith 1 φ ∧ φ 0 = 0 ∧
      s = |∫ x, φ x ∂(ν : Measure (Torus d)) - ∫ x, φ x ∂(η : Measure (Torus d))|} := by
  refine ⟨2 * Real.sqrt d, ?_⟩
  rintro s ⟨φ, hφ, h0, rfl⟩
  have := abs_sub _ _ |>.trans (add_le_add (abs_integral_flatLip_le ν hφ h0)
    (abs_integral_flatLip_le η hφ h0))
  linarith

theorem le_dLip (ν η : ProbabilityMeasure (Torus d)) {φ : Torus d → ℝ}
    (hφ : FlatLipschitzWith 1 φ) (h0 : φ 0 = 0) :
    |∫ x, φ x ∂(ν : Measure (Torus d)) - ∫ x, φ x ∂(η : Measure (Torus d))| ≤ dLip ν η :=
  le_csSup (bddAbove_dLip ν η) ⟨φ, hφ, h0, rfl⟩

theorem flatLip_zero : FlatLipschitzWith 1 (fun _ : Torus d => (0 : ℝ)) := fun x y => by
  simp only [sub_self, abs_zero, one_mul]; exact Real.sqrt_nonneg _

theorem dLip_nonneg (ν η : ProbabilityMeasure (Torus d)) : 0 ≤ dLip ν η :=
  (abs_nonneg _).trans (le_dLip ν η flatLip_zero rfl)

theorem dLip_le_of {ν η : ProbabilityMeasure (Torus d)} {c : ℝ}
    (h : ∀ φ : Torus d → ℝ, FlatLipschitzWith 1 φ → φ 0 = 0 →
      |∫ x, φ x ∂(ν : Measure (Torus d)) - ∫ x, φ x ∂(η : Measure (Torus d))| ≤ c) :
    dLip ν η ≤ c :=
  csSup_le ⟨_, ⟨_, flatLip_zero, rfl, rfl⟩⟩ fun s ⟨φ, hφ, h0, hs⟩ => hs ▸ h φ hφ h0

theorem dLip_comm (ν η : ProbabilityMeasure (Torus d)) : dLip ν η = dLip η ν := by
  refine le_antisymm (dLip_le_of fun φ hφ h0 => ?_) (dLip_le_of fun φ hφ h0 => ?_)
  · rw [abs_sub_comm]; exact le_dLip η ν hφ h0
  · rw [abs_sub_comm]; exact le_dLip ν η hφ h0

theorem dLip_triangle (ν η ξ : ProbabilityMeasure (Torus d)) :
    dLip ν ξ ≤ dLip ν η + dLip η ξ := by
  refine dLip_le_of fun φ hφ h0 => ?_
  have h1 := le_dLip ν η hφ h0
  have h2 := le_dLip η ξ hφ h0
  calc |∫ x, φ x ∂(ν : Measure (Torus d)) - ∫ x, φ x ∂(ξ : Measure (Torus d))|
      = |(∫ x, φ x ∂(ν : Measure (Torus d)) - ∫ x, φ x ∂(η : Measure (Torus d))) +
          (∫ x, φ x ∂(η : Measure (Torus d)) - ∫ x, φ x ∂(ξ : Measure (Torus d)))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)

theorem dLip_self (ν : ProbabilityMeasure (Torus d)) : dLip ν ν = 0 :=
  le_antisymm (dLip_le_of fun φ _ _ => by simp) (dLip_nonneg ν ν)

/-- `d_Lip(νₙ, η) ≤ bₙ → 0` implies `νₙ → η`. -/
theorem tendsto_of_dLip_le {ν : ℕ → ProbabilityMeasure (Torus d)} {η : ProbabilityMeasure (Torus d)}
    {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0)) (h : ∀ n, dLip (ν n) η ≤ b n) :
    Tendsto ν atTop (𝓝 η) :=
  (dLip_metrizes ν η).2 (squeeze_zero (fun n => dLip_nonneg _ _) h hb)

theorem eq_of_dLip_eq_zero {ν η : ProbabilityMeasure (Torus d)} (h : dLip ν η = 0) : ν = η := by
  have := tendsto_of_dLip_le (ν := fun _ => ν) (η := η) (b := fun _ => 0) tendsto_const_nhds
    (fun _ => h.le)
  exact tendsto_nhds_unique tendsto_const_nhds this

/-- `d_Lip` of two densities is at most `√d` times their `L¹` distance. -/
theorem dLip_le_L1 {ν η : ProbabilityMeasure (Torus d)} {f g : Torus d → ℝ}
    (hν : (ν : Measure (Torus d)) = densMeasure f) (hη : (η : Measure (Torus d)) = densMeasure g)
    (hf : Integrable f (haar d)) (hg : Integrable g (haar d))
    (hf0 : ∀ᵐ x ∂haar d, 0 ≤ f x) (hg0 : ∀ᵐ x ∂haar d, 0 ≤ g x) :
    dLip ν η ≤ Real.sqrt d * ∫ x, |f x - g x| ∂haar d := by
  set f' := hf.1.mk f
  set g' := hg.1.mk g
  have hff : f =ᵐ[haar d] f' := hf.1.ae_eq_mk
  have hgg : g =ᵐ[haar d] g' := hg.1.ae_eq_mk
  have hfm : Measurable f' := hf.1.stronglyMeasurable_mk.measurable
  have hgm : Measurable g' := hg.1.stronglyMeasurable_mk.measurable
  have hf0' : ∀ᵐ x ∂haar d, 0 ≤ f' x := by filter_upwards [hf0, hff] with x h1 h2; rwa [← h2]
  have hg0' : ∀ᵐ x ∂haar d, 0 ≤ g' x := by filter_upwards [hg0, hgg] with x h1 h2; rwa [← h2]
  have hfi : Integrable f' (haar d) := hf.congr hff
  have hgi : Integrable g' (haar d) := hg.congr hgg
  have e : ∫ x, |f x - g x| ∂haar d = ∫ x, |f' x - g' x| ∂haar d := by
    refine integral_congr_ae ?_
    filter_upwards [hff, hgg] with x h1 h2; rw [h1, h2]
  rw [e]
  refine dLip_le_of fun φ hφ h0 => ?_
  rw [hν, hη, densMeasure_congr_ae hff, densMeasure_congr_ae hgg,
    integral_densMeasure_ae hfm hf0' φ, integral_densMeasure_ae hgm hg0' φ]
  have hφm := (lipschitz_of_flatLip hφ).continuous.aestronglyMeasurable (μ := haar d)
  have hb : ∀ᵐ x ∂haar d, ‖φ x‖ ≤ Real.sqrt d :=
    Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_le_sqrt_of_flatLip hφ h0 x
  have i1 : Integrable (fun x => φ x * f' x) (haar d) := hfi.bdd_mul hφm hb
  have i2 : Integrable (fun x => φ x * g' x) (haar d) := hgi.bdd_mul hφm hb
  rw [← integral_sub i1 i2]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono (i1.sub i2).abs ((hfi.sub hgi).abs.const_mul _) fun x => ?_
  show |φ x * f' x - φ x * g' x| ≤ Real.sqrt d * |f' x - g' x|
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (abs_le_sqrt_of_flatLip hφ h0 x) (abs_nonneg _)

end SharpLSI
