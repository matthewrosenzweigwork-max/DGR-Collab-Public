import SharpSymmetricLSI.Paper.LocalStructure3

/-!
# Section 4.2: finite dimension of `ker(I + T)` and an orthonormal basis (Phase 3, lane D; R14)
-/

noncomputable section
open MeasureTheory InformationTheory Filter Real Topology BoundedContinuousFunction
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

section fd
variable (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
include hyp

theorem integrable_bcf (u : Torus d →ᵇ ℝ) : Integrable (⇑u) μ :=
  integrable_of_bdd u.continuous.measurable (C := ‖u‖) fun x => by
    rw [← Real.norm_eq_abs]; exact u.norm_coe_le_norm x

theorem memL20_of_ker {u : Torus d →ᵇ ℝ} (hu : u ∈ kerSpace hyp μ) : MemL20 μ (⇑u) :=
  ⟨MemLp.of_bound u.continuous.aestronglyMeasurable ‖u‖ (Eventually.of_forall fun x =>
    u.norm_coe_le_norm x), hu.2⟩

/-- `Top` is continuous under bounded pointwise convergence. -/
theorem tendsto_Top {fs : ℕ → Torus d → ℝ} {f : Torus d → ℝ} (hfm : ∀ n, Measurable (fs n))
    {B : ℝ} (hB : ∀ n x, |fs n x| ≤ B) (hlim : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (x : Torus d) : Tendsto (fun n => Top W μ (fs n) x) atTop (𝓝 (Top W μ f x)) := by
  obtain ⟨BW, hBW⟩ := exists_bound_of_continuous (X := Torus d × Torus d) hyp.continuous_W
  have hBW0 : 0 ≤ BW := (abs_nonneg _).trans (hBW 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 0)
  have ta : ∀ x, Tendsto (fun n => ∫ y, W x y * fs n y ∂μ) atTop (𝓝 (∫ y, W x y * f y ∂μ)) :=
    fun x => tendsto_integral_of_dominated_convergence (fun _ => BW * B)
      (fun n => ((hyp.continuous_W.measurable.comp measurable_prodMk_left).mul
        (hfm n)).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul (hBW (x, y)) (hB n y) (abs_nonneg _) hBW0)
      (Eventually.of_forall fun y => (hlim y).const_mul _)
  have tb : Tendsto (fun n => ∫ x', (∫ y, W x' y * fs n y ∂μ) ∂μ) atTop
      (𝓝 (∫ x', (∫ y, W x' y * f y ∂μ) ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun _ => BW * B)
      (fun n => aW_aesm hyp μ (hfm n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x' => by
        rw [Real.norm_eq_abs]
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ y, |W x' y * fs n y| ∂μ ≤ ∫ _y, BW * B ∂μ :=
              integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
                (integrable_const _) (Eventually.of_forall fun y => by
                  show |W x' y * fs n y| ≤ BW * B
                  rw [abs_mul]; exact mul_le_mul (hBW (x', y)) (hB n y) (abs_nonneg _) hBW0)
          _ = BW * B := by simp)
      (Eventually.of_forall ta)
  exact (ta x).sub tb

/-- **`ker(I+T)` is finite-dimensional** (Riesz). -/
theorem kerSpace_finiteDimensional : FiniteDimensional ℝ (kerSpace hyp μ) := by
  obtain ⟨C, hC⟩ := Top_W1inf hyp μ
  set L : NNReal := (max C 0).toNNReal
  refine FiniteDimensional.of_isCompact_closedBall₀ (𝕜 := ℝ) (V := kerSpace hyp μ) one_pos ?_
  refine IsSeqCompact.isCompact fun u hu => ?_
  -- uniform bounds
  have hb : ∀ n x, |(u n : Torus d →ᵇ ℝ) x| ≤ 1 := fun n x => by
    have h1 : ‖(u n : Torus d →ᵇ ℝ)‖ ≤ 1 := by
      have := Metric.mem_closedBall.mp (hu n)
      rw [Subtype.dist_eq, ZeroMemClass.coe_zero, dist_zero_right] at this
      exact this
    rw [← Real.norm_eq_abs]
    exact ((u n : Torus d →ᵇ ℝ).norm_coe_le_norm x).trans h1
  have hL : ∀ n, LipschitzWith L ((u n : Torus d →ᵇ ℝ) : Torus d → ℝ) := fun n => by
    have hmem := (u n).2
    have h20 := memL20_of_ker hyp μ hmem
    have hT := (hC _ h20).2
    have he : ((u n : Torus d →ᵇ ℝ) : Torus d → ℝ) = fun x => -Top W μ (u n : Torus d →ᵇ ℝ) x :=
      funext fun x => by linarith [hmem.1 x]
    have hsq : Real.sqrt (∫ y, (u n : Torus d →ᵇ ℝ) y ^ 2 ∂μ) ≤ 1 := by
      rw [Real.sqrt_le_one]
      calc ∫ y, (u n : Torus d →ᵇ ℝ) y ^ 2 ∂μ ≤ ∫ _y, (1 : ℝ) ∂μ :=
            integral_mono h20.1.integrable_sq (integrable_const _) fun y => by
              have := hb n y
              nlinarith [abs_nonneg ((u n : Torus d →ᵇ ℝ) y), sq_abs ((u n : Torus d →ᵇ ℝ) y)]
        _ = 1 := by simp
    rw [he]
    refine (hT.neg).weaken ?_
    refine Real.toNNReal_le_toNNReal ?_
    have := Real.sqrt_nonneg (∫ y, (u n : Torus d →ᵇ ℝ) y ^ 2 ∂μ)
    rcases le_total C 0 with hC0 | hC0
    · rw [max_eq_right hC0]; nlinarith
    · rw [max_eq_left hC0]; nlinarith
  obtain ⟨φ, hφ, v, hv, hunif⟩ := exists_subseq_unif (fun n => ((u n : Torus d →ᵇ ℝ) : Torus d → ℝ))
    (C := 1) hb hL
  have hlim : ∀ x, Tendsto (fun n => (u (φ n) : Torus d →ᵇ ℝ) x) atTop (𝓝 (v x)) := fun x => by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif (ε / 2) (by positivity))
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; linarith [hN n hn x]⟩
  have hvb : ∀ x, |v x| ≤ 1 := fun x => by
    have := (continuous_abs.tendsto _).comp (hlim x)
    exact le_of_tendsto' this fun n => hb (φ n) x
  set v' : Torus d →ᵇ ℝ := mkOfCompact ⟨v, hv⟩
  have hv'mem : v' ∈ kerSpace hyp μ := by
    refine ⟨fun x => ?_, ?_⟩
    · have t := (hlim x).add (tendsto_Top hyp μ (fs := fun n => ((u (φ n) : Torus d →ᵇ ℝ) :
        Torus d → ℝ)) (fun n => (u (φ n) : Torus d →ᵇ ℝ).continuous.measurable)
        (fun n => hb (φ n)) hlim x)
      have hz : ∀ n, (u (φ n) : Torus d →ᵇ ℝ) x + Top W μ (u (φ n) : Torus d →ᵇ ℝ) x = 0 :=
        fun n => (u (φ n)).2.1 x
      simp_rw [hz] at t
      show v x + Top W μ v x = 0
      exact tendsto_nhds_unique t tendsto_const_nhds
    · have t := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
        (fun n => (u (φ n) : Torus d →ᵇ ℝ).continuous.aestronglyMeasurable) (integrable_const _)
        (fun n => Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb (φ n) x)
        (Eventually.of_forall hlim)
      have hz : ∀ n, ∫ x, (u (φ n) : Torus d →ᵇ ℝ) x ∂μ = 0 := fun n => (u (φ n)).2.2
      simp_rw [hz] at t
      show ∫ x, v x ∂μ = 0
      exact tendsto_nhds_unique t tendsto_const_nhds
  refine ⟨⟨v', hv'mem⟩, ?_, φ, hφ, ?_⟩
  · rw [Metric.mem_closedBall, Subtype.dist_eq, ZeroMemClass.coe_zero, dist_zero_right]
    exact (norm_le (f := v') zero_le_one).mpr fun x => by
      rw [Real.norm_eq_abs]; exact hvb x
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif (ε / 2) (by positivity))
    refine ⟨N, fun n hn => ?_⟩
    show dist ((u (φ n) : Torus d →ᵇ ℝ)) v' < ε
    refine lt_of_le_of_lt ((dist_le (C := ε / 2) (by positivity)).mpr fun x => ?_) (by linarith)
    rw [Real.dist_eq]; exact hN n hn x

end fd

end SharpLSI
