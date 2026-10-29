import SharpSymmetricLSI.Paper.GaussForm7

/-!
# R32 (B3): the generator in `L²(γ)` and the closability inequality

* `memLp_gen`: `L c ∈ L²(γ)`.
* `Cyl.formR`: the form of a cylinder as a real number; `form = ofReal formR` for `λ ≥ 0`.
* `two_mul_le_formR`: `2 ∫ u(-Lc) ≤ ℰ(u) + ℰ(c)` for `λ ≥ 0` (Cauchy–Schwarz pointwise).
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ContDiff ENNReal

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ}

theorem memLp_coord_gamma (hγ : IsCenteredGaussianCov γ C) (q : ℕ) :
    MemLp (fun z : ℕ → ℝ => z q) 2 γ := by
  haveI := hγ.1
  have h := hγ.2 {q} (fun _ => 1)
  simp only [Finset.sum_singleton, one_mul] at h
  have hm : Measurable fun z : ℕ → ℝ => z q := measurable_pi_apply q
  have hi : MemLp id 2 (γ.map fun z : ℕ → ℝ => z q) := by
    rw [h]; exact memLp_id_gaussianReal' 2 (by norm_num)
  exact (memLp_map_measure_iff aestronglyMeasurable_id hm.aemeasurable).1 hi

theorem memLp_of_bdd {f : (ℕ → ℝ) → ℝ} [IsFiniteMeasure γ] (hf : Measurable f) {B : ℝ}
    (hB : ∀ z, |f z| ≤ B) : MemLp f 2 γ :=
  MemLp.of_bound hf.aestronglyMeasurable B (Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hB z)

/-- **`L c ∈ L²(γ)`.** -/
theorem memLp_gen {T : ℕ → ℕ → ℝ} (hγ : IsCenteredGaussianCov γ C) {Y : ℕ → (ℕ → ℝ) → ℝ}
    (hY : ∀ i, IsRowVariable T γ i (Y i)) (lam' : ℕ → ℝ) (c : Cyl) :
    MemLp (c.gen lam' Y) 2 γ := by
  haveI := hγ.1
  have e : c.gen lam' Y = fun z => ∑ i : Fin c.J, lam' i * (c.dd2 i z - (z i + Y i z) * c.dd i z) := by
    funext z
    unfold Cyl.gen
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [c.dd_of_lt i.isLt]; rfl
  rw [e]
  refine memLp_finsetSum (ε' := ℝ) _ fun i _ => ?_
  obtain ⟨B2, hB2⟩ := c.exists_dd2_bound i
  obtain ⟨B1, hB1⟩ := c.exists_dd_bound
  have h1 : MemLp (c.dd2 i) 2 γ := memLp_of_bdd (c.measurable_dd2 i) hB2
  have hzY : MemLp (fun z => z i + Y i z) 2 γ := (memLp_coord_gamma hγ i).add (hY i).1
  have h2 : MemLp (fun z => (z i + Y i z) * c.dd i z) 2 γ :=
    hzY.of_le_mul (c := B1) (hzY.aestronglyMeasurable.mul (c.measurable_dd i).aestronglyMeasurable)
      (Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hB1 i z) (abs_nonneg _))
  exact (h1.sub h2).const_mul _

/-- The form of a cylinder, as a real number. -/
noncomputable def Cyl.formR (lam' : ℕ → ℝ) (γ : Measure (ℕ → ℝ)) (c : Cyl) : ℝ :=
  ∫ z, ∑ i : Fin c.J, lam' i * c.dd i z ^ 2 ∂γ

theorem Cyl.integrable_sum_sq [IsProbabilityMeasure γ] (lam' : ℕ → ℝ) (u : Cyl) (K : ℕ) :
    Integrable (fun z => ∑ i ∈ Finset.range K, lam' i * u.dd i z ^ 2) γ := by
  obtain ⟨B, hB⟩ := u.exists_dd_bound
  refine integrable_finsetSum _ fun i _ => ?_
  refine (integrable_of_bdd_gamma ((u.measurable_dd i).pow_const 2) (B := B ^ 2) fun z => ?_).const_mul _
  rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB i z) 2

theorem Cyl.sum_fin_eq_range (lam' : ℕ → ℝ) (u : Cyl) (K : ℕ) (z : ℕ → ℝ) :
    ∑ i : Fin K, lam' i * u.dd i z ^ 2 = ∑ i ∈ Finset.range K, lam' i * u.dd i z ^ 2 :=
  Fin.sum_univ_eq_sum_range (fun i => lam' i * u.dd i z ^ 2) K

theorem Cyl.form_eq_ofReal [IsProbabilityMeasure γ] {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i)
    (c : Cyl) : c.form lam' γ = ENNReal.ofReal (c.formR lam' γ) := by
  unfold Cyl.form Cyl.formR
  have e : ∀ z, ∑ i : Fin c.J, lam' i * (fderiv ℝ c.φ (fun j => z j) (Pi.single i 1)) ^ 2 =
      ∑ i : Fin c.J, lam' i * c.dd i z ^ 2 := fun z =>
    Finset.sum_congr rfl fun i _ => by rw [c.dd_of_lt i.isLt]; rfl
  simp_rw [e]
  rw [ofReal_integral_eq_lintegral_ofReal]
  · simp_rw [c.sum_fin_eq_range]; exact c.integrable_sum_sq lam' c.J
  · exact Eventually.of_forall fun z => Finset.sum_nonneg fun i _ => mul_nonneg (hlam i) (sq_nonneg _)

/-- The sum over the first `K` coordinates is at most the full form (`∂_i u = 0` for `i ≥ J_u`). -/
theorem Cyl.sum_range_le (lam' : ℕ → ℝ) (hlam : ∀ i, 0 ≤ lam' i) (u : Cyl) (K : ℕ) (z : ℕ → ℝ) :
    ∑ i ∈ Finset.range K, lam' i * u.dd i z ^ 2 ≤ ∑ i ∈ Finset.range u.J, lam' i * u.dd i z ^ 2 := by
  have hz : ∀ i, u.J ≤ i → lam' i * u.dd i z ^ 2 = 0 := fun i hi => by
    simp [Cyl.dd, not_lt.2 hi]
  calc ∑ i ∈ Finset.range K, lam' i * u.dd i z ^ 2
      ≤ ∑ i ∈ Finset.range (u.J + K), lam' i * u.dd i z ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          fun i _ _ => mul_nonneg (hlam i) (sq_nonneg _)
    _ = ∑ i ∈ Finset.range u.J, lam' i * u.dd i z ^ 2 := by
        rw [Finset.sum_range_add]
        simp [hz]

variable {T : ℕ → ℕ → ℝ}

/-- `∫ c(-Lc) dγ = ℰ(c)`. -/
theorem cyl_ibp_self (hγ : IsCenteredGaussianCov γ C) (hPSD : ∀ N, (blockMat C N).PosSemidef)
    (hC : IsInverseOfIPlus T C) {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i))
    (lam' : ℕ → ℝ) (c : Cyl) :
    ∫ z, c.eval z * (-(c.gen lam' Y z)) ∂γ = c.formR lam' γ := by
  haveI := hγ.1
  rw [cyl_ibp hγ hPSD hC hY lam' c c, Cyl.formR, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_const_mul]; congr 1; funext z; ring
  · intro i _
    obtain ⟨B, hB⟩ := c.exists_dd_bound
    refine (integrable_of_bdd_gamma ((c.measurable_dd i).pow_const 2) (B := B ^ 2) fun z => ?_).const_mul _
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB i z) 2

/-- **The closability inequality** `2 ∫ u(-Lc) ≤ ℰ(u) + ℰ(c)`. -/
theorem two_mul_le_formR (hγ : IsCenteredGaussianCov γ C) (hPSD : ∀ N, (blockMat C N).PosSemidef)
    (hC : IsInverseOfIPlus T C) {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i))
    {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (u c : Cyl) :
    2 * ∫ z, u.eval z * (-(c.gen lam' Y z)) ∂γ ≤ u.formR lam' γ + c.formR lam' γ := by
  haveI := hγ.1
  rw [cyl_ibp hγ hPSD hC hY lam' u c]
  obtain ⟨Bu, hBu⟩ := u.exists_dd_bound
  obtain ⟨Bc, hBc⟩ := c.exists_dd_bound
  have hi : ∀ i : Fin c.J, Integrable (fun z => u.dd i z * c.dd i z) γ := fun i =>
    integrable_of_bdd_gamma ((u.measurable_dd i).mul (c.measurable_dd i)) (B := Bu * Bc) fun z => by
      rw [abs_mul]; exact mul_le_mul (hBu i z) (hBc i z) (abs_nonneg _) ((abs_nonneg _).trans (hBu i z))
  have hL : 2 * ∑ i : Fin c.J, lam' i * ∫ z, u.dd i z * c.dd i z ∂γ =
      ∫ z, 2 * ∑ i : Fin c.J, lam' i * (u.dd i z * c.dd i z) ∂γ := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ => (hi i).const_mul _]
    congr 1; exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
  rw [hL, Cyl.formR, Cyl.formR, ← integral_add]
  · refine integral_mono ?_ ?_ fun z => ?_
    · exact (integrable_finsetSum _ fun i _ => (hi i).const_mul _).const_mul _
    · simp_rw [u.sum_fin_eq_range, c.sum_fin_eq_range]
      exact (u.integrable_sum_sq lam' u.J).add (c.integrable_sum_sq lam' c.J)
    · simp only
      rw [u.sum_fin_eq_range, c.sum_fin_eq_range]
      have h1 : 2 * ∑ i : Fin c.J, lam' i * (u.dd i z * c.dd i z) ≤
          ∑ i ∈ Finset.range c.J, lam' i * u.dd i z ^ 2 +
            ∑ i ∈ Finset.range c.J, lam' i * c.dd i z ^ 2 := by
        rw [Fin.sum_univ_eq_sum_range (fun i => lam' i * (u.dd i z * c.dd i z)), Finset.mul_sum,
          ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        nlinarith [mul_nonneg (hlam i) (sq_nonneg (u.dd i z - c.dd i z))]
      linarith [u.sum_range_le lam' hlam c.J z]
  · simp_rw [u.sum_fin_eq_range]; exact u.integrable_sum_sq lam' u.J
  · simp_rw [c.sum_fin_eq_range]; exact c.integrable_sum_sq lam' c.J

end SharpLSI
