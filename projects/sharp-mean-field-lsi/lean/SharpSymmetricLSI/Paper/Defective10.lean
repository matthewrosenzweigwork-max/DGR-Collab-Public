import SharpSymmetricLSI.Paper.Defective9

/-!
# R03 (Proposition 2.2), part 10: the explicit ratio is the conditional expectation

For bounded measurable `F`, `condRatio F (past X) (X_j) = ν[F | ℱ_j ∨ σ(X_j)]` `ν`-a.e.
(`condRatio_ae_eq_condExp`), by the defining property of `condExp` on the generating sets
`{(past, X_j) ∈ T}` and the block disintegration (`integral_assemble`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d N : ℕ}

section cexp
variable {j : ℕ} (hj : j < N)

theorem integral_assemble {G : Config N d → ℝ} (hG : Integrable G volume) :
    ∫ X, G X = ∫ q : Config j d × Torus d, ∫ z, G (assemble hj q.1 q.2 z)
      ∂(volume : Measure (Config (N - j - 1) d)) ∂((volume : Measure (Config j d)).prod volume) := by
  have hmp := measurePreserving_assemble (d := d) hj
  have hGi := hmp.integrable_comp_of_integrable hG
  rw [← MeasurePreserving.integral_comp' (f := assembleEquiv hj) hmp G]
  exact integral_prod (fun q : (Config j d × Torus d) × Config (N - j - 1) d =>
    G (assemble hj q.1.1 q.1.2 q.2)) hGi

variable {Q : Config N d → ℝ} (hQm : Measurable Q) {c C : ℝ} (hc : 0 < c) (hQc : ∀ X, c ≤ Q X)
  (hQC : ∀ X, Q X ≤ C)

include hQm hc hQc hQC in
theorem abs_condRatio_le {F : Config N d → ℝ} (hFm : Measurable F) {B : ℝ} (hFB : ∀ X, |F X| ≤ B)
    (p : Config j d) (x : Torus d) : |condRatio hj Q F p x| ≤ B := by
  have hQ0 : ∀ X, 0 ≤ Q X := fun X => hc.le.trans (hQc X)
  have hzm : Measurable fun z : Config (N - j - 1) d => assemble hj p x z :=
    (measurable_assemble hj).comp ((measurable_const (a := (p, x))).prodMk measurable_id)
  have hm : 0 < margQ hj Q p x := hc.trans_le (margQ_bounds hj hQm hQc hQC p x).1
  have hQi : Integrable (fun z => Q (assemble hj p x z)) (volume : Measure (Config (N - j - 1) d)) :=
    Integrable.of_bound (hQm.comp hzm).aestronglyMeasurable C (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hQ0 _)]; exact hQC _)
  unfold condRatio
  rw [abs_div, abs_of_pos hm, div_le_iff₀ hm]
  calc |∫ z, F (assemble hj p x z) * Q (assemble hj p x z) ∂(volume : Measure (Config (N - j - 1) d))|
      ≤ ∫ z, |F (assemble hj p x z) * Q (assemble hj p x z)|
          ∂(volume : Measure (Config (N - j - 1) d)) := abs_integral_le_integral_abs
    _ ≤ ∫ z, B * Q (assemble hj p x z) ∂(volume : Measure (Config (N - j - 1) d)) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
          (hQi.const_mul B) (Eventually.of_forall fun z => ?_)
        show |F _ * Q _| ≤ B * Q _
        rw [abs_mul, abs_of_nonneg (hQ0 _)]
        exact mul_le_mul_of_nonneg_right (hFB _) (hQ0 _)
    _ = B * margQ hj Q p x := by rw [integral_const_mul]; rfl

include hQm hc hQc hQC in
/-- **`condRatio` is the conditional expectation.** -/
theorem condRatio_ae_eq_condExp
    [IsProbabilityMeasure ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X))]
    {F : Config N d → ℝ} (hFm : Measurable F) {B : ℝ} (hFB : ∀ X, |F X| ≤ B) :
    (fun X => condRatio hj Q F (past j hj.le X) (X ⟨j, hj⟩)) =ᵐ[(volume : Measure (Config N d)).withDensity
      fun X => ENNReal.ofReal (Q X)]
      ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X))[F | pastNextSA j hj] := by
  set ν := (volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (Q X)
  have hQ0 : ∀ X, 0 ≤ Q X := fun X => hc.le.trans (hQc X)
  have hπ : Measurable fun X : Config N d => (past j hj.le X, X ⟨j, hj⟩) :=
    (measurable_past hj.le).prodMk (measurable_pi_apply _)
  have hm : pastNextSA (d := d) j hj ≤ MeasurableSpace.pi := measurable_iff_comap_le.mp hπ
  have hR := measurable_condRatio hj hQm hFm
  have hRb := abs_condRatio_le hj hQm hc hQc hQC hFm hFB
  have hFi : Integrable F ν := Integrable.of_bound hFm.aestronglyMeasurable B
    (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hFB X)
  have hgm : Measurable[pastNextSA j hj] fun X : Config N d =>
      condRatio hj Q F (past j hj.le X) (X ⟨j, hj⟩) :=
    hR.comp (measurable_iff_comap_le.mpr le_rfl)
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hFi (fun s _ _ => ?_) (fun s hs _ => ?_)
    hgm.aestronglyMeasurable
  · exact (Integrable.of_bound (hgm.mono hm le_rfl).aestronglyMeasurable B
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hRb _ _)).integrableOn
  · obtain ⟨T, hT, rfl⟩ := hs
    rw [← integral_indicator (hπ hT), ← integral_indicator (hπ hT)]
    simp only [ν]
    rw [integral_withDensity_eq_integral_toReal_smul (f := fun X => ENNReal.ofReal (Q X))
        (ENNReal.measurable_ofReal.comp hQm) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul (f := fun X => ENNReal.ofReal (Q X))
        (ENNReal.measurable_ofReal.comp hQm) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hQ0 _), smul_eq_mul]
    have hind : ∀ (G : Config N d → ℝ) (X : Config N d),
        ((fun X => (past j hj.le X, X ⟨j, hj⟩)) ⁻¹' T).indicator G X =
          T.indicator 1 (past j hj.le X, X ⟨j, hj⟩) * G X := fun G X => by
      by_cases h : (past j hj.le X, X ⟨j, hj⟩) ∈ T <;> simp [Set.indicator, h]
    simp_rw [hind]
    have hTm : Measurable (T.indicator (1 : Config j d × Torus d → ℝ)) :=
      measurable_const.indicator hT
    have bnd : ∀ (G : Config N d → ℝ), Measurable G → (∀ X, |G X| ≤ B) →
        Integrable (fun X => Q X * (T.indicator 1 (past j hj.le X, X ⟨j, hj⟩) * G X)) volume :=
      fun G hGm hGB => Integrable.of_bound ((hQm.mul ((hTm.comp hπ).mul hGm)).aestronglyMeasurable)
        (C * B) (Eventually.of_forall fun X => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hQ0 X)]
          have h1 : |T.indicator (1 : Config j d × Torus d → ℝ) (past j hj.le X, X ⟨j, hj⟩)| ≤ 1 := by
            by_cases h : (past j hj.le X, X ⟨j, hj⟩) ∈ T <;> simp [Set.indicator, h]
          have h2 := hGB X
          have h3 := hQC X
          calc Q X * (|T.indicator 1 (past j hj.le X, X ⟨j, hj⟩)| * |G X|) ≤ C * (1 * B) :=
                mul_le_mul h3 (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one)
                  (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ((hQ0 X).trans h3)
          _ = C * B := by ring)
    rw [integral_assemble hj (bnd (fun X => condRatio hj Q F (past j hj.le X) (X ⟨j, hj⟩))
        (hR.comp hπ) fun X => hRb _ _),
      integral_assemble hj (bnd _ hFm hFB)]
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    simp only [past_assemble, cur_assemble]
    have hzm : Measurable fun z : Config (N - j - 1) d => assemble hj q.1 q.2 z :=
      (measurable_assemble hj).comp ((measurable_const (a := q)).prodMk measurable_id)
    have e1 : ∫ z, Q (assemble hj q.1 q.2 z) * (T.indicator 1 q * condRatio hj Q F q.1 q.2)
        ∂(volume : Measure (Config (N - j - 1) d)) =
        T.indicator 1 q * condRatio hj Q F q.1 q.2 * margQ hj Q q.1 q.2 := by
      simp_rw [mul_comm (Q _)]
      rw [integral_const_mul]; rfl
    have e2 : ∫ z, Q (assemble hj q.1 q.2 z) * (T.indicator 1 q * F (assemble hj q.1 q.2 z))
        ∂(volume : Measure (Config (N - j - 1) d)) =
        T.indicator 1 q * ∫ z, F (assemble hj q.1 q.2 z) * Q (assemble hj q.1 q.2 z)
          ∂(volume : Measure (Config (N - j - 1) d)) := by
      rw [← integral_const_mul]
      congr 1; funext z; ring
    have hm0 : 0 < margQ hj Q q.1 q.2 := hc.trans_le (margQ_bounds hj hQm hQc hQC q.1 q.2).1
    rw [e1, e2, condRatio, mul_assoc, div_mul_cancel₀ _ hm0.ne']

end cexp

end SharpLSI
