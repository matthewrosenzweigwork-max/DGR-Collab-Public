import SharpSymmetricLSI.Paper.Rothaus

/-!
# (5.18): the reference logarithmic Sobolev inequality (Phase 3, lane D; R22)

Holley–Stroock perturbation of the unit-torus inequality `lsi_torus_H1` (constant `4π² ≥ 1`):
`Ent_P(u) ≤ ∫ t klFun(u/t) dP` for every `t > 0`, so a density `p ≤ c₊` gives
`Ent_P(g²) ≤ c₊ Ent_haar(g²)`, and `p ≥ c₋` gives `∫|∇g|² dx ≤ c₋⁻¹ ∫|∇g|² dP`.
-/

noncomputable section
open MeasureTheory InformationTheory Filter
open scoped ENNReal Real

namespace SharpLSI

/-- Variational upper bound for the entropy: any reference level `t > 0` dominates. -/
theorem ent_le_shift {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {u : α → ℝ} (hu0 : ∀ x, 0 ≤ u x) (hui : Integrable u P) {t : ℝ} (ht : 0 < t) :
    ent P u ≤ ∫⁻ x, ENNReal.ofReal (t * klFun (u x / t)) ∂P := by
  unfold ent
  rw [if_pos hui]
  set m := ∫ y, u y ∂P with hmdef
  rcases (integral_nonneg hu0 : 0 ≤ m).eq_or_lt with h | hm
  · have hm0 : m = 0 := hmdef.trans h.symm
    rw [hm0]; simp
  by_cases hfin : ∫⁻ x, ENNReal.ofReal (t * klFun (u x / t)) ∂P = ⊤
  · rw [hfin]; exact le_top
  have hgm : AEStronglyMeasurable (fun x => t * klFun (u x / t)) P :=
    ((measurable_klFun.comp_aemeasurable (hui.1.aemeasurable.div_const t)).const_mul t
      ).aestronglyMeasurable
  have hg0 : 0 ≤ᵐ[P] fun x => t * klFun (u x / t) :=
    Eventually.of_forall fun x => mul_nonneg ht.le (klFun_nonneg (div_nonneg (hu0 x) ht.le))
  have hgi : Integrable (fun x => t * klFun (u x / t)) P :=
    (lintegral_ofReal_ne_top_iff_integrable hgm hg0).mp hfin
  have hBi : Integrable (fun x => u x * Real.log (t / m) + m - t) P :=
    ((hui.mul_const _).add (integrable_const m)).sub (integrable_const t)
  have hpt : ∀ x, m * klFun (u x / m) = t * klFun (u x / t) + (u x * Real.log (t / m) + m - t) :=
    fun x => klFun_shift hm ht (hu0 x)
  have hmi : Integrable (fun x => m * klFun (u x / m)) P := by
    simp_rw [hpt]; exact hgi.add hBi
  have hm0 : 0 ≤ᵐ[P] fun x => m * klFun (u x / m) :=
    Eventually.of_forall fun x => mul_nonneg hm.le (klFun_nonneg (div_nonneg (hu0 x) hm.le))
  rw [← ofReal_integral_eq_lintegral_ofReal hmi hm0, ← ofReal_integral_eq_lintegral_ofReal hgi hg0]
  refine ENNReal.ofReal_le_ofReal ?_
  have eB : ∫ x, (u x * Real.log (t / m) + m - t) ∂P = -(t * klFun (m / t)) := by
    rw [integral_sub (f := fun x => u x * Real.log (t / m) + m)
      ((hui.mul_const _).add (integrable_const m)) (integrable_const t),
      integral_add (f := fun x => u x * Real.log (t / m)) (hui.mul_const _) (integrable_const m),
      integral_mul_const]
    have := klFun_shift hm ht hm.le
    rw [← hmdef, div_self hm.ne', klFun_one, mul_zero] at this
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, ← hmdef]
    linarith
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hgi hBi, eB]
  linarith [mul_nonneg ht.le (klFun_nonneg (div_nonneg hm.le ht.le))]

variable {d : ℕ}

/-- **(5.18)** with `a_μ = c₋/c₊`. -/
theorem reference_lsi_aux {p : Torus d → ℝ} {cm cp : ℝ} (hcm : 0 < cm)
    (hp : ∀ x, cm ≤ p x ∧ p x ≤ cp) (hp1 : ∫ x, p x ∂haar d = 1) (hpm : Measurable p)
    {g : Torus d → ℝ} (hg : MemH1 ((haar d).withDensity fun x => ENNReal.ofReal (p x)) g) :
    ent ((haar d).withDensity fun x => ENNReal.ofReal (p x)) (fun x => g x ^ 2) ≤
      ENNReal.ofReal (2 / (cm / cp)) *
        dirichlet ((haar d).withDensity fun x => ENNReal.ofReal (p x)) g := by
  set P := (haar d).withDensity fun x => ENNReal.ofReal (p x) with hPdef
  obtain ⟨x0⟩ : Nonempty (Torus d) := inferInstance
  have hcp : 0 < cp := hcm.trans_le ((hp x0).1.trans (hp x0).2)
  have hpi : Integrable p (haar d) := Integrable.of_bound hpm.aestronglyMeasurable cp
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (hcm.trans_le (hp x).1)]; exact (hp x).2)
  haveI hPprob : IsProbabilityMeasure P := ⟨by
    rw [hPdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hpi
        (Eventually.of_forall fun x => hcm.le.trans (hp x).1), hp1, ENNReal.ofReal_one]⟩
  have hle : haar d ≤ ENNReal.ofReal (1 / cm) • P := by
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, hPdef, withDensity_apply _ hs]
    calc haar d s = ENNReal.ofReal (1 / cm) * (ENNReal.ofReal cm * haar d s) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hcm.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (1 / cm) * ∫⁻ x in s, ENNReal.ofReal (p x) ∂haar d := by
          gcongr
          rw [← setLIntegral_const]
          exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp x).1
  have hPle : P ≤ ENNReal.ofReal cp • haar d := by
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, hPdef, withDensity_apply _ hs, ← setLIntegral_const]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp x).2
  obtain ⟨hW, hL2, hG2⟩ := hg
  have hH1 : MemH1 (volume : Measure (Torus d)) g :=
    ⟨hW, hL2.of_measure_le_smul ENNReal.ofReal_ne_top hle,
      hG2.of_measure_le_smul ENNReal.ofReal_ne_top hle⟩
  have hiP : Integrable (fun x => g x ^ 2) P := hL2.integrable_sq
  have hiH : Integrable (fun x => g x ^ 2) (haar d) := hH1.2.1.integrable_sq
  set t := ∫ x, g x ^ 2 ∂haar d with htdef
  have hdir : dirichlet (haar d) g ≤ ENNReal.ofReal (1 / cm) * dirichlet P g := by
    unfold dirichlet
    rw [← smul_eq_mul, ← lintegral_smul_measure]
    exact lintegral_mono' hle le_rfl
  have hA : 1 ≤ aCos := by
    unfold aCos; nlinarith [Real.pi_gt_three]
  have hconst : ENNReal.ofReal cp * (ENNReal.ofReal (2 / aCos) * ENNReal.ofReal (1 / cm)) ≤
      ENNReal.ofReal (2 / (cm / cp)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hcp.le]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : 2 / (cm / cp) = cp * (2 * (1 / cm)) := by field_simp
    rw [e]
    gcongr
    exact div_le_self zero_le_two hA
  rcases (integral_nonneg fun x => sq_nonneg (g x) : 0 ≤ t).eq_or_lt with h0 | htpos
  · -- `g = 0` a.e.
    have hz : (fun x => g x ^ 2) =ᵐ[haar d] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (g x)) hiH).mp h0.symm
    have hzP : (fun x => g x ^ 2) =ᵐ[P] 0 := withDensity_absolutelyContinuous _ _ |>.ae_le hz
    have hm0 : ∫ x, g x ^ 2 ∂P = 0 := by rw [integral_congr_ae hzP]; simp
    unfold ent
    rw [if_pos hiP, hm0]
    simp
  calc ent P (fun x => g x ^ 2)
      ≤ ∫⁻ x, ENNReal.ofReal (t * klFun (g x ^ 2 / t)) ∂P :=
        ent_le_shift (fun x => sq_nonneg (g x)) hiP htpos
    _ ≤ ∫⁻ x, ENNReal.ofReal (t * klFun (g x ^ 2 / t)) ∂(ENNReal.ofReal cp • haar d) :=
        lintegral_mono' hPle le_rfl
    _ = ENNReal.ofReal cp * ent (haar d) (fun x => g x ^ 2) := by
        rw [lintegral_smul_measure, smul_eq_mul]
        unfold ent; rw [if_pos hiH]
    _ ≤ ENNReal.ofReal cp * (ENNReal.ofReal (2 / aCos) * dirichlet (haar d) g) := by
        gcongr; exact lsi_torus_H1 hH1
    _ ≤ ENNReal.ofReal cp * (ENNReal.ofReal (2 / aCos) * (ENNReal.ofReal (1 / cm) *
          dirichlet P g)) := by gcongr
    _ = ENNReal.ofReal cp * (ENNReal.ofReal (2 / aCos) * ENNReal.ofReal (1 / cm)) *
          dirichlet P g := by ring
    _ ≤ ENNReal.ofReal (2 / (cm / cp)) * dirichlet P g := by gcongr

end SharpLSI
