import FullLabeledLSI.Paper.PermAvg
import SharpSymmetricLSI.Paper.ProductFisherGrad
import SharpSymmetricLSI.Paper.R37Particle

/-!
# Fisher information of a density relative to a density

For probability densities `f, q` on a torus (measurable, bounded above and below by positive
constants) with `log(f/q)` having a bounded weak gradient `g`:
`I(f·vol | q·vol) = ∫ |g|² f dvol`, and the transfer to `Config N d` through `flat`.
-/

noncomputable section
open MeasureTheory InformationTheory Real Filter Topology
open scoped ENNReal ContDiff

namespace SharpLSI.FL

section Torus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fisherInfo_dens_torus {f q : UnitAddTorus ι → ℝ} (hf : Measurable f) (hq : Measurable q)
    (hfb : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ f x ∧ f x ≤ C)
    (hqb : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ q x ∧ q x ≤ C)
    {g : UnitAddTorus ι → ι → ℝ}
    (hg : IsWeakGrad (fun y => Real.log (f y / q y)) g) (hgb : ∃ Cg : ℝ, ∀ y k, |g y k| ≤ Cg) :
    fisherInfo ((volume : Measure (UnitAddTorus ι)).withDensity fun y => ENNReal.ofReal (f y))
        ((volume : Measure (UnitAddTorus ι)).withDensity fun y => ENNReal.ofReal (q y)) =
      ∫⁻ y, ENNReal.ofReal (f y * sqNorm (g y)) ∂(volume : Measure (UnitAddTorus ι)) := by
  obtain ⟨cf, Cf, hcf, hf'⟩ := hfb
  obtain ⟨cq, Cq, hcq, hq'⟩ := hqb
  have hf0 : ∀ x, 0 < f x := fun x => lt_of_lt_of_le hcf (hf' x).1
  have hq0 : ∀ x, 0 < q x := fun x => lt_of_lt_of_le hcq (hq' x).1
  obtain ⟨B, hB⟩ := bdd_log_div ⟨cf, Cf, hcf, hf'⟩ ⟨cq, Cq, hcq, hq'⟩
  obtain ⟨Cg, hCg⟩ := hgb
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary _))
  set vol : Measure (UnitAddTorus ι) := volume with hvol
  set ν := vol.withDensity fun y => ENNReal.ofReal (f y) with hν
  set P := vol.withDensity fun y => ENNReal.ofReal (q y) with hP
  have hqm : Measurable fun y => ENNReal.ofReal (q y) := hq.ennreal_ofReal
  have hPvol : P ≪ vol := withDensity_absolutelyContinuous _ _
  have hvolP : vol ≪ P := withDensity_absolutelyContinuous' hqm.aemeasurable
    (Filter.Eventually.of_forall fun x => by simpa using hq0 x)
  have hPfin : IsFiniteMeasure P := by
    refine isFiniteMeasure_withDensity_ofReal ?_
    exact (Integrable.of_bound hq.aestronglyMeasurable Cq (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (hq0 y)]; exact (hq' y).2)).hasFiniteIntegral
  have hac : ν ≪ P := (withDensity_absolutelyContinuous _ _).trans hvolP
  have hrn := rnDeriv_dens (m := vol) hf hq hf0 hq0
  set l : UnitAddTorus ι → ℝ := fun y => Real.log (f y / q y) with hl
  have hE : ∀ᵐ y ∂vol, Real.sqrt (ν.rnDeriv P y).toReal = Real.exp (l y / 2) := by
    filter_upwards [hrn] with y hy
    rw [hy, ENNReal.toReal_ofReal (div_pos (hf0 y) (hq0 y)).le, Real.exp_half, hl]
    simp only
    rw [Real.exp_log (div_pos (hf0 y) (hq0 y))]
  -- weak gradient of `exp (l/2)`
  have iΦ : Integrable l vol :=
    Integrable.of_bound hg.aestronglyMeasurable_fun B (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hB y)
  have igΦ : ∀ k, Integrable (fun y => g y k) vol := fun k =>
    Integrable.of_bound (hg.aestronglyMeasurable_grad k) Cg (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hCg y k)
  obtain ⟨L, hL⟩ := deriv_expCut_bdd B hB0
  have h := isWeakGrad_comp hg iΦ igΦ ((contDiff_expCut B hB0).of_le (by simp)) hL
  have e1 : (fun y => expCut B hB0 (l y)) = fun y => Real.exp (l y / 2) :=
    funext fun y => expCut_eq hB0 (hB y)
  have e2 : (fun y k => deriv (expCut B hB0) (l y) * g y k) =
      fun y k => Real.exp (l y / 2) / 2 * g y k :=
    funext fun y => funext fun k => by rw [deriv_expCut hB0 (hB y)]
  rw [e1, e2] at h
  have hu : IsWeakGrad (fun y => Real.sqrt (ν.rnDeriv P y).toReal)
      (fun y k => Real.exp (l y / 2) / 2 * g y k) := by
    refine h.congr_ae ?_
    filter_upwards [hE] with y hy using hy.symm
  have hwg := weakGrad_ae_eq hu
  have hEb : ∀ y, |Real.exp (l y / 2)| ≤ Real.exp (B / 2) := fun y => by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hB y)).2])
  set Cs : ℝ := Fintype.card ι * (Real.exp (B / 2) / 2 * Cg) ^ 2 with hCs
  have hsqb : ∀ y, sqNorm (fun k => Real.exp (l y / 2) / 2 * g y k) ≤ Cs := fun y => by
    unfold sqNorm
    calc ∑ k, (Real.exp (l y / 2) / 2 * g y k) ^ 2
        ≤ ∑ _k : ι, (Real.exp (B / 2) / 2 * Cg) ^ 2 := Finset.sum_le_sum fun k _ => by
          rw [← sq_abs, abs_mul, abs_div, abs_of_pos (Real.exp_pos _), abs_two]
          refine pow_le_pow_left₀ (by positivity) (mul_le_mul ?_ (hCg y k) (abs_nonneg _)
            (by positivity)) 2
          exact div_le_div_of_nonneg_right (by simpa [abs_of_pos (Real.exp_pos _)] using hEb y)
            (by norm_num)
      _ = Cs := by simp [hCs]
  have hH1 : MemH1 P (fun y => Real.sqrt (ν.rnDeriv P y).toReal) := by
    refine ⟨⟨_, hu⟩, ?_, ?_⟩
    · refine MemLp.of_bound (hu.aestronglyMeasurable_fun.mono_ac hPvol) (Real.exp (B / 2)) ?_
      filter_upwards [hPvol.ae_le hE] with y hy
      rw [Real.norm_eq_abs, hy]; exact hEb y
    · refine MemLp.of_bound ((Real.continuous_sqrt.comp_aestronglyMeasurable
        (isWeakGrad_weakGrad ⟨_, hu⟩).aestronglyMeasurable_sqNorm).mono_ac hPvol)
        (Real.sqrt Cs) ?_
      filter_upwards [hPvol.ae_le hwg] with y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), hy]
      exact Real.sqrt_le_sqrt (hsqb y)
  unfold fisherInfo
  rw [if_pos ⟨hac, hH1⟩]
  unfold dirichlet
  have e1 : ∫⁻ y, ENNReal.ofReal (sqNorm (weakGrad (fun y => Real.sqrt (ν.rnDeriv P y).toReal) y))
        ∂P =
      ∫⁻ y, ENNReal.ofReal (sqNorm (fun k => Real.exp (l y / 2) / 2 * g y k)) ∂P :=
    lintegral_congr_ae (by filter_upwards [hPvol.ae_le hwg] with y hy; rw [hy])
  rw [e1, hP]
  have hgm : AEMeasurable (fun y => ENNReal.ofReal
      (sqNorm (fun k => Real.exp (l y / 2) / 2 * g y k))) vol :=
    ENNReal.measurable_ofReal.comp_aemeasurable hu.aestronglyMeasurable_sqNorm.aemeasurable
  rw [lintegral_withDensity_eq_lintegral_mul₀ hqm.aemeasurable hgm,
    ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_congr fun y => ?_
  simp only [Pi.mul_apply]
  have hEsq : Real.exp (l y / 2) ^ 2 = f y / q y := by
    rw [← Real.exp_nat_mul]
    rw [show ((2 : ℕ) : ℝ) * (l y / 2) = l y by push_cast; ring, hl]
    simp only
    exact Real.exp_log (div_pos (hf0 y) (hq0 y))
  have hnorm : sqNorm (fun k => Real.exp (l y / 2) / 2 * g y k) =
      (f y / q y) / 4 * sqNorm (g y) := by
    unfold sqNorm
    rw [Finset.mul_sum, ← hEsq]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hnorm, ← ENNReal.ofReal_mul (hq0 y).le, ← ENNReal.ofReal_ofNat 4,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  have := (hq0 y).ne'
  field_simp

end Torus

section Config

variable {N d : ℕ}

theorem map_flat_withDensity {F : Config N d → ℝ≥0∞} (hF : Measurable F) :
    ((volume : Measure (Config N d)).withDensity F).map flat =
      (volume : Measure (UnitAddTorus (Fin N × Fin d))).withDensity (F ∘ unflat) := by
  rw [← map_flat_volume N]
  ext s hs
  have hFu : Measurable (F ∘ unflat : UnitAddTorus (Fin N × Fin d) → ℝ≥0∞) :=
    hF.comp measurable_unflat
  rw [Measure.map_apply measurable_flat hs, withDensity_apply _ (measurable_flat hs),
    withDensity_apply _ hs, setLIntegral_map hs hFu measurable_flat]
  rfl

/-- **Fisher information of a density relative to a density on `Config N d`**:
`I(u·m | p·m) = ∫ |∇ log(u/p)|² u dm` for positive bounded densities with `log(u/p)` having a
bounded weak gradient `g` on the flat torus. -/
theorem fisherInfoC_dens {u p : Config N d → ℝ} (hu : Measurable u) (hp : Measurable p)
    (hub : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ u x ∧ u x ≤ C)
    (hpb : ∃ c C : ℝ, 0 < c ∧ ∀ x, c ≤ p x ∧ p x ≤ C)
    {g : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ}
    (hg : IsWeakGrad (fun y => Real.log (u (unflat y) / p (unflat y))) g)
    (hgb : ∃ Cg : ℝ, ∀ y k, |g y k| ≤ Cg) :
    fisherInfoC ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (u X))
        ((volume : Measure (Config N d)).withDensity fun X => ENNReal.ofReal (p X)) =
      ∫⁻ X, ENNReal.ofReal (u X * sqNorm (g (flat X))) ∂(volume : Measure (Config N d)) := by
  unfold fisherInfoC
  rw [map_flat_withDensity hu.ennreal_ofReal, map_flat_withDensity hp.ennreal_ofReal]
  have hu' : Measurable (u ∘ unflat : UnitAddTorus (Fin N × Fin d) → ℝ) :=
    hu.comp measurable_unflat
  have hp' : Measurable (p ∘ unflat : UnitAddTorus (Fin N × Fin d) → ℝ) :=
    hp.comp measurable_unflat
  obtain ⟨cu, Cu, hcu, hu1⟩ := hub
  obtain ⟨cp, Cp, hcp, hp1⟩ := hpb
  have := fisherInfo_dens_torus hu' hp' ⟨cu, Cu, hcu, fun x => hu1 _⟩ ⟨cp, Cp, hcp, fun x => hp1 _⟩
    hg hgb
  refine (this.trans ?_)
  rw [← map_flat_volume N, measurableEmbedding_flat.lintegral_map]
  rfl

end Config

end SharpLSI.FL
