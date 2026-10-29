import SharpSymmetricLSI.Paper.Defective1
import SharpSymmetricLSI.Paper.ReferenceLSI
import SharpSymmetricLSI.Paper.CosineTagged
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Paper.EntFinite

/-!
# R03 (Proposition 2.2), part 2: the defective inequality at fixed `N` with small energy coefficient

Holley–Stroock perturbation (as in `ReferenceLSI`) of the `η`-defective torus inequality
(`elsi_torus_H1`) to a measure with density in `[c₋, c₊]` (`perturb_elsi`), applied to the flattened
Gibbs measure: for every `N ≥ 1` and `η > 0` there is `B` with
`Ent_{P_N}(f²) ≤ η ℰ_N(f) + B ∫ f² dP_N` for all `f ∈ H¹(P_N)` (`fixedN_defective`).
-/

noncomputable section
open MeasureTheory InformationTheory Filter
open scoped ENNReal Real

namespace SharpLSI

section perturb
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Holley–Stroock for the `η`-defective inequality. -/
theorem perturb_elsi {p : UnitAddTorus ι → ℝ} {cm cp : ℝ} (hcm : 0 < cm)
    (hp : ∀ x, cm ≤ p x ∧ p x ≤ cp) (hpm : Measurable p)
    [hQ : IsProbabilityMeasure ((volume : Measure (UnitAddTorus ι)).withDensity
      fun x => ENNReal.ofReal (p x))]
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {g : UnitAddTorus ι → ℝ}
    (hg : MemH1 ((volume : Measure (UnitAddTorus ι)).withDensity fun x => ENNReal.ofReal (p x)) g) :
    ent ((volume : Measure (UnitAddTorus ι)).withDensity fun x => ENNReal.ofReal (p x))
        (fun x => g x ^ 2) ≤
      ENNReal.ofReal (cp * (2 * η / aCos) / cm) *
          dirichlet ((volume : Measure (UnitAddTorus ι)).withDensity
            fun x => ENNReal.ofReal (p x)) g +
        ENNReal.ofReal (cp * (Fintype.card ι * (6 * Real.log (1 / η))) / cm) *
          ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂((volume : Measure (UnitAddTorus ι)).withDensity
            fun x => ENNReal.ofReal (p x)) := by
  set Q := (volume : Measure (UnitAddTorus ι)).withDensity fun x => ENNReal.ofReal (p x) with hQdef
  obtain ⟨x0⟩ : Nonempty (UnitAddTorus ι) := inferInstance
  have hcp : 0 < cp := hcm.trans_le ((hp x0).1.trans (hp x0).2)
  have hle : (volume : Measure (UnitAddTorus ι)) ≤ ENNReal.ofReal (1 / cm) • Q := by
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, hQdef, withDensity_apply _ hs]
    calc volume s = ENNReal.ofReal (1 / cm) * (ENNReal.ofReal cm * volume s) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hcm.ne',
            ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (1 / cm) * ∫⁻ x in s, ENNReal.ofReal (p x) := by
          gcongr
          rw [← setLIntegral_const]
          exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp x).1
  have hQle : Q ≤ ENNReal.ofReal cp • (volume : Measure (UnitAddTorus ι)) := by
    refine Measure.le_iff.mpr fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, hQdef, withDensity_apply _ hs, ← setLIntegral_const]
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hp x).2
  obtain ⟨hW, hL2, hG2⟩ := hg
  have hH1 : MemH1 (volume : Measure (UnitAddTorus ι)) g :=
    ⟨hW, hL2.of_measure_le_smul ENNReal.ofReal_ne_top hle,
      hG2.of_measure_le_smul ENNReal.ofReal_ne_top hle⟩
  have hiQ : Integrable (fun x => g x ^ 2) Q := hL2.integrable_sq
  have hiH : Integrable (fun x => g x ^ 2) volume := hH1.2.1.integrable_sq
  set t := ∫ x, g x ^ 2 with htdef
  have hdir : dirichlet volume g ≤ ENNReal.ofReal (1 / cm) * dirichlet Q g := by
    unfold dirichlet
    rw [← smul_eq_mul, ← lintegral_smul_measure]
    exact lintegral_mono' hle le_rfl
  have hmass : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ≤
      ENNReal.ofReal (1 / cm) * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Q := by
    rw [← smul_eq_mul, ← lintegral_smul_measure]
    exact lintegral_mono' hle le_rfl
  set β := (Fintype.card ι : ℝ) * (6 * Real.log (1 / η))
  have hβ : 0 ≤ β := mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (by norm_num) (Real.log_nonneg (by rw [le_div_iff₀ hη0]; linarith)))
  have ha0 : 0 < aCos := by unfold aCos; positivity
  rcases (integral_nonneg fun x => sq_nonneg (g x) : 0 ≤ t).eq_or_lt with h0 | htpos
  · -- `g = 0` a.e.
    have hz : (fun x => g x ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (g x)) hiH).mp h0.symm
    have hzP : (fun x => g x ^ 2) =ᵐ[Q] 0 := withDensity_absolutelyContinuous _ _ |>.ae_le hz
    have hm0 : ∫ x, g x ^ 2 ∂Q = 0 := by rw [integral_congr_ae hzP]; simp
    have : ent Q (fun x => g x ^ 2) = 0 := by
      unfold ent
      rw [if_pos hiQ, hm0]
      simp
    rw [this]; exact bot_le
  have e1 : ENNReal.ofReal cp * (ENNReal.ofReal (2 * η / aCos) * (ENNReal.ofReal (1 / cm) *
      dirichlet Q g)) = ENNReal.ofReal (cp * (2 * η / aCos) / cm) * dirichlet Q g := by
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hcp.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 2; ring
  have e2 : ENNReal.ofReal cp * (ENNReal.ofReal β * (ENNReal.ofReal (1 / cm) *
      ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Q)) =
      ENNReal.ofReal (cp * β / cm) * ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Q := by
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hcp.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 2; ring
  calc ent Q (fun x => g x ^ 2)
      ≤ ∫⁻ x, ENNReal.ofReal (t * klFun (g x ^ 2 / t)) ∂Q :=
        ent_le_shift (fun x => sq_nonneg (g x)) hiQ htpos
    _ ≤ ∫⁻ x, ENNReal.ofReal (t * klFun (g x ^ 2 / t)) ∂(ENNReal.ofReal cp • volume) :=
        lintegral_mono' hQle le_rfl
    _ = ENNReal.ofReal cp * ent volume (fun x => g x ^ 2) := by
        rw [lintegral_smul_measure, smul_eq_mul]
        unfold ent; rw [if_pos hiH]
    _ ≤ ENNReal.ofReal cp * (ENNReal.ofReal (2 * η / aCos) * dirichlet volume g +
          ENNReal.ofReal β * ∫⁻ x, ENNReal.ofReal (g x ^ 2)) := by
        gcongr; exact elsi_torus_H1 hη0 hη1 hH1
    _ ≤ ENNReal.ofReal cp * (ENNReal.ofReal (2 * η / aCos) * (ENNReal.ofReal (1 / cm) *
          dirichlet Q g) + ENNReal.ofReal β * (ENNReal.ofReal (1 / cm) *
          ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂Q)) := by gcongr
    _ = _ := by rw [mul_add, e1, e2]

end perturb

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem gibbs_map_flat_withDensity (hyp : Hyp V W KV KW) (N : ℕ) :
    (gibbs V W N).map flat = (volume : Measure (UnitAddTorus (Fin N × Fin d))).withDensity
      (fun y => ENNReal.ofReal
        ((gibbsDensity (volume : Measure (Config N d)) (hamiltonian V W N) (unflat y)).toReal)) := by
  have hm : Measurable fun X : Config N d => gibbsDensity volume (hamiltonian V W N) X :=
    measurable_gibbsDensity _ (continuous_hamiltonian hyp N)
  obtain ⟨C, hCt, hC⟩ := exists_gibbsDensity_upper hyp N
  have hpt : ∀ y, ENNReal.ofReal ((gibbsDensity (volume : Measure (Config N d))
      (hamiltonian V W N) (unflat y)).toReal) =
      gibbsDensity (volume : Measure (Config N d)) (hamiltonian V W N) (unflat y) := fun y =>
    ENNReal.ofReal_toReal ((hC _).trans_lt hCt.lt_top).ne
  simp_rw [hpt]
  ext s hs
  rw [Measure.map_apply measurable_flat hs,
    show gibbs V W N = (volume : Measure (Config N d)).withDensity
      (gibbsDensity volume (hamiltonian V W N)) from rfl,
    withDensity_apply _ (measurable_flat hs), withDensity_apply _ hs]
  have hmp : MeasurePreserving (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  exact hmp.setLIntegral_comp_preimage hs (hm.comp measurable_unflat)

/-- **Fixed `N`, small energy coefficient.** -/
theorem fixedN_defective (hyp : Hyp V W KV KW) {N : ℕ} {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, ∀ f : Config N d → ℝ, MemH1C (gibbs V W N) f →
      ent (gibbs V W N) (fun X => f X ^ 2) ≤ ENNReal.ofReal η * energy V W N f +
        ENNReal.ofReal B * ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N := by
  haveI := gibbs_isProbabilityMeasure hyp N
  obtain ⟨c, hc0, hct, hc⟩ := exists_gibbsDensity_lower hyp N
  obtain ⟨C, hCt, hC⟩ := exists_gibbsDensity_upper hyp N
  set g := fun X : Config N d => gibbsDensity (volume : Measure (Config N d)) (hamiltonian V W N) X
  set p : UnitAddTorus (Fin N × Fin d) → ℝ := fun y => (g (unflat y)).toReal
  set cm := c.toReal
  set cp := C.toReal
  have hcm : 0 < cm := ENNReal.toReal_pos hc0 hct
  have hp : ∀ y, cm ≤ p y ∧ p y ≤ cp := fun y =>
    ⟨ENNReal.toReal_mono ((hC _).trans_lt hCt.lt_top).ne (hc _),
      ENNReal.toReal_mono hCt (hC _)⟩
  have hpm : Measurable p :=
    ((measurable_gibbsDensity _ (continuous_hamiltonian hyp N)).comp measurable_unflat).ennreal_toReal
  have hmap := gibbs_map_flat_withDensity hyp N
  haveI : IsProbabilityMeasure ((volume : Measure (UnitAddTorus (Fin N × Fin d))).withDensity
      fun y => ENNReal.ofReal (p y)) := by
    rw [← hmap]; infer_instance
  have ha0 : 0 < aCos := by unfold aCos; positivity
  have hcp : 0 < cp := hcm.trans_le ((hp (flat (fun _ => 0))).1.trans (hp _).2)
  set η' := min 1 (η * aCos * cm / (2 * cp))
  have hη'0 : 0 < η' := lt_min one_pos (by positivity)
  have hη'1 : η' ≤ 1 := min_le_left _ _
  refine ⟨cp * (Fintype.card (Fin N × Fin d) * (6 * Real.log (1 / η'))) / cm, fun f hf => ?_⟩
  have hf' : MemH1 ((volume : Measure (UnitAddTorus (Fin N × Fin d))).withDensity
      fun y => ENNReal.ofReal (p y)) (f ∘ unflat) := by
    have := hf; unfold MemH1C at this; rwa [hmap] at this
  have key := perturb_elsi hcm hp hpm hη'0 hη'1 hf'
  rw [← hmap] at key
  have hent : ent (gibbs V W N) (fun X => f X ^ 2) =
      ent ((gibbs V W N).map flat) (fun y => (f ∘ unflat) y ^ 2) := by
    have := ent_comp (gibbs V W N) measurable_flat (u := fun y => (f ∘ unflat) y ^ 2)
      ((hf.2.1.aestronglyMeasurable).pow 2)
    exact this
  have hmass : ∫⁻ X, ENNReal.ofReal (f X ^ 2) ∂gibbs V W N =
      ∫⁻ y, ENNReal.ofReal ((f ∘ unflat) y ^ 2) ∂((gibbs V W N).map flat) := by
    rw [measurableEmbedding_flat.lintegral_map]; rfl
  rw [hent, energy_eq_dirichlet hyp hf.1, hmass]
  refine key.trans (add_le_add ?_ le_rfl)
  gcongr
  -- `cp (2η'/a)/cm ≤ η`
  have : η' ≤ η * aCos * cm / (2 * cp) := min_le_right _ _
  rw [div_le_iff₀ hcm]
  have h2 : cp * (2 * η' / aCos) ≤ cp * (2 * (η * aCos * cm / (2 * cp)) / aCos) := by gcongr
  calc cp * (2 * η' / aCos) ≤ cp * (2 * (η * aCos * cm / (2 * cp)) / aCos) := h2
    _ = η * cm := by field_simp

end SharpLSI
