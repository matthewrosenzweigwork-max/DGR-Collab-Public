import SharpSymmetricLSI.Paper.GroundState
import SharpSymmetricLSI.Paper.BoundedPerturbation
import SharpSymmetricLSI.Infra.Centering

/-!
# Proposition 3.5: uniform full-labeled inequalities (Phase 3, lane C; R39)

* Step 1: `λ^all_{N,κ} ≥ a e^{-κN/2}` (bounded perturbation with `ψ = U_N`, `osc U_N ≤ κN/2`).
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI

theorem var_map_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (P : Measure α)
    {φ : α → β} (hφ : Measurable φ) {u : β → ℝ} (hu : AEStronglyMeasurable u (P.map φ)) :
    var P (fun x => u (φ x)) = var (P.map φ) u := by
  unfold var ProbabilityTheory.evariance
  rw [integral_map hφ.aemeasurable hu]
  exact (lintegral_map' ((hu.sub aestronglyMeasurable_const).enorm.pow_const 2)
    hφ.aemeasurable).symm

section Cosine

variable {N : ℕ}

theorem sumCos_sq_add_sumSin_sq_le (x : Fin N × Fin 1 → ℝ) :
    sumCos x ^ 2 + sumSin x ^ 2 ≤ (N : ℝ) ^ 2 := by
  unfold sumCos sumSin
  rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  calc ∑ j, (∑ k, Real.cos (thetaC x j) * Real.cos (thetaC x k) +
        ∑ k, Real.sin (thetaC x j) * Real.sin (thetaC x k))
      ≤ ∑ _j : Fin N, ∑ _k : Fin N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun k _ => ?_
        nlinarith [Real.cos_sq_add_sin_sq (thetaC x j), Real.cos_sq_add_sin_sq (thetaC x k),
          sq_nonneg (Real.cos (thetaC x j) - Real.cos (thetaC x k)),
          sq_nonneg (Real.sin (thetaC x j) - Real.sin (thetaC x k))]
    _ = (N : ℝ) ^ 2 := by simp [sq]

theorem UL_le {κ : ℝ} (hκ : 0 ≤ κ) (hN : 1 ≤ N) (x : Fin N × Fin 1 → ℝ) :
    UL κ N x ≤ κ * N / 2 := by
  unfold UL
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := sumCos_sq_add_sumSin_sq_le x
  calc κ / (2 * N) * (sumCos x ^ 2 + sumSin x ^ 2) ≤ κ / (2 * N) * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = κ * N / 2 := by field_simp

theorem memH1_volume_of_gsMeas {κ : ℝ} (hκ : 0 ≤ κ) {u : UnitAddTorus (Fin N × Fin 1) → ℝ}
    (hu : MemH1 (gsMeas κ N) u) : MemH1 volume u := by
  obtain ⟨C, hC, hle⟩ := volume_le_smul_gsMeas (N := N) hκ
  exact ⟨hu.1, hu.2.1.of_measure_le_smul hC hle, hu.2.2.of_measure_le_smul hC hle⟩

theorem gsMeas_eq_perturbation (κ : ℝ) :
    gsMeas κ N = (volume : Measure (UnitAddTorus (Fin N × Fin 1))).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-UL κ N (secT x)) /
        ∫ y, Real.exp (-UL κ N (secT y)))) := by
  have h := integral_gsW (N := N) κ
  simp only [gsW] at h
  rw [integral_const_mul] at h
  have hI : ∫ y : UnitAddTorus (Fin N × Fin 1), Real.exp (-UL κ N (secT y)) = (gsC κ N)⁻¹ := by
    exact eq_inv_of_mul_eq_one_right h
  rw [gsMeas]
  congr 1; funext x
  rw [hI, div_inv_eq_mul, mul_comm]; rfl

/-- `Var_P(f) ≤ (e^{κN/2}/a) ℰ(f)` (bounded perturbation, Step 1 of Proposition 3.5). -/
theorem var_le_energy_cos {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) {f : Config N 1 → ℝ}
    (hf : MemH1C (gibbs cosV (cosW κ) N) f) :
    var (gibbs cosV (cosW κ) N) f ≤
      ENNReal.ofReal (Real.exp (κ * N / 2) / aCos) * energy cosV (cosW κ) N f := by
  have hH1 : MemH1 ((gibbs cosV (cosW κ) N).map flat) (f ∘ unflat) := hf
  have henergy := energy_eq_dirichlet (cosine_hyp_all κ) hH1.1
  have hvar := var_map_eq (gibbs cosV (cosW κ) N) measurable_flat hH1.2.1.aestronglyMeasurable
  rw [show var (gibbs cosV (cosW κ) N) f =
    var (gibbs cosV (cosW κ) N) (fun X => (f ∘ unflat) (flat X)) from rfl, hvar, henergy]
  rw [gibbs_map_flat_eq] at hH1 ⊢
  have hv := memH1_volume_of_gsMeas hκ.le hH1
  have hψm : Measurable fun y : UnitAddTorus (Fin N × Fin 1) => UL κ N (secT y) :=
    (contDiff_UL κ).continuous.measurable.comp measurable_secT
  have hb : ∃ B, ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin N × Fin 1))),
      |UL κ N (secT x)| ≤ B :=
    ⟨κ * N / 2, Eventually.of_forall fun x => by
      rw [abs_of_nonneg (UL_nonneg hκ.le _)]; exact UL_le hκ.le hN _⟩
  have hBP := bounded_perturbation_aux hψm.aemeasurable hb hv
  rw [← gsMeas_eq_perturbation] at hBP
  refine hBP.trans (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le)
  have hsup : essSup (fun x => UL κ N (secT x)) (volume : Measure (UnitAddTorus (Fin N × Fin 1)))
      ≤ κ * N / 2 :=
    essSup_le_of_ae_le _ (Eventually.of_forall fun x => UL_le hκ.le hN _)
      (isCoboundedUnder_le_of_eventually_le _ (x := 0) (Eventually.of_forall fun x =>
        UL_nonneg hκ.le _))
  have hinf : 0 ≤ essInf (fun x => UL κ N (secT x)) (volume : Measure (UnitAddTorus (Fin N × Fin 1))) :=
    le_essInf_of_ae_le _ (Eventually.of_forall fun x => UL_nonneg hκ.le _)
      (isCoboundedUnder_ge_of_eventually_le _ (x := κ * N / 2) (Eventually.of_forall fun x =>
        UL_le hκ.le hN _))
  have ha : aCos = 4 * π ^ 2 := rfl
  rw [← ha]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
    (by rw [ha]; positivity)

/-- Step 1 of Proposition 3.5: `λ^all_{N,κ} ≥ a e^{-κN/2}`. -/
theorem lamAll_ge_exp {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) :
    ENNReal.ofReal (aCos * Real.exp (-κ * N / 2)) ≤ lamAll cosV (cosW κ) N := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  haveI := gibbs_isProbabilityMeasure (cosine_hyp_all κ) N
  unfold lamAll
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨hf1, hvar⟩ := hf
  have hle := var_le_energy_cos hκ hN hf1
  have hvt : var (gibbs cosV (cosW κ) N) f ≠ ⊤ :=
    ProbabilityTheory.evariance_ne_top (memLp_of_memH1C (cosine_hyp_all κ) hf1)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hvar.ne') (Or.inl hvt)]
  calc ENNReal.ofReal (aCos * Real.exp (-κ * N / 2)) * var (gibbs cosV (cosW κ) N) f
      ≤ ENNReal.ofReal (aCos * Real.exp (-κ * N / 2)) *
          (ENNReal.ofReal (Real.exp (κ * N / 2) / aCos) * energy cosV (cosW κ) N f) :=
        mul_le_mul_of_nonneg_left hle zero_le
    _ = energy cosV (cosW κ) N f := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        have : aCos * Real.exp (-κ * N / 2) * (Real.exp (κ * N / 2) / aCos) = 1 := by
          rw [show -κ * N / 2 = -(κ * N / 2) by ring, Real.exp_neg]
          field_simp
        rw [this, ENNReal.ofReal_one, one_mul]

/-- Step 3 of Proposition 3.5 ((3.26)): `r^all ≥ 2aλ/(4λ + (2κ+8)a)`. -/
theorem rAll_ge_of_lamAll {κ : ℝ} (hκ : 0 < κ) (hN : 1 ≤ N) :
    2 * ENNReal.ofReal aCos * lamAll cosV (cosW κ) N /
        (4 * lamAll cosV (cosW κ) N + ENNReal.ofReal ((2 * κ + 8) * aCos)) ≤
      rAll cosV (cosW κ) N := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  have hyp := cosine_hyp_all κ
  haveI := gibbs_isProbabilityMeasure hyp N
  set P := gibbs cosV (cosW κ) N with hP
  set L := lamAll cosV (cosW κ) N with hL
  unfold rAll
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨hf1, hent⟩ := hf
  set c := ∫ X, f X ∂P with hc
  have hg1 : MemH1C P (fun X => f X - c) := by
    have := memH1C_add_const hyp hf1 (-c); simpa [sub_eq_add_neg] using this
  have hEg : energy cosV (cosW κ) N (fun X => f X - c) = energy cosV (cosW κ) N f := by
    have := energy_add_const hyp hf1 (-c); simpa [sub_eq_add_neg] using this
  have hdef := cosine_defective_aux hκ hN hg1
  have hvar : ∫⁻ X, ENNReal.ofReal ((f X - c) ^ 2) ∂P = var P f := by
    unfold var ProbabilityTheory.evariance
    congr 1; funext X
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  rw [hEg, hvar] at hdef
  have hcent := ent_centering (memLp_of_memH1C hyp hf1)
  set A := ent P (fun X => f X ^ 2) with hA
  set E := energy cosV (cosW κ) N f with hE
  set V := var P f with hV
  have hAle : A ≤ ENNReal.ofReal (4 / aCos) * E + ENNReal.ofReal (2 * κ + 8) * V := by
    calc A ≤ 2 * (ENNReal.ofReal (2 / aCos) * E + ENNReal.ofReal κ * V) + 8 * V :=
          hcent.trans (add_le_add (mul_le_mul_of_nonneg_left hdef zero_le) le_rfl)
      _ = ENNReal.ofReal (4 / aCos) * E + ENNReal.ofReal (2 * κ + 8) * V := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, add_assoc, ← add_mul]
          congr 2
          · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
            congr 1; ring
          · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by simp,
              ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by norm_num)]
  have hLV : L * V ≤ E := by
    rcases (zero_le : (0 : ℝ≥0∞) ≤ V).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact zero_le
    · have hVt : V ≠ ⊤ := ProbabilityTheory.evariance_ne_top (memLp_of_memH1C hyp hf1)
      have : L ≤ E / V := iInf₂_le f ⟨hf1, hpos⟩
      exact ENNReal.mul_le_of_le_div this
  have hAt : A ≠ ⊤ := (ent_sq_lt_top_aux hyp hf1).ne
  have hEt : E ≠ ⊤ := (energy_lt_top hyp hf1).ne
  have hVt : V ≠ ⊤ := ProbabilityTheory.evariance_ne_top (memLp_of_memH1C hyp hf1)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hent.ne') (Or.inl hAt)]
  by_cases hLt : L = ⊤
  · rw [hLt]
    have h1 : 2 * ENNReal.ofReal aCos * ⊤ = ⊤ :=
      ENNReal.mul_top (by simp [ha0])
    have h2 : 4 * (⊤ : ℝ≥0∞) + ENNReal.ofReal ((2 * κ + 8) * aCos) = ⊤ := by simp
    rw [h1, h2, ENNReal.div_top, zero_mul]
    exact zero_le
  -- the finite case, in `ℝ`
  set l := L.toReal with hl
  have hLl : L = ENNReal.ofReal l := (ENNReal.ofReal_toReal hLt).symm
  have hl0 : 0 ≤ l := ENNReal.toReal_nonneg
  set Ar := A.toReal
  set Er := E.toReal
  set Vr := V.toReal
  have hAA : A = ENNReal.ofReal Ar := (ENNReal.ofReal_toReal hAt).symm
  have hEE : E = ENNReal.ofReal Er := (ENNReal.ofReal_toReal hEt).symm
  have hVV : V = ENNReal.ofReal Vr := (ENNReal.ofReal_toReal hVt).symm
  have hAr0 : 0 ≤ Ar := ENNReal.toReal_nonneg
  have hEr0 : 0 ≤ Er := ENNReal.toReal_nonneg
  have hVr0 : 0 ≤ Vr := ENNReal.toReal_nonneg
  have hb0 : 0 < (2 * κ + 8) * aCos := by positivity
  rw [hAA, hEE, hVV, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hAle
  rw [hLl, hVV, hEE, ← ENNReal.ofReal_mul hl0, ENNReal.ofReal_le_ofReal_iff hEr0] at hLV
  rw [hLl, hAA, hEE]
  have hX : 2 * ENNReal.ofReal aCos * ENNReal.ofReal l /
      (4 * ENNReal.ofReal l + ENNReal.ofReal ((2 * κ + 8) * aCos)) =
      ENNReal.ofReal (2 * aCos * l / (4 * l + (2 * κ + 8) * aCos)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    congr 1
    · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]; simp
    · rw [ENNReal.ofReal_add (by positivity) hb0.le, ENNReal.ofReal_mul (p := 4) (by norm_num)]; simp
  rw [hX, ← ENNReal.ofReal_mul (by positivity), show (2 : ℝ≥0∞) * ENNReal.ofReal Er =
    ENNReal.ofReal (2 * Er) by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h1 : aCos * l * Ar ≤ aCos * l * (4 / aCos * Er + (2 * κ + 8) * Vr) :=
    mul_le_mul_of_nonneg_left hAle (by positivity)
  have h2 : aCos * l * (4 / aCos * Er + (2 * κ + 8) * Vr) =
      4 * l * Er + (2 * κ + 8) * aCos * (l * Vr) := by field_simp
  have h3 : (2 * κ + 8) * aCos * (l * Vr) ≤ (2 * κ + 8) * aCos * Er :=
    mul_le_mul_of_nonneg_left hLV hb0.le
  nlinarith

end Cosine

end SharpLSI
