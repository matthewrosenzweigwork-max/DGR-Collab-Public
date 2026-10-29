import LeanResearch.Imported.TauCetiAppendix.MeasureTheory.Integral.NormRpow
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! Exact radial tail integral in Appendix A, with ordinary Euclidean
Lebesgue measure. The Haar radial formula and the one-dimensional improper
integral prove both integrability and the stated coefficient. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace PeriodicAttractiveLogGas.RadialTail
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

lemma radial_tail {s R : ℝ} (hs : s < -(Module.finrank ℝ E : ℝ)) (hR : 0 < R) :
    IntegrableOn (fun x : E => ‖x‖ ^ s) (closedBall (0 : E) R)ᶜ μ ∧
      (∫ x in (closedBall (0 : E) R)ᶜ, ‖x‖ ^ s ∂μ) =
        (Module.finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
          (-R ^ ((Module.finrank ℝ E : ℝ) + s) / ((Module.finrank ℝ E : ℝ) + s)) := by
  let d := Module.finrank ℝ E
  let f : ℝ → ℝ := (Ioi R).indicator (fun r => r ^ s)
  have hd : 1 ≤ d := Module.finrank_pos
  have he (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
      r ^ (d - 1) • f r = (Ioi R).indicator (fun r : ℝ => r ^ ((d : ℝ) - 1 + s)) r := by
    by_cases h : R < r
    · simp only [f, indicator_of_mem (mem_Ioi.mpr h), smul_eq_mul]
      rw [← Real.rpow_natCast r (d - 1), Nat.cast_sub hd, Nat.cast_one, ← Real.rpow_add hr]
    · simp only [f, indicator_of_notMem (show r ∉ Ioi R from h), smul_zero]
  have hg : Integrable (fun r : ℝ => (Ioi R).indicator (fun r => r ^ ((d : ℝ) - 1 + s)) r) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by dsimp only [d]; linarith) hR)
  have hrad : IntegrableOn (fun r : ℝ => r ^ (d - 1) • f r) (Ioi (0 : ℝ)) := by
    apply hg.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (he r hr).symm
  have hfun : (fun x : E => f ‖x‖) = ((closedBall (0 : E) R)ᶜ).indicator (fun x : E => ‖x‖ ^ s) := by
    funext x
    simp only [f, indicator, mem_Ioi, mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
  have hint : IntegrableOn (fun x : E => ‖x‖ ^ s) (closedBall (0 : E) R)ᶜ μ := by
    rw [← integrable_indicator_iff measurableSet_closedBall.compl, ← hfun]
    exact (integrable_fun_norm_addHaar μ).mpr hrad
  refine ⟨hint, ?_⟩
  rw [← integral_indicator measurableSet_closedBall.compl, ← hfun, integral_fun_norm_addHaar]
  have hi : (∫ r in Ioi (0 : ℝ), r ^ (d - 1) • f r) =
      -R ^ ((d : ℝ) + s) / ((d : ℝ) + s) := by
    rw [setIntegral_congr_fun measurableSet_Ioi he,
      setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi hR.le), integral_Ioi_rpow_of_lt (by dsimp only [d]; linarith) hR]
    congr 1 <;> ring_nf
  change d • μ.real (ball (0 : E) 1) • (∫ r in Ioi (0 : ℝ), r ^ (d - 1) • f r) = _
  rw [hi]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

lemma translated_tail {s R : ℝ} (hs : s < -(Module.finrank ℝ E : ℝ)) (hR : 0 < R) (x : E) :
    IntegrableOn (fun y : E => ‖x - y‖ ^ s) (closedBall x R)ᶜ μ ∧
      (∫ y in (closedBall x R)ᶜ, ‖x - y‖ ^ s ∂μ) =
        (Module.finrank ℝ E : ℝ) * μ.real (ball (0 : E) 1) *
          (-R ^ ((Module.finrank ℝ E : ℝ) + s) / ((Module.finrank ℝ E : ℝ) + s)) := by
  have hpres := measurePreserving_add_right μ x
  have hemb := (MeasurableEquiv.addRight x : E ≃ᵐ E).measurableEmbedding
  have hpre : (fun z : E => z + x) ⁻¹' (closedBall x R)ᶜ = (closedBall (0 : E) R)ᶜ := by
    ext z
    simp only [mem_preimage, mem_compl_iff, mem_closedBall, dist_eq_norm, add_sub_cancel_right, sub_zero]
  have hfun : (fun z : E => ‖x - (z + x)‖ ^ s) = fun z => ‖z‖ ^ s := by
    funext z
    rw [show x - (z + x) = -z by abel, norm_neg]
  constructor
  · rw [← hpres.integrableOn_comp_preimage hemb, hpre]
    change IntegrableOn (fun z : E => ‖x - (z + x)‖ ^ s) (closedBall (0 : E) R)ᶜ μ
    rw [hfun]
    exact (radial_tail hs hR).1
  · rw [← hpres.setIntegral_preimage_emb hemb, hpre, hfun]
    exact (radial_tail hs hR).2

/-- Exact lower-integral tail. The boundary sphere has zero Haar measure. -/
theorem kernel_square_tail {ι : Type*} [Fintype ι] (hd : 2 < Fintype.card ι)
    (x : EuclideanSpace ℝ ι) {R : ℝ} (hR : 0 < R) :
    (∫⁻ y in (ball x R)ᶜ, ‖x - y‖ₑ ^ (2 - 2 * (Fintype.card ι : ℝ))) =
      ENNReal.ofReal (((Fintype.card ι : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ ι) 1) /
        ((Fintype.card ι : ℝ) - 2)) * R ^ (2 - (Fintype.card ι : ℝ))) := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hs : (2 - 2 * (Fintype.card ι : ℝ)) < -(Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) := by
    simp only [finrank_euclideanSpace]
    have hh : (2 : ℝ) < Fintype.card ι := by exact_mod_cast hd
    linarith
  have ht := translated_tail (μ := volume) hs hR x
  have hball : closedBall x R =ᵐ[volume] ball x R :=
    (ae_eq_of_subset_of_measure_ge ball_subset_closedBall
      (Measure.addHaar_closedBall_eq_addHaar_ball volume x R).le measurableSet_ball.nullMeasurableSet
      measure_closedBall_lt_top.ne).symm
  rw [Measure.restrict_congr_set hball.compl.symm]
  have he : (∫⁻ y in (closedBall x R)ᶜ, ‖x - y‖ₑ ^ (2 - 2 * (Fintype.card ι : ℝ))) =
      ENNReal.ofReal (∫ y in (closedBall x R)ᶜ, ‖x - y‖ ^ (2 - 2 * (Fintype.card ι : ℝ))) := by
    rw [ofReal_integral_eq_lintegral_ofReal ht.1
      (Eventually.of_forall fun y => Real.rpow_nonneg (norm_nonneg _) _)]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_closedBall.compl] with y hy
    have hpos : 0 < ‖x - y‖ := by
      have hh : R < dist y x := lt_of_not_ge hy
      simpa only [dist_eq_norm, norm_sub_rev] using hR.trans hh
    rw [← ENNReal.ofReal_rpow_of_pos hpos, ofReal_norm]
  rw [he, ht.2]
  congr 1
  simp only [finrank_euclideanSpace]
  rw [show (Fintype.card ι : ℝ) + (2 - 2 * (Fintype.card ι : ℝ)) =
    -((Fintype.card ι : ℝ) - 2) by ring, neg_div_neg_eq]
  rw [show -((Fintype.card ι : ℝ) - 2) = 2 - (Fintype.card ι : ℝ) by ring]
  ring

end PeriodicAttractiveLogGas.RadialTail
