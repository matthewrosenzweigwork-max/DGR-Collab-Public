import FullLabeledLSI.Examples.E01g1_Weak
import FullLabeledLSI.Paper.Sec8Fourier5
import FullLabeledLSI.Paper.Sec8Fourier9

/-!
# Lane D, Task C (E01g1): the gap and dissipation of a single density for `W = C(0) - C(x-y)`

`entR`, `cqR`, `GR = H - ½⟨ρ, C*ρ⟩`, `DR = ∫ (2 (√ρ)' - √ρ (C'*ρ))²`; and
`gap zeroV (attrW C) (densMeasure ρ) = GR C ρ`, `dissipation zeroV (attrW C) ρ = DR C ρ`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-- Entropy `H(ρ|m)` as a real number. -/
noncomputable def entR (ρ : Torus 1 → ℝ) : ℝ := (klDiv (densMeasure ρ) (haar 1)).toReal

/-- `⟨ρ, C*ρ⟩`. -/
noncomputable def cqR (C ρ : Torus 1 → ℝ) : ℝ := ∫ x, ρ x * convT C ρ x ∂haar 1

/-- The gap `G(ρ) = H(ρ|m) - ½⟨ρ, C*ρ⟩`. -/
noncomputable def GR (C ρ : Torus 1 → ℝ) : ℝ := entR ρ - cqR C ρ / 2

/-- The dissipation `D(ρ) = ∫ (2 (√ρ)' - √ρ (C'*ρ))²`. -/
noncomputable def DR (C ρ : Torus 1 → ℝ) : ℝ :=
  ∫ x, (2 * weakGrad (fun y => Real.sqrt (ρ y)) x 0 - Real.sqrt (ρ x) * convT (dT C) ρ x) ^ 2 ∂haar 1

/-- The Fisher information `4 ∫ ((√ρ)')²`. -/
noncomputable def IR (ρ : Torus 1 → ℝ) : ℝ := 4 * ∫ x, weakGrad (fun y => Real.sqrt (ρ y)) x 0 ^ 2 ∂haar 1

theorem attrW_eq (C : Torus 1 → ℝ) : attrW C = Sec8.WG (fun x => -C x) := by
  funext x y; simp only [attrW, Sec8.WG]; ring

theorem convT_eq_conv {g ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1) :
    convT g ρ = fun x => ∫ y, g (x - y) ∂densMeasure ρ := by
  funext x
  rw [integral_densMeasure' h0 h1]
  unfold convT
  congr 1; funext y; ring

theorem Fstar_attr {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) :
    Fstar zeroV (attrW C) = ((C 0 / 2 : ℝ) : EReal) := by
  have hGc : Continuous (fun x => -C x) := (continuous_of_smooth hC.smooth).neg
  have h := Sec8.freeEnergy_WG_haar (d := 1) hGc
  unfold IsMinimizer at hmin
  have e : (zeroV : Torus 1 → ℝ) = fun _ => (0 : ℝ) := rfl
  rw [← hmin]
  rw [attrW_eq, e]
  show freeEnergy (fun _ => (0 : ℝ)) (Sec8.WG fun x => -C x) (haar 1) = _
  rw [h]
  congr 1
  have : Sec8.meanT (fun x : Torus 1 => -C x) = 0 := by
    unfold Sec8.meanT; rw [integral_neg, hC.meanZero]; simp
  rw [this]; ring

theorem Qint_eq_cqR {C ρ : Torus 1 → ℝ} (hC : Continuous C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) : Sec8.Qint (densMeasure ρ) C = cqR C ρ := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  rw [Sec8.Qint_swap hC, integral_densMeasure' h0 h1]
  unfold cqR
  congr 1; funext x
  rw [convT_eq_conv h0 h1]

theorem gap_eq {C : Torus 1 → ℝ} (hC : GoodKernel C) (hmin : IsMinimizer zeroV (attrW C) haarPM)
    {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    gap zeroV (attrW C) (densMeasure ρ) = ((GR C ρ : ℝ) : EReal) := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  have hCc := continuous_of_smooth hC.smooth
  have hGc : Continuous (fun x => -C x) := hCc.neg
  have hfin := (circle_quantitative_lsi_aux h0 h1 hH).1
  unfold gap
  rw [Fstar_attr hC hmin, attrW_eq]
  have e : (zeroV : Torus 1 → ℝ) = fun _ => (0 : ℝ) := rfl
  rw [e]
  rw [Sec8.freeEnergy_WG hGc (densMeasure ρ)]
  have hQ : Sec8.Qint (densMeasure ρ) (fun x => -C x) = - cqR C ρ := by
    rw [← Qint_eq_cqR hCc h0 h1]
    unfold Sec8.Qint
    simp [integral_neg]
  rw [hQ]
  have hkl : ((klDiv (densMeasure ρ) (haar 1) : ℝ≥0∞) : EReal) = ((entR ρ : ℝ) : EReal) := by
    unfold entR
    rw [← EReal.coe_ennreal_toReal hfin]
  rw [hkl]
  unfold GR
  rw [← EReal.coe_add, ← EReal.coe_sub]
  congr 1
  ring

theorem isSmoothT_const_sub (a : ℝ) {h : Torus 1 → ℝ} (hh : IsSmoothT h) :
    IsSmoothT (fun y => a - h y) := by
  rw [isSmoothT_iff_lift1] at hh ⊢
  exact contDiff_const.sub hh

theorem integrable_conv_mul {g ρ : Torus 1 → ℝ} (hg : Continuous g) (hρi : Integrable ρ (haar 1))
    (y : Torus 1) : Integrable (fun x => g (y - x) * ρ x) (haar 1) := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hg.continuousOn
  exact hρi.bdd_mul (c := M) (f := fun x => g (y - x))
    (hg.comp (continuous_sub_left y)).aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa using hM (y - x) (Set.mem_univ _))

theorem convDens_attr {C ρ : Torus 1 → ℝ} (hC : Continuous C) (h1 : ∫ x, ρ x ∂haar 1 = 1) :
    convDens (attrW C) ρ = fun y => C 0 - convT C ρ y := by
  funext y
  unfold convDens convT attrW
  have hρi := integrable_of_integral_eq_one' h1
  have hCi := integrable_conv_mul hC hρi y
  have e : (fun x : Torus 1 => (C 0 - C (y - x)) * ρ x) = fun x => C 0 * ρ x - C (y - x) * ρ x := by
    funext x; ring
  rw [e, integral_sub (hρi.const_mul _) hCi, integral_const_mul, h1]
  ring

theorem hasWeakGrad_diss {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) :
    IsSmoothT (fun y => zeroV y + convDens (attrW C) ρ y) ∧
      (fun x => weakGrad (fun y => zeroV y + convDens (attrW C) ρ y) x 0) =ᵐ[haar 1]
        fun x => - convT (dT C) ρ x := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  have hCc := continuous_of_smooth hC.smooth
  have hfun : (fun y => zeroV y + convDens (attrW C) ρ y) = fun y => C 0 - convT C ρ y := by
    funext y; rw [convDens_attr hCc h1]; simp [zeroV]
  have hcs : IsSmoothT (convT C ρ) := by
    rw [convT_eq_conv h0 h1]; exact isSmoothT_conv hC.smooth _
  have hsm : IsSmoothT (fun y => C 0 - convT C ρ y) := isSmoothT_const_sub _ hcs
  rw [hfun]
  refine ⟨hsm, ?_⟩
  refine (weakGrad_ae_dT hsm).trans (Eventually.of_forall fun x => ?_)
  show dT (fun y => C 0 - convT C ρ y) x = _
  rw [dT_const_sub]
  congr 1
  have hcv : convT C ρ = fun x => ∫ y, C (x - y) ∂densMeasure ρ := convT_eq_conv h0 h1
  rw [hcv, dT_conv hC.smooth, convT_eq_conv h0 h1]

theorem integrable_DR_integrand {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    Integrable (fun x => (2 * weakGrad (fun y => Real.sqrt (ρ y)) x 0 -
      Real.sqrt (ρ x) * convT (dT C) ρ x) ^ 2) (haar 1) := by
  have hb : Continuous (convT (dT C) ρ) := by
    have hs : IsSmoothT (convT (dT C) ρ) := by
      haveI := isProbabilityMeasure_densMeasure' h0 h1
      rw [convT_eq_conv h0 h1]; exact isSmoothT_conv (isSmoothT_dT hC.smooth) _
    exact continuous_of_smooth hs
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hb.continuousOn
  have hw := (memLp_weakGrad_zero hH).const_mul 2
  have hf : MemLp (fun x => Real.sqrt (ρ x)) 2 (haar 1) := hH.2.1
  have hfb : MemLp (fun x => Real.sqrt (ρ x) * convT (dT C) ρ x) 2 (haar 1) := by
    have hbm : MemLp (convT (dT C) ρ) ⊤ (haar 1) :=
      MemLp.of_bound hb.aestronglyMeasurable M (Eventually.of_forall fun x => by
        simpa using hM x (Set.mem_univ _))
    have := hbm.mul hf (r := 2)
    refine this.ae_eq (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  exact (hw.sub hfb).integrable_sq

theorem diss_eq {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    dissipation zeroV (attrW C) ρ = ENNReal.ofReal (DR C ρ) := by
  obtain ⟨hsm, hae⟩ := hasWeakGrad_diss hC h0 h1
  unfold dissipation
  rw [if_pos ⟨hH, hasWeakGrad_of_smooth hsm⟩]
  have hint := integrable_DR_integrand hC h0 h1 hH
  unfold DR
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  simp only [Fin.sum_univ_one]
  rw [hx]
  congr 1; ring

theorem admissible_iff {C ρ : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) :
    Admissible zeroV (attrW C) ρ ↔
      (∀ x, 0 ≤ ρ x) ∧ ∫ x, ρ x ∂haar 1 = 1 ∧ MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) ∧
        0 < GR C ρ := by
  constructor
  · rintro ⟨h0, h1, hH, hg⟩
    refine ⟨h0, h1, hH, ?_⟩
    rw [gap_eq hC hmin h0 h1 hH] at hg
    exact_mod_cast hg
  · rintro ⟨h0, h1, hH, hg⟩
    refine ⟨h0, h1, hH, ?_⟩
    rw [gap_eq hC hmin h0 h1 hH]
    exact_mod_cast hg

end SharpLSI.FL.Ex.LaneD
