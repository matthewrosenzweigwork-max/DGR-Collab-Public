import FullLabeledLSI.Examples.E01a_Common
import FullLabeledLSI.Examples.Paper.Sec9LamG
import FullLabeledLSI.Paper.Sec8Fourier5
import FullLabeledLSI.Paper.Sec8Fourier9
import SharpSymmetricLSI.Paper.CircleLSIExt
import SharpSymmetricLSI.Paper.CosineTest
import SharpSymmetricLSI.Paper.KLLsc
import SharpSymmetricLSI.Statements.R10_Lemma_3_2

/-!
# E01b: Lane A proofs for Section 9 (route plan `Audit/FLX/route_plan_20261008.md`)
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL
namespace Ex

theorem attrW_eq_WG (C : Torus 1 → ℝ) : attrW C = Sec8.WG (fun x => -C x) := by
  funext x y; simp [attrW, Sec8.WG]; ring

theorem Fstar_attr {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) : Fstar zeroV (attrW C) = ((C 0 / 2 : ℝ) : EReal) := by
  have hc : Continuous (fun x => -C x) := (continuous_of_isSmoothT hC.smooth).neg
  have h := hmin
  unfold IsMinimizer at h
  have hz : zeroV = fun _ => (0:ℝ) := rfl
  rw [← h, hz, attrW_eq_WG]
  have h1 : Sec8.meanT (fun x => -C x) = 0 := by
    have := hC.meanZero
    simp only [Sec8.meanT, integral_neg]
    have h2 : (volume : Measure (Torus 1)) = haar 1 := rfl
    rw [h2, this]; simp
  rw [show (haarPM : Measure (Torus 1)) = haar 1 from rfl, Sec8.freeEnergy_WG_haar hc, h1]
  congr 1; simp

theorem bar_nonneg' (F : Family 1) (hF : F.Admissible) : ∀ x, 0 ≤ F.bar x := fun x =>
  Finset.sum_nonneg fun a _ => mul_nonneg (hF.1 a).le ((hF.2.2 a).1 x)

theorem bar_integral' (F : Family 1) (hF : F.Admissible) : ∫ x, F.bar x ∂haar 1 = 1 := by
  have hi : ∀ a, Integrable (F.ρ a) (haar 1) := fun a => integrable_of_integral_eq_one' (hF.2.2 a).2.1
  unfold Family.bar
  rw [integral_finsetSum _ fun a _ => (hi a).const_mul _]
  simp_rw [integral_const_mul, (hF.2.2 _).2.1]
  simpa using hF.2.1

theorem Qint_attr {C : Torus 1 → ℝ} (hC : GoodKernel C) (F : Family 1) (hF : F.Admissible) :
    Sec8.Qint (densMeasure F.bar) (fun x => -C x) = -∫ x, F.bar x * convT C F.bar x ∂haar 1 := by
  have hc : Continuous (fun x => -C x) := (continuous_of_isSmoothT hC.smooth).neg
  have := isProbabilityMeasure_densMeasure' (bar_nonneg' F hF) (bar_integral' F hF)
  rw [Sec8.Qint_swap hc, ← integral_neg]
  rw [integral_densMeasure' (bar_nonneg' F hF) (bar_integral' F hF)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [integral_densMeasure' (bar_nonneg' F hF) (bar_integral' F hF), convT]
  have h : ∫ x1, F.bar x1 * -C (x - x1) ∂haar 1 = -∫ y, C (x - y) * F.bar y ∂haar 1 := by
    rw [← integral_neg]; congr 1; funext y; ring
  rw [h]; ring

theorem msGap_attr_proved {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (F : Family 1) (hF : F.Admissible) :
    msGap zeroV (attrW C) F =
      ((∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar 1) : ℝ≥0∞) : EReal) -
        ((1 / 2 * ∫ x, F.bar x * convT C F.bar x ∂haar 1 : ℝ) : EReal) := by
  have := isProbabilityMeasure_densMeasure' (bar_nonneg' F hF) (bar_integral' F hF)
  have hc : Continuous (fun x => -C x) := (continuous_of_isSmoothT hC.smooth).neg
  unfold msGap
  rw [Fstar_attr hC hmin]
  have hI : interE (attrW C) (densMeasure F.bar) (densMeasure F.bar) =
      -(∫ x, F.bar x * convT C F.bar x ∂haar 1) + C 0 := by
    rw [attrW_eq_WG, Sec8.interE_WG hc, Qint_attr hC F hF]; simp
  have hP : potE zeroV (densMeasure F.bar) = 0 := by simp [potE, zeroV]
  rw [hP, hI, sub_eq_add_neg, add_assoc, ← EReal.coe_neg, ← EReal.coe_add]
  rw [sub_eq_add_neg, ← EReal.coe_neg]
  congr 2
  ring


/-! ### Exact dissipation of a single density for `W = G(x-y) - G 0` -/

theorem sq_expand_eq {d : ℕ} {u : Torus d → ℝ} {w b : Fin d → Torus d → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hu : MemLp u 2 (haar d)) (hw : ∀ k, MemLp (w k) 2 (haar d))
    (hbm : ∀ k, Measurable (b k)) (hbb : ∀ k x, |b k x| ≤ C) :
    Integrable (fun x => ∑ k, (2 * w k x + u x * b k x) ^ 2) (haar d) ∧
    ∫ x, ∑ k, (2 * w k x + u x * b k x) ^ 2 ∂haar d =
      4 * ∑ k, ∫ x, w k x ^ 2 ∂haar d + 4 * ∑ k, ∫ x, u x * w k x * b k x ∂haar d +
        ∑ k, ∫ x, (u x * b k x) ^ 2 ∂haar d := by
  have iU2 : Integrable (fun x => u x ^ 2) (haar d) := hu.integrable_sq
  have iA : ∀ k, Integrable (fun x => w k x ^ 2) (haar d) := fun k => (hw k).integrable_sq
  have iB : ∀ k, Integrable (fun x => u x * w k x * b k x) (haar d) := fun k =>
    Integrable.mono' ((iU2.add (iA k)).const_mul C)
      (((hu.aestronglyMeasurable.mul (hw k).aestronglyMeasurable).mul
        (hbm k).aestronglyMeasurable)) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 : |u x| * |w k x| ≤ u x ^ 2 + w k x ^ 2 := by
          nlinarith [sq_abs (u x), sq_abs (w k x), sq_nonneg (|u x| - |w k x|)]
        calc |u x| * |w k x| * |b k x| ≤ (u x ^ 2 + w k x ^ 2) * C :=
              mul_le_mul h1 (hbb k x) (abs_nonneg _) (by positivity)
          _ = C * (u x ^ 2 + w k x ^ 2) := by ring)
  have iC : ∀ k, Integrable (fun x => (u x * b k x) ^ 2) (haar d) := fun k =>
    Integrable.mono' (iU2.const_mul (C ^ 2))
      ((hu.aestronglyMeasurable.mul (hbm k).aestronglyMeasurable).pow 2)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
        have : b k x ^ 2 ≤ C ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbb k x) 2
        calc u x ^ 2 * b k x ^ 2 ≤ u x ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_left this (sq_nonneg _)
          _ = C ^ 2 * u x ^ 2 := by ring)
  have hpt : ∀ k x, (2 * w k x + u x * b k x) ^ 2 =
      4 * w k x ^ 2 + 4 * (u x * w k x * b k x) + (u x * b k x) ^ 2 := fun k x => by ring
  have iT : ∀ k, Integrable (fun x => (2 * w k x + u x * b k x) ^ 2) (haar d) := fun k => by
    simp_rw [hpt]
    exact (((iA k).const_mul 4).add ((iB k).const_mul 4)).add (iC k)
  refine ⟨integrable_finsetSum _ fun k _ => iT k, ?_⟩
  rw [integral_finsetSum _ fun k _ => iT k]
  have hk : ∀ k, ∫ x, (2 * w k x + u x * b k x) ^ 2 ∂haar d =
      4 * ∫ x, w k x ^ 2 ∂haar d + 4 * ∫ x, u x * w k x * b k x ∂haar d +
        ∫ x, (u x * b k x) ^ 2 ∂haar d := fun k => by
    simp_rw [hpt]
    have h1 : Integrable (fun x => 4 * w k x ^ 2 + 4 * (u x * w k x * b k x)) (haar d) :=
      ((iA k).const_mul 4).add ((iB k).const_mul 4)
    rw [integral_add h1 (iC k), integral_add ((iA k).const_mul 4) ((iB k).const_mul 4),
      integral_const_mul, integral_const_mul]
  simp_rw [hk]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]


open Sec8 in
theorem dissipation_WG_eq {d : ℕ} {G : Torus d → ℝ} (hG : IsSmoothT G) (hGe : ∀ x, G (-x) = G x)
    {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    0 ≤ 4 * ∑ k, ∫ x, weakGrad (fun y => Real.sqrt (ρ y)) x k ^ 2 ∂haar d -
        2 * Qint (densMeasure ρ) (lap G) +
          ∑ k, ∫ x, ρ x * bForceL (WG G) ρ x k ^ 2 ∂haar d ∧
    dissipation (fun _ => (0 : ℝ)) (WG G) ρ = ENNReal.ofReal (
      4 * ∑ k, ∫ x, weakGrad (fun y => Real.sqrt (ρ y)) x k ^ 2 ∂haar d -
        2 * Qint (densMeasure ρ) (lap G) +
          ∑ k, ∫ x, ρ x * bForceL (WG G) ρ x k ^ 2 ∂haar d) := by
  obtain ⟨KW, hyp⟩ := hyp_WG hG hGe
  have hρi := integrable_of_integral_eq_one' hρ1
  set u : Torus d → ℝ := fun x => Real.sqrt (ρ x) with hudef
  have hw := isWeakGrad_weakGrad hH1.1
  have hu2 : MemLp u 2 (haar d) := hH1.2.1
  have hg2 : ∀ k, MemLp (fun x => weakGrad u x k) 2 (haar d) := fun k =>
    hH1.2.2.of_le (hw.aestronglyMeasurable_grad k) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ k)
  have hsq := isWeakGrad_sq hw hu2 hg2
  have hsq' : IsWeakGrad ρ (fun y k => 2 * u y * weakGrad u y k) := by
    have : (fun y => u y ^ 2) = ρ := funext fun x => Real.sq_sqrt (hρ0 x)
    rwa [this] at hsq
  have hb2 : ∀ a b : ℝ, |2 * a * b| ≤ a ^ 2 + b ^ 2 := fun a b => by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  have hgi : ∀ k, Integrable (fun y => 2 * u y * weakGrad u y k) (haar d) := fun k =>
    Integrable.mono' (hu2.integrable_sq.add (hg2 k).integrable_sq)
      ((hu2.aestronglyMeasurable.const_mul 2).mul (hg2 k).aestronglyMeasurable)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb2 _ _)
  have hcross := cross_term_eq hG hρ0 hρ1 hsq' hgi
  have hΦ : IsWeakGrad (fun x => (0 : ℝ) + convDens (WG G) ρ x) (bForceL (WG G) ρ) := by
    simpa using isWeakGrad_convDens' hyp hρi
  have hae : weakGrad (fun x => (0 : ℝ) + convDens (WG G) ρ x) =ᵐ[haar d] bForceL (WG G) ρ :=
    appA_weakGrad_ae_eq hΦ
  obtain ⟨C, hC0, hC⟩ := Sec8.abs_bForceL_le hG hρ0 hρ1
  obtain ⟨hint, heq⟩ := sq_expand_eq (u := u) (w := fun k x => weakGrad u x k)
    (b := fun k x => bForceL (WG G) ρ x k) hC0 hu2 hg2
    (fun k => measurable_bForceL' hyp hρi k) hC
  have e : ∀ k, ∫ x, 2 * u x * weakGrad u x k * bForceL (WG G) ρ x k ∂haar d =
      2 * ∫ x, u x * weakGrad u x k * bForceL (WG G) ρ x k ∂haar d := fun k => by
    rw [← integral_const_mul]; congr 1; funext x; ring
  simp_rw [e] at hcross
  rw [← Finset.mul_sum] at hcross
  have hr : ∀ k, ∫ x, (u x * bForceL (WG G) ρ x k) ^ 2 ∂haar d =
      ∫ x, ρ x * bForceL (WG G) ρ x k ^ 2 ∂haar d := fun k => by
    congr 1; funext x; rw [mul_pow, hudef]; simp only; rw [Real.sq_sqrt (hρ0 x)]
  have hX : 4 * ∑ k, ∫ x, weakGrad (fun y => Real.sqrt (ρ y)) x k ^ 2 ∂haar d -
        2 * Qint (densMeasure ρ) (lap G) +
          ∑ k, ∫ x, ρ x * bForceL (WG G) ρ x k ^ 2 ∂haar d =
      ∫ x, ∑ k, (2 * weakGrad u x k + u x * bForceL (WG G) ρ x k) ^ 2 ∂haar d := by
    rw [heq]
    simp_rw [hr]
    linarith
  refine ⟨hX ▸ integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _, ?_⟩
  unfold dissipation
  rw [if_pos ⟨hH1, ⟨_, hΦ⟩⟩]
  have hL3 : ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad u x k +
        u x * weakGrad (fun y => (fun _ => (0 : ℝ)) y + convDens (WG G) ρ y) x k) ^ 2) ∂haar d =
      ENNReal.ofReal (∫ x, ∑ k, (2 * weakGrad u x k + u x * bForceL (WG G) ρ x k) ^ 2 ∂haar d) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
      Finset.sum_nonneg fun k _ => sq_nonneg _)]
    refine lintegral_congr_ae (hae.mono fun x hx => ?_)
    have hx' : weakGrad (fun y => (fun _ => (0 : ℝ)) y + convDens (WG G) ρ y) x =
        bForceL (WG G) ρ x := hx
    simp only [hx']
  rw [hL3, hX]


/-! ### Bridge `dT` ↔ `dpart` -/

theorem liftT_rep (x : Torus 1) : liftT (fun _ : Fin 1 => rep x) = x := by
  funext i
  have h := (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1 : ℝ)) (x 0)).choose_spec
  rw [Subsingleton.elim i 0]
  exact h

theorem dpart_eq_dT {f : Torus 1 → ℝ} (hf : IsSmoothT f) (x : Torus 1) : dpart f 0 x = dT f x := by
  have hg : Differentiable ℝ (f ∘ liftT) := by unfold IsSmoothT at hf; exact hf.differentiable (by simp)
  have hx : x = liftT (fun _ : Fin 1 => rep x) := (liftT_rep x).symm
  rw [hx, dpart_liftT]
  unfold dT
  rw [liftT_rep]
  have hc : HasDerivAt (fun t : ℝ => (fun _ : Fin 1 => t)) (fun _ : Fin 1 => (1 : ℝ)) (rep x) :=
    hasDerivAt_pi.mpr fun _ => hasDerivAt_id _
  have := (hg (fun _ : Fin 1 => rep x)).hasFDerivAt.comp_hasDerivAt (rep x) hc
  rw [show (fun _ : Fin 1 => (1 : ℝ)) = Pi.single (0 : Fin 1) 1 from by
    funext i; rw [Subsingleton.elim i 0]; simp] at this
  exact this.deriv.symm


/-! ### `lap`, `bForceL` for the attractive kernel -/

theorem dT_eq_dpart {f : Torus 1 → ℝ} (hf : IsSmoothT f) : dT f = dpart f 0 :=
  funext fun x => (dpart_eq_dT hf x).symm

theorem isSmoothT_neg' {f : Torus 1 → ℝ} (hf : IsSmoothT f) : IsSmoothT (fun x => -f x) := by
  unfold IsSmoothT at *
  exact hf.neg

theorem dT_neg (f : Torus 1 → ℝ) (x : Torus 1) : dT (fun y => -f y) x = -dT f x := by
  unfold dT
  exact deriv.fun_neg (f := fun t : ℝ => f (liftT fun _ : Fin 1 => t)) |>.trans rfl

theorem dT_smooth {f : Torus 1 → ℝ} (hf : IsSmoothT f) : IsSmoothT (dT f) := by
  rw [dT_eq_dpart hf]; exact Sec8.isSmoothT_dpart hf 0

theorem lap_neg {C : Torus 1 → ℝ} (hC : IsSmoothT C) (x : Torus 1) :
    lap (fun y => -C y) x = -dT (dT C) x := by
  have h1 : dpart (fun y => -C y) 0 = fun y => -dT C y := by
    funext y; rw [← dT_eq_dpart (isSmoothT_neg' hC) |> fun h => congrFun h y, dT_neg]
  have h2 := dT_smooth hC
  simp only [lap, Fin.sum_univ_one, h1]
  rw [dpart_eq_dT (isSmoothT_neg' h2), dT_neg]

theorem bForceL_attr {C : Torus 1 → ℝ} (hC : GoodKernel C) (ρ : Torus 1 → ℝ) (x : Torus 1) :
    bForceL (attrW C) ρ x 0 = -convT (dT C) ρ x := by
  rw [attrW_eq_WG, Sec8.bForceL_WG (isSmoothT_neg' hC.smooth)]
  have h1 : dpart (fun y => -C y) 0 = fun y => -dT C y := by
    funext y; rw [← dT_eq_dpart (isSmoothT_neg' hC.smooth) |> fun h => congrFun h y, dT_neg]
  rw [h1]; unfold convT
  rw [← integral_neg]; congr 1; funext y; ring

theorem hyp_attr_aux {C : Torus 1 → ℝ} (hC : GoodKernel C) : ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW := by
  obtain ⟨KW, hyp⟩ := Sec8.hyp_WG (isSmoothT_neg' hC.smooth) (fun x => by simp [hC.even x])
  rw [attrW_eq_WG]
  exact ⟨0, KW, hyp⟩

theorem Qint_conv {K : Torus 1 → ℝ} (hK : Continuous K) (F : Family 1) (hF : F.Admissible) :
    Sec8.Qint (densMeasure F.bar) K = ∫ x, F.bar x * convT K F.bar x ∂haar 1 := by
  have := isProbabilityMeasure_densMeasure' (bar_nonneg' F hF) (bar_integral' F hF)
  rw [Sec8.Qint_swap hK, integral_densMeasure' (bar_nonneg' F hF) (bar_integral' F hF)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [integral_densMeasure' (bar_nonneg' F hF) (bar_integral' F hF), convT]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only; ring


theorem msDiss_attr_proved {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (F : Family 1) (hF : F.Admissible)
    (hfin : msDiss zeroV (attrW C) F ≠ ⊤) :
    (msDiss zeroV (attrW C) F).toReal =
      ∑ a, F.θ a * (fisherInfo (densMeasure (F.ρ a)) (haar 1)).toReal +
        2 * ∫ x, F.bar x * convT (dT (dT C)) F.bar x ∂haar 1 +
          ∫ x, F.bar x * (convT (dT C) F.bar x) ^ 2 ∂haar 1 := by
  obtain ⟨KV, KW, hyp⟩ := hyp_attr_aux hC
  have hdec := msDiss_decomp F hyp hF
  have hfi := Sec8.fisher_identity_d F hF
  have hb0 := bar_nonneg' F hF
  have hb1 := bar_integral' F hF
  have hH := memH1_sqrtBar F hF
  have hGs := isSmoothT_neg' hC.smooth
  have hGe : ∀ x, (fun y => -C y) (-x) = (fun y => -C y) x := fun x => by simp [hC.even x]
  obtain ⟨hXnn, hD⟩ := dissipation_WG_eq hGs hGe hb0 hb1 hH
  have hD' : dissipation zeroV (attrW C) F.bar = ENNReal.ofReal (
      4 * ∑ k, ∫ x, weakGrad (fun y => Real.sqrt (F.bar y)) x k ^ 2 ∂haar 1 -
        2 * Sec8.Qint (densMeasure F.bar) (lap fun y => -C y) +
          ∑ k, ∫ x, F.bar x * bForceL (Sec8.WG fun y => -C y) F.bar x k ^ 2 ∂haar 1) := by
    rw [attrW_eq_WG]; exact hD
  have hlt := (msGap_msDiss_lt_top (by norm_num) hyp hF).2.2
  simp only [Fin.sum_univ_one] at hD' hXnn
  -- the interaction terms
  have hlapc : Continuous (lap fun y => -C y) := continuous_of_isSmoothT (Sec8.isSmoothT_lap hGs)
  have hQ : Sec8.Qint (densMeasure F.bar) (lap fun y => -C y) =
      -∫ x, F.bar x * convT (dT (dT C)) F.bar x ∂haar 1 := by
    rw [Qint_conv hlapc F hF, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [convT, lap_neg hC.smooth]
    rw [← mul_neg, ← integral_neg]; congr 2; funext y; ring
  have hB : ∫ x, F.bar x * bForceL (Sec8.WG fun y => -C y) F.bar x 0 ^ 2 ∂haar 1 =
      ∫ x, F.bar x * (convT (dT C) F.bar x) ^ 2 ∂haar 1 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← attrW_eq_WG, bForceL_attr hC]; ring
  rw [hQ, hB] at hD'
  rw [hQ, hB] at hXnn
  -- species Fisher informations
  have hfa : ∀ a, fisherInfo (densMeasure (F.ρ a)) (haar 1) =
      ENNReal.ofReal (4 * ∫ x, weakGrad (fun x => Real.sqrt (F.ρ a x)) x 0 ^ 2 ∂haar 1) :=
    fun a => fisherInfo_densMeasure_eq (hF.2.2 a).1 (hF.2.2 a).2.1 (hF.2.2 a).2.2
  have hD2nn : ∀ ρ : Torus 1 → ℝ, 0 ≤ ∫ x, weakGrad (fun x => Real.sqrt (ρ x)) x 0 ^ 2 ∂haar 1 :=
    fun ρ => integral_nonneg fun x => sq_nonneg _
  have hD2eq : ∀ ρ : Torus 1 → ℝ, Sec8.D2 ρ = ∫ x, weakGrad (fun x => Real.sqrt (ρ x)) x 0 ^ 2 ∂haar 1 :=
    fun ρ => by simp [Sec8.D2, Fin.sum_univ_one]
  set S : ℝ := ∑ a, F.θ a * (4 * ∫ x, weakGrad (fun x => Real.sqrt (F.ρ a x)) x 0 ^ 2 ∂haar 1) with hSdef
  set D2b : ℝ := ∫ x, weakGrad (fun x => Real.sqrt (F.bar x)) x 0 ^ 2 ∂haar 1 with hD2b
  set R : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar with hR
  have hRtop : R ≠ ⊤ := (ENNReal.add_lt_top.1 (hdec ▸ hlt)).2.ne
  have hLHS : ∑ a, ENNReal.ofReal (F.θ a) * ENNReal.ofReal (4 * Sec8.D2 (F.ρ a)) = ENNReal.ofReal S := by
    rw [hSdef, ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hF.1 a).le
      (mul_nonneg (by norm_num) (hD2nn _)))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ENNReal.ofReal_mul (hF.1 a).le, hD2eq]
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun a _ => mul_nonneg (hF.1 a).le
    (mul_nonneg (by norm_num) (hD2nn _))
  have hS : S = 4 * D2b + R.toReal := by
    have := congrArg ENNReal.toReal hfi
    rw [hLHS, ENNReal.toReal_ofReal hSnn, ENNReal.toReal_add ENNReal.ofReal_ne_top hRtop,
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (by rw [hD2eq]; exact hD2nn _)), hD2eq] at this
    exact this
  rw [hdec, ENNReal.toReal_add (by
      rw [hD']; exact ENNReal.ofReal_ne_top) hRtop, hD', ENNReal.toReal_ofReal hXnn]
  have hfa' : ∑ a, F.θ a * (fisherInfo (densMeasure (F.ρ a)) (haar 1)).toReal = S := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hfa, ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (hD2nn _))]
  rw [hfa']
  linarith


theorem hyp_attr_proved {C : Torus 1 → ℝ} (hC : GoodKernel C) :
    ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW := hyp_attr_aux hC

theorem msDiss_ne_top_attr_proved {C : Torus 1 → ℝ} (hC : GoodKernel C) (F : Family 1)
    (hF : F.Admissible) : msDiss zeroV (attrW C) F ≠ ⊤ := by
  obtain ⟨KV, KW, hyp⟩ := hyp_attr_aux hC
  exact (msGap_msDiss_lt_top (by norm_num) hyp hF).2.2.ne



theorem agreement_of_bounds_proved {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (hyp : ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hlow : ENNReal.ofReal ℓ ≤ rMs zeroV (attrW C))
    (hup : ∀ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ),
      IsRefEigenbasis (haar 1) e lam → IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm →
        lamG (lamShift lam) Cm ≤ ENNReal.ofReal ℓ) :
    AgreementAt (attrW C) ℓ := by
  obtain ⟨KV, KW, hyp⟩ := hyp
  have hd : 1 ≤ 1 := le_rfl
  have hMS_le : rMs zeroV (attrW C) ≤ rStar zeroV (attrW C) := (upper_comparison hd hyp).2
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal ℓ := ENNReal.ofReal_pos.mpr hℓ
  have hr : 0 < rStar zeroV (attrW C) := lt_of_lt_of_le hpos (hlow.trans hMS_le)
  have hlam : ∀ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ),
      IsRefEigenbasis (haar 1) e lam → IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm →
        lamG (lamShift lam) Cm = ENNReal.ofReal ℓ := fun e lam Cm he hCm =>
    le_antisymm (hup e lam Cm he hCm)
      (hlow.trans (hMS_le.trans (rStar_le_lamG hd hyp hr hmin he hCm)))
  have hMS : rMs zeroV (attrW C) = ENNReal.ofReal ℓ := by
    obtain ⟨e, lam, he⟩ := (ref_spectrum hd hyp hr hmin).1
    obtain ⟨Cm, hCm⟩ := exists_inverseOfIPlus hyp haarPM hd hr hmin he
    exact le_antisymm (hMS_le.trans ((rStar_le_lamG hd hyp hr hmin he hCm).trans
      (hlam e lam Cm he hCm).le)) hlow
  have hRS : rStar zeroV (attrW C) = ENNReal.ofReal ℓ := by
    obtain ⟨e, lam, he⟩ := (ref_spectrum hd hyp hr hmin).1
    obtain ⟨Cm, hCm⟩ := exists_inverseOfIPlus hyp haarPM hd hr hmin he
    exact le_antisymm ((rStar_le_lamG hd hyp hr hmin he hCm).trans (hlam e lam Cm he hCm).le)
      (hlow.trans hMS_le)
  refine ⟨hMS, hRS, ⟨?_, hlam⟩, ?_, ?_⟩
  · obtain ⟨e, lam, he⟩ := (ref_spectrum hd hyp hr hmin).1
    obtain ⟨Cm, hCm⟩ := exists_inverseOfIPlus hyp haarPM hd hr hmin he
    exact ⟨e, lam, Cm, he, hCm⟩
  · rw [← hMS]; exact full_labeled_lsi_limit hd hyp
  · rw [← hRS]; exact sharp_symmetric_lsi_limit hd hyp


section Bessel
open Real intervalIntegral

theorem A_rec (j : ℕ) : ∫ x in (0:ℝ)..(2 * π), cos x ^ (2 * (j + 1)) =
    (2 * j + 1) / (2 * j + 2) * ∫ x in (0:ℝ)..(2 * π), cos x ^ (2 * j) := by
  have := integral_cos_pow (a := 0) (b := 2 * π) (2 * j)
  simp only [sin_zero, mul_zero, sub_zero, sin_two_pi, zero_div, zero_add] at this
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, this]
  push_cast; ring_nf

theorem A_bound (j : ℕ) : (∫ s in (0:ℝ)..1, cos (2 * π * s) ^ (2 * j)) * (4 ^ j * j.factorial) ≤
    (2 * j).factorial := by
  have h1 : ∀ n : ℕ, ∫ s in (0:ℝ)..1, cos (2 * π * s) ^ n =
      (2 * π)⁻¹ * ∫ x in (0:ℝ)..(2 * π), cos x ^ n := fun n => by
    rw [intervalIntegral.integral_comp_mul_left (fun x => cos x ^ n) (by positivity)]
    simp
  induction j with
  | zero => simp
  | succ j ih =>
    rw [h1] at ih ⊢
    rw [A_rec]
    have hpos : (0:ℝ) < 2 * π := by positivity
    push_cast [Nat.factorial_succ, pow_succ] at *
    set a := ∫ x in (0:ℝ)..(2 * π), cos x ^ (2 * j)
    have hf : (0:ℝ) < ((2*j).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have e : (2 * (j+1)).factorial = (2*j+2) * (2*j+1) * (2*j).factorial := by
      rw [show 2 * (j+1) = (2*j+1)+1 by ring, Nat.factorial_succ, Nat.factorial_succ]; ring
    rw [e]; push_cast
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    have e2 : (2 * π)⁻¹ * ((2 * (j:ℝ) + 1) / (2 * j + 2) * a) * (4 ^ j * 4 * ((j + 1) * (j.factorial:ℝ))) =
        2 * (2 * j + 1) * ((2 * π)⁻¹ * a * (4 ^ j * (j.factorial:ℝ))) := by
      field_simp; ring
    rw [e2]
    nlinarith [mul_le_mul_of_nonneg_left ih (by positivity : (0:ℝ) ≤ 2 * (2 * j + 1)), mul_nonneg hj hf.le]


theorem J_symm (t : ℝ) : ∫ s in (0:ℝ)..1, exp (t * cos (2 * π * s)) =
    ∫ s in (0:ℝ)..1, exp (-(t * cos (2 * π * s))) := by
  set f : ℝ → ℝ := fun s => exp (-(t * cos (2 * π * s))) with hf
  have hper : Function.Periodic f 1 := fun s => by
    simp only [hf]; congr 3; rw [mul_add, mul_one, cos_add_two_pi]
  have h1 : ∫ s in (0:ℝ)..1, exp (t * cos (2 * π * s)) = ∫ s in (0:ℝ)..1, f (s + 1/2) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hf]
    rw [mul_add, show 2 * π * (1/2:ℝ) = π by ring, cos_add_pi]; simp
  rw [h1, intervalIntegral.integral_comp_add_right f (1/2)]
  have := hper.intervalIntegral_add_eq (1/2) 0
  simpa [add_comm] using (by rw [show (0:ℝ) + 1 = 1 by ring] at this; linarith [this] : ∫ x in (1/2:ℝ)..(1/2 + 1), f x = ∫ x in (0:ℝ)..1, f x)


theorem J_le (t : ℝ) : ∫ s in (0:ℝ)..1, exp (t * cos (2 * π * s)) ≤ exp (t ^ 2 / 4) := by
  have hcosh : ∫ s in (0:ℝ)..1, exp (t * cos (2 * π * s)) =
      ∫ s in (0:ℝ)..1, Real.cosh (t * cos (2 * π * s)) := by
    have hc1 : IntervalIntegrable (fun s : ℝ => exp (t * cos (2 * π * s))) volume 0 1 :=
      (by fun_prop : Continuous fun s : ℝ => exp (t * cos (2 * π * s))).intervalIntegrable _ _
    have hc2 : IntervalIntegrable (fun s : ℝ => exp (-(t * cos (2 * π * s)))) volume 0 1 :=
      (by fun_prop : Continuous fun s : ℝ => exp (-(t * cos (2 * π * s)))).intervalIntegrable _ _
    simp_rw [Real.cosh_eq]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add hc1 hc2, ← J_symm t]
    ring
  rw [hcosh, intervalIntegral.integral_of_le zero_le_one]
  have hevenpow : ∀ n : ℕ, 0 ≤ t ^ (2 * n) := fun n => by
    have : t ^ (2 * n) = (t ^ n) ^ 2 := by ring
    rw [this]; positivity
  have hF : ∀ n : ℕ, Integrable (fun s : ℝ => (t * cos (2 * π * s)) ^ (2 * n) / ((2 * n).factorial : ℝ))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
    fun n => (by fun_prop : Continuous fun s : ℝ => (t * cos (2 * π * s)) ^ (2 * n) /
      ((2 * n).factorial : ℝ)).integrableOn_Ioc
  have hint : ∀ n : ℕ, ∫ s in Set.Ioc (0:ℝ) 1, (t * cos (2 * π * s)) ^ (2 * n) / ((2 * n).factorial : ℝ) =
      t ^ (2 * n) * (∫ s in (0:ℝ)..1, cos (2 * π * s) ^ (2 * n)) / ((2 * n).factorial : ℝ) := fun n => by
    rw [MeasureTheory.integral_div, ← intervalIntegral.integral_of_le zero_le_one]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun s _ => by simp only [mul_pow]
  have hbound : ∀ n : ℕ, t ^ (2 * n) * (∫ s in (0:ℝ)..1, cos (2 * π * s) ^ (2 * n)) / ((2 * n).factorial : ℝ) ≤
      (t ^ 2 / 4) ^ n / (n.factorial : ℝ) := fun n => by
    have h1 := A_bound n
    have hf : (0:ℝ) < ((2 * n).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hn : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have ht := hevenpow n
    have : (t ^ 2 / 4) ^ n = t ^ (2 * n) / 4 ^ n := by rw [div_pow, ← pow_mul]
    rw [this, div_div, div_le_div_iff₀ hf (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 ht]
  have hAnn : ∀ n : ℕ, 0 ≤ ∫ s in (0:ℝ)..1, cos (2 * π * s) ^ (2 * n) := fun n =>
    intervalIntegral.integral_nonneg zero_le_one fun s _ => by
      have : cos (2 * π * s) ^ (2 * n) = (cos (2 * π * s) ^ n) ^ 2 := by ring
      rw [this]; positivity
  have hnorm : ∀ n : ℕ, ∫ s in Set.Ioc (0:ℝ) 1, ‖(t * cos (2 * π * s)) ^ (2 * n) / ((2 * n).factorial : ℝ)‖ =
      ∫ s in Set.Ioc (0:ℝ) 1, (t * cos (2 * π * s)) ^ (2 * n) / ((2 * n).factorial : ℝ) := fun n => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only
    rw [Real.norm_eq_abs, abs_of_nonneg]
    have : (t * cos (2 * π * s)) ^ (2 * n) = ((t * cos (2 * π * s)) ^ n) ^ 2 := by ring
    rw [this]; positivity
  have hsum_exp : HasSum (fun n : ℕ => (t ^ 2 / 4) ^ n / (n.factorial : ℝ)) (exp (t ^ 2 / 4)) := by
    have := NormedSpace.expSeries_div_hasSum_exp (t ^ 2 / 4)
    rwa [← Real.exp_eq_exp_ℝ] at this
  have hnn : ∀ n : ℕ, 0 ≤ ∫ s in Set.Ioc (0:ℝ) 1, (t * cos (2 * π * s)) ^ (2 * n) / ((2 * n).factorial : ℝ) :=
    fun n => by
    rw [hint]; exact div_nonneg (mul_nonneg (hevenpow n) (hAnn n)) (Nat.cast_nonneg _)
  have hsumm : Summable fun n : ℕ => ∫ s in Set.Ioc (0:ℝ) 1,
      ‖(t * cos (2 * π * s)) ^ (2 * n) / ((2 * n).factorial : ℝ)‖ := by
    simp_rw [hnorm]
    refine Summable.of_nonneg_of_le hnn (fun n => ?_) hsum_exp.summable
    rw [hint]; exact hbound n
  have hts := integral_tsum_of_summable_integral_norm hF hsumm
  have hpt : ∀ s : ℝ, HasSum (fun n : ℕ => (t * cos (2 * π * s)) ^ (2 * n) / ((2 * n).factorial : ℝ))
      (Real.cosh (t * cos (2 * π * s))) := fun s => Real.hasSum_cosh _
  calc ∫ s in Set.Ioc (0:ℝ) 1, Real.cosh (t * cos (2 * π * s))
      = ∫ s in Set.Ioc (0:ℝ) 1, ∑' n : ℕ, (t * cos (2 * π * s)) ^ (2 * n) / ((2 * n).factorial : ℝ) := by
        congr 1; funext s; exact (hpt s).tsum_eq.symm
    _ = ∑' n : ℕ, ∫ s in Set.Ioc (0:ℝ) 1, (t * cos (2 * π * s)) ^ (2 * n) / ((2 * n).factorial : ℝ) := hts.symm
    _ ≤ ∑' n : ℕ, (t ^ 2 / 4) ^ n / (n.factorial : ℝ) := by
        refine Summable.tsum_le_tsum (fun n => ?_) ?_ hsum_exp.summable
        · rw [hint]; exact hbound n
        · exact Summable.of_nonneg_of_le hnn (fun n => by rw [hint]; exact hbound n) hsum_exp.summable
    _ = exp (t ^ 2 / 4) := hsum_exp.tsum_eq


end Bessel

theorem periodic_comp {h : ℝ → ℝ} (hper : Function.Periodic h 1) (hc : Continuous h) (k : ℕ) (hk : 1 ≤ k) (d : ℝ) :
    ∫ s in (0:ℝ)..1, h ((k:ℝ) * s + d) = ∫ s in (0:ℝ)..1, h s := by
  have hk0 : (k:ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_add h hk0 d]
  simp only [mul_zero, zero_add, mul_one, smul_eq_mul]
  have h1 := hper.intervalIntegral_add_zsmul_eq (k:ℤ) d (fun _ _ => hc.intervalIntegrable _ _)
  have h2 := hper.intervalIntegral_add_eq d 0
  simp only [zsmul_eq_mul, Int.cast_natCast, mul_one, smul_eq_mul, zero_add] at h1 h2
  rw [add_comm (k:ℝ) d, h1, h2, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]


theorem torus_J {k : ℕ} (hk : 1 ≤ k) (β t : ℝ) :
    ∫ y : Torus 1, Real.exp (t * (Complex.exp (β * Complex.I) * fourier (k : ℤ) (y 0)).re) ∂haar 1 =
      ∫ s in (0:ℝ)..1, Real.exp (t * Real.cos (2 * π * s)) := by
  rw [integral_torus1 (fun z => Real.exp (t * (Complex.exp (β * Complex.I) * fourier (k : ℤ) z).re))]
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hper : Function.Periodic (fun s : ℝ => Real.exp (t * Real.cos (2 * π * s))) 1 := fun s => by
    show Real.exp (t * Real.cos (2 * π * (s + 1))) = Real.exp (t * Real.cos (2 * π * s))
    rw [show 2 * π * (s + 1) = 2 * π * s + 2 * π by ring, Real.cos_add_two_pi]
  have hc : Continuous (fun s : ℝ => Real.exp (t * Real.cos (2 * π * s))) := by fun_prop
  rw [← periodic_comp hper hc k hk (β / (2 * π))]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show Real.exp (t * (Complex.exp (β * Complex.I) * fourier (k : ℤ) (s : UnitAddCircle)).re) =
    Real.exp (t * Real.cos (2 * π * ((k:ℝ) * s + β / (2 * π))))
  rw [fourier_coe_apply, ← Complex.exp_add]
  simp only [Complex.ofReal_one, div_one]
  have : (β : ℂ) * Complex.I + 2 * π * Complex.I * (k : ℤ) * s =
      ((β + 2 * π * k * s : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]
  congr 3
  field_simp
  ring


theorem fourier_entropy_bound_proved {k : ℕ} (hk : 1 ≤ k) (ρ : Torus 1 → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) :
    ENNReal.ofReal (Complex.normSq (∫ x, fourier (k : ℤ) (x 0) * (ρ x : ℂ) ∂haar 1)) ≤
      klDiv (densMeasure ρ) (haar 1) := by
  set m : ℂ := ∫ x, fourier (k : ℤ) (x 0) * (ρ x : ℂ) ∂haar 1 with hm
  by_cases hm0 : m = 0
  · simp [hm0]
  have hρi : Integrable ρ (haar 1) := integrable_of_integral_eq_one' hρ1
  have hP := isProbabilityMeasure_densMeasure' hρ0 hρ1
  set M : ℝ := ‖m‖ with hM
  have hMpos : 0 < M := norm_pos_iff.mpr hm0
  set β : ℝ := -Complex.arg m with hβ
  set u : ℂ := Complex.exp (β * Complex.I) with hu
  have hum : u * m = (M : ℂ) := by
    have h := Complex.norm_mul_exp_arg_mul_I m
    rw [hu, hβ]
    conv_lhs => rw [← h]
    rw [← mul_assoc, mul_comm _ (‖m‖ : ℂ), mul_assoc, ← Complex.exp_add]
    push_cast
    simp [hM]
  set t : ℝ := 2 * M with ht
  set g : Torus 1 → ℝ := fun x => t * (u * fourier (k : ℤ) (x 0)).re with hg
  have hfc : Continuous (fun x : Torus 1 => fourier (k : ℤ) (x 0)) :=
    (fourier (k : ℤ)).continuous.comp (continuous_apply 0)
  have hgc : Continuous g := continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul hfc))
  have hunit : ‖u‖ = 1 := by rw [hu]; exact Complex.norm_exp_ofReal_mul_I β
  have hgB : ∀ x, |g x| ≤ |t| := fun x => by
    simp only [hg, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    calc |(u * fourier (k : ℤ) (x 0)).re| ≤ ‖u * fourier (k : ℤ) (x 0)‖ := Complex.abs_re_le_norm _
      _ ≤ 1 := by
        rw [norm_mul, hunit, one_mul]
        exact ((fourier (k : ℤ)).norm_coe_le_norm (x 0)).trans (fourier_norm _).le
  have hdv := dvFun_le_klDiv (ρ := densMeasure ρ) (ν := haar 1) hgc.measurable hgB
  -- the linear term
  have hint : Integrable (fun x : Torus 1 => u * (fourier (k : ℤ) (x 0) * (ρ x : ℂ))) (haar 1) := by
    refine Integrable.const_mul ?_ u
    exact Integrable.bdd_mul (f := fun x : Torus 1 => fourier (k : ℤ) (x 0)) (c := 1) hρi.ofReal
      hfc.aestronglyMeasurable (Eventually.of_forall fun x =>
        ((fourier (k : ℤ)).norm_coe_le_norm (x 0)).trans (fourier_norm _).le)
  have hre : (u * m).re = M := by rw [hum]; simp
  have hlin : ∫ x, g x ∂densMeasure ρ = 2 * M ^ 2 := by
    rw [integral_densMeasure' hρ0 hρ1]
    have h1 : ∀ x, ρ x * g x = t * (u * (fourier (k : ℤ) (x 0) * (ρ x : ℂ))).re := fun x => by
      simp only [hg]
      rw [show u * (fourier (k : ℤ) (x 0) * (ρ x : ℂ)) = (u * fourier (k : ℤ) (x 0)) * (ρ x : ℂ) by ring,
        Complex.re_mul_ofReal]
      ring
    simp_rw [h1]
    have hr := integral_re hint
    simp only [RCLike.re_to_complex] at hr
    rw [integral_const_mul, hr, integral_const_mul, ← hm, hre, ht]
    ring
  -- the exponential moment
  have hexp : ∫ x, Real.exp (g x) ∂haar 1 = ∫ s in (0:ℝ)..1, Real.exp (t * Real.cos (2 * π * s)) :=
    torus_J hk β t
  have hexp_int : Integrable (fun x => Real.exp (g x)) (haar 1) :=
    (Real.continuous_exp.comp hgc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpos := integral_exp_pos (μ := haar 1) (f := g) hexp_int
  have hJ := J_le t
  have hlog : Real.log (∫ x, Real.exp (g x) ∂haar 1) ≤ M ^ 2 := by
    rw [Real.log_le_iff_le_exp hpos]
    calc ∫ x, Real.exp (g x) ∂haar 1 ≤ Real.exp (t ^ 2 / 4) := hexp ▸ hJ
      _ = Real.exp (M ^ 2) := by rw [ht]; ring_nf
  have hdv' : M ^ 2 ≤ dvFun (densMeasure ρ) (haar 1) g := by
    unfold dvFun; rw [hlin]; linarith
  have hnormSq : Complex.normSq m = M ^ 2 := by rw [Complex.normSq_eq_norm_sq]
  rw [hnormSq]
  by_cases htop : klDiv (densMeasure ρ) (haar 1) = ⊤
  · rw [htop]; exact le_top
  · have hfin : (klDiv (densMeasure ρ) (haar 1)) = ENNReal.ofReal (klDiv (densMeasure ρ) (haar 1)).toReal :=
      (ENNReal.ofReal_toReal htop).symm
    have h2 : (dvFun (densMeasure ρ) (haar 1) g : ℝ) ≤ (klDiv (densMeasure ρ) (haar 1)).toReal := by
      rw [← EReal.coe_ennreal_toReal htop] at hdv
      exact EReal.coe_le_coe_iff.mp hdv
    rw [hfin]
    exact ENNReal.ofReal_le_ofReal ((hdv'.trans h2))



/-- `sin(2π k x)` on `𝕋^1`. -/
noncomputable def sinMode (k : ℕ) (x : Torus 1) : ℝ := (fourier (k : ℤ) (x 0)).im

theorem cosMode_liftT (k : ℕ) (t : ℝ) : cosMode k (liftT fun _ : Fin 1 => t) = Real.cos (2 * π * k * t) := by
  unfold cosMode liftT
  simp only
  rw [fourier_coe_apply]
  push_cast
  rw [show (2 * (π : ℂ) * Complex.I * k * t / 1) = ((2 * π * k * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

theorem sinMode_liftT (k : ℕ) (t : ℝ) : sinMode k (liftT fun _ : Fin 1 => t) = Real.sin (2 * π * k * t) := by
  unfold sinMode liftT
  simp only
  rw [fourier_coe_apply]
  push_cast
  rw [show (2 * (π : ℂ) * Complex.I * k * t / 1) = ((2 * π * k * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_im]

theorem cosMode_eq_rep (k : ℕ) (x : Torus 1) : cosMode k x = Real.cos (2 * π * k * rep x) := by
  conv_lhs => rw [← liftT_rep x]
  exact cosMode_liftT k _

theorem sinMode_eq_rep (k : ℕ) (x : Torus 1) : sinMode k x = Real.sin (2 * π * k * rep x) := by
  conv_lhs => rw [← liftT_rep x]
  exact sinMode_liftT k _

theorem dT_cosMode (k : ℕ) (x : Torus 1) : dT (cosMode k) x = -(2 * π * k) * sinMode k x := by
  unfold dT
  simp_rw [cosMode_liftT]
  rw [sinMode_eq_rep]
  have h : HasDerivAt (fun t : ℝ => Real.cos (2 * π * k * t)) (-Real.sin (2 * π * k * rep x) * (2 * π * k * 1)) (rep x) :=
    ((hasDerivAt_id' (rep x)).const_mul (2 * π * k)).cos
  rw [h.deriv]; ring

theorem dT_sinMode (k : ℕ) (x : Torus 1) : dT (sinMode k) x = (2 * π * k) * cosMode k x := by
  unfold dT
  simp_rw [sinMode_liftT]
  rw [cosMode_eq_rep]
  have h : HasDerivAt (fun t : ℝ => Real.sin (2 * π * k * t)) (Real.cos (2 * π * k * rep x) * (2 * π * k * 1)) (rep x) :=
    ((hasDerivAt_id' (rep x)).const_mul (2 * π * k)).sin
  rw [h.deriv]; ring

theorem sub_eq_liftT (x y : Torus 1) : x - y = liftT (fun _ : Fin 1 => rep x - rep y) := by
  funext i
  rw [Subsingleton.elim i 0]
  have hx : x 0 = ((rep x : ℝ) : UnitAddCircle) := congrFun (liftT_rep x).symm 0
  have hy : y 0 = ((rep y : ℝ) : UnitAddCircle) := congrFun (liftT_rep y).symm 0
  show x 0 - y 0 = _
  rw [hx, hy]
  rfl

theorem cosMode_sub (x y : Torus 1) :
    cosMode 1 (x - y) = cosMode 1 x * cosMode 1 y + sinMode 1 x * sinMode 1 y := by
  rw [sub_eq_liftT, cosMode_liftT, cosMode_eq_rep, cosMode_eq_rep, sinMode_eq_rep, sinMode_eq_rep]
  push_cast
  rw [show 2 * π * 1 * (rep x - rep y) = 2 * π * 1 * rep x - 2 * π * 1 * rep y by ring, Real.cos_sub]

theorem sinMode_sub (x y : Torus 1) :
    sinMode 1 (x - y) = sinMode 1 x * cosMode 1 y - cosMode 1 x * sinMode 1 y := by
  rw [sub_eq_liftT, sinMode_liftT, cosMode_eq_rep, cosMode_eq_rep, sinMode_eq_rep, sinMode_eq_rep]
  push_cast
  rw [show 2 * π * 1 * (rep x - rep y) = 2 * π * 1 * rep x - 2 * π * 1 * rep y by ring, Real.sin_sub]


theorem continuous_cosMode (k : ℕ) : Continuous (cosMode k) :=
  Complex.continuous_re.comp ((fourier (k : ℤ)).continuous.comp (continuous_apply 0))

theorem continuous_sinMode (k : ℕ) : Continuous (sinMode k) :=
  Complex.continuous_im.comp ((fourier (k : ℤ)).continuous.comp (continuous_apply 0))

theorem abs_cosMode_le (k : ℕ) (x : Torus 1) : |cosMode k x| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (((fourier (k : ℤ)).norm_coe_le_norm (x 0)).trans (fourier_norm _).le)

theorem abs_sinMode_le (k : ℕ) (x : Torus 1) : |sinMode k x| ≤ 1 :=
  (Complex.abs_im_le_norm _).trans (((fourier (k : ℤ)).norm_coe_le_norm (x 0)).trans (fourier_norm _).le)

theorem integrable_mode_mul {f : Torus 1 → ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ 1) {ρ : Torus 1 → ℝ}
    (hρi : Integrable ρ (haar 1)) : Integrable (fun x => f x * ρ x) (haar 1) :=
  Integrable.bdd_mul (c := 1) hρi hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

theorem dT_const_mul (c : ℝ) (f : Torus 1 → ℝ) (x : Torus 1) :
    dT (fun y => c * f y) x = c * dT f x := by
  unfold dT
  exact congrFun (deriv_const_mul_field' (𝕜 := ℝ) (v := fun t : ℝ => f (liftT fun _ : Fin 1 => t)) c) (rep x)

theorem dT_harm (a : ℝ) (x : Torus 1) : dT (harmKernel 1 a) x = -(4 * π * a) * sinMode 1 x := by
  have : harmKernel 1 a = fun y => (2 * a) * cosMode 1 y := by
    funext y; unfold harmKernel; ring
  rw [this, dT_const_mul, dT_cosMode]; push_cast; ring

theorem dT_dT_harm (a : ℝ) (x : Torus 1) : dT (dT (harmKernel 1 a)) x = -(8 * π ^ 2 * a) * cosMode 1 x := by
  have : dT (harmKernel 1 a) = fun y => (-(4 * π * a)) * sinMode 1 y := by
    funext y; exact dT_harm a y
  rw [this, dT_const_mul, dT_sinMode]; push_cast; ring


/-- First cosine/sine moments `A = ∫ cos(2πx) ρ`, `B = ∫ sin(2πx) ρ`. -/
noncomputable def momA (ρ : Torus 1 → ℝ) : ℝ := ∫ x, cosMode 1 x * ρ x ∂haar 1
noncomputable def momB (ρ : Torus 1 → ℝ) : ℝ := ∫ x, sinMode 1 x * ρ x ∂haar 1

theorem conv_cos {ρ : Torus 1 → ℝ} (hρi : Integrable ρ (haar 1)) (x : Torus 1) :
    convT (cosMode 1) ρ x = cosMode 1 x * momA ρ + sinMode 1 x * momB ρ := by
  have hc := integrable_mode_mul (continuous_cosMode 1) (abs_cosMode_le 1) hρi
  have hs := integrable_mode_mul (continuous_sinMode 1) (abs_sinMode_le 1) hρi
  unfold convT momA momB
  have : ∀ y, cosMode 1 (x - y) * ρ y = cosMode 1 x * (cosMode 1 y * ρ y) + sinMode 1 x * (sinMode 1 y * ρ y) :=
    fun y => by rw [cosMode_sub]; ring
  simp_rw [this]
  rw [integral_add (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]

theorem conv_sin {ρ : Torus 1 → ℝ} (hρi : Integrable ρ (haar 1)) (x : Torus 1) :
    convT (sinMode 1) ρ x = sinMode 1 x * momA ρ - cosMode 1 x * momB ρ := by
  have hc := integrable_mode_mul (continuous_cosMode 1) (abs_cosMode_le 1) hρi
  have hs := integrable_mode_mul (continuous_sinMode 1) (abs_sinMode_le 1) hρi
  unfold convT momA momB
  have : ∀ y, sinMode 1 (x - y) * ρ y = sinMode 1 x * (cosMode 1 y * ρ y) - cosMode 1 x * (sinMode 1 y * ρ y) :=
    fun y => by rw [sinMode_sub]; ring
  simp_rw [this]
  rw [integral_sub (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]

theorem convT_const_mul (c : ℝ) (g ρ : Torus 1 → ℝ) (x : Torus 1) :
    convT (fun y => c * g y) ρ x = c * convT g ρ x := by
  unfold convT
  rw [← integral_const_mul]
  congr 1; funext y; ring

theorem conv_harm {ρ : Torus 1 → ℝ} (hρi : Integrable ρ (haar 1)) (a : ℝ) (x : Torus 1) :
    convT (harmKernel 1 a) ρ x = 2 * a * (cosMode 1 x * momA ρ + sinMode 1 x * momB ρ) := by
  have : harmKernel 1 a = fun y => (2 * a) * cosMode 1 y := by
    funext y; unfold harmKernel; ring
  rw [this, convT_const_mul, conv_cos hρi]

theorem conv_dT_harm {ρ : Torus 1 → ℝ} (hρi : Integrable ρ (haar 1)) (a : ℝ) (x : Torus 1) :
    convT (dT (harmKernel 1 a)) ρ x = -(4 * π * a) * (sinMode 1 x * momA ρ - cosMode 1 x * momB ρ) := by
  have : dT (harmKernel 1 a) = fun y => (-(4 * π * a)) * sinMode 1 y := funext fun y => dT_harm a y
  rw [this, convT_const_mul, conv_sin hρi]

theorem conv_dT_dT_harm {ρ : Torus 1 → ℝ} (hρi : Integrable ρ (haar 1)) (a : ℝ) (x : Torus 1) :
    convT (dT (dT (harmKernel 1 a))) ρ x = -(8 * π ^ 2 * a) * (cosMode 1 x * momA ρ + sinMode 1 x * momB ρ) := by
  have : dT (dT (harmKernel 1 a)) = fun y => (-(8 * π ^ 2 * a)) * cosMode 1 y :=
    funext fun y => dT_dT_harm a y
  rw [this, convT_const_mul, conv_cos hρi]

theorem int_rho_linear {ρ : Torus 1 → ℝ} (hρi : Integrable ρ (haar 1)) (p q : ℝ) :
    ∫ x, ρ x * (cosMode 1 x * p + sinMode 1 x * q) ∂haar 1 = momA ρ * p + momB ρ * q := by
  have hc := integrable_mode_mul (continuous_cosMode 1) (abs_cosMode_le 1) hρi
  have hs := integrable_mode_mul (continuous_sinMode 1) (abs_sinMode_le 1) hρi
  unfold momA momB
  have : ∀ x, ρ x * (cosMode 1 x * p + sinMode 1 x * q) = (cosMode 1 x * ρ x) * p + (sinMode 1 x * ρ x) * q :=
    fun x => by ring
  simp_rw [this]
  rw [integral_add (hc.mul_const _) (hs.mul_const _), integral_mul_const, integral_mul_const]


theorem cosMode_one_eq_gCos : cosMode 1 = gCos := rfl

theorem neg_eq_liftT (x : Torus 1) : -x = liftT (fun _ : Fin 1 => -rep x) := by
  funext i
  rw [Subsingleton.elim i 0]
  have hx : x 0 = ((rep x : ℝ) : UnitAddCircle) := congrFun (liftT_rep x).symm 0
  show -(x 0) = _
  rw [hx]
  rfl

theorem cosMode_neg (x : Torus 1) : cosMode 1 (-x) = cosMode 1 x := by
  rw [neg_eq_liftT, cosMode_liftT, cosMode_eq_rep]
  push_cast
  rw [mul_neg, Real.cos_neg]

theorem goodKernel_harm (a : ℝ) : GoodKernel (harmKernel 1 a) where
  smooth := by
    have h : harmKernel 1 a = fun y => (2 * a) * gCos y := by
      funext y; unfold harmKernel; rw [cosMode_one_eq_gCos]
    rw [h]
    unfold IsSmoothT
    exact contDiff_const.mul contDiff_gCos_lift
  even := fun x => by
    unfold harmKernel; rw [cosMode_neg]
  meanZero := by
    have h : harmKernel 1 a = fun y => (2 * a) * gCos y := by
      funext y; unfold harmKernel; rw [cosMode_one_eq_gCos]
    rw [h, integral_const_mul, integral_gCos]; ring


theorem fourier_entropy_bound_meas {k : ℕ} (hk : 1 ≤ k) (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    ENNReal.ofReal (Complex.normSq (∫ x, fourier (k : ℤ) (x 0) ∂μ)) ≤ klDiv μ (haar 1) := by
  set m : ℂ := ∫ x, fourier (k : ℤ) (x 0) ∂μ with hm
  by_cases hm0 : m = 0
  · simp [hm0]
  set M : ℝ := ‖m‖ with hM
  have hMpos : 0 < M := norm_pos_iff.mpr hm0
  set β : ℝ := -Complex.arg m with hβ
  set u : ℂ := Complex.exp (β * Complex.I) with hu
  have hum : u * m = (M : ℂ) := by
    have h := Complex.norm_mul_exp_arg_mul_I m
    rw [hu, hβ]
    conv_lhs => rw [← h]
    rw [← mul_assoc, mul_comm _ (‖m‖ : ℂ), mul_assoc, ← Complex.exp_add]
    push_cast
    simp [hM]
  set t : ℝ := 2 * M with ht
  set g : Torus 1 → ℝ := fun x => t * (u * fourier (k : ℤ) (x 0)).re with hg
  have hfc : Continuous (fun x : Torus 1 => fourier (k : ℤ) (x 0)) :=
    (fourier (k : ℤ)).continuous.comp (continuous_apply 0)
  have hgc : Continuous g := continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul hfc))
  have hunit : ‖u‖ = 1 := by rw [hu]; exact Complex.norm_exp_ofReal_mul_I β
  have hgB : ∀ x, |g x| ≤ |t| := fun x => by
    simp only [hg, abs_mul]
    refine mul_le_of_le_one_right (abs_nonneg _) ?_
    calc |(u * fourier (k : ℤ) (x 0)).re| ≤ ‖u * fourier (k : ℤ) (x 0)‖ := Complex.abs_re_le_norm _
      _ ≤ 1 := by
        rw [norm_mul, hunit, one_mul]
        exact ((fourier (k : ℤ)).norm_coe_le_norm (x 0)).trans (fourier_norm _).le
  have hdv := dvFun_le_klDiv (ρ := μ) (ν := haar 1) hgc.measurable hgB
  have hfi : Integrable (fun x : Torus 1 => fourier (k : ℤ) (x 0)) μ :=
    hfc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hre : (u * m).re = M := by rw [hum]; simp
  have hlin : ∫ x, g x ∂μ = 2 * M ^ 2 := by
    have hr := integral_re (hfi.const_mul u)
    simp only [RCLike.re_to_complex] at hr
    simp only [hg]
    rw [integral_const_mul, hr, integral_const_mul, ← hm, hre, ht]
    ring
  have hexp : ∫ x, Real.exp (g x) ∂haar 1 = ∫ s in (0:ℝ)..1, Real.exp (t * Real.cos (2 * π * s)) :=
    torus_J hk β t
  have hexp_int : Integrable (fun x => Real.exp (g x)) (haar 1) :=
    (Real.continuous_exp.comp hgc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpos := integral_exp_pos (μ := haar 1) (f := g) hexp_int
  have hJ := J_le t
  have hlog : Real.log (∫ x, Real.exp (g x) ∂haar 1) ≤ M ^ 2 := by
    rw [Real.log_le_iff_le_exp hpos]
    calc ∫ x, Real.exp (g x) ∂haar 1 ≤ Real.exp (t ^ 2 / 4) := hexp ▸ hJ
      _ = Real.exp (M ^ 2) := by rw [ht]; ring_nf
  have hdv' : M ^ 2 ≤ dvFun μ (haar 1) g := by
    unfold dvFun; rw [hlin]; linarith
  have hnormSq : Complex.normSq m = M ^ 2 := by rw [Complex.normSq_eq_norm_sq]
  rw [hnormSq]
  by_cases htop : klDiv μ (haar 1) = ⊤
  · rw [htop]; exact le_top
  · have hfin : (klDiv μ (haar 1)) = ENNReal.ofReal (klDiv μ (haar 1)).toReal :=
      (ENNReal.ofReal_toReal htop).symm
    have h2 : (dvFun μ (haar 1) g : ℝ) ≤ (klDiv μ (haar 1)).toReal := by
      rw [← EReal.coe_ennreal_toReal htop] at hdv
      exact EReal.coe_le_coe_iff.mp hdv
    rw [hfin]
    exact ENNReal.ofReal_le_ofReal ((hdv'.trans h2))


theorem cosMode_zero : cosMode 1 0 = 1 := by
  unfold cosMode; simp

/-- Real moments of a probability measure. -/
noncomputable def mA (μ : Measure (Torus 1)) : ℝ := ∫ x, cosMode 1 x ∂μ
noncomputable def mB (μ : Measure (Torus 1)) : ℝ := ∫ x, sinMode 1 x ∂μ

theorem normSq_fourier_one (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    Complex.normSq (∫ x, fourier ((1 : ℕ) : ℤ) (x 0) ∂μ) = mA μ ^ 2 + mB μ ^ 2 := by
  have hfc : Continuous (fun x : Torus 1 => fourier ((1 : ℕ) : ℤ) (x 0)) :=
    (fourier ((1 : ℕ) : ℤ)).continuous.comp (continuous_apply (0 : Fin 1))
  have hfi : Integrable (fun x : Torus 1 => fourier ((1 : ℕ) : ℤ) (x 0)) μ :=
    hfc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [Complex.normSq_apply]
  have h1 := integral_re hfi
  have h2 := integral_im hfi
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at h1 h2
  rw [← h1, ← h2]
  unfold mA mB cosMode sinMode
  ring

theorem interE_harm (a : ℝ) (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    interE (attrW (harmKernel 1 a)) μ μ = 2 * a - 2 * a * (mA μ ^ 2 + mB μ ^ 2) := by
  have hc : Integrable (cosMode 1) μ :=
    (continuous_cosMode 1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Integrable (sinMode 1) μ :=
    (continuous_sinMode 1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have key : ∀ p q : ℝ, ∫ x, (2 * a - p * cosMode 1 x - q * sinMode 1 x) ∂μ =
      2 * a - p * mA μ - q * mB μ := fun p q => by
    rw [integral_sub (f := fun x => 2 * a - p * cosMode 1 x) (g := fun x => q * sinMode 1 x)
        ((integrable_const _).sub (hc.const_mul p)) (hs.const_mul q),
      integral_sub (f := fun _ => 2 * a) (g := fun x => p * cosMode 1 x) (integrable_const _)
        (hc.const_mul p), integral_const_mul, integral_const_mul, integral_const_mul]
    simp [mA, mB]
  unfold interE attrW harmKernel
  simp only [cosMode_zero]
  have : ∀ y, ∫ x, (2 * a * 1 - 2 * a * cosMode 1 (x - y)) ∂μ =
      2 * a - 2 * a * cosMode 1 y * mA μ - 2 * a * sinMode 1 y * mB μ := fun y => by
    rw [← key]
    congr 1; funext x
    rw [cosMode_sub]; ring
  simp_rw [this]
  have hI : ∀ y, 2 * a - 2 * a * cosMode 1 y * mA μ - 2 * a * sinMode 1 y * mB μ =
      2 * a - (2 * a * mA μ) * cosMode 1 y - (2 * a * mB μ) * sinMode 1 y := fun y => by ring
  simp_rw [hI]
  rw [key]
  unfold mA mB
  ring


theorem freeEnergy_harm (a : ℝ) (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    freeEnergy zeroV (attrW (harmKernel 1 a)) μ =
      ((klDiv μ (haar 1) : ℝ≥0∞) : EReal) + ((a - a * (mA μ ^ 2 + mB μ ^ 2) : ℝ) : EReal) := by
  unfold freeEnergy
  rw [interE_harm]
  simp only [potE, zeroV, integral_zero, zero_add]
  congr 2; ring

theorem mA_haar : mA (haar 1) = 0 := integral_gCos
theorem mB_haar : mB (haar 1) = 0 := integral_sCos

theorem freeEnergy_harm_haar (a : ℝ) : freeEnergy zeroV (attrW (harmKernel 1 a)) (haar 1) = ((a : ℝ) : EReal) := by
  rw [freeEnergy_harm, klDiv_self, mA_haar, mB_haar]
  simp only [EReal.coe_ennreal_zero, zero_add]
  congr 1; ring

theorem n_le_klDiv (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] :
    ENNReal.ofReal (mA μ ^ 2 + mB μ ^ 2) ≤ klDiv μ (haar 1) := by
  have := fourier_entropy_bound_meas (k := 1) le_rfl μ
  rwa [normSq_fourier_one] at this

theorem Fstar_harm {a : ℝ} (ha1 : a ≤ 1) :
    Fstar zeroV (attrW (harmKernel 1 a)) = ((a : ℝ) : EReal) := by
  apply le_antisymm
  · exact (iInf_le (fun ρ : ProbabilityMeasure (Torus 1) => freeEnergy zeroV (attrW (harmKernel 1 a)) ρ)
      ⟨haar 1, inferInstance⟩).trans (freeEnergy_harm_haar a).le
  · refine le_iInf fun μ => ?_
    have : IsProbabilityMeasure (μ : Measure (Torus 1)) := inferInstance
    rw [freeEnergy_harm]
    by_cases hK : klDiv (μ : Measure (Torus 1)) (haar 1) = ⊤
    · rw [hK, EReal.coe_ennreal_top, EReal.top_add_coe]; exact le_top
    · have hn := n_le_klDiv (μ : Measure (Torus 1))
      have hn' : mA (μ : Measure (Torus 1)) ^ 2 + mB (μ : Measure (Torus 1)) ^ 2 ≤
          (klDiv (μ : Measure (Torus 1)) (haar 1)).toReal := by
        have := ENNReal.toReal_mono hK hn
        rwa [ENNReal.toReal_ofReal (by positivity)] at this
      rw [← EReal.coe_ennreal_toReal hK, ← EReal.coe_add]
      refine EReal.coe_le_coe_iff.mpr ?_
      have hq : 0 ≤ mA (μ : Measure (Torus 1)) ^ 2 + mB (μ : Measure (Torus 1)) ^ 2 := by positivity
      nlinarith

theorem isMinimizer_harm_iff {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (μ : ProbabilityMeasure (Torus 1)) :
    IsMinimizer zeroV (attrW (harmKernel 1 a)) μ ↔ (μ : Measure (Torus 1)) = haar 1 := by
  have : IsProbabilityMeasure (μ : Measure (Torus 1)) := inferInstance
  unfold IsMinimizer
  rw [Fstar_harm ha1.le, freeEnergy_harm]
  constructor
  · intro h
    have hK : klDiv (μ : Measure (Torus 1)) (haar 1) ≠ ⊤ := by
      intro hK; rw [hK, EReal.coe_ennreal_top, EReal.top_add_coe] at h; simp at h
    rw [← EReal.coe_ennreal_toReal hK, ← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    have hn := n_le_klDiv (μ : Measure (Torus 1))
    have hn' : mA (μ : Measure (Torus 1)) ^ 2 + mB (μ : Measure (Torus 1)) ^ 2 ≤
        (klDiv (μ : Measure (Torus 1)) (haar 1)).toReal := by
      have := ENNReal.toReal_mono hK hn
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hq : 0 ≤ mA (μ : Measure (Torus 1)) ^ 2 + mB (μ : Measure (Torus 1)) ^ 2 := by positivity
    have hk0 := ENNReal.toReal_nonneg (a := klDiv (μ : Measure (Torus 1)) (haar 1))
    have hk : (klDiv (μ : Measure (Torus 1)) (haar 1)).toReal = 0 := by nlinarith
    have : klDiv (μ : Measure (Torus 1)) (haar 1) = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hk with h0 | h0
      · exact h0
      · exact absurd h0 hK
    exact (klDiv_eq_zero_iff).mp this
  · intro h
    rw [h, klDiv_self, mA_haar, mB_haar]
    simp only [EReal.coe_ennreal_zero, zero_add]
    congr 1; ring

theorem harmMinimizer {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HaarUniqueMinimizer (attrW (harmKernel 1 a)) := by
  refine ⟨(isMinimizer_harm_iff ha0 ha1 haarPM).2 rfl, fun μ hμ => ?_⟩
  have := (isMinimizer_harm_iff ha0 ha1 μ).1 hμ
  exact Subtype.ext (by simpa [haarPM] using this)


theorem haar_isMin {a : ℝ} (ha1 : a ≤ 1) :
    IsMinimizer zeroV (attrW (harmKernel 1 a)) haarPM := by
  unfold IsMinimizer
  rw [Fstar_harm ha1]
  exact freeEnergy_harm_haar a

/-- Species entropies and Fisher informations as reals. -/
noncomputable def sumH (F : Family 1) : ℝ := ∑ b, F.θ b * (klDiv (densMeasure (F.ρ b)) (haar 1)).toReal
noncomputable def sumI (F : Family 1) : ℝ := ∑ b, F.θ b * (fisherInfo (densMeasure (F.ρ b)) (haar 1)).toReal

theorem species_fin (F : Family 1) (hF : F.Admissible) (b : Fin F.q) :
    klDiv (densMeasure (F.ρ b)) (haar 1) ≠ ⊤ ∧ fisherInfo (densMeasure (F.ρ b)) (haar 1) ≠ ⊤ := by
  have h := circle_quantitative_lsi (hF.2.2 b).1 (hF.2.2 b).2.1 (hF.2.2 b).2.2
  exact ⟨h.1, h.2.1⟩

theorem msGap_harm_real {a : ℝ} (ha1 : a ≤ 1) (F : Family 1) (hF : F.Admissible) :
    (msGap zeroV (attrW (harmKernel 1 a)) F).toReal =
      sumH F - a * (momA F.bar ^ 2 + momB F.bar ^ 2) := by
  have hg := msGap_attr_proved (goodKernel_harm a) (haar_isMin ha1) F hF
  have hρi : Integrable F.bar (haar 1) := integrable_of_integral_eq_one' (bar_integral' F hF)
  have hfin : (∑ b, ENNReal.ofReal (F.θ b) * klDiv (densMeasure (F.ρ b)) (haar 1) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun b _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (species_fin F hF b).1
  have hI : (1 / 2 * ∫ x, F.bar x * convT (harmKernel 1 a) F.bar x ∂haar 1 : ℝ) =
      a * (momA F.bar ^ 2 + momB F.bar ^ 2) := by
    simp_rw [conv_harm hρi]
    have : ∀ x, F.bar x * (2 * a * (cosMode 1 x * momA F.bar + sinMode 1 x * momB F.bar)) =
        (2 * a) * (F.bar x * (cosMode 1 x * momA F.bar + sinMode 1 x * momB F.bar)) := fun x => by ring
    simp_rw [this]
    rw [integral_const_mul, int_rho_linear hρi]; ring
  rw [hg, hI, ← EReal.coe_ennreal_toReal hfin, ← EReal.coe_sub, EReal.toReal_coe]
  unfold sumH
  rw [ENNReal.toReal_sum (fun b _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (species_fin F hF b).1)]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hF.1 b).le]


/-- `Ψ = ∫ ρ̄ (A sin - B cos)²`, the quadratic-coefficient integral. -/
noncomputable def psiInt (ρ : Torus 1 → ℝ) : ℝ :=
  ∫ x, ρ x * (sinMode 1 x * momA ρ - cosMode 1 x * momB ρ) ^ 2 ∂haar 1

theorem msDiss_harm_real {a : ℝ} (ha1 : a ≤ 1) (F : Family 1) (hF : F.Admissible) :
    (msDiss zeroV (attrW (harmKernel 1 a)) F).toReal =
      sumI F - 16 * π ^ 2 * a * (momA F.bar ^ 2 + momB F.bar ^ 2) + 16 * π ^ 2 * a ^ 2 * psiInt F.bar := by
  have hd := msDiss_attr_proved (goodKernel_harm a) (haar_isMin ha1) F hF
    (msDiss_ne_top_attr_proved (goodKernel_harm a) F hF)
  have hρi : Integrable F.bar (haar 1) := integrable_of_integral_eq_one' (bar_integral' F hF)
  rw [hd]
  have h2 : 2 * ∫ x, F.bar x * convT (dT (dT (harmKernel 1 a))) F.bar x ∂haar 1 =
      -(16 * π ^ 2 * a) * (momA F.bar ^ 2 + momB F.bar ^ 2) := by
    simp_rw [conv_dT_dT_harm hρi]
    have : ∀ x, F.bar x * (-(8 * π ^ 2 * a) * (cosMode 1 x * momA F.bar + sinMode 1 x * momB F.bar)) =
        (-(8 * π ^ 2 * a)) * (F.bar x * (cosMode 1 x * momA F.bar + sinMode 1 x * momB F.bar)) := fun x => by ring
    simp_rw [this]
    rw [integral_const_mul, int_rho_linear hρi]; ring
  have h3 : ∫ x, F.bar x * (convT (dT (harmKernel 1 a)) F.bar x) ^ 2 ∂haar 1 =
      16 * π ^ 2 * a ^ 2 * psiInt F.bar := by
    simp_rw [conv_dT_harm hρi]
    unfold psiInt
    rw [← integral_const_mul]
    congr 1; funext x; ring
  rw [h2, h3]
  unfold sumI
  ring


theorem momAB_dens (F : Family 1) (hF : F.Admissible) :
    mA (densMeasure F.bar) ^ 2 + mB (densMeasure F.bar) ^ 2 = momA F.bar ^ 2 + momB F.bar ^ 2 := by
  have hA : mA (densMeasure F.bar) = momA F.bar := by
    unfold mA momA
    rw [integral_densMeasure' (bar_nonneg' F hF) (bar_integral' F hF)]
    congr 1; funext x; ring
  have hB : mB (densMeasure F.bar) = momB F.bar := by
    unfold mB momB
    rw [integral_densMeasure' (bar_nonneg' F hF) (bar_integral' F hF)]
    congr 1; funext x; ring
  rw [hA, hB]

theorem sumH_ge_N (F : Family 1) (hF : F.Admissible) : momA F.bar ^ 2 + momB F.bar ^ 2 ≤ sumH F := by
  have hP := isProbabilityMeasure_densMeasure' (bar_nonneg' F hF) (bar_integral' F hF)
  have hn := n_le_klDiv (densMeasure F.bar)
  rw [momAB_dens F hF] at hn
  have hid := entropy_identity F hF
  have hfin : (∑ b, ENNReal.ofReal (F.θ b) * klDiv (densMeasure (F.ρ b)) (haar 1) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun b _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (species_fin F hF b).1
  have hle : ENNReal.ofReal (momA F.bar ^ 2 + momB F.bar ^ 2) ≤
      ∑ b, ENNReal.ofReal (F.θ b) * klDiv (densMeasure (F.ρ b)) (haar 1) := by
    rw [hid]
    exact hn.trans le_self_add
  have := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_ofReal (by positivity)] at this
  refine this.trans (le_of_eq ?_)
  unfold sumH
  rw [ENNReal.toReal_sum (fun b _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (species_fin F hF b).1)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hF.1 b).le]

theorem sumI_ge (F : Family 1) (hF : F.Admissible) : 8 * π ^ 2 * sumH F ≤ sumI F := by
  unfold sumH sumI
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have h := circle_quantitative_lsi (hF.2.2 b).1 (hF.2.2 b).2.1 (hF.2.2 b).2.2
  have h4 := h.2.2.2
  have hH : 0 ≤ (klDiv (densMeasure (F.ρ b)) (haar 1)).toReal := ENNReal.toReal_nonneg
  have hac : aCos = 4 * π ^ 2 := rfl
  have hθ := (hF.1 b).le
  have : 2 * aCos * (klDiv (densMeasure (F.ρ b)) (haar 1)).toReal ≤
      (fisherInfo (densMeasure (F.ρ b)) (haar 1)).toReal := by
    have hq : 0 ≤ aCos / 6 * (klDiv (densMeasure (F.ρ b)) (haar 1)).toReal ^ 2 := by
      rw [hac]; positivity
    linarith
  rw [hac] at this
  nlinarith [mul_le_mul_of_nonneg_left this hθ]

theorem harm_deficit {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (F : Family 1) (hF : F.Admissible) :
    8 * π ^ 2 * (1 - a) * (msGap zeroV (attrW (harmKernel 1 a)) F).toReal ≤
      (msDiss zeroV (attrW (harmKernel 1 a)) F).toReal := by
  rw [msGap_harm_real ha1 F hF, msDiss_harm_real ha1 F hF]
  have hD1 := ENNReal.toReal_nonneg (a := msDiss zeroV (attrW (harmKernel 1 1)) F)
  rw [msDiss_harm_real le_rfl F hF] at hD1
  have hE := sumH_ge_N F hF
  have hX := sumI_ge F hF
  have hπ : 0 < π ^ 2 := by positivity
  have hΨ : 0 ≤ psiInt F.bar := by
    unfold psiInt
    exact integral_nonneg fun x => mul_nonneg (bar_nonneg' F hF x) (sq_nonneg _)
  set N := momA F.bar ^ 2 + momB F.bar ^ 2 with hN
  set Ψ := psiInt F.bar
  rcases le_or_gt 0 (2 * Ψ - N) with hc | hc
  · nlinarith [mul_nonneg ha0 (sub_nonneg.2 hE), mul_nonneg (mul_nonneg ha0 ha0) hc, hπ]
  · have h1 : 0 ≤ a * (1 - a) * (-(2 * Ψ - N)) :=
      mul_nonneg (mul_nonneg ha0 (sub_nonneg.2 ha1)) (by linarith)
    nlinarith [mul_nonneg ha0 (sub_nonneg.2 hE), h1, hπ, mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hX),
      mul_nonneg ha0 hD1]


theorem harm_rMs_ge {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    ENNReal.ofReal (aCos * (1 - a)) ≤ rMs zeroV (attrW (harmKernel 1 a)) := by
  obtain ⟨KV, KW, hyp⟩ := hyp_attr_aux (goodKernel_harm a)
  unfold rMs
  refine le_iInf₂ fun F hF => ?_
  obtain ⟨hFa, hFg⟩ := hF
  obtain ⟨hgtop, hgbot, hdtop⟩ := msGap_msDiss_lt_top (by norm_num) hyp hFa
  have hGfin := hgtop.ne
  have hGeq : ((msGap zeroV (attrW (harmKernel 1 a)) F).toReal : EReal) =
      msGap zeroV (attrW (harmKernel 1 a)) F := EReal.coe_toReal hGfin hgbot.ne'
  have hGpos : 0 < (msGap zeroV (attrW (harmKernel 1 a)) F).toReal := by
    rw [← hGeq] at hFg
    exact EReal.coe_pos.mp hFg
  have hGen : (msGap zeroV (attrW (harmKernel 1 a)) F).toENNReal =
      ENNReal.ofReal (msGap zeroV (attrW (harmKernel 1 a)) F).toReal := by
    unfold EReal.toENNReal; rw [if_neg hGfin]
  have hDeq : msDiss zeroV (attrW (harmKernel 1 a)) F =
      ENNReal.ofReal (msDiss zeroV (attrW (harmKernel 1 a)) F).toReal :=
    (ENNReal.ofReal_toReal hdtop.ne).symm
  rw [hGen]
  set G := (msGap zeroV (attrW (harmKernel 1 a)) F).toReal
  set D := (msDiss zeroV (attrW (harmKernel 1 a)) F).toReal
  rw [hDeq]
  have hdef := harm_deficit ha0 ha1.le F hFa
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hGpos])) (Or.inl (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by unfold aCos; nlinarith [Real.pi_pos])]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold aCos
  nlinarith [hdef]


theorem int_fourier (m : ℤ) : ∫ y : Torus 1, fourier m (y 0) ∂haar 1 = if m = 0 then 1 else 0 := by
  have h := integral_mFourier (ι := Fin 1) (fun _ => m)
  have e : ∀ y : Torus 1, UnitAddTorus.mFourier (fun _ : Fin 1 => m) y = fourier m (y 0) := fun y => by
    simp [UnitAddTorus.mFourier]
  simp_rw [e] at h
  rw [h]
  have hiff : ((fun _ : Fin 1 => m) = 0) ↔ m = 0 :=
    ⟨fun h => congrFun h 0, fun h => funext fun _ => h⟩
  simp only [hiff]

theorem cosMode_complex (x : Torus 1) :
    (cosMode 1 x : ℂ) = (fourier 1 (x 0) + fourier (-1) (x 0)) / 2 := by
  unfold cosMode
  rw [fourier_neg]
  simp only [Nat.cast_one]
  rw [Complex.add_conj]
  simp

theorem chat_harm (a : ℝ) (n : ℤ) : chat (harmKernel 1 a) n = if n = 1 ∨ n = -1 then a else 0 := by
  unfold chat
  have hexp : ∀ x : Torus 1, fourier (-n) (x 0) * (harmKernel 1 a x : ℂ) =
      a * (fourier (-n + 1) (x 0) + fourier (-n - 1) (x 0)) := fun x => by
    unfold harmKernel
    push_cast
    rw [cosMode_complex, fourier_add, show -n - 1 = -n + -1 by ring, fourier_add]
    ring
  simp_rw [hexp]
  have hfi : ∀ m : ℤ, Integrable (fun x : Torus 1 => fourier m (x 0)) (haar 1) := fun m =>
    ((fourier m).continuous.comp (continuous_apply (0 : Fin 1))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_const_mul, integral_add (hfi _) (hfi _), int_fourier, int_fourier]
  by_cases h1 : n = 1
  · subst h1; simp
  · by_cases h2 : n = -1
    · subst h2; simp
    · have e1 : ¬ (-n + 1 = 0) := fun h => h1 (by omega)
      have e2 : ¬ (-n - 1 = 0) := fun h => h2 (by omega)
      simp [e1, e2, h1, h2]

theorem chat_harm_le {a : ℝ} (ha0 : 0 ≤ a) (n : ℤ) : chat (harmKernel 1 a) n ≤ a := by
  rw [chat_harm]; split_ifs <;> linarith


/-- Proposition 9.2 (`first_attractive_cosine`).  The upper bound `λ_G ≤ ℓ` inside `AgreementAt` uses
lane D's proved `LaneD.lamG_formula` (Paper/Sec9LamG), not the E01a stub. -/
theorem first_attractive_cosine_proved {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    HaarUniqueMinimizer (attrW (harmKernel 1 a)) ∧ Fstar zeroV (attrW (harmKernel 1 a)) = (a : EReal) ∧
      AgreementAt (attrW (harmKernel 1 a)) (aCos * (1 - a)) := by
  refine ⟨harmMinimizer ha0 ha1, Fstar_harm ha1.le, ?_⟩
  have hC := goodKernel_harm a
  have hℓ : 0 < aCos * (1 - a) := by
    unfold aCos; exact mul_pos (by positivity) (by linarith)
  refine agreement_of_bounds_proved hC (haar_isMin ha1.le) (hyp_attr_aux hC) hℓ (harm_rMs_ge ha0 ha1) ?_
  intro e lam Cm he hCm
  have hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat (harmKernel 1 a) n ≤ 1 - δ :=
    ⟨1 - a, by linarith, fun n _ => by have := chat_harm_le ha0 n; linarith⟩
  rw [LaneD.lamG_formula hC (haar_isMin ha1.le) (hyp_attr_aux hC) hsup e lam Cm he hCm]
  refine (iInf_le _ 0).trans (le_of_eq ?_)
  have h1 : chat (harmKernel 1 a) (((0 : ℕ) : ℤ) + 1) = a := by
    rw [chat_harm]; simp
  rw [h1]
  congr 1
  simp



/-- The three interaction functionals of a density. -/
noncomputable def KK (C : Torus 1 → ℝ) (ρ : Torus 1 → ℝ) : ℝ := ∫ x, ρ x * convT C ρ x ∂haar 1
noncomputable def JJ (C : Torus 1 → ℝ) (ρ : Torus 1 → ℝ) : ℝ := ∫ x, ρ x * convT (dT (dT C)) ρ x ∂haar 1
noncomputable def LL (C : Torus 1 → ℝ) (ρ : Torus 1 → ℝ) : ℝ := ∫ x, ρ x * (convT (dT C) ρ x) ^ 2 ∂haar 1

theorem msGap_attr_real {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (F : Family 1) (hF : F.Admissible) :
    (msGap zeroV (attrW C) F).toReal = sumH F - 1 / 2 * KK C F.bar := by
  have hg := msGap_attr_proved hC hmin F hF
  have hfin : (∑ b, ENNReal.ofReal (F.θ b) * klDiv (densMeasure (F.ρ b)) (haar 1) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun b _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (species_fin F hF b).1
  rw [hg, ← EReal.coe_ennreal_toReal hfin, ← EReal.coe_sub, EReal.toReal_coe]
  unfold sumH
  rw [ENNReal.toReal_sum (fun b _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (species_fin F hF b).1)]
  unfold KK
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hF.1 b).le]

theorem msDiss_attr_real {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (F : Family 1) (hF : F.Admissible) :
    (msDiss zeroV (attrW C) F).toReal = sumI F + 2 * JJ C F.bar + LL C F.bar := by
  rw [msDiss_attr_proved hC hmin F hF (msDiss_ne_top_attr_proved hC F hF)]
  rfl


theorem convS_dens (g ρ : Torus 1 → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar 1 = 1) (x : Torus 1) :
    convS g (densMeasure ρ) 0 x = convT g ρ x := by
  unfold convS intS convT
  rw [integral_densMeasure' hρ0 hρ1]
  simp only [integral_zero_measure, sub_zero]
  congr 1; funext y; ring

theorem Uint_dens (C : Torus 1 → ℝ) (ℓ : ℝ) (ρ : Torus 1 → ℝ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar 1 = 1) :
    Uint C ℓ (densMeasure ρ) 0 = 2 * JJ C ρ + LL C ρ + ℓ * KK C ρ := by
  unfold Uint
  have hc : ∀ f : Torus 1 → ℝ, intS f (densMeasure ρ) 0 = ∫ x, ρ x * f x ∂haar 1 := fun f => by
    unfold intS; rw [integral_densMeasure' hρ0 hρ1]; simp
  simp_rw [hc, convS_dens _ _ hρ0 hρ1]
  rfl


theorem uint_concave_sum {C : Torus 1 → ℝ} {ℓ : ℝ} (hconc : UintConcave C ℓ) {ι : Type*} [DecidableEq ι]
    (μ : ι → Measure (Torus 1)) (hμ : ∀ i, IsProbabilityMeasure (μ i)) (s : Finset ι) :
    ∀ w : ι → ℝ, (∀ i ∈ s, 0 < w i) → ∑ i ∈ s, w i = 1 →
      ∑ i ∈ s, w i * Uint C ℓ (μ i) 0 ≤ Uint C ℓ (∑ i ∈ s, ENNReal.ofReal (w i) • μ i) 0 := by
  induction s using Finset.induction_on with
  | empty => intro w _ h; simp at h
  | insert j s hj ih =>
    intro w hw hw1
    rw [Finset.sum_insert hj] at hw1
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hwj : 0 < w j := hw j (Finset.mem_insert_self _ _)
    by_cases hs : s = ∅
    · subst hs
      simp at hw1 ⊢
      rw [hw1]; simp
    · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
      have hws : ∀ i ∈ s, 0 < w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
      set c : ℝ := ∑ i ∈ s, w i with hc
      have hcpos : 0 < c := Finset.sum_pos hws hne
      have hcj : c = 1 - w j := by linarith
      have hw'sum : ∑ i ∈ s, w i / c = 1 := by rw [← Finset.sum_div, ← hc, div_self hcpos.ne']
      have hIH := ih (fun i => w i / c) (fun i hi => div_pos (hws i hi) hcpos) hw'sum
      set ν : Measure (Torus 1) := ∑ i ∈ s, ENNReal.ofReal (w i / c) • μ i with hν
      have hνP : IsProbabilityMeasure ν := by
        constructor
        rw [hν, Measure.coe_finsetSum, Finset.sum_apply]
        simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => (div_pos (hws i hi) hcpos).le), hw'sum]
        simp
      have ht1 : w j ≤ 1 := by linarith
      have hconcj := hconc ν (μ j) hνP (hμ j) (w j) hwj.le ht1
      have hmeas : ENNReal.ofReal (1 - w j) • ν + ENNReal.ofReal (w j) • μ j =
          ENNReal.ofReal (w j) • μ j + ∑ i ∈ s, ENNReal.ofReal (w i) • μ i := by
        rw [add_comm, hν, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [smul_smul, ← ENNReal.ofReal_mul (by linarith), ← hcj]
        congr 2
        field_simp
      rw [hmeas] at hconcj
      have hsum : ∑ i ∈ s, w i * Uint C ℓ (μ i) 0 = c * ∑ i ∈ s, w i / c * Uint C ℓ (μ i) 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        field_simp
      rw [hsum]
      have : c * ∑ i ∈ s, w i / c * Uint C ℓ (μ i) 0 ≤ c * Uint C ℓ ν 0 :=
        mul_le_mul_of_nonneg_left hIH hcpos.le
      rw [show (1 - w j) = c from hcj.symm] at hconcj
      linarith [hconcj, this]


theorem densMeasure_bar (F : Family 1) (hF : F.Admissible) :
    densMeasure F.bar = ∑ b, ENNReal.ofReal (F.θ b) • densMeasure (F.ρ b) := by
  ext s hs
  simp only [densMeasure, withDensity_apply _ hs, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]
  have hρm : ∀ b, AEMeasurable (fun x => ENNReal.ofReal (F.ρ b x)) ((haar 1).restrict s) := fun b =>
    (ENNReal.measurable_ofReal.comp_aemeasurable (rho_aemeasurable F hF b)).mono_measure
      Measure.restrict_le_self
  have : ∀ x, ENNReal.ofReal (F.bar x) = ∑ b, ENNReal.ofReal (F.θ b) * ENNReal.ofReal (F.ρ b x) := fun x => by
    unfold Family.bar
    rw [ENNReal.ofReal_sum_of_nonneg fun b _ => mul_nonneg (hF.1 b).le ((hF.2.2 b).1 x)]
    exact Finset.sum_congr rfl fun b _ => ENNReal.ofReal_mul (hF.1 b).le
  simp_rw [this]
  rw [lintegral_finsetSum' _ fun b _ => (hρm b).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [lintegral_const_mul'' _ (hρm b)]


theorem quot_of_real {ℓ D G : ℝ} (hℓ : 0 ≤ ℓ) (hG : 0 < G) (h : 2 * ℓ * G ≤ D) :
    ENNReal.ofReal ℓ ≤ ENNReal.ofReal D / (2 * ENNReal.ofReal G) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hG])) (Or.inl (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hℓ]
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

theorem real_of_quot {ℓ D G : ℝ} (hℓ : 0 ≤ ℓ) (hG : 0 < G) (hD : 0 ≤ D)
    (h : ENNReal.ofReal ℓ ≤ ENNReal.ofReal D / (2 * ENNReal.ofReal G)) : 2 * ℓ * G ≤ D := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hG])) (Or.inl (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))] at h
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hℓ, ENNReal.ofReal_le_ofReal_iff hD] at h
  nlinarith

theorem rMs_ge_of_deficit {W : Torus 1 → Torus 1 → ℝ} {KV KW : ℝ} (hyp : Hyp zeroV W KV KW) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ)
    (h : ∀ F : Family 1, F.Admissible → 2 * ℓ * (msGap zeroV W F).toReal ≤ (msDiss zeroV W F).toReal) :
    ENNReal.ofReal ℓ ≤ rMs zeroV W := by
  unfold rMs
  refine le_iInf₂ fun F hF => ?_
  obtain ⟨hFa, hFg⟩ := hF
  obtain ⟨hgtop, hgbot, hdtop⟩ := msGap_msDiss_lt_top (by norm_num) hyp hFa
  have hGeq : ((msGap zeroV W F).toReal : EReal) = msGap zeroV W F := EReal.coe_toReal hgtop.ne hgbot.ne'
  have hGpos : 0 < (msGap zeroV W F).toReal := by
    rw [← hGeq] at hFg
    exact EReal.coe_pos.mp hFg
  have hGen : (msGap zeroV W F).toENNReal = ENNReal.ofReal (msGap zeroV W F).toReal := by
    unfold EReal.toENNReal; rw [if_neg hgtop.ne]
  have hDeq : msDiss zeroV W F = ENNReal.ofReal (msDiss zeroV W F).toReal :=
    (ENNReal.ofReal_toReal hdtop.ne).symm
  rw [hGen, hDeq]
  exact quot_of_real hℓ hGpos (h F hFa)

theorem single_sum' {M : Type*} [AddCommMonoid M] (ρ : Torus 1 → ℝ) (f : Fin (Family.single ρ).q → M) :
    ∑ a, f a = f ⟨0, Nat.one_pos⟩ := Fin.sum_univ_one f

theorem single_adm (ρ : Torus 1 → ℝ) (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) : (Family.single ρ).Admissible := by
  refine ⟨fun _ => one_pos, ?_, fun a => ⟨h0, h1, hH⟩⟩
  rw [single_sum']; rfl

theorem sumH_single (ρ : Torus 1 → ℝ) :
    sumH (Family.single ρ) = (klDiv (densMeasure ρ) (haar 1)).toReal := by
  unfold sumH; rw [single_sum']; simp [Family.single]

theorem sumI_single (ρ : Torus 1 → ℝ) :
    sumI (Family.single ρ) = (fisherInfo (densMeasure ρ) (haar 1)).toReal := by
  unfold sumI; rw [single_sum']; simp [Family.single]


theorem deficit_decomp {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (ℓ : ℝ) (F : Family 1) (hF : F.Admissible) :
    (msDiss zeroV (attrW C) F).toReal - 2 * ℓ * (msGap zeroV (attrW C) F).toReal =
      (sumI F - 2 * ℓ * sumH F) + Uint C ℓ (densMeasure F.bar) 0 := by
  rw [msDiss_attr_real hC hmin F hF, msGap_attr_real hC hmin F hF,
    Uint_dens C ℓ F.bar (bar_nonneg' F hF) (bar_integral' F hF)]
  ring

theorem spec_nonneg {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ)
    (hr : rStar zeroV (attrW C) = ENNReal.ofReal ℓ) (ρ : Torus 1 → ℝ) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    2 * ℓ * (msGap zeroV (attrW C) (Family.single ρ)).toReal ≤
      (msDiss zeroV (attrW C) (Family.single ρ)).toReal := by
  obtain ⟨KV, KW, hyp⟩ := hyp_attr_aux hC
  have hFa := single_adm ρ h0 h1 hH
  obtain ⟨hgtop, hgbot, hdtop⟩ := msGap_msDiss_lt_top (by norm_num) hyp hFa
  have hg0 := (species_decomposition hyp (Family.single ρ) hFa).2.2
  have hDnn := ENNReal.toReal_nonneg (a := msDiss zeroV (attrW C) (Family.single ρ))
  rcases hg0.eq_or_lt with hz | hpos
  · have : (msGap zeroV (attrW C) (Family.single ρ)).toReal = 0 := by rw [← hz]; rfl
    rw [this]; simpa using hDnn
  · have hGeq : ((msGap zeroV (attrW C) (Family.single ρ)).toReal : EReal) =
        msGap zeroV (attrW C) (Family.single ρ) := EReal.coe_toReal hgtop.ne hgbot.ne'
    have hGpos : 0 < (msGap zeroV (attrW C) (Family.single ρ)).toReal := by
      rw [← hGeq] at hpos; exact EReal.coe_pos.mp hpos
    have hadm : SharpLSI.Admissible zeroV (attrW C) ρ := by
      refine ⟨h0, h1, hH, ?_⟩
      rw [← msGap_single]; exact hpos
    have hle : rStar zeroV (attrW C) ≤ dissipation zeroV (attrW C) ρ /
        (2 * (gap zeroV (attrW C) (densMeasure ρ)).toENNReal) :=
      iInf₂_le ρ hadm
    rw [hr, ← msGap_single, ← msDiss_single] at hle
    have hGen : (msGap zeroV (attrW C) (Family.single ρ)).toENNReal =
        ENNReal.ofReal (msGap zeroV (attrW C) (Family.single ρ)).toReal := by
      unfold EReal.toENNReal; rw [if_neg hgtop.ne]
    have hDeq : msDiss zeroV (attrW C) (Family.single ρ) =
        ENNReal.ofReal (msDiss zeroV (attrW C) (Family.single ρ)).toReal :=
      (ENNReal.ofReal_toReal hdtop.ne).symm
    rw [hGen, hDeq] at hle
    exact real_of_quot hℓ0 hGpos hDnn hle

theorem interaction_concavity_proved {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ)
    (hℓ : rStar zeroV (attrW C) = ENNReal.ofReal ℓ) (hconc : UintConcave C ℓ) :
    rMs zeroV (attrW C) = rStar zeroV (attrW C) := by
  obtain ⟨KV, KW, hyp⟩ := hyp_attr_aux hC
  apply le_antisymm (upper_comparison (le_refl 1) hyp).2
  rw [hℓ]
  refine rMs_ge_of_deficit hyp hℓ0 fun F hF => ?_
  -- species deficits
  have hspec : ∀ b, 0 ≤ (sumI (Family.single (F.ρ b)) - 2 * ℓ * sumH (Family.single (F.ρ b))) +
      Uint C ℓ (densMeasure (F.ρ b)) 0 := fun b => by
    have h1 := spec_nonneg hC hmin hℓ0 hℓ (F.ρ b) (hF.2.2 b).1 (hF.2.2 b).2.1 (hF.2.2 b).2.2
    have h2 := deficit_decomp hC hmin ℓ (Family.single (F.ρ b))
      (single_adm _ (hF.2.2 b).1 (hF.2.2 b).2.1 (hF.2.2 b).2.2)
    rw [Family.single_bar] at h2
    linarith
  have hμP : ∀ b, IsProbabilityMeasure (densMeasure (F.ρ b)) := fun b =>
    isProbabilityMeasure_densMeasure' (hF.2.2 b).1 (hF.2.2 b).2.1
  have hmix := uint_concave_sum hconc (fun b => densMeasure (F.ρ b)) hμP Finset.univ F.θ
    (fun b _ => hF.1 b) hF.2.1
  rw [← densMeasure_bar F hF] at hmix
  have hsplit : ∑ b, F.θ b * ((sumI (Family.single (F.ρ b)) - 2 * ℓ * sumH (Family.single (F.ρ b))) +
      Uint C ℓ (densMeasure (F.ρ b)) 0) = (sumI F - 2 * ℓ * sumH F) +
        ∑ b, F.θ b * Uint C ℓ (densMeasure (F.ρ b)) 0 := by
    simp_rw [sumI_single, sumH_single, mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    unfold sumI sumH
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  have hnn : 0 ≤ ∑ b, F.θ b * ((sumI (Family.single (F.ρ b)) - 2 * ℓ * sumH (Family.single (F.ρ b))) +
      Uint C ℓ (densMeasure (F.ρ b)) 0) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (hF.1 b).le (hspec b)
  have hdec := deficit_decomp hC hmin ℓ F hF
  linarith




theorem integral_dens_gen {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ (haar 1))
    (F : Torus 1 → ℝ) : ∫ x, F x ∂densMeasure ρ = ∫ x, ρ x * F x ∂haar 1 := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) (haar 1) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hρi.aestronglyMeasurable.aemeasurable
  rw [densMeasure, integral_withDensity_eq_integral_toReal_smul₀ hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul]

theorem densMeasure_add_smul {f g : Torus 1 → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfi : Integrable f (haar 1)) (hgi : Integrable g (haar 1)) {c : ℝ} (hc : 0 ≤ c) :
    densMeasure (fun x => f x + c * g x) = densMeasure f + ENNReal.ofReal c • densMeasure g := by
  ext s hs
  simp only [densMeasure, withDensity_apply _ hs, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have hfm : AEMeasurable (fun x => ENNReal.ofReal (f x)) ((haar 1).restrict s) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hfi.aestronglyMeasurable.aemeasurable).mono_measure
      Measure.restrict_le_self
  have hgm : AEMeasurable (fun x => ENNReal.ofReal (g x)) ((haar 1).restrict s) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hgi.aestronglyMeasurable.aemeasurable).mono_measure
      Measure.restrict_le_self
  have : ∀ x, ENNReal.ofReal (f x + c * g x) = ENNReal.ofReal (f x) + ENNReal.ofReal c * ENNReal.ofReal (g x) :=
    fun x => by rw [ENNReal.ofReal_add (hf0 x) (mul_nonneg hc (hg0 x)), ENNReal.ofReal_mul hc]
  simp_rw [this]
  rw [lintegral_add_left' hfm, lintegral_const_mul'' _ hgm]


/-! ### convolution of a continuous kernel with an integrable density -/

theorem exists_bound_of_continuous {g : Torus 1 → ℝ} (hg : Continuous g) : ∃ M, ∀ x, |g x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ.exists_bound_of_continuousOn hg.continuousOn)
  exact ⟨M, fun x => by simpa using hM x (Set.mem_univ x)⟩

theorem convT_integrand_integrable {g : Torus 1 → ℝ} (hg : Continuous g) {φ : Torus 1 → ℝ}
    (hφ : Integrable φ (haar 1)) (x : Torus 1) :
    Integrable (fun y => g (x - y) * φ y) (haar 1) := by
  obtain ⟨M, hM⟩ := exists_bound_of_continuous hg
  exact Integrable.bdd_mul (c := M) hφ (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _)

theorem convT_continuous {g : Torus 1 → ℝ} (hg : Continuous g) {φ : Torus 1 → ℝ}
    (hφ : Integrable φ (haar 1)) : Continuous (convT g φ) := by
  obtain ⟨M, hM⟩ := exists_bound_of_continuous hg
  unfold convT
  refine continuous_of_dominated (bound := fun y => M * |φ y|) (fun x => ?_) (fun x => ?_) ?_ ?_
  · exact (convT_integrand_integrable hg hφ x).aestronglyMeasurable
  · refine Eventually.of_forall fun y => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM _) (abs_nonneg _)
  · exact (hφ.abs.const_mul M)
  · exact Eventually.of_forall fun y => (hg.comp (continuous_id.sub continuous_const)).mul continuous_const

theorem convT_bound {g : Torus 1 → ℝ} (hg : Continuous g) {φ : Torus 1 → ℝ}
    (hφ : Integrable φ (haar 1)) : ∃ M, ∀ x, |convT g φ x| ≤ M := by
  exact exists_bound_of_continuous (convT_continuous hg hφ)

theorem convT_add_smul {g : Torus 1 → ℝ} (hg : Continuous g) {f h : Torus 1 → ℝ}
    (hf : Integrable f (haar 1)) (hh : Integrable h (haar 1)) (c : ℝ) (x : Torus 1) :
    convT g (fun y => f y + c * h y) x = convT g f x + c * convT g h x := by
  unfold convT
  have : ∀ y, g (x - y) * (f y + c * h y) = g (x - y) * f y + c * (g (x - y) * h y) := fun y => by ring
  simp_rw [this]
  rw [integral_add (convT_integrand_integrable hg hf x) ((convT_integrand_integrable hg hh x).const_mul c),
    integral_const_mul]


theorem integrable_mul_cont {f c : Torus 1 → ℝ} (hf : Integrable f (haar 1)) (hc : Continuous c) :
    Integrable (fun x => f x * c x) (haar 1) := by
  obtain ⟨M, hM⟩ := exists_bound_of_continuous hc
  exact (Integrable.bdd_mul (c := M) hf hc.aestronglyMeasurable
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _)).congr
    (Eventually.of_forall fun x => by simp [mul_comm])

/-- The bilinear form `⟨f, g * h⟩ = ∫ f (g * h)`. -/
noncomputable def BB (g f h : Torus 1 → ℝ) : ℝ := ∫ x, f x * convT g h x ∂haar 1

theorem BB_add_left {g : Torus 1 → ℝ} (hg : Continuous g) {f1 f2 h : Torus 1 → ℝ}
    (hf1 : Integrable f1 (haar 1)) (hf2 : Integrable f2 (haar 1)) (hh : Integrable h (haar 1)) (c : ℝ) :
    BB g (fun y => f1 y + c * f2 y) h = BB g f1 h + c * BB g f2 h := by
  unfold BB
  have hcv := convT_continuous hg hh
  have : ∀ x, (f1 x + c * f2 x) * convT g h x = f1 x * convT g h x + c * (f2 x * convT g h x) :=
    fun x => by ring
  simp_rw [this]
  rw [integral_add (integrable_mul_cont hf1 hcv) ((integrable_mul_cont hf2 hcv).const_mul c),
    integral_const_mul]

theorem BB_add_right {g : Torus 1 → ℝ} (hg : Continuous g) {f h1 h2 : Torus 1 → ℝ}
    (hf : Integrable f (haar 1)) (hh1 : Integrable h1 (haar 1)) (hh2 : Integrable h2 (haar 1)) (c : ℝ) :
    BB g f (fun y => h1 y + c * h2 y) = BB g f h1 + c * BB g f h2 := by
  unfold BB
  have : ∀ x, f x * convT g (fun y => h1 y + c * h2 y) x =
      f x * convT g h1 x + c * (f x * convT g h2 x) := fun x => by
    rw [convT_add_smul hg hh1 hh2]; ring
  simp_rw [this]
  rw [integral_add (integrable_mul_cont hf (convT_continuous hg hh1))
    ((integrable_mul_cont hf (convT_continuous hg hh2)).const_mul c), integral_const_mul]

theorem BB_expand {g : Torus 1 → ℝ} (hg : Continuous g) {φ δ : Torus 1 → ℝ}
    (hφ : Integrable φ (haar 1)) (hδ : Integrable δ (haar 1)) (s : ℝ) :
    BB g (fun y => φ y + s * δ y) (fun y => φ y + s * δ y) =
      BB g φ φ + s * (BB g φ δ + BB g δ φ) + s ^ 2 * BB g δ δ := by
  have hsd : Integrable (fun y => s * δ y) (haar 1) := hδ.const_mul s
  have hsum : Integrable (fun y => φ y + s * δ y) (haar 1) := hφ.add hsd
  rw [BB_add_left hg hφ hδ hsum s, BB_add_right hg hφ hφ hδ s, BB_add_right hg hδ hφ hδ s]
  ring


theorem LL_expand {k : Torus 1 → ℝ} (hk : Continuous k) {φ δ : Torus 1 → ℝ}
    (hφ : Integrable φ (haar 1)) (hδ : Integrable δ (haar 1)) (s : ℝ) :
    ∫ x, (φ x + s * δ x) * (convT k (fun y => φ y + s * δ y) x) ^ 2 ∂haar 1 =
      (∫ x, φ x * (convT k φ x) ^ 2 ∂haar 1) +
      s * (2 * ∫ x, φ x * (convT k φ x * convT k δ x) ∂haar 1 + ∫ x, δ x * (convT k φ x) ^ 2 ∂haar 1) +
      s ^ 2 * ((∫ x, φ x * (convT k δ x) ^ 2 ∂haar 1) + 2 * ∫ x, δ x * (convT k φ x * convT k δ x) ∂haar 1) +
      s ^ 3 * ∫ x, δ x * (convT k δ x) ^ 2 ∂haar 1 := by
  have hu := convT_continuous hk hφ
  have hv := convT_continuous hk hδ
  have e1 : ∀ x, convT k (fun y => φ y + s * δ y) x = convT k φ x + s * convT k δ x :=
    fun x => convT_add_smul hk hφ hδ s x
  simp_rw [e1]
  have i1 : Integrable (fun x => φ x * (convT k φ x) ^ 2) (haar 1) := integrable_mul_cont hφ (hu.pow 2)
  have i2 : Integrable (fun x => φ x * (convT k φ x * convT k δ x)) (haar 1) :=
    integrable_mul_cont hφ (hu.mul hv)
  have i3 : Integrable (fun x => δ x * (convT k φ x) ^ 2) (haar 1) := integrable_mul_cont hδ (hu.pow 2)
  have i4 : Integrable (fun x => φ x * (convT k δ x) ^ 2) (haar 1) := integrable_mul_cont hφ (hv.pow 2)
  have i5 : Integrable (fun x => δ x * (convT k φ x * convT k δ x)) (haar 1) :=
    integrable_mul_cont hδ (hu.mul hv)
  have i6 : Integrable (fun x => δ x * (convT k δ x) ^ 2) (haar 1) := integrable_mul_cont hδ (hv.pow 2)
  have pt : ∀ x, (φ x + s * δ x) * (convT k φ x + s * convT k δ x) ^ 2 =
      φ x * (convT k φ x) ^ 2 + s * (2 * (φ x * (convT k φ x * convT k δ x)) + δ x * (convT k φ x) ^ 2) +
      s ^ 2 * (φ x * (convT k δ x) ^ 2 + 2 * (δ x * (convT k φ x * convT k δ x))) +
      s ^ 3 * (δ x * (convT k δ x) ^ 2) := fun x => by ring
  simp_rw [pt]
  have j1 : Integrable (fun x => 2 * (φ x * (convT k φ x * convT k δ x)) + δ x * (convT k φ x) ^ 2) (haar 1) :=
    (i2.const_mul 2).add i3
  have j2 : Integrable (fun x => φ x * (convT k δ x) ^ 2 + 2 * (δ x * (convT k φ x * convT k δ x))) (haar 1) :=
    i4.add (i5.const_mul 2)
  have j3 : Integrable (fun x => φ x * (convT k φ x) ^ 2 +
      s * (2 * (φ x * (convT k φ x * convT k δ x)) + δ x * (convT k φ x) ^ 2)) (haar 1) :=
    i1.add (j1.const_mul s)
  have j4 : Integrable (fun x => φ x * (convT k φ x) ^ 2 +
      s * (2 * (φ x * (convT k φ x * convT k δ x)) + δ x * (convT k φ x) ^ 2) +
      s ^ 2 * (φ x * (convT k δ x) ^ 2 + 2 * (δ x * (convT k φ x * convT k δ x)))) (haar 1) :=
    j3.add (j2.const_mul (s ^ 2))
  rw [integral_add j4 (i6.const_mul (s ^ 3)), integral_add j3 (j2.const_mul (s ^ 2)),
    integral_add i1 (j1.const_mul s), integral_const_mul, integral_const_mul, integral_const_mul,
    integral_add (i2.const_mul 2) i3, integral_const_mul, integral_add i4 (i5.const_mul 2),
    integral_const_mul]


/-- `U(φ) = 2⟨φ, C''*φ⟩ + ∫φ (C'*φ)² + ℓ⟨φ, C*φ⟩` for a real function `φ`. -/
noncomputable def Ufun (C : Torus 1 → ℝ) (ℓ : ℝ) (φ : Torus 1 → ℝ) : ℝ :=
  2 * JJ C φ + LL C φ + ℓ * KK C φ

noncomputable def cA1 (C : Torus 1 → ℝ) (ℓ : ℝ) (φ δ : Torus 1 → ℝ) : ℝ :=
  2 * (BB (dT (dT C)) φ δ + BB (dT (dT C)) δ φ) + ℓ * (BB C φ δ + BB C δ φ) +
    (2 * ∫ x, φ x * (convT (dT C) φ x * convT (dT C) δ x) ∂haar 1 +
      ∫ x, δ x * (convT (dT C) φ x) ^ 2 ∂haar 1)

noncomputable def cA2 (C : Torus 1 → ℝ) (ℓ : ℝ) (φ δ : Torus 1 → ℝ) : ℝ :=
  2 * JJ C δ + ℓ * KK C δ +
    ((∫ x, φ x * (convT (dT C) δ x) ^ 2 ∂haar 1) +
      2 * ∫ x, δ x * (convT (dT C) φ x * convT (dT C) δ x) ∂haar 1)

noncomputable def cA3 (C : Torus 1 → ℝ) (δ : Torus 1 → ℝ) : ℝ :=
  ∫ x, δ x * (convT (dT C) δ x) ^ 2 ∂haar 1

theorem Ufun_poly {C : Torus 1 → ℝ} (hc0 : Continuous C) (hc1 : Continuous (dT C))
    (hc2 : Continuous (dT (dT C))) (ℓ : ℝ) {φ δ : Torus 1 → ℝ}
    (hφ : Integrable φ (haar 1)) (hδ : Integrable δ (haar 1)) (s : ℝ) :
    Ufun C ℓ (fun y => φ y + s * δ y) =
      Ufun C ℓ φ + s * cA1 C ℓ φ δ + s ^ 2 * cA2 C ℓ φ δ + s ^ 3 * cA3 C δ := by
  have hJ : JJ C (fun y => φ y + s * δ y) = JJ C φ + s * (BB (dT (dT C)) φ δ + BB (dT (dT C)) δ φ) +
      s ^ 2 * JJ C δ := BB_expand hc2 hφ hδ s
  have hK : KK C (fun y => φ y + s * δ y) = KK C φ + s * (BB C φ δ + BB C δ φ) + s ^ 2 * KK C δ :=
    BB_expand hc0 hφ hδ s
  have hL : LL C (fun y => φ y + s * δ y) = _ := LL_expand hc1 hφ hδ s
  unfold Ufun cA1 cA2 cA3
  rw [hJ, hK, hL]
  unfold LL
  ring


theorem cA2_base_change {C : Torus 1 → ℝ} (hc1 : Continuous (dT C)) (ℓ : ℝ) {φ δ : Torus 1 → ℝ}
    (hφ : Integrable φ (haar 1)) (hδ : Integrable δ (haar 1)) (t : ℝ) :
    cA2 C ℓ (fun y => φ y + t * δ y) δ = cA2 C ℓ φ δ + 3 * t * cA3 C δ := by
  have hu := convT_continuous hc1 hφ
  have hv := convT_continuous hc1 hδ
  have e1 : ∀ x, convT (dT C) (fun y => φ y + t * δ y) x = convT (dT C) φ x + t * convT (dT C) δ x :=
    fun x => convT_add_smul hc1 hφ hδ t x
  unfold cA2 cA3
  simp_rw [e1]
  have i1 : Integrable (fun x => φ x * (convT (dT C) δ x) ^ 2) (haar 1) := integrable_mul_cont hφ (hv.pow 2)
  have i2 : Integrable (fun x => δ x * (convT (dT C) δ x) ^ 2) (haar 1) := integrable_mul_cont hδ (hv.pow 2)
  have i3 : Integrable (fun x => δ x * (convT (dT C) φ x * convT (dT C) δ x)) (haar 1) :=
    integrable_mul_cont hδ (hu.mul hv)
  have p1 : ∀ x, (φ x + t * δ x) * (convT (dT C) δ x) ^ 2 =
      φ x * (convT (dT C) δ x) ^ 2 + t * (δ x * (convT (dT C) δ x) ^ 2) := fun x => by ring
  have p2 : ∀ x, δ x * ((convT (dT C) φ x + t * convT (dT C) δ x) * convT (dT C) δ x) =
      δ x * (convT (dT C) φ x * convT (dT C) δ x) + t * (δ x * (convT (dT C) δ x) ^ 2) := fun x => by ring
  simp_rw [p1, p2]
  rw [integral_add i1 (i2.const_mul t), integral_add i3 (i2.const_mul t), integral_const_mul]
  ring

theorem cA1_add_smul {C : Torus 1 → ℝ} (hc0 : Continuous C) (hc1 : Continuous (dT C))
    (hc2 : Continuous (dT (dT C))) (ℓ : ℝ) {φ δ1 δ2 : Torus 1 → ℝ}
    (hφ : Integrable φ (haar 1)) (hδ1 : Integrable δ1 (haar 1)) (hδ2 : Integrable δ2 (haar 1)) (c : ℝ) :
    cA1 C ℓ φ (fun y => δ1 y + c * δ2 y) = cA1 C ℓ φ δ1 + c * cA1 C ℓ φ δ2 := by
  have hu := convT_continuous hc1 hφ
  have hv1 := convT_continuous hc1 hδ1
  have hv2 := convT_continuous hc1 hδ2
  have e1 : ∀ x, convT (dT C) (fun y => δ1 y + c * δ2 y) x = convT (dT C) δ1 x + c * convT (dT C) δ2 x :=
    fun x => convT_add_smul hc1 hδ1 hδ2 c x
  unfold cA1
  rw [BB_add_right hc2 hφ hδ1 hδ2 c, BB_add_left hc2 hδ1 hδ2 hφ c, BB_add_right hc0 hφ hδ1 hδ2 c,
    BB_add_left hc0 hδ1 hδ2 hφ c]
  simp_rw [e1]
  have i1 : Integrable (fun x => φ x * (convT (dT C) φ x * convT (dT C) δ1 x)) (haar 1) :=
    integrable_mul_cont hφ (hu.mul hv1)
  have i2 : Integrable (fun x => φ x * (convT (dT C) φ x * convT (dT C) δ2 x)) (haar 1) :=
    integrable_mul_cont hφ (hu.mul hv2)
  have i3 : Integrable (fun x => δ1 x * (convT (dT C) φ x) ^ 2) (haar 1) := integrable_mul_cont hδ1 (hu.pow 2)
  have i4 : Integrable (fun x => δ2 x * (convT (dT C) φ x) ^ 2) (haar 1) := integrable_mul_cont hδ2 (hu.pow 2)
  have p1 : ∀ x, φ x * (convT (dT C) φ x * (convT (dT C) δ1 x + c * convT (dT C) δ2 x)) =
      φ x * (convT (dT C) φ x * convT (dT C) δ1 x) + c * (φ x * (convT (dT C) φ x * convT (dT C) δ2 x)) :=
    fun x => by ring
  have p2 : ∀ x, (δ1 x + c * δ2 x) * (convT (dT C) φ x) ^ 2 =
      δ1 x * (convT (dT C) φ x) ^ 2 + c * (δ2 x * (convT (dT C) φ x) ^ 2) := fun x => by ring
  simp_rw [p1, p2]
  rw [integral_add i1 (i2.const_mul c), integral_add i3 (i4.const_mul c), integral_const_mul,
    integral_const_mul]
  ring


theorem iDW_poly (A0 A1 A2 A3 : ℝ) :
    iteratedDerivWithin 2 (fun s : ℝ => A0 + s * A1 + s ^ 2 * A2 + s ^ 3 * A3) (Set.Ici 0) 0 = 2 * A2 := by
  have hs : UniqueDiffOn ℝ (Set.Ici (0:ℝ)) := uniqueDiffOn_Ici 0
  rw [iteratedDerivWithin_eq_iteratedDeriv hs (by fun_prop) (Set.mem_Ici.mpr le_rfl)]
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have h1 : deriv (fun s : ℝ => A0 + s * A1 + s ^ 2 * A2 + s ^ 3 * A3) =
      fun s => A1 + 2 * s * A2 + 3 * s ^ 2 * A3 := by
    funext s
    have h := (((hasDerivAt_const s A0).add ((hasDerivAt_id s).mul_const A1)).add
        ((hasDerivAt_pow 2 s).mul_const A2)).add ((hasDerivAt_pow 3 s).mul_const A3)
    exact (h.congr_deriv (by simp)).deriv
  rw [h1]
  have h := ((hasDerivAt_const (0:ℝ) A1).add (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const A2)).add
      (((hasDerivAt_pow 2 (0:ℝ)).const_mul 3).mul_const A3)
  have h' : HasDerivAt (fun s : ℝ => A1 + 2 * s * A2 + 3 * s ^ 2 * A3) (2 * A2) 0 :=
    h.congr_deriv (by simp)
  rw [h'.deriv]

theorem convS_densdiff {g : Torus 1 → ℝ} (hg : Continuous g) {f1 f2 : Torus 1 → ℝ}
    (h1 : ∀ x, 0 ≤ f1 x) (h2 : ∀ x, 0 ≤ f2 x) (i1 : Integrable f1 (haar 1)) (i2 : Integrable f2 (haar 1))
    (x : Torus 1) : convS g (densMeasure f1) (densMeasure f2) x = convT g (fun y => f1 y - f2 y) x := by
  unfold convS intS convT
  rw [integral_dens_gen h1 i1, integral_dens_gen h2 i2, ← integral_sub]
  · congr 1; funext y; ring
  · exact (convT_integrand_integrable hg i1 x).congr (Eventually.of_forall fun y => by simp [mul_comm])
  · exact (convT_integrand_integrable hg i2 x).congr (Eventually.of_forall fun y => by simp [mul_comm])

theorem Uint_densdiff {C : Torus 1 → ℝ} (hc0 : Continuous C) (hc1 : Continuous (dT C))
    (hc2 : Continuous (dT (dT C))) (ℓ : ℝ) {f1 f2 : Torus 1 → ℝ}
    (h1 : ∀ x, 0 ≤ f1 x) (h2 : ∀ x, 0 ≤ f2 x) (i1 : Integrable f1 (haar 1)) (i2 : Integrable f2 (haar 1)) :
    Uint C ℓ (densMeasure f1) (densMeasure f2) = Ufun C ℓ (fun y => f1 y - f2 y) := by
  have hd : Integrable (fun y => f1 y - f2 y) (haar 1) := i1.sub i2
  have hint : ∀ H : Torus 1 → ℝ, Continuous H →
      intS H (densMeasure f1) (densMeasure f2) = ∫ x, (f1 x - f2 x) * H x ∂haar 1 := fun H hH => by
    unfold intS
    rw [integral_dens_gen h1 i1, integral_dens_gen h2 i2, ← integral_sub (integrable_mul_cont i1 hH) (integrable_mul_cont i2 hH)]
    congr 1; funext x; ring
  unfold Uint Ufun
  simp_rw [convS_densdiff hc0 h1 h2 i1 i2, convS_densdiff hc1 h1 h2 i1 i2, convS_densdiff hc2 h1 h2 i1 i2]
  rw [hint (fun x => convT (dT (dT C)) (fun y => f1 y - f2 y) x) (convT_continuous hc2 hd),
    hint (fun x => convT (dT C) (fun y => f1 y - f2 y) x ^ 2) ((convT_continuous hc1 hd).pow 2),
    hint (fun x => convT C (fun y => f1 y - f2 y) x) (convT_continuous hc0 hd)]
  rfl


theorem densMeasure_smul {g : Torus 1 → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g (haar 1)) {c : ℝ}
    (hc : 0 ≤ c) : densMeasure (fun x => c * g x) = ENNReal.ofReal c • densMeasure g := by
  have h := densMeasure_add_smul (f := fun _ => (0:ℝ)) (g := g) (fun _ => le_rfl) hg0
    (integrable_zero _ _ _) hgi hc
  have h0 : densMeasure (fun _ : Torus 1 => (0:ℝ)) = 0 := by
    simp [densMeasure]
  simpa [h0] using h

theorem UintHess_dens {C : Torus 1 → ℝ} (hc0 : Continuous C) (hc1 : Continuous (dT C))
    (hc2 : Continuous (dT (dT C))) (ℓ : ℝ) {φ r1 r2 : Torus 1 → ℝ}
    (hφ0 : ∀ x, 0 ≤ φ x) (hr10 : ∀ x, 0 ≤ r1 x) (hr20 : ∀ x, 0 ≤ r2 x)
    (hφ : Integrable φ (haar 1)) (hr1 : Integrable r1 (haar 1)) (hr2 : Integrable r2 (haar 1)) :
    UintHess C ℓ (densMeasure φ) (densMeasure r1) (densMeasure r2) =
      2 * cA2 C ℓ φ (fun y => r1 y - r2 y) := by
  unfold UintHess
  have hδ : Integrable (fun y => r1 y - r2 y) (haar 1) := hr1.sub hr2
  have heq : Set.EqOn
      (fun s : ℝ => Uint C ℓ (densMeasure φ + ENNReal.ofReal s • densMeasure r1)
        (ENNReal.ofReal s • densMeasure r2))
      (fun s : ℝ => Ufun C ℓ φ + s * cA1 C ℓ φ (fun y => r1 y - r2 y) +
        s ^ 2 * cA2 C ℓ φ (fun y => r1 y - r2 y) + s ^ 3 * cA3 C (fun y => r1 y - r2 y)) (Set.Ici 0) := by
    intro s hs
    have hs0 : 0 ≤ s := hs
    simp only
    rw [← densMeasure_add_smul hφ0 hr10 hφ hr1 hs0, ← densMeasure_smul hr20 hr2 hs0]
    have hf1 : Integrable (fun x => φ x + s * r1 x) (haar 1) := hφ.add (hr1.const_mul s)
    have hf2 : Integrable (fun x => s * r2 x) (haar 1) := hr2.const_mul s
    rw [Uint_densdiff hc0 hc1 hc2 ℓ (fun x => add_nonneg (hφ0 x) (mul_nonneg hs0 (hr10 x)))
      (fun x => mul_nonneg hs0 (hr20 x)) hf1 hf2]
    have : (fun y => (φ y + s * r1 y) - s * r2 y) = fun y => φ y + s * (r1 y - r2 y) := by
      funext y; ring
    rw [this, Ufun_poly hc0 hc1 hc2 ℓ hφ hδ s]
  rw [iteratedDerivWithin_congr heq (Set.mem_Ici.mpr le_rfl)]
  exact iDW_poly _ _ _ _


theorem cA1_zero (C : Torus 1 → ℝ) (ℓ : ℝ) (φ : Torus 1 → ℝ) : cA1 C ℓ φ (fun _ => 0) = 0 := by
  have hc : ∀ (g : Torus 1 → ℝ), convT g (fun _ => (0:ℝ)) = fun _ => 0 := fun g => by
    funext x; unfold convT; simp
  unfold cA1 BB
  simp [hc]

theorem cA1_sum {C : Torus 1 → ℝ} (hc0 : Continuous C) (hc1 : Continuous (dT C))
    (hc2 : Continuous (dT (dT C))) (ℓ : ℝ) {φ : Torus 1 → ℝ} (hφ : Integrable φ (haar 1)) {ι : Type*}
    [DecidableEq ι] (δ : ι → Torus 1 → ℝ) (hδ : ∀ i, Integrable (δ i) (haar 1)) (w : ι → ℝ)
    (s : Finset ι) :
    cA1 C ℓ φ (fun y => ∑ i ∈ s, w i * δ i y) = ∑ i ∈ s, w i * cA1 C ℓ φ (δ i) := by
  induction s using Finset.induction_on with
  | empty => simp [cA1_zero]
  | insert j s hj ih =>
    have hsum : Integrable (fun y => ∑ i ∈ s, w i * δ i y) (haar 1) :=
      integrable_finsetSum _ fun i _ => (hδ i).const_mul (w i)
    have e : (fun y => ∑ i ∈ insert j s, w i * δ i y) = fun y => (∑ i ∈ s, w i * δ i y) + w j * δ j y := by
      funext y; rw [Finset.sum_insert hj]; ring
    rw [e, cA1_add_smul hc0 hc1 hc2 ℓ hφ hsum (hδ j) (w j), ih, Finset.sum_insert hj]
    ring


theorem QC_nonneg {C : Torus 1 → ℝ}
    (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re) (α β : Measure (Torus 1)) :
    0 ≤ QC C α β := by
  unfold QC
  refine tsum_nonneg fun n => ?_
  have hc := hCpos n.1 n.2
  have ha : 0 ≤ aCos := by unfold aCos; positivity
  exact mul_nonneg (mul_nonneg (mul_nonneg ha (sq_nonneg _)) hc) (Complex.normSq_nonneg _)

theorem interaction_compensation_proved {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM)
    (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re)
    {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ : rStar zeroV (attrW C) = ENNReal.ofReal ℓ) {γ : ℝ} (hγ : 0 ≤ γ)
    (hhess : ∀ (ρ α₁ β₁ : Measure (Torus 1)), IsProbabilityMeasure ρ → IsFiniteMeasure α₁ →
      IsFiniteMeasure β₁ → α₁ Set.univ = β₁ Set.univ →
        UintHess C ℓ ρ α₁ β₁ ≤ -γ * QC C α₁ β₁)
    (F : Family 1) (hF : F.Admissible) :
    deficit (attrW C) ℓ F ≥
        ∑ a, F.θ a * ((dissipation zeroV (attrW C) (F.ρ a)).toReal -
            2 * ℓ * (gap zeroV (attrW C) (densMeasure (F.ρ a))).toReal) +
          γ / 2 * ∑ a, F.θ a *
            QC C (densMeasure (F.ρ a)) (densMeasure F.bar) ∧
      ∑ a, F.θ a * ((dissipation zeroV (attrW C) (F.ρ a)).toReal -
            2 * ℓ * (gap zeroV (attrW C) (densMeasure (F.ρ a))).toReal) +
          γ / 2 * ∑ a, F.θ a *
            QC C (densMeasure (F.ρ a)) (densMeasure F.bar) ≥ 0 := by
  have hc0 : Continuous C := continuous_of_isSmoothT hC.smooth
  have hc1 : Continuous (dT C) := continuous_of_isSmoothT (dT_smooth hC.smooth)
  have hc2 : Continuous (dT (dT C)) := continuous_of_isSmoothT (dT_smooth (dT_smooth hC.smooth))
  have hρ0 := fun b => (hF.2.2 b).1
  have hρ1 := fun b => (hF.2.2 b).2.1
  have hρi : ∀ b, Integrable (F.ρ b) (haar 1) := fun b => integrable_of_integral_eq_one' (hρ1 b)
  have hb0 := bar_nonneg' F hF
  have hb1 := bar_integral' F hF
  have hbi : Integrable F.bar (haar 1) := integrable_of_integral_eq_one' hb1
  -- species deficits
  have hspec : ∀ b, (dissipation zeroV (attrW C) (F.ρ b)).toReal -
      2 * ℓ * (gap zeroV (attrW C) (densMeasure (F.ρ b))).toReal =
      (sumI (Family.single (F.ρ b)) - 2 * ℓ * sumH (Family.single (F.ρ b))) + Ufun C ℓ (F.ρ b) := fun b => by
    have h2 := deficit_decomp hC hmin ℓ (Family.single (F.ρ b))
      (single_adm _ (hρ0 b) (hρ1 b) (hF.2.2 b).2.2)
    rw [Family.single_bar, msDiss_single, msGap_single, Uint_dens C ℓ _ (hρ0 b) (hρ1 b)] at h2
    rw [h2]; unfold Ufun; ring
  have hspec_nn : ∀ b, 0 ≤ (dissipation zeroV (attrW C) (F.ρ b)).toReal -
      2 * ℓ * (gap zeroV (attrW C) (densMeasure (F.ρ b))).toReal := fun b => by
    have := spec_nonneg hC hmin hℓ0 hℓ (F.ρ b) (hρ0 b) (hρ1 b) (hF.2.2 b).2.2
    rw [msDiss_single, msGap_single] at this
    linarith
  have hQnn : ∀ b, 0 ≤ QC C (densMeasure (F.ρ b)) (densMeasure F.bar) := fun b => QC_nonneg hCpos _ _
  refine ⟨?_, ?_⟩
  swap
  · refine add_nonneg (Finset.sum_nonneg fun b _ => mul_nonneg (hF.1 b).le (hspec_nn b)) ?_
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun b _ => mul_nonneg (hF.1 b).le (hQnn b))
  · set δ : Fin F.q → Torus 1 → ℝ := fun b y => F.ρ b y - F.bar y with hδdef
    have hδi : ∀ b, Integrable (δ b) (haar 1) := fun b => (hρi b).sub hbi
    -- step 1: Ufun of a species is bounded by the second-order expansion
    have hK : ∀ b, Ufun C ℓ (F.ρ b) ≤ Ufun C ℓ F.bar + cA1 C ℓ F.bar (δ b) -
        γ / 2 * QC C (densMeasure (F.ρ b)) (densMeasure F.bar) := fun b => by
      have hpoly := Ufun_poly hc0 hc1 hc2 ℓ hbi (hδi b) 1
      have e1 : (fun y => F.bar y + 1 * δ b y) = F.ρ b := by funext y; simp [hδdef]
      rw [e1] at hpoly
      -- the base point
      set ρ' : Torus 1 → ℝ := fun y => F.bar y + (1 / 3) * δ b y with hρ'
      have hρ'0 : ∀ y, 0 ≤ ρ' y := fun y => by
        simp only [hρ', hδdef]; nlinarith [hb0 y, hρ0 b y]
      have hρ'i : Integrable ρ' (haar 1) := hbi.add ((hδi b).const_mul (1 / 3))
      have hρ'1 : ∫ y, ρ' y ∂haar 1 = 1 := by
        simp only [hρ']
        rw [integral_add hbi ((hδi b).const_mul (1 / 3)), integral_const_mul, hb1]
        simp only [hδdef]
        rw [integral_sub (hρi b) hbi, hρ1 b, hb1]; norm_num
      have hP := isProbabilityMeasure_densMeasure' hρ'0 hρ'1
      have hPb := isProbabilityMeasure_densMeasure' (hρ0 b) (hρ1 b)
      have hPbar := isProbabilityMeasure_densMeasure' hb0 hb1
      have hh := hhess (densMeasure ρ') (densMeasure (F.ρ b)) (densMeasure F.bar) hP inferInstance
        inferInstance (by rw [measure_univ, measure_univ])
      rw [UintHess_dens hc0 hc1 hc2 ℓ hρ'0 (hρ0 b) hb0 hρ'i (hρi b) hbi] at hh
      have hbc := cA2_base_change hc1 ℓ hbi (hδi b) (1 / 3)
      have hδfun : (fun y => F.ρ b y - F.bar y) = δ b := rfl
      rw [hδfun] at hh
      simp only [hρ'] at hh
      rw [hbc] at hh
      linarith
    -- step 2: sum with weights
    have hsum_cA1 : ∑ b, F.θ b * cA1 C ℓ F.bar (δ b) = 0 := by
      have h := cA1_sum hc0 hc1 hc2 ℓ hbi δ hδi F.θ Finset.univ
      have hz : (fun y => ∑ b, F.θ b * δ b y) = fun _ => 0 := by
        funext y
        simp only [hδdef, mul_sub, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul, hF.2.1, one_mul]
        unfold Family.bar
        simp
      rw [hz, cA1_zero] at h
      exact h.symm
    have hmix : ∑ b, F.θ b * Ufun C ℓ (F.ρ b) ≤ Ufun C ℓ F.bar -
        γ / 2 * ∑ b, F.θ b * QC C (densMeasure (F.ρ b)) (densMeasure F.bar) := by
      calc ∑ b, F.θ b * Ufun C ℓ (F.ρ b)
          ≤ ∑ b, F.θ b * (Ufun C ℓ F.bar + cA1 C ℓ F.bar (δ b) -
              γ / 2 * QC C (densMeasure (F.ρ b)) (densMeasure F.bar)) :=
            Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hK b) (hF.1 b).le
        _ = Ufun C ℓ F.bar - γ / 2 * ∑ b, F.θ b * QC C (densMeasure (F.ρ b)) (densMeasure F.bar) := by
            have : ∀ b, F.θ b * (Ufun C ℓ F.bar + cA1 C ℓ F.bar (δ b) -
                γ / 2 * QC C (densMeasure (F.ρ b)) (densMeasure F.bar)) =
                F.θ b * Ufun C ℓ F.bar + F.θ b * cA1 C ℓ F.bar (δ b) -
                γ / 2 * (F.θ b * QC C (densMeasure (F.ρ b)) (densMeasure F.bar)) := fun b => by ring
            simp_rw [this]
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hF.2.1, one_mul,
              hsum_cA1, ← Finset.mul_sum]
            ring
    -- step 3: assemble
    have hdec := deficit_decomp hC hmin ℓ F hF
    rw [Uint_dens C ℓ F.bar hb0 hb1] at hdec
    simp_rw [hspec]
    have hsplit : ∑ b, F.θ b * ((sumI (Family.single (F.ρ b)) - 2 * ℓ * sumH (Family.single (F.ρ b))) +
        Ufun C ℓ (F.ρ b)) = (sumI F - 2 * ℓ * sumH F) + ∑ b, F.θ b * Ufun C ℓ (F.ρ b) := by
      simp_rw [sumI_single, sumH_single, mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      unfold sumI sumH
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [hsplit]
    unfold deficit
    unfold Ufun at hmix ⊢
    linarith



/-! ### Statement-identity checks: each `*_proved` theorem has exactly the type of the E01/E01a original. -/

example : (type_of% @msGap_attr) = (type_of% @msGap_attr_proved) := rfl
example : (type_of% @msDiss_attr) = (type_of% @msDiss_attr_proved) := rfl
example : (type_of% @msDiss_ne_top_attr) = (type_of% @msDiss_ne_top_attr_proved) := rfl
example : (type_of% @hyp_attr) = (type_of% @hyp_attr_proved) := rfl
example : (type_of% @agreement_of_bounds) = (type_of% @agreement_of_bounds_proved) := rfl
example : (type_of% @fourier_entropy_bound) = (type_of% @fourier_entropy_bound_proved) := rfl
example : (type_of% @first_attractive_cosine) = (type_of% @first_attractive_cosine_proved) := rfl
example : (type_of% @interaction_concavity) = (type_of% @interaction_concavity_proved) := rfl
example : (type_of% @interaction_compensation) = (type_of% @interaction_compensation_proved) := rfl

end Ex
end SharpLSI.FL
