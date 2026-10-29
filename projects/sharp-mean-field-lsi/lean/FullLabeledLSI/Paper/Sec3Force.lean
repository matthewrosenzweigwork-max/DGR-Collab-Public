import SharpSymmetricLSI.Paper.AppAStab1
import SharpSymmetricLSI.Statements.R06_Upper_Bound

/-!
# Vector bound for the interaction force of a signed density

`‖∫ ∇₁W(x,y) h(y) dy‖² ≤ B² (∫|h|)²` for a.e. `x`, where `|∇₁W| ≤ B` a.e. on pairs.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem bGrad_pair_bound (hyp : Hyp V W KV KW) {B : ℝ}
    (hB : ∀ᵐ X ∂(volume : Measure (Config 2 d)),
      sqNorm (fun k => grad1W W (X 0) (X 1) k) ≤ B ^ 2) :
    ∀ᵐ p ∂(haar d).prod (haar d), sqNorm (fun k => bGrad W p.1 p.2 k) ≤ B ^ 2 := by
  have hmp := (measurePreserving_piFinTwo (fun _ : Fin 2 => (volume : Measure (Torus d))))
  have hW' : ∀ᵐ p ∂(haar d).prod (haar d), sqNorm (fun k => grad1W W p.1 p.2 k) ≤ B ^ 2 := by
    have := hmp.symm.quasiMeasurePreserving.ae hB
    refine this.mono fun p hp => ?_
    simpa [MeasurableEquiv.piFinTwo] using hp
  have hlip := isWeakGrad_lipGrad (continuous_W2 hyp) (lipschitz_W2 hyp)
  have hae := appA_weakGrad_ae_eq hlip
  have hae' : ∀ᵐ p ∂(haar d).prod (haar d),
      weakGrad (W2 W) (pairFlat p) = lipGrad (W2 W) (pairFlat p) :=
    measurePreserving_pairFlat.quasiMeasurePreserving.ae hae
  filter_upwards [hW', hae'] with p hp1 hp2
  have e : ∀ k, bGrad W p.1 p.2 k = grad1W W p.1 p.2 k := fun k => by
    rw [grad1W_eq_weakGrad_W2, show ((p.1, p.2) : Torus d × Torus d) = p from rfl, hp2]
    rfl
  simpa only [e] using hp1


theorem bForceL_sqNorm_le (hyp : Hyp V W KV KW) {B : ℝ}
    (hB : ∀ᵐ X ∂(volume : Measure (Config 2 d)),
      sqNorm (fun k => grad1W W (X 0) (X 1) k) ≤ B ^ 2)
    {h : Torus d → ℝ} (hh : Integrable h (haar d)) :
    ∀ᵐ x ∂haar d, sqNorm (fun k => bForceL W h x k) ≤ B ^ 2 * (∫ y, |h y| ∂haar d) ^ 2 := by
  have hpair := bGrad_pair_bound hyp hB
  have hcomp : ∀ᵐ p ∂(haar d).prod (haar d), ∀ k, |bGrad W p.1 p.2 k| ≤ |B| := by
    filter_upwards [hpair] with p hp k
    refine (appA_abs_le_sqrt_sqNorm _ k).trans ?_
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hp
  filter_upwards [Measure.ae_ae_of_ae_prod hpair, integrable_bGrad_mul hcomp hyp hh]
    with x hx hxi
  set F : Fin d → ℝ := fun k => bForceL W h x k with hF
  set M : ℝ := ∫ y, |h y| ∂haar d with hM
  have hM0 : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
  have hF0 : 0 ≤ sqNorm F := sqNorm_nonneg _
  set s : ℝ := Real.sqrt (sqNorm F) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = sqNorm F := Real.sq_sqrt hF0
  -- `∑ F_k² = ∫ (∑ F_k b_k(y)) h(y) dy`
  have hint : ∀ k, Integrable (fun y => F k * (bGrad W x y k * h y)) (haar d) := fun k =>
    (hxi k).const_mul _
  have h1 : sqNorm F = ∫ y, (∑ k, F k * bGrad W x y k) * h y ∂haar d := by
    unfold sqNorm
    have e1 : ∀ k, F k ^ 2 = ∫ y, F k * (bGrad W x y k * h y) ∂haar d := fun k => by
      rw [integral_const_mul, sq]
      rfl
    simp_rw [e1]
    rw [← integral_finsetSum _ fun k _ => hint k]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hbd : ∀ᵐ y ∂haar d, (∑ k, F k * bGrad W x y k) * h y ≤ s * |B| * |h y| := by
    filter_upwards [hx] with y hy
    have hcs : (∑ k, F k * bGrad W x y k) ^ 2 ≤ sqNorm F * sqNorm (fun k => bGrad W x y k) := by
      unfold sqNorm
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : |∑ k, F k * bGrad W x y k| ≤ s * |B| := by
      refine (Real.abs_le_sqrt hcs).trans ?_
      rw [Real.sqrt_mul hF0, ← Real.sqrt_sq_eq_abs B, hs]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hy) (Real.sqrt_nonneg _)
    calc (∑ k, F k * bGrad W x y k) * h y ≤ |(∑ k, F k * bGrad W x y k) * h y| := le_abs_self _
      _ = |∑ k, F k * bGrad W x y k| * |h y| := abs_mul _ _
      _ ≤ s * |B| * |h y| := mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
  have hli : Integrable (fun y => (∑ k, F k * bGrad W x y k) * h y) (haar d) := by
    have := integrable_finsetSum (Finset.univ : Finset (Fin d)) fun k _ => hint k
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : sqNorm F ≤ s * |B| * M := by
    rw [h1]
    calc ∫ y, (∑ k, F k * bGrad W x y k) * h y ∂haar d ≤ ∫ y, s * |B| * |h y| ∂haar d :=
          integral_mono_ae hli (hh.abs.const_mul _) hbd
      _ = s * |B| * M := by rw [integral_const_mul]
  have hBM : 0 ≤ |B| * M := mul_nonneg (abs_nonneg _) hM0
  have h4 : s ≤ |B| * M := by
    by_contra hlt
    push_neg at hlt
    have : s * s ≤ s * (|B| * M) := by nlinarith [hs2, h2]
    have hspos : 0 < s := lt_of_le_of_lt hBM hlt
    nlinarith
  calc sqNorm F = s ^ 2 := hs2.symm
    _ ≤ (|B| * M) ^ 2 := pow_le_pow_left₀ hs0 h4 2
    _ = B ^ 2 * M ^ 2 := by rw [mul_pow, sq_abs]

end SharpLSI.FL
