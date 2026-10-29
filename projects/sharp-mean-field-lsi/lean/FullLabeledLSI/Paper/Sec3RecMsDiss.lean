import FullLabeledLSI.Paper.Sec3RecDiss
import FullLabeledLSI.Paper.Sec3RecFLimit

/-!
# Proposition 3.2: `D_θ` for smooth positive families, and the Fisher limit
-/

noncomputable section
open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {q : ℕ}

theorem mForce_eq_bForceL {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar d = 1)
    (x : Torus d) (k : Fin d) : mForce W (densMeasure ρ) x k = bForceL W ρ x k :=
  (bForce_eq hρ0 h1 x k).symm

theorem measurable_mForce (hyp : Hyp V W KV KW) {ρ : Torus d → ℝ} (hρc : Continuous ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar d = 1) (k : Fin d) :
    Measurable fun x => mForce W (densMeasure ρ) x k := by
  have : (fun x => mForce W (densMeasure ρ) x k) = fun x => bForceL W ρ x k :=
    funext fun x => mForce_eq_bForceL hρ0 h1 x k
  rw [this]
  exact (((measurable_bGrad hyp (W := W) k).mul (hρc.measurable.comp measurable_snd)
    ).stronglyMeasurable.integral_prod_right (ν := haar d)
      (f := fun x y => bGrad W x y k * ρ y)).measurable

theorem abs_mForce_le (hyp : Hyp V W KV KW) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∃ C, ∀ x k, |mForce W μ x k| ≤ C := by
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  refine ⟨Cb, fun x k => ?_⟩
  unfold mForce
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |bGrad W x y k| ∂μ ≤ ∫ _, Cb ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const Cb) (Filter.Eventually.of_forall fun y => hCb x y k)
    _ = Cb := by simp


theorem integral_expand_sq {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (θ : Fin q → ℝ)
    {a : Torus d → ℝ} {m : Fin q → Torus d → ℝ} (ha : Measurable a) (hm : ∀ t, Measurable (m t))
    {Ca : ℝ} (hCa : ∀ x, |a x| ≤ Ca) {Cm : ℝ} (hCm : ∀ t x, |m t x| ≤ Cm) :
    ∫ x, (a x + ∑ t, θ t * m t x) ^ 2 ∂μ =
      ∫ x, a x ^ 2 ∂μ + 2 * ∑ t, θ t * ∫ x, a x * m t x ∂μ +
        ∑ t, ∑ u, θ t * θ u * ∫ x, m t x * m u x ∂μ := by
  have ib : ∀ {f : Torus d → ℝ} {C : ℝ}, Measurable f → (∀ x, |f x| ≤ C) → Integrable f μ :=
    fun hf hC => Integrable.of_bound hf.aestronglyMeasurable _
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have i1 : Integrable (fun x => a x ^ 2) μ := ib (ha.pow_const 2) (C := Ca ^ 2) fun x => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hCa x) 2
  have i2 : ∀ t, Integrable (fun x => a x * m t x) μ := fun t =>
    ib (ha.mul (hm t)) (C := Ca * Cm) fun x => by
      rw [abs_mul]; exact mul_le_mul (hCa x) (hCm t x) (abs_nonneg _) ((abs_nonneg _).trans (hCa x))
  have i3 : ∀ t u, Integrable (fun x => m t x * m u x) μ := fun t u =>
    ib ((hm t).mul (hm u)) (C := Cm * Cm) fun x => by
      rw [abs_mul]; exact mul_le_mul (hCm t x) (hCm u x) (abs_nonneg _)
        ((abs_nonneg _).trans (hCm t x))
  have e : ∀ x, (a x + ∑ t, θ t * m t x) ^ 2 =
      a x ^ 2 + 2 * ∑ t, θ t * (a x * m t x) + ∑ t, ∑ u, θ t * θ u * (m t x * m u x) := fun x => by
    have hM : a x * ∑ t, θ t * m t x = ∑ t, θ t * (a x * m t x) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
    have hMM : (∑ t, θ t * m t x) ^ 2 = ∑ t, ∑ u, θ t * θ u * (m t x * m u x) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring
    rw [← hM, ← hMM]; ring
  simp_rw [e]
  have j2 : Integrable (fun x => 2 * ∑ t, θ t * (a x * m t x)) μ :=
    (integrable_finsetSum _ fun t _ => (i2 t).const_mul _).const_mul _
  have j3 : Integrable (fun x => ∑ t, ∑ u, θ t * θ u * (m t x * m u x)) μ :=
    integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun u _ => (i3 t u).const_mul _
  have h12 : Integrable (fun x => a x ^ 2 + 2 * ∑ t, θ t * (a x * m t x)) μ := i1.add j2
  rw [integral_add h12 j3, integral_add i1 j2, integral_const_mul,
    integral_finsetSum _ fun t _ => (i2 t).const_mul _,
    integral_finsetSum _ fun t _ => integrable_finsetSum _ fun u _ => (i3 t u).const_mul _]
  have h4 : ∀ t, ∫ x, ∑ u, θ t * θ u * (m t x * m u x) ∂μ =
      ∑ u, θ t * θ u * ∫ x, m t x * m u x ∂μ := fun t => by
    rw [integral_finsetSum _ fun u _ => (i3 t u).const_mul _]
    exact Finset.sum_congr rfl fun u _ => by rw [integral_const_mul]
  simp_rw [integral_const_mul, h4]


theorem bForceL_mix (hyp : Hyp V W KV KW) (θ : Fin q → ℝ) (ρ : Fin q → Torus d → ℝ)
    (hρc : ∀ s, Continuous (ρ s)) (hρ0 : ∀ s x, 0 ≤ ρ s x) (hρ1 : ∀ s, ∫ x, ρ s x ∂haar d = 1)
    (x : Torus d) (k : Fin d) :
    bForceL W (fun y => ∑ t, θ t * ρ t y) x k = ∑ t, θ t * mForce W (densMeasure (ρ t)) x k := by
  obtain ⟨Cb, hCb⟩ := bGrad_bdd hyp (W := W)
  have hρi : ∀ t, Integrable (ρ t) (haar d) := fun t => integrable_of_integral_eq_one' (hρ1 t)
  have hint : ∀ t, Integrable (fun y => bGrad W x y k * (θ t * ρ t y)) (haar d) := fun t => by
    have := ((hρi t).const_mul (θ t)).bdd_mul (c := Cb)
      (((measurable_bGrad hyp (W := W) k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hCb x y k)
    exact this
  unfold bForceL
  have e : ∀ y, bGrad W x y k * (∑ t, θ t * ρ t y) = ∑ t, bGrad W x y k * (θ t * ρ t y) := fun y => by
    rw [Finset.mul_sum]
  simp_rw [e]
  rw [integral_finsetSum _ fun t _ => hint t]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [mForce_eq_bForceL (hρ0 t) (hρ1 t), bForceL, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)


theorem msDiss_smooth (hyp : Hyp V W KV KW) (θ : Fin q → ℝ) (ρ : Fin q → Torus d → ℝ)
    (hθ0 : ∀ s, 0 ≤ θ s) (hθ1 : ∑ s, θ s = 1)
    (hρ : ∀ s, IsSmoothT (ρ s) ∧ (∀ x, 0 < ρ s x) ∧ ∫ x, ρ s x ∂haar d = 1) :
    msDiss V W (⟨q, θ, ρ⟩ : Family d) =
      ENNReal.ofReal (∑ k : Fin d, ∑ s, θ s * tauInf V W ρ θ k s) := by
  have hρ0 : ∀ s x, 0 ≤ ρ s x := fun s x => ((hρ s).2.1 x).le
  have hρ1 : ∀ s, ∫ x, ρ s x ∂haar d = 1 := fun s => (hρ s).2.2
  have hρc : ∀ s, Continuous (ρ s) := fun s => (hρ s).1.continuous
  have hρi : ∀ s, Integrable (ρ s) (haar d) := fun s => integrable_of_integral_eq_one' (hρ1 s)
  have hbc : Continuous (fun y => ∑ t, θ t * ρ t y) :=
    continuous_finset_sum _ fun t _ => continuous_const.mul (hρc t)
  have hb0 : ∀ x, 0 ≤ ∑ t, θ t * ρ t x := fun x =>
    Finset.sum_nonneg fun t _ => mul_nonneg (hθ0 t) (hρ0 t x)
  have hb1 : ∫ x, (∑ t, θ t * ρ t x) ∂haar d = 1 := by
    rw [integral_finsetSum _ fun t _ => (hρi t).const_mul _]
    simp_rw [integral_const_mul, hρ1, mul_one]; exact hθ1
  have hI : ∀ s, (∫ x, ∑ k, (aGrad V (ρ s) x k + bForceL W (fun y => ∑ t, θ t * ρ t y) x k) ^ 2
      ∂densMeasure (ρ s)) = ∑ k : Fin d, tauInf V W ρ θ k s := fun s => by
    haveI : IsProbabilityMeasure (densMeasure (ρ s)) :=
      isProbabilityMeasure_densMeasure' (hρ0 s) (hρ1 s)
    obtain ⟨Ca, hCa⟩ := aGrad_bdd hyp (hρ s).1 (hρ s).2.1
    have hCm : ∀ t, ∃ C, ∀ x k, |mForce W (densMeasure (ρ t)) x k| ≤ C := fun t => by
      haveI : IsProbabilityMeasure (densMeasure (ρ t)) :=
        isProbabilityMeasure_densMeasure' (hρ0 t) (hρ1 t)
      exact abs_mForce_le hyp _
    choose Cm hCm using hCm
    set CM : ℝ := ∑ t, |Cm t| with hCM
    have hCmM : ∀ t x k, |mForce W (densMeasure (ρ t)) x k| ≤ CM := fun t x k =>
      (hCm t x k).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun t => |Cm t|) (fun _ _ => abs_nonneg _) (Finset.mem_univ t)))
    have hint : ∀ k, Integrable (fun x => (aGrad V (ρ s) x k +
        ∑ t, θ t * mForce W (densMeasure (ρ t)) x k) ^ 2) (densMeasure (ρ s)) := fun k => by
      refine Integrable.of_bound (C := (Ca + ∑ t, |θ t| * CM) ^ 2)
        (((measurable_aGrad hyp (hρ s).1 (hρ s).2.1 k).add (Finset.measurable_sum _ fun t _ =>
          measurable_const.mul (measurable_mForce hyp (hρc t) (hρ0 t) (hρ1 t) k))).pow_const 2
          ).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_pow]
      refine pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans (add_le_add (hCa x k) ?_)) 2
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hCmM t x k) (abs_nonneg _)
    simp_rw [bForceL_mix hyp θ ρ hρc hρ0 hρ1]
    rw [integral_finsetSum _ fun k _ => hint k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_expand_sq θ (measurable_aGrad hyp (hρ s).1 (hρ s).2.1 k)
      (fun t => measurable_mForce hyp (hρc t) (hρ0 t) (hρ1 t) k) (fun x => hCa x k)
      (fun t x => hCmM t x k)]
    rfl
  have hnn : ∀ s, 0 ≤ ∑ k : Fin d, tauInf V W ρ θ k s := fun s => by
    rw [← hI s]
    exact integral_nonneg fun x => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hsd : ∀ s, speciesDiss V W (ρ s) (fun y => ∑ t, θ t * ρ t y) =
      ENNReal.ofReal (∑ k : Fin d, tauInf V W ρ θ k s) := fun s => by
    rw [speciesDiss_smooth hyp (hρ s).1 (hρ s).2.1 (hρ s).2.2 hbc hb0 hb1, hI s]
  unfold msDiss
  show ∑ a, ENNReal.ofReal (θ a) * speciesDiss V W (ρ a) (fun y => ∑ t, θ t * ρ t y) = _
  simp_rw [hsd]
  have e : ∑ k : Fin d, ∑ s, θ s * tauInf V W ρ θ k s = ∑ s, θ s * ∑ k : Fin d, tauInf V W ρ θ k s := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => by rw [Finset.mul_sum]
  rw [e, ENNReal.ofReal_sum_of_nonneg fun s _ => mul_nonneg (hθ0 s) (hnn s)]
  exact Finset.sum_congr rfl fun s _ => (ENNReal.ofReal_mul (hθ0 s)).symm

end SharpLSI.FL
