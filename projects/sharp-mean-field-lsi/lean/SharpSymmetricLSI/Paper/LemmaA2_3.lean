import SharpSymmetricLSI.Paper.LemmaA2_2

/-!
# R25 (A.9), part 3: `-log p` is semiconvex (`semiconvex_negLog`)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

/-- Where `(-log q ∘ liftT) s` is a.e. measurable, it agrees a.e. with `(-log ρ ∘ liftT) s`. -/
theorem ae_eq_negLog {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q ρ : Torus d → ℝ}
    (hq : μ = densMeasure q) (hρ : μ = densMeasure ρ) {c : ℝ} (hc : 0 < c) (hρc : ∀ y, c ≤ ρ y)
    (hq0 : ∀ y, 0 < q y) (hρm : Measurable ρ) {s : (Fin d → ℝ) → ℝ} (hs : Measurable s)
    (hF : AEStronglyMeasurable (fun x => -Real.log (q (liftT x)) * s x) volume) :
    (fun x => -Real.log (q (liftT x)) * s x) =ᵐ[volume] fun x => -Real.log (ρ (liftT x)) * s x := by
  have hρ0 : ∀ y, 0 < ρ y := fun y => hc.trans_le (hρc y)
  set F := fun x => -Real.log (q (liftT x)) * s x
  set G := fun x => -Real.log (ρ (liftT x)) * s x
  have hG : Measurable G := ((hρm.comp measurable_liftT).log.neg).mul hs
  set R := fun x => (F x - G x) / s x
  have hR : AEMeasurable R volume := (hF.aemeasurable.sub hG.aemeasurable).div hs.aemeasurable
  set R' := hR.mk R
  have hR'm : Measurable R' := hR.measurable_mk
  set N := toMeasurable volume {x | R x ≠ R' x}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [measure_toMeasurable]; exact ae_iff.mp hR.ae_eq_mk
  have key : ∀ x, x ∉ N → s x ≠ 0 → R' x = Real.log (ρ (liftT x)) - Real.log (q (liftT x)) := by
    intro x hx hsx
    have h1 : R x = R' x := by
      by_contra h; exact hx (subset_toMeasurable _ _ h)
    rw [← h1]
    simp only [R, F, G]
    field_simp
    ring
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  set A1 : ℕ → Set (Fin d → ℝ) := fun k => ({x | s x ≠ 0} ∩ {x | ε k ≤ R' x}) \ N
  set A2 : ℕ → Set (Fin d → ℝ) := fun k => ({x | s x ≠ 0} ∩ {x | R' x ≤ -ε k}) \ N
  have hA1 : ∀ k, volume (A1 k) = 0 := fun k => by
    refine volume_eq_zero_of_bad (Bad := fun y => q y ≤ Real.exp (-ε k) * ρ y)
      (fun E hE hB => haar_eq_zero_of_le hq hρ hc hρc hE (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by linarith [hε k])) hB)
      (((hs (measurableSet_singleton 0).compl).inter (measurableSet_le measurable_const hR'm)).diff
        hNm) fun x hx => ?_
    have h := key x hx.2 hx.1.1
    have h2 : ε k ≤ R' x := hx.1.2
    rw [h] at h2
    have h3 : Real.log (q (liftT x)) ≤ Real.log (ρ (liftT x)) + -ε k := by linarith
    calc q (liftT x) = Real.exp (Real.log (q (liftT x))) := (Real.exp_log (hq0 _)).symm
      _ ≤ Real.exp (Real.log (ρ (liftT x)) + -ε k) := Real.exp_le_exp.mpr h3
      _ = Real.exp (-ε k) * ρ (liftT x) := by rw [Real.exp_add, Real.exp_log (hρ0 _), mul_comm]
  have hA2 : ∀ k, volume (A2 k) = 0 := fun k => by
    refine volume_eq_zero_of_bad (Bad := fun y => Real.exp (ε k) * ρ y ≤ q y)
      (fun E hE hB => haar_eq_zero_of_ge hq hρ hc hρc hE
        (Real.one_lt_exp_iff.mpr (hε k)) hB)
      (((hs (measurableSet_singleton 0).compl).inter (measurableSet_le hR'm measurable_const)).diff
        hNm) fun x hx => ?_
    have h := key x hx.2 hx.1.1
    have h2 : R' x ≤ -ε k := hx.1.2
    rw [h] at h2
    have h3 : Real.log (ρ (liftT x)) + ε k ≤ Real.log (q (liftT x)) := by linarith
    calc Real.exp (ε k) * ρ (liftT x) = Real.exp (Real.log (ρ (liftT x)) + ε k) := by
          rw [Real.exp_add, Real.exp_log (hρ0 _), mul_comm]
      _ ≤ Real.exp (Real.log (q (liftT x))) := Real.exp_le_exp.mpr h3
      _ = q (liftT x) := Real.exp_log (hq0 _)
  have hN : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), x ∉ N := by
    rw [ae_iff]; simpa using hN0
  have h1 : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ∀ k, x ∉ A1 k :=
    ae_all_iff.mpr fun k => by rw [ae_iff]; simpa using hA1 k
  have h2 : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ∀ k, x ∉ A2 k :=
    ae_all_iff.mpr fun k => by rw [ae_iff]; simpa using hA2 k
  filter_upwards [hN, h1, h2] with x hxN hx1 hx2
  by_cases hsx : s x = 0
  · simp only [F, G, hsx, mul_zero]
  have hk := key x hxN hsx
  set r := Real.log (ρ (liftT x)) - Real.log (q (liftT x))
  have hr : r = 0 := by
    rcases lt_trichotomy r 0 with h | h | h
    · obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (neg_pos.mpr h)
      exact absurd ⟨⟨hsx, show R' x ≤ -ε k by rw [hk]; simp only [ε]; linarith⟩, hxN⟩ (hx2 k)
    · exact h
    · obtain ⟨k, hk'⟩ := exists_nat_one_div_lt h
      exact absurd ⟨⟨hsx, show ε k ≤ R' x by rw [hk]; simp only [ε]; linarith⟩, hxN⟩ (hx1 k)
  simp only [F, G]
  rw [show Real.log (q (liftT x)) = Real.log (ρ (liftT x)) by simp only [r] at hr; linarith]

section semiconvex

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem continuous_convMeas (hyp : Hyp V W KV KW) (ν : Measure (Torus d)) [IsFiniteMeasure ν] :
    Continuous (convMeas W ν) := by
  obtain ⟨B, hB⟩ := exists_bound_W hyp
  refine continuous_of_dominated (bound := fun _ => B) (fun x => ?_)
    (fun x => Eventually.of_forall fun y => ?_) (integrable_const B)
    (Eventually.of_forall fun y => ?_)
  · exact (hyp.continuous_W.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hB _ _
  · exact hyp.continuous_W.comp (continuous_id.prodMk continuous_const)

/-- **The semiconvexity clause of (A.9)**, `K_Q = K_V + K_W`. -/
theorem semiconvex_negLog (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) {p : Torus d → ℝ}
    (hp : (∀ x, 0 < p x) ∧ (μ : Measure (Torus d)) = densMeasure p) :
    ∃ KQ : ℝ, 0 ≤ KQ ∧
      ∀ φ : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → (∀ x, 0 ≤ φ x) →
        ∀ ξ : Fin d → ℝ, -KQ * (∑ k, ξ k ^ 2) * ∫ x, φ x ≤
          ∫ x, -Real.log (p (liftT x)) * secondDirDeriv φ ξ x := by
  refine ⟨KV + KW, add_nonneg hyp.KV_nonneg hyp.KW_nonneg, fun φ hφ hφc hφ0 ξ => ?_⟩
  set s := secondDirDeriv φ ξ
  have hsc : Continuous s := contDiff_secondDirDeriv_aux hφ ξ
  have hS : 0 ≤ ∑ k, ξ k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hI0 : 0 ≤ ∫ x, φ x := integral_nonneg hφ0
  by_cases hI : Integrable (fun x => -Real.log (p (liftT x)) * s x)
  swap
  · rw [integral_undef hI]
    have := mul_nonneg (mul_nonneg (add_nonneg hyp.KV_nonneg hyp.KW_nonneg) hS) hI0
    linarith
  obtain ⟨c, C, L, hc, hb⟩ := elDensity_bounds hyp
  obtain ⟨hbd, hL⟩ := hb (μ : Measure (Torus d)) inferInstance
  have hμρ := minimizer_eq_elDensity hyp hμ
  have hae := ae_eq_negLog hp.2 hμρ hc (fun y => (hbd y).1) hp.1 hL.continuous.measurable
    hsc.measurable hI.aestronglyMeasurable
  rw [integral_congr_ae hae]
  set Z := ∫ y, Real.exp (-V y - convMeas W (μ : Measure (Torus d)) y) ∂haar d
  have hZ : Z ≠ 0 := by
    intro h
    have h0 := (hbd 0).1
    have e : elDens V W (μ : Measure (Torus d)) 0 = Real.exp (-V 0 - convMeas W (μ : Measure (Torus d)) 0) / Z := rfl
    rw [e, h, div_zero] at h0
    linarith
  have hlog : ∀ y, -Real.log (elDens V W (μ : Measure (Torus d)) y) = V y + convMeas W (μ : Measure (Torus d)) y + Real.log Z := by
    intro y
    show -Real.log (Real.exp (-V y - convMeas W (μ : Measure (Torus d)) y) / Z) = _
    rw [Real.log_div (Real.exp_ne_zero _) hZ, Real.log_exp]
    ring
  simp_rw [hlog, add_mul]
  have hV := integrable_comp_liftT_mul hyp.continuous_V hφ hφc ξ
  have hW := integrable_comp_liftT_mul (continuous_convMeas hyp (μ : Measure (Torus d))) hφ hφc ξ
  have hZi : Integrable (fun x => Real.log Z * s x) := (hsc.integrable_of_hasCompactSupport
    (hasCompactSupport_secondDirDeriv hφc ξ)).const_mul _
  rw [integral_add (f := fun a => V (liftT a) * s a + convMeas W (μ : Measure (Torus d)) (liftT a) * s a)
    (hV.add hW) hZi, integral_add hV hW, integral_const_mul,
    integral_secondDirDeriv hφ hφc ξ, mul_zero, add_zero]
  have h1 := hyp.semiconvex_V φ hφ hφc hφ0 ξ
  have h2 := convMeas_semiconvex hyp (μ : Measure (Torus d)) hφ hφc hφ0 ξ
  linarith

end semiconvex

end SharpLSI
