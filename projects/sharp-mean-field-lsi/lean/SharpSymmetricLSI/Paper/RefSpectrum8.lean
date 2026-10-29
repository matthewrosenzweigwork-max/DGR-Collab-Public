import SharpSymmetricLSI.Paper.RefSpectrum7
import SharpSymmetricLSI.Paper.SemiconvexLip2

/-!
# R23 (6.1), part 8: the eigen-equation in Haar form

With `σ = 1/ρ` Lipschitz and `b = -ρ ∇σ` (bounded), testing the weak eigen-equation
`∫ ∇e·∇φ dP = λ ∫ eφ dP` with `φ = σΘ` (`Θ` smooth periodic) gives
`∫ ∇e·∇Θ dm = ∫ (λe + b·∇e) Θ dm` (`haar_eq`), hence `ĝ(k) = 4π²|k|²ê(k)` for
`g = λe + b·∇e` (`cf_srcG`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal Real ContDiff NNReal
open UnitAddTorus

namespace SharpLSI

variable {d : ℕ}

/-- `1/ρ`. -/
noncomputable def recipD (ρ : Torus d → ℝ) (y : Torus d) : ℝ := 1 / ρ y

/-- The drift `b = -ρ ∇(1/ρ)`. -/
noncomputable def driftB (ρ : Torus d → ℝ) (y : Torus d) (k : Fin d) : ℝ :=
  -ρ y * lipGrad (recipD ρ) y k

/-- The eigenfunction source term `g = λe + b·∇e`. -/
noncomputable def srcG (ρ : Torus d → ℝ) (lam : ℝ) (e : Torus d → ℝ) (y : Torus d) : ℝ :=
  lam * e y + ∑ k, driftB ρ y k * weakGrad e y k

section haar

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρc : Continuous ρ) {Lσ : ℝ≥0}
  (hσ : LipschitzWith Lσ (recipD ρ ∘ liftT))
include hρ hρc hσ

theorem continuous_recipD : Continuous (recipD ρ) :=
  continuous_const.div hρc fun y => (hρ.pos.trans_le (hρ.lower y)).ne'

theorem isWeakGrad_recipD : IsWeakGrad (recipD ρ) (lipGrad (recipD ρ)) :=
  isWeakGrad_lipGrad (continuous_recipD hρ hρc hσ) hσ

theorem abs_driftB_le (y : Torus d) (k : Fin d) : |driftB ρ y k| ≤ C * Lσ := by
  rw [driftB, abs_mul, abs_neg, abs_of_nonneg (hρ.nonneg y)]
  exact mul_le_mul (hρ.upper y) (abs_lipGrad_le hσ y k) (abs_nonneg _) hρ.C_pos.le

theorem measurable_driftB (k : Fin d) : Measurable fun y => driftB ρ y k :=
  (hρ.meas.neg).mul (measurable_lipGrad (continuous_recipD hρ hρc hσ) k)

theorem abs_recipD_le (y : Torus d) : |recipD ρ y| ≤ 1 / c := by
  rw [recipD, abs_of_pos (by have := hρ.pos.trans_le (hρ.lower y); positivity)]
  exact one_div_le_one_div_of_le hρ.pos (hρ.lower y)

/-- **The eigen-equation in Haar form.** -/
theorem haar_eq {e : Torus d → ℝ} {lam : ℝ} (he : MemH1 (densMeasure ρ) e)
    (heig : ∀ φ, MemH1 (densMeasure ρ) φ →
      dirB (densMeasure ρ) e φ = lam * ∫ x, e x * φ x ∂densMeasure ρ)
    {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) :
    ∫ y, ∑ k, weakGrad e y k * Dk Θ k (secT y) = ∫ y, srcG ρ lam e y * Θ (secT y) := by
  set P := densMeasure ρ
  haveI := hρ.isProb
  obtain ⟨BΘ, hBΘ⟩ := periodic_bounded hΘ.continuous hp
  have hBD : ∀ k, ∃ B, ∀ x, ‖Dk Θ k x‖ ≤ B := fun k =>
    periodic_bounded (contDiff_Dk hΘ k).continuous (hp.Dk k)
  choose BD hBD using hBD
  have hΘm : Measurable fun y => Θ (secT y) := hΘ.continuous.measurable.comp measurable_secT
  have hDm : ∀ k, Measurable fun y => Dk Θ k (secT y) := fun k =>
    (contDiff_Dk hΘ k).continuous.measurable.comp measurable_secT
  set σ := recipD ρ
  have hσc := continuous_recipD hρ hρc hσ
  have hσw := isWeakGrad_recipD hρ hρc hσ
  set φ := fun y => σ y * Θ (secT y)
  set Gφ : Torus d → Fin d → ℝ := fun y k => lipGrad σ y k * Θ (secT y) + σ y * Dk Θ k (secT y)
  have hφw : IsWeakGrad φ Gφ := hσw.mul_smooth hΘ hp
  have hGφm : ∀ k, Measurable fun y => Gφ y k := fun k =>
    ((measurable_lipGrad hσc k).mul hΘm).add (hσc.measurable.mul (hDm k))
  have hGφb : ∀ k y, |Gφ y k| ≤ Lσ * BΘ + 1 / c * BD k := by
    intro k y
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul]
    · exact mul_le_mul (abs_lipGrad_le hσ y k) (hBΘ _) (abs_nonneg _) Lσ.2
    · exact mul_le_mul (abs_recipD_le hρ hρc hσ y) (hBD k _) (abs_nonneg _)
        (by have := hρ.pos; positivity)
  have hae : weakGrad φ =ᵐ[volume] Gφ := weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hφw⟩) hφw
  have hGφP : ∀ k, MemLp (fun y => Gφ y k) 2 P := fun k =>
    MemLp.of_bound (hGφm k).aestronglyMeasurable _ (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hGφb k y)
  have hφH : MemH1 P φ := by
    refine ⟨⟨_, hφw⟩, ?_, memLp_sqrt_sqNorm_of hρ fun k => (hGφP k).ae_eq ?_⟩
    · refine MemLp.of_bound (hσc.measurable.mul hΘm).aestronglyMeasurable (1 / c * BΘ)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_recipD_le hρ hρc hσ y) (hBΘ _) (abs_nonneg _)
        (by have := hρ.pos; positivity)
    · filter_upwards [hρ.ac.ae_le hae] with y hy
      rw [hy]
  have h := heig φ hφH
  -- rewrite both sides as Haar integrals
  have hρσ : ∀ y, ρ y * σ y = 1 := fun y => by
    simp only [σ, recipD]; field_simp [(hρ.pos.trans_le (hρ.lower y)).ne']
  have hge : ∀ k, MemLp (fun y => weakGrad e y k) 2 volume := fun k =>
    memLp_grad_vol hρ.haar_le_smul hρ.le_smul he k
  have hev : MemLp e 2 volume := memLp_vol hρ.haar_le_smul he
  have hL : dirB P e φ = (∫ y, ∑ k, weakGrad e y k * Dk Θ k (secT y)) +
      ∫ y, (∑ k, -driftB ρ y k * weakGrad e y k) * Θ (secT y) := by
    unfold dirB
    have haeP : weakGrad φ =ᵐ[densMeasure ρ] Gφ := hρ.ac.ae_le hae
    rw [integral_congr_ae (g := fun y => ∑ k, weakGrad e y k * Gφ y k)
      (haeP.mono fun y hy => by simp only [hy]), hρ.integral_eq]
    have e1 : ∀ y, ρ y * ∑ k, weakGrad e y k * Gφ y k =
        ∑ k, weakGrad e y k * Dk Θ k (secT y) +
          (∑ k, -driftB ρ y k * weakGrad e y k) * Θ (secT y) := by
      intro y
      show ρ y * ∑ k, weakGrad e y k * (lipGrad σ y k * Θ (secT y) + σ y * Dk Θ k (secT y)) = _
      simp only [driftB, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have := hρσ y
      linear_combination (weakGrad e y k * Dk Θ k (secT y)) * this
    simp_rw [e1]
    refine integral_add ?_ ?_
    · refine integrable_finset_sum _ fun k _ => ?_
      exact ((hge k).integrable one_le_two).mul_bdd (c := BD k) (hDm k).aestronglyMeasurable
        (Eventually.of_forall fun y => hBD k _)
    · refine (integrable_finset_sum _ fun k _ => ?_).mul_bdd (c := BΘ) hΘm.aestronglyMeasurable
        (Eventually.of_forall fun y => hBΘ _)
      exact (((hge k).integrable one_le_two).mul_bdd (c := C * Lσ)
        ((measurable_driftB hρ hρc hσ k).neg).aestronglyMeasurable
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, Pi.neg_apply, abs_neg]; exact abs_driftB_le hρ hρc hσ y k)).congr
        (Eventually.of_forall fun y => by simp only [Pi.mul_apply, Pi.neg_apply]; ring)
  have hR : lam * ∫ x, e x * φ x ∂P = ∫ y, lam * e y * Θ (secT y) := by
    rw [hρ.integral_eq, ← integral_const_mul]
    congr 1; funext y
    simp only [φ]
    have := hρσ y
    linear_combination (lam * e y * Θ (secT y)) * this
  rw [hL, hR] at h
  have hI2 : Integrable (fun y => (∑ k, -driftB ρ y k * weakGrad e y k) * Θ (secT y)) volume := by
    refine (integrable_finset_sum _ fun k _ => ?_).mul_bdd (c := BΘ) hΘm.aestronglyMeasurable
      (Eventually.of_forall fun y => hBΘ _)
    exact (((hge k).integrable one_le_two).mul_bdd (c := C * Lσ)
      ((measurable_driftB hρ hρc hσ k).neg).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, Pi.neg_apply, abs_neg]; exact abs_driftB_le hρ hρc hσ y k)).congr
      (Eventually.of_forall fun y => by simp only [Pi.mul_apply, Pi.neg_apply]; ring)
  have hI3 : Integrable (fun y => lam * e y * Θ (secT y)) volume :=
    ((hev.integrable one_le_two).const_mul lam).mul_bdd (c := BΘ) hΘm.aestronglyMeasurable
      (Eventually.of_forall fun y => hBΘ _)
  have hsrc : ∫ y, srcG ρ lam e y * Θ (secT y) =
      (∫ y, lam * e y * Θ (secT y)) - ∫ y, (∑ k, -driftB ρ y k * weakGrad e y k) * Θ (secT y) := by
    refine (integral_congr_ae (Eventually.of_forall fun y => ?_)).trans (integral_sub hI3 hI2)
    simp only [srcG, Finset.sum_neg_distrib, neg_mul]
    ring
  rw [hsrc]
  linarith

theorem memLp_srcG {e : Torus d → ℝ} (he : MemH1 (densMeasure ρ) e) (lam : ℝ) :
    MemLp (srcG ρ lam e) 2 volume := by
  haveI := hρ.isProb
  have hge : ∀ k, MemLp (fun y => weakGrad e y k) 2 volume := fun k =>
    memLp_grad_vol hρ.haar_le_smul hρ.le_smul he k
  have hev : MemLp e 2 volume := memLp_vol hρ.haar_le_smul he
  refine (hev.const_mul lam).add (memLp_finset_sum _ fun k _ => ?_)
  refine ((hge k).const_mul (C * Lσ)).of_le
    ((measurable_driftB hρ hρc hσ k).aestronglyMeasurable.mul (hge k).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  have hCL : |C * (Lσ : ℝ)| = C * Lσ := abs_of_nonneg (mul_nonneg hρ.C_pos.le (NNReal.coe_nonneg Lσ))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, hCL]
  exact mul_le_mul_of_nonneg_right (abs_driftB_le hρ hρc hσ y k) (abs_nonneg _)

/-- **Fourier form of the eigen-equation.** -/
theorem cf_srcG {e : Torus d → ℝ} {lam : ℝ} (he : MemH1 (densMeasure ρ) e)
    (heig : ∀ φ, MemH1 (densMeasure ρ) φ →
      dirB (densMeasure ρ) e φ = lam * ∫ x, e x * φ x ∂densMeasure ρ) (k : Fin d → ℤ) :
    mFourierCoeff (fun y => (srcG ρ lam e y : ℂ)) k =
      4 * π ^ 2 * (∑ j, ((k j : ℂ)) ^ 2) * mFourierCoeff (fun y => (e y : ℂ)) k := by
  haveI := hρ.isProb
  exact cf_of_weak_eq (isWeakGrad_weakGrad he.1)
    ((memLp_vol hρ.haar_le_smul he).integrable one_le_two)
    (fun j => (memLp_grad_vol hρ.haar_le_smul hρ.le_smul he j).integrable one_le_two)
    ((memLp_srcG hρ hρc hσ he lam).integrable one_le_two)
    (fun Θ hΘ hp => haar_eq hρ hρc hσ he heig hΘ hp) k

end haar

end SharpLSI
