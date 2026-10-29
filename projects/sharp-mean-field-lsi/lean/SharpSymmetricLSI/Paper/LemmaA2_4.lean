import SharpSymmetricLSI.Paper.LemmaA2_3
import SharpSymmetricLSI.Paper.RefSpectrum17
import SharpSymmetricLSI.Paper.GroundState

/-!
# R25 (A.9), part 4: smooth densities, integration by parts, decay of coefficients

For a good density `ρ` with smooth lift and a smooth periodic `Θ`,
`∫ ∇e·∇Θ dμ = -∫ e div(ρ∇Θ) dm` for `e ∈ H¹(μ)` (`dirB_smooth_eq`). Hence for an eigenpair
`λ ⟨e, Θ⟩_μ = ⟨e, AΘ⟩_μ` with `AΘ = -div(ρ∇Θ)/ρ` smooth periodic (`eig_genA`), and iterating,
`|λ|^m |⟨e, Θ⟩_μ| ≤ (1 + sup|A^mΘ|²)/2` (`abs_coeff_le`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real ContDiff NNReal

namespace SharpLSI

variable {d : ℕ}

theorem isPer_comp_liftT (ρ : Torus d → ℝ) : IsPer (ρ ∘ liftT) := fun m x => by
  simp only [Function.comp, liftT_add_intVec]

theorem comp_secT_comp_liftT {Θ : (Fin d → ℝ) → ℝ} (hp : IsPer Θ) : (Θ ∘ secT) ∘ liftT = Θ :=
  funext fun x => hp.secT_liftT x

/-- `div(ρ∇Θ)` on lifts. -/
noncomputable def divRho (ρ : Torus d → ℝ) (Θ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ k, Dk (fun z => ρ (liftT z) * Dk Θ k z) k x

/-- The generator on lifts, `AΘ = -div(ρ∇Θ)/ρ`. -/
noncomputable def genA (ρ : Torus d → ℝ) (Θ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  -divRho ρ Θ x / ρ (liftT x)

section smooth

variable {ρ : Torus d → ℝ} (hρs : ContDiff ℝ ∞ (ρ ∘ liftT))

include hρs in
theorem contDiff_divRho {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) :
    ContDiff ℝ ∞ (divRho ρ Θ) :=
  ContDiff.sum fun k _ => contDiff_Dk (hρs.mul (contDiff_Dk hΘ k)) k

theorem isPer_divRho {Θ : (Fin d → ℝ) → ℝ} (hp : IsPer Θ) : IsPer (divRho ρ Θ) := by
  intro m x
  simp only [divRho]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : IsPer (fun z => ρ (liftT z) * Dk Θ k z) := fun m' z => by
    simp only [liftT_add_intVec, hp.Dk k m' z]
  exact h.Dk k m x

include hρs in
theorem contDiff_genA {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hpos : ∀ y, 0 < ρ y) :
    ContDiff ℝ ∞ (genA ρ Θ) :=
  (contDiff_divRho hρs hΘ).neg.div hρs fun x => (hpos _).ne'

theorem isPer_genA {Θ : (Fin d → ℝ) → ℝ} (hp : IsPer Θ) : IsPer (genA ρ Θ) := by
  intro m x
  simp only [genA, liftT_add_intVec, isPer_divRho hp m x]

include hρs in
theorem contDiff_iterate_genA {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hpos : ∀ y, 0 < ρ y)
    (m : ℕ) : ContDiff ℝ ∞ ((genA ρ)^[m] Θ) := by
  induction m generalizing Θ with
  | zero => exact hΘ
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih (contDiff_genA hρs hΘ hpos)

theorem isPer_iterate_genA {Θ : (Fin d → ℝ) → ℝ} (hp : IsPer Θ) (m : ℕ) :
    IsPer ((genA ρ)^[m] Θ) := by
  induction m generalizing Θ with
  | zero => exact hp
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih (isPer_genA hp)

end smooth

section good

variable {ρ : Torus d → ℝ} {c C : ℝ} (hρ : GoodDens ρ c C) (hρs : ContDiff ℝ ∞ (ρ ∘ liftT))
include hρ hρs

theorem memH1_smooth {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) :
    MemH1 (densMeasure ρ) (Θ ∘ secT) := by
  refine memH1_of_vol hρ (memH1_of_contDiff ?_)
  rw [comp_secT_comp_liftT hp]; exact hΘ

theorem weakGrad_smooth {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) :
    weakGrad (Θ ∘ secT) =ᵐ[volume] fun y k => Dk Θ k (secT y) := by
  have h1 : ContDiff ℝ 1 ((Θ ∘ secT) ∘ liftT) := by
    rw [comp_secT_comp_liftT hp]; exact hΘ.of_le (by norm_cast)
  have hw := isWeakGrad_of_contDiff h1
  rw [comp_secT_comp_liftT hp] at hw
  exact weakGrad_ae_unique (isWeakGrad_weakGrad ⟨_, hw⟩) hw

/-- **Integration by parts against a smooth periodic function.** -/
theorem dirB_smooth_eq {e : Torus d → ℝ} (he : MemH1 (densMeasure ρ) e) {Θ : (Fin d → ℝ) → ℝ}
    (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) :
    dirB (densMeasure ρ) e (Θ ∘ secT) = -∫ y, e y * divRho ρ Θ (secT y) := by
  haveI := hρ.isProb
  have hev : MemLp e 2 volume := memLp_vol hρ.haar_le_smul he
  have hge : ∀ k, MemLp (fun y => weakGrad e y k) 2 volume := fun k =>
    memLp_grad_vol hρ.haar_le_smul hρ.le_smul he k
  set Ψ : Fin d → (Fin d → ℝ) → ℝ := fun k z => ρ (liftT z) * Dk Θ k z
  have hΨ : ∀ k, ContDiff ℝ ∞ (Ψ k) := fun k => hρs.mul (contDiff_Dk hΘ k)
  have hΨp : ∀ k, IsPer (Ψ k) := fun k m z => by
    simp only [Ψ, liftT_add_intVec, hp.Dk k m z]
  have hΨb : ∀ k, ∃ B, ∀ x, ‖Ψ k x‖ ≤ B := fun k => periodic_bounded (hΨ k).continuous (hΨp k)
  choose BΨ hBΨ using hΨb
  have hΨm : ∀ k, Measurable fun y => Ψ k (secT y) := fun k =>
    (hΨ k).continuous.measurable.comp measurable_secT
  have hρΨ : ∀ y k, ρ y * Dk Θ k (secT y) = Ψ k (secT y) := fun y k => by
    simp only [Ψ, liftT_secT]
  have hint : ∀ k, Integrable fun y => weakGrad e y k * Ψ k (secT y) := fun k =>
    ((hge k).integrable one_le_two).mul_bdd (c := BΨ k) (hΨm k).aestronglyMeasurable
      (Eventually.of_forall fun y => hBΨ k _)
  unfold dirB
  have hae : (fun x => ∑ k, weakGrad e x k * weakGrad (Θ ∘ secT) x k) =ᵐ[densMeasure ρ]
      fun x => ∑ k, weakGrad e x k * Dk Θ k (secT x) := by
    filter_upwards [hρ.ac.ae_le (weakGrad_smooth hρ hρs hΘ hp)] with x hx
    simp only [hx]
  rw [integral_congr_ae hae, hρ.integral_eq]
  have e1 : (fun x => ρ x * ∑ k, weakGrad e x k * Dk Θ k (secT x)) =
      fun x => ∑ k, weakGrad e x k * Ψ k (secT x) := by
    funext x; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hρΨ]; ring
  rw [e1, integral_finset_sum _ fun k _ => hint k]
  have e2 : ∀ k, ∫ y, weakGrad e y k * Ψ k (secT y) = -∫ y, e y * Dk (Ψ k) k (secT y) := by
    intro k
    rw [integral_mul_Dk_eq (isWeakGrad_weakGrad he.1) (hev.integrable one_le_two)
      (fun j => (hge j).integrable one_le_two) (hΨ k) (hΨp k) k]
    simp
  simp_rw [e2]
  rw [Finset.sum_neg_distrib, neg_inj]
  have hDb : ∀ k, ∃ B, ∀ x, ‖Dk (Ψ k) k x‖ ≤ B := fun k =>
    periodic_bounded (contDiff_Dk (hΨ k) k).continuous ((hΨp k).Dk k)
  choose BD hBD using hDb
  have hsum : ∫ y, e y * divRho ρ Θ (secT y) = ∑ k, ∫ y, e y * Dk (Ψ k) k (secT y) := by
    have hi : ∀ k ∈ Finset.univ, Integrable (fun y => e y * Dk (Ψ k) k (secT y)) := fun k _ =>
      (hev.integrable one_le_two).mul_bdd (c := BD k)
        ((contDiff_Dk (hΨ k) k).continuous.measurable.comp measurable_secT).aestronglyMeasurable
        (Eventually.of_forall fun y => hBD k _)
    rw [← integral_finset_sum _ hi]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [divRho, Finset.mul_sum, Ψ]
  rw [hsum]

/-- **`λ ⟨e,Θ⟩ = ⟨e, AΘ⟩`** for an eigenpair. -/
theorem eig_genA {e : Torus d → ℝ} {lam : ℝ} (he : IsEig (densMeasure ρ) e lam)
    {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) :
    lam * ∫ y, e y * Θ (secT y) ∂densMeasure ρ =
      ∫ y, e y * genA ρ Θ (secT y) ∂densMeasure ρ := by
  have h := he.2.2 _ (memH1_smooth hρ hρs hΘ hp)
  rw [dirB_smooth_eq hρ hρs he.1 hΘ hp] at h
  simp only [Function.comp] at h
  rw [← h, hρ.integral_eq, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have hy : ρ (liftT (secT y)) = ρ y := by rw [liftT_secT]
  have hpos : ρ y ≠ 0 := (hρ.pos.trans_le (hρ.lower y)).ne'
  simp only [genA, hy]
  field_simp

theorem eig_genA_iter {e : Torus d → ℝ} {lam : ℝ} (he : IsEig (densMeasure ρ) e lam)
    {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) (m : ℕ) :
    lam ^ m * ∫ y, e y * Θ (secT y) ∂densMeasure ρ =
      ∫ y, e y * (genA ρ)^[m] Θ (secT y) ∂densMeasure ρ := by
  have hpos : ∀ y, 0 < ρ y := fun y => hρ.pos.trans_le (hρ.lower y)
  induction m generalizing Θ with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, pow_succ, mul_assoc, eig_genA hρ hρs he hΘ hp,
      ih (contDiff_genA hρs hΘ hpos) (isPer_genA hp)]

/-- **Decay of coefficients against smooth functions.** -/
theorem abs_coeff_le {e : Torus d → ℝ} {lam : ℝ} (he : IsEig (densMeasure ρ) e lam)
    {Θ : (Fin d → ℝ) → ℝ} (hΘ : ContDiff ℝ ∞ Θ) (hp : IsPer Θ) (m : ℕ) {B : ℝ}
    (hB : ∀ x, |(genA ρ)^[m] Θ x| ≤ B) :
    |lam| ^ m * |∫ y, e y * Θ (secT y) ∂densMeasure ρ| ≤ (1 + B ^ 2) / 2 := by
  haveI := hρ.isProb
  have hpos : ∀ y, 0 < ρ y := fun y => hρ.pos.trans_le (hρ.lower y)
  rw [← abs_pow, ← abs_mul, eig_genA_iter hρ hρs he hΘ hp m]
  set h := fun y => (genA ρ)^[m] Θ (secT y)
  have hhm : Measurable h :=
    (contDiff_iterate_genA hρs hΘ hpos m).continuous.measurable.comp measurable_secT
  have he2 : Integrable (fun y => e y ^ 2) (densMeasure ρ) := he.1.2.1.integrable_sq
  have hh2 : Integrable (fun y => h y ^ 2) (densMeasure ρ) :=
    (integrable_const (B ^ 2)).mono' (hhm.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2)
  have hint : Integrable (fun y => (e y ^ 2 + h y ^ 2) / 2) (densMeasure ρ) :=
    (he2.add hh2).div_const 2
  calc |∫ y, e y * h y ∂densMeasure ρ| ≤ ∫ y, |e y * h y| ∂densMeasure ρ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, (e y ^ 2 + h y ^ 2) / 2 ∂densMeasure ρ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _) hint
          (Eventually.of_forall fun y => ?_)
        show |e y * h y| ≤ (e y ^ 2 + h y ^ 2) / 2
        rw [abs_mul]
        nlinarith [sq_nonneg (|e y| - |h y|), sq_abs (e y), sq_abs (h y)]
    _ = ((∫ y, e y ^ 2 ∂densMeasure ρ) + ∫ y, h y ^ 2 ∂densMeasure ρ) / 2 := by
        rw [integral_div, integral_add he2 hh2]
    _ ≤ (1 + B ^ 2) / 2 := by
        rw [he.2.1]
        have : ∫ y, h y ^ 2 ∂densMeasure ρ ≤ ∫ _y, B ^ 2 ∂densMeasure ρ :=
          integral_mono hh2 (integrable_const _) fun y => by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
        simp at this
        linarith

end good

end SharpLSI
