import SharpSymmetricLSI.Paper.GroundT2
import SharpSymmetricLSI.Paper.ForceExp
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Paper.CenteredEntropy

/-!
# R30 groundwork: the weak gradient of `f √p_N` on `𝕋^{N×d}`

`U_N ∘ unflat` has the explicit bounded weak gradient `gsG` ((5.12)); with the chain rule for
`e^{-u/2}` and the product rule with a Lipschitz factor, `F · e^{-U_N/2}` has the weak gradient
`(∇F) e^{-U_N/2} - ½ F e^{-U_N/2} ∇U_N` for every integrable weak-gradient pair `(F, ∇F)`.
-/

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- The explicit weak gradient of `U_N ∘ unflat` ((5.12)). -/
noncomputable def gsG (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (N : ℕ)
    (y : UnitAddTorus (Fin N × Fin d)) (p : Fin N × Fin d) : ℝ :=
  (N : ℝ)⁻¹ * ((∑ l ∈ Finset.univ.erase p.1, (bGrad W (unflat y p.1) (unflat y l) p.2 -
    bForceL W (densOf μ) (unflat y p.1) p.2)) + -bForceL W (densOf μ) (unflat y p.1) p.2)

section
variable (hyp : Hyp V W KV KW) {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
  (hac : μ ≪ haar d) {N : ℕ} (hN : 1 ≤ N)
include hyp hac hN

theorem isWeakGrad_gsU : IsWeakGrad (Ucentered W μ N ∘ unflat) (gsG W μ N) := by
  have h := isWeakGrad_Ucentered hyp hac (N := N)
  convert h using 1
  funext y p
  exact (GUsum_flat hyp hN _ (unflat y) p.1 p.2).symm

omit hN in
theorem measurable_gsG (p : Fin N × Fin d) : Measurable fun y => gsG W μ N y p := by
  obtain ⟨-, hβm, -, -⟩ := forceMean_props hyp hac
  have hb := measurable_bGrad hyp (W := W) p.2
  have hu : ∀ i : Fin N, Measurable fun y : UnitAddTorus (Fin N × Fin d) => unflat y i :=
    fun i => (measurable_pi_apply i).comp measurable_unflat
  unfold gsG
  refine measurable_const.mul ((Finset.measurable_sum _ fun l _ => ?_).add ((hβm p.2).comp
    (hu p.1)).neg)
  exact (hb.comp ((hu p.1).prodMk (hu l))).sub ((hβm p.2).comp (hu p.1))

omit hN in
theorem exists_bound_gsG : ∃ C, 0 ≤ C ∧ ∀ y p, |gsG W μ N y p| ≤ C := by
  obtain ⟨Cb', hCb'⟩ := bGrad_bdd hyp (W := W)
  set Cb := max Cb' 0
  have hCb : ∀ x y k, |bGrad W x y k| ≤ Cb := fun x y k => (hCb' x y k).trans (le_max_left _ _)
  have hCb0 : 0 ≤ Cb := le_max_right _ _
  have hβ : ∀ x k, |bForceL W (densOf μ) x k| ≤ Cb := fun x k =>
    abs_bForceL_le hyp (fun x => ENNReal.toReal_nonneg) (integral_densOf_eq_one hac) hCb x k
  refine ⟨2 * Cb, by positivity, fun y p => ?_⟩
  unfold gsG
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; exact p.1.elim0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hpos
  rw [abs_mul, abs_inv, abs_of_pos hNr, inv_mul_le_iff₀ hNr]
  have h1 : |∑ l ∈ Finset.univ.erase p.1, (bGrad W (unflat y p.1) (unflat y l) p.2 -
      bForceL W (densOf μ) (unflat y p.1) p.2)| ≤ ((N : ℝ) - 1) * (2 * Cb) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hcard : ((Finset.univ.erase p.1).card : ℝ) = (N : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        Nat.cast_sub hpos]; simp
    refine (Finset.sum_le_sum (g := fun _ => 2 * Cb) fun l _ => (abs_sub _ _).trans ?_).trans ?_
    · have := hCb (unflat y p.1) (unflat y l) p.2; have := hβ (unflat y p.1) p.2; linarith
    · rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have h2 := hβ (unflat y p.1) p.2
  calc |(∑ l ∈ Finset.univ.erase p.1, (bGrad W (unflat y p.1) (unflat y l) p.2 -
        bForceL W (densOf μ) (unflat y p.1) p.2)) + -bForceL W (densOf μ) (unflat y p.1) p.2|
      ≤ ((N : ℝ) - 1) * (2 * Cb) + Cb := by
        refine (abs_add_le _ _).trans ?_; rw [abs_neg]; linarith
    _ ≤ N * (2 * Cb) := by nlinarith

/-- `e^{-U_N/2}` on the flat torus. -/
noncomputable def gsE (W : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (N : ℕ)
    (y : UnitAddTorus (Fin N × Fin d)) : ℝ :=
  rexp (-(Ucentered W μ N (unflat y)) / 2)

omit hac hN in
theorem measurable_gsE : Measurable (gsE W μ N) :=
  (((measurable_Ucentered hyp μ N).comp measurable_unflat).neg.div_const 2).exp

omit hac hN in
theorem exists_bound_gsE : ∃ B, ∀ y, |gsE W μ N y| ≤ B := by
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μ N
  refine ⟨rexp (BU / 2), fun y => ?_⟩
  rw [gsE, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (by have := (abs_le.1 (hBU (unflat y))).1; linarith)

theorem isWeakGrad_gsE :
    IsWeakGrad (gsE W μ N) (fun y k => -(1 / 2) * gsE W μ N y * gsG W μ N y k) := by
  obtain ⟨BU, hBU⟩ := Ucentered_bdd hyp μ N
  obtain ⟨C, -, hC⟩ := exists_bound_gsG hyp hac (N := N) (μ := μ)
  have hUm := (measurable_Ucentered hyp μ N).comp measurable_unflat
  exact isWeakGrad_exp_neg_half (isWeakGrad_gsU hyp hac hN) (integrable_of_bdd hUm fun y => hBU _)
    (fun k => integrable_of_bdd (measurable_gsG hyp hac k) fun y => hC y k) (fun y => hBU _)

/-- **The weak gradient of `F e^{-U_N/2}`.** -/
theorem isWeakGrad_mul_gsE {F : UnitAddTorus (Fin N × Fin d) → ℝ}
    {gF : UnitAddTorus (Fin N × Fin d) → Fin N × Fin d → ℝ} (hF : IsWeakGrad F gF)
    (hFi : Integrable F volume) (hgFi : ∀ k, Integrable (fun y => gF y k) volume) :
    IsWeakGrad (fun y => F y * gsE W μ N y)
      (fun y k => gF y k * gsE W μ N y + F y * (-(1 / 2) * gsE W μ N y * gsG W μ N y k)) := by
  obtain ⟨BE, hBE⟩ := exists_bound_gsE hyp (W := W) (μ := μ) (N := N)
  obtain ⟨C, -, hC⟩ := exists_bound_gsG hyp hac (N := N) (μ := μ)
  refine hF.mul_lip hFi hgFi (isWeakGrad_gsE hyp hac hN) (measurable_gsE hyp) hBE
    (fun k => (measurable_const.mul (measurable_gsE hyp)).mul (measurable_gsG hyp hac k))
    (L := 1 / 2 * BE * C) fun y k => ?_
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hBE0 : 0 ≤ BE := (abs_nonneg _).trans (hBE y)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hBE y) (by norm_num)) (hC y k) (abs_nonneg _)
    (by positivity)

end

end SharpLSI
