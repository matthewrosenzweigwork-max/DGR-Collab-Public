import SharpSymmetricLSI.Paper.CosineD3
import SharpSymmetricLSI.Paper.RStarFree

/-!
# The `d`-dimensional cosine model (4): `r_* ≥ a`

For admissible `ρ`, `f = √ρ`: `D(ρ) ≥ 4∫|∇f|² + 2aκ ∑ₖ Q_k(ρ)` (`dissipation_cosWd_ge`), from
`D(ρ) = ∑ₖ ∫ (2∂ₖf + κ f ∂ₖ(W*ρ)/κ)²`, dropping the square of the interaction term and
integrating the cross term by parts (`weak_fourier_relations_d` applied to `∂ₖ(f²) = 2f∂ₖf`).
The logarithmic Sobolev inequality of the torus then gives `D ≥ 2a(H + κ ∑ Q_k) ≥ 2a G`, so
`r_* ≥ a = 4π²` for every `d` (`rStar_ge_cosWd`) and `r_* > 0` (`rStar_pos_cosWd`).
-/

open MeasureTheory Set Filter InformationTheory
open scoped ENNReal Real

namespace SharpLSI

variable {d : ℕ}

/-- One coordinate of the dissipation: if `∫ 2uw c = 2πB` and `∫ 2uw s = -2πA`, then
`∫ (2w + κ u G)² ≥ 4 ∫ w² + 2aκ (A² + B²)` for `G = 2π(-A s + B c)`. -/
theorem cosD_term_ge {κ : ℝ} {u w c s : Torus d → ℝ} (hu : MemLp u 2 (haar d))
    (hw : MemLp w 2 (haar d)) (hc : Continuous c) (hs : Continuous s) (hcb : ∀ x, |c x| ≤ 1)
    (hsb : ∀ x, |s x| ≤ 1) {A B : ℝ}
    (r1 : ∫ x, 2 * u x * w x * c x ∂haar d = 2 * π * B)
    (r2 : ∫ x, 2 * u x * w x * s x ∂haar d = -(2 * π) * A) :
    Integrable (fun x => (2 * w x + κ * u x * (2 * π * (-A * s x + B * c x))) ^ 2) (haar d) ∧
    4 * ∫ x, w x ^ 2 ∂haar d + 2 * aCos * κ * (A ^ 2 + B ^ 2) ≤
      ∫ x, (2 * w x + κ * u x * (2 * π * (-A * s x + B * c x))) ^ 2 ∂haar d := by
  set G : Torus d → ℝ := fun x => 2 * π * (-A * s x + B * c x) with hGdef
  have hGc : Continuous G := continuous_const.mul ((continuous_const.mul hs).add
    (continuous_const.mul hc))
  set Cg := 2 * π * (|A| + |B|) with hCgdef
  have hCg : ∀ x, |G x| ≤ Cg := fun x => by
    have hin : |-A * s x + B * c x| ≤ |A| + |B| := by
      calc |-A * s x + B * c x| ≤ |-A * s x| + |B * c x| := abs_add_le _ _
        _ = |A| * |s x| + |B| * |c x| := by rw [abs_mul, abs_mul, abs_neg]
        _ ≤ |A| * 1 + |B| * 1 := by gcongr <;> simp [hsb x, hcb x]
        _ = |A| + |B| := by ring
    rw [hGdef, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), hCgdef]
    exact mul_le_mul_of_nonneg_left hin (by positivity)
  have hCg0 : 0 ≤ Cg := by positivity
  have iU2 : Integrable (fun x => u x ^ 2) (haar d) := hu.integrable_sq
  have iW2 : Integrable (fun x => w x ^ 2) (haar d) := hw.integrable_sq
  have hb2 : ∀ a b : ℝ, |2 * a * b| ≤ a ^ 2 + b ^ 2 := fun a b => by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  have i2uw : ∀ {F : Torus d → ℝ} {C : ℝ}, 0 ≤ C → Continuous F → (∀ x, |F x| ≤ C) →
      Integrable (fun x => 2 * u x * w x * F x) (haar d) := fun {F} {C} hC hF hFb =>
    Integrable.mono' ((iU2.add iW2).const_mul C)
      (((hu.aestronglyMeasurable.const_mul 2).mul hw.aestronglyMeasurable).mul
        hF.aestronglyMeasurable) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |2 * u x * w x| * |F x| ≤ (u x ^ 2 + w x ^ 2) * C :=
              mul_le_mul (hb2 _ _) (hFb x) (abs_nonneg _) (by positivity)
          _ = C * (u x ^ 2 + w x ^ 2) := by ring)
  have iUG := i2uw hCg0 hGc hCg
  have iUU : Integrable (fun x => u x ^ 2 * G x ^ 2) (haar d) :=
    Integrable.mono' (iU2.const_mul (Cg ^ 2))
      ((hu.aestronglyMeasurable.pow 2).mul (hGc.aestronglyMeasurable.pow 2))
      (Eventually.of_forall fun x => by
        have hG2 : G x ^ 2 ≤ Cg ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hCg x) 2
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm (Cg ^ 2)]
        exact mul_le_mul_of_nonneg_left hG2 (sq_nonneg _))
  have hpt : ∀ x, (2 * w x + κ * u x * G x) ^ 2 =
      4 * w x ^ 2 + (2 * κ * (2 * u x * w x * G x) + κ ^ 2 * (u x ^ 2 * G x ^ 2)) :=
    fun x => by ring
  have iD : Integrable (fun x => (2 * w x + κ * u x * G x) ^ 2) (haar d) := by
    simp_rw [hpt]
    exact (iW2.const_mul 4).add ((iUG.const_mul _).add (iUU.const_mul _))
  refine ⟨iD, ?_⟩
  have hexp : ∫ x, (2 * w x + κ * u x * G x) ^ 2 ∂haar d =
      4 * (∫ x, w x ^ 2 ∂haar d) + (2 * κ * (∫ x, 2 * u x * w x * G x ∂haar d) +
        κ ^ 2 * ∫ x, u x ^ 2 * G x ^ 2 ∂haar d) := by
    simp_rw [hpt]
    rw [integral_add (f := fun x => 4 * w x ^ 2)
      (g := fun x => 2 * κ * (2 * u x * w x * G x) + κ ^ 2 * (u x ^ 2 * G x ^ 2))
      (iW2.const_mul 4) ((iUG.const_mul _).add (iUU.const_mul _)),
      integral_add (f := fun x => 2 * κ * (2 * u x * w x * G x))
      (g := fun x => κ ^ 2 * (u x ^ 2 * G x ^ 2)) (iUG.const_mul _) (iUU.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  have hmid : ∫ x, 2 * u x * w x * G x ∂haar d = aCos * (A ^ 2 + B ^ 2) := by
    have i1 := i2uw zero_le_one hs hsb
    have i2 := i2uw zero_le_one hc hcb
    have e : ∀ x, 2 * u x * w x * G x =
        2 * π * (-A * (2 * u x * w x * s x) + B * (2 * u x * w x * c x)) :=
      fun x => by rw [hGdef]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
      integral_const_mul, r1, r2]
    unfold aCos
    ring
  have hJ : 0 ≤ ∫ x, u x ^ 2 * G x ^ 2 ∂haar d :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  rw [hexp, hmid]
  nlinarith [mul_nonneg (sq_nonneg κ) hJ]

/-- **`D(ρ) ≥ 4∫|∇√ρ|² + 2aκ ∑ₖ Q_k(ρ)`.** -/
theorem dissipation_cosWd_ge (κ : ℝ) {ρ : Torus d → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫ x, ρ x ∂haar d = 1) (hH1 : MemH1 (haar d) (fun x => Real.sqrt (ρ x))) :
    ENNReal.ofReal (4 * ∑ k, ∫ x, weakGrad (fun y => Real.sqrt (ρ y)) x k ^ 2 ∂haar d +
      2 * aCos * κ * ∑ k, cosDQ k (densMeasure ρ)) ≤ dissipation (fun _ => 0) (cosWd κ) ρ := by
  set u : Torus d → ℝ := fun x => Real.sqrt (ρ x) with hu_def
  have hu2ρ : ∀ x, u x ^ 2 = ρ x := fun x => Real.sq_sqrt (hρ0 x)
  set A := cosDA ρ
  set B := cosDB ρ
  -- the potential
  set Φ : Torus d → ℝ := fun x => (fun _ : Torus d => (0 : ℝ)) x + convDens (cosWd κ) ρ x
    with hΦ
  have hlift : Φ ∘ liftT = fun z => κ * (cosDT A B z - d) := convDens_cosWd_lift κ hρ1
  have hT1 : ContDiff ℝ 1 (cosDT A B) := (contDiff_cosDT A B).of_le le_top
  have hF : ContDiff ℝ 1 (Φ ∘ liftT) := by
    rw [hlift]; exact contDiff_const.mul (hT1.sub contDiff_const)
  set G : Fin d → Torus d → ℝ := fun k x => 2 * π * (-A k * cosDs k x + B k * cosDc k x)
  have hG' : ∀ᵐ x ∂haar d, ∀ k, weakGrad Φ x k = κ * G k x := by
    filter_upwards [weakGrad_ae_eq_of_contDiff hF] with x hx
    intro k
    rw [hx]
    simp only
    rw [hlift, show (fun z => κ * (cosDT A B z - d)) = fun z => κ * ((cosDT A B) z - d) from rfl,
      fderiv_const_mul ((hT1.differentiable one_ne_zero (secT x)).sub_const _),
      fderiv_sub_const]
    simp only [smul_apply, smul_eq_mul]
    rw [fderiv_cosDT]
    simp only [G, cosDs_secT, cosDc_secT]
  -- weak gradients of `u`
  have hw := isWeakGrad_weakGrad hH1.1
  have hu2 : MemLp u 2 (haar d) := hH1.2.1
  have hg2 : ∀ k, MemLp (fun x => weakGrad u x k) 2 (haar d) := fun k =>
    hH1.2.2.of_le (hw.aestronglyMeasurable_grad k) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ k)
  have hsq := isWeakGrad_sq hw hu2 hg2
  have hb2 : ∀ a b : ℝ, |2 * a * b| ≤ a ^ 2 + b ^ 2 := fun a b => by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
  have hgi : ∀ k, Integrable (fun y => 2 * u y * weakGrad u y k) (haar d) := fun k =>
    Integrable.mono' (hu2.integrable_sq.add (hg2 k).integrable_sq)
      ((hu2.aestronglyMeasurable.const_mul 2).mul (hg2 k).aestronglyMeasurable)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hb2 _ _)
  have hfrel := weak_fourier_relations_d hsq hu2.integrable_sq hgi
  simp_rw [hu2ρ] at hfrel
  -- each coordinate
  have hterm : ∀ k, Integrable (fun x => (2 * weakGrad u x k + κ * u x * G k x) ^ 2) (haar d) ∧
      4 * ∫ x, weakGrad u x k ^ 2 ∂haar d + 2 * aCos * κ * (A k ^ 2 + B k ^ 2) ≤
        ∫ x, (2 * weakGrad u x k + κ * u x * G k x) ^ 2 ∂haar d := fun k =>
    cosD_term_ge hu2 (hg2 k) (continuous_cosDc k) (continuous_cosDs k) (abs_cosDc_le k)
      (abs_cosDs_le k)
      (by rw [show B k = ∫ y, cosDs k y * ρ y ∂haar d from rfl, ← (hfrel k).1]
          congr 1; funext x; ring)
      (by rw [show A k = ∫ y, cosDc k y * ρ y ∂haar d from rfl, ← (hfrel k).2]
          congr 1; funext x; ring)
  have hsum : Integrable (fun x => ∑ k, (2 * weakGrad u x k + κ * u x * G k x) ^ 2) (haar d) :=
    integrable_finsetSum _ fun k _ => (hterm k).1
  -- the dissipation
  unfold dissipation
  rw [if_pos ⟨hH1, ⟨_, isWeakGrad_of_contDiff hF⟩⟩]
  have hL : ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad u x k + u x * weakGrad Φ x k) ^ 2)
      ∂haar d = ENNReal.ofReal (∫ x, ∑ k, (2 * weakGrad u x k + κ * u x * G k x) ^ 2 ∂haar d) := by
    rw [ofReal_integral_eq_lintegral_ofReal hsum (Eventually.of_forall fun x =>
      Finset.sum_nonneg fun k _ => sq_nonneg _)]
    refine lintegral_congr_ae (hG'.mono fun x hx => ?_)
    simp only [hx]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hL, integral_finsetSum _ fun k _ => (hterm k).1]
  refine ENNReal.ofReal_le_ofReal ?_
  have hQ : ∀ k, cosDQ k (densMeasure ρ) = A k ^ 2 + B k ^ 2 := cosDQ_densMeasure hρ0 hρ1
  simp_rw [hQ, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => (hterm k).2

/-- **`r_* ≥ a = 4π²` for the `d`-dimensional cosine model.** -/
theorem rStar_ge_cosWd {κ : ℝ} (hκ : 0 < κ) :
    ENNReal.ofReal aCos ≤ rStar (d := d) (fun _ => 0) (cosWd κ) := by
  have ha0 : 0 < aCos := by unfold aCos; positivity
  refine le_iInf₂ fun ρ hρ => ?_
  obtain ⟨h0, h1, hH1, hgap⟩ := hρ
  have hP := isProbabilityMeasure_densMeasure' h0 h1
  set h : Torus d → ℝ := fun x => Real.sqrt (ρ x)
  have hsq : (fun x => h x ^ 2) = ρ := funext fun x => Real.sq_sqrt (h0 x)
  have hKL : klDiv (densMeasure ρ) (haar d) = ent (haar d) (fun x => h x ^ 2) := by
    rw [hsq, klDiv_densMeasure' h0 h1, ent, if_pos (integrable_of_integral_eq_one' h1), h1]
    simp
  set S := ∑ k, cosDQ k (densMeasure ρ) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => cosDQ_nonneg k _
  have hkS : 0 ≤ κ / 2 * S := by positivity
  -- the gap
  have hG := gap_cosWd (d := d) hκ (densMeasure ρ)
  rw [← hS] at hG
  have hcoe : ((κ / 2 * S : ℝ) : EReal) = ((ENNReal.ofReal (κ / 2 * S) : ℝ≥0∞) : EReal) := by
    rw [EReal.coe_ennreal_ofReal, max_eq_left hkS]
  rw [hcoe, ← EReal.coe_ennreal_add] at hG
  have hGe : (gap (fun _ => 0) (cosWd κ) (densMeasure ρ)).toENNReal =
      klDiv (densMeasure ρ) (haar d) + ENNReal.ofReal (κ / 2 * S) := by
    rw [hG, EReal.toENNReal_coe]
  have hKtop : klDiv (densMeasure ρ) (haar d) ≠ ⊤ := by
    have := (gap_lt_top_of_admissible (hyp_cosWd (d := d) hκ) ⟨h0, h1, hH1, hgap⟩).1
    rw [hG] at this
    intro ht; rw [ht, top_add] at this; simp at this
  have hG0 : klDiv (densMeasure ρ) (haar d) + ENNReal.ofReal (κ / 2 * S) ≠ 0 := by
    intro hz; rw [← hGe] at hz
    rw [EReal.toENNReal_eq_zero_iff] at hz
    exact absurd hgap (not_lt.2 hz)
  -- the Dirichlet integral
  set X := ∑ k, ∫ x, weakGrad h x k ^ 2 ∂haar d with hX
  have hw := isWeakGrad_weakGrad hH1.1
  have hg2 : ∀ k, MemLp (fun x => weakGrad h x k) 2 (haar d) := fun k =>
    hH1.2.2.of_le (hw.aestronglyMeasurable_grad k) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact abs_le_sqrt_sqNorm _ k)
  have hdir : dirichlet (haar d) h = ENNReal.ofReal X := by
    unfold dirichlet sqNorm
    rw [hX, ← integral_finsetSum _ fun k _ => (hg2 k).integrable_sq,
      ofReal_integral_eq_lintegral_ofReal (integrable_finsetSum _ fun k _ => (hg2 k).integrable_sq)
        (Eventually.of_forall fun x => Finset.sum_nonneg fun k _ => sq_nonneg _)]
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun k _ => integral_nonneg fun x => sq_nonneg _
  -- the logarithmic Sobolev inequality
  have hLSI : ent (haar d) (fun x => h x ^ 2) ≤ ENNReal.ofReal (2 / aCos) * dirichlet (haar d) h :=
    lsi_torus_H1 (ι := Fin d) hH1
  rw [← hKL, hdir, ← ENNReal.ofReal_mul (by positivity)] at hLSI
  have hKr : (klDiv (densMeasure ρ) (haar d)).toReal ≤ 2 / aCos * X :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hLSI
  have hK0 : 0 ≤ (klDiv (densMeasure ρ) (haar d)).toReal := ENNReal.toReal_nonneg
  -- the dissipation
  have hD := dissipation_cosWd_ge κ h0 h1 hH1
  rw [← hS] at hD
  rw [hGe, ENNReal.le_div_iff_mul_le (Or.inl (mul_ne_zero two_ne_zero hG0))
    (Or.inl (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ENNReal.add_ne_top.2
      ⟨hKtop, ENNReal.ofReal_ne_top⟩)))]
  have e : ENNReal.ofReal aCos * (2 * (klDiv (densMeasure ρ) (haar d) +
      ENNReal.ofReal (κ / 2 * S))) =
      ENNReal.ofReal (aCos * (2 * ((klDiv (densMeasure ρ) (haar d)).toReal + κ / 2 * S))) := by
    rw [← ENNReal.ofReal_toReal hKtop, ← ENNReal.ofReal_add hK0 hkS,
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul ha0.le, ENNReal.toReal_ofReal hK0]
  rw [e]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hD
  have h1' : aCos * (klDiv (densMeasure ρ) (haar d)).toReal ≤ 2 * X := by
    have := mul_le_mul_of_nonneg_left hKr ha0.le
    rwa [show aCos * (2 / aCos * X) = 2 * X by field_simp] at this
  nlinarith [mul_nonneg (mul_nonneg ha0.le hκ.le) hS0]

/-- **`r_* > 0` for the `d`-dimensional cosine model** (every `d ≥ 1`, every `κ > 0`). -/
theorem rStar_pos_cosWd (hd : 1 ≤ d) {κ : ℝ} (hκ : 0 < κ) :
    0 < rStar (d := d) (fun _ => 0) (cosWd κ) :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by unfold aCos; positivity)) (rStar_ge_cosWd hκ)

end SharpLSI
