import FullLabeledLSI.Paper.Sec8Smooth
import FullLabeledLSI.Paper.Sec8Approx
import FullLabeledLSI.Paper.Sec8Agree
import FullLabeledLSI.Statements.S07_Prop_3_1
import SharpSymmetricLSI.Statements.R01_Theorem_1_1
import SharpSymmetricLSI.Paper.CosineTest

/-!
# Section 8.2: the obstruction at a mean-field quotient optimizer (Proposition 8.2)

For a smooth strictly positive probability density `ρ` and a smooth `k` with `∫ ρ k = 0`, the two
equally weighted species `ρ (1 ± t k)` have average `ρ`.  Their relative entropies are bounded
below by `t² ∫ ρ k² / (2(1+δ))` and their relative Fisher informations bounded above by
`t² ∫ ρ |∇k|² / (1-δ)`, `δ = |t| ‖k‖_∞`.
-/

open MeasureTheory InformationTheory Filter Topology SharpLSI.FL.Gross
open scoped ENNReal ContDiff

namespace SharpLSI.FL
namespace Sec8

variable {d : ℕ}

/-- The sign `+1` for the first species and `-1` for the second. -/
def sgn2 (a : Fin 2) : ℝ := if a = 0 then 1 else -1

theorem abs_sgn2 (a : Fin 2) : |sgn2 a| = 1 := by
  unfold sgn2; split_ifs <;> simp

theorem sgn2_sq (a : Fin 2) : sgn2 a ^ 2 = 1 := by
  unfold sgn2; split_ifs <;> simp

/-- The two equally weighted species `ρ (1 ± t k)`. -/
noncomputable def pertFamily (ρ k : Torus d → ℝ) (t : ℝ) : Family d :=
  ⟨2, fun _ => 1 / 2, fun a x => ρ x * (1 + sgn2 a * t * k x)⟩

theorem pertFamily_bar (ρ k : Torus d → ℝ) (t : ℝ) : (pertFamily ρ k t).bar = ρ := by
  funext x
  have h : ∑ a : Fin 2, (1 / 2 : ℝ) * (ρ x * (1 + sgn2 a * t * k x)) = ρ x := by
    rw [Fin.sum_univ_two]
    simp only [sgn2]
    simp
    ring
  exact h

theorem factor_pos {k : Torus d → ℝ} {B : ℝ} (hB : ∀ x, |k x| ≤ B) {t : ℝ} (ht : |t| * B < 1)
    (a : Fin 2) (x : Torus d) : 1 - |t| * B ≤ 1 + sgn2 a * t * k x ∧
      1 + sgn2 a * t * k x ≤ 1 + |t| * B := by
  have h1 : |sgn2 a * t * k x| ≤ |t| * B := by
    rw [abs_mul, abs_mul, abs_sgn2, one_mul]
    exact mul_le_mul_of_nonneg_left (hB x) (abs_nonneg t)
  constructor <;> linarith [abs_le.1 h1]

/-- Data for the perturbation: a smooth positive probability density `ρ` and a smooth bounded
`k` with `∫ ρ k = 0`. -/
structure PertData (ρ k : Torus d → ℝ) (B : ℝ) : Prop where
  ρs : IsSmoothT ρ
  ρp : ∀ x, 0 < ρ x
  ρ1 : ∫ x, ρ x ∂haar d = 1
  ks : IsSmoothT k
  k0 : ∫ x, ρ x * k x ∂haar d = 0
  kB : ∀ x, |k x| ≤ B

variable {ρ k : Torus d → ℝ} {B t : ℝ}

theorem PertData.fp (h : PertData ρ k B) (ht : |t| * B < 1) (a : Fin 2) (x : Torus d) :
    0 < 1 + sgn2 a * t * k x := by
  linarith [(factor_pos h.kB ht a x).1, abs_nonneg t, (abs_nonneg (k x)).trans (h.kB x)]

theorem PertData.smooth_species (h : PertData ρ k B) (a : Fin 2) :
    IsSmoothT (fun x => ρ x * (1 + sgn2 a * t * k x)) :=
  isSmoothT_mul h.ρs (isSmoothT_one_add (sgn2 a * t) h.ks |> fun h' => by
    simpa [mul_assoc] using h')

theorem PertData.pos_species (h : PertData ρ k B) (ht : |t| * B < 1) (a : Fin 2) (x : Torus d) :
    0 < ρ x * (1 + sgn2 a * t * k x) := mul_pos (h.ρp x) (h.fp ht a x)

theorem PertData.integral_species (h : PertData ρ k B) (a : Fin 2) :
    ∫ x, ρ x * (1 + sgn2 a * t * k x) ∂haar d = 1 := by
  have e : ∀ x, ρ x * (1 + sgn2 a * t * k x) = ρ x + sgn2 a * t * (ρ x * k x) := fun x => by ring
  simp_rw [e]
  have i1 : Integrable ρ (haar d) := integrable_of_smooth h.ρs
  have i2 : Integrable (fun x => ρ x * k x) (haar d) :=
    integrable_of_smooth (isSmoothT_mul h.ρs h.ks)
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, h.ρ1, h.k0]
  simp

theorem PertData.admissible (h : PertData ρ k B) (ht : |t| * B < 1) :
    (pertFamily ρ k t).Admissible := by
  refine ⟨fun _ => by show (0 : ℝ) < 1 / 2; norm_num, ?_, fun a => ?_⟩
  · show ∑ _a : Fin 2, (1 / 2 : ℝ) = 1
    simp [Fin.sum_univ_two]
  · refine ⟨fun x => (h.pos_species ht a x).le, h.integral_species a, ?_⟩
    exact memH1_of_smooth (isSmoothT_sqrt (h.smooth_species a) (h.pos_species ht a))


/-- Pointwise product rule for `√(A (1 + cK))`. -/
theorem sqrt_mul_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (A K : E → ℝ) (c : ℝ)
    (z e : E) (hA : DifferentiableAt ℝ A z) (hK : DifferentiableAt ℝ K z) (hApos : 0 < A z)
    (hS : 0 < 1 + c * K z) :
    2 * fderiv ℝ (fun w => Real.sqrt (A w * (1 + c * K w))) z e -
      Real.sqrt (A z * (1 + c * K z)) * (2 * fderiv ℝ (fun w => Real.sqrt (A w)) z e / Real.sqrt (A z))
      = Real.sqrt (A z) * (c * fderiv ℝ K z e) / Real.sqrt (1 + c * K z) := by
  have hd1 : HasFDerivAt (fun w => A w * (1 + c * K w))
      (A z • (c • fderiv ℝ K z) + (1 + c * K z) • fderiv ℝ A z) z := by
    have h1 : HasFDerivAt (fun w => 1 + c * K w) (c • fderiv ℝ K z) z :=
      ((hK.hasFDerivAt.const_mul c).const_add 1)
    exact hA.hasFDerivAt.mul h1
  have hpos : 0 < A z * (1 + c * K z) := mul_pos hApos hS
  have hs1 := hd1.sqrt hpos.ne'
  have hs2 := hA.hasFDerivAt.sqrt hApos.ne'
  rw [hs1.fderiv, hs2.fderiv]
  simp only [smul_apply, add_apply, smul_eq_mul]
  have hsA : 0 < Real.sqrt (A z) := Real.sqrt_pos.2 hApos
  have hsS : 0 < Real.sqrt (1 + c * K z) := Real.sqrt_pos.2 hS
  rw [Real.sqrt_mul hApos.le]
  have e1 : Real.sqrt (A z) ^ 2 = A z := Real.sq_sqrt hApos.le
  have e2 : Real.sqrt (1 + c * K z) ^ 2 = 1 + c * K z := Real.sq_sqrt hS.le
  field_simp
  rw [e1, e2]
  ring

theorem dT_sqrt_pert (hρ : IsSmoothT ρ) (hk : IsSmoothT k) (hρp : ∀ x, 0 < ρ x) (c : ℝ)
    (z : Fin d → ℝ) (hS : 0 < 1 + c * k (liftT z)) (j : Fin d) :
    2 * dT (fun y => Real.sqrt (ρ y * (1 + c * k y))) j (liftT z) -
      Real.sqrt (ρ (liftT z) * (1 + c * k (liftT z))) *
        (2 * dT (fun y => Real.sqrt (ρ y)) j (liftT z) / Real.sqrt (ρ (liftT z))) =
    Real.sqrt (ρ (liftT z)) * (c * dT k j (liftT z)) / Real.sqrt (1 + c * k (liftT z)) := by
  simp only [dT_liftT]
  exact sqrt_mul_deriv (ρ ∘ liftT) (k ∘ liftT) c z (Pi.single j 1)
    ((hρ.differentiable (by simp)) z) ((hk.differentiable (by simp)) z) (hρp _) hS

/-- The pointwise Taylor bound for `klFun (1 + u)`. -/
theorem klFun_ge {u δ : ℝ} (hδ : δ < 1) (hu : |u| ≤ δ) :
    u ^ 2 / (2 * (1 + δ)) ≤ klFun (1 + u) := by
  have := (SharpLSI.mul_log_taylor_bounds hδ hu).1
  rw [klFun_apply]
  linarith

theorem pert_integrand (h : PertData ρ k B) (ht : |t| * B < 1) (a : Fin 2) (x : Torus d) :
    ∑ j, (2 * dT (fun y => Real.sqrt (ρ y * (1 + sgn2 a * t * k y))) j x -
      Real.sqrt (ρ x * (1 + sgn2 a * t * k x)) *
        (2 * dT (fun y => Real.sqrt (ρ y)) j x / Real.sqrt (ρ x))) ^ 2
      = t ^ 2 * (ρ x * gradSq k x) / (1 + sgn2 a * t * k x) := by
  obtain ⟨z, rfl⟩ : ∃ z, liftT z = x := ⟨secT x, liftT_secT x⟩
  have hS := h.fp ht a (liftT z)
  have hρ := h.ρp (liftT z)
  have hsr : Real.sqrt (ρ (liftT z)) ^ 2 = ρ (liftT z) := Real.sq_sqrt hρ.le
  have hss : Real.sqrt (1 + sgn2 a * t * k (liftT z)) ^ 2 = 1 + sgn2 a * t * k (liftT z) :=
    Real.sq_sqrt hS.le
  have hsq := sgn2_sq a
  simp only [dT_sqrt_pert h.ρs h.ks h.ρp (sgn2 a * t) z hS]
  unfold gradSq
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [div_pow, mul_pow, mul_pow, hsr, hss, mul_pow, hsq]
  field_simp

theorem integrable_rho_gradSq (h : PertData ρ k B) :
    Integrable (fun x => ρ x * gradSq k x) (haar d) := by
  have hk1 := c1T_of_smooth h.ks
  have hm : Measurable (gradSq k) := by
    unfold gradSq
    exact Finset.measurable_sum _ fun j _ => (hk1.dT_measurable j).pow_const 2
  have hb : ∀ j, ∃ K, ∀ y, |dT k j y| ≤ K := fun j => hk1.dT_bounded j
  choose K hK using hb
  obtain ⟨R, hR⟩ := SharpLSI.exists_bound_of_continuous (continuous_of_smooth h.ρs)
  refine Integrable.of_bound ((continuous_of_smooth h.ρs).measurable.mul hm).aestronglyMeasurable
    (R * ∑ j, K j ^ 2) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |gradSq k x| ≤ ∑ j, K j ^ 2 := by
    rw [abs_of_nonneg (gradSq_nonneg k x)]
    exact Finset.sum_le_sum fun j _ => by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hK j x) 2
  exact mul_le_mul (hR x) h1 (abs_nonneg _) ((abs_nonneg _).trans (hR x))

theorem integrable_rho_sq (h : PertData ρ k B) :
    Integrable (fun x => ρ x * k x ^ 2) (haar d) :=
  integrable_of_smooth (isSmoothT_mul h.ρs (isSmoothT_mul h.ks h.ks |> fun h' => by
    simpa [pow_two] using h'))

/-- Lower bound for the relative entropy of a perturbed species. -/
theorem klDiv_pert_ge (h : PertData ρ k B) (ht : |t| * B < 1) (a : Fin 2) :
    ENNReal.ofReal (t ^ 2 * (∫ x, ρ x * k x ^ 2 ∂haar d) / (2 * (1 + |t| * B))) ≤
      klDiv (densMeasure ((pertFamily ρ k t).ρ a)) (densMeasure (pertFamily ρ k t).bar) := by
  have hF := h.admissible ht
  rw [klDiv_species (pertFamily ρ k t) hF a, pertFamily_bar]
  have hδ0 : 0 ≤ |t| * B := by
    have := (abs_nonneg (k (Classical.arbitrary _))).trans (h.kB (Classical.arbitrary _))
    positivity
  have hI := integrable_rho_sq h
  calc ENNReal.ofReal (t ^ 2 * (∫ x, ρ x * k x ^ 2 ∂haar d) / (2 * (1 + |t| * B)))
      = ENNReal.ofReal (∫ x, ρ x * (sgn2 a * t * k x) ^ 2 / (2 * (1 + |t| * B)) ∂haar d) := by
        congr 1
        have e : ∀ x, ρ x * (sgn2 a * t * k x) ^ 2 = t ^ 2 * (ρ x * k x ^ 2) := fun x => by
          have := sgn2_sq a
          calc ρ x * (sgn2 a * t * k x) ^ 2 = ρ x * (sgn2 a ^ 2 * t ^ 2 * k x ^ 2) := by ring
            _ = _ := by rw [this]; ring
        simp_rw [e]
        rw [integral_div, integral_const_mul]
    _ = ∫⁻ x, ENNReal.ofReal (ρ x * (sgn2 a * t * k x) ^ 2 / (2 * (1 + |t| * B))) ∂haar d := by
        refine ofReal_integral_eq_lintegral_ofReal ?_ ?_
        · have e : ∀ x, ρ x * (sgn2 a * t * k x) ^ 2 = t ^ 2 * (ρ x * k x ^ 2) := fun x => by
            have := sgn2_sq a
            calc ρ x * (sgn2 a * t * k x) ^ 2 = ρ x * (sgn2 a ^ 2 * t ^ 2 * k x ^ 2) := by ring
              _ = _ := by rw [this]; ring
          simp_rw [e]
          exact ((hI.const_mul (t ^ 2)).div_const _)
        · exact Eventually.of_forall fun x => by
            have := h.ρp x
            positivity
    _ ≤ _ := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        have hρx : 0 < ρ x := h.ρp x
        have hu : |sgn2 a * t * k x| ≤ |t| * B := by
          rw [abs_mul, abs_mul, abs_sgn2, one_mul]
          exact mul_le_mul_of_nonneg_left (h.kB x) (abs_nonneg t)
        have hk := klFun_ge ht hu
        have hrat : ρ x * (1 + sgn2 a * t * k x) / ρ x = 1 + sgn2 a * t * k x := by
          field_simp
        have : (pertFamily ρ k t).ρ a x / ρ x = 1 + sgn2 a * t * k x := hrat
        rw [this, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hk hρx.le

/-- Upper bound for the relative Fisher information of a perturbed species. -/
theorem relFisher_pert_le (h : PertData ρ k B) (ht : |t| * B < 1) (a : Fin 2) :
    relFisher ((pertFamily ρ k t).ρ a) (pertFamily ρ k t).bar ≤
      ENNReal.ofReal (t ^ 2 * (∫ x, ρ x * gradSq k x ∂haar d) / (1 - |t| * B)) := by
  rw [pertFamily_bar]
  show relFisher (fun x => ρ x * (1 + sgn2 a * t * k x)) ρ ≤ _
  rw [relFisher_smooth (h.smooth_species a) h.ρs (h.pos_species ht a) h.ρp]
  simp_rw [pert_integrand h ht a]
  have hI := integrable_rho_gradSq h
  have hδ0 : 0 ≤ |t| * B := by
    have := (abs_nonneg (k (Classical.arbitrary _))).trans (h.kB (Classical.arbitrary _))
    positivity
  have hpos : 0 < 1 - |t| * B := by linarith
  calc ∫⁻ x, ENNReal.ofReal (t ^ 2 * (ρ x * gradSq k x) / (1 + sgn2 a * t * k x)) ∂haar d
      ≤ ∫⁻ x, ENNReal.ofReal (t ^ 2 * (ρ x * gradSq k x) / (1 - |t| * B)) ∂haar d := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        have hn : 0 ≤ t ^ 2 * (ρ x * gradSq k x) :=
          mul_nonneg (sq_nonneg _) (mul_nonneg (h.ρp x).le (gradSq_nonneg k x))
        exact div_le_div_of_nonneg_left hn hpos (factor_pos h.kB ht a x).1
    _ = ENNReal.ofReal (∫ x, t ^ 2 * (ρ x * gradSq k x) / (1 - |t| * B) ∂haar d) := by
        symm
        refine ofReal_integral_eq_lintegral_ofReal ((hI.const_mul (t ^ 2)).div_const _) ?_
        exact Eventually.of_forall fun x => by
          have := h.ρp x
          have := gradSq_nonneg k x
          positivity
    _ = _ := by
        congr 1
        rw [integral_div, integral_const_mul]

variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- For a small nonzero `t` the perturbed family has quotient below `r_*`. -/
theorem rMs_lt_of_test (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hk : PertData ρ k B)
    (hG : 0 < gap V W (densMeasure ρ))
    (hatt : dissipation V W ρ = 2 * rStar V W * (gap V W (densMeasure ρ)).toENNReal)
    (hVpos : 0 < ∫ x, ρ x * k x ^ 2 ∂haar d)
    (hlt : ∫ x, ρ x * gradSq k x ∂haar d <
      (rStar V W).toReal * ∫ x, ρ x * k x ^ 2 ∂haar d) :
    rMs V W < rStar V W := by
  have hRfin : rStar V W < ⊤ := Sec8.rStar_lt_top hd hyp
  set R := (rStar V W).toReal with hR
  have hRr : ENNReal.ofReal R = rStar V W := ENNReal.ofReal_toReal hRfin.ne
  set D := ∫ x, ρ x * gradSq k x ∂haar d with hDdef
  set V0 := ∫ x, ρ x * k x ^ 2 ∂haar d with hV0def
  have hD0 : 0 ≤ D := integral_nonneg fun x => mul_nonneg (hk.ρp x).le (gradSq_nonneg k x)
  have hRV : 0 < R * V0 := lt_of_le_of_lt hD0 hlt
  have hRpos : 0 < R := (mul_pos_iff_of_pos_right hVpos).1 hRV
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hk.kB (Classical.arbitrary _))
  set B' := B + 1 with hB'
  have hB'pos : 0 < B' := by linarith
  have hk' : PertData ρ k B' := ⟨hk.ρs, hk.ρp, hk.ρ1, hk.ks, hk.k0,
    fun x => (hk.kB x).trans (by linarith)⟩
  set e0 := (R * V0 - D) / (D + R * V0) with he0
  have hDRpos : 0 < D + R * V0 := by linarith
  have he0pos : 0 < e0 := div_pos (by linarith) hDRpos
  set δ := min (1 / 2) (e0 / 2) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ e0 / 2 := min_le_right _ _
  set t := δ / B' with ht
  have htpos : 0 < t := div_pos hδpos hB'pos
  have htB : |t| * B' = δ := by
    rw [abs_of_pos htpos, ht]; field_simp
  have htB1 : |t| * B' < 1 := by rw [htB]; linarith
  have hkey : D * (1 + δ) < R * V0 * (1 - δ) := by
    have h1 : δ * (D + R * V0) ≤ e0 / 2 * (D + R * V0) :=
      mul_le_mul_of_nonneg_right hδ2 hDRpos.le
    have h2 : e0 / 2 * (D + R * V0) = (R * V0 - D) / 2 := by
      rw [he0]; field_simp
    nlinarith
  set F := pertFamily ρ k t with hFdef
  have hF : F.Admissible := hk'.admissible htB1
  have hbar : F.bar = ρ := pertFamily_bar ρ k t
  obtain ⟨hG', hD', -⟩ := species_decomposition hyp F hF
  rw [hbar] at hG' hD'
  have hfin := Sec8.terms_finite hd hyp F hF
  rw [hbar] at hfin
  have hgfin : gap V W (densMeasure ρ) < ⊤ := hfin.2.2.1
  set g0 := (gap V W (densMeasure ρ)).toENNReal with hg0
  have hg0top : g0 ≠ ⊤ := EReal.toENNReal_ne_top_iff.2 hgfin.ne
  have hg0pos : g0 ≠ 0 := (EReal.toENNReal_pos_iff.2 hG).ne'
  have hg_eq : gap V W (densMeasure ρ) = (g0 : EReal) := (EReal.coe_toENNReal hG.le).symm
  set K : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (densMeasure ρ)
    with hK
  set I : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) ρ with hI
  have hmsGap : msGap V W F = ((g0 + K : ℝ≥0∞) : EReal) := by
    rw [hG', hg_eq, EReal.coe_ennreal_add]
  have hms_pos : 0 < msGap V W F := by
    rw [hmsGap]; exact EReal.coe_ennreal_pos.2 (pos_iff_ne_zero.2 (by simp [hg0pos]))
  have hKtop : K ≠ ⊤ := by
    refine (ENNReal.sum_lt_top.2 fun a _ => ?_).ne
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin.2.2.2.2 a).2
  have htoE : (msGap V W F).toENNReal = g0 + K := by rw [hmsGap, EReal.toENNReal_coe]
  -- bounds on the relative terms
  set L := ENNReal.ofReal (t ^ 2 * V0 / (2 * (1 + δ))) with hL
  set U := ENNReal.ofReal (t ^ 2 * D / (1 - δ)) with hU
  have hθ : ENNReal.ofReal (1 / 2 : ℝ) + ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  have hKge : L ≤ K := by
    have h1 : ∀ a : Fin 2, L ≤ klDiv (densMeasure ((pertFamily ρ k t).ρ a)) (densMeasure ρ) :=
      fun a => by
        have := klDiv_pert_ge hk' htB1 a
        rw [pertFamily_bar, htB] at this
        exact this
    calc L = (ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2)) * L := by rw [hθ, one_mul]
      _ = ENNReal.ofReal (1 / 2) * L + ENNReal.ofReal (1 / 2) * L := by rw [add_mul]
      _ ≤ _ := by
        rw [hK]
        refine le_of_le_of_eq ?_ (Fin.sum_univ_two _).symm
        exact add_le_add (mul_le_mul' le_rfl (h1 0)) (mul_le_mul' le_rfl (h1 1))
  have hIle : I ≤ U := by
    have h1 : ∀ a : Fin 2, relFisher ((pertFamily ρ k t).ρ a) ρ ≤ U := fun a => by
      have := relFisher_pert_le hk' htB1 a
      rw [pertFamily_bar, htB] at this
      exact this
    calc I = ENNReal.ofReal (1 / 2) * relFisher ((pertFamily ρ k t).ρ (0 : Fin 2)) ρ +
          ENNReal.ofReal (1 / 2) * relFisher ((pertFamily ρ k t).ρ (1 : Fin 2)) ρ := by
          rw [hI]; exact Fin.sum_univ_two _
      _ ≤ ENNReal.ofReal (1 / 2) * U + ENNReal.ofReal (1 / 2) * U := by
        exact add_le_add (mul_le_mul' le_rfl (h1 0)) (mul_le_mul' le_rfl (h1 1))
      _ = U := by rw [← add_mul, hθ, one_mul]
  have hUlt : U < 2 * rStar V W * L := by
    rw [← hRr, hU, hL, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by positivity)]
    have hpos : 0 < 2 * R * (t ^ 2 * V0 / (2 * (1 + δ))) := by positivity
    refine (ENNReal.ofReal_lt_ofReal_iff hpos).2 ?_
    have e : 2 * R * (t ^ 2 * V0 / (2 * (1 + δ))) = t ^ 2 * (R * V0) / (1 + δ) := by
      field_simp
    rw [e, div_lt_div_iff₀ (by linarith) (by linarith)]
    have ht2 : 0 < t ^ 2 := by positivity
    nlinarith [mul_pos ht2 hRV]
  have hlt2 : msDiss V W F < 2 * rStar V W * (g0 + K) := by
    rw [hD', hatt, mul_add]
    refine ENNReal.add_lt_add_left (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
      hRfin.ne) hg0top) ?_
    exact lt_of_le_of_lt hIle (lt_of_lt_of_le hUlt (mul_le_mul' le_rfl hKge))
  have hmsA : MsAdmissible V W F := ⟨hF, hms_pos⟩
  have h2g : 2 * (g0 + K) ≠ 0 := by simp [hg0pos]
  have h2gtop : 2 * (g0 + K) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.2 ⟨hg0top, hKtop⟩)
  calc rMs V W ≤ msDiss V W F / (2 * (msGap V W F).toENNReal) := by
        unfold rMs; exact iInf₂_le F hmsA
    _ < rStar V W := by
        rw [htoE]
        refine (ENNReal.div_lt_iff (Or.inl h2g) (Or.inl h2gtop)).2 ?_
        calc msDiss V W F < 2 * rStar V W * (g0 + K) := hlt2
          _ = rStar V W * (2 * (g0 + K)) := by ring

/-- Proposition 8.2 (given the full-labeled limit theorem). -/
theorem quotient_optimizer_core (hd : 1 ≤ d) (hyp : Hyp V W KV KW)
    (hlim : Tendsto (fun N => rAll V W N) atTop (𝓝 (rMs V W)))
    (hρs : IsSmoothT ρ) (hρp : ∀ x, 0 < ρ x) (hρ1 : ∫ x, ρ x ∂haar d = 1)
    (hG : 0 < gap V W (densMeasure ρ))
    (hatt : dissipation V W ρ = 2 * rStar V W * (gap V W (densMeasure ρ)).toENNReal)
    (hP : poincareConst (densMeasure ρ) < rStar V W) :
    Tendsto (fun N => rAll V W N) atTop (𝓝 (rMs V W)) ∧ rMs V W < rStar V W ∧
      Tendsto (fun N => rSym V W N) atTop (𝓝 (rStar V W)) := by
  refine ⟨hlim, ?_, SharpLSI.sharp_symmetric_lsi_limit hd hyp⟩
  have hRfin : rStar V W < ⊤ := Sec8.rStar_lt_top hd hyp
  have hRr : ENNReal.ofReal (rStar V W).toReal = rStar V W := ENNReal.ofReal_toReal hRfin.ne
  obtain ⟨k, hks, hk0, hVpos, hlt⟩ := exists_smooth_test hρs hρp hρ1 (R := (rStar V W).toReal)
    (by rw [hRr]; exact hP)
  have hkc := continuous_of_smooth hks
  obtain ⟨B, hB⟩ := SharpLSI.exists_bound_of_continuous hkc
  exact rMs_lt_of_test hd hyp (B := B) ⟨hρs, hρp, hρ1, hks, hk0, hB⟩ hG hatt hVpos hlt

end Sec8
end SharpLSI.FL
