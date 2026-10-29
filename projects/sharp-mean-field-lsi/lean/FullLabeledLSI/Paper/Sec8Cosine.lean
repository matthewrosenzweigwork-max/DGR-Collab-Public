import FullLabeledLSI.Statements.S07_Prop_3_1
import FullLabeledLSI.Paper.Sec3Dilute
import FullLabeledLSI.Defs.F07_Sanity
import SharpSymmetricLSI.Statements.R09_Cosine_Upper
import SharpSymmetricLSI.Statements.R10_Lemma_3_2
import SharpSymmetricLSI.Statements.R12_Cosine_Strict
import SharpSymmetricLSI.Statements.R01_Theorem_1_1
import SharpSymmetricLSI.Paper.CircleLSIExt
import SharpSymmetricLSI.Paper.CosineTagged

/-!
# Section 8.4: the cosine interaction (Corollary 8.3)

`r_ms = 4 pi^2` for `V = 0`, `W_kappa = kappa (cos - 1)` on the circle.  The lower bound compares the
multi-species excess with the one-species cosine expansion and the circle LSI of each species; the
upper bound is the one-particle test `1 + epsilon cos` through the equilibrium `m`.
-/

open MeasureTheory InformationTheory Filter Topology SharpLSI
open scoped ENNReal ContDiff

namespace SharpLSI.FL
namespace Sec8

theorem hyp_zero {d : ℕ} : Hyp (fun _ : Torus d => (0 : ℝ)) (fun _ _ => (0 : ℝ)) 0 0 where
  KV_nonneg := le_rfl
  KW_nonneg := le_rfl
  continuous_V := continuous_const
  continuous_W := continuous_const
  semiconvex_V := by intros; simp
  semiconvex_W := by intros; simp
  symm := fun _ _ => rfl
  diag := fun _ => rfl

theorem convDens_zero {d : ℕ} (ρ : Torus d → ℝ) :
    (fun y => (0 : ℝ) + convDens (fun _ _ => (0 : ℝ)) ρ y) = fun _ => 0 := by
  funext y; simp [convDens]

theorem hasWeakGrad_zero {d : ℕ} (ρ : Torus d → ℝ) :
    HasWeakGrad (fun y => (0 : ℝ) + convDens (fun _ _ => (0 : ℝ)) ρ y) := by
  rw [convDens_zero]; exact ⟨_, isWeakGrad_const 0⟩

theorem speciesDiss_zero {d : ℕ} (ρa ρb : Torus d → ℝ) :
    speciesDiss (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) ρa ρb =
      dissipation (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) ρa := by
  unfold speciesDiss dissipation
  by_cases hm : MemH1 (haar d) (fun x => Real.sqrt (ρa x))
  · rw [if_pos ⟨hm, hasWeakGrad_zero ρb⟩, if_pos ⟨hm, hasWeakGrad_zero ρa⟩]
    simp only [convDens_zero]
  · rw [if_neg (fun h => hm h.1), if_neg (fun h => hm h.1)]

theorem dissipation_zero_eq {ρ : Torus 1 → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    dissipation (fun _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) ρ = fisherInfo (densMeasure ρ) (haar 1) := by
  rw [fisherInfo_densMeasure_eq hρ0 hρ1 hH]
  have hw := hasWeakGrad_zero ρ
  unfold dissipation
  rw [if_pos ⟨hH, hw⟩]
  have hae : weakGrad (fun y => (0 : ℝ) + convDens (fun _ _ => (0 : ℝ)) ρ y) =ᵐ[haar 1] 0 := by
    rw [convDens_zero]; exact weakGrad_ae_eq (isWeakGrad_const 0)
  have hg2 := memLp_weakGrad_zero hH
  calc ∫⁻ x, ENNReal.ofReal (∑ k, (2 * weakGrad (fun y => Real.sqrt (ρ y)) x k +
        Real.sqrt (ρ x) * weakGrad (fun y => (0 : ℝ) + convDens (fun _ _ => (0 : ℝ)) ρ y) x k) ^ 2)
        ∂haar 1
      = ∫⁻ x, ENNReal.ofReal (4 * weakGrad (fun y => Real.sqrt (ρ y)) x 0 ^ 2) ∂haar 1 := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with x hx
        have : weakGrad (fun y => (0 : ℝ) + convDens (fun _ _ => (0 : ℝ)) ρ y) x 0 = 0 := by
          rw [hx]; rfl
        simp only [Fin.sum_univ_one, this, mul_zero, add_zero]
        congr 1; ring
    _ = ENNReal.ofReal (∫ x, 4 * weakGrad (fun y => Real.sqrt (ρ y)) x 0 ^ 2 ∂haar 1) :=
        (ofReal_integral_eq_lintegral_ofReal (hg2.integrable_sq.const_mul 4)
          (Eventually.of_forall fun x => by positivity)).symm
    _ = _ := by rw [integral_const_mul]

theorem fisher_identity (F : Family 1) (hF : F.Admissible) :
    ∑ a, ENNReal.ofReal (F.θ a) * fisherInfo (densMeasure (F.ρ a)) (haar 1) =
      fisherInfo (densMeasure F.bar) (haar 1) +
        ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar := by
  obtain ⟨-, hD, -⟩ := species_decomposition (hyp_zero (d := 1)) F hF
  unfold msDiss at hD
  simp_rw [speciesDiss_zero] at hD
  rw [dissipation_zero_eq (bar_nonneg F hF) (bar_integral F hF) (memH1_sqrtBar F hF)] at hD
  rw [← hD]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dissipation_zero_eq (hF.2.2 a).1 (hF.2.2 a).2.1 (hF.2.2 a).2.2]

/-- From the real inequality `2a H ≤ I` for finite `H`, `I`. -/
theorem ofReal_mul_le_of_toReal {a : ℝ} (ha : 0 ≤ a) {H I : ℝ≥0∞} (hH : H ≠ ⊤) (hI : I ≠ ⊤)
    (h : a * H.toReal ≤ I.toReal) : ENNReal.ofReal a * H ≤ I := by
  rw [← ENNReal.ofReal_toReal hH, ← ENNReal.ofReal_toReal hI, ← ENNReal.ofReal_mul ha]
  exact ENNReal.ofReal_le_ofReal h

/-- The multi-species cosine excess is nonnegative: `2a G_θ ≤ D_θ`. -/
theorem cos_key {κ : ℝ} (hκ : 0 < κ) (F : Family 1) (hF : F.Admissible) :
    ENNReal.ofReal (2 * aCos) * (msGap cosV (cosW κ) F).toENNReal ≤ msDiss cosV (cosW κ) F := by
  obtain ⟨hGd, hDd, -⟩ := species_decomposition (cosine_hyp hκ) F hF
  have ha : 0 < aCos := by unfold aCos; positivity
  have hb0 := bar_nonneg F hF
  have hb1 := bar_integral F hF
  have hbH := memH1_sqrtBar F hF
  obtain ⟨hHm, hIm, -, -⟩ := circle_quantitative_lsi hb0 hb1 hbH
  have hsp : ∀ a, klDiv (densMeasure (F.ρ a)) (haar 1) ≠ ⊤ ∧
      fisherInfo (densMeasure (F.ρ a)) (haar 1) ≠ ⊤ ∧
      ENNReal.ofReal (2 * aCos) * klDiv (densMeasure (F.ρ a)) (haar 1) ≤
        fisherInfo (densMeasure (F.ρ a)) (haar 1) := fun a => by
    obtain ⟨h1, h2, -, h4⟩ := circle_quantitative_lsi (hF.2.2 a).1 (hF.2.2 a).2.1 (hF.2.2 a).2.2
    refine ⟨h1, h2, ofReal_mul_le_of_toReal (by positivity) h1 h2 ?_⟩
    nlinarith [sq_nonneg (klDiv (densMeasure (F.ρ a)) (haar 1)).toReal]
  have hfe := cosine_free_energy hκ
  set Q := firstMode F.bar with hQ
  have hQ0 : 0 ≤ Q := Complex.normSq_nonneg _
  have hgap := hfe.2.2.2.1 F.bar hb0 hb1
  have hexp := cosine_dissipation_expansion hκ hb0 hb1 hIm
  set Hm := klDiv (densMeasure F.bar) (haar 1) with hHmdef
  set K : ℝ≥0∞ := ∑ a, ENNReal.ofReal (F.θ a) *
    klDiv (densMeasure (F.ρ a)) (densMeasure F.bar) with hK
  have hent := entropy_identity F hF
  -- the gap
  have hmsGap : msGap cosV (cosW κ) F =
      ((Hm + K + ENNReal.ofReal (κ / 2 * Q) : ℝ≥0∞) : EReal) := by
    rw [hGd, hgap, EReal.coe_ennreal_add, EReal.coe_ennreal_add,
      EReal.coe_ennreal_ofReal, max_eq_left (by positivity)]
    abel
  rw [hmsGap, EReal.toENNReal_coe]
  -- the dissipation
  rw [hDd, hexp]
  have hsum : ENNReal.ofReal (2 * aCos) * (Hm + K) ≤
      ∑ a, ENNReal.ofReal (F.θ a) * fisherInfo (densMeasure (F.ρ a)) (haar 1) := by
    rw [← hent, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    calc ENNReal.ofReal (2 * aCos) * (ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar 1))
        = ENNReal.ofReal (F.θ a) * (ENNReal.ofReal (2 * aCos) * klDiv (densMeasure (F.ρ a)) (haar 1)) := by
          ring
      _ ≤ _ := mul_le_mul' le_rfl (hsp a).2.2
  rw [fisher_identity F hF] at hsum
  have hQterm : ENNReal.ofReal (2 * aCos) * ENNReal.ofReal (κ / 2 * Q) ≤
      ENNReal.ofReal (2 * aCos * κ * Q) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ aCos * κ * Q := by positivity
    nlinarith
  calc ENNReal.ofReal (2 * aCos) * (Hm + K + ENNReal.ofReal (κ / 2 * Q))
      = ENNReal.ofReal (2 * aCos) * (Hm + K) +
        ENNReal.ofReal (2 * aCos) * ENNReal.ofReal (κ / 2 * Q) := by ring
    _ ≤ (fisherInfo (densMeasure F.bar) (haar 1) +
          ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar) +
        ENNReal.ofReal (2 * aCos * κ * Q) := add_le_add hsum hQterm
    _ ≤ _ := by
        have : fisherInfo (densMeasure F.bar) (haar 1) + ENNReal.ofReal (2 * aCos * κ * Q) +
          ENNReal.ofReal (κ ^ 2 * ∫ x, F.bar x * weakGrad (gConv F.bar) x 0 ^ 2 ∂haar 1) +
          ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar =
          ((fisherInfo (densMeasure F.bar) (haar 1) +
          ∑ a, ENNReal.ofReal (F.θ a) * relFisher (F.ρ a) F.bar) +
            ENNReal.ofReal (2 * aCos * κ * Q)) +
          ENNReal.ofReal (κ ^ 2 * ∫ x, F.bar x * weakGrad (gConv F.bar) x 0 ^ 2 ∂haar 1) := by ring
        rw [hQ, this]
        exact le_self_add

/-- The one-particle test `1 + ε cos(2πx)` gives `r_LS(m) ≤ 4π²`. -/
theorem rLS_haar_le : rLS (haar 1) ≤ ENNReal.ofReal aCos := by
  have hsmall : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < 1 / 40 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (by norm_num)))
  have hne : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ≠ 0 := self_mem_nhdsWithin
  refine ge_of_tendsto cosine_test_quotient ?_
  filter_upwards [hsmall, hne] with ε h1 h2
  have hE : 0 < entHEps ε := by
    have hb := (abs_le.mp (entHEps_approx (ε := ε) (by linarith))).1
    have he2 : 0 < ε ^ 2 := by positivity
    have h3 : |ε| ^ 3 = |ε| * ε ^ 2 := by rw [pow_succ, sq_abs]; ring
    have h4 : 0 < ε ^ 2 * (1 - 20 * |ε|) := mul_pos he2 (by linarith)
    rw [h3] at hb
    linarith
  have hpos : 0 < ent (haar 1) (fun x => (1 + ε * gCos x) ^ 2) := by
    rw [ent_hEps]; exact ENNReal.ofReal_pos.mpr hE
  unfold rLS
  exact iInf₂_le (f := fun (f : Torus 1 → ℝ) _ =>
    2 * dirichlet (haar 1) f / ent (haar 1) (fun x => f x ^ 2))
    (fun x => 1 + ε * gCos x) ⟨memH1_hEps ε, hpos⟩

theorem haar_minimizer {κ : ℝ} (hκ : 0 < κ) :
    IsMinimizer cosV (cosW κ) (⟨haar 1, inferInstance⟩ : ProbabilityMeasure (Torus 1)) :=
  ((cosine_free_energy hκ).2.2.1 _).2 rfl

/-- Corollary 8.3: `r_ms = 4π²`. -/
theorem cosine_rMs {κ : ℝ} (hκ : 0 < κ) : rMs cosV (cosW κ) = ENNReal.ofReal aCos := by
  refine le_antisymm ?_ ?_
  · refine le_trans ?_ rLS_haar_le
    have h := equilibrium_inf_le_rLS (cosine_hyp hκ) (haar_minimizer hκ)
    refine le_trans (le_iInf₂ fun F hF => ?_) h
    exact iInf₂_le F hF.1
  · unfold rMs
    refine le_iInf₂ fun F hF => ?_
    have hpos : 0 < (msGap cosV (cosW κ) F).toENNReal := EReal.toENNReal_pos_iff.2 hF.2
    have hfin : (msGap cosV (cosW κ) F).toENNReal ≠ ⊤ :=
      EReal.toENNReal_ne_top_iff.2 (msGap_msDiss_lt_top (le_refl 1) (cosine_hyp hκ) hF.1).1.ne
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos.ne'))
      (Or.inl (ENNReal.mul_ne_top (by norm_num) hfin))]
    have h := cos_key hκ F hF.1
    calc ENNReal.ofReal aCos * (2 * (msGap cosV (cosW κ) F).toENNReal)
        = ENNReal.ofReal (2 * aCos) * (msGap cosV (cosW κ) F).toENNReal := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]; ring
      _ ≤ _ := h

/-- Corollary 8.3, (8.13). -/
theorem cosine_core {κ : ℝ} (hκ : 0 < κ)
    (hlim : Tendsto (fun N => rAll cosV (cosW κ) N) atTop (𝓝 (rMs cosV (cosW κ)))) :
    rMs cosV (cosW κ) = ENNReal.ofReal aCos ∧
      Tendsto (fun N => rAll cosV (cosW κ) N) atTop (𝓝 (ENNReal.ofReal aCos)) ∧
      ENNReal.ofReal aCos < rStar cosV (cosW κ) ∧
      Tendsto (fun N => rSym cosV (cosW κ) N) atTop (𝓝 (rStar cosV (cosW κ))) :=
  ⟨cosine_rMs hκ, (cosine_rMs hκ) ▸ hlim, cosine_strict hκ,
    sharp_symmetric_lsi_limit (le_refl 1) (cosine_hyp hκ)⟩

end Sec8
end SharpLSI.FL
