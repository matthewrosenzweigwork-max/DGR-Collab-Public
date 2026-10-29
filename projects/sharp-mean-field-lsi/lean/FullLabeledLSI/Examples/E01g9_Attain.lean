import FullLabeledLSI.Examples.E01g9_Congr
import FullLabeledLSI.Examples.E01g5_EL
import FullLabeledLSI.Examples.E01g7_LamG
import FullLabeledLSI.Examples.E01b_LaneA

/-!
# Lane D, Task C (E01g9): Lemma 9.9, `scalar_quotient_attainment`
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem GR_one {C : Torus 1 → ℝ} (hC : GoodKernel C) : GR C (fun _ => (1 : ℝ)) = 0 := by
  have hCc := continuous_of_smooth hC.smooth
  have h0 : ∀ x : Torus 1, 0 ≤ (1 : ℝ) := fun _ => zero_le_one
  have h1 : ∫ x : Torus 1, (1 : ℝ) ∂haar 1 = 1 := by simp
  unfold GR entR cqR
  have hd : densMeasure (fun _ : Torus 1 => (1 : ℝ)) = haar 1 := by
    simp [densMeasure]
  rw [hd]
  have hconv : ∀ x : Torus 1, convT C (fun _ => (1 : ℝ)) x = 0 := by
    intro x
    unfold convT
    simp only [mul_one]
    rw [integral_sub_left_eq_self (fun z => C z) (haar 1) x]
    exact hC.meanZero
  simp [hconv]

theorem nonneg_of_cont_ae {v : Torus 1 → ℝ} (hv : Continuous v) (h : ∀ᵐ x ∂haar 1, 0 ≤ v x) :
    ∀ x, 0 ≤ v x := by
  have h2 : v =ᵐ[haar 1] fun x => |v x| := h.mono fun x hx => (abs_of_nonneg hx).symm
  have := (Continuous.ae_eq_iff_eq (haar 1) hv hv.abs).1 h2
  intro x
  rw [this]; exact abs_nonneg _

/-- An admissible density can be replaced by a continuous one with the same gap and dissipation. -/
theorem exists_cont_adm {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) {ρ : Torus 1 → ℝ}
    (hρ : Admissible zeroV (attrW C) ρ) :
    ∃ ρ' : Torus 1 → ℝ, Continuous ρ' ∧ Admissible zeroV (attrW C) ρ' ∧
      dissipation zeroV (attrW C) ρ' = dissipation zeroV (attrW C) ρ ∧
      gap zeroV (attrW C) (densMeasure ρ') = gap zeroV (attrW C) (densMeasure ρ) := by
  obtain ⟨h0, h1, hH, hg⟩ := (admissible_iff hC hmin).1 hρ
  obtain ⟨v, hvc, hvae⟩ := exists_cont_rep hH
  have hv0 : ∀ x, 0 ≤ v x :=
    nonneg_of_cont_ae hvc (hvae.mono fun x hx => by rw [hx]; exact Real.sqrt_nonneg _)
  set ρ' : Torus 1 → ℝ := fun x => v x ^ 2 with hρ'
  have hae : ρ' =ᵐ[haar 1] ρ := hvae.mono fun x hx => by
    simp only [hρ']; rw [hx]; exact Real.sq_sqrt (h0 x)
  have hsq : (fun x => Real.sqrt (ρ' x)) = v := funext fun x => Real.sqrt_sq (hv0 x)
  have hH' : MemH1 (haar 1) (fun x => Real.sqrt (ρ' x)) := by
    rw [hsq]
    exact appA_memH1_congr_ae (hvae.symm) hH
  have h0' : ∀ x, 0 ≤ ρ' x := fun x => sq_nonneg _
  have h1' : ∫ x, ρ' x ∂haar 1 = 1 := by rw [integral_congr_ae hae]; exact h1
  have hG' : GR C ρ' = GR C ρ := GR_congr_ae hae
  have hadm' : Admissible zeroV (attrW C) ρ' :=
    (admissible_iff hC hmin).2 ⟨h0', h1', hH', by rw [hG']; exact hg⟩
  refine ⟨ρ', hvc.pow 2, hadm', ?_, ?_⟩
  · rw [diss_eq hC h0' h1' hH', diss_eq hC h0 h1 hH, DR_congr_ae hae.symm hH]
  · rw [gap_eq hC hmin h0' h1' hH', gap_eq hC hmin h0 h1 hH, hG']

/-- A minimizing sequence of continuous admissible densities for `r_*`. -/
theorem exists_min_seq {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) :
    ∃ ρ : ℕ → Torus 1 → ℝ, (∀ n, Continuous (ρ n)) ∧ (∀ n, Admissible zeroV (attrW C) (ρ n)) ∧
      Tendsto (fun n => dissipation zeroV (attrW C) (ρ n) /
        (2 * (gap zeroV (attrW C) (densMeasure (ρ n))).toENNReal)) atTop
        (𝓝 (rStar zeroV (attrW C))) := by
  obtain ⟨KV, KW, hyp⟩ := Ex.hyp_attr_proved hC
  obtain ⟨ρ0, hρ0⟩ := admissible_nonempty (d := 1) (le_refl 1) hyp
  let F : {ρ : Torus 1 → ℝ // Admissible zeroV (attrW C) ρ} → ℝ≥0∞ := fun ρ =>
    dissipation zeroV (attrW C) ρ.1 / (2 * (gap zeroV (attrW C) (densMeasure ρ.1)).toENNReal)
  have hS : (Set.range F).Nonempty := ⟨F ⟨ρ0, hρ0⟩, ⟨_, rfl⟩⟩
  obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sInf hS (OrderBot.bddBelow _)
  have hr : rStar zeroV (attrW C) = sInf (Set.range F) := by
    rw [sInf_range]; unfold rStar; exact iInf_subtype'
  choose ρ hρ using hmem
  choose ρ' hc hadm hd hg using fun n => exists_cont_adm hC hmin (ρ n).2
  refine ⟨ρ', hc, hadm, ?_⟩
  rw [hr]
  refine hu.congr fun n => ?_
  have := hρ n
  rw [← this]
  simp only [F]
  rw [hd, hg]

theorem weakEL_regularity_smooth_of_weakGrad {r : ℝ} (hr : 0 ≤ r) {A : Torus 1 → ℝ}
    (hA : IsSmoothT A) {f : Torus 1 → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf : MemH1 (haar 1) f)
    (hf1 : ∫ x, f x ^ 2 ∂haar 1 = 1) {η : ℝ}
    (hweak : ∀ φ : Torus 1 → ℝ, IsSmoothT φ →
      ∫ x, (4 * weakGrad f x 0 * weakGrad φ x 0 + A x * f x * φ x -
        4 * r * f x * Real.log (f x) * φ x) ∂haar 1 = η * ∫ x, f x * φ x ∂haar 1) :
    ∃ g : Torus 1 → ℝ, g =ᵐ[haar 1] f ∧ IsSmoothT g ∧ (∀ x, 0 < g x) := by
  obtain ⟨g, hg, hgs, hgp, -⟩ := weakEL_regularity_ae_smooth hr hA hf0 hf hf1 (η := η)
    (fun φ hφ => by
      have hφw : weakGrad φ =ᵐ[haar 1] fun y _ => dpart_appA φ 0 y :=
        weakGrad_ae_eq (Reg.isWeakGrad_smooth_zero hφ)
      rw [← hweak φ hφ]
      refine integral_congr_ae ?_
      filter_upwards [hφw] with x hx
      rw [congrFun hx 0])
  exact ⟨g, hg, hgs, hgp⟩


theorem mu_ge {C : Torus 1 → ℝ} {δ : ℝ} (hδ : 0 < δ) (hsup : ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ)
    (n : ℕ) : aCos * δ ≤ aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat C ((n : ℤ) + 1)) := by
  have ha : 0 < aCos := by unfold aCos; positivity
  have h := hsup ((n : ℤ) + 1) (by omega)
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    nlinarith
  have h2 : δ ≤ 1 - chat C ((n : ℤ) + 1) := by linarith
  calc aCos * δ ≤ aCos * 1 * δ := by simp
    _ ≤ aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat C ((n : ℤ) + 1)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 ha.le) h2 hδ.le (by positivity)

/-- Lemma 9.9, parts (i) and (ii). -/
theorem scalar_quotient_attainment {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re ≤ 1 - δ)
    (huniq : HaarUniqueMinimizer (attrW C))
    (hzero : ∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      dissipation zeroV (attrW C) ρ = 0 → ρ =ᵐ[haar 1] fun _ => 1) :
    0 < rStar zeroV (attrW C) ∧
      (∀ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ),
          IsRefEigenbasis (haar 1) e lam → IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm →
          rStar zeroV (attrW C) < lamG (lamShift lam) Cm →
        ∃ ρ : Torus 1 → ℝ, IsSmoothT ρ ∧ (∀ x, 0 < ρ x) ∧ ∫ x, ρ x ∂haar 1 = 1 ∧
          ¬ (ρ =ᵐ[haar 1] fun _ => 1) ∧ 0 < gap zeroV (attrW C) (densMeasure ρ) ∧
          dissipation zeroV (attrW C) ρ =
            2 * rStar zeroV (attrW C) * (gap zeroV (attrW C) (densMeasure ρ)).toENNReal) := by
  have hmin0 := huniq.1
  have hsup' : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ := hsup
  obtain ⟨δ, hδ, hδs⟩ := hsup'
  obtain ⟨ρs, hc, hadm, hmt⟩ := exists_min_seq hC hmin0
  obtain ⟨φ, f, hφ, hfc, hf0, hf1, hfH, hunif, hweak, hcase⟩ :=
    scalar_quotient_minimizing_sequence hC hCpos hsup huniq hzero ρs hadm hc hmt
  have hf2 : ∀ x, 0 ≤ f x ^ 2 := fun x => sq_nonneg _
  have hrfin := rStar_ne_top hC hmin0
  set r0 : ℝ := (rStar zeroV (attrW C)).toReal with hr0def
  have hrr : rStar zeroV (attrW C) = ENNReal.ofReal r0 := (ENNReal.ofReal_toReal hrfin).symm
  have hr0 : 0 ≤ r0 := ENNReal.toReal_nonneg
  obtain ⟨e0, lam0, Cm0, he0, hCm0⟩ := exists_ref_data hC hmin0 (Ex.hyp_attr_proved hC) ⟨δ, hδ, hδs⟩
  have hlam0 : ENNReal.ofReal (aCos * δ) ≤ lamG (lamShift lam0) Cm0 := by
    rw [lamG_formula hC hmin0 (Ex.hyp_attr_proved hC) ⟨δ, hδ, hδs⟩ e0 lam0 Cm0 he0 hCm0]
    exact le_iInf fun n => ENNReal.ofReal_le_ofReal (mu_ge hδ hδs n)
  have hapos : 0 < aCos * δ := by unfold aCos; positivity
  refine ⟨?_, ?_⟩
  · rcases hcase with ⟨hadmf, hdiss⟩ | ⟨-, hlam⟩
    · by_contra hneg
      have hz : rStar zeroV (attrW C) = 0 := le_antisymm (not_lt.1 hneg) (by simp)
      rw [hz] at hdiss
      simp only [mul_zero, zero_mul] at hdiss
      obtain ⟨-, h1, hH, hG⟩ := (admissible_iff hC hmin0).1 hadmf
      have hae := hzero _ hf2 h1 hdiss
      have := GR_congr_ae (C := C) hae
      rw [GR_one hC] at this
      linarith
    · calc 0 < ENNReal.ofReal (aCos * δ) := ENNReal.ofReal_pos.2 hapos
        _ ≤ lamG (lamShift lam0) Cm0 := hlam0
        _ ≤ _ := hlam e0 lam0 Cm0 he0 hCm0
  · intro e lam Cm he hCm hlt
    rcases hcase with ⟨hadmf, hdiss⟩ | ⟨-, hlam⟩
    swap
    · exact absurd (hlam e lam Cm he hCm) (not_le.2 hlt)
    obtain ⟨-, h1, hH2, hG⟩ := (admissible_iff hC hmin0).1 hadmf
    have hDReq : DR C (fun x => f x ^ 2) = 2 * r0 * GR C (fun x => f x ^ 2) := by
      rw [diss_eq hC hf2 h1 hH2, gap_eq hC hmin0 hf2 h1 hH2, EReal.real_coe_toENNReal, hrr,
        ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)] at hdiss
      exact (ENNReal.ofReal_eq_ofReal_iff (DR_nonneg _ _) (by positivity)).1 hdiss
    have hlow : ∀ σ : Torus 1 → ℝ, (∀ x, 0 ≤ σ x) → ∫ x, σ x ∂haar 1 = 1 →
        MemH1 (haar 1) (fun x => Real.sqrt (σ x)) → 0 < GR C σ → 2 * r0 * GR C σ ≤ DR C σ := by
      intro σ h0 h1σ hHσ hGσ
      have hadmσ : Admissible zeroV (attrW C) σ := (admissible_iff hC hmin0).2 ⟨h0, h1σ, hHσ, hGσ⟩
      have hle : rStar zeroV (attrW C) ≤ dissipation zeroV (attrW C) σ /
          (2 * (gap zeroV (attrW C) (densMeasure σ)).toENNReal) := iInf₂_le _ hadmσ
      rw [quot_real hC hmin0 hadmσ, hrr, ENNReal.ofReal_le_ofReal_iff
        (div_nonneg (DR_nonneg _ _) (by positivity)), le_div_iff₀ (by positivity)] at hle
      linarith
    obtain ⟨η, hη⟩ := weak_EL_of_critical hC hr0 hf0 hfc hfH hf1 hG hDReq.le hlow
    have hA : IsSmoothT (Apot C r0 (fun y => f y ^ 2)) :=
      isSmoothT_Apot hC r0 hf2 h1 (hfc.pow 2).measurable
    obtain ⟨g, hgae, hgs, hgp⟩ := weakEL_regularity_smooth_of_weakGrad hr0 hA hf0 hfH hf1 hη
    set ρ : Torus 1 → ℝ := fun x => g x ^ 2 with hρdef
    have hρae : ρ =ᵐ[haar 1] fun x => f x ^ 2 := hgae.mono fun x hx => by simp only [hρdef, hx]
    have hρs : IsSmoothT ρ := by
      rw [isSmoothT_iff_lift1] at hgs ⊢
      exact hgs.pow 2
    have hρ0 : ∀ x, 0 ≤ ρ x := fun x => sq_nonneg _
    have hρ1 : ∫ x, ρ x ∂haar 1 = 1 := by rw [integral_congr_ae hρae]; exact h1
    have hsq : (fun x => Real.sqrt (ρ x)) = g := funext fun x => Real.sqrt_sq (hgp x).le
    have hHρ : MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) := by
      rw [hsq]; exact memH1_of_contDiff hgs
    have hmeas : densMeasure ρ = densMeasure (fun x => f x ^ 2) := densMeasure_congr_ae hρae
    refine ⟨ρ, hρs, fun x => pow_pos (hgp x) 2, hρ1, ?_, ?_, ?_⟩
    · intro hone
      have := GR_congr_ae (C := C) (hρae.symm.trans hone)
      rw [GR_one hC] at this
      linarith
    · rw [hmeas, gap_eq hC hmin0 hf2 h1 hH2]
      exact_mod_cast hG
    · rw [diss_eq hC hρ0 hρ1 hHρ, ← DR_congr_ae hρae.symm hH2, ← diss_eq hC hf2 h1 hH2]
      rw [hmeas]; exact hdiss


end SharpLSI.FL.Ex.LaneD
