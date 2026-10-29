import FullLabeledLSI.Defs.F07_Sanity
import FullLabeledLSI.Paper.Sec3RecFinal
import FullLabeledLSI.Paper.Sec3RecoveryReg
import FullLabeledLSI.Paper.Sec3Entropy
import FullLabeledLSI.Statements.S08_Prop_3_2
import FullLabeledLSI.Statements.S09_Prop_3_3
import FullLabeledLSI.Statements.S10_Prop_3_4
import SharpSymmetricLSI.Statements.R02_Prop_2_1
import SharpSymmetricLSI.Paper.R37Particle
import SharpSymmetricLSI.Paper.AppAEvol1

/-!
# Proposition 2.1: assembly (FL, Section 3.1 / Section 4)

* `rAll_le_fisher_div`: `r_N^all ≤ I(ν|P_N) / (2 H(ν|P_N))` for a probability `ν` of finite
  positive entropy (the test function is `√(dν/dP_N)`; no symmetry is used).
* `rMs_le_rStar`: `r_ms ≤ r_*` from one-group families.
* `limsup_rAll_le_rMs`: `limsup r_N^all ≤ r_ms` from the product recovery of Proposition 3.2.
* `rMs_pos_le_rLS_aux`: `0 < r_ms ≤ r_LS(μ)` from Propositions 3.3 and 3.4.
* `rMs_eq_smooth_inf_aux`: the infimum over smooth strictly positive families, from the
  componentwise regularization `family_regularization` (groups of weight zero are removed).
-/

noncomputable section
open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem div_div_nat_cancel (I K : ℝ≥0∞) {N : ℕ} (hN0 : (N : ℝ≥0∞) ≠ 0) (hNt : (N : ℝ≥0∞) ≠ ⊤) :
    I / (2 * K) = (I / N) / (2 * (K / N)) := by
  have e : 2 * (K / (N : ℝ≥0∞)) = (2 * K) * (N : ℝ≥0∞)⁻¹ := by
    rw [div_eq_mul_inv, mul_assoc]
  rw [e, div_eq_mul_inv I (N : ℝ≥0∞)]
  exact (ENNReal.mul_div_mul_right _ _ (ENNReal.inv_ne_zero.2 hNt)
    (ENNReal.inv_ne_top.2 hN0)).symm

/-- `r_N^all ≤ I(ν|P_N)/(2H(ν|P_N))` when `0 < H(ν|P_N) < ⊤`. -/
theorem rAll_le_fisher_div (hyp : Hyp V W KV KW) {N : ℕ} {ν : Measure (Config N d)}
    [IsProbabilityMeasure ν] (hK0 : 0 < klDiv ν (gibbs V W N))
    (hKt : klDiv ν (gibbs V W N) ≠ ⊤) :
    rAll V W N ≤ fisherInfoC ν (gibbs V W N) / (2 * klDiv ν (gibbs V W N)) := by
  have : IsProbabilityMeasure (gibbs V W N) := gibbs_isProbabilityMeasure hyp N
  have hac : ν ≪ gibbs V W N := (klDiv_ne_top_iff.1 hKt).1
  have hent : ent (gibbs V W N) (fun X => sqrtDens ν (gibbs V W N) X ^ 2) =
      klDiv ν (gibbs V W N) := (klDiv_eq_ent hac).symm
  have hF := fisherInfoC_eq hyp hac
  by_cases hm : MemH1C (gibbs V W N) (sqrtDens ν (gibbs V W N))
  · rw [if_pos hm] at hF
    have hle : rAll V W N ≤ 2 * energy V W N (sqrtDens ν (gibbs V W N)) /
        ent (gibbs V W N) (fun X => sqrtDens ν (gibbs V W N) X ^ 2) :=
      iInf₂_le (f := fun (f : Config N d → ℝ) _ => 2 * energy V W N f /
        ent (gibbs V W N) (fun X => f X ^ 2)) (sqrtDens ν (gibbs V W N))
        ⟨hm, by rw [hent]; exact hK0⟩
    refine hle.trans (le_of_eq ?_)
    rw [hent, hF, show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_assoc (2 : ℝ≥0∞) 2,
      ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
  · rw [if_neg hm] at hF
    rw [hF, ENNReal.top_div_of_ne_top (ENNReal.mul_ne_top (by norm_num) hKt)]
    exact le_top

/-- `r_ms ≤ r_*`: one-group families. -/
theorem rMs_le_rStar : rMs V W ≤ rStar V W := by
  refine le_iInf₂ fun ρ hρ => ?_
  have h := iInf₂_le (f := fun (F : Family d) (_ : F ∈ {F : Family d | MsAdmissible V W F}) =>
    msDiss V W F / (2 * (msGap V W F).toENNReal)) (Family.single ρ)
    ((msAdmissible_single_iff V W ρ).2 hρ)
  rw [msDiss_single, msGap_single] at h
  exact h

/-- `limsup r_N^all ≤ r_ms`. -/
theorem limsup_rAll_le_rMs (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    limsup (fun N => rAll V W N) atTop ≤ rMs V W := by
  refine le_iInf₂ fun F hF => ?_
  obtain ⟨dens, hdens, hKL, hFI⟩ := product_recovery hd hyp F hF
  obtain ⟨hGt, -, hDt⟩ := msGap_msDiss_lt_top hd hyp hF.1
  set G := (msGap V W F).toENNReal with hGdef
  set D := msDiss V W F with hDdef
  have hG0 : G ≠ 0 := (EReal.toENNReal_pos_iff.2 hF.2).ne'
  have hGt' : G ≠ ⊤ := by
    rw [hGdef]; intro hc
    exact absurd (EReal.toENNReal_eq_top_iff.1 hc) hGt.ne
  have hprob : ∀ N, IsProbabilityMeasure (Measure.pi fun i : Fin N => densMeasure (dens N i)) := by
    intro N
    haveI : ∀ i, IsProbabilityMeasure (densMeasure (dens N i)) := fun i =>
      isProbabilityMeasure_densMeasure' (hdens N i).2.1 (hdens N i).2.2
    infer_instance
  set ν : (N : ℕ) → Measure (Config N d) := fun N =>
    Measure.pi fun i : Fin N => densMeasure (dens N i) with hν
  set u : ℕ → ℝ≥0∞ := fun N => (fisherInfoC (ν N) (gibbs V W N) / N) /
    (2 * (klDiv (ν N) (gibbs V W N) / N)) with hu
  have hulim : Tendsto u atTop (𝓝 (D / (2 * G))) := by
    refine ENNReal.Tendsto.div hFI (Or.inr (by simp [hG0])) (ENNReal.Tendsto.const_mul hKL
      (Or.inr (by norm_num))) (Or.inl (ENNReal.mul_ne_top (by norm_num) hGt'))
  have hle : ∀ᶠ N in atTop, rAll V W N ≤ u N := by
    have h1 : ∀ᶠ N : ℕ in atTop, 0 < klDiv (ν N) (gibbs V W N) / N :=
      hKL.eventually (lt_mem_nhds (pos_iff_ne_zero.2 hG0))
    have h2 : ∀ᶠ N : ℕ in atTop, klDiv (ν N) (gibbs V W N) / N < ⊤ :=
      hKL.eventually (gt_mem_nhds (lt_top_iff_ne_top.2 hGt'))
    filter_upwards [h1, h2, eventually_ge_atTop 1] with N hN1 hN2 hN
    have hNne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    have hNt : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
    have hKne : klDiv (ν N) (gibbs V W N) ≠ ⊤ := by
      intro hc
      rw [hc, ENNReal.top_div_of_ne_top hNt] at hN2
      exact lt_irrefl _ hN2
    have hK0 : 0 < klDiv (ν N) (gibbs V W N) := by
      rcases eq_or_ne (klDiv (ν N) (gibbs V W N)) 0 with h | h
      · rw [h, ENNReal.zero_div] at hN1; exact absurd hN1 (lt_irrefl _)
      · exact pos_iff_ne_zero.2 h
    haveI := hprob N
    refine (rAll_le_fisher_div hyp hK0 hKne).trans (le_of_eq ?_)
    exact div_div_nat_cancel _ _ hNne hNt
  calc limsup (fun N => rAll V W N) atTop ≤ limsup u atTop := limsup_le_limsup hle
    _ = D / (2 * G) := hulim.limsup_eq

/-! ### Positivity and the equilibrium bound -/

theorem exists_grad1W_bound (hyp : Hyp V W KV KW) :
    ∃ B : ℝ, ∀ᵐ X ∂(volume : Measure (Config 2 d)),
      sqNorm (fun k => grad1W W (X 0) (X 1) k) ≤ B ^ 2 := by
  have hne := (memLp_top_sqrt_sqNorm_grad1W hyp).eLpNorm_lt_top.ne
  refine ⟨(eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤
    volume).toReal, ?_⟩
  filter_upwards [ae_le_of_eLpNorm_top hne] with X hX
  rw [abs_of_nonneg (Real.sqrt_nonneg _)] at hX
  calc sqNorm (fun k => grad1W W (X 0) (X 1) k)
      = Real.sqrt (sqNorm (grad1W W (X 0) (X 1))) ^ 2 := by
        rw [Real.sq_sqrt (sqNorm_nonneg _)]
    _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hX 2

theorem rMs_pos_le_rLS_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ) :
    0 < rMs V W ∧ rMs V W ≤ rLS (μ : Measure (Torus d)) := by
  obtain ⟨-, hall⟩ := prop_equilibrium hd hyp hr
  obtain ⟨p, -, -, σ, -, c, hc, hc1, -, hcoer⟩ := hall μ hμ
  obtain ⟨B, hB⟩ := exists_grad1W_bound hyp
  refine ⟨(rMs_lower_bound hd hyp hr μ hμ c hc hc1 hcoer B hB).1, ?_⟩
  rw [← equilibrium_families hd hyp hr μ hμ]
  refine le_iInf₂ fun F hF => ?_
  exact iInf₂_le (f := fun (F : Family d) (_ : F ∈ {F : Family d | MsAdmissible V W F}) =>
    msDiss V W F / (2 * (msGap V W F).toENNReal)) F hF.1

/-! ### Smooth strictly positive families -/

/-- The family obtained by deleting the groups of weight zero. -/
def posFamily (G : Family d) : Family d :=
  open Classical in
  ⟨(Finset.univ.filter (fun s : Fin G.q => 0 < G.θ s)).card,
    fun a => G.θ ((Finset.univ.filter (fun s : Fin G.q => 0 < G.θ s)).equivFin.symm a),
    fun a => G.ρ ((Finset.univ.filter (fun s : Fin G.q => 0 < G.θ s)).equivFin.symm a)⟩

open Classical in
theorem sum_posFamily {M : Type*} [AddCommMonoid M] (G : Family d) (φ : Fin G.q → M)
    (hφ : ∀ s, ¬ 0 < G.θ s → φ s = 0) :
    ∑ a : Fin (posFamily G).q,
      φ ((Finset.univ.filter (fun s : Fin G.q => 0 < G.θ s)).equivFin.symm a) = ∑ s, φ s := by
  set S := Finset.univ.filter (fun s : Fin G.q => 0 < G.θ s) with hS
  have h1 : ∑ a : Fin S.card, φ (S.equivFin.symm a) = ∑ s : S, φ s :=
    Equiv.sum_comp S.equivFin.symm (fun s : S => φ s)
  have h2 : ∑ s : S, φ s = ∑ s ∈ S, φ s := Finset.sum_coe_sort S φ
  have h3 : ∑ s ∈ S, φ s = ∑ s, φ s := by
    refine Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hφ s ?_
    intro h; exact hs (by simp [hS, h])
  exact h1.trans (h2.trans h3)

theorem posFamily_props {G : Family d} (hθ0 : ∀ s, 0 ≤ G.θ s) (hθ1 : ∑ s, G.θ s = 1) :
    (∀ a, 0 < (posFamily G).θ a) ∧ ∑ a, (posFamily G).θ a = 1 ∧
      (∀ a, ∃ s, (posFamily G).ρ a = G.ρ s) ∧
      (posFamily G).bar = G.bar ∧
      (∀ V W, msGap V W (posFamily G) = msGap V W G) ∧
      (∀ V W, msDiss V W (posFamily G) = msDiss V W G) := by
  classical
  have hz : ∀ s, ¬ 0 < G.θ s → G.θ s = 0 := fun s h => le_antisymm (not_lt.1 h) (hθ0 s)
  have hbar : (posFamily G).bar = G.bar := by
    funext x
    unfold Family.bar
    exact sum_posFamily G (fun s => G.θ s * G.ρ s x) fun s h => by simp [hz s h]
  refine ⟨fun a => ?_, ?_, fun a => ⟨_, rfl⟩, hbar, fun V W => ?_, fun V W => ?_⟩
  · exact (Finset.mem_filter.1 ((Finset.univ.filter (fun s : Fin G.q => 0 < G.θ s)).equivFin.symm
      a).2).2
  · exact (sum_posFamily G (fun s => G.θ s) fun s h => hz s h).trans hθ1
  · unfold msGap
    rw [hbar]
    congr 3
    exact sum_posFamily G (fun s => ENNReal.ofReal (G.θ s) * klDiv (densMeasure (G.ρ s)) (haar d))
      fun s h => by simp [hz s h]
  · unfold msDiss
    rw [hbar]
    exact sum_posFamily G (fun s => ENNReal.ofReal (G.θ s) * speciesDiss V W (G.ρ s) G.bar)
      fun s h => by simp [hz s h]

theorem rMs_eq_smooth_inf_aux (hd : 1 ≤ d) (hyp : Hyp V W KV KW) :
    rMs V W = ⨅ F ∈ {F : Family d | MsAdmissible V W F ∧
        ∀ a, IsSmoothT (F.ρ a) ∧ ∀ x, 0 < F.ρ a x},
      msDiss V W F / (2 * (msGap V W F).toENNReal) := by
  refine le_antisymm (le_iInf₂ fun F hF => iInf₂_le (f := fun (F : Family d)
    (_ : F ∈ {F : Family d | MsAdmissible V W F}) =>
      msDiss V W F / (2 * (msGap V W F).toENNReal)) F hF.1) ?_
  refine le_iInf₂ fun F hF => ?_
  obtain ⟨hAd, hpos⟩ := hF
  obtain ⟨hGt, -, hDt⟩ := msGap_msDiss_lt_top hd hyp hAd
  obtain ⟨Fs, hFs, hG, hD⟩ := family_regularization hyp F hAd
  set G := (msGap V W F).toENNReal with hGdef
  have hG0 : G ≠ 0 := (EReal.toENNReal_pos_iff.2 hpos).ne'
  have hGt' : G ≠ ⊤ := by
    rw [hGdef]; intro hc
    exact absurd (EReal.toENNReal_eq_top_iff.1 hc) hGt.ne
  have hlim : Tendsto (fun n => msDiss V W (Fs n) / (2 * (msGap V W (Fs n)).toENNReal)) atTop
      (𝓝 (msDiss V W F / (2 * G))) :=
    ENNReal.Tendsto.div hD (Or.inr (by simp [hG0])) (ENNReal.Tendsto.const_mul hG
      (Or.inr (by norm_num))) (Or.inl (ENNReal.mul_ne_top (by norm_num) hGt'))
  have hev : ∀ᶠ n in atTop, 0 < (msGap V W (Fs n)).toENNReal :=
    hG.eventually (lt_mem_nhds (pos_iff_ne_zero.2 hG0))
  refine ge_of_tendsto hlim ?_
  filter_upwards [hev] with n hn
  obtain ⟨hθ0, hθ1, hρ⟩ := hFs n
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := posFamily_props hθ0 hθ1
  have hsm : ∀ a, IsSmoothT ((posFamily (Fs n)).ρ a) ∧ ∀ x, 0 < (posFamily (Fs n)).ρ a x := by
    intro a
    obtain ⟨s, hs⟩ := hp3 a
    rw [hs]; exact ⟨(hρ s).1, (hρ s).2.1⟩
  have hAdm : (posFamily (Fs n)).Admissible := by
    refine ⟨hp1, hp2, fun a => ?_⟩
    obtain ⟨s, hs⟩ := hp3 a
    rw [hs]
    refine ⟨fun x => ((hρ s).2.1 x).le, (hρ s).2.2, ?_⟩
    exact SharpLSI.memH1_of_contDiff (ContDiff.sqrt (hρ s).1 fun z => ((hρ s).2.1 _).ne')
  have hgap : 0 < msGap V W (posFamily (Fs n)) := by
    rw [hp5]; exact EReal.toENNReal_pos_iff.1 hn
  have := iInf₂_le (f := fun (F : Family d) (_ : F ∈ {F : Family d | MsAdmissible V W F ∧
      ∀ a, IsSmoothT (F.ρ a) ∧ ∀ x, 0 < F.ρ a x}) =>
      msDiss V W F / (2 * (msGap V W F).toENNReal)) (posFamily (Fs n)) ⟨⟨hAdm, hgap⟩, hsm⟩
  rw [hp5, hp6] at this
  exact this

end SharpLSI.FL
