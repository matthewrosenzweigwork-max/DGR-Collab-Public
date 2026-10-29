import FullLabeledLSI.Examples.E01g7_LamG
import FullLabeledLSI.Examples.E01g3_Limit
import FullLabeledLSI.Examples.E01g2_Compact
import FullLabeledLSI.Examples.E01b_LaneA

/-!
# Lane D, Task C (E01g8): Lemma 9.9, middle sentence (`scalar_quotient_minimizing_sequence`)
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-- `r_*` is finite. -/
theorem rStar_ne_top {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) :
    rStar zeroV (attrW C) ≠ ⊤ := by
  obtain ⟨KV, KW, hyp⟩ := Ex.hyp_attr_proved hC
  obtain ⟨ρ0, hρ0⟩ := admissible_nonempty (d := 1) (le_refl 1) hyp
  have h1 := (gap_lt_top_of_admissible hyp hρ0).2
  have h2 : rStar zeroV (attrW C) ≤
      dissipation zeroV (attrW C) ρ0 / (2 * (gap zeroV (attrW C) (densMeasure ρ0)).toENNReal) :=
    iInf₂_le ρ0 hρ0
  refine ne_top_of_le_ne_top ?_ h2
  refine ENNReal.div_ne_top h1.ne ?_
  obtain ⟨h0, h1', hH, hg⟩ := (admissible_iff hC hmin).1 hρ0
  rw [gap_eq hC hmin h0 h1' hH, EReal.real_coe_toENNReal]
  have : ENNReal.ofReal (GR C ρ0) ≠ 0 := (ENNReal.ofReal_pos.2 hg).ne'
  simpa using this

theorem scalar_quotient_minimizing_sequence {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re ≤ 1 - δ)
    (huniq : HaarUniqueMinimizer (attrW C))
    (hzero : ∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      dissipation zeroV (attrW C) ρ = 0 → ρ =ᵐ[haar 1] fun _ => 1)
    (ρ : ℕ → Torus 1 → ℝ) (hρ : ∀ n, SharpLSI.Admissible zeroV (attrW C) (ρ n))
    (hρc : ∀ n, Continuous (ρ n))
    (hmin : Tendsto (fun n => dissipation zeroV (attrW C) (ρ n) /
      (2 * (gap zeroV (attrW C) (densMeasure (ρ n))).toENNReal)) atTop (𝓝 (rStar zeroV (attrW C)))) :
    ∃ (φ : ℕ → ℕ) (f : Torus 1 → ℝ), StrictMono φ ∧ Continuous f ∧ (∀ x, 0 ≤ f x) ∧
      ∫ x, f x ^ 2 ∂haar 1 = 1 ∧ MemH1 (haar 1) f ∧
      TendstoUniformly (fun n x => Real.sqrt (ρ (φ n) x)) f atTop ∧
      (∀ g : Torus 1 → ℝ, MemH1 (haar 1) g →
        Tendsto (fun n => ∫ x, Real.sqrt (ρ (φ n) x) * g x ∂haar 1 +
            ∫ x, weakGrad (fun y => Real.sqrt (ρ (φ n) y)) x 0 * weakGrad g x 0 ∂haar 1) atTop
          (𝓝 (∫ x, f x * g x ∂haar 1 + ∫ x, weakGrad f x 0 * weakGrad g x 0 ∂haar 1))) ∧
      ((SharpLSI.Admissible zeroV (attrW C) (fun x => f x ^ 2) ∧
          dissipation zeroV (attrW C) (fun x => f x ^ 2) =
            2 * rStar zeroV (attrW C) *
              (gap zeroV (attrW C) (densMeasure (fun x => f x ^ 2))).toENNReal) ∨
        ((∀ x, f x = 1) ∧
          ∀ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ),
            IsRefEigenbasis (haar 1) e lam → IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm →
              lamG (lamShift lam) Cm ≤ rStar zeroV (attrW C))) := by
  have hmin0 := huniq.1
  have hCpos' : ∀ n : ℤ, n ≠ 0 → 0 ≤ chat C n := hCpos
  have hsup' : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ := hsup
  have hadm : ∀ n, (∀ x, 0 ≤ ρ n x) ∧ ∫ x, ρ n x ∂haar 1 = 1 ∧
      MemH1 (haar 1) (fun x => Real.sqrt (ρ n x)) ∧ 0 < GR C (ρ n) :=
    fun n => (admissible_iff hC hmin0).1 (hρ n)
  set q : ℕ → ℝ := fun n => DR C (ρ n) / (2 * GR C (ρ n)) with hq
  have hqn : ∀ n, 0 ≤ q n := fun n =>
    div_nonneg (DR_nonneg _ _) (by have := (hadm n).2.2.2; positivity)
  have hquot : ∀ n, dissipation zeroV (attrW C) (ρ n) /
      (2 * (gap zeroV (attrW C) (densMeasure (ρ n))).toENNReal) = ENNReal.ofReal (q n) :=
    fun n => quot_real hC hmin0 (hρ n)
  set r0 : ℝ := (rStar zeroV (attrW C)).toReal with hr0def
  have hrfin := rStar_ne_top hC hmin0
  have hrr : rStar zeroV (attrW C) = ENNReal.ofReal r0 := (ENNReal.ofReal_toReal hrfin).symm
  have hr0 : 0 ≤ r0 := ENNReal.toReal_nonneg
  have hqt : Tendsto q atTop (𝓝 r0) := by
    have := (ENNReal.tendsto_toReal hrfin).comp hmin
    refine this.congr fun n => ?_
    simp [Function.comp, hquot n, ENNReal.toReal_ofReal (hqn n)]
  -- a priori bound along the tail
  obtain ⟨B, hB⟩ := apriori hC hCpos' (L := r0 + 1) (by linarith)
  obtain ⟨N0, hN0⟩ : ∃ N0, ∀ n ≥ N0, q n ≤ r0 + 1 :=
    eventually_atTop.1 ((hqt.eventually (gt_mem_nhds (by linarith : r0 < r0 + 1))).mono fun n hn => hn.le)
  have hIR : ∀ n, IR (ρ (n + N0)) ≤ B := fun n => hB _ (hadm _).1 (hadm _).2.1 (hadm _).2.2.1 (by
    have h1 := hN0 (n + N0) (by omega)
    have hG := (hadm (n + N0)).2.2.2
    simp only [hq] at h1
    rw [div_le_iff₀ (by positivity)] at h1
    linarith)
  set u : ℕ → Torus 1 → ℝ := fun n x => Real.sqrt (ρ (n + N0) x) with hu
  have hD : ∀ n, ∫ x, weakGrad (u n) x 0 ^ 2 ∂haar 1 ≤ B / 4 := fun n => by
    have := hIR n
    unfold IR at this
    simp only [hu]
    linarith
  have hu1 : ∀ n, ∫ x, u n x ^ 2 ∂haar 1 = 1 := fun n => by
    simp only [hu]
    simp_rw [Real.sq_sqrt ((hadm _).1 _)]
    exact (hadm _).2.1
  obtain ⟨φ0, f, L, hφ0, hfc, hf0, hf1, hfH, hunif, hweakL2, hweakH1, hLim, hLle⟩ :=
    h1_unif_compact (u := u) (D := B / 4) (fun n => Real.continuous_sqrt.comp (hρc _))
      (fun n x => Real.sqrt_nonneg _) (fun n => (hadm _).2.2.1) hu1 hD
  -- the limit density
  set ρ'' : ℕ → Torus 1 → ℝ := fun n => ρ (φ0 n + N0) with hρ''
  have hu_eq : ∀ n x, ρ'' n x = u (φ0 n) x ^ 2 := fun n x =>
    (Real.sq_sqrt ((hadm (φ0 n + N0)).1 x)).symm
  have hdc : DensConv ρ'' (fun x => f x ^ 2) ((1 + (B / 4 + 1) / 2) ^ 2) :=
    { nonneg := fun n x => (hadm (φ0 n + N0)).1 x
      mass := fun n => (hadm (φ0 n + N0)).2.1
      bound := fun n x => by
        rw [hu_eq]
        have h := unif_bound (Real.continuous_sqrt.comp (hρc (φ0 n + N0))) (hadm (φ0 n + N0)).2.2.1
          (hu1 (φ0 n)) (hD (φ0 n)) x
        have h' : |u (φ0 n) x| ≤ 1 + (B / 4 + 1) / 2 := h
        calc u (φ0 n) x ^ 2 = |u (φ0 n) x| ^ 2 := (sq_abs _).symm
          _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h' 2
      tendsto := fun x => by
        simp_rw [hu_eq]
        exact (hunif.tendsto_at x).pow 2 }
  have hent := hdc.tendsto_entropy
  have hcq := hdc.tendsto_cqR hC
  have hGt : Tendsto (fun n => GR C (ρ'' n)) atTop (𝓝 (GR C (fun x => f x ^ 2))) := by
    unfold GR; exact hent.sub (hcq.div_const 2)
  have hshift : Tendsto (fun n => φ0 n + N0) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right _ _) hφ0.tendsto_atTop
  have hq'' : Tendsto (fun n => q (φ0 n + N0)) atTop (𝓝 r0) := hqt.comp hshift
  have hDt : Tendsto (fun n => DR C (ρ'' n)) atTop (𝓝 (r0 * (2 * GR C (fun x => f x ^ 2)))) := by
    refine (hq''.mul (hGt.const_mul 2)).congr fun n => ?_
    have hG := (hadm (φ0 n + N0)).2.2.2
    simp only [hq, hρ'']
    field_simp
  have hweak : ∀ g : Torus 1 → ℝ, MemLp g 2 (haar 1) →
      Tendsto (fun n => ∫ x, weakGrad (fun y => Real.sqrt (ρ'' n y)) x 0 * g x ∂haar 1) atTop
        (𝓝 (∫ x, weakGrad f x 0 * g x ∂haar 1)) := fun g hg => hweakL2 g hg
  have hDR := DR_lsc hC hdc hf0 hfH (fun n => (hadm (φ0 n + N0)).2.2.1) hweak hDt
  have hG0 : 0 ≤ GR C (fun x => f x ^ 2) := ge_of_tendsto' hGt fun n => (hadm (φ0 n + N0)).2.2.2.le
  have hf2 : ∀ x, 0 ≤ f x ^ 2 := fun x => sq_nonneg _
  have hsqrt : (fun y => Real.sqrt (f y ^ 2)) = f := funext fun y => Real.sqrt_sq (hf0 y)
  have hH2 : MemH1 (haar 1) (fun x => Real.sqrt (f x ^ 2)) := by rw [hsqrt]; exact hfH
  refine ⟨fun n => φ0 n + N0, f, (fun a b hab => by have := hφ0 hab; show φ0 a + N0 < φ0 b + N0; omega), hfc, hf0, hf1, hfH, hunif, hweakH1, ?_⟩
  by_cases hGpos : 0 < GR C (fun x => f x ^ 2)
  · left
    have hadmf : Admissible zeroV (attrW C) (fun x => f x ^ 2) :=
      (admissible_iff hC hmin0).2 ⟨hf2, hf1, hH2, hGpos⟩
    refine ⟨hadmf, ?_⟩
    have hle : rStar zeroV (attrW C) ≤ dissipation zeroV (attrW C) (fun x => f x ^ 2) /
        (2 * (gap zeroV (attrW C) (densMeasure (fun x => f x ^ 2))).toENNReal) :=
      iInf₂_le _ hadmf
    rw [quot_real hC hmin0 hadmf, hrr, ENNReal.ofReal_le_ofReal_iff
      (div_nonneg (DR_nonneg _ _) (by positivity)), le_div_iff₀ (by positivity)] at hle
    have hDReq : DR C (fun x => f x ^ 2) = r0 * (2 * GR C (fun x => f x ^ 2)) :=
      le_antisymm hDR hle
    rw [diss_eq hC hf2 hf1 hH2, gap_eq hC hmin0 hf2 hf1 hH2, EReal.real_coe_toENNReal, hrr,
      hDReq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp [mul_comm, mul_left_comm, mul_assoc]
  · right
    have hGz : GR C (fun x => f x ^ 2) = 0 := le_antisymm (not_lt.1 hGpos) hG0
    have hae := eq_one_of_GR_zero hC huniq hf2 hf1 hH2 hGz
    have hf_one : f = fun _ => 1 := by
      rw [← Continuous.ae_eq_iff_eq (haar 1) hfc continuous_const]
      filter_upwards [hae] with x hx
      have : f x ^ 2 = 1 := hx
      exact (pow_eq_one_iff_of_nonneg (hf0 x) (by norm_num)).1 this
    refine ⟨fun x => by rw [hf_one], ?_⟩
    intro e lam Cm he hCm
    obtain ⟨δ, hδ, hδs⟩ := hsup'
    have hLam : LamF C ≤ r0 := by
      refine le_of_forall_pos_le_add fun η hη => ?_
      obtain ⟨ε, hε, hnear⟩ := near_uniform hC hCpos' ⟨δ, hδ, hδs⟩ η hη
      have hev : ∀ᶠ n in atTop, ∀ x, |ρ'' n x - 1| ≤ ε := by
        have ht := Metric.tendstoUniformly_iff.1 hunif (min 1 (ε / 3)) (by positivity)
        filter_upwards [ht] with n hn x
        have h1 := hn x
        have hfx : f x = 1 := by rw [hf_one]
        rw [hfx, Real.dist_eq] at h1
        rw [hu_eq]
        set y := u (φ0 n) x
        have hm1 : min 1 (ε / 3) ≤ 1 := min_le_left _ _
        have hm2 : min 1 (ε / 3) ≤ ε / 3 := min_le_right _ _
        have h2 : |1 - y| < min 1 (ε / 3) := h1
        have h3 : |y - 1| < min 1 (ε / 3) := by rwa [abs_sub_comm]
        have h4 : |y + 1| ≤ 3 := by
          have := abs_lt.1 h3; rw [abs_le]; constructor <;> nlinarith
        calc |y ^ 2 - 1| = |y - 1| * |y + 1| := by rw [← abs_mul]; ring_nf
          _ ≤ (ε / 3) * 3 := mul_le_mul (h3.le.trans hm2) h4 (abs_nonneg _) (by positivity)
          _ = ε := by ring
      have hge : ∀ᶠ n in atTop, LamF C - η ≤ q (φ0 n + N0) := hev.mono fun n hn => by
        have h := hnear (ρ'' n) (hdc.nonneg n) (hdc.mass n) (hadm (φ0 n + N0)).2.2.1 hn
        have hG := (hadm (φ0 n + N0)).2.2.2
        show LamF C - η ≤ DR C (ρ (φ0 n + N0)) / (2 * GR C (ρ (φ0 n + N0)))
        rw [le_div_iff₀ (by positivity)]
        linarith
      have := le_of_tendsto_of_tendsto tendsto_const_nhds hq'' hge
      linarith
    have := lamG_le_of_LamF_le hC hmin0 (Ex.hyp_attr_proved hC) ⟨δ, hδ, hδs⟩ e lam Cm he hCm hLam
    rwa [hrr]

end SharpLSI.FL.Ex.LaneD
