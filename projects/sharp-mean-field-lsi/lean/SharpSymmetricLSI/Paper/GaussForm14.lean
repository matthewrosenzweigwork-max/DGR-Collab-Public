import SharpSymmetricLSI.Paper.GaussForm13

/-!
# R32 (D3): the parallelogram identity for `ℰ_∞`

`ℰ_∞(f+g) + ℰ_∞(f-g) = 2ℰ_∞(f) + 2ℰ_∞(g)` when `ℰ_∞(f), ℰ_∞(g) < ∞` (`gaussForm_parallelogram`),
for `λ ≥ 0` and any probability measure `γ`. The inequality `≤` uses approximating sequences with
convergent forms and the cutoff lemma to bring `u_n ± v_n` into single cylinders; `≥` follows by
applying `≤` to `f ± g` and scaling.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ContDiff ENNReal NNReal

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)}

/-- A sequence of cylinders converging to `f` whose forms converge to at most `ℰ_∞(f) + δ`. -/
theorem exists_seq_form_tendsto {lam' : ℕ → ℝ} {f : (ℕ → ℝ) → ℝ} (hf : gaussForm lam' γ f < ⊤)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ (u : ℕ → Cyl) (a : ℝ≥0∞),
      Tendsto (fun n => eLpNorm (fun z => (u n).eval z - f z) 2 γ) atTop (𝓝 0) ∧
      Tendsto (fun n => (u n).form lam' γ) atTop (𝓝 a) ∧ a < gaussForm lam' γ f + δ := by
  have hlt : gaussForm lam' γ f < gaussForm lam' γ f + δ := ENNReal.lt_add_right hf.ne hδ.ne'
  obtain ⟨u, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hu, hlt⟩ := iInf_lt_iff.1 hlt
  obtain ⟨x, hx1, hx2⟩ := exists_seq_tendsto_liminf (f := atTop) (u := fun n => (u n).form lam' γ)
  exact ⟨fun n => u (x n), _, hu.comp hx2, hx1, hlt⟩

theorem formG_lt_top [IsProbabilityMeasure γ] (lam' : ℕ → ℝ) {N : ℕ} {G : (Fin N → ℝ) → ℝ}
    {B : ℝ} (hB : ∀ x, ‖fderiv ℝ G x‖ ≤ B) : formG lam' γ N G < ⊤ := by
  unfold formG
  calc ∫⁻ z, ENNReal.ofReal (∑ i : Fin N, lam' i * (fderiv ℝ G (zBlock N z) (Pi.single i 1)) ^ 2) ∂γ
      ≤ ∫⁻ _z, ENNReal.ofReal (∑ i : Fin N, |lam' i| * B ^ 2) ∂γ :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun i _ => by
          have h := abs_pd_le hB i (zBlock N z)
          have : (fderiv ℝ G (zBlock N z) (Pi.single i 1)) ^ 2 ≤ B ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
          exact (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
            (mul_le_mul_of_nonneg_left this (abs_nonneg _)))
    _ < ⊤ := by
        rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem ennreal_liminf_add_le (u v : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n => u n + v n) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat]
  have hm : ∀ w : ℕ → ℝ≥0∞, Monotone fun n => ⨅ i ≥ n, w i := fun w a b hab =>
    le_iInf₂ fun k hk => iInf₂_le k (le_trans hab hk)
  rw [ENNReal.iSup_add_iSup_of_monotone (hm u) (hm v)]
  exact iSup_mono fun n => le_iInf₂ fun k hk => add_le_add (iInf₂_le k hk) (iInf₂_le k hk)

theorem gaussForm_parallelogram_le [IsProbabilityMeasure γ] {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i)
    (f g : (ℕ → ℝ) → ℝ) :
    gaussForm lam' γ (fun z => f z + g z) + gaussForm lam' γ (fun z => f z - g z) ≤
      2 * gaussForm lam' γ f + 2 * gaussForm lam' γ g := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hfin => ?_
  have hf : gaussForm lam' γ f < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt le_self_add hfin).ne two_ne_zero
  have hg : gaussForm lam' γ g < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt le_add_self hfin).ne two_ne_zero
  set δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 4 with hδdef
  have hδ : 0 < δ := ENNReal.div_pos (by simpa using hε.ne') (by norm_num)
  obtain ⟨u, a, hu, hua, ha⟩ := exists_seq_form_tendsto hf hδ
  obtain ⟨v, b, hv, hvb, hb⟩ := exists_seq_form_tendsto hg hδ
  set η : ℕ → ℝ≥0∞ := fun n => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ with hηdef
  have hηpos : ∀ n, 0 < η n := fun n => ENNReal.inv_pos.2 (ENNReal.natCast_ne_top _)
  have hη0 : Tendsto η atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
  have hchoose : ∀ n : ℕ, ∃ m : ℕ,
      eLpNorm (fun z => (cutCyl _ ((u n).contDiff_pm (v n) 1) m).eval z -
        (u n).pm (v n) 1 (zBlock _ z)) 2 γ < η n ∧
      eLpNorm (fun z => (cutCyl _ ((u n).contDiff_pm (v n) (-1)) m).eval z -
        (u n).pm (v n) (-1) (zBlock _ z)) 2 γ < η n ∧
      (cutCyl _ ((u n).contDiff_pm (v n) 1) m).form lam' γ <
        formG lam' γ _ ((u n).pm (v n) 1) + η n ∧
      (cutCyl _ ((u n).contDiff_pm (v n) (-1)) m).form lam' γ <
        formG lam' γ _ ((u n).pm (v n) (-1)) + η n := fun n => by
    obtain ⟨Bp, hBp1, hBp2⟩ := (u n).exists_pm_bounds (v n) 1
    obtain ⟨Bm, hBm1, hBm2⟩ := (u n).exists_pm_bounds (v n) (-1)
    have T1 := tendsto_cutCyl_L2 (γ := γ) ((u n).contDiff_pm (v n) 1) hBp1
    have T2 := tendsto_cutCyl_L2 (γ := γ) ((u n).contDiff_pm (v n) (-1)) hBm1
    have T3 := tendsto_cutCyl_form (γ := γ) ((u n).contDiff_pm (v n) 1) hBp1 hBp2 lam'
    have T4 := tendsto_cutCyl_form (γ := γ) ((u n).contDiff_pm (v n) (-1)) hBm1 hBm2 lam'
    exact ((T1.eventually (gt_mem_nhds (hηpos n))).and ((T2.eventually (gt_mem_nhds (hηpos n))).and
      ((T3.eventually (gt_mem_nhds (ENNReal.lt_add_right (formG_lt_top lam' hBp2).ne
        (hηpos n).ne'))).and (T4.eventually (gt_mem_nhds (ENNReal.lt_add_right
          (formG_lt_top lam' hBm2).ne (hηpos n).ne')))))).exists
  choose m hm using hchoose
  set wp : ℕ → Cyl := fun n => cutCyl _ ((u n).contDiff_pm (v n) 1) (m n)
  set wm : ℕ → Cyl := fun n => cutCyl _ ((u n).contDiff_pm (v n) (-1)) (m n)
  -- `L²` convergence of `wp, wm`
  have hwp : Tendsto (fun n => eLpNorm (fun z => (wp n).eval z - (f z + g z)) 2 γ) atTop (𝓝 0) := by
    have hup := hη0.add (hu.add hv)
    simp only [add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => bot_le)
      fun n => ?_
    have e : (fun z => (wp n).eval z - (f z + g z)) =
        (fun z => (wp n).eval z - (u n).pm (v n) 1 (zBlock _ z)) +
          ((fun z => (u n).eval z - f z) + fun z => (v n).eval z - g z) := by
      funext z; simp only [Pi.add_apply, Cyl.pm_zBlock]; ring
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add (hm n).1.le
      (eLpNorm_add_le (by norm_num)))
  have hwm : Tendsto (fun n => eLpNorm (fun z => (wm n).eval z - (f z - g z)) 2 γ) atTop (𝓝 0) := by
    have hv' : Tendsto (fun n => eLpNorm (fun z => g z - (v n).eval z) 2 γ) atTop (𝓝 0) := by
      refine hv.congr fun n => ?_
      exact eLpNorm_sub_comm (fun z => (v n).eval z) g 2 γ
    have hup := hη0.add (hu.add hv')
    simp only [add_zero] at hup
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => bot_le)
      fun n => ?_
    have e : (fun z => (wm n).eval z - (f z - g z)) =
        (fun z => (wm n).eval z - (u n).pm (v n) (-1) (zBlock _ z)) +
          ((fun z => (u n).eval z - f z) + fun z => g z - (v n).eval z) := by
      funext z; simp only [Pi.add_apply, Cyl.pm_zBlock]; ring
    rw [e]
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add (hm n).2.1.le
      (eLpNorm_add_le (by norm_num)))
  -- the forms
  have hsum : ∀ n, (wp n).form lam' γ + (wm n).form lam' γ ≤
      2 * (u n).form lam' γ + 2 * (v n).form lam' γ + 2 * η n := fun n => by
    have h1 := (hm n).2.2.1.le
    have h2 := (hm n).2.2.2.le
    have h3 := formG_parallelogram (γ := γ) hlam (u n) (v n)
    calc (wp n).form lam' γ + (wm n).form lam' γ
        ≤ (formG lam' γ _ ((u n).pm (v n) 1) + η n) + (formG lam' γ _ ((u n).pm (v n) (-1)) + η n) :=
          add_le_add h1 h2
      _ = (formG lam' γ _ ((u n).pm (v n) 1) + formG lam' γ _ ((u n).pm (v n) (-1))) + 2 * η n := by
          ring
      _ = 2 * (u n).form lam' γ + 2 * (v n).form lam' γ + 2 * η n := by rw [h3]
  have hlim : Tendsto (fun n => 2 * (u n).form lam' γ + 2 * (v n).form lam' γ + 2 * η n) atTop
      (𝓝 (2 * a + 2 * b)) := by
    have := ((ENNReal.Tendsto.const_mul (a := 2) hua (Or.inr ENNReal.ofNat_ne_top)).add
      (ENNReal.Tendsto.const_mul (a := 2) hvb (Or.inr ENNReal.ofNat_ne_top))).add
      (ENNReal.Tendsto.const_mul (a := 2) hη0 (Or.inr ENNReal.ofNat_ne_top))
    simpa using this
  calc gaussForm lam' γ (fun z => f z + g z) + gaussForm lam' γ (fun z => f z - g z)
      ≤ liminf (fun n => (wp n).form lam' γ) atTop + liminf (fun n => (wm n).form lam' γ) atTop :=
        add_le_add (gaussForm_le_liminf wp hwp) (gaussForm_le_liminf wm hwm)
    _ ≤ liminf (fun n => (wp n).form lam' γ + (wm n).form lam' γ) atTop :=
        ennreal_liminf_add_le _ _
    _ ≤ liminf (fun n => 2 * (u n).form lam' γ + 2 * (v n).form lam' γ + 2 * η n) atTop :=
        liminf_le_liminf (Eventually.of_forall hsum)
    _ = 2 * a + 2 * b := hlim.liminf_eq
    _ ≤ 2 * (gaussForm lam' γ f + δ) + 2 * (gaussForm lam' γ g + δ) :=
        add_le_add (mul_le_mul_right ha.le 2) (mul_le_mul_right hb.le 2)
    _ = 2 * gaussForm lam' γ f + 2 * gaussForm lam' γ g + 4 * δ := by ring
    _ = 2 * gaussForm lam' γ f + 2 * gaussForm lam' γ g + ε := by
        rw [hδdef, ENNReal.mul_div_cancel (by norm_num) (by norm_num)]

/-- **The parallelogram identity** for `ℰ_∞`. -/
theorem gaussForm_parallelogram [IsProbabilityMeasure γ] {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i)
    {f g : (ℕ → ℝ) → ℝ} (hf : gaussForm lam' γ f < ⊤) (hg : gaussForm lam' γ g < ⊤) :
    gaussForm lam' γ (fun z => f z + g z) < ⊤ ∧
      gaussForm lam' γ (fun z => f z + g z) + gaussForm lam' γ (fun z => f z - g z) =
        2 * gaussForm lam' γ f + 2 * gaussForm lam' γ g := by
  have hle := gaussForm_parallelogram_le (γ := γ) hlam f g
  have hfin : 2 * gaussForm lam' γ f + 2 * gaussForm lam' γ g < ⊤ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num) hf, ENNReal.mul_lt_top (by norm_num) hg⟩
  refine ⟨lt_of_le_of_lt (le_self_add.trans hle) hfin, le_antisymm hle ?_⟩
  have h2 := gaussForm_parallelogram_le (γ := γ) hlam (fun z => f z + g z) (fun z => f z - g z)
  have e1 : (fun z => (f z + g z) + (f z - g z)) = fun z => 2 * f z := funext fun z => by ring
  have e2 : (fun z => (f z + g z) - (f z - g z)) = fun z => 2 * g z := funext fun z => by ring
  rw [e1, e2, gaussForm_smul hlam, gaussForm_smul hlam] at h2
  have h4 : ENNReal.ofReal ((2 : ℝ) ^ 2) = 2 * 2 := by norm_num
  rw [h4] at h2
  have h5 : 2 * (2 * gaussForm lam' γ f + 2 * gaussForm lam' γ g) ≤
      2 * (gaussForm lam' γ (fun z => f z + g z) + gaussForm lam' γ (fun z => f z - g z)) := by
    calc 2 * (2 * gaussForm lam' γ f + 2 * gaussForm lam' γ g)
        = 2 * 2 * gaussForm lam' γ f + 2 * 2 * gaussForm lam' γ g := by ring
      _ ≤ _ := h2
      _ = _ := by ring
  exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 h5

/-- The reference eigenvalues are nonnegative. -/
theorem IsRefEigenbasis.lam_nonneg' {d : ℕ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
    {lam : ℕ → ℝ} (he : IsRefEigenbasis μ e lam) (j : ℕ) : 0 ≤ lam j := by
  have h := he.eigen j (e j) (he.memH1 j)
  rw [he.orthonormal, if_pos rfl, mul_one] at h
  rw [← h]
  exact integral_nonneg fun x => Finset.sum_nonneg fun k _ => mul_self_nonneg _

end SharpLSI
