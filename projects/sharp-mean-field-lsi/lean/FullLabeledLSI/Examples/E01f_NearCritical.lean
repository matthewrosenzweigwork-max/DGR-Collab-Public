import FullLabeledLSI.Examples.Paper.Sec9Prop97C
import FullLabeledLSI.Examples.E01f_SmallRate

/-!
# Proposition 9.7 (`higher_near_critical`), lane C

Assembly.  For `k ≥ 2` and `a` close to `1`, with `r = 4π² k² (1-a)`: every admissible family has
nonnegative deficit.  Proof: a minimizing family (Lemma 9.5) has all species equal (Lemma 9.6, in the
explicit form `sMin_unique_of_small`); the common profile is `1/k`-periodic (translation by `1/k` preserves
the Euler equation, then `periodic_unique`); the dilation `F(s) ↦ F(s/k)` reduces the deficit to
`k²` times a deficit for `k = 1` at rate `4π²(1-a)`, which is nonnegative by lane A's `harm_deficit`.
The final theorem is `SharpLSI.FL.Ex.LaneC.higher_near_critical` (statement of the E01 theorem).
-/

open MeasureTheory InformationTheory Filter Topology Set
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.LaneC

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR FL.Ex.Def FL.Ex.P97

/-- Lane A's `k = 1` result in deficit form. -/
theorem deficit_one_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {h : Torus 1 → ℝ} (hh : Def.Adm h) :
    0 ≤ Def.Lam 1 a (aCos * (1 - a)) (Def.Pt 1 (aCos * (1 - a)) h) := by
  set r' := aCos * (1 - a) with hr'
  have hθ : ∀ _ : Fin 1, (0 : ℝ) < 1 := fun _ => one_pos
  have hfam := Def.mkFamily_adm (θ := fun _ : Fin 1 => (1 : ℝ)) (f := fun _ => h) hθ (by simp)
    (fun _ => hh)
  have hdef := Def.deficit_mkFamily (le_refl 1) ha0 ha1.le r' (θ := fun _ : Fin 1 => (1 : ℝ))
    (f := fun _ => h) hθ (by simp) (fun _ => hh)
  have hd := harm_deficit ha0 ha1.le _ hfam
  simp only [Finset.univ_unique, Finset.sum_singleton, one_smul] at hdef
  unfold deficit at hdef
  rw [← hdef]
  have : 2 * r' = 8 * π ^ 2 * (1 - a) := by rw [hr']; unfold aCos; ring
  rw [this]
  linarith

theorem commonPotential_bound {k : ℕ} (_hk : 1 ≤ k) {a r : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {R : ℝ}
    (hR : ∀ a r c1 s1 c2 s2 : ℝ, |a| ≤ 1 → |r| ≤ 1 → |c1| ≤ 1 → |s1| ≤ 1 → |c2| ≤ 1 → |s2| ≤ 1 →
      ∀ x, |Def.Abasis k a r c1 s1 c2 s2 x| ≤ R)
    (G : Family 1) (hG : G.Admissible) (x : Torus 1) :
    |commonPotential (harmKernel k a) r G.bar x| ≤ R := by
  have hrle : r ≤ aCos := hr1.trans (by unfold aCos; nlinarith [Real.pi_gt_three])
  obtain ⟨-, hb⟩ := Def.comb_bounds (k := k) hr0 hrle (fun i => (hG.1 i).le) hG.2.1
    (fun i => Def.adm_fOf hG i)
  rw [Def.commonPotential_eq_Abasis G hG a r]
  exact hR a r _ _ _ _ (by rw [abs_of_nonneg ha0]; exact ha1) (by rw [abs_of_nonneg hr0]; exact hr1)
    (hb 0) (hb 1) (hb 2) (hb 3) x

theorem deficit_nonneg_near {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {r R : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hrr : r = aCos * (k : ℝ) ^ 2 * (1 - a)) (hR0 : 0 ≤ R)
    (hRb : ∀ G : Family 1, G.Admissible → ∀ x,
      |commonPotential (harmKernel k a) r G.bar x| ≤ R)
    (hsmall : r * (1 + (Real.sqrt R + R)) ^ 2 < 4 * π ^ 2 * (Real.exp (-(1 + R))) ^ 2) :
    ∀ G : Family 1, G.Admissible → 0 ≤ deficit (attrW (harmKernel k a)) r G := by
  have hrle : r < aCos := lt_of_le_of_lt hr1 (by unfold aCos; nlinarith [Real.pi_gt_three])
  obtain ⟨F, hF, hq, hFmin⟩ := Def.exists_min_family hk ha0 ha1.le hr0 hrle
  suffices h : 0 ≤ deficit (attrW (harmKernel k a)) r F from fun G hG => h.trans (hFmin G hG)
  set A := commonPotential (harmKernel k a) r F.bar with hA
  have hAs : IsSmoothT A := by
    rw [hA, Def.commonPotential_eq_Abasis F hF a r]
    exact isSmoothT_Abasis _ _ _ _ _ _ _
  have hAc : Continuous A := continuous_of_isSmoothT hAs
  have hAR : ∀ x, |A x| ≤ R := hRb F hF
  have hSM : ∀ i, IsSMin r A (Def.fOf F i) := isSMin_species hk ha0 ha1.le r F hF hFmin
  have hq1 : 0 < F.q := by
    by_contra h
    have h0 : F.q = 0 := by omega
    have hempty : IsEmpty (Fin F.q) := ⟨fun i => by have := i.2; omega⟩
    have := hF.2.1
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact zero_ne_one this
  set i0 : Fin F.q := ⟨0, hq1⟩ with hi0
  have hae : ∀ i, Def.fOf F i =ᵐ[haar 1] Def.fOf F i0 := fun i =>
    sMin_unique_of_small hr0 hr1 hAc hAR hsmall (hSM i0) (hSM i)
  have hp : ∑ i, F.θ i • Def.Pt k r (Def.fOf F i) = Def.Pt k r (Def.fOf F i0) := by
    have h1 : ∀ i, Def.Pt k r (Def.fOf F i) = Def.Pt k r (Def.fOf F i0) := fun i =>
      P97.Pt_congr_ae k r (Def.adm_fOf hF i) (hae i)
    simp_rw [h1]
    rw [← Finset.sum_smul, hF.2.1, one_smul]
  have hdef : deficit (attrW (harmKernel k a)) r F = Def.Lam k a r (Def.Pt k r (Def.fOf F i0)) := by
    rw [Def.deficit_eq_Lam hk ha0 ha1.le r F hF, hp]
  obtain ⟨hlo, -, -, -⟩ := sMin_bounds hr0 hr1 hAc hAR (hSM i0)
  obtain ⟨Fp, hF2, hper, hpos, hode, hmass, hFM, hFae⟩ := sMin_ode_data hr0 hr1 hAc hAR (hSM i0)
  set η := sFunctional r A (Def.fOf F i0) with hη
  have hPt : Def.Pt k r (Def.fOf F i0) = Def.Pt k r (P97.prof Fp) :=
    P97.Pt_congr_ae k r (Def.adm_fOf hF i0) hFae.symm
  have hd1 : ∀ {H : ℝ → ℝ}, ContDiff ℝ 2 H → ∀ x, HasDerivAt H (deriv H x) x :=
    fun hH x => ((hH.differentiable (by norm_num)) x).hasDerivAt
  have hd2 : ∀ {H : ℝ → ℝ}, ContDiff ℝ 2 H → ∀ x, HasDerivAt (deriv H) (deriv (deriv H) x) x :=
    fun hH x => (((contDiff_one_deriv_of_two hH).differentiable one_ne_zero) x).hasDerivAt
  have hd2c : ∀ {H : ℝ → ℝ}, ContDiff ℝ 2 H → Continuous (deriv (deriv H)) :=
    fun hH => (contDiff_one_iff_deriv.1 (contDiff_one_deriv_of_two hH)).2
  have hd1c : ∀ {H : ℝ → ℝ}, ContDiff ℝ 2 H → Continuous (deriv H) :=
    fun hH => (contDiff_one_deriv_of_two hH).continuous
  set M : ℝ := 1 + (Real.sqrt R + R) with hM
  set c : ℝ := Real.exp (-(1 + R)) with hc
  have hcpos : 0 < c := Real.exp_pos _
  have hB : ∀ x, (A (lineT x) - η) / 4 ≤ R / 2 := fun x => by
    have := (abs_le.1 (hAR (lineT x))).2
    linarith
  have hlow : ∀ x, c ≤ Fp x :=
    min_lower_bound hR0 hr0 hr1 (hd1 hF2) (hd2 hF2) hpos hper hode hB hmass
  -- the potential is `1/k`-periodic along the line
  obtain ⟨c1, s1, c2, s2, hAab⟩ : ∃ c1 s1 c2 s2 : ℝ, A = Def.Abasis k a r c1 s1 c2 s2 :=
    ⟨_, _, _, _, Def.commonPotential_eq_Abasis F hF a r⟩
  have hAper : ∀ s, A (lineT (s + 1 / (k : ℝ))) = A (lineT s) := fun s => by
    rw [hAab]; exact P97.Abasis_lineT_periodic hk _ _ _ _ _ _ s
  -- translation by `1/k`
  have hFτ_per : Function.Periodic (fun s => Fp (s + 1 / (k : ℝ))) 1 := by
    intro s
    show Fp (s + 1 + 1 / (k : ℝ)) = Fp (s + 1 / (k : ℝ))
    rw [show s + 1 + 1 / (k : ℝ) = (s + 1 / (k : ℝ)) + 1 by ring]
    exact hper _
  have hper2 : Function.Periodic (fun x => Fp x ^ 2) 1 := fun x => by simp [hper x]
  have hmτ : ∫ s in (0 : ℝ)..1, Fp (s + 1 / (k : ℝ)) ^ 2 = 1 := by
    have key : ∫ x in (1 / (k : ℝ))..(1 / (k : ℝ) + 1), Fp x ^ 2 = ∫ x in (0 : ℝ)..1, Fp x ^ 2 := by
      simpa using hper2.intervalIntegral_add_eq (1 / (k : ℝ)) 0
    rw [intervalIntegral.integral_comp_add_right (fun x => Fp x ^ 2) (1 / (k : ℝ)), zero_add,
      add_comm (1 : ℝ) (1 / (k : ℝ)), key, hmass]
  have hGd1 : ∀ x, HasDerivAt (fun s => Fp (s + 1 / (k : ℝ))) (deriv Fp (x + 1 / (k : ℝ))) x :=
    fun x => (hd1 hF2 (x + 1 / (k : ℝ))).comp_add_const x (1 / (k : ℝ))
  have hGd2 : ∀ x, HasDerivAt (fun s => deriv Fp (s + 1 / (k : ℝ)))
      (deriv (deriv Fp) (x + 1 / (k : ℝ))) x :=
    fun x => (hd2 hF2 (x + 1 / (k : ℝ))).comp_add_const x (1 / (k : ℝ))
  have hG2c : Continuous (fun s => deriv (deriv Fp) (s + 1 / (k : ℝ))) :=
    (hd2c hF2).comp (continuous_id.add continuous_const)
  have hodeG : ∀ s, deriv (deriv Fp) (s + 1 / (k : ℝ)) =
      Fp (s + 1 / (k : ℝ)) * ((A (lineT s) - η) / 4 - r * Real.log (Fp (s + 1 / (k : ℝ)))) := by
    intro s
    rw [hode (s + 1 / (k : ℝ)), hAper s]
  have huniq : Fp = fun s => Fp (s + 1 / (k : ℝ)) :=
    periodic_unique (r := r) (M := M) (c := c) hcpos hr0 hsmall (F := Fp) (F1 := deriv Fp)
      (F2 := deriv (deriv Fp)) (G := fun s => Fp (s + 1 / (k : ℝ)))
      (G1 := fun s => deriv Fp (s + 1 / (k : ℝ)))
      (G2 := fun s => deriv (deriv Fp) (s + 1 / (k : ℝ)))
      (B := fun s => (A (lineT s) - η) / 4) (hd1 hF2) (hd2 hF2) hGd1 hGd2 (hd2c hF2) hG2c hper
      hFτ_per hlow (fun x => hlow _) hFM (fun x => hFM _) hode hodeG hmass hmτ
  have hperk : Function.Periodic Fp (1 / (k : ℝ)) := fun s => (congrFun huniq s).symm
  -- the dilated profile and Lane A's `k = 1` result
  have hLam := P97.Lam_scaling hk a r (hd1 hF2) (hd1c hF2) hper hperk hmass
  obtain ⟨hdG, hc1G, hpG⟩ := P97.scaling_data hk (hd1 hF2) (hd1c hF2) hperk
  have hFc : Continuous Fp := hF2.continuous
  have hmG : ∫ s in (0 : ℝ)..1, Fp (s / k) ^ 2 = 1 := by
    have := P97.integral_dilate hk (φ := fun s => Fp s ^ 2) (hFc.pow 2)
      (fun t => by show Fp (t + 1 / (k : ℝ)) ^ 2 = Fp t ^ 2; rw [hperk t])
    rw [this, hmass]
  have hAdmG := P97.adm_prof hdG hc1G hpG (fun s => (hpos _).le) hmG
  have hE2 := deficit_one_nonneg ha0 ha1 hAdmG
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hrk : r / (k : ℝ) ^ 2 = aCos * (1 - a) := by rw [hrr]; field_simp
  rw [hdef, hPt, hLam, hrk]
  exact mul_nonneg (sq_nonneg _) hE2

/-- **Proposition 9.7** (statement of the E01 theorem `higher_near_critical`). -/
theorem higher_near_critical {k : ℕ} (hk : 2 ≤ k) :
    ∃ ak : ℝ, 1 - 1 / (k : ℝ) ^ 2 ≤ ak ∧ ak < 1 ∧ ∀ a : ℝ, ak < a → a < 1 →
      HaarUniqueMinimizer (attrW (harmKernel k a)) ∧
        AgreementAt (attrW (harmKernel k a)) (aCos * (k : ℝ) ^ 2 * (1 - a)) := by
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
  have hacos : (1 : ℝ) < aCos := by unfold aCos; nlinarith [Real.pi_gt_three]
  obtain ⟨Rk, hRk⟩ := P97.exists_Abasis_bound k
  set R : ℝ := max Rk 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hRk' : ∀ a r c1 s1 c2 s2 : ℝ, |a| ≤ 1 → |r| ≤ 1 → |c1| ≤ 1 → |s1| ≤ 1 → |c2| ≤ 1 →
      |s2| ≤ 1 → ∀ x, |Def.Abasis k a r c1 s1 c2 s2 x| ≤ R := fun a r c1 s1 c2 s2 h1 h2 h3 h4 h5 h6 x =>
    (hRk a r c1 s1 c2 s2 h1 h2 h3 h4 h5 h6 x).trans (le_max_left _ _)
  set c : ℝ := Real.exp (-(1 + R)) with hc
  set M : ℝ := 1 + (Real.sqrt R + R) with hM
  have hcpos : 0 < c := Real.exp_pos _
  set δ : ℝ := 4 * π ^ 2 * c ^ 2 / (M ^ 2 + 1) with hδ
  have hδpos : 0 < δ := by positivity
  set ε : ℝ := min 1 δ with hε
  have hεpos : 0 < ε := lt_min one_pos hδpos
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεδ : ε ≤ δ := min_le_right _ _
  have hden : 0 < aCos * (k : ℝ) ^ 2 := by positivity
  refine ⟨1 - ε / (aCos * (k : ℝ) ^ 2), ?_, ?_, fun a hak ha1 => ?_⟩
  · have : ε / (aCos * (k : ℝ) ^ 2) ≤ 1 / (k : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ hden (by positivity)]
      nlinarith
    linarith
  · have : 0 < ε / (aCos * (k : ℝ) ^ 2) := by positivity
    linarith
  · set r : ℝ := aCos * (k : ℝ) ^ 2 * (1 - a) with hr
    have ha0 : 0 ≤ a := by
      have h1 : ε / (aCos * (k : ℝ) ^ 2) ≤ 1 := by
        rw [div_le_one hden]; nlinarith
      linarith
    have hr0 : 0 < r := by rw [hr]; exact mul_pos hden (by linarith)
    have hrε : r < ε := by
      have : 1 - a < ε / (aCos * (k : ℝ) ^ 2) := by linarith
      rw [lt_div_iff₀ hden] at this
      rw [hr]; linarith
    have hr1 : r ≤ 1 := hrε.le.trans hε1
    have hsmall : r * M ^ 2 < 4 * π ^ 2 * c ^ 2 := by
      have h1 : r < δ := lt_of_lt_of_le hrε hεδ
      rw [hδ, lt_div_iff₀ (by positivity)] at h1
      nlinarith [sq_nonneg M]
    have hRb : ∀ G : Family 1, G.Admissible → ∀ x,
        |commonPotential (harmKernel k a) r G.bar x| ≤ R := fun G hG x =>
      commonPotential_bound hk1 ha0 ha1.le hr0.le hr1 hRk' G hG x
    have hnn := deficit_nonneg_near hk1 ha0 ha1 hr0.le hr1 hr hR0 hRb hsmall
    have hC := Def.goodKernel_harmKernel hk1 a
    have hmin := Def.harmKernel_isMinimizer hk1 ha0 ha1.le
    refine ⟨P97.harmKernel_haarUnique hk1 ha0 ha1, ?_⟩
    exact agreement_of_bounds_proved hC hmin (hyp_attr_aux hC) hr0
      (P97.rMs_ge_of_deficit_nonneg hk1 hr0.le hnn)
      (fun e lam Cm he hCm => P97.lamG_le_harm hk1 ha0 ha1 e lam Cm he hCm)

end SharpLSI.FL.Ex.LaneC
