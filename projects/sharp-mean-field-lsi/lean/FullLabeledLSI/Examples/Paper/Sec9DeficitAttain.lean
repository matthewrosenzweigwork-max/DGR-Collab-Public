import FullLabeledLSI.Examples.Paper.Sec9DeficitFamily

/-!
# Lemma 9.5, L4: the infimum of the deficit is attained by a family with at most six species

Lane C of the Section 9 formalization.  The deficit of a family is `Λ(p)` with
`p = ∑ θ_i Pt(f_i) ∈ ℝ⁵` (`deficit_eq_Lam`).  By Carathéodory every point of `conv(Pt(Adm))` is a convex
combination of at most six points of `Pt(Adm)`; a minimizing sequence of six-slot data is compactified,
and the closedness of `K` (`closed_K`) gives the limit family.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.Def

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR FL.Ex.Cmp

/-! ### Carathéodory with padding to six slots -/

theorem finrank_PE : Module.finrank ℝ PE = 5 := by
  simp [PE, Module.finrank_prod]

theorem exists_fin6 {S : Set PE} (hS : S.Nonempty) {p : PE} (hp : p ∈ convexHull ℝ S) :
    ∃ (θ : Fin 6 → ℝ) (z : Fin 6 → PE), (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1 ∧ (∀ i, z i ∈ S) ∧
      ∑ i, θ i • z i = p := by
  obtain ⟨ι, _, z0, w0, hz0, hai, hw0, hs0, hc0⟩ := eq_pos_convex_span_of_mem_convexHull hp
  have hcard : Fintype.card ι ≤ 6 := by
    have h1 := hai.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z0))
    rw [finrank_PE] at h2
    exact h1.trans (Nat.add_le_add_right h2 1)
  obtain ⟨s0, hs0'⟩ := hS
  classical
  let g : ι → Fin 6 := fun i => Fin.castLE hcard (Fintype.equivFin ι i)
  have hg : Function.Injective g := by
    intro i j hij
    exact (Fintype.equivFin ι).injective (Fin.castLE_injective hcard hij)
  let θ : Fin 6 → ℝ := fun j => ∑ i, if g i = j then w0 i else 0
  let z : Fin 6 → PE := fun j => if h : ∃ i, g i = j then z0 h.choose else s0
  have hzg : ∀ i, z (g i) = z0 i := by
    intro i
    have h : ∃ i', g i' = g i := ⟨i, rfl⟩
    simp only [z, h, ↓reduceDIte]
    have := hg h.choose_spec
    rw [this]
  refine ⟨θ, z, fun j => ?_, ?_, fun j => ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => by split_ifs; exact (hw0 i).le; exact le_rfl
  · simp only [θ]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq, hs0]
  · simp only [z]
    split_ifs with h
    · exact hz0 ⟨_, rfl⟩
    · exact hs0'
  · simp only [θ, Finset.sum_smul]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ j : Fin 6, (if g i = j then w0 i else 0) • z j = w0 i • z0 i := by
      intro i
      simp only [ite_smul, zero_smul]
      rw [Finset.sum_ite_eq]
      simp [hzg]
    simp_rw [this]
    exact hc0

/-! ### Bounds for convex combinations of profile points -/

theorem exists_Psi_bound (k : ℕ) (a r : ℝ) :
    ∃ M : ℝ, ∀ m : Fin 4 → ℝ, (∀ j, |m j| ≤ 1) → |PsiV k a r m| ≤ M := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin 4 => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuous_PsiV k a r).continuousOn
  refine ⟨M, fun m hm => ?_⟩
  have := hM m (fun j _ => abs_le.1 (hm j))
  simpa using this

theorem comb_bounds {k : ℕ} {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ aCos) {ι : Type*} [Fintype ι]
    {θ : ι → ℝ} (hθ0 : ∀ i, 0 ≤ θ i) (hθ1 : ∑ i, θ i = 1) {f : ι → Torus 1 → ℝ}
    (hf : ∀ i, Adm (f i)) :
    0 ≤ (∑ i, θ i • Pt k r (f i)).2 ∧ ∀ j, |(∑ i, θ i • Pt k r (f i)).1 j| ≤ 1 := by
  refine ⟨?_, fun j => ?_⟩
  · simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul, Pt]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hθ0 i) (Jf_nonneg hr0 hr (hf i))
  · simp only [Prod.fst_sum, Prod.smul_fst, Pt, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc |∑ i, θ i * mvecF k (f i) j| ≤ ∑ i, |θ i * mvecF k (f i) j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, θ i := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (hθ0 i)]
          calc θ i * |mvecF k (f i) j| ≤ θ i * 1 :=
                mul_le_mul_of_nonneg_left (abs_mvecF_le k (hf i) j) (hθ0 i)
            _ = θ i := mul_one _
      _ = 1 := hθ1

theorem Pt_mem_K {k : ℕ} {r : ℝ} {f : Torus 1 → ℝ} (hf : Adm f) : Pt k r f ∈ Kset k r :=
  ⟨f, hf, rfl, le_rfl⟩

/-! ### Attainment -/

theorem exists_min_family {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < aCos) :
    ∃ F : Family 1, F.Admissible ∧ F.q ≤ 6 ∧
      ∀ G : Family 1, G.Admissible →
        deficit (attrW (harmKernel k a)) r F ≤ deficit (attrW (harmKernel k a)) r G := by
  classical
  have hrle : r ≤ aCos := hr.le
  set S : Set PE := {z | ∃ f, Adm f ∧ Pt k r f = z} with hSdef
  have hone : Adm (fun _ : Torus 1 => (1 : ℝ)) := ⟨fun _ => zero_le_one, SR.memH1_one, by simp⟩
  have hS : S.Nonempty := ⟨_, _, hone, rfl⟩
  obtain ⟨M, hM⟩ := exists_Psi_bound k a r
  set Dset : Set ℝ := {d | ∃ G : Family 1, G.Admissible ∧
    deficit (attrW (harmKernel k a)) r G = d} with hDset
  have hG1 : (mkFamily (fun _ : Fin 1 => (1 : ℝ)) (fun _ => fun _ : Torus 1 => (1 : ℝ))).Admissible :=
    mkFamily_adm (fun _ => one_pos) (by simp) (fun _ => hone)
  have hDne : Dset.Nonempty := ⟨_, _, hG1, rfl⟩
  -- the point of an admissible family
  have hpt : ∀ G : Family 1, G.Admissible →
      deficit (attrW (harmKernel k a)) r G = Lam k a r (∑ i, G.θ i • Pt k r (fOf G i)) :=
    fun G hG => deficit_eq_Lam hk ha0 ha1 r G hG
  have hLamLow : ∀ {ι : Type} [Fintype ι] {θ : ι → ℝ} {f : ι → Torus 1 → ℝ}, (∀ i, 0 ≤ θ i) →
      ∑ i, θ i = 1 → (∀ i, Adm (f i)) → -M ≤ Lam k a r (∑ i, θ i • Pt k r (f i)) := by
    intro ι _ θ f h0 h1 hf
    obtain ⟨hb1, hb2⟩ := comb_bounds (k := k) hr0 hrle h0 h1 hf
    have := hM _ hb2
    unfold Lam
    linarith [(abs_le.1 this).1]
  have hDbdd : BddBelow Dset := by
    refine ⟨-M, ?_⟩
    rintro _ ⟨G, hG, rfl⟩
    rw [hpt G hG]
    exact hLamLow (fun i => (hG.1 i).le) hG.2.1 (fun i => adm_fOf hG i)
  obtain ⟨u, hanti, hulim, humem⟩ := exists_seq_tendsto_sInf hDne hDbdd
  choose G hGadm hGdef using humem
  -- six-slot data
  have hpc : ∀ n, (∑ i, (G n).θ i • Pt k r (fOf (G n) i)) ∈ convexHull ℝ S := by
    intro n
    exact (convex_convexHull ℝ S).sum_mem (fun i _ => ((hGadm n).1 i).le) (hGadm n).2.1
      (fun i _ => subset_convexHull ℝ S ⟨fOf (G n) i, adm_fOf (hGadm n) i, rfl⟩)
  choose θ z hθ0 hθ1 hzS hz using fun n => exists_fin6 hS (hpc n)
  have hfex : ∀ n i, ∃ f, Adm f ∧ Pt k r f = z n i := fun n i => hzS n i
  choose f hfAdm hfPt using hfex
  have hdefn : ∀ n, Lam k a r (∑ i, θ n i • z n i) = u n := by
    intro n
    rw [hz n, ← hpt (G n) (hGadm n)]
    exact hGdef n
  have hcb : ∀ n, 0 ≤ (∑ i, θ n i • z n i).2 ∧ ∀ j, |(∑ i, θ n i • z n i).1 j| ≤ 1 := by
    intro n
    have := comb_bounds (k := k) hr0 hrle (hθ0 n) (hθ1 n) (hfAdm n)
    simpa only [hfPt] using this
  have hp2 : ∀ n, (∑ i, θ n i • z n i).2 ≤ u 0 + M := by
    intro n
    have h1 := hdefn n
    have h2 := (abs_le.1 (hM _ (hcb n).2)).1
    unfold Lam at h1
    have : u n ≤ u 0 := hanti (Nat.zero_le n)
    linarith
  have hzJ : ∀ n i, 0 ≤ (z n i).2 := fun n i => by
    rw [← hfPt n i]; exact Jf_nonneg hr0 hrle (hfAdm n i)
  have hterm : ∀ n i, θ n i * (z n i).2 ≤ u 0 + M := by
    intro n i
    have hsum : (∑ i, θ n i • z n i).2 = ∑ i, θ n i * (z n i).2 := by
      simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
    have := Finset.single_le_sum (f := fun i => θ n i * (z n i).2)
      (fun i _ => mul_nonneg (hθ0 n i) (hzJ n i)) (Finset.mem_univ i)
    linarith [hp2 n]
  have hθle : ∀ n i, θ n i ≤ 1 := by
    intro n i
    have := Finset.single_le_sum (f := fun i => θ n i) (fun i _ => hθ0 n i) (Finset.mem_univ i)
    linarith [hθ1 n]
  set R : ℝ := max 1 (u 0 + M) with hR
  have hXb : ∀ n, ((θ n, fun i => θ n i • z n i) : (Fin 6 → ℝ) × (Fin 6 → PE)) ∈
      Metric.closedBall (0 : (Fin 6 → ℝ) × (Fin 6 → PE)) R := by
    intro n
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    have hR0 : 0 ≤ R := (zero_le_one).trans (le_max_left _ _)
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun i => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hθ0 n i)]
      exact (hθle n i).trans (le_max_left _ _)
    · refine (pi_norm_le_iff_of_nonneg hR0).2 fun i => ?_
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · refine (pi_norm_le_iff_of_nonneg hR0).2 fun j => ?_
        rw [Real.norm_eq_abs]
        simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
        have hmj : |(z n i).1 j| ≤ 1 := by rw [← hfPt n i]; exact abs_mvecF_le k (hfAdm n i) j
        rw [abs_mul, abs_of_nonneg (hθ0 n i)]
        calc θ n i * |(z n i).1 j| ≤ 1 * 1 :=
              mul_le_mul (hθle n i) hmj (abs_nonneg _) zero_le_one
          _ ≤ R := by rw [mul_one]; exact le_max_left _ _
      · rw [Real.norm_eq_abs]
        simp only [Prod.smul_snd, smul_eq_mul]
        rw [abs_of_nonneg (mul_nonneg (hθ0 n i) (hzJ n i))]
        exact (hterm n i).trans (le_max_right _ _)
  obtain ⟨Xl, -, φ, hφ, hXl⟩ := (isCompact_closedBall (0 : (Fin 6 → ℝ) × (Fin 6 → PE)) R).tendsto_subseq hXb
  set θl : Fin 6 → ℝ := Xl.1 with hθl
  set vl : Fin 6 → PE := Xl.2 with hvl
  have hθt : ∀ i, Tendsto (fun n => θ (φ n) i) atTop (𝓝 (θl i)) := fun i =>
    ((continuous_apply i).comp continuous_fst).tendsto Xl |>.comp hXl
  have hvt : ∀ i, Tendsto (fun n => θ (φ n) i • z (φ n) i) atTop (𝓝 (vl i)) := fun i =>
    ((continuous_apply i).comp continuous_snd).tendsto Xl |>.comp hXl
  have hθl0 : ∀ i, 0 ≤ θl i := fun i => ge_of_tendsto' (hθt i) fun n => hθ0 (φ n) i
  have hθl1 : ∑ i, θl i = 1 := by
    have : Tendsto (fun n => ∑ i, θ (φ n) i) atTop (𝓝 (∑ i, θl i)) :=
      tendsto_finsetSum _ fun i _ => hθt i
    exact tendsto_nhds_unique this (by simp [hθ1])
  -- the second components are nonnegative; the first are controlled by the weights
  have hvl2 : ∀ i, 0 ≤ (vl i).2 := fun i => by
    have := ((continuous_snd.tendsto (vl i)).comp (hvt i))
    exact ge_of_tendsto' this fun n => by
      simp only [Function.comp, Prod.smul_snd, smul_eq_mul]
      exact mul_nonneg (hθ0 _ i) (hzJ _ i)
  have hvl1 : ∀ i j, |(vl i).1 j| ≤ θl i := fun i j => by
    have h1 := ((continuous_abs.comp ((continuous_apply j).comp continuous_fst)).tendsto (vl i)).comp (hvt i)
    refine le_of_tendsto_of_tendsto h1 (hθt i) (Eventually.of_forall fun n => ?_)
    simp only [Function.comp, Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    have hmj : |(z (φ n) i).1 j| ≤ 1 := by
      rw [← hfPt (φ n) i]; exact abs_mvecF_le k (hfAdm _ i) j
    rw [abs_mul, abs_of_nonneg (hθ0 _ i)]
    calc θ (φ n) i * |(z (φ n) i).1 j| ≤ θ (φ n) i * 1 :=
          mul_le_mul_of_nonneg_left hmj (hθ0 _ i)
      _ = θ (φ n) i := mul_one _
  -- limit profiles
  have hex : ∀ i, ∃ g : Torus 1 → ℝ, Adm g ∧ (0 < θl i →
      mvecF k g = ((θl i)⁻¹ • vl i).1 ∧ Jf r g ≤ ((θl i)⁻¹ • vl i).2) := by
    intro i
    by_cases hi : 0 < θl i
    · have hzt : Tendsto (fun n => z (φ n) i) atTop (𝓝 ((θl i)⁻¹ • vl i)) := by
        have h1 : Tendsto (fun n => (θ (φ n) i)⁻¹ • (θ (φ n) i • z (φ n) i)) atTop
            (𝓝 ((θl i)⁻¹ • vl i)) := ((hθt i).inv₀ hi.ne').smul (hvt i)
        refine h1.congr' ?_
        filter_upwards [(hθt i).eventually (lt_mem_nhds hi)] with n hn
        rw [smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
      have hmem : (θl i)⁻¹ • vl i ∈ Kset k r :=
        (closed_K k hr0 hr).mem_of_tendsto hzt (Eventually.of_forall fun n => by
          rw [← hfPt]; exact Pt_mem_K (hfAdm _ i))
      obtain ⟨g, hg, hg1, hg2⟩ := hmem
      exact ⟨g, hg, fun _ => ⟨hg1, hg2⟩⟩
    · exact ⟨fun _ => 1, hone, fun h => absurd h hi⟩
  choose g hgAdm hgK using hex
  set Ipos : Finset (Fin 6) := Finset.univ.filter (fun i => 0 < θl i) with hIpos
  have hoff : ∀ i, i ∉ Ipos → θl i = 0 := fun i hi => by
    have : ¬ 0 < θl i := fun h => hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    exact le_antisymm (not_lt.1 this) (hθl0 i)
  have hvoff : ∀ i, i ∉ Ipos → ∀ j, (vl i).1 j = 0 := fun i hi j => by
    have := hvl1 i j
    rw [hoff i hi] at this
    exact abs_nonpos_iff.1 this
  set q' : PE := ∑ i ∈ Ipos, θl i • Pt k r (g i) with hq'
  set V : PE := ∑ i, vl i with hV
  have hq1 : q'.1 = V.1 := by
    funext j
    simp only [hq', hV, Prod.fst_sum, Finset.sum_apply, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Pt]
    rw [← Finset.sum_subset (Finset.subset_univ Ipos) (fun i _ hi => hvoff i hi j)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hipos : 0 < θl i := (Finset.mem_filter.1 hi).2
    rw [(hgK i hipos).1]
    simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
    rw [mul_inv_cancel_left₀ hipos.ne']
  have hq2 : q'.2 ≤ V.2 := by
    simp only [hq', hV, Prod.snd_sum, Prod.smul_snd, smul_eq_mul, Pt]
    calc ∑ i ∈ Ipos, θl i * Jf r (g i) ≤ ∑ i ∈ Ipos, (vl i).2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hipos : 0 < θl i := (Finset.mem_filter.1 hi).2
          have h2 := (hgK i hipos).2
          simp only [Prod.smul_snd, smul_eq_mul] at h2
          calc θl i * Jf r (g i) ≤ θl i * ((θl i)⁻¹ * (vl i).2) :=
                mul_le_mul_of_nonneg_left h2 hipos.le
            _ = (vl i).2 := by rw [mul_inv_cancel_left₀ hipos.ne']
      _ ≤ ∑ i, (vl i).2 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => hvl2 i)
  -- the limit point has value `inf`
  have hLamV : Lam k a r V = sInf Dset := by
    have h1 : Tendsto (fun n => ∑ i, θ (φ n) i • z (φ n) i) atTop (𝓝 V) :=
      tendsto_finsetSum _ fun i _ => hvt i
    have h2 := ((continuous_Lam k a r).tendsto V).comp h1
    have h3 : Tendsto (fun n => Lam k a r (∑ i, θ (φ n) i • z (φ n) i)) atTop (𝓝 (sInf Dset)) :=
      (hulim.comp hφ.tendsto_atTop).congr fun n => (hdefn (φ n)).symm
    exact tendsto_nhds_unique h2 h3
  have hLamq : Lam k a r q' ≤ sInf Dset := by
    rw [← hLamV]
    unfold Lam
    rw [hq1]
    linarith
  -- the new family
  set n' : ℕ := Ipos.card with hn'
  let ee : Fin n' ≃ Ipos := (Ipos.equivFin).symm
  have hθ'pos : ∀ j : Fin n', 0 < θl (ee j) := fun j => (Finset.mem_filter.1 (ee j).2).2
  have hsumsub : ∀ {β : Type} [AddCommMonoid β] (h : Fin 6 → β), (∀ i, i ∉ Ipos → h i = 0) →
      ∑ j : Fin n', h (ee j) = ∑ i, h i := by
    intro β _ h hz0
    calc ∑ j : Fin n', h (ee j) = ∑ i : Ipos, h i := Equiv.sum_comp ee (fun i : Ipos => h i)
      _ = ∑ i ∈ Ipos, h i := Finset.sum_coe_sort Ipos h
      _ = ∑ i, h i := Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hz0 i hi)
  have hsum' : ∑ j : Fin n', θl (ee j) = 1 := by
    rw [hsumsub θl hoff, hθl1]
  have hF : (mkFamily (fun j : Fin n' => θl (ee j)) (fun j => g (ee j))).Admissible :=
    mkFamily_adm hθ'pos hsum' (fun j => hgAdm _)
  have hPt' : ∑ j : Fin n', θl (ee j) • Pt k r (g (ee j)) = q' := by
    have := hsumsub (fun i => θl i • Pt k r (g i)) (fun i hi => by simp [hoff i hi])
    rw [this]
    simp only [hq']
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simp [hoff i hi])).symm
  have hdefF : deficit (attrW (harmKernel k a)) r
      (mkFamily (fun j : Fin n' => θl (ee j)) (fun j => g (ee j))) = Lam k a r q' := by
    rw [deficit_mkFamily hk ha0 ha1 r hθ'pos hsum' (fun j => hgAdm _), hPt']
  refine ⟨mkFamily (fun j : Fin n' => θl (ee j)) (fun j => g (ee j)), hF, ?_, fun G' hG' => ?_⟩
  · show n' ≤ 6
    simpa using Finset.card_le_univ Ipos
  · rw [hdefF]
    exact hLamq.trans (csInf_le hDbdd ⟨G', hG', rfl⟩)

end SharpLSI.FL.Ex.Def
