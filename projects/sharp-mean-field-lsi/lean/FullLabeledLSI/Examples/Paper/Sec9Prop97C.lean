import FullLabeledLSI.Examples.Paper.Sec9Prop97B

/-!
# Proposition 9.7, part C: invariance and bounds for the common potential

Lane C of the Section 9 formalization.  `Pt_congr_ae` (profile data only depends on the a.e. class),
`cosK_lineT` and the `1/k`-periodicity of the common potential, and a uniform bound on the common potential
for `a, r ∈ [0,1]` (`commonPotential_bound`).
-/

open MeasureTheory InformationTheory Filter Topology Set
open scoped ENNReal Real

namespace SharpLSI.FL.Ex.P97

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR FL.Ex.Def

theorem Pt_congr_ae (k : ℕ) (r : ℝ) {f g : Torus 1 → ℝ} (hf : Def.Adm f)
    (h : f =ᵐ[haar 1] g) : Def.Pt k r f = Def.Pt k r g := by
  have h2 : (fun x => f x ^ 2) =ᵐ[haar 1] fun x => g x ^ 2 := h.mono fun x hx => by simp only; rw [hx]
  obtain ⟨-, hgrad⟩ := memH1_congr_ae' hf.2.1 h
  have hmc : ∀ j : ℤ, Def.mcos j (fun x => f x ^ 2) = Def.mcos j (fun x => g x ^ 2) := fun j => by
    unfold Def.mcos
    exact integral_congr_ae (h2.mono fun x hx => by simp only at hx ⊢; rw [hx])
  have hms : ∀ j : ℤ, Def.msin j (fun x => f x ^ 2) = Def.msin j (fun x => g x ^ 2) := fun j => by
    unfold Def.msin
    exact integral_congr_ae (h2.mono fun x hx => by simp only at hx ⊢; rw [hx])
  have hW : Def.Wd f = Def.Wd g := by
    unfold Def.Wd
    exact integral_congr_ae (hgrad.mono fun x hx => by simp only at hx ⊢; rw [hx])
  have hH : Def.Hf f = Def.Hf g := by
    unfold Def.Hf
    rw [densMeasure_congr_ae h2]
  refine Prod.ext ?_ ?_
  · funext j
    fin_cases j
    · exact hmc _
    · exact hms _
    · exact hmc _
    · exact hms _
  · simp only [Def.Pt, Def.Jf, hW, hH]

theorem cosK_lineT (j : ℤ) (s : ℝ) : Reg.cosK j (lineT s) = Real.cos (2 * π * j * s) := by
  obtain ⟨m, hm⟩ := secT_lineT_sub s
  unfold Reg.cosK
  rw [hm, show 2 * π * j * (s + m) = 2 * π * j * s + ((j * m : ℤ) : ℝ) * (2 * π) by push_cast; ring]
  exact Real.cos_add_int_mul_two_pi _ _

theorem sinK_lineT (j : ℤ) (s : ℝ) : sinK j (lineT s) = Real.sin (2 * π * j * s) := by
  obtain ⟨m, hm⟩ := secT_lineT_sub s
  unfold sinK
  rw [hm, show 2 * π * j * (s + m) = 2 * π * j * s + ((j * m : ℤ) : ℝ) * (2 * π) by push_cast; ring]
  exact Real.sin_add_int_mul_two_pi _ _

/-- The common potential is `1/k`-periodic along the line. -/
theorem Abasis_lineT_periodic {k : ℕ} (hk : 1 ≤ k) (a r c1 s1 c2 s2 : ℝ) (s : ℝ) :
    Def.Abasis k a r c1 s1 c2 s2 (lineT (s + 1 / (k : ℝ))) = Def.Abasis k a r c1 s1 c2 s2 (lineT s) := by
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [Def.Abasis_eq, Def.Abasis_eq, cosK_lineT, cosK_lineT, sinK_lineT, sinK_lineT, cosK_lineT,
    cosK_lineT, sinK_lineT, sinK_lineT]
  have e1 : 2 * π * ((k : ℤ) : ℝ) * (s + 1 / k) = 2 * π * ((k : ℤ) : ℝ) * s + 1 * (2 * π) := by
    push_cast; field_simp
  have e2 : 2 * π * ((2 * (k : ℤ) : ℤ) : ℝ) * (s + 1 / k) =
      2 * π * ((2 * (k : ℤ) : ℤ) : ℝ) * s + 2 * (2 * π) := by
    push_cast; field_simp
  have c1' := Real.cos_add_int_mul_two_pi (2 * π * ((k : ℤ) : ℝ) * s) 1
  have s1' := Real.sin_add_int_mul_two_pi (2 * π * ((k : ℤ) : ℝ) * s) 1
  have c2' := Real.cos_add_int_mul_two_pi (2 * π * ((2 * (k : ℤ) : ℤ) : ℝ) * s) 2
  have s2' := Real.sin_add_int_mul_two_pi (2 * π * ((2 * (k : ℤ) : ℤ) : ℝ) * s) 2
  simp only [Int.cast_one, Int.cast_ofNat] at c1' s1' c2' s2'
  rw [e1, e2, c1', s1', c2', s2']

/-! ### A uniform bound -/

theorem exists_Abasis_bound (k : ℕ) :
    ∃ R : ℝ, ∀ a r c1 s1 c2 s2 : ℝ, |a| ≤ 1 → |r| ≤ 1 → |c1| ≤ 1 → |s1| ≤ 1 → |c2| ≤ 1 → |s2| ≤ 1 →
      ∀ x, |Def.Abasis k a r c1 s1 c2 s2 x| ≤ R := by
  let Φ : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ → ℝ := fun v =>
    |Def.alpha0 k v.1 v.2.2.1 v.2.2.2.1| + |Def.beta1 k v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2.1 v.2.2.2.2.2| +
      |Def.beta2 k v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2.1 v.2.2.2.2.2| +
      |Def.beta3 k v.1 v.2.2.1 v.2.2.2.1| + |Def.beta4 k v.1 v.2.2.1 v.2.2.2.1|
  have hΦ : Continuous Φ := by
    unfold Φ Def.alpha0 Def.beta1 Def.beta2 Def.beta3 Def.beta4
    fun_prop
  let I : Set ℝ := Set.Icc (-1) 1
  have hK : IsCompact (I ×ˢ I ×ˢ I ×ˢ I ×ˢ I ×ˢ I) :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod
      (isCompact_Icc.prod isCompact_Icc))))
  obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨R, fun a r c1 s1 c2 s2 ha hr h1 h2 h3 h4 x => ?_⟩
  have hmem : (a, r, c1, s1, c2, s2) ∈ I ×ˢ I ×ˢ I ×ˢ I ×ˢ I ×ˢ I := by
    simp only [I, Set.mem_prod, Set.mem_Icc]
    exact ⟨abs_le.1 ha, abs_le.1 hr, abs_le.1 h1, abs_le.1 h2, abs_le.1 h3, abs_le.1 h4⟩
  have hb := hR _ hmem
  have hΦ0 : 0 ≤ Φ (a, r, c1, s1, c2, s2) := by unfold Φ; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hΦ0] at hb
  refine le_trans ?_ hb
  rw [Def.Abasis_eq]
  have hc1 := abs_cosK_le (k : ℤ) x
  have hs1 := abs_sinK_le (k : ℤ) x
  have hc2 := abs_cosK_le (2 * (k : ℤ)) x
  have hs2 := abs_sinK_le (2 * (k : ℤ)) x
  have t1 : |Def.beta1 k a r c1 s1 c2 s2 * Reg.cosK k x| ≤ |Def.beta1 k a r c1 s1 c2 s2| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hc1
  have t2 : |Def.beta2 k a r c1 s1 c2 s2 * sinK k x| ≤ |Def.beta2 k a r c1 s1 c2 s2| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hs1
  have t3 : |Def.beta3 k a c1 s1 * Reg.cosK (2 * (k : ℤ)) x| ≤ |Def.beta3 k a c1 s1| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hc2
  have t4 : |Def.beta4 k a c1 s1 * sinK (2 * (k : ℤ)) x| ≤ |Def.beta4 k a c1 s1| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hs2
  unfold Φ
  simp only
  calc _ ≤ |Def.alpha0 k a c1 s1| + |Def.beta1 k a r c1 s1 c2 s2 * Reg.cosK (↑k) x| +
        |Def.beta2 k a r c1 s1 c2 s2 * sinK (↑k) x| +
        |Def.beta3 k a c1 s1 * Reg.cosK (2 * ↑k) x| + |Def.beta4 k a c1 s1 * sinK (2 * ↑k) x| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by linarith

end SharpLSI.FL.Ex.P97
