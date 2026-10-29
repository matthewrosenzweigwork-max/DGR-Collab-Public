import FullLabeledLSI.Examples.Paper.Sec9DeficitVar

/-!
# Lemma 9.5 (`harmonic_deficit_attainment`), lane C

Assembly of L0-L6: attainment by a family with at most six species (`exists_min_family`), one-site
minimality of every species density (`one_site_mean_le` plus the weighted-average argument), and
smoothness/positivity/Euler equation via H8 (`sMin_regularity_ae_smooth`) for the smooth
potential `A = commonPotential = Abasis`.  The final theorem
`SharpLSI.FL.Ex.LaneC.harmonic_deficit_attainment` has the statement of the E01 theorem of the same name.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Ex.LaneC

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR FL.Ex.Def

theorem sFunctional_eq_oneSite (r : ℝ) (A : Torus 1 → ℝ) {f : Torus 1 → ℝ} (hf : Def.Adm f) :
    sFunctional r A f = oneSite r A (fun x => f x ^ 2) := by
  have h := Jfun_sq r hf
  unfold Def.Jfun Def.Jf Def.Wd Def.Hf at h
  unfold sFunctional oneSite
  linarith

theorem isSmoothT_Abasis (k : ℕ) (a r c1 s1 c2 s2 : ℝ) : IsSmoothT (Abasis k a r c1 s1 c2 s2) := by
  have h1 : ContDiff ℝ ∞ (fun z : Fin 1 → ℝ => Reg.cosK k (liftT z)) := isSmoothT_cosK k
  have h2 : ContDiff ℝ ∞ (fun z : Fin 1 → ℝ => sinK k (liftT z)) := isSmoothT_sinK k
  have h3 : ContDiff ℝ ∞ (fun z : Fin 1 → ℝ => Reg.cosK (2 * (k : ℤ)) (liftT z)) :=
    isSmoothT_cosK _
  have h4 : ContDiff ℝ ∞ (fun z : Fin 1 → ℝ => sinK (2 * (k : ℤ)) (liftT z)) := isSmoothT_sinK _
  unfold IsSmoothT
  have e : (Abasis k a r c1 s1 c2 s2) ∘ liftT = fun z => alpha0 k a c1 s1 +
      beta1 k a r c1 s1 c2 s2 * Reg.cosK k (liftT z) + beta2 k a r c1 s1 c2 s2 * sinK k (liftT z) +
      beta3 k a c1 s1 * Reg.cosK (2 * (k : ℤ)) (liftT z) +
      beta4 k a c1 s1 * sinK (2 * (k : ℤ)) (liftT z) := by
    funext z; simp only [Function.comp, Abasis_eq]
  rw [e]
  exact (((contDiff_const.add (contDiff_const.mul h1)).add (contDiff_const.mul h2)).add
    (contDiff_const.mul h3)).add (contDiff_const.mul h4)

theorem oneSite_all_eq {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℝ)
    (G : Family 1) (hG : G.Admissible)
    (hmin : ∀ H : Family 1, H.Admissible →
      deficit (attrW (harmKernel k a)) r G ≤ deficit (attrW (harmKernel k a)) r H) (i : Fin G.q) :
    oneSite r (commonPotential (harmKernel k a) r G.bar) (G.ρ i) =
      ∑ j, G.θ j * oneSite r (commonPotential (harmKernel k a) r G.bar) (G.ρ j) := by
  set A := commonPotential (harmKernel k a) r G.bar with hA
  set m : Fin G.q → ℝ := fun j => oneSite r A (G.ρ j) with hm
  set mean := ∑ j, G.θ j * m j with hmean
  have hge : ∀ j, mean ≤ m j := by
    intro j
    have := one_site_mean_le hk ha0 ha1 r G hG hmin (adm_fOf hG j)
    rw [sq_fOf hG j] at this
    exact this
  have hsum0 : ∑ j, G.θ j * (m j - mean) = 0 := by
    have : ∑ j, G.θ j * (m j - mean) = ∑ j, G.θ j * m j - mean * ∑ j, G.θ j := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hG.2.1]; ring
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    mul_nonneg (hG.1 j).le (sub_nonneg.2 (hge j)))).1 hsum0 i (Finset.mem_univ _)
  rcases mul_eq_zero.1 hz with h | h
  · exact absurd h (hG.1 i).ne'
  · linarith

/-- Every species profile of a minimizing family minimizes `S_{r,A}` for the common potential. -/
theorem isSMin_species {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (r : ℝ)
    (G : Family 1) (hG : G.Admissible)
    (hmin : ∀ H : Family 1, H.Admissible →
      deficit (attrW (harmKernel k a)) r G ≤ deficit (attrW (harmKernel k a)) r H) (i : Fin G.q) :
    IsSMin r (commonPotential (harmKernel k a) r G.bar) (fOf G i) := by
  set A := commonPotential (harmKernel k a) r G.bar with hA
  have hfi := adm_fOf hG i
  refine ⟨hfi.1, hfi.2.1, hfi.2.2, fun g hg0 hgH hg1 => ?_⟩
  have hg : Def.Adm g := ⟨hg0, hgH, hg1⟩
  rw [sFunctional_eq_oneSite r A hfi, sFunctional_eq_oneSite r A hg, sq_fOf hG i]
  rw [oneSite_all_eq hk ha0 ha1 r G hG hmin i]
  have h := one_site_mean_le hk ha0 ha1 r G hG hmin hg
  exact h

/-- Lemma 9.5. -/
theorem harmonic_deficit_attainment {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < aCos) :
    ∃ F : Family 1, F.Admissible ∧ F.q ≤ 6 ∧
      (∀ G : Family 1, G.Admissible → deficit (attrW (harmKernel k a)) r F ≤
        deficit (attrW (harmKernel k a)) r G) ∧
      ∀ G : Family 1, G.Admissible →
        deficit (attrW (harmKernel k a)) r G = (⨅ H : {H : Family 1 // H.Admissible},
            deficit (attrW (harmKernel k a)) r H.1) →
        (∀ i, ∀ q : Torus 1 → ℝ, (∀ x, 0 ≤ q x) → ∫ x, q x ∂haar 1 = 1 →
            MemH1 (haar 1) (fun x => Real.sqrt (q x)) →
          oneSite r (commonPotential (harmKernel k a) r G.bar) (G.ρ i) ≤
            oneSite r (commonPotential (harmKernel k a) r G.bar) q) ∧
        (∀ i, ∃ f : Torus 1 → ℝ, IsSmoothT f ∧ (∀ x, 0 < f x) ∧
          (fun x => f x ^ 2) =ᵐ[haar 1] G.ρ i ∧
          ∃ η : ℝ, η = oneSite r (commonPotential (harmKernel k a) r G.bar) (G.ρ i) ∧
            ∀ x : Torus 1,
              -4 * dT (dT f) x + commonPotential (harmKernel k a) r G.bar x * f x -
                  4 * r * f x * Real.log (f x) = η * f x) := by
  have ha1' : a ≤ 1 := ha1.le
  obtain ⟨F, hF, hq, hFmin⟩ := exists_min_family hk ha0 ha1' hr0.le hr1
  refine ⟨F, hF, hq, hFmin, fun G hG hGeq => ?_⟩
  have hbdd : BddBelow (Set.range fun H : {H : Family 1 // H.Admissible} =>
      deficit (attrW (harmKernel k a)) r H.1) := by
    obtain ⟨M, hM⟩ := deficit_lower hk ha0 ha1' hr0.le hr1.le
    exact ⟨-M, by rintro _ ⟨H, rfl⟩; exact hM H.1 H.2⟩
  have hmin : ∀ H : Family 1, H.Admissible →
      deficit (attrW (harmKernel k a)) r G ≤ deficit (attrW (harmKernel k a)) r H := by
    intro H hH
    rw [hGeq]
    exact ciInf_le hbdd ⟨H, hH⟩
  have hi : ∀ i, ∀ q : Torus 1 → ℝ, (∀ x, 0 ≤ q x) → ∫ x, q x ∂haar 1 = 1 →
      MemH1 (haar 1) (fun x => Real.sqrt (q x)) →
      oneSite r (commonPotential (harmKernel k a) r G.bar) (G.ρ i) ≤
        oneSite r (commonPotential (harmKernel k a) r G.bar) q := by
    intro i q hq0 hq1 hqH
    have hfq : Def.Adm (fun x => Real.sqrt (q x)) :=
      ⟨fun x => Real.sqrt_nonneg _, hqH, by simp_rw [Real.sq_sqrt (hq0 _)]; exact hq1⟩
    have h := one_site_mean_le hk ha0 ha1' r G hG hmin hfq
    have hsq : (fun x => Real.sqrt (q x) ^ 2) = q := funext fun x => Real.sq_sqrt (hq0 x)
    rw [hsq] at h
    rw [oneSite_all_eq hk ha0 ha1' r G hG hmin i]
    exact h
  refine ⟨hi, fun i => ?_⟩
  set A := commonPotential (harmKernel k a) r G.bar with hA
  have hAs : IsSmoothT A := by
    rw [hA, commonPotential_eq_Abasis G hG a r]
    exact isSmoothT_Abasis _ _ _ _ _ _ _
  have hfi := adm_fOf hG i
  have hSMin : IsSMin r A (fOf G i) := by
    refine ⟨hfi.1, hfi.2.1, hfi.2.2, fun g hg0 hgH hg1 => ?_⟩
    have hg : Def.Adm g := ⟨hg0, hgH, hg1⟩
    rw [sFunctional_eq_oneSite r A hfi, sFunctional_eq_oneSite r A hg, sq_fOf hG i]
    refine hi i (fun x => g x ^ 2) (fun x => sq_nonneg _) hg1 ?_
    have : (fun x => Real.sqrt (g x ^ 2)) = g := funext fun x => Real.sqrt_sq (hg0 x)
    rw [this]; exact hgH
  obtain ⟨f, hfae, hfs, hfpos, hfeq⟩ := sMin_regularity_ae_smooth hr0.le hAs hSMin
  refine ⟨f, hfs, hfpos, ?_, sFunctional r A (fOf G i), ?_, hfeq⟩
  · filter_upwards [hfae] with x hx
    rw [hx]
    exact congrFun (sq_fOf hG i) x
  · rw [sFunctional_eq_oneSite r A hfi, sq_fOf hG i]

end SharpLSI.FL.Ex.LaneC
