import FullLabeledLSI.Examples.E01f_Deficit

/-!
# Lemma 9.5, additive follow-up: regularity of *every* one-site minimizer

Response to the external review.  `LaneC.harmonic_deficit_attainment` proves regularity for the species
densities of a minimizing family.  This file proves the same smoothness / positivity / Euler equation for an
arbitrary normalized minimizer `q` of the one-site functional with the common potential of a minimizing family.
Nothing frozen is edited.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Ex.LaneC

open SharpLSI FL.Ex.Reg FL.Ex FL.Ex.SR FL.Ex.Def

theorem harmonic_one_site_regularity {k : ℕ} (hk : 1 ≤ k) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < aCos)
    (G : Family 1) (hG : G.Admissible)
    (hGeq : deficit (attrW (harmKernel k a)) r G = ⨅ H : {H : Family 1 // H.Admissible},
        deficit (attrW (harmKernel k a)) r H.1)
    (q : Torus 1 → ℝ) (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∫ x, q x ∂haar 1 = 1)
    (hqH : MemH1 (haar 1) (fun x => Real.sqrt (q x)))
    (hqmin : ∀ q' : Torus 1 → ℝ, (∀ x, 0 ≤ q' x) → ∫ x, q' x ∂haar 1 = 1 →
        MemH1 (haar 1) (fun x => Real.sqrt (q' x)) →
        oneSite r (commonPotential (harmKernel k a) r G.bar) q ≤
          oneSite r (commonPotential (harmKernel k a) r G.bar) q') :
    (∀ i, oneSite r (commonPotential (harmKernel k a) r G.bar) q =
        oneSite r (commonPotential (harmKernel k a) r G.bar) (G.ρ i)) ∧
    ∃ f : Torus 1 → ℝ, IsSmoothT f ∧ (∀ x, 0 < f x) ∧ (fun x => f x ^ 2) =ᵐ[haar 1] q ∧
      ∃ η : ℝ, η = oneSite r (commonPotential (harmKernel k a) r G.bar) q ∧
        ∀ x : Torus 1,
          -4 * dT (dT f) x + commonPotential (harmKernel k a) r G.bar x * f x -
              4 * r * f x * Real.log (f x) = η * f x := by
  have ha1' : a ≤ 1 := ha1.le
  have hbdd : BddBelow (Set.range fun H : {H : Family 1 // H.Admissible} =>
      deficit (attrW (harmKernel k a)) r H.1) := by
    obtain ⟨M, hM⟩ := deficit_lower hk ha0 ha1' hr0.le hr1.le
    exact ⟨-M, by rintro _ ⟨H, rfl⟩; exact hM H.1 H.2⟩
  have hmin : ∀ H : Family 1, H.Admissible →
      deficit (attrW (harmKernel k a)) r G ≤ deficit (attrW (harmKernel k a)) r H := by
    intro H hH
    rw [hGeq]
    exact ciInf_le hbdd ⟨H, hH⟩
  set A := commonPotential (harmKernel k a) r G.bar with hA
  -- species are one-site minimizers
  have hi : ∀ i, ∀ q' : Torus 1 → ℝ, (∀ x, 0 ≤ q' x) → ∫ x, q' x ∂haar 1 = 1 →
      MemH1 (haar 1) (fun x => Real.sqrt (q' x)) → oneSite r A (G.ρ i) ≤ oneSite r A q' := by
    intro i q' hq0' hq1' hqH'
    have hfq : Def.Adm (fun x => Real.sqrt (q' x)) :=
      ⟨fun x => Real.sqrt_nonneg _, hqH', by simp_rw [Real.sq_sqrt (hq0' _)]; exact hq1'⟩
    have h := one_site_mean_le hk ha0 ha1' r G hG hmin hfq
    have hsq : (fun x => Real.sqrt (q' x) ^ 2) = q' := funext fun x => Real.sq_sqrt (hq0' x)
    rw [hsq] at h
    rw [oneSite_all_eq hk ha0 ha1' r G hG hmin i]
    exact h
  -- first conjunct
  have hfirst : ∀ i, oneSite r A q = oneSite r A (G.ρ i) := by
    intro i
    refine le_antisymm (hqmin (G.ρ i) (hG.2.2 i).1 (hG.2.2 i).2.1 (hG.2.2 i).2.2) ?_
    exact hi i q hq0 hq1 hqH
  refine ⟨hfirst, ?_⟩
  -- `√q` minimizes `S_{r,A}`
  have hAs : IsSmoothT A := by
    rw [hA, commonPotential_eq_Abasis G hG a r]
    exact isSmoothT_Abasis _ _ _ _ _ _ _
  have hf0 : Def.Adm (fun x => Real.sqrt (q x)) :=
    ⟨fun x => Real.sqrt_nonneg _, hqH, by simp_rw [Real.sq_sqrt (hq0 _)]; exact hq1⟩
  have hsq0 : (fun x => Real.sqrt (q x) ^ 2) = q := funext fun x => Real.sq_sqrt (hq0 x)
  have hSMin : IsSMin r A (fun x => Real.sqrt (q x)) := by
    refine ⟨hf0.1, hf0.2.1, hf0.2.2, fun g hg0 hgH hg1 => ?_⟩
    have hg : Def.Adm g := ⟨hg0, hgH, hg1⟩
    rw [sFunctional_eq_oneSite r A hf0, sFunctional_eq_oneSite r A hg, hsq0]
    refine hqmin (fun x => g x ^ 2) (fun x => sq_nonneg _) hg1 ?_
    have : (fun x => Real.sqrt (g x ^ 2)) = g := funext fun x => Real.sqrt_sq (hg0 x)
    rw [this]; exact hgH
  obtain ⟨f, hfae, hfs, hfpos, hfeq⟩ := sMin_regularity_ae_smooth hr0.le hAs hSMin
  refine ⟨f, hfs, hfpos, ?_, sFunctional r A (fun x => Real.sqrt (q x)), ?_, hfeq⟩
  · filter_upwards [hfae] with x hx
    rw [hx]
    exact congrFun hsq0 x
  · rw [sFunctional_eq_oneSite r A hf0, hsq0]

end SharpLSI.FL.Ex.LaneC
