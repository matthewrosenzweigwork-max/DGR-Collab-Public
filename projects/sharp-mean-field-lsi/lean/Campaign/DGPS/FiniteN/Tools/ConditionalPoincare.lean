import Mathlib

/-!
# FIN021 (partial): Prekopa-Leindler infrastructure for the conditional Poincare estimate

One-dimensional Brunn-Minkowski for measurable sets and the normalized (sup = 1) one-dimensional
Prekopa-Leindler inequality, the first building block of the Bobkov-Ledoux route to the sharp
Poincare constant for strongly log-concave measures on a convex ball.
-/

namespace DGPS.FiniteN.Tools.ConditionalPoincare

open MeasureTheory Set

lemma bm_compact {K L C : Set ℝ} (hK : IsCompact K) (hL : IsCompact L) (hK0 : K.Nonempty)
    (hL0 : L.Nonempty) (hC : ∀ x ∈ K, ∀ y ∈ L, x + y ∈ C) :
    volume K + volume L ≤ volume C := by
  obtain ⟨a, haK, haM⟩ := hK.exists_isMaxOn hK0 continuous_id.continuousOn
  obtain ⟨b, hbL, hbM⟩ := hL.exists_isMinOn hL0 continuous_id.continuousOn
  set S : Set ℝ := (fun x => x + b) '' K with hS
  set T : Set ℝ := (fun y => a + y) '' L with hT
  have hSK : volume S = volume K := by
    rw [hS, Set.image_add_right, measure_preimage_add_right]
  have hTL : volume T = volume L := by
    rw [hT, Set.image_add_left, measure_preimage_add]
  have hTm : MeasurableSet T := (hL.image (continuous_const.add continuous_id)).measurableSet
  have hsub : S ∪ T ⊆ C := by
    rintro _ (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact hC x hx b hbL
    · exact hC a haK y hy
  have hint : volume (S ∩ T) = 0 := by
    refine measure_mono_null (t := {a + b}) ?_ (measure_singleton _)
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have h1 : x ≤ a := haM hx
    have h2 : b ≤ y := hbM hy
    have h3 : a + y = x + b := hxy
    simp only [mem_singleton_iff]
    linarith
  have := measure_union_add_inter (μ := volume) S hTm
  rw [hint, add_zero] at this
  calc volume K + volume L = volume S + volume T := by rw [hSK, hTL]
    _ = volume (S ∪ T) := this.symm
    _ ≤ volume C := measure_mono hsub

lemma bm_measurable {A B C : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : A.Nonempty) (hB0 : B.Nonempty) (hC : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ C) :
    volume A + volume B ≤ volume C := by
  obtain ⟨a0, ha0⟩ := hA0
  obtain ⟨b0, hb0⟩ := hB0
  have key : ∀ K ⊆ A, IsCompact K → ∀ L ⊆ B, IsCompact L →
      volume K + volume L ≤ volume C := by
    intro K hKA hK L hLB hL
    have hK' : IsCompact (insert a0 K) := hK.insert a0
    have hL' : IsCompact (insert b0 L) := hL.insert b0
    calc volume K + volume L ≤ volume (insert a0 K) + volume (insert b0 L) := by
          gcongr <;> exact subset_insert _ _
      _ ≤ volume C := bm_compact hK' hL' ⟨a0, mem_insert _ _⟩ ⟨b0, mem_insert _ _⟩ (by
          intro x hx y hy
          refine hC x ?_ y ?_
          · rcases hx with rfl | hx
            · exact ha0
            · exact hKA hx
          · rcases hy with rfl | hy
            · exact hb0
            · exact hLB hy)
  by_contra hcon
  rw [not_le] at hcon
  rcases eq_or_ne (volume A) 0 with hA0 | hA0
  · rw [hA0, zero_add] at hcon
    refine absurd hcon (not_lt.mpr (le_of_forall_lt fun r hr => ?_))
    obtain ⟨L, hLB, hL, hrL⟩ := hB.exists_lt_isCompact hr
    have := key ∅ (empty_subset _) isCompact_empty L hLB hL
    simp at this
    exact hrL.trans_le this
  rcases eq_or_ne (volume B) 0 with hB0 | hB0
  · rw [hB0, add_zero] at hcon
    refine absurd hcon (not_lt.mpr (le_of_forall_lt fun r hr => ?_))
    obtain ⟨K, hKA, hK, hrK⟩ := hA.exists_lt_isCompact hr
    have := key K hKA hK ∅ (empty_subset _) isCompact_empty
    simp at this
    exact hrK.trans_le this
  obtain ⟨u, hu, v, hv, huv⟩ := ENNReal.exists_lt_add_of_lt_add hcon hA0 hB0
  obtain ⟨K, hKA, hK, hKu⟩ := hA.exists_lt_isCompact hu
  obtain ⟨L, hLB, hL, hLv⟩ := hB.exists_lt_isCompact hv
  have := key K hKA hK L hLB hL
  exact absurd (huv.trans (ENNReal.add_lt_add hKu hLv)) (not_lt.mpr this)

lemma level_set_ineq {f g h : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (f1 : ∀ x, f x ≤ 1) (g1 : ∀ x, g x ≤ 1)
    (fs : ∀ t < 1, ∃ x, t < f x) (gs : ∀ t < 1, ∃ x, t < g x)
    (hyp : ∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) (h0 : ∀ x, 0 ≤ h x)
    {t : ℝ} (ht : 0 < t) :
    volume {x | t < f x} + volume {x | t < g x} ≤ 2 * volume {x | t < h x} := by
  by_cases ht1 : 1 ≤ t
  · have e1 : {x | t < f x} = ∅ := by
      ext x; simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]; linarith [f1 x]
    have e2 : {x | t < g x} = ∅ := by
      ext x; simp only [Set.mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]; linarith [g1 x]
    simp [e1, e2]
  rw [not_le] at ht1
  obtain ⟨a0, ha0⟩ := fs t ht1
  obtain ⟨b0, hb0⟩ := gs t ht1
  have hA : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hf
  have hB : MeasurableSet {x | t < g x} := measurableSet_lt measurable_const hg
  have key := bm_measurable hA hB ⟨a0, ha0⟩ ⟨b0, hb0⟩
    (C := (fun s : ℝ => 2⁻¹ * s) ⁻¹' {x | t < h x}) (by
      intro x hx y hy
      have hx : t < f x := hx
      have hy : t < g y := hy
      show t < h (2⁻¹ * (x + y))
      have hxy := hyp x y
      by_contra hcon
      rw [not_lt] at hcon
      have h1 : h (2⁻¹ * (x + y)) ^ 2 ≤ t ^ 2 := by
        have := h0 (2⁻¹ * (x + y))
        nlinarith
      have h2 : h ((x + y) / 2) = h (2⁻¹ * (x + y)) := by congr 1; ring
      rw [h2] at hxy
      nlinarith [mul_lt_mul'' hx hy ht.le ht.le])
  rw [Real.volume_preimage_mul_left (by norm_num)] at key
  have : ENNReal.ofReal |(2⁻¹ : ℝ)⁻¹| = 2 := by
    rw [inv_inv, abs_of_pos (by norm_num : (0:ℝ) < 2)]; simp
  rwa [this] at key

lemma meas_lt_measurable (f : ℝ → ℝ) : Measurable (fun t : ℝ => volume {x | t < f x}) :=
  Antitone.measurable (fun _ _ hab => measure_mono fun _ hx => lt_of_le_of_lt hab hx)

lemma pl1_norm {f g h : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (f0 : ∀ x, 0 ≤ f x) (g0 : ∀ x, 0 ≤ g x) (h0 : ∀ x, 0 ≤ h x)
    (f1 : ∀ x, f x ≤ 1) (g1 : ∀ x, g x ≤ 1)
    (fs : ∀ t < 1, ∃ x, t < f x) (gs : ∀ t < 1, ∃ x, t < g x)
    (hyp : ∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) :
    (∫⁻ x, ENNReal.ofReal (f x)) + ∫⁻ x, ENNReal.ofReal (g x) ≤ 2 * ∫⁻ x, ENNReal.ofReal (h x) := by
  rw [lintegral_eq_lintegral_meas_lt volume (Filter.Eventually.of_forall f0) hf.aemeasurable,
    lintegral_eq_lintegral_meas_lt volume (Filter.Eventually.of_forall g0) hg.aemeasurable,
    lintegral_eq_lintegral_meas_lt volume (Filter.Eventually.of_forall h0) hh.aemeasurable,
    ← lintegral_const_mul' _ _ (by simp), ← lintegral_add_left']
  · refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    exact level_set_ineq hf hg f1 g1 fs gs hyp h0 ht
  · exact (meas_lt_measurable f).aemeasurable

end DGPS.FiniteN.Tools.ConditionalPoincare
