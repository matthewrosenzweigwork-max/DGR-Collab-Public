import Mathlib

/-!
# Prekopa-Leindler inequality on `ℝ^k` (INF001)

For `t ∈ [0,1]` and measurable `f g h` on `EuclideanSpace ℝ (Fin k)` with
`f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)` for all `x y`:
`(∫ f) ^ (1 - t) * (∫ g) ^ t ≤ ∫ h`.

* `prekopaLeindler_lintegral`: `ℝ≥0∞`-valued form (`∫⁻`), no integrability hypotheses.
* `prekopaLeindler`: real-valued form (nonnegative `f g`, integrable `f g h`).
* `prekopaLeindler_one`: the case of `ℝ` (dimension one).

Proof: 1D Brunn-Minkowski for measurable sets (compact approximation), the layer-cake formula and
weighted AM-GM for normalized functions, scaling and truncation for the general 1D case, then
induction on the dimension by Fubini through `Fin (n+1) → ℝ ≃ᵐ ℝ × (Fin n → ℝ)`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise

namespace DGPS.FiniteN.Tools

/-- One-dimensional Brunn-Minkowski, additive form, for measurable sets. -/
theorem bm_one_aux_compact {K L C : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hKn : K.Nonempty) (hLn : L.Nonempty)
    (hsub : ∀ a ∈ K, ∀ b ∈ L, a + b ∈ C) :
    volume K + volume L ≤ volume C := by
  obtain ⟨k1, hk1, hk1m⟩ := hK.exists_isMaxOn hKn continuousOn_id
  obtain ⟨l0, hl0, hl0m⟩ := hL.exists_isMinOn hLn continuousOn_id
  set S1 : Set ℝ := (fun x => x + l0) '' K with hS1
  set S2 : Set ℝ := (fun x => k1 + x) '' L with hS2
  have hS1c : IsCompact S1 := hK.image (by fun_prop)
  have hS2c : IsCompact S2 := hL.image (by fun_prop)
  have hv1 : volume S1 = volume K := by
    rw [hS1, Set.image_add_right, measure_preimage_add_right]
  have hv2 : volume S2 = volume L := by
    rw [hS2, Set.image_add_left, measure_preimage_add]
  have hinter : volume (S1 ∩ S2) = 0 := by
    apply measure_mono_null (t := {k1 + l0}) _ (measure_singleton _)
    rintro x ⟨⟨k, hk, rfl⟩, ⟨l, hl, hl'⟩⟩
    have h1 : k ≤ k1 := hk1m hk
    have h2 : l0 ≤ l := hl0m hl
    simp only at hl'
    simp only [mem_singleton_iff]
    linarith
  have hunion : S1 ∪ S2 ⊆ C := by
    rintro x (⟨k, hk, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact hsub k hk l0 hl0
    · exact hsub k1 hk1 l hl
  calc volume K + volume L = volume S1 + volume S2 := by rw [hv1, hv2]
    _ = volume (S1 ∪ S2) + volume (S1 ∩ S2) := (measure_union_add_inter _ hS2c.isClosed.measurableSet).symm
    _ = volume (S1 ∪ S2) := by rw [hinter, add_zero]
    _ ≤ volume C := measure_mono hunion

theorem bm_one {A B C : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hsub : ∀ a ∈ A, ∀ b ∈ B, a + b ∈ C) :
    volume A + volume B ≤ volume C := by
  obtain ⟨a0, ha0⟩ := hAn
  obtain ⟨b0, hb0⟩ := hBn
  by_cases hAt : volume A = ∞
  · have : volume A ≤ volume C := by
      calc volume A = volume ((fun x => x + b0) '' A) := by
            rw [Set.image_add_right, measure_preimage_add_right]
        _ ≤ volume C := by
            apply measure_mono
            rintro _ ⟨a, ha, rfl⟩
            exact hsub a ha b0 hb0
    rw [hAt] at this ⊢
    simp only [top_add]
    exact this
  by_cases hBt : volume B = ∞
  · have : volume B ≤ volume C := by
      calc volume B = volume ((fun x => a0 + x) '' B) := by
            rw [Set.image_add_left, measure_preimage_add]
        _ ≤ volume C := by
            apply measure_mono
            rintro _ ⟨b, hb, rfl⟩
            exact hsub a0 ha0 b hb
    rw [hBt] at this ⊢
    simp only [add_top]
    exact this
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε2 : ((ε : ℝ≥0∞) / 2) ≠ 0 := by simp [hε.ne']
  obtain ⟨K, hKA, hKc, hK⟩ := hA.exists_isCompact_lt_add hAt hε2
  obtain ⟨L, hLB, hLc, hL⟩ := hB.exists_isCompact_lt_add hBt hε2
  have hK' : IsCompact (insert a0 K) := hKc.insert a0
  have hL' : IsCompact (insert b0 L) := hLc.insert b0
  have key := bm_one_aux_compact hK' hL' (insert_nonempty _ _) (insert_nonempty _ _)
    (fun a ha b hb => hsub a (by rcases ha with rfl | ha; exacts [ha0, hKA ha])
      b (by rcases hb with rfl | hb; exacts [hb0, hLB hb]))
  have h1 : volume K ≤ volume (insert a0 K) := measure_mono (subset_insert _ _)
  have h2 : volume L ≤ volume (insert b0 L) := measure_mono (subset_insert _ _)
  calc volume A + volume B ≤ (volume K + ε / 2) + (volume L + ε / 2) := add_le_add hK.le hL.le
    _ = (volume K + volume L) + ε := by
        rw [add_add_add_comm, ENNReal.add_halves]
    _ ≤ volume C + ε := by gcongr; exact (add_le_add h1 h2).trans key


/-- Convex-combination Brunn-Minkowski on the line. -/
theorem bm_one_conv {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {A B C : Set ℝ} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hsub : ∀ a ∈ A, ∀ b ∈ B, (1 - t) * a + t * b ∈ C) :
    ENNReal.ofReal (1 - t) * volume A + ENNReal.ofReal t * volume B ≤ volume C := by
  have h1 : (0 : ℝ) < 1 - t := by linarith [ht.2]
  have e1 : volume ((1 - t) • A) = ENNReal.ofReal (1 - t) * volume A := by
    rw [Measure.addHaar_smul]; simp [abs_of_pos h1]
  have e2 : volume (t • B) = ENNReal.ofReal t * volume B := by
    rw [Measure.addHaar_smul]; simp [abs_of_pos ht.1]
  rw [← e1, ← e2]
  refine bm_one (hA.const_smul₀ _) (hB.const_smul₀ _) (hAn.smul_set) (hBn.smul_set) ?_
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact hsub a ha b hb

theorem lintegral_eq_layer {F : ℝ → ℝ≥0∞} (hF : Measurable F) (h1 : ∀ x, F x ≤ 1) :
    ∫⁻ x, F x = ∫⁻ w in Ioi (0 : ℝ), volume {x | ENNReal.ofReal w < F x} := by
  have hne : ∀ x, F x ≠ ∞ := fun x => (h1 x).trans_lt ENNReal.one_lt_top |>.ne
  have key := lintegral_eq_lintegral_meas_lt volume (f := fun x => (F x).toReal)
    (ae_of_all _ fun x => ENNReal.toReal_nonneg) hF.ennreal_toReal.aemeasurable
  simp_rw [ENNReal.ofReal_toReal (hne _)] at key
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi fun w hw => ?_
  congr 1
  ext x
  simp only [mem_ofPred_eq]
  exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hw) (hne x)).symm

theorem level_ineq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfs : ∀ w < (1 : ℝ≥0∞), ∃ x, w < f x) (hgs : ∀ w < (1 : ℝ≥0∞), ∃ x, w < g x)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) {w : ℝ} (hw : 0 < w) :
    ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal w < f x} +
      ENNReal.ofReal t * volume {x | ENNReal.ofReal w < g x} ≤
      volume {x | ENNReal.ofReal w < min (h x) 1} := by
  have h1 : (0 : ℝ) < 1 - t := by linarith [ht.2]
  by_cases hw1 : 1 ≤ w
  · have e : ∀ F : ℝ → ℝ≥0∞, (∀ x, F x ≤ 1) → {x | ENNReal.ofReal w < F x} = ∅ := by
      intro F hF
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (hF x).trans (by simpa using hw1)
    rw [e f hf1, e g hg1]; simp
  · rw [not_le] at hw1
    have hwl : ENNReal.ofReal w < 1 := by simpa using hw1
    obtain ⟨a, ha⟩ := hfs _ hwl
    obtain ⟨b, hb⟩ := hgs _ hwl
    refine bm_one_conv ht (measurableSet_lt measurable_const hf) (measurableSet_lt measurable_const hg)
      ⟨a, ha⟩ ⟨b, hb⟩ ?_
    intro x hx y hy
    simp only [mem_ofPred_eq] at hx hy ⊢
    refine lt_min ?_ hwl
    have hwp : ENNReal.ofReal w ≠ 0 := by simpa using hw
    have hwt : ENNReal.ofReal w ≠ ∞ := ENNReal.ofReal_ne_top
    have e : ENNReal.ofReal w ^ (1 - t) * ENNReal.ofReal w ^ t = ENNReal.ofReal w := by
      rw [← ENNReal.rpow_add _ _ hwp hwt]; simp
    calc ENNReal.ofReal w = ENNReal.ofReal w ^ (1 - t) * ENNReal.ofReal w ^ t := e.symm
      _ < f x ^ (1 - t) * g y ^ t := by
        apply ENNReal.mul_lt_mul
        · exact ENNReal.rpow_lt_rpow hx h1
        · exact ENNReal.rpow_lt_rpow hy ht.1
      _ ≤ _ := hfgh x y


theorem amgm_ennreal {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (X Y : ℝ≥0∞) :
    X ^ (1 - t) * Y ^ t ≤ ENNReal.ofReal (1 - t) * X + ENNReal.ofReal t * Y := by
  have h1 : (0 : ℝ) < 1 - t := by linarith [ht.2]
  have p1 : ENNReal.ofReal (1 - t) ≠ 0 := by simpa using h1
  have p2 : ENNReal.ofReal t ≠ 0 := by simpa using ht.1
  by_cases hX : X = ∞
  · subst hX; simp [ENNReal.mul_top p1]
  by_cases hY : Y = ∞
  · subst hY; simp [ENNReal.mul_top p2]
  lift X to ℝ≥0 using hX
  lift Y to ℝ≥0 using hY
  have e1 : (((1 - t).toNNReal : ℝ≥0) : ℝ) = 1 - t := Real.coe_toNNReal _ h1.le
  have e2 : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht.1.le
  have := NNReal.geom_mean_le_arith_mean2_weighted (w₁ := (1 - t).toNNReal) (w₂ := t.toNNReal)
    (p₁ := X) (p₂ := Y) (by ext; simp [e1, e2])
  rw [e1, e2] at this
  have h := (ENNReal.coe_le_coe.2 this)
  rw [ENNReal.coe_add, ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_nonneg _ h1.le, ENNReal.coe_rpow_of_nonneg _ ht.1.le] at h
  exact h

theorem pl_one_normalized {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfs : ∀ w < (1 : ℝ≥0∞), ∃ x, w < f x) (hgs : ∀ w < (1 : ℝ≥0∞), ∃ x, w < g x)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  have hmin : ∫⁻ x, min (h x) 1 ≤ ∫⁻ x, h x := lintegral_mono fun x => min_le_left _ _
  have hL : ∫⁻ x, min (h x) 1 = ∫⁻ w in Ioi (0 : ℝ), volume {x | ENNReal.ofReal w < min (h x) 1} :=
    lintegral_eq_layer (hh.min measurable_const) fun x => min_le_right _ _
  have hlev : ∫⁻ w in Ioi (0 : ℝ), (ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal w < f x} +
      ENNReal.ofReal t * volume {x | ENNReal.ofReal w < g x}) ≤
      ∫⁻ x, min (h x) 1 := by
    rw [hL]
    exact setLIntegral_mono' measurableSet_Ioi fun w hw =>
      level_ineq ht hf hg hf1 hg1 hfs hgs hfgh hw
  have hsplit := le_lintegral_add (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun w => ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal w < f x})
    (fun w => ENNReal.ofReal t * volume {x | ENNReal.ofReal w < g x})
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_eq_layer hf hf1, ← lintegral_eq_layer hg hg1] at hsplit
  exact (amgm_ennreal ht _ _).trans (hsplit.trans (hlev.trans hmin))


theorem pl_one_bdd {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfb : (⨆ x, f x) ≠ ∞) (hgb : (⨆ x, g x) ≠ ∞)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  have h1 : (0 : ℝ) < 1 - t := by linarith [ht.2]
  set a := ⨆ x, f x with ha
  set b := ⨆ x, g x with hb
  by_cases ha0 : a = 0
  · have : ∀ x, f x = 0 := fun x => le_antisymm (ha0 ▸ le_iSup f x) bot_le
    simp [this, ENNReal.zero_rpow_of_pos h1]
  by_cases hb0 : b = 0
  · have : ∀ x, g x = 0 := fun x => le_antisymm (hb0 ▸ le_iSup g x) bot_le
    simp [this, ENNReal.zero_rpow_of_pos ht.1]
  have hc0 : a ^ (1 - t) * b ^ t ≠ 0 := by
    apply mul_ne_zero
    · exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hfb).ne'
    · exact (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hgb).ne'
  have hct : a ^ (1 - t) * b ^ t ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg h1.le hfb)
      (ENNReal.rpow_ne_top_of_nonneg ht.1.le hgb)
  set c := a ^ (1 - t) * b ^ t with hc
  have hfl : ∀ x, f x ≤ a := fun x => le_iSup f x
  have hgl : ∀ x, g x ≤ b := fun x => le_iSup g x
  have key := pl_one_normalized ht (f := fun x => f x / a) (g := fun x => g x / b)
    (h := fun x => h x / c) (hf.div_const _) (hg.div_const _) (hh.div_const _)
    (fun x => by
      rw [ENNReal.div_le_iff ha0 hfb, one_mul]; exact hfl x)
    (fun x => by
      rw [ENNReal.div_le_iff hb0 hgb, one_mul]; exact hgl x)
    (fun w hw => by
      have : w * a < a := by
        calc w * a < 1 * a := (ENNReal.mul_lt_mul_iff_left ha0 hfb).2 hw
          _ = a := one_mul a
      obtain ⟨x, hx⟩ := lt_iSup_iff.1 this
      exact ⟨x, (ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hfb)).2 hx⟩)
    (fun w hw => by
      have : w * b < b := by
        calc w * b < 1 * b := (ENNReal.mul_lt_mul_iff_left hb0 hgb).2 hw
          _ = b := one_mul b
      obtain ⟨x, hx⟩ := lt_iSup_iff.1 this
      exact ⟨x, (ENNReal.lt_div_iff_mul_lt (Or.inl hb0) (Or.inl hgb)).2 hx⟩)
    (fun x y => by
      rw [ENNReal.div_rpow_of_nonneg _ _ h1.le, ENNReal.div_rpow_of_nonneg _ _ ht.1.le]
      simp only [div_eq_mul_inv]
      calc f x ^ (1 - t) * (a ^ (1 - t))⁻¹ * (g y ^ t * (b ^ t)⁻¹)
          = (f x ^ (1 - t) * g y ^ t) * ((a ^ (1 - t))⁻¹ * (b ^ t)⁻¹) := by ring
        _ = (f x ^ (1 - t) * g y ^ t) * c⁻¹ := by
            rw [hc, ENNReal.mul_inv (Or.inl (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hfb).ne')
              (Or.inl (ENNReal.rpow_ne_top_of_nonneg h1.le hfb))]
        _ ≤ h _ * c⁻¹ := by gcongr; exact hfgh x y)
  simp only [div_eq_mul_inv] at key
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 ha0),
    lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hb0),
    lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc0),
    ENNReal.mul_rpow_of_nonneg _ _ h1.le, ENNReal.mul_rpow_of_nonneg _ _ ht.1.le,
    ENNReal.inv_rpow, ENNReal.inv_rpow] at key
  have e : ((∫⁻ x, f x) ^ (1 - t) * (a ^ (1 - t))⁻¹) * ((∫⁻ x, g x) ^ t * (b ^ t)⁻¹) =
      ((∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t) * c⁻¹ := by
    rw [hc, ENNReal.mul_inv (Or.inl (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hfb).ne')
      (Or.inl (ENNReal.rpow_ne_top_of_nonneg h1.le hfb))]
    ring
  rw [e] at key
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.inv_ne_zero.2 hct) (ENNReal.inv_ne_top.2 hc0)).1 key


theorem lintegral_trunc_iSup {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ⨆ n : ℕ, ∫⁻ x, min (f x) n := by
  rw [← lintegral_iSup (fun n => hf.min measurable_const)]
  · congr 1; ext x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast]; simp
  · intro m n hmn x
    exact min_le_min le_rfl (by exact_mod_cast hmn)

theorem pl_one {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  have h1 : (0 : ℝ) < 1 - t := by linarith [ht.2]
  have hb : ∀ (F : ℝ → ℝ≥0∞) (n : ℕ), (⨆ x, min (F x) n) ≠ ∞ := fun F n =>
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (iSup_le fun x => min_le_right _ _)
  have hmono : ∀ F : ℝ → ℝ≥0∞, Monotone fun n : ℕ => ∫⁻ x, min (F x) n := fun F m n hmn =>
    lintegral_mono fun x => min_le_min le_rfl (by exact_mod_cast hmn)
  have hn : ∀ n : ℕ, (∫⁻ x, min (f x) n) ^ (1 - t) * (∫⁻ x, min (g x) n) ^ t ≤ ∫⁻ x, h x :=
    fun n => pl_one_bdd ht (hf.min measurable_const) (hg.min measurable_const) hh (hb f n) (hb g n)
      fun x y => le_trans (by gcongr <;> first | exact min_le_left _ _ | exact ht.1.le ) (hfgh x y)
  rw [lintegral_trunc_iSup hf, lintegral_trunc_iSup hg,
    (Monotone.map_iSup_of_continuousAt (f := fun z : ℝ≥0∞ => z ^ (1 - t))
      (ENNReal.continuous_rpow_const.continuousAt) (fun a b hab => ENNReal.rpow_le_rpow hab h1.le)
      (ENNReal.zero_rpow_of_pos h1)),
    (Monotone.map_iSup_of_continuousAt (f := fun z : ℝ≥0∞ => z ^ t)
      (ENNReal.continuous_rpow_const.continuousAt) (fun a b hab => ENNReal.rpow_le_rpow hab ht.1.le)
      (ENNReal.zero_rpow_of_pos ht.1)) ]
  rw [ENNReal.iSup_mul]
  refine iSup_le fun m => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  refine le_trans ?_ (hn (max m n))
  have hm := hmono f (le_max_left m n)
  have hm' := hmono g (le_max_right m n)
  gcongr
  exact ht.1.le


/-- The Prekopa-Leindler property (ENNReal form) for a measure on a real vector space. -/
def PLProp {X : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X] (μ : Measure X) : Prop :=
  ∀ t ∈ Ioo (0 : ℝ) 1, ∀ f g h : X → ℝ≥0∞, Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) →
    (∫⁻ x, f x ∂μ) ^ (1 - t) * (∫⁻ x, g x ∂μ) ^ t ≤ ∫⁻ x, h x ∂μ

theorem plProp_real : PLProp (volume : Measure ℝ) := by
  intro t ht f g h hf hg hh hfgh
  exact pl_one ht hf hg hh fun x y => by simpa using hfgh x y

theorem plProp_prod {Y : Type*} [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y]
    {μ : Measure Y} [SFinite μ] (hY : PLProp μ) :
    PLProp ((volume : Measure ℝ).prod μ) := by
  intro t ht f g h hf hg hh hfgh
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.aemeasurable,
    lintegral_prod _ hh.aemeasurable]
  refine plProp_real t ht _ _ _ hf.lintegral_prod_right' hg.lintegral_prod_right'
    hh.lintegral_prod_right' fun s s' => ?_
  refine hY t ht _ _ _ (hf.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left)
    (hh.comp measurable_prodMk_left) fun y y' => ?_
  simpa using hfgh (s, y) (s', y')

theorem plProp_transfer {X Z : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Z] [Module ℝ Z] [MeasurableSpace Z] {μX : Measure X} {μZ : Measure Z}
    (e : Z ≃ᵐ X) (he : MeasurePreserving e μZ μX)
    (hlin : ∀ (t : ℝ) (z z' : Z), e ((1 - t) • z + t • z') = (1 - t) • e z + t • e z')
    (hX : PLProp μX) : PLProp μZ := by
  intro t ht f g h hf hg hh hfgh
  have hint : ∀ F : Z → ℝ≥0∞, ∫⁻ z, F z ∂μZ = ∫⁻ x, F (e.symm x) ∂μX := by
    intro F
    have := he.lintegral_comp_emb e.measurableEmbedding (fun x => F (e.symm x))
    simpa using this
  rw [hint f, hint g, hint h]
  refine hX t ht _ _ _ (hf.comp e.symm.measurable) (hg.comp e.symm.measurable)
    (hh.comp e.symm.measurable) fun x y => ?_
  have h1 : e.symm ((1 - t) • x + t • y) = (1 - t) • e.symm x + t • e.symm y := by
    apply e.injective
    rw [hlin]; simp
  simp only [h1]
  exact hfgh _ _

theorem plProp_pi (k : ℕ) : PLProp (volume : Measure (Fin k → ℝ)) := by
  induction k with
  | zero =>
    intro t ht f g h hf hg hh hfgh
    rw [volume_pi, Measure.pi_of_empty]
    simp only [lintegral_dirac]
    have := hfgh (fun a => isEmptyElim a) (fun a => isEmptyElim a)
    rwa [Subsingleton.elim ((1 - t) • (fun a : Fin 0 => isEmptyElim a : Fin 0 → ℝ) +
      t • (fun a : Fin 0 => isEmptyElim a : Fin 0 → ℝ)) (fun a => isEmptyElim a)] at this
  | succ n ih =>
    refine plProp_transfer (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ?_ (plProp_prod ih)
    intro t z z'
    ext i
    · simp [MeasurableEquiv.piFinSuccAbove]
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]


/-- The Prekopa-Leindler property extends to the endpoints `t = 0` and `t = 1`. -/
theorem plProp_Icc {X : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    {μ : Measure X} (hX : PLProp μ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {f g h : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x ∂μ) ^ (1 - t) * (∫⁻ x, g x ∂μ) ^ t ≤ ∫⁻ x, h x ∂μ := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · subst h0
    simp only [sub_zero, ENNReal.rpow_one, ENNReal.rpow_zero, mul_one, zero_smul, add_zero,
      one_smul] at hfgh ⊢
    exact lintegral_mono fun x => hfgh x x
  rcases eq_or_lt_of_le ht.2 with h1 | h1
  · subst h1
    simp only [sub_self, ENNReal.rpow_one, ENNReal.rpow_zero, one_mul, zero_smul, zero_add,
      one_smul] at hfgh ⊢
    exact lintegral_mono fun x => hfgh x x
  exact hX t ⟨h0, h1⟩ f g h hf hg hh hfgh

theorem plProp_real_valued {X : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    {μ : Measure X} (hX : PLProp μ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {f g h : X → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y))
    (hfi : Integrable f μ) (hgi : Integrable g μ) (hhi : Integrable h μ) :
    (∫ x, f x ∂μ) ^ (1 - t) * (∫ x, g x ∂μ) ^ t ≤ ∫ x, h x ∂μ := by
  have h1t : 0 ≤ 1 - t := by linarith [ht.2]
  have hh0 : ∀ z, 0 ≤ h z := by
    intro z
    have := hfgh z z
    rw [← add_smul, sub_add_cancel, one_smul] at this
    exact le_trans (mul_nonneg (Real.rpow_nonneg (hf0 z) _) (Real.rpow_nonneg (hg0 z) _)) this
  have key := plProp_Icc hX ht (f := fun x => ENNReal.ofReal (f x)) (g := fun x => ENNReal.ofReal (g x))
    (h := fun x => ENNReal.ofReal (h x)) hf.ennreal_ofReal hg.ennreal_ofReal hh.ennreal_ofReal
    (fun x y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (hf0 x) h1t, ENNReal.ofReal_rpow_of_nonneg (hg0 y) ht.1,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf0 x) _)]
      exact ENNReal.ofReal_le_ofReal (hfgh x y))
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ hf0),
    ← ofReal_integral_eq_lintegral_ofReal hgi (ae_of_all _ hg0),
    ← ofReal_integral_eq_lintegral_ofReal hhi (ae_of_all _ hh0),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hf0) h1t,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg hg0) ht.1,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg hf0) _),
    ENNReal.ofReal_le_ofReal_iff (integral_nonneg hh0)] at key
  exact key

/-- Prekopa-Leindler on `ℝ^k` (Euclidean space), `ℝ≥0∞`-valued form, no integrability needed. -/
theorem prekopaLeindler_lintegral (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {f g h : EuclideanSpace ℝ (Fin k) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) :
    (∫⁻ x, f x) ^ (1 - t) * (∫⁻ x, g x) ^ t ≤ ∫⁻ x, h x := by
  refine plProp_Icc ?_ ht hf hg hh hfgh
  refine plProp_transfer (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin k)) ?_ (plProp_pi k)
  intro t z z'
  simp

/-- **Prekopa-Leindler inequality** on `ℝ^k`. -/
theorem prekopaLeindler (k : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {f g h : EuclideanSpace ℝ (Fin k) → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y))
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h) :
    (∫ x, f x) ^ (1 - t) * (∫ x, g x) ^ t ≤ ∫ x, h x := by
  refine plProp_real_valued ?_ ht hf hg hh hf0 hg0 hfgh hfi hgi hhi
  refine plProp_transfer (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin k)) ?_ (plProp_pi k)
  intro t z z'
  simp

/-- **Prekopa-Leindler inequality** in dimension one. -/
theorem prekopaLeindler_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {f g h : ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y))
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h) :
    (∫ x, f x) ^ (1 - t) * (∫ x, g x) ^ t ≤ ∫ x, h x :=
  plProp_real_valued plProp_real ht hf hg hh hf0 hg0 (fun x y => by simpa using hfgh x y)
    hfi hgi hhi

end DGPS.FiniteN.Tools
