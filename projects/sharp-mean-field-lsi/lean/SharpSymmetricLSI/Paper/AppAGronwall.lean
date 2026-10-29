import Mathlib

/-!
# A Grönwall lemma for the kernel `(t - u)^{-1/2}` (Lemma A.1, absorption argument)

If `0 ≤ e ≤ M` is continuous on `[0, T]`, `e 0 ≤ a` and
`e t ≤ a + K ∫₀ᵗ (t - u)^{-1/2} e(u) du` for `0 < t ≤ T`, then `e t ≤ C(K, T) a` on `[0, T]`
(`singular_gronwall`). As in the manuscript: choose `δ` with `2K√δ ≤ 1/2`, absorb the integral
over the last window of length `δ` after taking the supremum, and iterate over `⌈T/δ⌉` windows.
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace SharpLSI

/-- `∫_{t-δ}^{t} (t-u)^{-1/2} du = 2√δ`. -/
theorem integral_rsqrt_window {t δ : ℝ} (hδ : 0 < δ) :
    ∫ u in Ioo (t - δ) t, (t - u) ^ (-(1 : ℝ) / 2) = 2 * Real.sqrt δ := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_left (fun s => s ^ (-(1 : ℝ) / 2)) t]
  simp only [sub_self, sub_sub_cancel]
  rw [integral_rpow (Or.inl (by norm_num))]
  rw [Real.sqrt_eq_rpow, Real.zero_rpow (by norm_num)]
  norm_num
  ring

theorem integrableOn_rsqrt_window {t δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun u => (t - u) ^ (-(1 : ℝ) / 2)) (Ioo (t - δ) t) := by
  by_contra h
  have := integral_rsqrt_window (t := t) hδ
  rw [integral_undef h] at this
  have : 0 < 2 * Real.sqrt δ := by positivity
  linarith

theorem integrableOn_rsqrt {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u => (t - u) ^ (-(1 : ℝ) / 2)) (Ioo 0 t) := by
  have := integrableOn_rsqrt_window (t := t) ht
  simpa using this

/-- The iteration constants. -/
noncomputable def gronC (K T δ : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => 2 * (gronC K T δ n + 1 + K * T * δ ^ (-(1 : ℝ) / 2) * gronC K T δ n)

theorem gronC_nonneg {K T δ : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T) (hδ : 0 < δ) :
    ∀ n, 0 ≤ gronC K T δ n
  | 0 => by simp [gronC]
  | n + 1 => by
    have := gronC_nonneg hK hT hδ n
    simp only [gronC]; positivity

/-- The window length. -/
noncomputable def gronδ (K : ℝ) : ℝ := 1 / (16 * (K + 1) ^ 2)

theorem gronδ_pos {K : ℝ} (hK : 0 ≤ K) : 0 < gronδ K := by unfold gronδ; positivity

theorem two_K_sqrt_gronδ {K : ℝ} (hK : 0 ≤ K) : K * (2 * Real.sqrt (gronδ K)) ≤ 1 / 2 := by
  unfold gronδ
  rw [show (1 : ℝ) / (16 * (K + 1) ^ 2) = (1 / (4 * (K + 1))) ^ 2 by field_simp; ring,
    Real.sqrt_sq (by positivity)]
  rw [show K * (2 * (1 / (4 * (K + 1)))) = K / (2 * (K + 1)) by field_simp; ring,
    div_le_iff₀ (by positivity)]
  linarith

/-- The Grönwall constant `C(K, T)`. -/
noncomputable def gronwallConst (K T : ℝ) : ℝ := gronC K T (gronδ K) ⌈T / gronδ K⌉₊

theorem gronwallConst_nonneg {K T : ℝ} (hK : 0 ≤ K) (hT : 0 ≤ T) : 0 ≤ gronwallConst K T :=
  gronC_nonneg hK hT (gronδ_pos hK) _

/-- **Singular Grönwall lemma.** -/
theorem singular_gronwall {e : ℝ → ℝ} {a K T M : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a) (hT : 0 ≤ T)
    (he0 : ∀ t ∈ Icc 0 T, 0 ≤ e t) (heM : ∀ t ∈ Icc 0 T, e t ≤ M)
    (hec : ContinuousOn e (Icc 0 T)) (h0 : e 0 ≤ a)
    (h : ∀ t ∈ Ioc 0 T, e t ≤ a + K * ∫ u in Ioo 0 t, (t - u) ^ (-(1 : ℝ) / 2) * e u) :
    ∀ t ∈ Icc 0 T, e t ≤ gronwallConst K T * a := by
  set δ := gronδ K with hδdef
  have hδ : 0 < δ := gronδ_pos hK
  set c := gronC K T δ with hcdef
  have hc0 : ∀ n, 0 ≤ c n := gronC_nonneg hK hT hδ
  -- the windows
  have key : ∀ n : ℕ, ∀ t ∈ Icc 0 T, t ≤ n * δ → e t ≤ c n * a := by
    intro n
    induction n with
    | zero =>
      intro t ht htn
      have : t = 0 := le_antisymm (by simpa using htn) ht.1
      subst this
      simpa [c, gronC] using h0
    | succ n ih =>
      set Wn := {t | t ∈ Icc 0 T ∧ t ≤ (n + 1 : ℕ) * δ} with hWn
      have hW0 : (0 : ℝ) ∈ Wn := ⟨⟨le_rfl, hT⟩, by positivity⟩
      have hbdd : BddAbove (e '' Wn) := ⟨M, by rintro _ ⟨t, ht, rfl⟩; exact heM t ht.1⟩
      set S := sSup (e '' Wn) with hS
      have heS : ∀ t ∈ Wn, e t ≤ S := fun t ht => le_csSup hbdd ⟨t, ht, rfl⟩
      have hS0 : 0 ≤ S := (he0 0 ⟨le_rfl, hT⟩).trans (heS 0 hW0)
      set A := c n * a + a * (1 + K * T * δ ^ (-(1 : ℝ) / 2) * c n) with hA
      have hbound : ∀ t ∈ Wn, e t ≤ A + S / 2 := by
        intro t ht
        by_cases htn : t ≤ n * δ
        · have := ih t ht.1 htn
          have : 0 ≤ a * (1 + K * T * δ ^ (-(1 : ℝ) / 2) * c n) := by
            have := hc0 n; positivity
          linarith
        · push Not at htn
          have ht0 : 0 < t := lt_of_le_of_lt (by positivity) htn
          have hmain := h t ⟨ht0, ht.1.2⟩
          -- bound the integrand
          set b : ℝ → ℝ := fun u => δ ^ (-(1 : ℝ) / 2) * (c n * a) +
            S * (Ioo (t - δ) t).indicator (fun u => (t - u) ^ (-(1 : ℝ) / 2)) u with hb
          have hbint : IntegrableOn b (Ioo 0 t) := by
            refine (integrableOn_const (by simp) enorm_ne_top).add ?_
            refine (((integrableOn_rsqrt_window (t := t) hδ).integrable_indicator
              measurableSet_Ioo).const_mul S).integrableOn
          have hle : ∀ u ∈ Ioo 0 t, (t - u) ^ (-(1 : ℝ) / 2) * e u ≤ b u := by
            intro u hu
            have hpos : 0 < t - u := sub_pos.2 hu.2
            have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.le.trans ht.1.2⟩
            by_cases hud : u ≤ t - δ
            · have h1 : (t - u) ^ (-(1 : ℝ) / 2) ≤ δ ^ (-(1 : ℝ) / 2) :=
                Real.rpow_le_rpow_of_nonpos hδ (by linarith) (by norm_num)
              have h2 : e u ≤ c n * a := ih u hu' (by
                have := ht.2; push_cast at this ⊢; linarith)
              have h3 : 0 ≤ S * (Ioo (t - δ) t).indicator
                  (fun u => (t - u) ^ (-(1 : ℝ) / 2)) u :=
                mul_nonneg hS0 (indicator_nonneg (fun w hw => Real.rpow_nonneg (sub_pos.2 hw.2).le _) _)
              calc (t - u) ^ (-(1 : ℝ) / 2) * e u ≤ δ ^ (-(1 : ℝ) / 2) * (c n * a) :=
                    mul_le_mul h1 h2 (he0 u hu') (Real.rpow_nonneg hδ.le _)
                _ ≤ b u := by simp only [hb]; linarith
            · push Not at hud
              have hmem : u ∈ Ioo (t - δ) t := ⟨hud, hu.2⟩
              have h2 : e u ≤ S := heS u ⟨hu', hu.2.le.trans ht.2⟩
              simp only [hb, indicator_of_mem hmem]
              have : 0 ≤ δ ^ (-(1 : ℝ) / 2) * (c n * a) := by have := hc0 n; positivity
              nlinarith [Real.rpow_nonneg hpos.le (-(1 : ℝ) / 2), he0 u hu']
          have hint_le : ∫ u in Ioo 0 t, (t - u) ^ (-(1 : ℝ) / 2) * e u ≤
              T * δ ^ (-(1 : ℝ) / 2) * (c n * a) + S * (2 * Real.sqrt δ) := by
            have hfi : IntegrableOn (fun u => (t - u) ^ (-(1 : ℝ) / 2) * e u) (Ioo 0 t) := by
              refine Integrable.mono' ((integrableOn_rsqrt ht0).mul_const M) ?_ ?_
              · exact ((continuousOn_const.sub continuousOn_id).rpow_const
                  (fun u hu => Or.inl (sub_pos.2 hu.2).ne')).mul
                  (hec.mono fun u hu => ⟨hu.1.le, hu.2.le.trans ht.1.2⟩)
                  |>.aestronglyMeasurable measurableSet_Ioo
              · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
                have hu' : u ∈ Icc 0 T := ⟨hu.1.le, hu.2.le.trans ht.1.2⟩
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (sub_pos.2 hu.2).le _),
                  abs_of_nonneg (he0 u hu')]
                exact mul_le_mul_of_nonneg_left (heM u hu')
                  (Real.rpow_nonneg (sub_pos.2 hu.2).le _)
            refine (setIntegral_mono_on hfi hbint measurableSet_Ioo hle).trans ?_
            show ∫ u in Ioo 0 t, (δ ^ (-(1 : ℝ) / 2) * (c n * a) +
              S * (Ioo (t - δ) t).indicator (fun u => (t - u) ^ (-(1 : ℝ) / 2)) u) ≤ _
            rw [integral_add (f := fun _ => δ ^ (-(1 : ℝ) / 2) * (c n * a))
              (g := fun u => S * (Ioo (t - δ) t).indicator (fun u => (t - u) ^ (-(1 : ℝ) / 2)) u)
              (integrableOn_const (by simp) enorm_ne_top)
              ((((integrableOn_rsqrt_window (t := t) hδ).integrable_indicator
              measurableSet_Ioo).const_mul S).integrableOn), setIntegral_const,
              integral_const_mul]
            refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ hS0)
            · rw [Real.volume_real_Ioo, smul_eq_mul]
              have := hc0 n
              have : max (t - 0) 0 ≤ T := by
                rw [sub_zero, max_eq_left ht0.le]; exact ht.1.2
              have hX : 0 ≤ δ ^ (-(1 : ℝ) / 2) * (c n * a) :=
                mul_nonneg (Real.rpow_nonneg hδ.le _) (mul_nonneg (hc0 n) ha)
              calc max (t - 0) 0 * (δ ^ (-(1 : ℝ) / 2) * (c n * a))
                  ≤ T * (δ ^ (-(1 : ℝ) / 2) * (c n * a)) := mul_le_mul_of_nonneg_right this hX
                _ = T * δ ^ (-(1 : ℝ) / 2) * (c n * a) := by ring
            · rw [← integral_rsqrt_window (t := t) hδ]
              refine (setIntegral_mono_set ?_ ?_ (Eventually.of_forall fun _ _ => mem_univ _ :
                Ioo 0 t ≤ᵐ[volume] univ)).trans ?_
              · exact ((integrableOn_rsqrt_window (t := t) hδ).integrable_indicator
                  measurableSet_Ioo).integrableOn
              · exact Eventually.of_forall fun u => indicator_nonneg (fun w hw => Real.rpow_nonneg (sub_pos.2 hw.2).le _) _
              · rw [setIntegral_univ, integral_indicator measurableSet_Ioo]
          have hK2 := two_K_sqrt_gronδ hK
          calc e t ≤ a + K * (T * δ ^ (-(1 : ℝ) / 2) * (c n * a) + S * (2 * Real.sqrt δ)) :=
                hmain.trans (by gcongr)
            _ ≤ A + S / 2 := by
                have : K * (S * (2 * Real.sqrt δ)) ≤ S / 2 := by
                  rw [show K * (S * (2 * Real.sqrt δ)) = S * (K * (2 * Real.sqrt δ)) by ring]
                  nlinarith
                have hcn := hc0 n
                nlinarith [mul_nonneg hcn ha]
      have hSle : S ≤ A + S / 2 :=
        csSup_le ⟨e 0, 0, hW0, rfl⟩ (by rintro _ ⟨t, ht, rfl⟩; exact hbound t ht)
      intro t ht htn
      calc e t ≤ S := heS t ⟨ht, htn⟩
        _ ≤ 2 * A := by linarith
        _ = c (n + 1) * a := by simp only [hA, c, gronC]; ring
  intro t ht
  refine key ⌈T / δ⌉₊ t ht ?_
  calc t ≤ T := ht.2
    _ = T / δ * δ := by field_simp
    _ ≤ ⌈T / δ⌉₊ * δ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) hδ.le

end SharpLSI
