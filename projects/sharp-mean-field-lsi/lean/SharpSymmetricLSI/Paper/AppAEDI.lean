import Mathlib

/-!
# (4.8) ⇒ (4.10): exponential decay and the tail bound from an energy–dissipation inequality

Abstract real-variable lemmas. `G, D : ℝ → ℝ≥0∞` with `G` finite on `[0,∞)`,
* (EDI) `G t + ∫_s^t D ≤ G s` for `0 ≤ s ≤ t`,
* (PL) `2r G u ≤ D u` for `u ≥ 0`, `r > 0`.
Then `G t ≤ G s e^{-2r(t-s)}` and `∫_t^∞ √D ≤ √(2/r) √(G t)`.
No measurability of `G` or `D` is assumed.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI

section EDI

variable {G D : ℝ → ℝ≥0∞}

theorem edi_antitone
    (h48 : ∀ s t, 0 ≤ s → s ≤ t → G t + ∫⁻ u in Icc s t, D u ≤ G s)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : G t ≤ G s :=
  le_self_add.trans (h48 s t hs hst)

theorem edi_step {c : ℝ≥0∞}
    (h48 : ∀ s t, 0 ≤ s → s ≤ t → G t + ∫⁻ u in Icc s t, D u ≤ G s)
    (hPL : ∀ u, 0 ≤ u → c * G u ≤ D u) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    G t + c * G t * ENNReal.ofReal (t - s) ≤ G s := by
  calc G t + c * G t * ENNReal.ofReal (t - s) = G t + ∫⁻ _u in Icc s t, c * G t := by
        rw [setLIntegral_const, Real.volume_Icc]
    _ ≤ G t + ∫⁻ u in Icc s t, D u := by
        refine add_le_add le_rfl (setLIntegral_mono' measurableSet_Icc fun u hu => ?_)
        exact (mul_le_mul_right (edi_antitone h48 (hs.trans hu.1) hu.2) c).trans
          (hPL u (hs.trans hu.1))
    _ ≤ G s := h48 s t hs hst

/-- **Exponential decay.** -/
theorem edi_decay {r : ℝ} (hr : 0 < r) (hfin : ∀ u, 0 ≤ u → G u ≠ ⊤)
    (h48 : ∀ s t, 0 ≤ s → s ≤ t → G t + ∫⁻ u in Icc s t, D u ≤ G s)
    (hPL : ∀ u, 0 ≤ u → ENNReal.ofReal (2 * r) * G u ≤ D u) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) : G t ≤ G s * ENNReal.ofReal (Real.exp (-(2 * r * (t - s)))) := by
  set g : ℝ → ℝ := fun u => (G u).toReal with hg
  have hG : ∀ u, 0 ≤ u → G u = ENNReal.ofReal (g u) := fun u hu =>
    (ENNReal.ofReal_toReal (hfin u hu)).symm
  have hg0 : ∀ u, 0 ≤ g u := fun u => ENNReal.toReal_nonneg
  have hstep : ∀ a b, s ≤ a → a ≤ b → g b * (1 + 2 * r * (b - a)) ≤ g a := by
    intro a b ha hab
    have h0a : 0 ≤ a := hs.trans ha
    have h0b : 0 ≤ b := h0a.trans hab
    have := edi_step h48 hPL h0a hab
    rw [hG b h0b, hG a h0a, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (hg0 b) (by
        have := hg0 b; have : 0 ≤ b - a := by linarith
        positivity)] at this
    have h2 := (ENNReal.ofReal_le_ofReal_iff (hg0 a)).1 this
    nlinarith
  set x := 2 * r * (t - s) with hx
  have hx0 : 0 ≤ x := by have : 0 ≤ t - s := by linarith
                         positivity
  have hn : ∀ n : ℕ, g t * (1 + x / n) ^ n ≤ g s := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      simp only [pow_zero, mul_one]
      have := hstep s t le_rfl hst
      have h1 : g t ≤ g t * (1 + 2 * r * (t - s)) :=
        le_mul_of_one_le_right (hg0 t) (by have : 0 ≤ t - s := by linarith
                                           nlinarith)
      linarith
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hpos
      set δ := (t - s) / n with hδ
      have hδ0 : 0 ≤ δ := div_nonneg (by linarith) hnpos.le
      have hk : ∀ k : ℕ, k ≤ n → g (s + k * δ) * (1 + x / n) ^ k ≤ g s := by
        intro k
        induction k with
        | zero => intro _; simp
        | succ k ih =>
          intro hk
          have hle := ih (by omega)
          have hxn : x / n = 2 * r * ((s + (k + 1 : ℕ) * δ) - (s + k * δ)) := by
            push_cast; rw [hx, hδ]; field_simp; ring
          have hs1 := hstep (s + k * δ) (s + (k + 1 : ℕ) * δ)
            (by have : 0 ≤ (k : ℝ) * δ := by positivity
                linarith)
            (by push_cast; nlinarith)
          rw [← hxn] at hs1
          have hp : 0 ≤ (1 + x / n) ^ k := by positivity
          calc g (s + (k + 1 : ℕ) * δ) * (1 + x / n) ^ (k + 1)
              = (g (s + (k + 1 : ℕ) * δ) * (1 + x / n)) * (1 + x / n) ^ k := by ring
            _ ≤ g (s + k * δ) * (1 + x / n) ^ k := mul_le_mul_of_nonneg_right hs1 hp
            _ ≤ g s := hle
      have := hk n le_rfl
      have e : s + (n : ℝ) * δ = t := by rw [hδ]; field_simp; ring
      rwa [e] at this
  have hlim : Tendsto (fun n : ℕ => g s / (1 + x / n) ^ n) atTop (𝓝 (g s / Real.exp x)) :=
    tendsto_const_nhds.div (Real.tendsto_one_add_div_pow_exp x) (Real.exp_pos x).ne'
  have hle : g t ≤ g s / Real.exp x := by
    refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have hp : 0 < (1 + x / n) ^ n := by positivity
    rw [le_div_iff₀ hp]; exact hn n
  rw [hG t (hs.trans hst), hG s hs, ← ENNReal.ofReal_mul (hg0 s), Real.exp_neg, ← div_eq_mul_inv]
  exact ENNReal.ofReal_le_ofReal hle

/-- The tail of the dissipation. -/
theorem edi_tail_le
    (h48 : ∀ s t, 0 ≤ s → s ≤ t → G t + ∫⁻ u in Icc s t, D u ≤ G s) {v : ℝ} (hv : 0 ≤ v) :
    ∫⁻ u in Ici v, D u ≤ G v := by
  have hsub : Ici v ⊆ ⋃ n : ℕ, Icc v (v + n) := fun u hu => by
    obtain ⟨n, hn⟩ := exists_nat_ge (u - v)
    exact mem_iUnion.2 ⟨n, hu, by linarith⟩
  refine (lintegral_mono_set hsub).trans ?_
  rw [setLIntegral_iUnion_of_directed _ (Monotone.directed_le fun m n hmn =>
    Icc_subset_Icc le_rfl (by have : (m : ℝ) ≤ n := by exact_mod_cast hmn
                              linarith))]
  exact iSup_le fun n => le_add_self.trans (h48 v (v + n) hv (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith))

theorem lintegral_exp_neg_Ioi {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ∫⁻ u in Ioi t, ENNReal.ofReal (r * Real.exp (-(r * (u - t)))) = 1 := by
  have e : ∀ u, r * Real.exp (-(r * (u - t))) = r * Real.exp (r * t) * Real.exp (-r * u) :=
    fun u => by rw [mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [e]
  have hi : IntegrableOn (fun u => r * Real.exp (r * t) * Real.exp (-r * u)) (Ioi t) :=
    (integrableOn_exp_mul_Ioi (by linarith) t).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun u => by positivity),
    integral_const_mul, integral_exp_mul_Ioi (by linarith)]
  rw [show r * Real.exp (r * t) * (-Real.exp (-r * t) / -r) =
      Real.exp (r * t) * Real.exp (-r * t) by field_simp, ← Real.exp_add]
  simp

theorem exp_weight_eq {r : ℝ} (hr : 0 < r) {t u : ℝ} (htu : t ≤ u) :
    ENNReal.ofReal (Real.exp (r * (u - t))) =
      1 + ∫⁻ v in Ioc t u, ENNReal.ofReal (r * Real.exp (r * (v - t))) := by
  have hd : ∀ v ∈ uIcc t u, HasDerivAt (fun v => Real.exp (r * (v - t)))
      (r * Real.exp (r * (v - t))) v := fun v _ => by
    have := ((hasDerivAt_id v).sub_const t).const_mul r |>.exp
    simpa [mul_comm] using this
  have hint : IntervalIntegrable (fun v => r * Real.exp (r * (v - t))) volume t u :=
    (by fun_prop : Continuous fun v => r * Real.exp (r * (v - t))).intervalIntegrable _ _
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_of_le htu] at hI
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((by fun_prop : Continuous fun v => r * Real.exp (r * (v - t))).integrableOn_Ioc)
    (Eventually.of_forall fun v => by positivity), hI]
  simp only [sub_self, mul_zero, Real.exp_zero]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
    (by have : 0 ≤ r * (u - t) := by nlinarith
        linarith [Real.add_one_le_exp (r * (u - t))])]
  congr 1; ring

/-- `∫_t^∞ D w ≤ 2 G t` for the weight `w = e^{r(u-t)}` and a measurable `D' ≤ D`. -/
theorem edi_weighted_le {r : ℝ} (hr : 0 < r) (hfin : ∀ u, 0 ≤ u → G u ≠ ⊤)
    (h48 : ∀ s t, 0 ≤ s → s ≤ t → G t + ∫⁻ u in Icc s t, D u ≤ G s)
    (hPL : ∀ u, 0 ≤ u → ENNReal.ofReal (2 * r) * G u ≤ D u) {t : ℝ} (ht : 0 ≤ t)
    {D' : ℝ → ℝ≥0∞} (hD'm : Measurable D') (hD'le : ∀ u, D' u ≤ D u) :
    ∫⁻ u in Ioi t, D' u * ENNReal.ofReal (Real.exp (r * (u - t))) ≤ 2 * G t := by
  set k : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (r * Real.exp (r * (v - t))) with hk
  have hkm : Measurable k := by
    refine ENNReal.measurable_ofReal.comp ?_; fun_prop
  -- split the weight
  have e1 : ∫⁻ u in Ioi t, D' u * ENNReal.ofReal (Real.exp (r * (u - t))) =
      ∫⁻ u in Ioi t, (D' u + ∫⁻ v in Ioi t, D' u * (Iic u).indicator k v) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    rw [exp_weight_eq hr (le_of_lt hu), mul_add, mul_one,
      lintegral_const_mul _ (hkm.indicator measurableSet_Iic), setLIntegral_indicator measurableSet_Iic,
      inter_comm, Ioi_inter_Iic]
  have hF : Measurable (Function.uncurry fun u v => D' u * (Iic u).indicator k v) := by
    have e : (Function.uncurry fun u v => D' u * (Iic u).indicator k v) =
        fun p : ℝ × ℝ => D' p.1 * ({q : ℝ × ℝ | q.2 ≤ q.1}.indicator (fun q => k q.2) p) := by
      funext p; simp [Set.indicator, Function.uncurry]
    rw [e]
    exact (hD'm.comp measurable_fst).mul ((hkm.comp measurable_snd).indicator
      (measurableSet_le measurable_snd measurable_fst))
  rw [e1, lintegral_add_left (hD'm), lintegral_lintegral_swap hF.aemeasurable]
  -- the first part
  have hA : ∫⁻ u in Ioi t, D' u ≤ G t :=
    ((lintegral_mono_set Ioi_subset_Ici_self).trans (lintegral_mono fun u => hD'le u)).trans
      (edi_tail_le h48 ht)
  -- the second part
  have hB : ∫⁻ v in Ioi t, ∫⁻ u in Ioi t, D' u * (Iic u).indicator k v ≤ G t := by
    have hpt : ∀ v ∈ Ioi t, ∫⁻ u in Ioi t, D' u * (Iic u).indicator k v ≤
        G t * ENNReal.ofReal (r * Real.exp (-(r * (v - t)))) := by
      intro v hv
      have hv0 : 0 ≤ v := ht.trans hv.le
      have e : ∀ u, D' u * (Iic u).indicator k v = (Ici v).indicator (fun u => D' u * k v) u :=
        fun u => by
          by_cases h : v ≤ u
          · simp [Set.indicator, h]
          · simp [Set.indicator, h]
      simp_rw [e]
      rw [setLIntegral_indicator measurableSet_Ici, lintegral_mul_const _ hD'm]
      calc (∫⁻ u in Ici v ∩ Ioi t, D' u) * k v ≤ G v * k v := by
            gcongr
            exact ((lintegral_mono_set inter_subset_left).trans
              (lintegral_mono fun u => hD'le u)).trans (edi_tail_le h48 hv0)
        _ ≤ (G t * ENNReal.ofReal (Real.exp (-(2 * r * (v - t))))) * k v := by
            gcongr; exact edi_decay hr hfin h48 hPL ht hv.le
        _ = G t * ENNReal.ofReal (r * Real.exp (-(r * (v - t)))) := by
            rw [hk, mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
            congr 2
            rw [mul_left_comm, ← Real.exp_add]; ring_nf
    calc ∫⁻ v in Ioi t, ∫⁻ u in Ioi t, D' u * (Iic u).indicator k v
        ≤ ∫⁻ v in Ioi t, G t * ENNReal.ofReal (r * Real.exp (-(r * (v - t)))) :=
          setLIntegral_mono' measurableSet_Ioi hpt
      _ = G t := by
          rw [lintegral_const_mul' _ _ (hfin t ht), lintegral_exp_neg_Ioi hr, mul_one]
  calc (∫⁻ u in Ioi t, D' u) + ∫⁻ v in Ioi t, ∫⁻ u in Ioi t, D' u * (Iic u).indicator k v
      ≤ G t + G t := add_le_add hA hB
    _ = 2 * G t := by ring

/-- **The tail bound** `∫_t^∞ √D ≤ √(2/r) √(G t)`. -/
theorem edi_sqrt_tail {r : ℝ} (hr : 0 < r) (hfin : ∀ u, 0 ≤ u → G u ≠ ⊤)
    (h48 : ∀ s t, 0 ≤ s → s ≤ t → G t + ∫⁻ u in Icc s t, D u ≤ G s)
    (hPL : ∀ u, 0 ≤ u → ENNReal.ofReal (2 * r) * G u ≤ D u) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ u in Ioi t, D u ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (2 / r)) * G t ^ (1 / 2 : ℝ) := by
  obtain ⟨h, hm, hle, heq⟩ := exists_measurable_le_lintegral_eq (volume.restrict (Ioi t))
    (fun u => D u ^ (1 / 2 : ℝ))
  set D' : ℝ → ℝ≥0∞ := fun u => h u ^ (2 : ℝ) with hD'
  have hD'm : Measurable D' := hm.pow_const _
  have hD'le : ∀ u, D' u ≤ D u := fun u => by
    calc h u ^ (2 : ℝ) ≤ (D u ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by gcongr; exact hle u
      _ = D u := by rw [← ENNReal.rpow_mul]; norm_num
  have hW := edi_weighted_le hr hfin h48 hPL ht hD'm hD'le
  set f : ℝ → ℝ≥0∞ := fun u => h u * ENNReal.ofReal (Real.exp (r * (u - t) / 2))
  set g : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (Real.exp (-(r * (u - t)) / 2))
  have hfg : ∀ u, h u = (f * g) u := fun u => by
    simp only [f, g, Pi.mul_apply]
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf; simp
  have hf2 : ∀ u, f u ^ (2 : ℝ) = D' u * ENNReal.ofReal (Real.exp (r * (u - t))) := fun u => by
    simp only [f, hD']
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg
      (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
    ring_nf
  have hg2 : ∀ u, g u ^ (2 : ℝ) = ENNReal.ofReal (Real.exp (-(r * (u - t)))) := fun u => by
    simp only [g]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num), ← Real.exp_mul]
    ring_nf
  have hgint : ∫⁻ u in Ioi t, g u ^ (2 : ℝ) = ENNReal.ofReal (1 / r) := by
    simp_rw [hg2]
    have h1 := lintegral_exp_neg_Ioi hr t
    have e : ∀ u, ENNReal.ofReal (r * Real.exp (-(r * (u - t)))) =
        ENNReal.ofReal r * ENNReal.ofReal (Real.exp (-(r * (u - t)))) := fun u =>
      ENNReal.ofReal_mul hr.le
    simp_rw [e] at h1
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1
    rw [ENNReal.ofReal_div_of_pos hr, ENNReal.ofReal_one,
      ENNReal.eq_div_iff (by simpa using hr) ENNReal.ofReal_ne_top]
    exact h1
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Ioi t))
    Real.HolderConjugate.two_two
    (hm.mul (ENNReal.measurable_ofReal.comp (by fun_prop))).aemeasurable
    (ENNReal.measurable_ofReal.comp (by fun_prop : Measurable fun u : ℝ =>
      Real.exp (-(r * (u - t)) / 2))).aemeasurable (f := f) (g := g)
  simp_rw [hf2, hgint] at hH
  rw [heq]
  calc ∫⁻ u in Ioi t, h u = ∫⁻ u in Ioi t, (f * g) u := by simp_rw [← hfg]
    _ ≤ (∫⁻ u in Ioi t, D' u * ENNReal.ofReal (Real.exp (r * (u - t)))) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (1 / r) ^ (1 / 2 : ℝ) := hH
    _ ≤ (2 * G t) ^ (1 / 2 : ℝ) * ENNReal.ofReal (1 / r) ^ (1 / 2 : ℝ) := by gcongr
    _ = ENNReal.ofReal (Real.sqrt (2 / r)) * G t ^ (1 / 2 : ℝ) := by
        have e1 : (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal (1 / r) ^ (1 / 2 : ℝ) =
            ENNReal.ofReal (Real.sqrt (2 / r)) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
            ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by norm_num),
            ENNReal.ofReal_rpow_of_nonneg (div_nonneg zero_le_one hr.le) (by norm_num),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _), ← Real.sqrt_eq_rpow,
            ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
          congr 2; ring
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← e1]; ring

/-- The case `r = ∞`: positive gap forces infinite dissipation, so `√D` has zero tail. -/
theorem edi_sqrt_tail_top (hfin : ∀ u, 0 ≤ u → G u ≠ ⊤)
    (h48 : ∀ s t, 0 ≤ s → s ≤ t → G t + ∫⁻ u in Icc s t, D u ≤ G s)
    (hPL : ∀ u, 0 ≤ u → G u ≠ 0 → D u = ⊤) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ u in Ioi t, D u ^ (1 / 2 : ℝ) = 0 := by
  -- `G` vanishes after `t`
  have hG0 : ∀ s, t < s → G s = 0 := by
    intro s hs
    by_contra hne
    have hall : ∀ u ∈ Ioo t s, D u = ⊤ := fun u hu => by
      refine hPL u (ht.trans hu.1.le) fun h0 => hne ?_
      exact le_antisymm ((edi_antitone h48 (ht.trans hu.1.le) hu.2.le).trans h0.le) zero_le
    have htop : ∫⁻ u in Icc t s, D u = ⊤ := by
      refine top_unique ?_
      calc (⊤ : ℝ≥0∞) = ∫⁻ _u in Ioo t s, ⊤ := by
            rw [setLIntegral_const, Real.volume_Ioo, ENNReal.top_mul]
            simpa using hs
        _ ≤ ∫⁻ u in Ioo t s, D u := setLIntegral_mono' measurableSet_Ioo fun u hu => (hall u hu).ge
        _ ≤ ∫⁻ u in Icc t s, D u := lintegral_mono_set Ioo_subset_Icc_self
    have := h48 t s ht hs.le
    rw [htop, add_top] at this
    exact hfin t ht (top_unique this)
  obtain ⟨h, hm, hle, heq⟩ := exists_measurable_le_lintegral_eq (volume.restrict (Ioi t))
    (fun u => D u ^ (1 / 2 : ℝ))
  rw [heq]
  have hz : ∀ n : ℕ, ∫⁻ u in Ici (t + 1 / (n + 1)), h u = 0 := by
    intro n
    set s := t + 1 / ((n : ℝ) + 1)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hs : t < s := by simp only [s]; linarith
    have h2 : ∫⁻ u in Ici s, h u ^ (2 : ℝ) = 0 := by
      refine le_antisymm ?_ zero_le
      calc ∫⁻ u in Ici s, h u ^ (2 : ℝ) ≤ ∫⁻ u in Ici s, D u := lintegral_mono fun u => by
            calc h u ^ (2 : ℝ) ≤ (D u ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by gcongr; exact hle u
              _ = D u := by rw [← ENNReal.rpow_mul]; norm_num
        _ ≤ G s := edi_tail_le h48 (ht.trans hs.le)
        _ = 0 := hG0 s hs
    rw [lintegral_eq_zero_iff (hm.pow_const _)] at h2
    rw [lintegral_eq_zero_iff hm]
    filter_upwards [h2] with u hu
    simpa using hu
  refine le_antisymm ?_ zero_le
  have hsub : Ioi t ⊆ ⋃ n : ℕ, Ici (t + 1 / ((n : ℝ) + 1)) := fun u hu => by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (mem_Ioi.1 hu))
    exact mem_iUnion.2 ⟨n, by simp only [mem_Ici]; linarith⟩
  calc ∫⁻ u in Ioi t, h u ≤ ∫⁻ u in ⋃ n : ℕ, Ici (t + 1 / ((n : ℝ) + 1)), h u :=
        lintegral_mono_set hsub
    _ ≤ ∑' n : ℕ, ∫⁻ u in Ici (t + 1 / ((n : ℝ) + 1)), h u := lintegral_iUnion_le _ _
    _ = 0 := by rw [ENNReal.tsum_eq_zero]; exact hz

/-- **(4.8) ⇒ (4.10)** in abstract form, with the rate `R ∈ (0, ∞]`. -/
theorem edi_decay_and_tail {R : ℝ≥0∞} (hR : 0 < R) (hfin : ∀ u, 0 ≤ u → G u ≠ ⊤)
    (h48 : ∀ s t, 0 ≤ s → s ≤ t → G t + ∫⁻ u in Icc s t, D u ≤ G s)
    (hPL : ∀ u, 0 ≤ u → 2 * R * G u ≤ D u) {t : ℝ} (ht : 0 ≤ t) :
    G t ≤ G 0 * ENNReal.ofReal (Real.exp (-2 * R.toReal * t)) ∧
    ∫⁻ u in Ioi t, D u ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (2 / R.toReal)) * G t ^ (1 / 2 : ℝ) := by
  rcases eq_or_ne R ⊤ with hRt | hRt
  · subst hRt
    simp only [ENNReal.toReal_top, mul_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one,
      mul_one, div_zero, Real.sqrt_zero, ENNReal.ofReal_zero, zero_mul, nonpos_iff_eq_zero]
    refine ⟨edi_antitone h48 le_rfl ht, edi_sqrt_tail_top hfin h48 (fun u hu hG => ?_) ht⟩
    have := hPL u hu
    rw [ENNReal.mul_top two_ne_zero, ENNReal.top_mul hG] at this
    exact top_unique this
  · have hr : 0 < R.toReal := ENNReal.toReal_pos hR.ne' hRt
    have hPL' : ∀ u, 0 ≤ u → ENNReal.ofReal (2 * R.toReal) * G u ≤ D u := fun u hu => by
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_toReal hRt]; simpa using hPL u hu
    refine ⟨?_, edi_sqrt_tail hr hfin h48 hPL' ht⟩
    have := edi_decay hr hfin h48 hPL' le_rfl ht
    convert this using 4; ring

end EDI

end SharpLSI
