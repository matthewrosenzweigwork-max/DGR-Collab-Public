import DGPS.Examples.RoughBoundary.Spikes

/-!
# Nowhere local square integrability of the spike sum (RUF003)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` section 1.2.  An open arc `J ⊂ T` of length
`d = b - a ∈ (0,1]` is `pt '' Ioo a b`.  For all large `n`, `∫_J h_n² ≥ d/(2n)`; hence `∫_J h² = ∞`
(harmonic divergence plus `(∑ h_n)² ≥ ∑ h_n²`), and `g' = h - c` is not in `L²(J)`, both on the
torus and in the real coordinate `t ↦ hSum (pt t) - hMean`.
-/

open MeasureTheory Set Filter Topology
namespace DGPS.Examples.RoughBoundary.Spikes
section RUF003

lemma nl_pt_add_int (x : ℝ) (k : ℤ) : pt (x + k) = pt x := by
  funext i
  show ((x + (k : ℝ) : ℝ) : UnitAddCircle) = (x : UnitAddCircle)
  rw [AddCircle.coe_add]
  have : ((k : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨k, by simp⟩
  rw [this, add_zero]

lemma nl_spike_mem {n : ℕ} (k : ℤ) {t : ℝ}
    (ht : t ∈ Ico ((k : ℝ) / M n) ((k : ℝ) / M n + ell n)) : pt t ∈ E n := by
  have hM := M_real_pos (n := n)
  set Mi : ℤ := (M n : ℤ) with hMi
  have hMpos : 0 < Mi := by rw [hMi]; exact_mod_cast M_pos (n := n)
  set q := k / Mi with hq
  set r := k % Mi with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ hMpos.ne'
  have hr1 : r < Mi := Int.emod_lt_of_pos _ hMpos
  have hk : k = r + Mi * q := by rw [hq, hr]; exact (Int.emod_add_mul_ediv k Mi).symm
  have hkR : (k : ℝ) = r + M n * q := by exact_mod_cast hk
  have hj : (r.toNat : ℝ) = r := by exact_mod_cast Int.toNat_of_nonneg hr0
  have hjlt : r.toNat < M n := by omega
  have e1 : (k : ℝ) / M n = r / M n + q := by rw [hkR]; field_simp
  rw [E, Set.mem_iUnion₂]
  refine ⟨r.toNat, Finset.mem_range.2 hjlt, ?_⟩
  refine ⟨t - q, ?_, ?_⟩
  · rw [hj]
    rw [e1] at ht
    constructor <;> linarith [ht.1, ht.2]
  · have := nl_pt_add_int (t - q) q
    rw [sub_add_cancel] at this
    exact this.symm

lemma nl_map_pt {a b : ℝ} (hb : b ≤ a + 1) :
    Measure.map pt (volume.restrict (Ioo a b)) = (haar 1).restrict (pt '' Ioo a b) := by
  have hsub : ∀ S, S ⊆ Ioo a b → S ⊆ Ioo a (a + 1) := fun S hS x hx =>
    ⟨(hS hx).1, (hS hx).2.trans_le hb⟩
  have hJm : MeasurableSet (pt '' Ioo a b) := (haar_pt_image (hsub _ subset_rfl) measurableSet_Ioo).1
  ext T hT
  rw [Measure.map_apply measurable_pt hT, Measure.restrict_apply hT, Measure.restrict_apply (hT.preimage measurable_pt)]
  have e : T ∩ pt '' Ioo a b = pt '' (Ioo a b ∩ pt ⁻¹' T) := by
    ext x; constructor
    · rintro ⟨hxT, s, hs, rfl⟩; exact ⟨s, ⟨hs, hxT⟩, rfl⟩
    · rintro ⟨s, ⟨hs, hsT⟩, rfl⟩; exact ⟨hsT, s, hs, rfl⟩
  rw [e, (haar_pt_image (hsub _ inter_subset_left) (measurableSet_Ioo.inter (hT.preimage measurable_pt))).2]
  rw [Set.inter_comm]

lemma nl_lintegral_pt {a b : ℝ} (hb : b ≤ a + 1) (F : Torus 1 → ENNReal) (hF : Measurable F) :
    ∫⁻ x in pt '' Ioo a b, F x ∂haar 1 = ∫⁻ t in Ioo a b, F (pt t) := by
  rw [← nl_map_pt hb, lintegral_map hF measurable_pt]

lemma nl_M_ge (n : ℕ) : (n : ℝ) ≤ M n := by
  have h1 : (n : ℝ) ^ 3 + 1 ≤ Real.exp ((n : ℝ) ^ 3) := by
    simpa [add_comm] using Real.add_one_le_exp ((n : ℝ) ^ 3)
  have h2 : Real.exp ((n : ℝ) ^ 3) ≤ M n := Nat.le_ceil _
  have h3 : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hpos
      nlinarith [sq_nonneg (n : ℝ)]
  linarith

lemma nl_line_lower {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} :
    ENNReal.ofReal ((A n) ^ 2) * ENNReal.ofReal ((M n : ℝ) * (b - a) - 2) * ENNReal.ofReal (ell n)
      ≤ ∫⁻ t in Ioo a b, ENNReal.ofReal (h n (pt t) ^ 2) := by
  have hM := M_real_pos (n := n)
  have hl := ell_pos hn
  have hlt := ell_lt hn
  have hMl : (M n : ℝ) * ell n < 1 := by
    rw [lt_div_iff₀ hM] at hlt; linarith
  set K : Finset ℤ := Finset.Ioc ⌊(M n : ℝ) * a⌋ ⌊(M n : ℝ) * b - (M n : ℝ) * ell n⌋ with hK
  set S : Set ℝ := ⋃ k ∈ K, Ico ((k : ℝ) / M n) ((k : ℝ) / M n + ell n) with hS
  have hSsub : S ⊆ Ioo a b := by
    intro t ht
    rw [hS, Set.mem_iUnion₂] at ht
    obtain ⟨k, hk, ht1, ht2⟩ := ht
    rw [hK, Finset.mem_Ioc] at hk
    have h1 : (M n : ℝ) * a < k := by
      have := Int.lt_floor_add_one ((M n : ℝ) * a)
      have h' : ((⌊(M n : ℝ) * a⌋ : ℤ) : ℝ) + 1 ≤ k := by exact_mod_cast hk.1
      linarith
    have h2 : (k : ℝ) ≤ (M n : ℝ) * b - (M n : ℝ) * ell n :=
      (Int.cast_le.2 hk.2).trans (Int.floor_le _)
    have h1' : a < (k : ℝ) / M n := by rw [lt_div_iff₀ hM]; linarith
    have h2' : (k : ℝ) / M n + ell n ≤ b := by
      have : (k : ℝ) / M n ≤ b - ell n := by rw [div_le_iff₀ hM]; linarith
      linarith
    exact ⟨h1'.trans_le ht1, ht2.trans_le h2'⟩
  have hSvol : volume S = (K.card : ENNReal) * ENNReal.ofReal (ell n) := by
    rw [hS, measure_biUnion_finset]
    · simp [Real.volume_Ico]
    · intro k _ k' _ hkk'
      rcases lt_or_gt_of_ne hkk' with h | h
      · refine Set.disjoint_left.2 fun x hx hx' => ?_
        have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast h
        have h3 : ((k : ℝ) + 1) / M n ≤ k' / M n := by gcongr
        rw [add_div] at h3
        linarith [hx.2, hx'.1, one_div (M n : ℝ)]
      · refine Set.disjoint_left.2 fun x hx hx' => ?_
        have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast h
        have h3 : ((k' : ℝ) + 1) / M n ≤ k / M n := by gcongr
        rw [add_div] at h3
        linarith [hx'.2, hx.1, one_div (M n : ℝ)]
    · intro k _; exact measurableSet_Ico
  have hSmeas : MeasurableSet S := Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Ico
  have hcard : (M n : ℝ) * (b - a) - 2 ≤ (K.card : ℝ) := by
    have e : (K.card : ℤ) = max (⌊(M n : ℝ) * b - (M n : ℝ) * ell n⌋ - ⌊(M n : ℝ) * a⌋) 0 := by
      rw [hK, Int.card_Ioc]; exact Int.toNat_eq_max _
    have e2 : ((K.card : ℤ) : ℝ) ≥ ((⌊(M n : ℝ) * b - (M n : ℝ) * ell n⌋ - ⌊(M n : ℝ) * a⌋ : ℤ) : ℝ) := by
      exact_mod_cast (by rw [e]; exact le_max_left _ _)
    have f1 := Int.sub_one_lt_floor ((M n : ℝ) * b - (M n : ℝ) * ell n)
    have f2 := Int.floor_le ((M n : ℝ) * a)
    push_cast at e2
    nlinarith
  calc ENNReal.ofReal ((A n) ^ 2) * ENNReal.ofReal ((M n : ℝ) * (b - a) - 2) * ENNReal.ofReal (ell n)
      ≤ ENNReal.ofReal ((A n) ^ 2) * (K.card : ENNReal) * ENNReal.ofReal (ell n) := by
        gcongr
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcard
    _ = ∫⁻ t in S, ENNReal.ofReal ((A n) ^ 2) := by
        rw [setLIntegral_const, hSvol]; ring
    _ = ∫⁻ t in S, ENNReal.ofReal (h n (pt t) ^ 2) := by
        refine setLIntegral_congr_fun hSmeas fun t ht => ?_
        rw [hS, Set.mem_iUnion₂] at ht
        obtain ⟨k, _, hk⟩ := ht
        have : pt t ∈ E n := nl_spike_mem k hk
        simp [h, this]
    _ ≤ _ := lintegral_mono_set hSsub

lemma nl_integrable_sq {n : ℕ} (hn : 2 ≤ n) : Integrable (fun x => h n x ^ 2) (haar 1) := by
  have : (fun x => h n x ^ 2) = (E n).indicator (fun _ => A n ^ 2) := by
    funext x; by_cases hx : x ∈ E n <;> simp [h, hx]
  rw [this]; exact (integrable_const _).indicator (E_measurable hn)

lemma nl_real_lower {n : ℕ} (hn : 2 ≤ n) {a b : ℝ} (hb : b ≤ a + 1)
    (hd : 4 ≤ (M n : ℝ) * (b - a)) :
    (b - a) / (2 * n) ≤ ∫ x in pt '' Ioo a b, h n x ^ 2 ∂haar 1 := by
  have hM := M_real_pos (n := n)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hl := ell_pos hn
  have hlow := nl_line_lower hn (a := a) (b := b)
  have hmeas' : Measurable (h n) := measurable_const.indicator (E_measurable hn)
  have hmeas2 : Measurable (fun x : Torus 1 => ENNReal.ofReal (h n x ^ 2)) :=
    (hmeas'.pow_const 2).ennreal_ofReal
  have htr := nl_lintegral_pt hb (fun x => ENNReal.ofReal (h n x ^ 2)) hmeas2
  have hAl : A n ^ 2 * ell n = 1 / ((n : ℝ) * M n) := by
    unfold A ell
    rw [← Real.exp_nat_mul, show (2 : ℕ) * (n : ℝ) = 2 * n by push_cast; ring]
    have := Real.exp_pos (2 * n)
    field_simp
  have hMd : 0 ≤ (M n : ℝ) * (b - a) - 2 := by linarith
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)] at hlow
  have hint := nl_integrable_sq hn
  have hint' : Integrable (fun x => h n x ^ 2) ((haar 1).restrict (pt '' Ioo a b)) := hint.restrict
  rw [← htr, ← ofReal_integral_eq_lintegral_ofReal hint'
    (Filter.Eventually.of_forall fun x => by positivity)] at hlow
  have hI0 : 0 ≤ ∫ x in pt '' Ioo a b, h n x ^ 2 ∂haar 1 :=
    integral_nonneg fun x => by positivity
  have h2 := (ENNReal.ofReal_le_ofReal_iff hI0).1 hlow
  refine le_trans ?_ h2
  have : A n ^ 2 * ((M n : ℝ) * (b - a) - 2) * ell n = ((M n : ℝ) * (b - a) - 2) * (1 / ((n : ℝ) * M n)) := by
    rw [← hAl]; ring
  rw [this]
  rw [div_le_iff₀ (by positivity)]
  have : ((M n : ℝ) * (b - a) - 2) * (1 / ((n : ℝ) * M n)) * (2 * n) = (2 * ((M n : ℝ) * (b - a) - 2)) / M n := by
    field_simp
  rw [this, le_div_iff₀ hM]
  nlinarith

lemma nl_eventually {a b : ℝ} (hab : a < b) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → 4 ≤ (M n : ℝ) * (b - a) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (4 / (b - a))
  refine ⟨max N 2, le_max_right _ _, fun n hn => ?_⟩
  have h1 : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have h2 := nl_M_ge n
  have hd : 0 < b - a := sub_pos.2 hab
  rw [div_le_iff₀ hd] at hN
  nlinarith

lemma nl_not_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {F : α → ℝ} (c : ℝ) (hF : ∫⁻ x, ENNReal.ofReal (F x ^ 2) ∂μ = ⊤) :
    ¬ MemLp (fun x => F x - c) 2 μ := by
  intro hm
  have hm' : MemLp F 2 μ := by
    have := hm.add (memLp_const (p := 2) c)
    have e : F = ((fun x => F x - c) + fun _ => c) := by funext x; simp
    rw [e]; exact this
  have hi := hm'.integrable_sq
  have := hi.lintegral_lt_top
  exact this.ne hF

lemma nl_sq_tsum_le (x : Torus 1) :
    ∑' n : ℕ, ENNReal.ofReal (h (n + 2) x ^ 2) ≤ hSumE x ^ 2 := by
  have e : ∀ n : ℕ, ENNReal.ofReal (h (n + 2) x ^ 2) = ENNReal.ofReal (h (n + 2) x) * ENNReal.ofReal (h (n + 2) x) := by
    intro n; rw [sq, ENNReal.ofReal_mul (h_nonneg _ _)]
  simp_rw [e]
  rw [sq]
  unfold hSumE
  conv_rhs => rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun n => ?_
  gcongr
  exact ENNReal.le_tsum (f := fun n : ℕ => ENNReal.ofReal (h (n + 2) x)) n

lemma nl_tsum_top {d : ℝ} (hd : 0 < d) (N : ℕ) (b : ℕ → ENNReal)
    (hb : ∀ n : ℕ, N ≤ n → ENNReal.ofReal (d / (2 * ((n + 2 : ℕ) : ℝ))) ≤ b n) :
    ∑' n, b n = ⊤ := by
  by_contra hne
  have hbt : ∀ n, b n ≠ ⊤ := fun n => ENNReal.ne_top_of_tsum_ne_top hne n
  have hs : Summable fun n => (b n).toReal := ENNReal.summable_toReal hne
  have hs2 : Summable fun n : ℕ => d / (2 * ((n + N + 2 : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_nat_add_iff N).2 hs)
    have := hb (n + N) (by omega)
    have h2 := ENNReal.toReal_mono (hbt _) this
    rw [ENNReal.toReal_ofReal (by positivity)] at h2
    have e : ((n + N + 2 : ℕ) : ℝ) = ((n + N + 2 : ℕ) : ℝ) := rfl
    simpa [add_assoc, add_comm, add_left_comm] using h2
  have hs3 : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) := by
    have h4 : Summable fun n : ℕ => 1 / ((n + N + 2 : ℕ) : ℝ) := by
      have := hs2.mul_left (2 / d)
      refine this.congr fun n => ?_
      have : (0 : ℝ) < ((n + N + 2 : ℕ) : ℝ) := by positivity
      field_simp
    have h5 : Summable fun n : ℕ => 1 / ((n + (N + 2) : ℕ) : ℝ) := by
      refine h4.congr fun n => ?_
      rw [show n + N + 2 = n + (N + 2) by omega]
    exact (summable_nat_add_iff (N + 2)).1 h5
  exact Real.not_summable_one_div_natCast hs3

lemma nl_lintegral_top {a b : ℝ} (hab : a < b) (hb : b ≤ a + 1) :
    ∫⁻ x in pt '' Ioo a b, ENNReal.ofReal (hSum x ^ 2) ∂haar 1 = ⊤ := by
  obtain ⟨N, hN2, hN⟩ := nl_eventually hab
  have hd : 0 < b - a := sub_pos.2 hab
  set μ := (haar 1).restrict (pt '' Ioo a b) with hμ
  have h1 : ∫⁻ x, ENNReal.ofReal (hSum x ^ 2) ∂μ = ∫⁻ x, hSumE x ^ 2 ∂μ := by
    have hfin : ∀ᵐ x ∂(haar 1), hSumE x < ⊤ :=
      ae_lt_top hSumE_meas (by rw [lintegral_hSumE]; exact ENNReal.ofReal_ne_top)
    refine lintegral_congr_ae ((ae_restrict_of_ae hfin).mono fun x hx => ?_)
    show ENNReal.ofReal (hSum x ^ 2) = hSumE x ^ 2
    rw [hSum_eq_toReal, ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  show ∫⁻ x, ENNReal.ofReal (hSum x ^ 2) ∂μ = ⊤
  rw [h1]
  refine top_unique ?_
  calc (⊤ : ENNReal) = ∑' n : ℕ, ∫⁻ x, ENNReal.ofReal (h (n + 2) x ^ 2) ∂μ := by
        symm
        refine nl_tsum_top hd N _ fun n hn => ?_
        have hn2 : 2 ≤ n + 2 := by omega
        have hl := nl_real_lower hn2 hb (hN (n + 2) (by omega))
        have hI := nl_integrable_sq hn2
        have hI' : Integrable (fun x => h (n + 2) x ^ 2) μ := hI.restrict
        rw [← ofReal_integral_eq_lintegral_ofReal hI'
          (Filter.Eventually.of_forall fun x => by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        refine le_trans (le_of_eq ?_) hl
        push_cast; ring
    _ = ∫⁻ x, ∑' n : ℕ, ENNReal.ofReal (h (n + 2) x ^ 2) ∂μ := by
        rw [lintegral_tsum]
        intro n
        exact (((h_meas n).pow_const 2).ennreal_ofReal).aemeasurable
    _ ≤ _ := lintegral_mono fun x => nl_sq_tsum_le x

/-- **RUF003.** Nowhere local square integrability: for every open arc `J = pt '' (a,b)` of `T`
(`a < b ≤ a + 1`, length `d = b - a`), `∫_J h_n² ≥ d/(2n)` for all large `n`, `∫_J h² = ∞`, and
neither `h` nor `g' = h - c` lies in `L²(J)` (also read through the lift `t ↦ hSum (pt t)`). -/
theorem nowhere_local_square_integrability {a b : ℝ} (hab : a < b) (hb : b ≤ a + 1) :
    (∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (b - a) / (2 * n) ≤ ∫ x in pt '' Ioo a b, h n x ^ 2 ∂haar 1) ∧
    ∫⁻ x in pt '' Ioo a b, ENNReal.ofReal (hSum x ^ 2) ∂haar 1 = ⊤ ∧
    ∫⁻ t in Ioo a b, ENNReal.ofReal (hSum (pt t) ^ 2) = ⊤ ∧
    ¬ MemLp hSum 2 ((haar 1).restrict (pt '' Ioo a b)) ∧
    ¬ MemLp (fun x => hSum x - hMean) 2 ((haar 1).restrict (pt '' Ioo a b)) ∧
    ¬ MemLp (fun t : ℝ => hSum (pt t) - hMean) 2 (volume.restrict (Ioo a b)) := by
  have htop := nl_lintegral_top hab hb
  have htop' : ∫⁻ t in Ioo a b, ENNReal.ofReal (hSum (pt t) ^ 2) = ⊤ := by
    rw [← nl_lintegral_pt hb (fun x => ENNReal.ofReal (hSum x ^ 2))
      ((hSum_meas.pow_const 2).ennreal_ofReal)]
    exact htop
  have hJfin : IsFiniteMeasure ((haar 1).restrict (pt '' Ioo a b)) := inferInstance
  have hlfin : IsFiniteMeasure (volume.restrict (Ioo a b)) := inferInstance
  refine ⟨?_, htop, htop', ?_, nl_not_memLp hMean htop, nl_not_memLp hMean htop'⟩
  · obtain ⟨N, hN2, hN⟩ := nl_eventually hab
    exact ⟨N, hN2, fun n hn => nl_real_lower (hN2.trans hn) hb (hN n hn)⟩
  · simpa using nl_not_memLp (μ := (haar 1).restrict (pt '' Ioo a b)) (F := hSum) 0 htop

end RUF003
end DGPS.Examples.RoughBoundary.Spikes
