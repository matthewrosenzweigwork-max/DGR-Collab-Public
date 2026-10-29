import FullLabeledLSI.Examples.E01g0_Tmat

/-!
# Lane D, Task A (H4): the exact formula (9.8) for `λ_G` and existence of reference data

Theorems `lamG_formula`, `exists_ref_data`, `lamGValue_of_formula` with EXACTLY the frozen
statements of `E01a_Common.lean`, proved in namespace `SharpLSI.FL.Ex.LaneD` (the integrator
replaces the sorried stubs).  The hypotheses `hmin`, `hyp` of the frozen statements are not needed.
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-! ### `λ_G` for a diagonal covariance -/

/-- `λ_G` for `C = diag(c)`: the infimum of the ratios `λ_i / c_i`. -/
theorem lamG_diag (lam' c : ℕ → ℝ) (hc0 : ∀ i, 0 < c i) (M : ℝ) (hcM : ∀ i, c i ≤ M)
    (hlam : ∀ i, 0 ≤ lam' i) :
    lamG lam' (fun i j => if i = j then c i else 0) = ⨅ i, ENNReal.ofReal (lam' i / c i) := by
  apply le_antisymm
  · refine le_iInf fun i => ?_
    have hmem : (Pi.single i (1 : ℝ) : ℕ → ℝ) ∈ {v : ℕ → ℝ | Summable (fun i => v i ^ 2) ∧
        Summable (fun i => lam' i * v i ^ 2) ∧ v ≠ 0} := by
      refine ⟨?_, ?_, ?_⟩
      · refine summable_of_ne_finset_zero (s := {i}) fun b hb => ?_
        simp at hb; simp [Pi.single_apply, hb]
      · refine summable_of_ne_finset_zero (s := {i}) fun b hb => ?_
        simp at hb; simp [Pi.single_apply, hb]
      · intro h; have := congrFun h i; simp at this
    refine (iInf₂_le (Pi.single i (1 : ℝ)) hmem).trans (le_of_eq ?_)
    have h1 : ∑' k, lam' k * (Pi.single i (1 : ℝ) : ℕ → ℝ) k ^ 2 = lam' i := by
      rw [tsum_eq_single i]
      · simp
      · intro b hb; simp [Pi.single_apply, hb]
    have h2 : ∑' k, (Pi.single i (1 : ℝ) : ℕ → ℝ) k *
        ∑' j, (if k = j then c k else 0) * (Pi.single i (1 : ℝ) : ℕ → ℝ) j = c i := by
      rw [tsum_eq_single i]
      · rw [tsum_eq_single i]
        · simp
        · intro b hb; simp [Pi.single_apply, hb]
      · intro b hb
        simp [Pi.single_apply, hb]
    rw [h1, h2, ENNReal.ofReal_div_of_pos (hc0 i)]
  · refine le_iInf₂ fun v hv => ?_
    obtain ⟨hv2, hvl, hv0⟩ := hv
    set L : ℝ≥0∞ := ⨅ i, ENNReal.ofReal (lam' i / c i) with hL
    have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iInf_le _ 0)
    set ℓ : ℝ := L.toReal with hℓ
    have hLℓ : ENNReal.ofReal ℓ = L := ENNReal.ofReal_toReal hLtop
    have hℓi : ∀ i, ℓ * c i ≤ lam' i := by
      intro i
      have h1 : ENNReal.ofReal ℓ ≤ ENNReal.ofReal (lam' i / c i) := by
        rw [hLℓ]; exact iInf_le _ i
      rw [ENNReal.ofReal_le_ofReal_iff (div_nonneg (hlam i) (hc0 i).le)] at h1
      rw [le_div_iff₀ (hc0 i)] at h1
      exact h1
    -- the denominator
    have hden : ∀ i, ∑' j, (if i = j then c i else 0) * v j = c i * v i := by
      intro i
      rw [tsum_eq_single i]
      · simp
      · intro b hb; simp [Ne.symm hb]
    have hsum1 : Summable (fun i => c i * v i ^ 2) := by
      refine Summable.of_nonneg_of_le (fun i => by have := hc0 i; positivity)
        (fun i => ?_) (hv2.mul_left M)
      exact mul_le_mul_of_nonneg_right (hcM i) (sq_nonneg _)
    have hden' : ∑' i, v i * ∑' j, (if i = j then c i else 0) * v j = ∑' i, c i * v i ^ 2 := by
      congr 1; funext i; rw [hden i]; ring
    rw [hden']
    have hpos : 0 < ∑' i, c i * v i ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h; push_neg at h; exact hv0 (funext h)
      exact hsum1.tsum_pos (fun i => by have := hc0 i; positivity) i
        (by have := hc0 i; have := sq_pos_of_ne_zero hi; positivity)
    have hle : ℓ * ∑' i, c i * v i ^ 2 ≤ ∑' i, lam' i * v i ^ 2 := by
      rw [← hsum1.tsum_mul_left]
      refine Summable.tsum_le_tsum (fun i => ?_) (hsum1.mul_left ℓ) hvl
      calc ℓ * (c i * v i ^ 2) = (ℓ * c i) * v i ^ 2 := by ring
        _ ≤ lam' i * v i ^ 2 := mul_le_mul_of_nonneg_right (hℓi i) (sq_nonneg _)
    rw [← hLℓ]
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hpos)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul (by positivity)]
    · exact ENNReal.ofReal_le_ofReal hle

/-! ### Frequencies of a reference eigenbasis -/

section freq

variable {e : ℕ → Torus 1 → ℝ} {lam : ℕ → ℝ}

/-- The frequency `N_i ≥ 1` of `e_{i+1}`. -/
noncomputable def Nf (he : IsRefEigenbasis (haar 1) e lam) (i : ℕ) : ℕ :=
  (exists_N he (Nat.succ_pos i)).choose

theorem Nf_pos (he : IsRefEigenbasis (haar 1) e lam) (i : ℕ) : 1 ≤ Nf he i :=
  (exists_N he (Nat.succ_pos i)).choose_spec.1

theorem Nf_lam (he : IsRefEigenbasis (haar 1) e lam) (i : ℕ) :
    lam (i + 1) = aCos * ((Nf he i : ℕ) : ℝ) ^ 2 :=
  (exists_N he (Nat.succ_pos i)).choose_spec.2.1

theorem Nf_supp (he : IsRefEigenbasis (haar 1) e lam) (i : ℕ) : SuppFreq (e (i + 1)) (Nf he i) :=
  (exists_N he (Nat.succ_pos i)).choose_spec.2.2

theorem Nf_surj (he : IsRefEigenbasis (haar 1) e lam) (N : ℕ) (hN : 1 ≤ N) :
    ∃ i, Nf he i = N := by
  obtain ⟨j, hj, hl⟩ := exists_index he N hN
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  refine ⟨i, ?_⟩
  have h1 := Nf_lam he i
  rw [h1] at hl
  have hapos : 0 < aCos := by unfold aCos; positivity
  have h2 : ((Nf he i : ℕ) : ℝ) ^ 2 = (N : ℝ) ^ 2 := mul_left_cancel₀ hapos.ne' hl
  have h3 : ((Nf he i : ℕ) : ℝ) = N := by
    have := (sq_eq_sq₀ (by positivity) (by positivity)).mp h2
    exact this
  exact_mod_cast h3

theorem Tmat_diag {C : Torus 1 → ℝ} (hC : GoodKernel C) (he : IsRefEigenbasis (haar 1) e lam)
    (i j : ℕ) :
    Tmat (attrW C) (haar 1) e i j = if i = j then -chat C ((Nf he j : ℕ) : ℤ) else 0 :=
  Tmat_entry hC he i j (Nf_pos he j) (Nf_supp he j)

theorem one_sub_chat_pos {C : Torus 1 → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hsup : ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ) (he : IsRefEigenbasis (haar 1) e lam) (i : ℕ) :
    δ ≤ 1 - chat C ((Nf he i : ℕ) : ℤ) := by
  have := hsup ((Nf he i : ℕ) : ℤ) (by have := Nf_pos he i; omega)
  linarith

/-- Columns of the inverse of `I + T` are diagonal. -/
theorem Cm_eq {C : Torus 1 → ℝ} (hC : GoodKernel C) {δ : ℝ} (hδ : 0 < δ)
    (hsup : ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ) (he : IsRefEigenbasis (haar 1) e lam)
    {Cm : ℕ → ℕ → ℝ} (hCm : IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm) (i j : ℕ) :
    Cm i j = if i = j then 1 / (1 - chat C ((Nf he i : ℕ) : ℤ)) else 0 := by
  have h := (hCm j).2 i |>.2
  have hpos := one_sub_chat_pos hδ hsup he i
  rw [tsum_eq_single i] at h
  · simp only [if_true, Tmat_diag hC he] at h
    have hne : 1 - chat C ((Nf he i : ℕ) : ℤ) ≠ 0 := by linarith
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl] at h ⊢
      field_simp
      linarith
    · rw [if_neg hij] at h ⊢
      have : (1 - chat C ((Nf he i : ℕ) : ℤ)) * Cm i j = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hne
      · exact h
  · intro k hk
    simp [Tmat_diag hC he, Ne.symm hk]

end freq

/-! ### Existence of reference data -/

theorem exists_ref_eigenbasis : ∃ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ),
    IsRefEigenbasis (haar 1) e lam := by
  have hG : GoodDens (fun _ : Torus 1 => (1 : ℝ)) 1 1 :=
    ⟨measurable_const, one_pos, fun _ => le_rfl, fun _ => le_rfl, by simp⟩
  have hd := isRefEigenbasis_eSeq hG (le_refl 1)
  have hmeas : densMeasure (fun _ : Torus 1 => (1 : ℝ)) = haar 1 := by
    simp [densMeasure]
  rw [hmeas] at hd
  exact ⟨_, _, hd⟩

/-! ### The three frozen statements -/

/-- (9.8): `λ_G = inf_{n ≥ 1} 4π² n² (1 - Ĉ(n))`. Frozen statement of `lamG_formula`. -/
theorem lamG_formula {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (hyp : ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ)
    (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ)
    (he : IsRefEigenbasis (haar 1) e lam) (hCm : IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm) :
    lamG (lamShift lam) Cm =
      ⨅ n : ℕ, ENNReal.ofReal (aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat C ((n : ℤ) + 1))) := by
  obtain ⟨δ, hδ, hsup⟩ := hsup
  have hapos : 0 < aCos := by unfold aCos; positivity
  set c : ℕ → ℝ := fun i => 1 / (1 - chat C ((Nf he i : ℕ) : ℤ)) with hc
  have hcpos : ∀ i, 0 < c i := fun i => by
    have := one_sub_chat_pos hδ hsup he i
    simp only [hc]; apply one_div_pos.mpr; linarith
  have hcM : ∀ i, c i ≤ 1 / δ := fun i => by
    have := one_sub_chat_pos hδ hsup he i
    simp only [hc]
    exact one_div_le_one_div_of_le hδ this
  have hCm' : Cm = fun i j => if i = j then c i else 0 := by
    funext i j; exact Cm_eq hC hδ hsup he hCm i j
  have hlam0 : ∀ i, 0 ≤ lamShift lam i := fun i => by
    unfold lamShift; rw [Nf_lam he i]; positivity
  rw [hCm', lamG_diag (lamShift lam) c hcpos (1 / δ) hcM hlam0]
  -- compare the two infima
  have hterm : ∀ i, lamShift lam i / c i =
      aCos * ((Nf he i : ℕ) : ℝ) ^ 2 * (1 - chat C ((Nf he i : ℕ) : ℤ)) := by
    intro i
    have := one_sub_chat_pos hδ hsup he i
    simp only [hc, lamShift]
    rw [Nf_lam he i]
    field_simp
  apply le_antisymm
  · refine le_iInf fun n => ?_
    obtain ⟨i, hi⟩ := Nf_surj he (n + 1) (by omega)
    refine (iInf_le _ i).trans (le_of_eq ?_)
    rw [hterm i, hi]
    push_cast
    rfl
  · refine le_iInf fun i => ?_
    obtain ⟨n, hn⟩ : ∃ n, Nf he i = n + 1 := ⟨Nf he i - 1, by have := Nf_pos he i; omega⟩
    refine (iInf_le _ n).trans (le_of_eq ?_)
    rw [hterm i, hn]
    push_cast
    rfl

/-- Existence of reference data `(e, lam, Cm)`. Frozen statement of `exists_ref_data`. -/
theorem exists_ref_data {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (hyp : ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ) :
    ∃ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ),
      IsRefEigenbasis (haar 1) e lam ∧ IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm := by
  obtain ⟨δ, hδ, hsup⟩ := hsup
  obtain ⟨e, lam, he⟩ := exists_ref_eigenbasis
  refine ⟨e, lam, fun i j => if i = j then 1 / (1 - chat C ((Nf he i : ℕ) : ℤ)) else 0, he, ?_⟩
  intro j
  have hpos := one_sub_chat_pos hδ hsup he
  refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
  · refine summable_of_ne_finset_zero (s := {j}) fun b hb => ?_
    simp at hb; simp [hb]
  · refine summable_of_ne_finset_zero (s := {i}) fun b hb => ?_
    simp at hb
    simp [Tmat_diag hC he, Ne.symm hb]
  · rw [tsum_eq_single i]
    · simp only [if_true, Tmat_diag hC he]
      by_cases hij : i = j
      · subst hij
        have := hpos i
        have hne : 1 - chat C ((Nf he i : ℕ) : ℤ) ≠ 0 := by linarith
        simp only [if_true]
        field_simp
        ring
      · simp [hij]
    · intro k hk
      simp [Tmat_diag hC he, Ne.symm hk]

/-- Frozen statement of `lamGValue_of_formula`. -/
theorem lamGValue_of_formula {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (hyp : ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ) :
    LamGValue (attrW C)
      (⨅ n : ℕ, ENNReal.ofReal (aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat C ((n : ℤ) + 1)))) :=
  ⟨exists_ref_data hC hmin hyp hsup, fun e lam Cm he hCm => lamG_formula hC hmin hyp hsup e lam Cm he hCm⟩

end SharpLSI.FL.Ex.LaneD
