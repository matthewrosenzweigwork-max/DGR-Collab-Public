import FullLabeledLSI.Paper.Sec6Rank2
import SharpSymmetricLSI.Paper.LamSym3
import SharpSymmetricLSI.Paper.GaussForm15

/-!
# Lemma 6.1, conclusions 3 and 4 (item M5), and the positivity export

* `positivity_export`: for large `R`, `I + a^R ≥ σ/2` on vectors supported in `s R`.
* `rank_errors_part3`: `λ_{G,R} = lamG (lamShift lam) (C_R) → lamG (lamShift lam) C`.
* `rank_errors_part4`: `b_R → b` (continuity of `min`).

Route for part 3.  Everything is done on finite sections and then passed to the limit through
the SYM toolkit (`GaussLaw5.tendsto_inner_secRes`, `LamSym3.tendsto_Qv_vtr`).
For the finite-section resolvents `x = (I+T_n)⁻¹u`, `y = (I+a_n)⁻¹u` one has
`⟨u,y⟩ - ⟨u,x⟩ = ⟨x,(T_n - a_n)y⟩`, hence `|⟨u,y⟩ - ⟨u,x⟩| ≤ b ‖x‖‖y‖ ≤ b ‖u‖²/(σ σ₂)` where `b`
bounds the Hilbert–Schmidt norm of `T - a` (Bessel, Part 2).  This transfers to the quadratic forms
`⟨v, C v⟩`, `⟨v, C_R v⟩` of `ℓ²` vectors by truncation.  A uniform lower bound
`⟨v, C v⟩ ≥ ‖v‖²/(3/2 + ‖T‖²_HS/2)` turns the absolute error into a relative one, and the infima
defining `lamG` are compared quotient by quotient.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace SharpLSI.FL

namespace Rank3

/-! ### The hypotheses of the SYM toolkit for a pair `(T, C)` -/

/-- `T` symmetric Hilbert–Schmidt with `I + T ≥ σ` on all finite sections, and `C = (I+T)⁻¹`. -/
structure SymPkg (T C : ℕ → ℕ → ℝ) (σ : ℝ) : Prop where
  symm : ∀ i j, T i j = T j i
  hs : Summable fun p : ℕ × ℕ => T p.1 p.2 ^ 2
  pos : 0 < σ
  sec : ∀ n (y : EuclideanSpace ℝ (Fin n)), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ
  inv : IsInverseOfIPlus T C

namespace SymPkg

variable {T C : ℕ → ℕ → ℝ} {σ : ℝ} (P : SymPkg T C σ)
include P

theorem Csymm (i j : ℕ) : C i j = C j i := C_symm_of_secOp P.symm P.hs P.pos P.sec P.inv i j

theorem nn (s : Finset ℕ) (v : ℕ → ℝ) : 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j :=
  quadC_nonneg P.symm P.hs P.pos P.sec P.inv s v

theorem up (s : Finset ℕ) (v : ℕ → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j ≤ (∑ i ∈ s, v i ^ 2) / σ :=
  quadC_le P.symm P.hs P.pos P.sec P.inv s v

theorem col (j : ℕ) : Summable fun k => C k j ^ 2 := (P.inv j).1

/-- The block quadratic forms converge to the `ℓ²` quadratic form. -/
theorem limQ {v : ℕ → ℝ} (hv : Summable fun i => v i ^ 2) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * C i j * v j) atTop
      (𝓝 (∑' i, v i * ∑' j, C i j * v j)) := by
  have h := tendsto_Qv_vtr P.pos P.Csymm P.nn P.up P.col hv
  simp_rw [Qv_vtr_eq] at h
  exact h

/-- A uniform lower bound for finite blocks of `C`: `C ≥ (3/2 + ‖T‖²_HS/2)⁻¹`. -/
theorem lower (s : Finset ℕ) (v : ℕ → ℝ) :
    (∑ i ∈ s, v i ^ 2) / (3 / 2 + (∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) / 2) ≤
      ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j := by
  set S := ∑' p : ℕ × ℕ, T p.1 p.2 ^ 2 with hSdef
  refine ge_of_tendsto (tendsto_inner_secRes P.symm P.hs P.pos P.sec P.inv s v) ?_
  filter_upwards [eventually_lt_of_finset s] with n hn
  rw [inner_secRes, ← norm_finVec_sq s hn, ← sum_inner_secVec_sq P.symm (finVec s v n),
    Finset.sum_div]
  refine Finset.sum_le_sum fun k _ => ?_
  have hpos : 0 < 1 + secEig P.symm n k := secEig_pos P.symm P.pos P.sec n k
  have hk2 : secEig P.symm n k ^ 2 ≤ S := by
    calc secEig P.symm n k ^ 2 ≤ ∑ k', secEig P.symm n k' ^ 2 :=
          Finset.single_le_sum (f := fun k' => secEig P.symm n k' ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
      _ = ∑ i : Fin n, ∑ j : Fin n, T i j ^ 2 := sum_secEig_sq P.symm
      _ ≤ S := sum_fin_sq_le_tsum P.hs n
  have hk : 1 + secEig P.symm n k ≤ 3 / 2 + S / 2 := by
    nlinarith [sq_nonneg (secEig P.symm n k - 1)]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hpos hk) (sq_nonneg _)

/-- The lower bound for the `ℓ²` quadratic form. -/
theorem Qlower {v : ℕ → ℝ} (hv : Summable fun i => v i ^ 2) :
    (∑' i, v i ^ 2) / (3 / 2 + (∑' p : ℕ × ℕ, T p.1 p.2 ^ 2) / 2) ≤
      ∑' i, v i * ∑' j, C i j * v j :=
  le_of_tendsto_of_tendsto' ((hv.hasSum.tendsto_sum_nat).div_const _) (P.limQ hv)
    fun n => P.lower (Finset.range n) v

end SymPkg

/-! ### Finite-dimensional estimates -/

theorem secOp_sub (M T a : ℕ → ℕ → ℝ) (hM : ∀ i j, M i j = T i j - a i j) {n : ℕ}
    (y : EuclideanSpace ℝ (Fin n)) :
    secOp M n y = secOp T n y - secOp a n y := by
  ext i
  simp only [secOp_apply, PiLp.sub_apply, hM, sub_mul, Finset.sum_sub_distrib]

theorem norm_secOp_le {n : ℕ} (M : ℕ → ℕ → ℝ) (y : EuclideanSpace ℝ (Fin n)) {b : ℝ}
    (hb0 : 0 ≤ b) (hb : ∑ i : Fin n, ∑ j : Fin n, M i j ^ 2 ≤ b ^ 2) :
    ‖secOp M n y‖ ≤ b * ‖y‖ := by
  have h1 : ‖secOp M n y‖ ^ 2 ≤ (b * ‖y‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs, secOp_apply]
    calc ∑ i : Fin n, (∑ j : Fin n, M i j * y j) ^ 2
        ≤ ∑ i : Fin n, ((∑ j : Fin n, M i j ^ 2) * ∑ j : Fin n, y j ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ i : Fin n, ∑ j : Fin n, M i j ^ 2) * ∑ j : Fin n, y j ^ 2 := by
          rw [← Finset.sum_mul]
      _ ≤ b ^ 2 * ∑ j : Fin n, y j ^ 2 :=
          mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  exact (abs_le_of_sq_le_sq h1 (by positivity)).trans' (le_abs_self _)

theorem norm_res_le {n : ℕ} {T : ℕ → ℕ → ℝ} {σ : ℝ} (hσ0 : 0 < σ)
    (hσ : ∀ y : EuclideanSpace ℝ (Fin n), σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp T n y⟫_ℝ)
    {x u : EuclideanSpace ℝ (Fin n)} (hx : x + secOp T n x = u) : ‖x‖ ≤ ‖u‖ / σ := by
  have h1 : σ * ‖x‖ ^ 2 ≤ ‖x‖ * ‖u‖ := by
    have h0 := hσ x
    have h2 : ⟪x, u⟫_ℝ = ‖x‖ ^ 2 + ⟪x, secOp T n x⟫_ℝ := by
      rw [← hx, inner_add_right, real_inner_self_eq_norm_sq]
    have h3 := real_inner_le_norm x u
    nlinarith
  rcases (norm_nonneg x).eq_or_lt with h0 | h0
  · rw [← h0]; exact div_nonneg (norm_nonneg _) hσ0.le
  · rw [le_div_iff₀ hσ0]
    have : ‖x‖ * (‖x‖ * σ) ≤ ‖x‖ * ‖u‖ := by nlinarith [h1]
    exact le_of_mul_le_mul_left this h0

/-- **Comparison of the blocks of `C = (I+T)⁻¹` and `C_R = (I+a)⁻¹`.** -/
theorem block_close {T a C CR : ℕ → ℕ → ℝ} {σ σ2 b : ℝ} (P : SymPkg T C σ)
    (Pa : SymPkg a CR σ2) (hb0 : 0 ≤ b)
    (hb : ∀ n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (T i j - a i j) ^ 2 ≤ b ^ 2)
    (s : Finset ℕ) (v : ℕ → ℝ) :
    |∑ i ∈ s, ∑ j ∈ s, v i * CR i j * v j - ∑ i ∈ s, ∑ j ∈ s, v i * C i j * v j| ≤
      b / (σ * σ2) * ∑ i ∈ s, v i ^ 2 := by
  have hlim := (tendsto_inner_secRes Pa.symm Pa.hs Pa.pos Pa.sec Pa.inv s v).sub
    (tendsto_inner_secRes P.symm P.hs P.pos P.sec P.inv s v)
  refine le_of_tendsto hlim.abs ?_
  filter_upwards [eventually_lt_of_finset s] with n hn
  set u := finVec s v n with hu
  set x := secRes P.symm u with hxdef
  set y := secRes Pa.symm u with hydef
  have hx : x + secOp T n x = u :=
    secRes_spec P.symm u (fun k => secEig_pos P.symm P.pos P.sec n k)
  have hy : y + secOp a n y = u :=
    secRes_spec Pa.symm u (fun k => secEig_pos Pa.symm Pa.pos Pa.sec n k)
  have hxn : ‖x‖ ≤ ‖u‖ / σ := norm_res_le P.pos (P.sec n) hx
  have hyn : ‖y‖ ≤ ‖u‖ / σ2 := norm_res_le Pa.pos (Pa.sec n) hy
  have hbn : ∑ i : Fin n, ∑ j : Fin n, (T i j - a i j) ^ 2 ≤ b ^ 2 := by
    rw [Rank2.sum_fin_eq_range (fun i j => (T i j - a i j) ^ 2) n]
    exact hb n
  have hid : ⟪u, y⟫_ℝ - ⟪u, x⟫_ℝ = ⟪x, secOp (fun i j => T i j - a i j) n y⟫_ℝ := by
    rw [secOp_sub (fun i j => T i j - a i j) T a (fun _ _ => rfl), inner_sub_right]
    have h1 : ⟪u, y⟫_ℝ = ⟪x, y⟫_ℝ + ⟪secOp T n x, y⟫_ℝ := by
      conv_lhs => rw [← hx]
      rw [inner_add_left]
    have h2 : ⟪u, x⟫_ℝ = ⟪y, x⟫_ℝ + ⟪secOp a n y, x⟫_ℝ := by
      conv_lhs => rw [← hy]
      rw [inner_add_left]
    have h3 : ⟪secOp T n x, y⟫_ℝ = ⟪x, secOp T n y⟫_ℝ := secOp_isSymmetric P.symm x y
    have h4 : ⟪secOp a n y, x⟫_ℝ = ⟪x, secOp a n y⟫_ℝ := real_inner_comm _ _
    have h5 : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := real_inner_comm _ _
    rw [h1, h2, h3, h4, h5]
    ring
  have hMy : ‖secOp (fun i j => T i j - a i j) n y‖ ≤ b * ‖y‖ := norm_secOp_le _ y hb0 hbn
  have hnu : ‖u‖ ^ 2 = ∑ i ∈ s, v i ^ 2 := norm_finVec_sq s hn v
  rw [hid]
  calc |⟪x, secOp (fun i j => T i j - a i j) n y⟫_ℝ|
      ≤ ‖x‖ * ‖secOp (fun i j => T i j - a i j) n y‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ * (b * ‖y‖) := mul_le_mul_of_nonneg_left hMy (norm_nonneg _)
    _ ≤ (‖u‖ / σ) * (b * (‖u‖ / σ2)) := by
        have h1 : ‖y‖ ≤ ‖u‖ / σ2 := hyn
        have h2 : b * ‖y‖ ≤ b * (‖u‖ / σ2) := mul_le_mul_of_nonneg_left h1 hb0
        exact mul_le_mul hxn h2 (mul_nonneg hb0 (norm_nonneg _))
          (div_nonneg (norm_nonneg _) P.pos.le)
    _ = b / (σ * σ2) * ‖u‖ ^ 2 := by
        have := P.pos.ne'; have := Pa.pos.ne'
        field_simp
    _ = b / (σ * σ2) * ∑ i ∈ s, v i ^ 2 := by rw [hnu]

/-- The same comparison for the `ℓ²` quadratic forms. -/
theorem Q_close {T a C CR : ℕ → ℕ → ℝ} {σ σ2 b : ℝ} (P : SymPkg T C σ)
    (Pa : SymPkg a CR σ2) (hb0 : 0 ≤ b)
    (hb : ∀ n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (T i j - a i j) ^ 2 ≤ b ^ 2)
    {v : ℕ → ℝ} (hv : Summable fun i => v i ^ 2) :
    |(∑' i, v i * ∑' j, CR i j * v j) - ∑' i, v i * ∑' j, C i j * v j| ≤
      b / (σ * σ2) * ∑' i, v i ^ 2 :=
  le_of_tendsto_of_tendsto' ((Pa.limQ hv).sub (P.limQ hv)).abs
    ((hv.hasSum.tendsto_sum_nat).const_mul _) fun n => block_close P Pa hb0 hb (Finset.range n) v

/-! ### Comparison of the infima defining `lamG` -/

theorem ofReal_div_le {N q q' ρ : ℝ} (hq : 0 < q) (hq' : 0 < q') (hρ : 1 ≤ ρ)
    (h : q ≤ ρ * q') :
    ENNReal.ofReal N / ENNReal.ofReal q' ≤
      ENNReal.ofReal ρ * (ENNReal.ofReal N / ENNReal.ofReal q) := by
  rcases le_or_gt N 0 with hN | hN
  · rw [ENNReal.ofReal_of_nonpos hN]; simp
  · rw [← ENNReal.ofReal_div_of_pos hq', ← ENNReal.ofReal_div_of_pos hq,
      ← ENNReal.ofReal_mul (by linarith)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : ρ * (N / q) = (ρ * N) / q := by ring
    rw [e, div_le_div_iff₀ hq' hq]
    calc N * q ≤ N * (ρ * q') := mul_le_mul_of_nonneg_left h hN.le
      _ = ρ * N * q' := by ring

theorem lamG_close {lam' : ℕ → ℝ} {C C' : ℕ → ℕ → ℝ} {c η : ℝ} (hc : 0 < c) (hη0 : 0 ≤ η)
    (hηc : η ≤ c / 2)
    (hlow : ∀ v : ℕ → ℝ, Summable (fun i => v i ^ 2) →
      c * ∑' i, v i ^ 2 ≤ ∑' i, v i * ∑' j, C i j * v j)
    (hclose : ∀ v : ℕ → ℝ, Summable (fun i => v i ^ 2) →
      |(∑' i, v i * ∑' j, C' i j * v j) - ∑' i, v i * ∑' j, C i j * v j| ≤
        η * ∑' i, v i ^ 2) :
    lamG lam' C' ≤ ENNReal.ofReal (1 + 2 * (η / c)) * lamG lam' C ∧
    lamG lam' C ≤ ENNReal.ofReal (1 + 2 * (η / c)) * lamG lam' C' := by
  set ρ : ℝ := 1 + 2 * (η / c) with hρ
  have hθ0 : 0 ≤ η / c := div_nonneg hη0 hc.le
  have hθ : η / c ≤ 1 / 2 := by rw [div_le_iff₀ hc]; linarith
  have hρ1 : 1 ≤ ρ := by rw [hρ]; linarith
  have hρ0 : ENNReal.ofReal ρ ≠ 0 := by
    simpa using (by linarith : (0 : ℝ) < ρ)
  have hρt : ENNReal.ofReal ρ ≠ ⊤ := ENNReal.ofReal_ne_top
  have key : ∀ (F F' : (ℕ → ℝ) → ℝ≥0∞) (S : Set (ℕ → ℝ)),
      (∀ v ∈ S, F' v ≤ ENNReal.ofReal ρ * F v) →
      ⨅ v ∈ S, F' v ≤ ENNReal.ofReal ρ * ⨅ v ∈ S, F v := by
    intro F F' S h
    rw [ENNReal.mul_iInf_of_ne hρ0 hρt]
    refine le_iInf fun v => ?_
    rw [ENNReal.mul_iInf_of_ne hρ0 hρt]
    refine le_iInf fun hv => ?_
    exact (iInf₂_le v hv).trans (h v hv)
  -- the pointwise comparison
  have pw : ∀ v : ℕ → ℝ, Summable (fun i => v i ^ 2) → v ≠ 0 →
      ∃ q q' : ℝ, 0 < q ∧ 0 < q' ∧ q = ∑' i, v i * ∑' j, C i j * v j ∧
        q' = ∑' i, v i * ∑' j, C' i j * v j ∧ q ≤ ρ * q' ∧ q' ≤ ρ * q := by
    intro v hv2 hv0
    set V := ∑' i, v i ^ 2 with hV
    have hVpos : 0 < V := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h
        exact hv0 (funext fun i => by by_contra hi; exact h ⟨i, hi⟩)
      exact hv2.tsum_pos (fun _ => sq_nonneg _) i (by positivity)
    have h1 := hlow v hv2
    have h2 := hclose v hv2
    obtain ⟨h2a, h2b⟩ := abs_le.1 h2
    set q := ∑' i, v i * ∑' j, C i j * v j with hq
    set q' := ∑' i, v i * ∑' j, C' i j * v j with hq'
    have hqpos : 0 < q := lt_of_lt_of_le (mul_pos hc hVpos) h1
    -- `η V ≤ θ q`
    have hηV : η * V ≤ (η / c) * q := by
      calc η * V = (η / c) * (c * V) := by field_simp
        _ ≤ (η / c) * q := mul_le_mul_of_nonneg_left h1 hθ0
    have hq'pos : 0 < q' := by
      have : (1 - η / c) * q ≤ q' := by nlinarith
      nlinarith
    refine ⟨q, q', hqpos, hq'pos, rfl, rfl, ?_, ?_⟩
    · -- `q ≤ ρ q'`
      have h3 : (1 - η / c) * q ≤ q' := by nlinarith
      have h4 : q ≤ ρ * ((1 - η / c) * q) := by
        have : ρ * (1 - η / c) ≥ 1 := by
          rw [hρ]; nlinarith
        nlinarith
      calc q ≤ ρ * ((1 - η / c) * q) := h4
        _ ≤ ρ * q' := mul_le_mul_of_nonneg_left h3 (by linarith)
    · have h3 : q' ≤ (1 + η / c) * q := by nlinarith
      calc q' ≤ (1 + η / c) * q := h3
        _ ≤ ρ * q := by rw [hρ]; nlinarith
  unfold lamG
  refine ⟨key _ _ _ fun v hv => ?_, key _ _ _ fun v hv => ?_⟩
  · obtain ⟨hv2, -, hv0⟩ := hv
    obtain ⟨q, q', hq, hq', hqe, hq'e, hle, -⟩ := pw v hv2 hv0
    rw [← hqe, ← hq'e]
    exact ofReal_div_le hq hq' hρ1 hle
  · obtain ⟨hv2, -, hv0⟩ := hv
    obtain ⟨q, q', hq, hq', hqe, hq'e, -, hle⟩ := pw v hv2 hv0
    rw [← hqe, ← hq'e]
    exact ofReal_div_le hq' hq hρ1 hle

theorem tendsto_of_ratio {L : ℝ≥0∞} {LR : ℕ → ℝ≥0∞} {η : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ R, 0 ≤ η R)
    (h : ∀ᶠ R in atTop, LR R ≤ ENNReal.ofReal (1 + 2 * (η R / c)) * L ∧
      L ≤ ENNReal.ofReal (1 + 2 * (η R / c)) * LR R) :
    Tendsto LR atTop (𝓝 L) := by
  have hρ : Tendsto (fun R => 1 + 2 * (η R / c)) atTop (𝓝 1) := by
    have := ((hη.div_const c).const_mul 2).const_add 1
    simpa using this
  have hρ0 : ∀ R, 0 < 1 + 2 * (η R / c) := fun R => by
    have := div_nonneg (hη0 R) hc.le; linarith
  have hup : Tendsto (fun R => ENNReal.ofReal (1 + 2 * (η R / c)) * L) atTop (𝓝 L) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hρ) (Or.inl (by simp) : _ ∨ L ≠ ⊤)
    simpa using this
  have hlow : Tendsto (fun R => ENNReal.ofReal ((1 + 2 * (η R / c))⁻¹) * L) atTop (𝓝 L) := by
    have h1 : Tendsto (fun R => (1 + 2 * (η R / c))⁻¹) atTop (𝓝 1) := by
      simpa using hρ.inv₀ one_ne_zero
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inl (by simp) : _ ∨ L ≠ ⊤)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ (h.mono fun R hR => hR.1)
  filter_upwards [h] with R hR
  have h2 := hR.2
  calc ENNReal.ofReal ((1 + 2 * (η R / c))⁻¹) * L
      ≤ ENNReal.ofReal ((1 + 2 * (η R / c))⁻¹) *
          (ENNReal.ofReal (1 + 2 * (η R / c)) * LR R) := by gcongr
    _ = LR R := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 (hρ0 R).le),
          inv_mul_cancel₀ (hρ0 R).ne', ENNReal.ofReal_one, one_mul]

/-! ### The Part 2 data for the finite-rank approximations -/

section Data

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem tendsto_epsR {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
    (A : FiniteRankApprox W μ e) :
    Tendsto (fun R => (Rank2.epsR W μ e A R).toReal) atTop (𝓝 0) := by
  have hε : Tendsto (fun R => Rank2.epsR W μ e A R) atTop (𝓝 0) := A.approx.2.1
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hε
  rw [ENNReal.toReal_zero] at h
  exact h

/-- `σ` from Proposition 2.1 and the Hilbert–Schmidt bounds of `T - a^R` for large `R`. -/
theorem rank_core (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ) {e : ℕ → Torus d → ℝ}
    {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) :
    ∃ σ : ℝ, 0 < σ ∧
      (∀ n (y : EuclideanSpace ℝ (Fin n)),
        σ * ‖y‖ ^ 2 ≤ ‖y‖ ^ 2 + ⟪y, secOp (Tmat W μ e) n y⟫_ℝ) ∧
      ∀ᶠ R in atTop, ∀ n, ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (Tmat W μ e i j - A.a R i j) ^ 2 ≤ ((Rank2.epsR W μ e A R).toReal) ^ 2 := by
  have : IsProbabilityMeasure (μ : Measure (Torus d)) := inferInstance
  have h21 := prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ
  obtain ⟨σ, hσ0, hσ⟩ := secOp_ge_of_prop21 hyp he h21
  refine ⟨σ, hσ0, hσ, ?_⟩
  have hD := kerData_mk hyp hμ he
  have hee' : ∀ᵐ x ∂(μ : Measure (Torus d)), ∀ j, e j x =
      (fun i => (he.memLp i).aestronglyMeasurable.mk (e i)) j x := by
    rw [ae_all_iff]; exact fun j => (he.memLp j).aestronglyMeasurable.ae_eq_mk
  have hε : Tendsto (fun R => Rank2.epsR W μ e A R) atTop (𝓝 0) := A.approx.2.1
  have hδ : Tendsto (fun R => Rank2.deltaR W μ e A R) atTop (𝓝 0) := A.approx.2.2.2.2.1
  filter_upwards [hε.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1)),
    hδ.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))] with R h1 h2
  exact (Rank2.rank_data_aux hyp hD hee' A R (h1.trans ENNReal.one_lt_top).ne
    (h2.trans ENNReal.one_lt_top).ne).1

/-- The quadratic form of `a` on a vector supported in `s`, through a finite section. -/
theorem inner_secOp_finVec {n : ℕ} (a : ℕ → ℕ → ℝ) {s : Finset ℕ} (hn : ∀ i ∈ s, i < n)
    (v : ℕ → ℝ) :
    ⟪finVec s v n, secOp a n (finVec s v n)⟫_ℝ = ∑ i ∈ s, ∑ j ∈ s, a i j * (v i * v j) := by
  rw [inner_secOp_self]
  have h1 : ∀ i j : Fin n, a i j * (finVec s v n i * finVec s v n j) =
      if (i : ℕ) ∈ s then (if (j : ℕ) ∈ s then a i j * (v i * v j) else 0) else 0 := by
    intro i j
    simp only [finVec, PiLp.toLp_apply]
    split_ifs <;> simp
  simp_rw [h1]
  have h2 : ∀ i : Fin n, ∑ j : Fin n, (if (i : ℕ) ∈ s then
      (if (j : ℕ) ∈ s then a i j * (v i * v j) else 0) else 0) =
      if (i : ℕ) ∈ s then ∑ j ∈ s, a i j * (v i * v j) else 0 := by
    intro i
    split_ifs with hi
    · exact sum_fin_ite s hn (fun j => a i j * (v i * v j))
    · simp
  simp_rw [h2]
  exact sum_fin_ite s hn (fun i => ∑ j ∈ s, a i j * (v i * v j))

end Data

end Rank3

section Main

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- **Positivity export** (the step `I + a^R ≥ σ/2` of Part 2): for large `R`, the quadratic form of
`I + a^R` on vectors supported in `s R` is at least `(σ/2)` times the squared norm. -/
theorem positivity_export (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) :
    ∃ σ : ℝ, 0 < σ ∧ ∃ R0 : ℕ, ∀ R ≥ R0, ∀ v : ℕ → ℝ, (∀ i, i ∉ A.s R → v i = 0) →
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, v i * ((if i = j then 1 else 0) + A.a R i j) * v j ≥
        (σ / 2) * ∑ i ∈ A.s R, v i ^ 2 := by
  obtain ⟨σ, hσ0, hσ, hHS⟩ := Rank3.rank_core hd hyp hr hμ he A
  have hb := Rank3.tendsto_epsR A
  obtain ⟨R0, hR0⟩ := eventually_atTop.1
    (hHS.and (hb.eventually (gt_mem_nhds (half_pos hσ0))))
  refine ⟨σ, hσ0, R0, fun R hR v _ => ?_⟩
  obtain ⟨hHS', hb'⟩ := hR0 R hR
  have hbR0 : 0 ≤ (Rank2.epsR W μ e A R).toReal := ENNReal.toReal_nonneg
  set n := (A.s R).sup id + 1 with hn_def
  have hn : ∀ i ∈ A.s R, i < n := fun i hi => by
    have := Finset.le_sup (f := id) hi
    simp only [id] at this
    omega
  have h := Rank2.secOp_ge_of_close hbR0 hσ hHS' n (finVec (A.s R) v n)
  rw [norm_finVec_sq (A.s R) hn v, Rank3.inner_secOp_finVec (A.a R) hn v] at h
  have hexp : ∑ i ∈ A.s R, ∑ j ∈ A.s R, v i * ((if i = j then 1 else 0) + A.a R i j) * v j =
      ∑ i ∈ A.s R, v i ^ 2 + ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * (v i * v j) := by
    have e1 : ∀ i j, v i * ((if i = j then 1 else 0) + A.a R i j) * v j =
        (if i = j then v i ^ 2 else 0) + A.a R i j * (v i * v j) := by
      intro i j
      split_ifs with hij
      · subst hij; ring
      · ring
    simp_rw [e1, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [Finset.sum_ite_eq, hi]
  rw [hexp]
  have hV : 0 ≤ ∑ i ∈ A.s R, v i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [mul_nonneg (by linarith : 0 ≤ σ / 2 - (Rank2.epsR W μ e A R).toReal) hV]

/-- **Lemma 6.1, third conclusion** (`rank_errors`, part 3): `λ_{G,R} → λ_G`. -/
theorem rank_errors_part3 (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (C : ℕ → ℕ → ℝ) (hC : IsInverseOfIPlus (Tmat W μ e) C)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (CR : ℕ → ℕ → ℕ → ℝ)
    (hCR : ∀ᶠ R in atTop, IsInverseOfIPlus (A.a R) (CR R)) :
    Tendsto (fun R => lamG (lamShift lam) (CR R)) atTop (𝓝 (lamG (lamShift lam) C)) := by
  obtain ⟨σ, hσ0, hσ, hHS⟩ := Rank3.rank_core hd hyp hr hμ he A
  have hT := Tmat_symm hyp hμ he
  have hS := (hasSum_Tmat_sq hyp hμ he).summable
  have P : Rank3.SymPkg (Tmat W μ e) C σ := ⟨hT, hS, hσ0, hσ, hC⟩
  set ST := ∑' p : ℕ × ℕ, Tmat W μ e p.1 p.2 ^ 2 with hST
  have hST0 : 0 ≤ ST := tsum_nonneg fun _ => sq_nonneg _
  have hΛpos : 0 < 3 / 2 + ST / 2 := by linarith
  set c : ℝ := (3 / 2 + ST / 2)⁻¹ with hc
  have hcpos : 0 < c := inv_pos.2 hΛpos
  have hσ2 : 0 < σ / 2 := half_pos hσ0
  set η : ℕ → ℝ := fun R => (Rank2.epsR W μ e A R).toReal / (σ * (σ / 2)) with hη
  have hη0 : ∀ R, 0 ≤ η R := fun R => div_nonneg ENNReal.toReal_nonneg (by positivity)
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have := (Rank3.tendsto_epsR A).div_const (σ * (σ / 2))
    simpa using this
  refine Rank3.tendsto_of_ratio hcpos hηlim hη0 ?_
  filter_upwards [hHS, hCR, (Rank3.tendsto_epsR A).eventually (gt_mem_nhds (half_pos hσ0)),
    hηlim.eventually (gt_mem_nhds (half_pos hcpos))] with R hHSR hCRR hbR hηR
  have hbR0 : 0 ≤ (Rank2.epsR W μ e A R).toReal := ENNReal.toReal_nonneg
  have hSa : Summable fun p : ℕ × ℕ => A.a R p.1 p.2 ^ 2 := by
    refine summable_of_ne_finset_zero (s := A.s R ×ˢ A.s R) fun p hp => ?_
    have : p.1 ∉ A.s R ∨ p.2 ∉ A.s R := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hp (Finset.mem_product.2 h)
    rw [A.supp R p.1 p.2 this]; norm_num
  have Pa : Rank3.SymPkg (A.a R) (CR R) (σ / 2) :=
    ⟨A.symm R, hSa, hσ2, fun n y => by
      have h := Rank2.secOp_ge_of_close hbR0 hσ hHSR n y
      have hy : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
      nlinarith [mul_nonneg (by linarith : 0 ≤ σ / 2 - (Rank2.epsR W μ e A R).toReal) hy],
      hCRR⟩
  refine Rank3.lamG_close hcpos (hη0 R) hηR.le ?_ ?_
  · intro v hv
    have := P.Qlower hv
    rwa [hc, inv_mul_eq_div]
  · intro v hv
    exact Rank3.Q_close P Pa hbR0 hHSR hv

/-- **Lemma 6.1, fourth conclusion** (`rank_errors`, part 4): `b_R → b`. -/
theorem rank_errors_part4 (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (C : ℕ → ℕ → ℝ) (hC : IsInverseOfIPlus (Tmat W μ e) C)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (CR : ℕ → ℕ → ℕ → ℝ)
    (hCR : ∀ᶠ R in atTop, IsInverseOfIPlus (A.a R) (CR R)) :
    Tendsto (fun R => bRate (μ : Measure (Torus d)) lam (CR R)) atTop
      (𝓝 (bRate (μ : Measure (Torus d)) lam C)) := by
  unfold bRate
  exact tendsto_const_nhds.min (rank_errors_part3 hd hyp hr μ hμ e lam he C hC A CR hCR)

end Main

end SharpLSI.FL
