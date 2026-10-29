import FullLabeledLSI.Infra.HypercontrGrossStep

/-!
# Gross's hypercontractivity theorem, abstract finite-dimensional form

Under `GrossHyp` (integration by parts + logarithmic Sobolev inequality for the family `M_k` with
weights `G c`), the heat flow `c ↦ c(t)`, `c(t)_k = e^{-tν_k} c_k`, satisfies
`‖u_{c(t)}‖_{q(t)} ≤ ‖u_c‖_2` with `q(t) = 1 + e^{2at}`. Corollary: `‖u_c‖_q ≤ (q-1)^{L/(2a)} ‖u_c‖_2`
for coefficient vectors supported on `{ν ≤ L}` when the `M_k` are orthonormal.
-/

noncomputable section

namespace SharpLSI.FL.Gross

open MeasureTheory Real Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {K : Type*} [Fintype K]
  {P : Measure Ω} [IsProbabilityMeasure P] {M : K → Ω → ℝ} {ν : K → ℝ}
  {G : (K → ℝ) → Ω → ℝ} {a : ℝ}

lemma memLp_M_of_ne_top (hM : ∀ k (n : ℕ), MemLp (M k) n P) (k : K) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (M k) p P := by
  refine (hM k ⌈p.toReal⌉₊).mono_exponent ?_
  calc p = ENNReal.ofReal p.toReal := (ENNReal.ofReal_toReal hp).symm
    _ ≤ ENNReal.ofReal (⌈p.toReal⌉₊ : ℝ) := ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
    _ = ((⌈p.toReal⌉₊ : ℕ) : ℝ≥0∞) := ENNReal.ofReal_natCast _

lemma memLp_uFun (hM : ∀ k (n : ℕ), MemLp (M k) n P) (c : K → ℝ) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (uFun M c) p P := by
  have : MemLp (fun ω => ∑ k, c k * M k ω) p P :=
    memLp_finsetSum Finset.univ fun k _ => (memLp_M_of_ne_top hM k hp).const_mul (c k)
  exact this

lemma flow_zero (ν c : K → ℝ) : flow ν 0 c = c := by
  funext k; simp [flow]

lemma Phi_pos (hM : ∀ k (n : ℕ), MemLp (M k) n P) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) (c : K → ℝ)
    (t : ℝ) : 0 < ∫ ω, Ft M ν c a ε t ω ∂P := by
  have hq : 0 ≤ qexp a t / 2 := by have := qexp_pos a t; positivity
  have h1 : (ε ^ 2) ^ (qexp a t / 2) ≤ ∫ ω, Ft M ν c a ε t ω ∂P := by
    calc (ε ^ 2) ^ (qexp a t / 2) = ∫ ω, (ε ^ 2) ^ (qexp a t / 2) ∂P := by simp
      _ ≤ _ := integral_mono (integrable_const _) (integrable_Ft hM ha hε t) fun ω => by
          unfold Ft Bt
          exact Real.rpow_le_rpow (by positivity) (by nlinarith [sq_nonneg (uT M ν c t ω)]) hq
  exact lt_of_lt_of_le (by positivity) h1

lemma Phi_zero (hM : ∀ k (n : ℕ), MemLp (M k) n P) (c : K → ℝ) (a ε : ℝ) :
    ∫ ω, Ft M ν c a ε 0 ω ∂P = (∫ ω, uFun M c ω ^ 2 ∂P) + ε ^ 2 := by
  have hu : Integrable (fun ω => uFun M c ω ^ 2) P := (memLp_uFun hM c (p := 2) (by simp)).integrable_sq
  have e : ∀ ω, Ft M ν c a ε 0 ω = uFun M c ω ^ 2 + ε ^ 2 := by
    intro ω
    unfold Ft Bt uT
    rw [flow_zero, qexp_zero]
    norm_num
  simp_rw [e]
  rw [integral_add hu (integrable_const _)]
  simp

/-- The comparison inequality `∫ ‖u_t‖^q ≤ (∫ u² + ε²)^{q/2}` for every `ε > 0`. -/
lemma integral_norm_rpow_le_aux (h : GrossHyp P M ν G a) (c : K → ℝ) {ε : ℝ} (hε : 0 < ε)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, ‖uFun M (flow ν t c) ω‖ ^ qexp a t ∂P ≤
      ((∫ ω, uFun M c ω ^ 2 ∂P) + ε ^ 2) ^ (qexp a t / 2) := by
  have ha := h.ha
  have hM := h.memLp
  have hq0 : 0 < qexp a t := qexp_pos a t
  -- the ODE comparison
  have hode := gross_ode ha (Φ := fun s => ∫ ω, Ft M ν c a ε s ω ∂P)
    (Φ' := fun s => ∫ ω, Dt M ν c a ε s ω ∂P)
    (fun s _ => Phi_pos hM ha hε c s)
    (fun s _ => (hasDerivAt_Phi M ν c a ε hM ha hε s).2)
    (fun s hs => Dt_integral_le h hε hs) t ht
  beta_reduce at hode
  rw [Phi_zero hM c a ε] at hode
  set Y := (∫ ω, uFun M c ω ^ 2 ∂P) + ε ^ 2 with hY
  have hYpos : 0 < Y := by
    have : 0 ≤ ∫ ω, uFun M c ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    positivity
  set Φt := ∫ ω, Ft M ν c a ε t ω ∂P with hΦt
  have hΦpos : 0 < Φt := Phi_pos hM ha hε c t
  -- `Φ(t) ≤ Y^{q/2}`
  have hlog : Real.log Φt ≤ qexp a t / 2 * Real.log Y := by
    rw [div_le_div_iff₀ hq0 (by norm_num : (0:ℝ) < 2)] at hode
    nlinarith
  have hΦle : Φt ≤ Y ^ (qexp a t / 2) := by
    rw [Real.rpow_def_of_pos hYpos]
    calc Φt = Real.exp (Real.log Φt) := (Real.exp_log hΦpos).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  -- `∫ ‖u_t‖^q ≤ Φ(t)`
  have hint : Integrable (fun ω => ‖uFun M (flow ν t c) ω‖ ^ qexp a t) P := by
    have := (memLp_uFun hM (flow ν t c) (p := ENNReal.ofReal (qexp a t))
      ENNReal.ofReal_ne_top).integrable_norm_rpow'
    rwa [ENNReal.toReal_ofReal hq0.le] at this
  refine le_trans (integral_mono hint (integrable_Ft hM ha hε t) fun ω => ?_) hΦle
  unfold Ft Bt
  have hqq : 0 ≤ qexp a t / 2 := by positivity
  calc ‖uFun M (flow ν t c) ω‖ ^ qexp a t
      = (uT M ν c t ω ^ 2) ^ (qexp a t / 2) := by
        rw [Real.norm_eq_abs, show qexp a t = 2 * (qexp a t / 2) by ring, Real.rpow_mul (abs_nonneg _)]
        simp [uT, Real.rpow_two, sq_abs]
    _ ≤ _ := Real.rpow_le_rpow (sq_nonneg _) (by nlinarith [sq_nonneg ε]) hqq


/-- `∫ ‖u_{c(t)}‖^{q(t)} ≤ (∫ u_c²)^{q(t)/2}`. -/
lemma integral_norm_rpow_le (h : GrossHyp P M ν G a) (c : K → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, ‖uFun M (flow ν t c) ω‖ ^ qexp a t ∂P ≤
      (∫ ω, uFun M c ω ^ 2 ∂P) ^ (qexp a t / 2) := by
  set Y : ℝ := ∫ ω, uFun M c ω ^ 2 ∂P with hYdef
  have hq : 0 ≤ qexp a t / 2 := by have := qexp_pos a t; positivity
  have hcont : Continuous fun ε : ℝ => (Y + ε ^ 2) ^ (qexp a t / 2) :=
    (continuous_const.add (continuous_pow 2)).rpow_const (fun _ => Or.inr hq)
  have h2 : Tendsto (fun ε : ℝ => (Y + ε ^ 2) ^ (qexp a t / 2)) (𝓝[>] 0)
      (𝓝 (Y ^ (qexp a t / 2))) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using this
  exact ge_of_tendsto h2 (eventually_nhdsWithin_of_forall fun ε hε =>
    integral_norm_rpow_le_aux h c hε ht)

/-- **Gross's hypercontractivity theorem** (abstract finite-dimensional form):
`‖u_{c(t)}‖_{L^{q(t)}} ≤ ‖u_c‖_{L²}` for `t ≥ 0`, `q(t) = 1 + e^{2at}`, `c(t)_k = e^{-tν_k} c_k`. -/
theorem gross_finite (h : GrossHyp P M ν G a) (c : K → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    eLpNorm (uFun M (flow ν t c)) (ENNReal.ofReal (qexp a t)) P ≤ eLpNorm (uFun M c) 2 P := by
  have hM := h.memLp
  have hq0 : 0 < qexp a t := qexp_pos a t
  have h1 := memLp_uFun hM (flow ν t c) (p := ENNReal.ofReal (qexp a t)) ENNReal.ofReal_ne_top
  have h2 := memLp_uFun hM c (p := 2) (by simp)
  rw [h1.eLpNorm_eq_integral_rpow_norm (by simpa using hq0) ENNReal.ofReal_ne_top,
    h2.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  apply ENNReal.ofReal_le_ofReal
  rw [ENNReal.toReal_ofReal hq0.le]
  have hY2 : ∫ ω, ‖uFun M c ω‖ ^ (2 : ℝ≥0∞).toReal ∂P = ∫ ω, uFun M c ω ^ 2 ∂P := by
    simp [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [hY2]
  have hY : 0 ≤ ∫ ω, uFun M c ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hA := integral_norm_rpow_le h c ht
  calc (∫ ω, ‖uFun M (flow ν t c) ω‖ ^ qexp a t ∂P) ^ (qexp a t)⁻¹
      ≤ ((∫ ω, uFun M c ω ^ 2 ∂P) ^ (qexp a t / 2)) ^ (qexp a t)⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun ω => by positivity) hA (inv_nonneg.2 hq0.le)
    _ = (∫ ω, uFun M c ω ^ 2 ∂P) ^ ((2 : ℝ≥0∞).toReal)⁻¹ := by
        rw [← Real.rpow_mul hY]
        congr 1
        simp only [ENNReal.toReal_ofNat]
        field_simp


section Poly

variable [DecidableEq K]

/-- `‖u_c‖₂² = ∑ c_k²` for orthonormal `M`. -/
lemma integral_uFun_sq (hM : ∀ k (n : ℕ), MemLp (M k) n P)
    (hortho : ∀ k l, ∫ ω, M k ω * M l ω ∂P = if k = l then 1 else 0) (c : K → ℝ) :
    ∫ ω, uFun M c ω ^ 2 ∂P = ∑ k, c k ^ 2 := by
  have hint : ∀ k l, Integrable (fun ω => M k ω * M l ω) P := fun k l =>
    (memLp_M_of_ne_top hM k (p := 2) (by simp)).integrable_mul
      (memLp_M_of_ne_top hM l (p := 2) (by simp))
  have e : ∀ ω, uFun M c ω ^ 2 = ∑ k, ∑ l, c k * c l * (M k ω * M l ω) := by
    intro ω
    unfold uFun
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hint k l).const_mul _]
  have : ∀ k, ∫ ω, ∑ l, c k * c l * (M k ω * M l ω) ∂P = c k ^ 2 := by
    intro k
    rw [integral_finsetSum _ fun l _ => (hint k l).const_mul _]
    simp_rw [integral_const_mul, hortho]
    simp [sq]
  simp_rw [this]

lemma eLpNorm_uFun_two (hM : ∀ k (n : ℕ), MemLp (M k) n P)
    (hortho : ∀ k l, ∫ ω, M k ω * M l ω ∂P = if k = l then 1 else 0) (c : K → ℝ) :
    eLpNorm (uFun M c) 2 P = ENNReal.ofReal (Real.sqrt (∑ k, c k ^ 2)) := by
  rw [(memLp_uFun hM c (p := 2) (by simp)).eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  congr 1
  have : ∫ ω, ‖uFun M c ω‖ ^ (2 : ℝ≥0∞).toReal ∂P = ∑ k, c k ^ 2 := by
    rw [← integral_uFun_sq hM hortho c]
    simp [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [this, Real.sqrt_eq_rpow]
  simp

/-- The polynomial moment bound `‖u_c‖_q ≤ (q-1)^{L/(2a)} ‖u_c‖₂` for coefficient vectors supported on
`{ν ≤ L}` (orthonormal `M`, `q ≥ 2`). -/
theorem poly_moment_bound (h : GrossHyp P M ν G a)
    (hortho : ∀ k l, ∫ ω, M k ω * M l ω ∂P = if k = l then 1 else 0)
    (c : K → ℝ) {L : ℝ} (hL : ∀ k, c k ≠ 0 → ν k ≤ L) {q : ℝ} (hq : 2 ≤ q) :
    eLpNorm (uFun M c) (ENNReal.ofReal q) P ≤
      ENNReal.ofReal ((q - 1) ^ (L / (2 * a))) * eLpNorm (uFun M c) 2 P := by
  have ha := h.ha
  have hM := h.memLp
  have hq1 : 1 ≤ q - 1 := by linarith
  have hq1pos : 0 < q - 1 := by linarith
  set s : ℝ := Real.log (q - 1) / (2 * a) with hs
  have hs0 : 0 ≤ s := div_nonneg (Real.log_nonneg hq1) (by positivity)
  set d : K → ℝ := fun k => Real.exp (s * ν k) * c k with hd
  have hflow : flow ν s d = c := by
    funext k
    simp only [flow, hd]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have hqs : qexp a s = q := by
    unfold qexp
    have : 2 * a * s = Real.log (q - 1) := by rw [hs]; field_simp
    rw [this, Real.exp_log hq1pos]; ring
  have hgross := gross_finite h d hs0
  rw [hflow, hqs] at hgross
  refine hgross.trans ?_
  rw [eLpNorm_uFun_two hM hortho, eLpNorm_uFun_two hM hortho]
  have hexp : Real.exp (s * L) = (q - 1) ^ (L / (2 * a)) := by
    rw [Real.rpow_def_of_pos hq1pos, hs]
    congr 1; ring
  rw [← hexp, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  have hsum : ∑ k, d k ^ 2 ≤ Real.exp (s * L) ^ 2 * ∑ k, c k ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hck : c k = 0
    · simp [hd, hck]
    · have hνk := hL k hck
      have h1 : Real.exp (s * ν k) ^ 2 ≤ Real.exp (s * L) ^ 2 :=
        pow_le_pow_left₀ (Real.exp_pos _).le
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hνk hs0)) 2
      calc d k ^ 2 = Real.exp (s * ν k) ^ 2 * c k ^ 2 := by simp only [hd]; rw [mul_pow]
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  calc Real.sqrt (∑ k, d k ^ 2) ≤ Real.sqrt (Real.exp (s * L) ^ 2 * ∑ k, c k ^ 2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.exp (s * L) * Real.sqrt (∑ k, c k ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]

end Poly

end SharpLSI.FL.Gross

end
