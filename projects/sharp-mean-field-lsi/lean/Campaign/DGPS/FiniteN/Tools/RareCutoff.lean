import DGPS.FiniteN.Tools.PositiveRate

/-!
# Rare cutoff variance and entropy weights (FIN018)

Let `0 ≤ f_N ≤ 1`, `f_N = 1` on `C_N`, `f_N = 0` off `S_N`, and
`c m_N ≤ P_N(C_N)`, `P_N(S_N) ≤ C m_N` with `m_N = N^β e^{-NΔ}`, `Δ > 0`.  With
`n_N = P_N(f_N²)`:
* `n_N` is comparable to `m_N` (`c m_N ≤ n_N ≤ C m_N`);
* `Var(f_N) ≥ n_N / 2` for large `N` (Cauchy-Schwarz `(P f)² ≤ P(S) n`);
* `Ent(f_N²) ≥ (Δ/2) N n_N` for large `N` (entropy `= P(f² log f²) - n log n`);
* if `E_N(f_N) ≤ C' N^{-α} n_N` then `λ_N ≤ C'' N^{-α}`, and for symmetric `f_N`,
  `r_N^sym ≤ C'' N^{-(α+1)}`.

Design notes (R5):
* Sequences are indexed by `N : ℕ+` with `f N : ParticleH1 A N`; all hypotheses and the
  conclusions are "for `N ≥ N₀`" (resp. "for `N ≥ N₁`"), `rareMass β Δ N = N^β e^{-NΔ}`.
* `supp f_N ⊂ S_N` is used in the weaker pointwise form `x ∉ S_N → f_N x = 0`.  The middle
  inequality `P(C_N) ≤ P(S_N)` of the source is a consequence (`C_N ⊆ S_N`) and not assumed.
* The rate conclusions are stated both in `ℝ≥0∞` (`≤ ofReal …`) and, via the real bridge, for
  `toReal`.  The upper bounds themselves force finiteness, so no positivity/finiteness input
  from FIN001 and no `0 < d` assumption is needed (for `d = 0` the hypotheses are
  inconsistent for large `N`); the file imports FIN001's module for the rate definitions
  (`particlePoincareRate`).
* Constants: `c' = Δ/2`, `C'' = 2C' + 4C'/Δ`.
-/

open MeasureTheory
open scoped ENNReal Asymptotics

namespace DGPS.FiniteN.RareCutoff

variable {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]

theorem sq_le_mul_of_le_indicator {f : α → ℝ} {S : Set α} (hS : MeasurableSet S)
    (hf : MemLp f 2 P) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) (hS0 : ∀ x, x ∉ S → f x = 0) :
    (∫ x, f x ∂P) ^ 2 ≤ (∫ x, f x ^ 2 ∂P) * P.real S := by
  have hint : Integrable f P := hf.integrable (by norm_num)
  have hint2 : Integrable (fun x => f x ^ 2) P := hf.integrable_sq
  have hfS : ∀ x, f x ≤ S.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ S
    · simpa [hx] using h1 x
    · simp [hx, hS0 x hx]
  have hindint : Integrable (S.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hS
  have hsval : ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂P = P.real S := by
    rw [integral_indicator hS]; simp
  have hasle : ∫ x, f x ∂P ≤ P.real S := by
    rw [← hsval]; exact integral_mono hint hindint hfS
  have ha0 : 0 ≤ ∫ x, f x ∂P := integral_nonneg h0
  set a := ∫ x, f x ∂P with ha
  set n := ∫ x, f x ^ 2 ∂P with hn
  set s := P.real S with hs
  have hs0 : 0 ≤ s := measureReal_nonneg
  -- quadratic inequality: 0 ≤ ∫ (f - t 1_S)^2 = n - 2 t a + t^2 s
  have key : ∀ t : ℝ, 0 ≤ n - 2 * t * a + t ^ 2 * s := by
    intro t
    have h : ∫ x, (f x - t * S.indicator (fun _ => (1 : ℝ)) x) ^ 2 ∂P
        = n - 2 * t * a + t ^ 2 * s := by
      have e : ∀ x, (f x - t * S.indicator (fun _ => (1 : ℝ)) x) ^ 2
          = f x ^ 2 - 2 * t * f x + t ^ 2 * S.indicator (fun _ => (1 : ℝ)) x := by
        intro x
        by_cases hx : x ∈ S
        · simp [hx]; ring
        · simp [hx, hS0 x hx]
      simp_rw [e]
      have i1 : Integrable (fun x => f x ^ 2 - 2 * t * f x) P :=
        hint2.sub (hint.const_mul _)
      have i2 : Integrable (fun x => t ^ 2 * S.indicator (fun _ => (1 : ℝ)) x) P :=
        hindint.const_mul _
      rw [integral_add i1 i2, integral_sub hint2 (hint.const_mul _), integral_const_mul,
        integral_const_mul, hsval]
    rw [← h]
    exact integral_nonneg fun x => sq_nonneg _
  rcases hs0.eq_or_lt with h | h
  · have : a = 0 := le_antisymm (h ▸ hasle) ha0
    rw [this, ← h]; simp
  · have := key (a / s)
    have e : n - 2 * (a / s) * a + (a / s) ^ 2 * s = n - a ^ 2 / s := by field_simp; ring
    rw [e, sub_nonneg, div_le_iff₀ h] at this
    linarith


theorem entropy_sq_ge {f : α → ℝ} {S : Set α} (hS : MeasurableSet S)
    (hf : MemLp f 2 P) (h1 : ∀ x, f x ≤ 1) (h0 : ∀ x, 0 ≤ f x)
    (hS0 : ∀ x, x ∉ S → f x = 0) :
    ENNReal.ofReal (-(P.real S) - (∫ x, f x ^ 2 ∂P) * Real.log (∫ x, f x ^ 2 ∂P)) ≤
      DGPS.homogeneousEntropy P (fun x => f x ^ 2) := by
  have hint2 : Integrable (fun x => f x ^ 2) P := hf.integrable_sq
  have hsq1 : ∀ x, f x ^ 2 ≤ 1 := fun x => by
    have := h0 x; have := h1 x; nlinarith
  have hlogm : AEStronglyMeasurable (fun x => f x ^ 2 * Real.log (f x ^ 2)) P :=
    ((hf.aemeasurable.pow_const 2).mul
      (Real.measurable_log.comp_aemeasurable (hf.aemeasurable.pow_const 2))).aestronglyMeasurable
  have hlog : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) P := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hlogm (ae_of_all _ fun x => ?_)
    have hv0 : 0 ≤ f x ^ 2 := sq_nonneg _
    have hlow := DGPS.self_mul_log_sub_add_one_nonneg hv0
    have hup : f x ^ 2 * Real.log (f x ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hv0 (Real.log_nonpos hv0 (hsq1 x))
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [hsq1 x]
  rw [DGPS.homogeneousEntropy_eq_formula (ae_of_all _ fun x => sq_nonneg (f x)) hint2 hlog]
  apply ENNReal.ofReal_le_ofReal
  have hindint : Integrable (S.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hS
  have hsval : ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂P = P.real S := by
    rw [integral_indicator hS]; simp
  have : ∫ x, -S.indicator (fun _ => (1 : ℝ)) x ∂P ≤ ∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂P := by
    refine integral_mono hindint.neg hlog fun x => ?_
    by_cases hx : x ∈ S
    · have := DGPS.self_mul_log_sub_add_one_nonneg (sq_nonneg (f x))
      have := hsq1 x
      have := sq_nonneg (f x)
      simp only [hx, Set.indicator_of_mem]; linarith
    · simp [hx, hS0 x hx]
  rw [integral_neg, hsval] at this
  linarith


theorem measureReal_le_integral_sq {f : α → ℝ} {C : Set α} (hC : MeasurableSet C)
    (hf : MemLp f 2 P) (hC1 : ∀ x, x ∈ C → f x = 1) :
    P.real C ≤ ∫ x, f x ^ 2 ∂P := by
  have hind : Integrable (C.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hC
  rw [← show ∫ x, C.indicator (fun _ => (1 : ℝ)) x ∂P = P.real C by
    rw [integral_indicator hC]; simp]
  refine integral_mono hind hf.integrable_sq fun x => ?_
  by_cases hx : x ∈ C
  · simp [hx, hC1 x hx]
  · simp [hx, sq_nonneg]

theorem integral_sq_le_measureReal {f : α → ℝ} {S : Set α} (hS : MeasurableSet S)
    (hf : MemLp f 2 P) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1)
    (hS0 : ∀ x, x ∉ S → f x = 0) :
    ∫ x, f x ^ 2 ∂P ≤ P.real S := by
  have hind : Integrable (S.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hS
  rw [← show ∫ x, S.indicator (fun _ => (1 : ℝ)) x ∂P = P.real S by
    rw [integral_indicator hS]; simp]
  refine integral_mono hf.integrable_sq hind fun x => ?_
  by_cases hx : x ∈ S
  · have := h0 x; have := h1 x
    simp only [hx, Set.indicator_of_mem]; nlinarith
  · simp [hx, hS0 x hx]

/-- The rare-state mass scale `m_N = N^β e^{-NΔ}`. -/
noncomputable def rareMass (β Δ : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ β * Real.exp (-((N : ℝ) * Δ))

theorem rareMass_pos (β Δ : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < rareMass β Δ N := by
  unfold rareMass
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

theorem rareMass_tendsto (β : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) :
    Filter.Tendsto (rareMass β Δ) Filter.atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero β Δ hΔ).comp tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp only [Function.comp, rareMass]
  rw [neg_mul, mul_comm Δ]

theorem eventually_scales (β c Cm : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → 1 ≤ N ∧ Cm * rareMass β Δ N ≤ 1 / 2 ∧
      β * Real.log N + (Real.log Cm + Cm / c) ≤ N * Δ / 2 := by
  have h1 : ∀ᶠ N : ℕ in Filter.atTop, 1 ≤ N := Filter.eventually_ge_atTop 1
  have h2 : ∀ᶠ N : ℕ in Filter.atTop, Cm * rareMass β Δ N ≤ 1 / 2 := by
    have := (rareMass_tendsto β hΔ).const_mul Cm
    rw [mul_zero] at this
    exact this.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have h3 : ∀ᶠ N : ℕ in Filter.atTop, β * Real.log N + (Real.log Cm + Cm / c) ≤ N * Δ / 2 := by
    have hlo : (fun x : ℝ => β * Real.log x + (Real.log Cm + Cm / c)) =o[Filter.atTop] id :=
      ((Real.isLittleO_log_id_atTop.const_mul_left β).add
        (Asymptotics.isLittleO_const_id_atTop (Real.log Cm + Cm / c)))
    have := (hlo.def (by positivity : 0 < Δ / 2))
    have h' := tendsto_natCast_atTop_atTop (R := ℝ) |>.eventually this
    filter_upwards [h'] with N hN
    simp only [id, Real.norm_eq_abs, Nat.abs_cast] at hN
    have := le_abs_self (β * Real.log N + (Real.log Cm + Cm / c))
    nlinarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 (h1.and (h2.and h3))
  exact ⟨N₁, fun N hN => ⟨(hN₁ N hN).1, (hN₁ N hN).2.1, (hN₁ N hN).2.2⟩⟩

end DGPS.FiniteN.RareCutoff

namespace DGPS.FiniteN

open DGPS DGPS.Particle MeasureTheory DGPS.FiniteN.RareCutoff

/-- Quantitative form of the weights with `c' = Δ/2`. -/
theorem rare_cutoff_scales {d : ℕ} (A : InteractionData d)
    (f : (N : ℕ+) → ParticleH1 A N) (Cs Ss : (N : ℕ+) → Set (ParticleSpace d N))
    (β Δ c Cm : ℝ) (hΔ : 0 < Δ) (hc : 0 < c) (N₀ : ℕ)
    (hCs : ∀ N, MeasurableSet (Cs N)) (hSs : ∀ N, MeasurableSet (Ss N))
    (hf0 : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, 0 ≤ f N x)
    (hf1 : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, f N x ≤ 1)
    (hfC : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, x ∈ Cs N → f N x = 1)
    (hfS : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, x ∉ Ss N → f N x = 0)
    (hCmass : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → c * rareMass β Δ N ≤ (particleLaw A N).real (Cs N))
    (hSmass : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → (particleLaw A N).real (Ss N) ≤ Cm * rareMass β Δ N) :
    ∃ N₁ : ℕ, N₀ ≤ N₁ ∧ ∀ N : ℕ+, N₁ ≤ (N : ℕ) →
      (c * rareMass β Δ N ≤ ∫ x, f N x ^ 2 ∂particleLaw A N ∧
        ∫ x, f N x ^ 2 ∂particleLaw A N ≤ Cm * rareMass β Δ N) ∧
      (∫ x, f N x ^ 2 ∂particleLaw A N) / 2 ≤ ProbabilityTheory.variance (f N).1 (particleLaw A N) ∧
      ENNReal.ofReal (Δ / 2 * (N : ℕ) * ∫ x, f N x ^ 2 ∂particleLaw A N) ≤ particleEntropy A N (f N) := by
  obtain ⟨N₁, hN₁⟩ := eventually_scales β c Cm hΔ
  refine ⟨max N₀ N₁, le_max_left _ _, fun N hN => ?_⟩
  have hN0 : N₀ ≤ (N : ℕ) := (le_max_left _ _).trans hN
  have hNN1 : N₁ ≤ (N : ℕ) := (le_max_right _ _).trans hN
  obtain ⟨hN1, hsmall, hlog⟩ := hN₁ N hNN1
  have hmpos := rareMass_pos β Δ hN1
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  set P := particleLaw A N with hP
  have hmem : MemLp (f N).1 2 P := (isParticleWeakGradient_particleWeakGradient (f N)).memLp
  have hnlo : c * rareMass β Δ N ≤ ∫ x, f N x ^ 2 ∂P :=
    (hCmass N hN0).trans (measureReal_le_integral_sq (hCs N) hmem (hfC N hN0))
  have hnhi : ∫ x, f N x ^ 2 ∂P ≤ Cm * rareMass β Δ N :=
    (integral_sq_le_measureReal (hSs N) hmem (hf0 N hN0) (hf1 N hN0) (hfS N hN0)).trans
      (hSmass N hN0)
  have hnpos : 0 < ∫ x, f N x ^ 2 ∂P := lt_of_lt_of_le (by positivity) hnlo
  have hCmpos : 0 < Cm := by
    by_contra h
    have h := not_lt.1 h
    nlinarith
  have hsS : P.real (Ss N) ≤ Cm * rareMass β Δ N := hSmass N hN0
  refine ⟨⟨hnlo, hnhi⟩, ?_, ?_⟩
  · have hvar := ProbabilityTheory.variance_eq_sub hmem
    have hcs := sq_le_mul_of_le_indicator (hSs N) hmem (hf0 N hN0) (hf1 N hN0) (hfS N hN0)
    have : ProbabilityTheory.variance (f N).1 P = (∫ x, f N x ^ 2 ∂P) - (∫ x, f N x ∂P) ^ 2 := hvar
    nlinarith
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      (entropy_sq_ge (hSs N) hmem (hf1 N hN0) (hf0 N hN0) (hfS N hN0))
    set n := ∫ x, f N x ^ 2 ∂P with hn
    have hlogn : Real.log n ≤ Real.log Cm + (β * Real.log ((N : ℕ) : ℝ) - ((N : ℕ) : ℝ) * Δ) := by
      calc Real.log n ≤ Real.log (Cm * rareMass β Δ N) := Real.log_le_log hnpos hnhi
        _ = _ := by
          unfold rareMass
          rw [Real.log_mul hCmpos.ne' (by positivity), Real.log_mul (by positivity)
            (Real.exp_pos _).ne', Real.log_rpow hNpos, Real.log_exp]
          ring
    have hsn : P.real (Ss N) ≤ Cm / c * n := by
      calc P.real (Ss N) ≤ Cm * rareMass β Δ N := hsS
        _ ≤ Cm * (n / c) := by
          gcongr
          rw [le_div_iff₀ hc]; linarith
        _ = Cm / c * n := by ring
    have h1 := mul_le_mul_of_nonneg_left hlogn hnpos.le
    have h2 := mul_le_mul_of_nonneg_left hlog hnpos.le
    nlinarith


/-- FIN018: rare cutoff variance and entropy weights.  See the module docstring. -/
theorem rare_cutoff_variance_and_entropy_weights {d : ℕ} (A : InteractionData d)
    (f : (N : ℕ+) → ParticleH1 A N) (Cs Ss : (N : ℕ+) → Set (ParticleSpace d N))
    (β Δ c Cm : ℝ) (hΔ : 0 < Δ) (hc : 0 < c) (N₀ : ℕ)
    (hCs : ∀ N, MeasurableSet (Cs N)) (hSs : ∀ N, MeasurableSet (Ss N))
    (hf0 : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, 0 ≤ f N x)
    (hf1 : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, f N x ≤ 1)
    (hfC : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, x ∈ Cs N → f N x = 1)
    (hfS : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → ∀ x, x ∉ Ss N → f N x = 0)
    (hCmass : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → c * rareMass β Δ N ≤ (particleLaw A N).real (Cs N))
    (hSmass : ∀ N : ℕ+, N₀ ≤ (N : ℕ) → (particleLaw A N).real (Ss N) ≤ Cm * rareMass β Δ N) :
    (∃ c' : ℝ, 0 < c' ∧ ∃ N₁ : ℕ, N₀ ≤ N₁ ∧ ∀ N : ℕ+, N₁ ≤ (N : ℕ) →
      (c * rareMass β Δ N ≤ ∫ x, f N x ^ 2 ∂particleLaw A N ∧
        ∫ x, f N x ^ 2 ∂particleLaw A N ≤ Cm * rareMass β Δ N) ∧
      (∫ x, f N x ^ 2 ∂particleLaw A N) / 2 ≤
        ProbabilityTheory.variance (f N).1 (particleLaw A N) ∧
      ENNReal.ofReal (c' * (N : ℕ) * ∫ x, f N x ^ 2 ∂particleLaw A N) ≤
        particleEntropy A N (f N)) ∧
    ∀ α C' : ℝ, 0 < C' →
      (∀ N : ℕ+, N₀ ≤ (N : ℕ) →
        particleEnergy A N (f N) ≤ C' * ((N : ℕ) : ℝ) ^ (-α) * ∫ x, f N x ^ 2 ∂particleLaw A N) →
      ∃ C'' : ℝ, 0 < C'' ∧ ∃ N₂ : ℕ, ∀ N : ℕ+, N₂ ≤ (N : ℕ) →
        (particlePoincareRate A N ≤ ENNReal.ofReal (C'' * ((N : ℕ) : ℝ) ^ (-α)) ∧
          (particlePoincareRate A N).toReal ≤ C'' * ((N : ℕ) : ℝ) ^ (-α)) ∧
        ((∀ N : ℕ+, N₀ ≤ (N : ℕ) → IsSymmetricParticleTest (f N)) →
          particleRateSym A N ≤ ENNReal.ofReal (C'' * ((N : ℕ) : ℝ) ^ (-(α + 1))) ∧
            (particleRateSym A N).toReal ≤ C'' * ((N : ℕ) : ℝ) ^ (-(α + 1))) := by
  obtain ⟨N₁, hN₁0, hsc⟩ := rare_cutoff_scales A f Cs Ss β Δ c Cm hΔ hc N₀ hCs hSs hf0 hf1 hfC hfS
    hCmass hSmass
  refine ⟨⟨Δ / 2, by positivity, N₁, hN₁0, hsc⟩, fun α C' hC' hE => ?_⟩
  obtain ⟨C'', hC''⟩ : ∃ C'' : ℝ, C'' = 2 * C' + 4 * C' / Δ := ⟨_, rfl⟩
  have hC''pos : 0 < C'' := by rw [hC'']; positivity
  refine ⟨C'', hC''pos, N₁, fun N hN => ?_⟩
  have hN0 : N₀ ≤ (N : ℕ) := hN₁0.trans hN
  obtain ⟨⟨hnlo, hnhi⟩, hvar, hent⟩ := hsc N hN
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hmpos := rareMass_pos β Δ (N.pos : 1 ≤ (N : ℕ))
  set n := ∫ x, f N x ^ 2 ∂particleLaw A N with hn
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity) hnlo
  have hpα : 0 < ((N : ℕ) : ℝ) ^ (-α) := Real.rpow_pos_of_pos hNpos _
  have hpα1 : ((N : ℕ) : ℝ) ^ (-(α + 1)) = ((N : ℕ) : ℝ) ^ (-α) / ((N : ℕ) : ℝ) := by
    rw [neg_add, Real.rpow_add hNpos, Real.rpow_neg_one, div_eq_mul_inv]
  have hE0 := particleEnergy_nonneg (f N)
  have hEN := hE N hN0
  have hCpp : 2 * C' ≤ C'' := by
    have : 0 ≤ 4 * C' / Δ := by positivity
    linarith
  have hCps : 4 * C' / Δ ≤ C'' := by
    have : 0 ≤ 2 * C' := by positivity
    linarith
  have hvpos : 0 < ProbabilityTheory.variance (f N).1 (particleLaw A N) :=
    lt_of_lt_of_le (by positivity) hvar
  have hP : particlePoincareRate A N ≤ ENNReal.ofReal (C'' * ((N : ℕ) : ℝ) ^ (-α)) := by
    refine (particlePoincareRate_le_quotient A N (f N) hvpos).trans ?_
    unfold particlePoincareQuotient
    rw [← ENNReal.ofReal_div_of_pos hvpos]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ hvpos]
    have h1 : 2 * C' * ((N : ℕ) : ℝ) ^ (-α) ≤ C'' * ((N : ℕ) : ℝ) ^ (-α) :=
      mul_le_mul_of_nonneg_right hCpp hpα.le
    have h2 : C' * ((N : ℕ) : ℝ) ^ (-α) * (n / 2) ≤
        C' * ((N : ℕ) : ℝ) ^ (-α) * ProbabilityTheory.variance (f N).1 (particleLaw A N) :=
      mul_le_mul_of_nonneg_left hvar (by positivity)
    have h3 : C'' * ((N : ℕ) : ℝ) ^ (-α) * ProbabilityTheory.variance (f N).1 (particleLaw A N) ≥
        2 * C' * ((N : ℕ) : ℝ) ^ (-α) * ProbabilityTheory.variance (f N).1 (particleLaw A N) :=
      mul_le_mul_of_nonneg_right h1 hvpos.le
    nlinarith
  refine ⟨⟨hP, ENNReal.toReal_le_of_le_ofReal (mul_pos hC''pos hpα).le hP⟩, fun hsym => ?_⟩
  have hentpos : 0 < particleEntropy A N (f N) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.2 (by positivity)) hent
  have hS : particleRateSym A N ≤ ENNReal.ofReal (C'' * ((N : ℕ) : ℝ) ^ (-(α + 1))) := by
    refine (particleRateSym_le_quotient A N (f N) (hsym N hN0) hentpos).trans ?_
    unfold particleQuotient
    refine (ENNReal.div_le_div_left hent _).trans ?_
    rw [← ENNReal.ofReal_div_of_pos (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_iff₀ (by positivity), hpα1]
    have hq : C'' * (((N : ℕ) : ℝ) ^ (-α) / ((N : ℕ) : ℝ)) ≥
        4 * C' / Δ * (((N : ℕ) : ℝ) ^ (-α) / ((N : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hCps (by positivity)
    have hq2 : 4 * C' / Δ * (((N : ℕ) : ℝ) ^ (-α) / ((N : ℕ) : ℝ)) *
        (Δ / 2 * ((N : ℕ) : ℝ) * n) = 2 * (C' * ((N : ℕ) : ℝ) ^ (-α) * n) := by
      field_simp; ring
    have hq3 : 4 * C' / Δ * (((N : ℕ) : ℝ) ^ (-α) / ((N : ℕ) : ℝ)) *
        (Δ / 2 * ((N : ℕ) : ℝ) * n) ≤ C'' * (((N : ℕ) : ℝ) ^ (-α) / ((N : ℕ) : ℝ)) *
        (Δ / 2 * ((N : ℕ) : ℝ) * n) :=
      mul_le_mul_of_nonneg_right hq (by positivity)
    nlinarith
  exact ⟨hS, ENNReal.toReal_le_of_le_ofReal (mul_pos hC''pos (Real.rpow_pos_of_pos hNpos _)).le hS⟩

end DGPS.FiniteN
