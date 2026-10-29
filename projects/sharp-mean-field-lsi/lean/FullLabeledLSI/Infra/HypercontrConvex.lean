import FullLabeledLSI.Infra.HypercontrGrossStep

/-!
# Gross's lemma: convex dissipation

For the abstract heat flow `u_t = ∑_k e^{-tν_k} c_k M_k` of `GrossHyp`, and a `C²` function `Γ`
with `Γ'' ≥ 0` and polynomial growth of `Γ, Γ', Γ''`, the functional `Θ(t) = ∫ Γ(u_t) dP` is
differentiable on `ℝ` with
`Θ'(t) = -∫ Γ''(u_t) G_{c(t)} dP ≤ 0`
(differentiation under the integral sign, then the integration by parts hypothesis `ibp` with the
test function `ψ = Γ'`). Hence `Θ` is non-increasing on `[0, ∞)`.
-/

noncomputable section

namespace SharpLSI.FL.Gross

open MeasureTheory Real Filter Topology

section Comp

variable {Ω ι : Type*} {S : Ω → ℝ} {F : ι → Ω → ℝ}

/-- Composition of a polynomially dominated family with a function of polynomial growth is
polynomially dominated. -/
lemma PolyDom.comp_poly (hS : ∀ ω, 0 ≤ S ω) (hF : PolyDom S F) {g : ℝ → ℝ} {C : ℝ} {m : ℕ}
    (hg : ∀ s, |g s| ≤ C * (1 + |s|) ^ m) : PolyDom S (fun i ω => g (F i ω)) := by
  have h1 : PolyDom S (fun i ω => (1 + |F i ω|) ^ m) :=
    ((PolyDom.const (S := S) (ι := ι) (1 : ℝ)).add hS hF.abs).pow hS m
  have h2 : PolyDom S (fun i ω => C * (1 + |F i ω|) ^ m) :=
    (PolyDom.const (S := S) (ι := ι) C).mul hS h1
  exact h2.mono fun i ω => (hg (F i ω)).trans (le_abs_self _)

end Comp

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {K : Type*} [Fintype K]
  {P : Measure Ω} [IsProbabilityMeasure P] {M : K → Ω → ℝ}

/-- Differentiation of `Θ(t) = ∫ Γ(u_t) dP` under the integral sign, for `C¹` functions `Γ` such
that `Γ` and `Γ'` have polynomial growth. -/
theorem hasDerivAt_Theta (hM : ∀ k (n : ℕ), MemLp (M k) n P) (ν c : K → ℝ) {Γ : ℝ → ℝ}
    (hΓ : ContDiff ℝ 1 Γ)
    (hgrow : ∃ C : ℝ, ∃ m : ℕ, ∀ s, |Γ s| + |deriv Γ s| ≤ C * (1 + |s|) ^ m) (t : ℝ) :
    Integrable (fun ω => deriv Γ (uT M ν c t ω) * (-(vT M ν c t ω))) P ∧
      HasDerivAt (fun s => ∫ ω, Γ (uT M ν c s ω) ∂P)
        (∫ ω, deriv Γ (uT M ν c t ω) * (-(vT M ν c t ω)) ∂P) t := by
  have hS := Sbase_nonneg M
  have hSm := memLp_Sbase M hM
  have hMe : ∀ k, AEMeasurable (M k) P := aem_of_memLp hM
  obtain ⟨C0, m, hg⟩ := hgrow
  have hg0 : ∀ s, |Γ s| ≤ C0 * (1 + |s|) ^ m := fun s => by
    linarith [hg s, abs_nonneg (deriv Γ s)]
  have hg1 : ∀ s, |deriv Γ s| ≤ C0 * (1 + |s|) ^ m := fun s => by
    linarith [hg s, abs_nonneg (Γ s)]
  have hΓc : Continuous Γ := hΓ.continuous
  have hΓ'c : Continuous (deriv Γ) := hΓ.continuous_deriv le_rfl
  have hΓd : Differentiable ℝ Γ := hΓ.differentiable one_ne_zero
  set T : ℝ := |t| + 1 with hT
  have htT : |t| ≤ T := by rw [hT]; linarith
  have hD : PolyDom (Sbase M)
      (fun (i : Ix T) ω => deriv Γ (uT M ν c i.1 ω) * (-(vT M ν c i.1 ω))) :=
    ((polyDom_uT M ν c T).comp_poly hS hg1).mul hS (polyDom_vT M ν c T).neg
  have hF : PolyDom (Sbase M) (fun (i : Ix T) ω => Γ (uT M ν c i.1 ω)) :=
    (polyDom_uT M ν c T).comp_poly hS hg0
  obtain ⟨C, _hC, N, hb⟩ := hD
  have hFmeas : ∀ s, AEStronglyMeasurable (fun ω => Γ (uT M ν c s ω)) P := fun s =>
    (hΓc.measurable.comp_aemeasurable (aem_uT M ν c hMe s)).aestronglyMeasurable
  have hFint : Integrable (fun ω => Γ (uT M ν c t ω)) P :=
    hF.integrable hS hSm ⟨t, htT⟩ (hFmeas t)
  have hD'meas : AEStronglyMeasurable
      (fun ω => deriv Γ (uT M ν c t ω) * (-(vT M ν c t ω))) P :=
    ((hΓ'c.measurable.comp_aemeasurable (aem_uT M ν c hMe t)).mul
      (aem_vT M ν c hMe t).neg).aestronglyMeasurable
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.Ioo (t - 1) (t + 1))
    (F := fun s ω => Γ (uT M ν c s ω))
    (F' := fun s ω => deriv Γ (uT M ν c s ω) * (-(vT M ν c s ω)))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall hFmeas) hFint hD'meas ?_
    ((integrable_one_add_pow hS hSm N).const_mul C)
    (Filter.Eventually.of_forall fun ω s _ => ?_)
  · refine Filter.Eventually.of_forall fun ω s hs => ?_
    have hsT : |s| ≤ T :=
      abs_le.mpr ⟨by linarith [hs.1, neg_abs_le t], by linarith [hs.2, le_abs_self t]⟩
    simpa [Real.norm_eq_abs] using hb ⟨s, hsT⟩ ω
  · exact hΓd.differentiableAt.hasDerivAt.comp s (hasDerivAt_uT M ν c ω s)

variable {ν : K → ℝ} {G : (K → ℝ) → Ω → ℝ} {a : ℝ}

/-- The derivative of the dissipation functional `Θ(t) = ∫ Γ(u_t) dP`:
`Θ'(t) = -∫ Γ''(u_t) G_{c(t)} dP`. -/
theorem hasDerivAt_dissipation (h : GrossHyp P M ν G a) (c : K → ℝ) {Γ : ℝ → ℝ}
    (hΓ : ContDiff ℝ 2 Γ)
    (hgrow : ∃ C : ℝ, ∃ m : ℕ,
      ∀ s, |Γ s| + |deriv Γ s| + |deriv (deriv Γ) s| ≤ C * (1 + |s|) ^ m) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, Γ (uFun M (flow ν s c) ω) ∂P)
      (-∫ ω, deriv (deriv Γ) (uFun M (flow ν t c) ω) * G (flow ν t c) ω ∂P) t := by
  have hΓ1 : ContDiff ℝ 1 Γ := hΓ.of_le (by norm_num)
  have hΓ' : ContDiff ℝ 1 (deriv Γ) := by
    have h2 : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) Γ := by
      rw [one_add_one_eq_two]; exact hΓ
    exact ((contDiff_succ_iff_deriv (n := 1)).mp h2).2.2
  obtain ⟨C, m, hg⟩ := hgrow
  have hg01 : ∃ C : ℝ, ∃ m : ℕ, ∀ s, |Γ s| + |deriv Γ s| ≤ C * (1 + |s|) ^ m :=
    ⟨C, m, fun s => by linarith [hg s, abs_nonneg (deriv (deriv Γ) s)]⟩
  have hg12 : ∃ C : ℝ, ∃ m : ℕ,
      ∀ s, |deriv Γ s| + |deriv (deriv Γ) s| ≤ C * (1 + |s|) ^ m :=
    ⟨C, m, fun s => by linarith [hg s, abs_nonneg (Γ s)]⟩
  have key := (hasDerivAt_Theta h.memLp ν c hΓ1 hg01 t).2
  have hibp := h.ibp (flow ν t c) (deriv Γ) hΓ' hg12
  have e : ∫ ω, deriv Γ (uT M ν c t ω) * (-(vT M ν c t ω)) ∂P =
      -∫ ω, deriv (deriv Γ) (uFun M (flow ν t c) ω) * G (flow ν t c) ω ∂P := by
    rw [← hibp, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show deriv Γ (uT M ν c t ω) * (-(vT M ν c t ω)) =
      -(deriv Γ (uT M ν c t ω) * vT M ν c t ω)
    ring
  rw [e] at key
  exact key

/-- **Convex dissipation.** If `Γ` is `C²` with `Γ'' ≥ 0` and polynomial growth of `Γ, Γ', Γ''`,
then `t ↦ ∫ Γ(u_t) dP` is non-increasing on `[0, ∞)`. -/
theorem convex_dissipation (h : GrossHyp P M ν G a) (c : K → ℝ) {Γ : ℝ → ℝ}
    (hΓ : ContDiff ℝ 2 Γ) (hnn : ∀ s, 0 ≤ deriv (deriv Γ) s)
    (hgrow : ∃ C : ℝ, ∃ m : ℕ,
      ∀ s, |Γ s| + |deriv Γ s| + |deriv (deriv Γ) s| ≤ C * (1 + |s|) ^ m) :
    AntitoneOn (fun t => ∫ ω, Γ (uFun M (flow ν t c) ω) ∂P) (Set.Ici 0) := by
  have hd := hasDerivAt_dissipation h c hΓ hgrow
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · exact fun t _ => (hd t).continuousAt.continuousWithinAt
  · intro t _
    exact (hd t).differentiableAt.differentiableWithinAt
  · intro t _
    rw [(hd t).deriv]
    have : 0 ≤ ∫ ω, deriv (deriv Γ) (uFun M (flow ν t c) ω) * G (flow ν t c) ω ∂P :=
      integral_nonneg fun ω => mul_nonneg (hnn _) (h.G_nonneg _ ω)
    linarith

/-- A `C²` convex function has non-negative second derivative. -/
lemma deriv_deriv_nonneg_of_convexOn {Γ : ℝ → ℝ} (hΓ : ContDiff ℝ 2 Γ)
    (hconv : ConvexOn ℝ Set.univ Γ) : ∀ s, 0 ≤ deriv (deriv Γ) s := by
  have hd : Differentiable ℝ Γ := hΓ.differentiable (by norm_num)
  have hmono : Monotone (deriv Γ) :=
    monotoneOn_univ.mp (hconv.monotoneOn_deriv fun x _ => hd x)
  intro s
  exact hmono.deriv_nonneg

/-- Convex dissipation, with convexity of `Γ` stated as `ConvexOn ℝ Set.univ Γ`. -/
theorem convex_dissipation_of_convexOn (h : GrossHyp P M ν G a) (c : K → ℝ) {Γ : ℝ → ℝ}
    (hΓ : ContDiff ℝ 2 Γ) (hconv : ConvexOn ℝ Set.univ Γ)
    (hgrow : ∃ C : ℝ, ∃ m : ℕ,
      ∀ s, |Γ s| + |deriv Γ s| + |deriv (deriv Γ) s| ≤ C * (1 + |s|) ^ m) :
    AntitoneOn (fun t => ∫ ω, Γ (uFun M (flow ν t c) ω) ∂P) (Set.Ici 0) :=
  convex_dissipation h c hΓ (deriv_deriv_nonneg_of_convexOn hΓ hconv) hgrow

end Main

end SharpLSI.FL.Gross

end
