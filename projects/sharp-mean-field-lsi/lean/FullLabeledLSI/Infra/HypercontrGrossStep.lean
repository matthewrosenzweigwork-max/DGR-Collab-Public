import FullLabeledLSI.Infra.HypercontrDeriv
import SharpSymmetricLSI.Infra.EntropyTensor

/-!
# Gross's lemma: the differential inequality `Φ' ≤ (q'/q) Φ log Φ`

Abstract hypotheses (`GrossHyp`): a family `M_k` of functions in every `L^p`, numbers `ν_k`,
non-negative weights `G c ∈ L²` (standing for `|∇u_c|²`), a rate `a > 0`, the integration by parts
identity for `C¹` test functions of polynomial growth, and the logarithmic Sobolev inequality for
`w = (u_c² + ε²)^{r/2}`. Under these, `Φ(t) = ∫ (u_t² + ε²)^{q(t)/2}` satisfies the differential
inequality on `[0, ∞)`.
-/

noncomputable section

namespace SharpLSI.FL.Gross

open MeasureTheory Real Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {K : Type*} [Fintype K]

/-- The abstract hypotheses of Gross's lemma. `u c = ∑ c_k M_k`, `A u_c = ∑ ν_k c_k M_k`,
`G c` stands for `|∇ u_c|²`. -/
structure GrossHyp (P : Measure Ω) (M : K → Ω → ℝ) (ν : K → ℝ) (G : (K → ℝ) → Ω → ℝ)
    (a : ℝ) : Prop where
  ha : 0 < a
  memLp : ∀ k (n : ℕ), MemLp (M k) n P
  G_nonneg : ∀ c ω, 0 ≤ G c ω
  G_memLp : ∀ c, MemLp (G c) 2 P
  /-- Integration by parts: `∫ ψ(u_c) A u_c = ∫ ψ'(u_c) G_c` for `C¹` `ψ` of polynomial growth. -/
  ibp : ∀ (c : K → ℝ) (ψ : ℝ → ℝ), ContDiff ℝ 1 ψ →
    (∃ C : ℝ, ∃ m : ℕ, ∀ s, |ψ s| + |deriv ψ s| ≤ C * (1 + |s|) ^ m) →
    ∫ ω, ψ (uFun M c ω) * Afun M ν c ω ∂P = ∫ ω, deriv ψ (uFun M c ω) * G c ω ∂P
  /-- Logarithmic Sobolev inequality for `w = (u_c² + ε²)^{r/2}`, `r ≥ 1`. -/
  lsi : ∀ (c : K → ℝ) (ε r : ℝ), 0 < ε → 1 ≤ r →
    SharpLSI.entR P (fun ω => (uFun M c ω ^ 2 + ε ^ 2) ^ r) ≤
      2 / a * (r ^ 2 * ∫ ω, uFun M c ω ^ 2 * (uFun M c ω ^ 2 + ε ^ 2) ^ (r - 2) * G c ω ∂P)

lemma PolyDom.restrict {ι : Type*} {S : Ω → ℝ} {F : ι → Ω → ℝ} (h : PolyDom S F) (i : ι) :
    PolyDom S (fun (_ : Unit) => F i) := by
  obtain ⟨C, hC, N, hb⟩ := h
  exact ⟨C, hC, N, fun _ ω => hb i ω⟩

section Psi

/-- The test function `ψ(s) = s (s² + ε²)^p`. -/
def psiF (ε p s : ℝ) : ℝ := s * (s ^ 2 + ε ^ 2) ^ p

lemma hasDerivAt_psiF {ε : ℝ} (hε : 0 < ε) (p s : ℝ) :
    HasDerivAt (psiF ε p) ((s ^ 2 + ε ^ 2) ^ p + 2 * p * s ^ 2 * (s ^ 2 + ε ^ 2) ^ (p - 1)) s := by
  have hb : 0 < s ^ 2 + ε ^ 2 := by positivity
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + ε ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_pow 2 s).add_const (ε ^ 2))
  have h2 := h1.rpow_const (p := p) (Or.inl hb.ne')
  have h3 := (hasDerivAt_id s).mul h2
  refine h3.congr_deriv ?_
  simp only [id]; ring

lemma contDiff_psiF {ε : ℝ} (hε : 0 < ε) (p : ℝ) : ContDiff ℝ 1 (psiF ε p) := by
  unfold psiF
  exact contDiff_id.mul (ContDiff.rpow_const_of_ne ((contDiff_id.pow 2).add contDiff_const)
    (fun s => by positivity))

lemma sq_mul_rpow_le {s ε : ℝ} (hε : 0 < ε) (p : ℝ) :
    s ^ 2 * (s ^ 2 + ε ^ 2) ^ (p - 1) ≤ (s ^ 2 + ε ^ 2) ^ p := by
  have hb : 0 < s ^ 2 + ε ^ 2 := by positivity
  calc s ^ 2 * (s ^ 2 + ε ^ 2) ^ (p - 1) ≤ (s ^ 2 + ε ^ 2) * (s ^ 2 + ε ^ 2) ^ (p - 1) :=
        mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ε]) (Real.rpow_nonneg hb.le _)
    _ = (s ^ 2 + ε ^ 2) ^ p := by
        rw [Real.rpow_sub_one hb.ne']; field_simp

/-- Polynomial growth of `ψ` and `ψ'` (as required by the integration by parts hypothesis). -/
lemma psiF_growth {ε : ℝ} (hε : 0 < ε) {p : ℝ} (hp : 0 ≤ p) :
    ∃ C : ℝ, ∃ m : ℕ, ∀ s, |psiF ε p s| + |deriv (psiF ε p) s| ≤ C * (1 + |s|) ^ m := by
  have hS : ∀ s : ℝ, 0 ≤ |s| := fun s => abs_nonneg s
  have hid : PolyDom (fun s : ℝ => |s|) (fun (_ : Unit) (s : ℝ) => s) :=
    (PolyDom.base hS).mono fun _ s => by simp
  have hB : PolyDom (fun s : ℝ => |s|) (fun (_ : Unit) (s : ℝ) => s ^ 2 + ε ^ 2) :=
    (hid.pow hS 2).add hS (PolyDom.const (ε ^ 2))
  have hBp : PolyDom (fun s : ℝ => |s|) (fun (_ : Unit) (s : ℝ) => (s ^ 2 + ε ^ 2) ^ p) :=
    PolyDom.rpow hS hB (fun _ s => by positivity) (p := fun _ => p) (P := p) (fun _ => hp)
      (fun _ => le_rfl)
  have h1 : PolyDom (fun s : ℝ => |s|) (fun (_ : Unit) (s : ℝ) => psiF ε p s) :=
    (hid.mul hS hBp)
  have h2 : PolyDom (fun s : ℝ => |s|) (fun (_ : Unit) (s : ℝ) => deriv (psiF ε p) s) := by
    have h3 : PolyDom (fun s : ℝ => |s|) (fun (_ : Unit) (s : ℝ) =>
        (s ^ 2 + ε ^ 2) ^ p + 2 * p * s ^ 2 * (s ^ 2 + ε ^ 2) ^ (p - 1)) := by
      refine hBp.add hS ?_
      refine ((PolyDom.const (2 * p)).mul hS hBp).mono fun _ s => ?_
      have := sq_mul_rpow_le (s := s) hε p
      have hb : 0 < s ^ 2 + ε ^ 2 := by positivity
      have hn : 0 ≤ s ^ 2 * (s ^ 2 + ε ^ 2) ^ (p - 1) := by
        have := Real.rpow_nonneg hb.le (p - 1); positivity
      calc |2 * p * s ^ 2 * (s ^ 2 + ε ^ 2) ^ (p - 1)|
          = |2 * p| * (s ^ 2 * (s ^ 2 + ε ^ 2) ^ (p - 1)) := by
            rw [show 2 * p * s ^ 2 * (s ^ 2 + ε ^ 2) ^ (p - 1) =
              2 * p * (s ^ 2 * (s ^ 2 + ε ^ 2) ^ (p - 1)) by ring, abs_mul, abs_of_nonneg hn]
        _ ≤ |2 * p| * (s ^ 2 + ε ^ 2) ^ p := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = |2 * p * (s ^ 2 + ε ^ 2) ^ p| := by
            rw [abs_mul (2 * p) ((s ^ 2 + ε ^ 2) ^ p), abs_of_nonneg (Real.rpow_nonneg hb.le _)]
    refine h3.mono fun _ s => ?_
    rw [(hasDerivAt_psiF hε p s).deriv]
  obtain ⟨C, hC, N, hb⟩ := h1.abs.add hS h2.abs
  refine ⟨C, N, fun s => ?_⟩
  have := hb () s
  rwa [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at this

end Psi

section Fixed

variable {P : Measure Ω} [IsProbabilityMeasure P] {M : K → Ω → ℝ} {ν : K → ℝ}
  {G : (K → ℝ) → Ω → ℝ} {a : ℝ}

variable (M ν) (c : K → ℝ) (a ε : ℝ)

lemma polyDom1_B (t : ℝ) : PolyDom (Sbase M) (fun (_ : Unit) ω => Bt M ν c ε t ω) :=
  (polyDom_B M ν c ε |t|).restrict ⟨t, le_rfl⟩

lemma polyDom1_Bpow (hε : 0 < ε) (t p : ℝ) (hp : 0 ≤ p) :
    PolyDom (Sbase M) (fun (_ : Unit) ω => Bt M ν c ε t ω ^ p) :=
  PolyDom.rpow (Sbase_nonneg M) (polyDom1_B M ν c ε t) (fun _ ω => (Bt_pos M ν c hε t ω).le)
    (p := fun _ => p) (P := p) (fun _ => hp) (fun _ => le_rfl)

lemma polyDom1_Ft (ha : 0 < a) (hε : 0 < ε) (t : ℝ) :
    PolyDom (Sbase M) (fun (_ : Unit) ω => Ft M ν c a ε t ω) :=
  (polyDom_Ft M ν c a ε ha hε |t|).restrict ⟨t, le_rfl⟩

variable {M ν c a ε}

lemma aem_of_memLp (hM : ∀ k (n : ℕ), MemLp (M k) n P) : ∀ k, AEMeasurable (M k) P :=
  fun k => (hM k 1).aestronglyMeasurable.aemeasurable

lemma integrable_Ft (hM : ∀ k (n : ℕ), MemLp (M k) n P) (ha : 0 < a) (hε : 0 < ε) (t : ℝ) :
    Integrable (Ft M ν c a ε t) P :=
  (polyDom1_Ft M ν c a ε ha hε t).integrable (Sbase_nonneg M) (memLp_Sbase M hM) ()
    (aem_Ft M ν c a ε (aem_of_memLp hM) t).aestronglyMeasurable

lemma integrable_f1 (hM : ∀ k (n : ℕ), MemLp (M k) n P) (ha : 0 < a) (hε : 0 < ε) {t : ℝ}
    (ht : 0 ≤ t) :
    Integrable (fun ω => uT M ν c t ω * vT M ν c t ω * Bt M ν c ε t ω ^ (qexp a t / 2 - 1)) P := by
  have hS := Sbase_nonneg M
  have hp : 0 ≤ qexp a t / 2 - 1 := by linarith [two_le_qexp ha.le ht]
  have hu : PolyDom (Sbase M) (fun (_ : Unit) ω => uT M ν c t ω) :=
    (polyDom_uT M ν c |t|).restrict ⟨t, le_rfl⟩
  have hv : PolyDom (Sbase M) (fun (_ : Unit) ω => vT M ν c t ω) :=
    (polyDom_vT M ν c |t|).restrict ⟨t, le_rfl⟩
  have hd := (hu.mul hS hv).mul hS (polyDom1_Bpow M ν c ε hε t _ hp)
  have hMe := aem_of_memLp hM
  exact hd.integrable hS (memLp_Sbase M hM) ()
    ((((aem_uT M ν c hMe t).mul (aem_vT M ν c hMe t)).mul
      ((aem_Bt M ν c ε hMe t).pow_const _)).aestronglyMeasurable)

lemma integrable_f2 (hM : ∀ k (n : ℕ), MemLp (M k) n P) (ha : 0 < a) (hε : 0 < ε) (t : ℝ) :
    Integrable (fun ω => Ft M ν c a ε t ω * Real.log (Bt M ν c ε t ω)) P := by
  have hS := Sbase_nonneg M
  have hd : PolyDom (Sbase M) (fun (_ : Unit) ω =>
      Ft M ν c a ε t ω * (|Real.log (ε ^ 2)| + Bt M ν c ε t ω)) :=
    (polyDom1_Ft M ν c a ε ha hε t).mul hS
      ((PolyDom.const (|Real.log (ε ^ 2)|)).add hS (polyDom1_B M ν c ε t))
  have hd' : PolyDom (Sbase M) (fun (_ : Unit) ω =>
      Ft M ν c a ε t ω * Real.log (Bt M ν c ε t ω)) := by
    refine hd.mono fun _ ω => ?_
    have hBi := Bt_pos M ν c hε t ω
    have hF0 : 0 ≤ Ft M ν c a ε t ω := Real.rpow_nonneg hBi.le _
    have hlogB := abs_log_le hε (show ε ^ 2 ≤ Bt M ν c ε t ω by
      unfold Bt; nlinarith [sq_nonneg (uT M ν c t ω)])
    have hnn : 0 ≤ Ft M ν c a ε t ω * (|Real.log (ε ^ 2)| + Bt M ν c ε t ω) := by positivity
    rw [abs_of_nonneg hnn, abs_mul, abs_of_nonneg hF0]
    exact mul_le_mul_of_nonneg_left hlogB hF0
  have hMe := aem_of_memLp hM
  exact hd'.integrable hS (memLp_Sbase M hM) ()
    (((aem_Ft M ν c a ε hMe t).mul (aem_Bt M ν c ε hMe t).log).aestronglyMeasurable)

lemma integrable_BpG (hM : ∀ k (n : ℕ), MemLp (M k) n P) (hε : 0 < ε) (t p : ℝ) (hp : 0 ≤ p)
    {g : Ω → ℝ} (hg : MemLp g 2 P) :
    Integrable (fun ω => Bt M ν c ε t ω ^ p * g ω) P :=
  (polyDom1_Bpow M ν c ε hε t p hp).integrable_mul (Sbase_nonneg M) (memLp_Sbase M hM) hg ()
    (((aem_Bt M ν c ε (aem_of_memLp hM) t).pow_const _).aestronglyMeasurable)

lemma integrable_uBG (hM : ∀ k (n : ℕ), MemLp (M k) n P) (hε : 0 < ε) (t p : ℝ) (hp : 0 ≤ p)
    {g : Ω → ℝ} (hg : MemLp g 2 P) :
    Integrable (fun ω => uT M ν c t ω ^ 2 * Bt M ν c ε t ω ^ (p - 1) * g ω) P := by
  have hd : PolyDom (Sbase M) (fun (_ : Unit) ω => uT M ν c t ω ^ 2 * Bt M ν c ε t ω ^ (p - 1)) := by
    refine (polyDom1_Bpow M ν c ε hε t p hp).mono fun _ ω => ?_
    have hBi := Bt_pos M ν c hε t ω
    have hle := sq_mul_rpow_le (s := uT M ν c t ω) hε p
    have hn : 0 ≤ uT M ν c t ω ^ 2 * Bt M ν c ε t ω ^ (p - 1) := by
      have := Real.rpow_nonneg hBi.le (p - 1); positivity
    rw [abs_of_nonneg hn, abs_of_nonneg (Real.rpow_nonneg hBi.le _)]
    exact hle
  have hMe := aem_of_memLp hM
  exact hd.integrable_mul (Sbase_nonneg M) (memLp_Sbase M hM) hg ()
    ((((aem_uT M ν c hMe t).pow_const 2).mul
      ((aem_Bt M ν c ε hMe t).pow_const _)).aestronglyMeasurable)

end Fixed

section Ineq

variable {P : Measure Ω} [IsProbabilityMeasure P] {M : K → Ω → ℝ} {ν : K → ℝ}
  {G : (K → ℝ) → Ω → ℝ} {a : ℝ} {c : K → ℝ} {ε : ℝ}

/-- The differential inequality `Φ' ≤ (q'/q) Φ log Φ`, at the integrated level. -/
theorem Dt_integral_le (h : GrossHyp P M ν G a) (hε : 0 < ε) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, Dt M ν c a ε t ω ∂P ≤
      2 * a * (qexp a t - 1) / qexp a t *
        ((∫ ω, Ft M ν c a ε t ω ∂P) * Real.log (∫ ω, Ft M ν c a ε t ω ∂P)) := by
  have ha := h.ha
  have hM := h.memLp
  have hG := h.G_memLp (flow ν t c)
  have hG0 := h.G_nonneg (flow ν t c)
  have hq2 : 2 ≤ qexp a t := two_le_qexp ha.le ht
  have hq0 : 0 < qexp a t := by linarith
  have hq1 : 0 ≤ qexp a t - 1 := by linarith
  have hp0 : 0 ≤ qexp a t / 2 - 1 := by linarith
  have e1 : qexp a t / 2 - 1 - 1 = qexp a t / 2 - 2 := by ring
  set I : ℝ := ∫ ω, uT M ν c t ω * vT M ν c t ω * Bt M ν c ε t ω ^ (qexp a t / 2 - 1) ∂P with hI
  set J : ℝ := ∫ ω, uT M ν c t ω ^ 2 * Bt M ν c ε t ω ^ (qexp a t / 2 - 2) *
    G (flow ν t c) ω ∂P with hJ
  set L : ℝ := ∫ ω, Ft M ν c a ε t ω * Real.log (Bt M ν c ε t ω) ∂P with hL
  set Φ : ℝ := ∫ ω, Ft M ν c a ε t ω ∂P with hΦ
  -- (1) the integral of `Dt`
  have hD : ∫ ω, Dt M ν c a ε t ω ∂P = -(qexp a t) * I + a * (qexp a t - 1) * L := by
    have e : ∀ ω, Dt M ν c a ε t ω =
        -(qexp a t) * (uT M ν c t ω * vT M ν c t ω * Bt M ν c ε t ω ^ (qexp a t / 2 - 1)) +
        a * (qexp a t - 1) * (Ft M ν c a ε t ω * Real.log (Bt M ν c ε t ω)) := by
      intro ω; unfold Dt Ft; ring
    simp_rw [e]
    rw [integral_add ((integrable_f1 hM ha hε ht).const_mul _)
      ((integrable_f2 hM ha hε t).const_mul _), integral_const_mul, integral_const_mul]
  -- (2) integration by parts with `ψ(s) = s (s² + ε²)^p`
  have hibp := h.ibp (flow ν t c) (psiF ε (qexp a t / 2 - 1)) (contDiff_psiF hε _)
    (psiF_growth hε hp0)
  have hder : ∀ s, deriv (psiF ε (qexp a t / 2 - 1)) s =
      (s ^ 2 + ε ^ 2) ^ (qexp a t / 2 - 1) +
        (qexp a t - 2) * (s ^ 2 * (s ^ 2 + ε ^ 2) ^ (qexp a t / 2 - 2)) := by
    intro s
    rw [(hasDerivAt_psiF hε _ s).deriv, e1]
    have e2 : 2 * (qexp a t / 2 - 1) = qexp a t - 2 := by ring
    rw [e2]; ring
  have hLHS : ∫ ω, psiF ε (qexp a t / 2 - 1) (uFun M (flow ν t c) ω) *
      Afun M ν (flow ν t c) ω ∂P = I := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show psiF ε (qexp a t / 2 - 1) (uT M ν c t ω) * vT M ν c t ω = _
    simp only [psiF, Bt]; ring
  have hJint : Integrable (fun ω => uT M ν c t ω ^ 2 * Bt M ν c ε t ω ^ (qexp a t / 2 - 2) *
      G (flow ν t c) ω) P := by
    have := integrable_uBG (M := M) (ν := ν) (c := c) hM hε t (qexp a t / 2 - 1) hp0 hG
    rwa [e1] at this
  have hBint := integrable_BpG (M := M) (ν := ν) (c := c) hM hε t (qexp a t / 2 - 1) hp0 hG
  have hgfun : (fun ω => deriv (psiF ε (qexp a t / 2 - 1)) (uFun M (flow ν t c) ω) *
      G (flow ν t c) ω) = fun ω =>
      Bt M ν c ε t ω ^ (qexp a t / 2 - 1) * G (flow ν t c) ω +
        (qexp a t - 2) * (uT M ν c t ω ^ 2 * Bt M ν c ε t ω ^ (qexp a t / 2 - 2) *
          G (flow ν t c) ω) := by
    funext ω
    rw [hder]
    show ((uT M ν c t ω ^ 2 + ε ^ 2) ^ (qexp a t / 2 - 1) + (qexp a t - 2) *
      (uT M ν c t ω ^ 2 * (uT M ν c t ω ^ 2 + ε ^ 2) ^ (qexp a t / 2 - 2))) *
        G (flow ν t c) ω = _
    simp only [Bt]; ring
  have hIJ : (qexp a t - 1) * J ≤ I := by
    rw [← hLHS, hibp, hgfun]
    calc (qexp a t - 1) * J = ∫ ω, (qexp a t - 1) * (uT M ν c t ω ^ 2 *
          Bt M ν c ε t ω ^ (qexp a t / 2 - 2) * G (flow ν t c) ω) ∂P := by
          rw [integral_const_mul]
      _ ≤ _ := by
          refine integral_mono (hJint.const_mul _) (hBint.add (hJint.const_mul _)) fun ω => ?_
          have hle := sq_mul_rpow_le (s := uT M ν c t ω) hε (qexp a t / 2 - 1)
          rw [e1] at hle
          have hX : uT M ν c t ω ^ 2 * Bt M ν c ε t ω ^ (qexp a t / 2 - 2) * G (flow ν t c) ω ≤
              Bt M ν c ε t ω ^ (qexp a t / 2 - 1) * G (flow ν t c) ω :=
            mul_le_mul_of_nonneg_right hle (hG0 ω)
          show (qexp a t - 1) * (uT M ν c t ω ^ 2 * Bt M ν c ε t ω ^ (qexp a t / 2 - 2) *
              G (flow ν t c) ω) ≤ _
          nlinarith [hX]
  -- (3) the logarithmic Sobolev inequality
  have hLSI : SharpLSI.entR P (Ft M ν c a ε t) ≤ 2 / a * ((qexp a t / 2) ^ 2 * J) :=
    h.lsi (flow ν t c) ε (qexp a t / 2) hε (by linarith)
  have hE : SharpLSI.entR P (Ft M ν c a ε t) = (qexp a t / 2) * L - Φ * Real.log Φ := by
    unfold SharpLSI.entR
    have e : ∀ ω, Ft M ν c a ε t ω * Real.log (Ft M ν c a ε t ω) =
        (qexp a t / 2) * (Ft M ν c a ε t ω * Real.log (Bt M ν c ε t ω)) := by
      intro ω
      unfold Ft
      rw [Real.log_rpow (Bt_pos M ν c hε t ω)]; ring
    simp_rw [e]
    rw [integral_const_mul]
  rw [hE] at hLSI
  have hE' : a * ((qexp a t / 2) * L - Φ * Real.log Φ) ≤ 2 * ((qexp a t / 2) ^ 2 * J) := by
    have := mul_le_mul_of_nonneg_left hLSI ha.le
    calc _ ≤ a * (2 / a * ((qexp a t / 2) ^ 2 * J)) := this
      _ = _ := by field_simp
  rw [hD, div_mul_eq_mul_div, le_div_iff₀ hq0]
  nlinarith [mul_le_mul_of_nonneg_left hE' hq1,
    mul_le_mul_of_nonneg_left hIJ (sq_nonneg (qexp a t))]

end Ineq

end SharpLSI.FL.Gross

end
