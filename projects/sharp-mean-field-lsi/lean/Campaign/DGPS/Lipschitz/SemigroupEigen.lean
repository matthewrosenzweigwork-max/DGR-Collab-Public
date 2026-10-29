import DGPS.Lipschitz.WeightedSpectrum
open MeasureTheory Filter Topology Set
open scoped InnerProductSpace LinearPMap NNReal

namespace DGPS.Lipschitz.SemigroupEigen

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Transport of a `LinearPMap` value along an equality of operators. -/
theorem pmap_apply_congr (A B : H →ₗ.[ℝ] H) (h : A = B) (x : H) (hA : x ∈ A.domain)
    (hB : x ∈ B.domain) : A ⟨x, hA⟩ = B ⟨x, hB⟩ := by
  subst h
  rfl

/-- The right derivative of `s ↦ S s e` at `x ≥ 0` for an eigenvector `e` of the generator. -/
theorem hasDerivWithinAt_orbit (Lg : H →ₗ.[ℝ] H) (S : ℝ≥0 → H →L[ℝ] H)
    (hadd : ∀ (s t : ℝ≥0) f, S (s + t) f = S s (S t f))
    (hder : ∀ f : Lg.domain, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S t (f : H) - f))
      (𝓝[≠] (0 : ℝ≥0)) (𝓝 (Lg f)))
    (e : H) (he : e ∈ Lg.domain) (lam : ℝ) (hLe : Lg ⟨e, he⟩ = (-lam) • e)
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (fun s : ℝ => S s.toNNReal e) ((-lam) • S x.toNNReal e) (Ici x) x := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ici_sdiff_left]
  have h1 := hder ⟨e, he⟩
  have hmap : Tendsto (fun s : ℝ => (s - x).toNNReal) (𝓝[>] x) (𝓝[≠] (0 : ℝ≥0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous fun s : ℝ => (s - x).toNNReal := by fun_prop
      have := (hc.tendsto x).mono_left (nhdsWithin_le_nhds (s := Ioi x))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have : 0 < s - x := sub_pos.mpr hs
      simpa using this
  have h2 := (h1.comp hmap)
  have h3 := ((S x.toNNReal).continuous.tendsto _).comp h2
  rw [hLe, map_smul] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : 0 ≤ s - x := (sub_pos.mpr hs).le
  have hsum : s.toNNReal = x.toNNReal + (s - x).toNNReal := by
    rw [← Real.toNNReal_add hx hs']; congr 1; ring
  simp only [Function.comp, slope_def_module, hsum, hadd, Real.coe_toNNReal _ hs', map_smul,
    map_sub]

/-- (b), abstract form: an eigenvector of the generator is an eigenvector of the semigroup. -/
theorem semigroup_apply_eigen (Lg : H →ₗ.[ℝ] H) (S : ℝ≥0 → H →L[ℝ] H)
    (hS0 : ∀ f, S 0 f = f)
    (hadd : ∀ (s t : ℝ≥0) f, S (s + t) f = S s (S t f))
    (hcont : ∀ f, Continuous fun t : ℝ≥0 => S t f)
    (hder : ∀ f : Lg.domain, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S t (f : H) - f))
      (𝓝[≠] (0 : ℝ≥0)) (𝓝 (Lg f)))
    (e : H) (he : e ∈ Lg.domain) (lam : ℝ) (hLe : Lg ⟨e, he⟩ = (-lam) • e) (t : ℝ≥0) :
    S t e = Real.exp (-lam * t) • e := by
  set g : ℝ → H := fun s => Real.exp (lam * s) • S s.toNNReal e with hg
  have hcg : ContinuousOn g (Icc 0 (t : ℝ)) := by
    have : Continuous g := by
      have h1 : Continuous fun s : ℝ => S s.toNNReal e :=
        (hcont e).comp continuous_real_toNNReal
      exact (by fun_prop : Continuous fun s : ℝ => Real.exp (lam * s)).smul h1
    exact this.continuousOn
  have hdg : ∀ x ∈ Ico 0 (t : ℝ), HasDerivWithinAt g 0 (Ici x) x := by
    intro x hx
    have h1 := hasDerivWithinAt_orbit Lg S hadd hder e he lam hLe hx.1
    have h2 : HasDerivWithinAt (fun s : ℝ => Real.exp (lam * s)) (lam * Real.exp (lam * x))
        (Ici x) x := by
      have := ((hasDerivAt_id x).const_mul lam).exp
      simpa [mul_comm] using this.hasDerivWithinAt
    have h3 := h2.smul h1
    convert h3 using 1
    rw [smul_smul, ← add_smul]
    simp [mul_comm]
  have := constant_of_has_deriv_right_zero hcg hdg t ⟨t.2, le_rfl⟩
  have h0 : g 0 = e := by simp [hg, hS0]
  rw [h0] at this
  simp only [hg, Real.toNNReal_coe] at this
  have h4 := congrArg (fun v => Real.exp (-lam * t) • v) this
  simp only [smul_smul, ← Real.exp_add] at h4
  simpa using h4

end Abstract

section Concrete

open DGPS DGPS.Analysis DGPS.Analysis.CompactResolvent

variable {d : ℕ} {w : Torus d → ℝ}

/-- LIP007d1.  Let `(Lg, S)` be the generator and semigroup of the weighted form on `L²(w m)`
(with the properties of LIP005 that are used: self-adjoint generator whose domain lies in `H²`,
the form–generator relation on `H¹` tests, semigroup law, strong continuity and the strong
derivative at `0` on the domain), and let `(e_j, λ_j, G_j)` be a weak eigenbasis as in LIP009.
Then (a) `e_j ∈ dom Lg`, `Lg e_j = -λ_j e_j`; (b) `S t e_j = e^{-λ_j t} e_j`;
(c) `⟨S t F, e_j⟩ = e^{-λ_j t}⟨F, e_j⟩`, and these coefficients determine `S t F`. -/
theorem lip007d1_semigroup_eigen
    (Lg : Hw d w →ₗ.[ℝ] Hw d w) (S : ℝ≥0 → Hw d w →L[ℝ] Hw d w)
    (hsa : IsSelfAdjoint Lg)
    (hdom : ∀ f : Hw d w, f ∈ Lg.domain → MemH2 (f : Torus d → ℝ))
    (hform : ∀ (f : Hw d w) (hf : f ∈ Lg.domain) (Gf : Torus d → Tangent d),
      IsWeakGradient (f : Torus d → ℝ) Gf → ∀ (v : Hw d w) (Gv : Torus d → Tangent d),
      IsWeakGradient (v : Torus d → ℝ) Gv →
        weightedForm w Gf Gv = -⟪Lg ⟨f, hf⟩, v⟫_ℝ)
    (hS0 : ∀ f, S 0 f = f) (hadd : ∀ (s t : ℝ≥0) f, S (s + t) f = S s (S t f))
    (hsymm : ∀ t, ∀ f g : Hw d w, ⟪S t f, g⟫_ℝ = ⟪f, S t g⟫_ℝ)
    (hcont : ∀ f, Continuous fun t : ℝ≥0 => S t f)
    (hder : ∀ f : Lg.domain, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S t (f : Hw d w) - f))
      (𝓝[≠] (0 : ℝ≥0)) (𝓝 (Lg f)))
    (e : HilbertBasis ℕ ℝ (Hw d w)) (lam : ℕ → ℝ) (G : ℕ → Torus d → Tangent d)
    (hgrad : ∀ j, IsWeakGradient ((e j : Hw d w) : Torus d → ℝ) (G j))
    (heig : ∀ j (f : Hw d w) (Y : Torus d → Tangent d), IsWeakGradient (f : Torus d → ℝ) Y →
      weightedForm w (G j) Y = lam j * ⟪e j, f⟫_ℝ) :
    (∀ j, ∃ h : e j ∈ Lg.domain, Lg ⟨e j, h⟩ = (-lam j) • e j) ∧
    (∀ (j : ℕ) (t : ℝ≥0), S t (e j) = Real.exp (-lam j * t) • e j) ∧
    (∀ (F : Hw d w) (t : ℝ≥0) (j : ℕ),
      ⟪S t F, e j⟫_ℝ = Real.exp (-lam j * t) * ⟪F, e j⟫_ℝ) ∧
    (∀ (F G' : Hw d w) (t : ℝ≥0),
      (∀ j, ⟪G', e j⟫_ℝ = Real.exp (-lam j * t) * ⟪F, e j⟫_ℝ) → G' = S t F) := by
  have hAdj : Lg† = Lg := hsa
  have ha : ∀ j, ∃ h : e j ∈ Lg.domain, Lg ⟨e j, h⟩ = (-lam j) • e j := by
    intro j
    have hx : ∀ x : Lg.domain, ⟪(-lam j) • e j, (x : Hw d w)⟫_ℝ = ⟪e j, Lg x⟫_ℝ := by
      intro x
      obtain ⟨Gx, Hx, hGx⟩ := hdom x x.2
      have h1 := hform x x.2 Gx hGx.grad (e j) (G j) (hgrad j)
      have h2 := heig j x Gx hGx.grad
      rw [weightedForm_comm] at h1
      rw [h2] at h1
      have h3 := real_inner_comm (Lg x : Hw d w) (e j)
      rw [real_inner_smul_left]
      have : Lg ⟨(x : Hw d w), x.2⟩ = Lg x := rfl
      rw [this] at h1
      linarith
    have hmem : e j ∈ Lg†.domain :=
      LinearPMap.mem_adjoint_domain_of_exists _ ⟨(-lam j) • e j, fun x => by
        rw [hx x]⟩
    have hmem' : e j ∈ Lg.domain := by rw [← hAdj]; exact hmem
    refine ⟨hmem', ?_⟩
    have h5 := LinearPMap.adjoint_apply_eq (T := Lg) (hT := hsa.dense_domain) ⟨e j, hmem⟩
      (x₀ := (-lam j) • e j) (fun x => by rw [hx x])
    rw [← h5]
    exact (pmap_apply_congr Lg Lg† hAdj.symm (e j) hmem' hmem)
  have hb : ∀ (j : ℕ) (t : ℝ≥0), S t (e j) = Real.exp (-lam j * t) • e j := by
    intro j t
    obtain ⟨h, hL⟩ := ha j
    exact semigroup_apply_eigen Lg S hS0 hadd hcont hder (e j) h (lam j) hL t
  have hc : ∀ (F : Hw d w) (t : ℝ≥0) (j : ℕ),
      ⟪S t F, e j⟫_ℝ = Real.exp (-lam j * t) * ⟪F, e j⟫_ℝ := by
    intro F t j
    rw [hsymm, hb, real_inner_smul_right]
  refine ⟨ha, hb, hc, ?_⟩
  intro F G' t hG
  have h0 : G' - S t F = 0 := by
    have : e.repr (G' - S t F) = 0 := by
      ext j
      have a1 : ⟪e j, G'⟫_ℝ = Real.exp (-lam j * t) * ⟪F, e j⟫_ℝ := by
        rw [real_inner_comm]; exact hG j
      have a2 : ⟪e j, S t F⟫_ℝ = Real.exp (-lam j * t) * ⟪F, e j⟫_ℝ := by
        rw [real_inner_comm]; exact hc F t j
      rw [HilbertBasis.repr_apply_apply, inner_sub_right, a1, a2]
      simp
    exact (e.repr.map_eq_zero_iff).mp this
  exact sub_eq_zero.mp h0

end Concrete

end DGPS.Lipschitz.SemigroupEigen
