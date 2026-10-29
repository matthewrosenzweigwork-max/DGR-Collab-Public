import FullLabeledLSI.Examples.E01_AttractiveStatements

/-!
# E01a: shared helper statements for the Section 9 proving lanes (STUBS, all `sorry`)

Interface stub (route plan `Audit/FLX/route_plan_20261008.md`, section 0, H0): statements of the helpers
H1, H3, H4, H8 so that the lanes compile against fixed signatures.  Nothing here is proved.  Every
declaration carries `sorry`; no sorry-free claim is made.

* H1 `msGap_attr`, `msDiss_attr`: the identities (9.2), (9.3) for `W = attrW C`.
* H3 `agreement_of_bounds`: reduction of `AgreementAt` to `ℓ ≤ r_ms` and `λ_G ≤ ℓ` for all reference data.
* H4 `lamG_formula`, `exists_ref_data`: the Fourier formula (9.8) for `λ_G`, and existence of data.
* H8 `sMin_regularity`: smoothness, positivity and the Euler equation of a minimizer of `S_{r,A}`.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL
namespace Ex

/-- The Fourier coefficient `Ĉ(n) = ∫ C e^{-2πinx} dm` (real part, as in `QC`, `hCpos`, `hsup`). -/
noncomputable def chat (C : Torus 1 → ℝ) (n : ℤ) : ℝ :=
  (∫ x, fourier (-n) (x 0) * (C x : ℂ) ∂haar 1).re

/-! ### H1: the identities (9.2) and (9.3) -/

/-- (9.2): if Haar minimizes the free energy of `W = C(0) - C(x-y)`, then for every admissible family
`G_θ(ρ) = ∑ θ_a H(ρ_a|m) - ½ ∫ ρ̄ (C*ρ̄) dm`.  (`F_* = C(0)/2` is part of the proof.) -/
theorem msGap_attr {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (F : Family 1) (hF : F.Admissible) :
    msGap zeroV (attrW C) F =
      ((∑ a, ENNReal.ofReal (F.θ a) * klDiv (densMeasure (F.ρ a)) (haar 1) : ℝ≥0∞) : EReal) -
        ((1 / 2 * ∫ x, F.bar x * convT C F.bar x ∂haar 1 : ℝ) : EReal) := by
  sorry

/-- (9.3): for every admissible family (under the Haar-minimizer hypothesis) `D_θ(ρ)` is finite and
`D_θ(ρ) = ∑ θ_a I(ρ_a|m) + 2 ∫ ρ̄ (C''*ρ̄) dm + ∫ ρ̄ |(C*ρ̄)'|² dm`, stated in real form because the
interaction terms need not be separately nonnegative. -/
theorem msDiss_attr {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (F : Family 1) (hF : F.Admissible)
    (hfin : msDiss zeroV (attrW C) F ≠ ⊤) :
    (msDiss zeroV (attrW C) F).toReal =
      ∑ a, F.θ a * (fisherInfo (densMeasure (F.ρ a)) (haar 1)).toReal +
        2 * ∫ x, F.bar x * convT (dT (dT C)) F.bar x ∂haar 1 +
          ∫ x, F.bar x * (convT (dT C) F.bar x) ^ 2 ∂haar 1 := by
  sorry

/-- Finiteness of `D_θ(ρ)` for admissible families of a good kernel (so `hfin` above is automatic). -/
theorem msDiss_ne_top_attr {C : Torus 1 → ℝ} (hC : GoodKernel C) (F : Family 1) (hF : F.Admissible) :
    msDiss zeroV (attrW C) F ≠ ⊤ := by
  sorry

/-! ### H3: the `AgreementAt` wrapper -/

/-- If `ℓ > 0`, `ofReal ℓ ≤ r_ms`, and `λ_G ≤ ofReal ℓ` for every reference eigenbasis datum of Haar
measure, then `AgreementAt W ℓ`.  Proof route: `r_ms ≤ r_* ≤ λ_G ≤ ofReal ℓ ≤ r_ms`
(`upper_comparison.2`, `rStar_le_lamG`), existence of reference data from `ref_spectrum` (needs
`r_* > 0`, available from `ofReal ℓ ≤ r_ms ≤ r_*`), and the two particle limits from
`full_labeled_lsi_limit` and `sharp_symmetric_lsi_limit`. -/
theorem agreement_of_bounds {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (hyp : ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (hlow : ENNReal.ofReal ℓ ≤ rMs zeroV (attrW C))
    (hup : ∀ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ),
      IsRefEigenbasis (haar 1) e lam → IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm →
        lamG (lamShift lam) Cm ≤ ENNReal.ofReal ℓ) :
    AgreementAt (attrW C) ℓ := by
  sorry

/-- `Hyp` for a smooth even kernel (route plan H2: `Sec8.hyp_WG`); stated here so lanes can quote it. -/
theorem hyp_attr {C : Torus 1 → ℝ} (hC : GoodKernel C) :
    ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW := by
  sorry

/-! ### H4: the exact formula (9.8) for `λ_G` -/

/-- (9.8): if `sup_{n≠0} Ĉ(n) < 1` and Haar is a free-energy minimizer, then for every reference
eigenbasis datum `λ_G = inf_{n ≥ 1} 4π² n² (1 - Ĉ(n))`.  No hypothesis `r_* > 0` is used. -/
theorem lamG_formula {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (hyp : ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ)
    (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ)
    (he : IsRefEigenbasis (haar 1) e lam) (hCm : IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm) :
    lamG (lamShift lam) Cm =
      ⨅ n : ℕ, ENNReal.ofReal (aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat C ((n : ℤ) + 1))) := by
  sorry

/-- Existence of reference data `(e, lam, Cm)` for Haar measure under `sup Ĉ < 1` and `Ĉ ≥ 0`
(used for the non-vacuity half of `LamGValue`). -/
theorem exists_ref_data {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (hyp : ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ) :
    ∃ (e : ℕ → Torus 1 → ℝ) (lam : ℕ → ℝ) (Cm : ℕ → ℕ → ℝ),
      IsRefEigenbasis (haar 1) e lam ∧ IsInverseOfIPlus (Tmat (attrW C) (haar 1) e) Cm := by
  sorry

/-- Consequence packaged for `LamGValue`: under the hypotheses of `lamG_formula` the value is the
Fourier infimum. -/
theorem lamGValue_of_formula {C : Torus 1 → ℝ} (hC : GoodKernel C)
    (hmin : IsMinimizer zeroV (attrW C) haarPM) (hyp : ∃ KV KW : ℝ, Hyp zeroV (attrW C) KV KW)
    (hsup : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℤ, n ≠ 0 → chat C n ≤ 1 - δ) :
    LamGValue (attrW C)
      (⨅ n : ℕ, ENNReal.ofReal (aCos * ((n : ℝ) + 1) ^ 2 * (1 - chat C ((n : ℤ) + 1)))) := by
  sorry

/-! ### H8: regularity of minimizers of `S_{r,A}` -/

/-- A minimizer `f` of `S_{r,A}` (`IsSMin`, constraint `∫ f² = 1`) with `A` smooth agrees almost everywhere with a
smooth, strictly positive function `g` solving `-4 g'' + A g - 4 r g log g = η g`, `η = S_{r,A}(f)` the minimum value.
(Smoothness of `A` is needed: for merely continuous `A` the minimizer is only `C²`; the a.e. representative is needed
because `IsSMin` does not see null sets.)  This is the route plan's H8 (shared by Lemma 9.5, Lemma 9.9). -/
theorem sMin_regularity {r : ℝ} (hr : 0 ≤ r) {A : Torus 1 → ℝ} (hA : IsSmoothT A) {f : Torus 1 → ℝ}
    (hf : IsSMin r A f) :
    ∃ g : Torus 1 → ℝ, g =ᵐ[haar 1] f ∧ IsSmoothT g ∧ (∀ x, 0 < g x) ∧
      ∀ x : Torus 1, -4 * dT (dT g) x + A x * g x - 4 * r * g x * Real.log (g x) =
        sFunctional r A f * g x := by
  sorry

end Ex
end SharpLSI.FL
