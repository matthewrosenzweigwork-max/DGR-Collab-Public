import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D19_Lip
import SharpSymmetricLSI.Statements.R06_Upper_Bound
import SharpSymmetricLSI.Infra.Heat
import SharpSymmetricLSI.Paper.AppAStab5
import SharpSymmetricLSI.Paper.AppAEvol1
import SharpSymmetricLSI.Paper.AppAEvol2
import SharpSymmetricLSI.Paper.AppAPicard5
import SharpSymmetricLSI.Paper.AppAPos9
import SharpSymmetricLSI.Paper.AppAEvol4
import SharpSymmetricLSI.Paper.AppAWeak5
import SharpSymmetricLSI.Paper.AppAEvol5

/-!
# R36: Lemma A.1 (`lem:evolution`), the bounded-density mean-field evolution

Manuscript Lemma A.1, (4.7)–(4.10), (A.3), (A.5). For every bounded probability density `ρ_0`,
the mean-field equation (4.7) `∂_tρ = Δρ + ∇·(ρ∇(V + W*ρ))` has a unique mild probability solution
in `C([0,∞); L¹(m)) ∩ L^∞([0,T] × 𝕋^d)` for every finite `T`, where mild means (A.5)
`ρ_t = H_tρ_0 + ∫_0^t ∇·H_{t-u}(ρ_u a_{ρ_u}) du`, `a_ρ = ∇V + ∇W*ρ`, `H_t = e^{tΔ}`. It satisfies
(4.8) `F(ρ_t) + ∫_s^t D(ρ_u) du ≤ F(ρ_s)` and (4.9) `d_Lip(ρ_s,ρ_t) ≤ ∫_s^t √D(ρ_u) du`
(`0 ≤ s ≤ t`), and, if `r_* > 0`, (4.10) `G(ρ_t) ≤ G(ρ_0) e^{-2r_*t}` and
`∫_t^∞ √D(ρ_u) du ≤ √(2/r_*) √G(ρ_t)`. (A.3) `sup_{t≤T} ‖ρ_t - η_t‖₁ ≤ C_T ‖ρ_0 - η_0‖₁`, with
`C_T` depending only on `T, d, B_0 = ‖∇V‖_∞ + ‖∇₁W‖_∞, L_0 = ‖∇₁W‖_∞`.

Encodings: the solution is a family `ρ : ℝ → 𝕋^d → ℝ` (values at `t ≥ 0`); the mild equation is
required for `t > 0` (with `ρ_t → ρ_0` in `L¹` as `t ↓ 0`) and holds `m`-a.e. in `x`;
uniqueness is a.e. equality at every `t ≥ 0`. Time integrals of `D` are lintegrals over
`[s,t]`. REVIEW.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ}

/-- The drift `a_ρ = ∇V + ∇(W*ρ)`. -/
noncomputable def driftField (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Torus d → ℝ)
    (x : Torus d) (k : Fin d) : ℝ :=
  weakGrad V x k + weakGrad (convDens W ρ) x k

/-- `ρ` is a mild probability solution of (4.7) in the class of Lemma A.1, from `ρ_0`. -/
def IsMildSolution (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ₀ : Torus d → ℝ)
    (ρ : ℝ → Torus d → ℝ) : Prop :=
  (∀ t, 0 ≤ t → (∀ᵐ x ∂haar d, 0 ≤ ρ t x) ∧ ∫ x, ρ t x ∂haar d = 1) ∧
  (∀ t, 0 ≤ t →
    Tendsto (fun s => eLpNorm (fun x => ρ s x - ρ t x) 1 (haar d)) (𝓝[Ici 0] t) (𝓝 0)) ∧
  ρ 0 = ρ₀ ∧
  (∀ T, ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ᵐ x ∂haar d, |ρ t x| ≤ B) ∧
  ∀ t, 0 < t → ρ t =ᵐ[haar d] fun x => heatT t ρ₀ x +
    ∫ u in Ioc 0 t, divHeatT (t - u) (fun y k => ρ u y * driftField V W (ρ u) y k) x

/-- `B_0 = ‖∇V‖_∞ + ‖∇₁W‖_∞` and `L_0 = ‖∇₁W‖_∞` bounds. -/
def DriftBounds (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (B₀ L₀ : ℝ) : Prop :=
  eLpNorm (fun x => Real.sqrt (sqNorm (weakGrad V x))) ⊤ (haar d) +
      eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume ≤
    ENNReal.ofReal B₀ ∧
  eLpNorm (fun X : Config 2 d => Real.sqrt (sqNorm (grad1W W (X 0) (X 1)))) ⊤ volume ≤
    ENNReal.ofReal L₀

/-- Lemma A.1: existence, uniqueness, (4.8)–(4.10). -/
theorem mf_evolution {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {ρ₀ : Torus d → ℝ} (hm : Measurable ρ₀)
    (h0 : ∀ x, 0 ≤ ρ₀ x) (h1 : ∫ x, ρ₀ x ∂haar d = 1) (hb : ∃ B, ∀ x, ρ₀ x ≤ B) :
    (∃ ρ, IsMildSolution V W ρ₀ ρ) ∧
    (∀ ρ η, IsMildSolution V W ρ₀ ρ → IsMildSolution V W ρ₀ η → ∀ t, 0 ≤ t → ρ t =ᵐ[haar d] η t) ∧
    ∀ ρ, IsMildSolution V W ρ₀ ρ →
      (∀ s t, 0 ≤ s → s ≤ t →
        freeEnergy V W (densMeasure (ρ t)) +
            ((∫⁻ u in Icc s t, dissipation V W (ρ u) : ℝ≥0∞) : EReal) ≤
          freeEnergy V W (densMeasure (ρ s))) ∧
      (∀ s t, 0 ≤ s → s ≤ t →
        ENNReal.ofReal (dLipM (densMeasure (ρ s)) (densMeasure (ρ t))) ≤
          ∫⁻ u in Icc s t, dissipation V W (ρ u) ^ (1 / 2 : ℝ)) ∧
      (0 < rStar V W → ∀ t, 0 ≤ t →
        gap V W (densMeasure (ρ t)) ≤
          gap V W (densMeasure (ρ 0)) * ((Real.exp (-2 * (rStar V W).toReal * t) : ℝ) : EReal) ∧
        ∫⁻ u in Ioi t, dissipation V W (ρ u) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (Real.sqrt (2 / (rStar V W).toReal)) *
            (gap V W (densMeasure (ρ t))).toENNReal ^ (1 / 2 : ℝ)) := by
  have conv : ∀ {ρ : ℝ → Torus d → ℝ}, IsMildSolution V W ρ₀ ρ → AppAMild V W ρ₀ ρ :=
    fun {ρ} hρ => ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.1, hρ.2.2.2.2⟩
  refine ⟨?_, fun ρ η hρ hη t ht => appAMild_unique hyp (conv hρ) (conv hη) ht,
    fun ρ hρ => appAMild_evolution hyp hm h0 h1 hb (conv hρ)⟩
  obtain ⟨ρ, hρ⟩ := exists_appAMild hyp hm h0 h1 hb
  exact ⟨ρ, hρ.prob, hρ.cont, hρ.init, hρ.bdd, hρ.mild⟩

/-- (A.3): `L¹` stability, with `C_T` depending only on `T, d, B_0, L_0`. -/
theorem flow_stability (d : ℕ) (T B₀ L₀ : ℝ) :
    ∃ C : ℝ, ∀ (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (KV KW : ℝ), Hyp V W KV KW →
      DriftBounds V W B₀ L₀ →
      ∀ ρ₀ η₀ ρ η, IsMildSolution V W ρ₀ ρ → IsMildSolution V W η₀ η →
        ∀ t ∈ Icc 0 T, eLpNorm (fun x => ρ t x - η t x) 1 (haar d) ≤
          ENNReal.ofReal C * eLpNorm (fun x => ρ₀ x - η₀ x) 1 (haar d) := by
  obtain ⟨C, hC⟩ := flow_stability_aux d T B₀ L₀
  exact ⟨C, fun V W KV KW hyp hDB ρ₀ η₀ ρ η hρ hη t ht =>
    hC V W KV KW hyp hDB ρ₀ η₀ ρ η ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.1, hρ.2.2.2.2⟩
      ⟨hη.1, hη.2.1, hη.2.2.1, hη.2.2.2.1, hη.2.2.2.2⟩ t ht⟩

end SharpLSI
