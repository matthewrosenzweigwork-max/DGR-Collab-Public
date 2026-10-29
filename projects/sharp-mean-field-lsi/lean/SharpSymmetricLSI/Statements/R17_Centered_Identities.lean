import SharpSymmetricLSI.Defs.D08_Gibbs
import SharpSymmetricLSI.Defs.D13_Equilibrium
import SharpSymmetricLSI.Paper.Centering

/-!
# R17: Section 4.3, centering identities (4.14), (4.15)

Manuscript Section 4.3. For a minimizer `μ` of `F` under (1.2):
* `∫ K(x,y) dμ(y) = 0` for every `x`, and the integral operator of `K` on `L²_0(μ)` is `T`;
* (4.15) `G(ρ) = H(ρ|μ) + J(ρ)` for every probability `ρ` (in `EReal`), and
  `dP_N = p_N dμ^{⊗N}` with `p_N = K_N^{-1} e^{-U_N}`, `U_N = N J(L_N)`.
(The manuscript states these for the unique minimizer under `r_* > 0`; they use only the
Euler–Lagrange equation (4.1), so they are stated for every minimizer.)
-/

open MeasureTheory InformationTheory

namespace SharpLSI

variable {d : ℕ}

/-- `∫ K(x,y) dμ(y) = 0` and `T h = ∫ K(·,y) h(y) dμ(y)` on `L²_0(μ)`. -/
theorem centeredKernel_props {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) :
    (∀ x, ∫ y, centeredKernel W μ x y ∂(μ : Measure (Torus d)) = 0) ∧
    ∀ h, MemL20 μ h → ∀ x,
      Top W μ h x = ∫ y, centeredKernel W μ x y * h y ∂(μ : Measure (Torus d)) := by
  exact ⟨fun x => integral_centeredKernel hyp μ x, fun h hh x => Top_eq_integral hyp μ hh x⟩

/-- (4.15): `G = H(·|μ) + J`. -/
theorem gap_eq_entropy_add_J {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (ρ : ProbabilityMeasure (Torus d)) :
    gap V W ρ = ((klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d)) : ENNReal) : EReal) +
      ((Jfun W μ ρ : ℝ) : EReal) := by
  exact gap_eq_aux hyp hμ ρ

/-- (4.15): `dP_N = K_N^{-1} e^{-U_N} dμ^{⊗N}`. -/
theorem gibbs_eq_centered {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) {μ : ProbabilityMeasure (Torus d)}
    (hμ : IsMinimizer V W μ) (N : ℕ) :
    gibbs V W N = (Measure.pi (fun _ : Fin N => (μ : Measure (Torus d)))).withDensity
      (fun X => ENNReal.ofReal (Real.exp (-Ucentered W μ N X) / centeredPartition W μ N)) := by
  exact gibbs_eq_centered_aux hyp hμ N

end SharpLSI
