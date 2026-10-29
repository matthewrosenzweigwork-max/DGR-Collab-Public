import SharpSymmetricLSI.Paper.R7Basic
import SharpSymmetricLSI.Paper.Prop23Defs

/-!
# (2.8) (lane s42): the lower bound `liminf λ_N^sym ≥ λ_G`

Manuscript Section 8.5: if along a subsequence there are symmetric mean-zero functions of unit
norm with energies below `a < λ_G`, compactness (`CompactnessProperty'`, (2.5)–(2.7)) gives a
Gaussian limit `F` with `∫F = 0`, `∫F² = 1`, `ℰ_∞(F) ≤ a`, contradicting the Gaussian Poincaré
inequality `Var_γ F ≤ ℰ_∞(F)/λ_G` (8.10). Stated for an arbitrary form `EInf` and constant `lG`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

/-- Normalization of a test function of the symmetric Poincaré quotient. -/
theorem normalize_poincare_test (hyp : Hyp V W KV KW) {N : ℕ} {f : Config N d → ℝ}
    (hmem : MemH1C (gibbs V W N) f) (hsym : IsSymmetric f) (hvar : 0 < var (gibbs V W N) f)
    {a : ℝ≥0∞} (hlt : energy V W N f / var (gibbs V W N) f < a) :
    ∃ g : Config N d → ℝ, MemH1C (gibbs V W N) g ∧ IsSymmetric g ∧
      ∫ X, g X ∂gibbs V W N = 0 ∧ ∫ X, g X ^ 2 ∂gibbs V W N = 1 ∧ energy V W N g < a := by
  haveI := gibbs_isProbabilityMeasure hyp N
  set P := gibbs V W N
  have hL2 := memLp_of_memH1C hyp hmem
  set m := ∫ X, f X ∂P
  set v := (var P f).toReal
  have hvt : var P f ≠ ⊤ := hL2.evariance_lt_top.ne
  have hve : var P f = ENNReal.ofReal v := (ENNReal.ofReal_toReal hvt).symm
  have hv0 : 0 < v := ENNReal.toReal_pos hvar.ne' hvt
  have hvv : v = ∫ X, (f X - m) ^ 2 ∂P := by
    show (evariance f P).toReal = _
    rw [← hL2.ofReal_variance_eq, ENNReal.toReal_ofReal (variance_nonneg _ _),
      variance_eq_integral hL2.aestronglyMeasurable.aemeasurable]
  set c := 1 / Real.sqrt v
  have hc2 : c ^ 2 = 1 / v := by
    rw [div_pow, one_pow, Real.sq_sqrt hv0.le]
  refine ⟨fun X => c * (f X + -m), memH1C_smul hyp (memH1C_add_const hyp hmem (-m)) c,
    fun σ X => by simp only [hsym σ X], ?_, ?_, ?_⟩
  · rw [integral_const_mul, integral_add (hL2.integrable one_le_two) (integrable_const _)]
    show c * (m + ∫ _X, -m ∂P) = 0
    rw [integral_const]
    simp
  · have e : (fun X => (c * (f X + -m)) ^ 2) = fun X => c ^ 2 * (f X - m) ^ 2 := by
      funext X; ring
    rw [e, integral_const_mul, ← hvv, hc2, one_div, inv_mul_cancel₀ hv0.ne']
  · rw [energy_smul hyp (memH1C_add_const hyp hmem (-m)) c, energy_add_const hyp hmem, hc2]
    calc ENNReal.ofReal (1 / v) * energy V W N f = energy V W N f / var P f := by
          rw [hve, ENNReal.div_eq_inv_mul, one_div, ENNReal.ofReal_inv_of_pos hv0]
      _ < a := hlt

/-- **`liminf λ_N^sym ≥ λ_G`** from compactness and the Gaussian Poincaré inequality. -/
theorem le_liminf_lamSym (hyp : Hyp V W KV KW) {γ : Measure (ℕ → ℝ)} [IsProbabilityMeasure γ]
    {EInf : ((ℕ → ℝ) → ℝ) → ℝ≥0∞} {lG : ℝ≥0∞} (hcomp : CompactnessProperty' V W γ EInf)
    (hP : ∀ f : (ℕ → ℝ) → ℝ, MemLp f 2 γ → var γ f ≤ EInf f / lG) :
    lG ≤ liminf (fun N => lamSym V W N) atTop := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, hLa, haG⟩ := exists_between hcon
  have hat : a ≠ ⊤ := haG.ne_top
  have hfreq : ∃ᶠ N in atTop, lamSym V W N < a := frequently_lt_of_liminf_lt (by isBoundedDefault) hLa
  -- normalized tests along a subsequence
  have hP' : ∃ᶠ N in atTop, ∃ g : Config N d → ℝ, MemH1C (gibbs V W N) g ∧ IsSymmetric g ∧
      ∫ X, g X ∂gibbs V W N = 0 ∧ ∫ X, g X ^ 2 ∂gibbs V W N = 1 ∧ energy V W N g < a := by
    refine hfreq.mono fun N hN => ?_
    unfold lamSym at hN
    obtain ⟨f, hf⟩ := iInf_lt_iff.mp hN
    obtain ⟨hfS, hlt⟩ := iInf_lt_iff.mp hf
    obtain ⟨hmem, hsym, hvar⟩ := hfS
    exact normalize_poincare_test hyp hmem hsym hvar hlt
  obtain ⟨φ, hφ, hφP⟩ := extraction_of_frequently_atTop hP'
  choose g hg using hφP
  have hN : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hB : ∃ B : NNReal, ∀ k,
      (∫⁻ X, ENNReal.ofReal (g k X ^ 2) ∂gibbs V W (φ k)) + energy V W (φ k) (g k) ≤ B := by
    refine ⟨(1 + a).toNNReal, fun k => ?_⟩
    obtain ⟨hmem, -, -, h2, hlt⟩ := hg k
    haveI := gibbs_isProbabilityMeasure hyp (φ k)
    have hi : Integrable (fun X => g k X ^ 2) (gibbs V W (φ k)) :=
      (memLp_of_memH1C hyp hmem).integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => sq_nonneg _), h2,
      ENNReal.ofReal_one, ENNReal.coe_toNNReal (by simpa using hat)]
    exact add_le_add le_rfl hlt.le
  obtain ⟨ψ, -, F, hF2, -, -, hmean, hsq, hform, -⟩ :=
    hcomp φ hN g (fun k => ⟨(hg k).1, (hg k).2.1⟩) hB
  have hF0 : ∫ z, F z ∂γ = 0 := by
    have : Tendsto (fun k => ∫ X, g (ψ k) X ∂gibbs V W (φ (ψ k))) atTop (𝓝 0) := by
      simp only [fun k => (hg (ψ k)).2.2.1]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hmean this
  have hF1 : ∫ z, F z ^ 2 ∂γ = 1 := by
    have : Tendsto (fun k => ∫ X, g (ψ k) X ^ 2 ∂gibbs V W (φ (ψ k))) atTop (𝓝 1) := by
      simp only [fun k => (hg (ψ k)).2.2.2.1]; exact tendsto_const_nhds
    exact tendsto_nhds_unique hsq this
  have hEa : EInf F ≤ a :=
    hform.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun k => (hg (ψ k)).2.2.2.2.le))
  have hvarF : var γ F = 1 := by
    show evariance F γ = 1
    rw [← hF2.ofReal_variance_eq,
      variance_of_integral_eq_zero hF2.aestronglyMeasurable.aemeasurable hF0]
    simp only [Pi.pow_apply, hF1, ENNReal.ofReal_one]
  have h1 := hP F hF2
  rw [hvarF] at h1
  have hlG0 : lG ≠ 0 := (lt_of_le_of_lt zero_le haG).ne'
  have h2 : EInf F / lG < 1 := by
    calc EInf F / lG ≤ a / lG := ENNReal.div_le_div_right hEa _
      _ < 1 := by
        exact ENNReal.div_lt_of_lt_mul (by rw [one_mul]; exact haG)
  exact absurd (h1.trans_lt h2) (lt_irrefl _)

end SharpLSI
