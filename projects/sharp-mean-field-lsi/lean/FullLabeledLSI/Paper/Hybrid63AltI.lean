import FullLabeledLSI.Paper.Hybrid63AltH

/-!
# Proposition 6.3: the per-`N` inequality

`per_N`: for one `N`, one coefficient array `c = coefArr T cc` (spectral range of `F`) and one `δ`
with `n > 0`:  `-(errors) ≤ Jexpr A lam (CR R) R F`, where the errors are seven explicit differences
of integrals (all with the measurable bounded basis `e'`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace SharpLSI.FL

variable {d : ℕ}

section errs
variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

/-- `|∫ F² v_R(Z_N) - ∫ F² v_R(Z^low)|`. -/
def errT1 (μ : Measure (Torus d)) (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (R : ℕ)
    (e' : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) : ℝ :=
  |∫ X, polyEval e' c X ^ 2 * vR A lam R (fun n => fluct e' N n X)
      ∂Measure.pi (fun _ : Fin N => μ) -
    ∫ X, polyEval e' c X ^ 2 * vR A lam R (zext (fun m : Fin J => Zlow e' c δ X m))
      ∂Measure.pi (fun _ : Fin N => μ)|

/-- `|∫ F² v_R(Z^low) - ∫ F̃² v_R(G)|`. -/
def errT2 (μ : Measure (Torus d)) (A : FiniteRankApprox W μ e) (lam : ℕ → ℝ) (R : ℕ)
    (e' : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) : ℝ :=
  |∫ X, polyEval e' c X ^ 2 * vR A lam R (zext (fun m : Fin J => Zlow e' c δ X m))
      ∂Measure.pi (fun _ : Fin N => μ) -
    ∫ w, hybEval e' c δ w ^ 2 * vR A lam R (zext (Glow c δ w)) ∂hybMeasure μ N J|

/-- `|∫ φ(F) - ∫ φ(F̃)|`. -/
def errT3 (μ : Measure (Torus d)) (e' : ℕ → Torus d → ℝ) {N J : ℕ}
    (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) : ℝ :=
  |∫ X, Sec6.phi (polyEval e' c X) ∂Measure.pi (fun _ : Fin N => μ) -
    ∫ w, Sec6.phi (hybEval e' c δ w) ∂hybMeasure μ N J|

/-- `|ψ(∫ F²) - ψ(∫ F̃²)|`. -/
def errT4 (μ : Measure (Torus d)) (e' : ℕ → Torus d → ℝ) {N J : ℕ}
    (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) : ℝ :=
  |Sec6.psi (∫ X, polyEval e' c X ^ 2 ∂Measure.pi (fun _ : Fin N => μ)) -
    Sec6.psi (∫ w, hybEval e' c δ w ^ 2 ∂hybMeasure μ N J)|

/-- `|∫ F² u_R(Z_N) - ∫ F² u_R(Z^low)|`. -/
def errT5 (μ : Measure (Torus d)) (A : FiniteRankApprox W μ e) (R : ℕ)
    (e' : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) : ℝ :=
  |∫ X, polyEval e' c X ^ 2 * uR A R (fun n => fluct e' N n X)
      ∂Measure.pi (fun _ : Fin N => μ) -
    ∫ X, polyEval e' c X ^ 2 * uR A R (zext (fun m : Fin J => Zlow e' c δ X m))
      ∂Measure.pi (fun _ : Fin N => μ)|

/-- `|∫ F² u_R(Z^low) - ∫ F̃² u_R(G)|`. -/
def errT6 (μ : Measure (Torus d)) (A : FiniteRankApprox W μ e) (R : ℕ)
    (e' : ℕ → Torus d → ℝ) {N J : ℕ} (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) : ℝ :=
  |∫ X, polyEval e' c X ^ 2 * uR A R (zext (fun m : Fin J => Zlow e' c δ X m))
      ∂Measure.pi (fun _ : Fin N => μ) -
    ∫ w, hybEval e' c δ w ^ 2 * uR A R (zext (Glow c δ w)) ∂hybMeasure μ N J|

/-- `|∫ F² - ∫ F̃²|`. -/
def errT7 (μ : Measure (Torus d)) (e' : ℕ → Torus d → ℝ) {N J : ℕ}
    (c : (Fin N → Fin (J + 1)) → ℝ) (δ : ℝ) : ℝ :=
  |∫ X, polyEval e' c X ^ 2 ∂Measure.pi (fun _ : Fin N => μ) -
    ∫ w, hybEval e' c δ w ^ 2 ∂hybMeasure μ N J|

end errs

section perN
variable {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}

theorem per_N (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : IsMinimizer V W μ)
    (e : ℕ → Torus d → ℝ) (lam : ℕ → ℝ) (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    (A : FiniteRankApprox W (μ : Measure (Torus d)) e) (CR : ℕ → ℕ → ℕ → ℝ) (R : ℕ)
    {σ : ℝ} (hσ : 0 < σ) (hpos : PosIPlus A R σ) (hC : IsInverseOfIPlus (A.a R) (CR R))
    (e' : ℕ → Torus d → ℝ) (hG : GoodBasis (μ : Measure (Torus d)) e')
    (hae : ∀ j, e j =ᵐ[(μ : Measure (Torus d))] e' j)
    (J : ℕ) (hJ : ∀ i ∈ A.s R, i < J) (L : ℝ) {N : ℕ} (T : Finset (Fin N → ℕ))
    (cc : (Fin N → ℕ) → ℝ) (hT : ∀ k ∈ T, ∑ i, lam (k i) ≤ L) (hTJ : ∀ k ∈ T, ∀ i, k i ≤ J)
    (F : Config N d → ℝ) (hF : ∀ X, F X = ∑ k ∈ T, cc k * ∏ i, e (k i) (X i))
    (δ : ℝ) (hn : 0 < lowCount (coefArr (J := J) T cc) δ) :
    -(errT1 (μ : Measure (Torus d)) A lam R e' (coefArr (J := J) T cc) δ +
      errT2 (μ : Measure (Torus d)) A lam R e' (coefArr (J := J) T cc) δ +
      (bRate (μ : Measure (Torus d)) lam (CR R)).toReal / 2 *
        (errT3 (μ : Measure (Torus d)) e' (coefArr (J := J) T cc) δ +
          errT4 (μ : Measure (Torus d)) e' (coefArr (J := J) T cc) δ +
          errT5 (μ : Measure (Torus d)) A R e' (coefArr (J := J) T cc) δ +
          errT6 (μ : Measure (Torus d)) A R e' (coefArr (J := J) T cc) δ +
          |Real.log (kappaR A R)| * errT7 (μ : Measure (Torus d)) e' (coefArr (J := J) T cc) δ))
      ≤ Jexpr A lam (CR R) R F := by
  set c : (Fin N → Fin (J + 1)) → ℝ := coefArr (J := J) T cc with hc
  have hcspec : SpectralCoeff lam L c := spectralCoeff_coefArr lam L T hT cc
  have hFe : F = polyEval e c := funext fun X => by
    rw [hF X, hc, polyEval_coefArr e T hTJ cc X]
  obtain ⟨eC, a, hac, hca, hC1, haeC, -, -, hlam0, hlamnn, -, -, -⟩ :=
    Gross.torus_standing hd hyp hr μ hμ e lam he
  -- the energy
  have hnn : 0 ≤ ∑ k ∈ T, (∑ i, lam (k i)) * cc k ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (Finset.sum_nonneg fun i _ => hlamnn _) (sq_nonneg _)
  have hE : (refEnergy (μ : Measure (Torus d)) (polyEval e c)).toReal =
      ∑ j, (∑ i, lam (j i)) * c j ^ 2 := by
    have := (Gross.torus_energy_formula hac hca he hC1 haeC T cc
      (F := polyEval e c) (fun X => by rw [hc, polyEval_coefArr e T hTJ cc X])).2
    rw [this, ENNReal.toReal_ofReal hnn, hc, energy_coefArr lam T hTJ cc]
  -- the hybrid inequality
  have hBs : (retained c δ).card < N := by
    have : (retained c δ).card ≤ N := by simpa using Finset.card_le_univ (retained c δ)
    unfold lowCount at hn; omega
  have hH := hybridInequality_alt hd hyp hr μ hμ e lam he A CR R σ hσ hpos hC J hJ L N
    (retained c δ) hBs c hcspec
  have hae' : ∀ j, e' j =ᵐ[(μ : Measure (Torus d))] e j := fun j => (hae j).symm
  have hpe := HLA.polyB_ae_congr (N := N) (J := J) (μ : Measure (Torus d)) hae' c (retained c δ)
  have hsq : (fun w => polyB e' c (retained c δ) w ^ 2) =ᵐ[hybMeasure (μ : Measure (Torus d)) N J]
      fun w => polyB e c (retained c δ) w ^ 2 := hpe.mono fun w hw => by simp only [hw]
  have U1 : ∫ w, polyB e c (retained c δ) w ^ 2 *
        vR A lam R (zext (Gcoll (retained c δ) w.2)) ∂hybMeasure (μ : Measure (Torus d)) N J =
      ∫ w, polyB e' c (retained c δ) w ^ 2 *
        vR A lam R (zext (Gcoll (retained c δ) w.2)) ∂hybMeasure (μ : Measure (Torus d)) N J :=
    integral_congr_ae (hpe.mono fun w hw => by simp only [hw])
  have U2 : ∫ w, polyB e c (retained c δ) w ^ 2 *
        uR A R (zext (Gcoll (retained c δ) w.2)) ∂hybMeasure (μ : Measure (Torus d)) N J =
      ∫ w, polyB e' c (retained c δ) w ^ 2 *
        uR A R (zext (Gcoll (retained c δ) w.2)) ∂hybMeasure (μ : Measure (Torus d)) N J :=
    integral_congr_ae (hpe.mono fun w hw => by simp only [hw])
  have U3 : ∫ w, polyB e c (retained c δ) w ^ 2 ∂hybMeasure (μ : Measure (Torus d)) N J =
      ∫ w, polyB e' c (retained c δ) w ^ 2 ∂hybMeasure (μ : Measure (Torus d)) N J :=
    (integral_congr_ae hsq).symm
  have U4 : ent (hybMeasure (μ : Measure (Torus d)) N J) (fun w => polyB e c (retained c δ) w ^ 2) =
      ent (hybMeasure (μ : Measure (Torus d)) N J) (fun w => polyB e' c (retained c δ) w ^ 2) :=
    (ent_congr_ae hsq).symm
  rw [U1, U2, U3, U4] at hH
  -- the entropies
  have hmomE : HybridPolyMoment (μ : Measure (Torus d)) e lam J :=
    hybridPolyMoment_of_min hd hyp hr μ hμ e lam he J
  have hmom' : HybridPolyMoment (μ : Measure (Torus d)) e' lam J :=
    hmomE.of_ae_eq hae
  obtain ⟨K4, -, hK4⟩ := hyb_integrable_pow hG hmom' L 4
  have hentH := ent_toReal_formula (hybMeasure (μ : Measure (Torus d)) N J)
    (measurable_polyB hG c (retained c δ)) (hK4 N (retained c δ) c hcspec).1
  obtain ⟨Kb, hKb⟩ := polyEval_bounded hG c
  have hentQ := ent_toReal_formula (Measure.pi fun _ : Fin N => (μ : Measure (Torus d)))
    (measurable_polyEval hG c)
    (Integrable.of_bound ((measurable_polyEval hG c).abs.pow_const 4).aestronglyMeasurable
      (|Kb| ^ 4) (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs, abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hKb X).trans (le_abs_self _)) 4))
  -- assemble
  have hJe := Jexpr_eq_e' A lam (CR R) R hae c hE
  rw [hFe, hJe]
  have key := master_alg (E := ∑ j, (∑ i, lam (j i)) * c j ^ 2)
    (Vq := ∫ X, polyEval e' c X ^ 2 * vR A lam R (fun n => fluct e' N n X)
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))))
    (Vl := ∫ X, polyEval e' c X ^ 2 * vR A lam R (zext (fun m : Fin J => Zlow e' c δ X m))
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))))
    (Uq := ∫ X, polyEval e' c X ^ 2 * uR A R (fun n => fluct e' N n X)
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))))
    (Ul := ∫ X, polyEval e' c X ^ 2 * uR A R (zext (fun m : Fin J => Zlow e' c δ X m))
      ∂Measure.pi (fun _ : Fin N => (μ : Measure (Torus d))))
    (ρ := (bRate (μ : Measure (Torus d)) lam (CR R)).toReal) (K := Real.log (kappaR A R))
    ENNReal.toReal_nonneg hentQ hentH hH
  unfold errT1 errT2 errT3 errT4 errT5 errT6 errT7
  exact key

end perN

end SharpLSI.FL

end
