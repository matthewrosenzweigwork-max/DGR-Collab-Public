import FullLabeledLSI.Nonvacuity.Prop82.CBdd
import FullLabeledLSI.Nonvacuity.Prop82.CCalc

/-!
# Lane C, module C4 (part 1): the profile `t ↦ f̄(t)` along a smooth variation

For `u` bounded measurable `≥ 0` with `∫ u² = 1`, and a smooth `φ` orthogonal to the five test
functions in the sense `∫ e_j u φ = 0`, the competitor densities are `ρ_t = (u + tφ)²/N(t)`.
This file defines the quantities entering `realDiss ρ_t - 2 R realGap ρ_t` and proves that the
resulting profile `Fb` has derivative `8 ∫ g φ' - 4 R ∫ u φ log u²` at `t = 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI.FL.Prop82

open SharpLSI

section Profile

variable (u φ : Torus 1 → ℝ)

noncomputable def MM (e : Torus 1 → ℝ) (t : ℝ) : ℝ := ∫ x, e x * (u x + t * φ x) ^ 2 ∂haar 1
noncomputable def NN (t : ℝ) : ℝ := MM u φ (fun _ => 1) t
noncomputable def Wd (t : ℝ) : ℝ :=
  ∫ x, (weakGrad u x 0 + t * dpart_appA φ 0 x) ^ 2 ∂haar 1
noncomputable def EE (t : ℝ) : ℝ :=
  ∫ x, (u x + t * φ x) ^ 2 * Real.log ((u x + t * φ x) ^ 2) ∂haar 1

noncomputable def eC : Torus 1 → ℝ := gCos
noncomputable def eS : Torus 1 → ℝ := sCos
noncomputable def eP : Torus 1 → ℝ := fun x => gCos x ^ 2
noncomputable def eQ : Torus 1 → ℝ := fun x => sCos x * gCos x

/-- The real gap of the competitor density, as an explicit function of `t`. -/
noncomputable def GG (t : ℝ) : ℝ :=
  EE u φ t / NN u φ t - Real.log (NN u φ t) +
    ((MM u φ eC t / NN u φ t) ^ 2 + (MM u φ eS t / NN u φ t) ^ 2) / 2

/-- The upper bound for `realDiss - 2 R realGap` of the competitor density. -/
noncomputable def Fb (t : ℝ) : ℝ :=
  4 * (Wd u φ t / NN u φ t) - 2 * realRate * (EE u φ t / NN u φ t - Real.log (NN u φ t)) +
    interaction (MM u φ eC t / NN u φ t) (MM u φ eS t / NN u φ t) (MM u φ eP t / NN u φ t)
      (MM u φ eQ t / NN u φ t)

end Profile

section Calculus

variable {u φ : Torus 1 → ℝ}

theorem MM_hasDerivAt_zero {e : Torus 1 → ℝ} (he : BM e) (hu : BM u) (hφ : BM φ)
    (hB : ∫ x, e x * (u x * φ x) ∂haar 1 = 0) :
    HasDerivAt (MM u φ e) 0 0 ∧ MM u φ e 0 = ∫ x, e x * u x ^ 2 ∂haar 1 := by
  have hfun : MM u φ e = fun t => (∫ x, e x * u x ^ 2 ∂haar 1) +
      t ^ 2 * (∫ x, e x * φ x ^ 2 ∂haar 1) := by
    funext t
    unfold MM
    rw [integral_quad he hu hφ t, hB]; ring
  refine ⟨?_, ?_⟩
  · rw [hfun]
    have := ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (∫ x, e x * φ x ^ 2 ∂haar 1)).const_add
      (∫ x, e x * u x ^ 2 ∂haar 1)
    simpa using this
  · rw [hfun]; simp

theorem Wd_hasDerivAt_zero (hg : MemLp (fun x => weakGrad u x 0) 2 (haar 1)) (hφ' : BM (dpart_appA φ 0)) :
    HasDerivAt (Wd u φ) (2 * ∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1) 0 ∧
      Wd u φ 0 = ∫ x, weakGrad u x 0 ^ 2 ∂haar 1 := by
  have i1 : Integrable (fun x => weakGrad u x 0 ^ 2) (haar 1) := hg.integrable_sq
  have i2 : Integrable (fun x => weakGrad u x 0 * dpart_appA φ 0 x) (haar 1) := by
    obtain ⟨C, hC⟩ := hφ'.bdd
    exact (hg.integrable one_le_two).mul_bdd hφ'.meas.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have i3 : Integrable (fun x => dpart_appA φ 0 x ^ 2) (haar 1) := hφ'.sq.integrable
  have hfun : Wd u φ = fun t => (∫ x, weakGrad u x 0 ^ 2 ∂haar 1) +
      2 * t * (∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1) +
        t ^ 2 * (∫ x, dpart_appA φ 0 x ^ 2 ∂haar 1) := by
    funext t
    unfold Wd
    have : ∀ x, (weakGrad u x 0 + t * dpart_appA φ 0 x) ^ 2 =
        weakGrad u x 0 ^ 2 + (2 * t) * (weakGrad u x 0 * dpart_appA φ 0 x) +
          t ^ 2 * dpart_appA φ 0 x ^ 2 := fun x => by ring
    simp_rw [this]
    have h12 : Integrable (fun x => weakGrad u x 0 ^ 2 +
        (2 * t) * (weakGrad u x 0 * dpart_appA φ 0 x)) (haar 1) := i1.add (i2.const_mul _)
    rw [integral_add h12 (i3.const_mul _), integral_add i1 (i2.const_mul _),
      integral_const_mul, integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [hfun]
    have h1 := ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
      (∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1)
    have h2 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const (∫ x, dpart_appA φ 0 x ^ 2 ∂haar 1)
    have := (h1.const_add (∫ x, weakGrad u x 0 ^ 2 ∂haar 1)).add h2
    convert this using 1
    · funext t; simp
    · simp
  · rw [hfun]; simp



theorem BM.mul_log_sq {f : Torus 1 → ℝ} (hf : BM f) : BM (fun x => f x * Real.log (f x ^ 2)) := by
  obtain ⟨C, hC⟩ := hf.bdd
  refine ⟨hf.meas.mul (Real.measurable_log.comp (hf.meas.pow_const 2)), ⟨2 + (max 1 C) ^ 2 * Real.log ((max 1 C) ^ 2), fun x => ?_⟩⟩
  exact abs_mul_log_sq_le ((hC x).trans (le_max_right _ _)) (le_max_left _ _)

theorem EE_hasDerivAt_zero (hu : BM u) (hφ : BM φ) (h0 : ∫ x, u x * φ x ∂haar 1 = 0) :
    HasDerivAt (EE u φ) (2 * ∫ x, u x * φ x * Real.log (u x ^ 2) ∂haar 1) 0 ∧
      EE u φ 0 = ∫ x, u x ^ 2 * Real.log (u x ^ 2) ∂haar 1 := by
  obtain ⟨K, hK⟩ := hu.bdd
  obtain ⟨L, hL⟩ := hφ.bdd
  refine ⟨?_, by simp [EE]⟩
  have h := hasDerivAt_integral_sq_log_sq hu.meas hφ.meas hK hL 0
  have e : ∫ x, 2 * (u x + 0 * φ x) * φ x * (Real.log ((u x + 0 * φ x) ^ 2) + 1) ∂haar 1 =
      2 * ∫ x, u x * φ x * Real.log (u x ^ 2) ∂haar 1 := by
    have i1 : Integrable (fun x => u x * φ x * Real.log (u x ^ 2)) (haar 1) := by
      have := (hφ.mul hu.mul_log_sq).integrable
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only; ring
    have i2 : Integrable (fun x => u x * φ x) (haar 1) := (hu.mul hφ).integrable
    have : ∀ x, 2 * (u x + 0 * φ x) * φ x * (Real.log ((u x + 0 * φ x) ^ 2) + 1) =
        2 * (u x * φ x * Real.log (u x ^ 2)) + 2 * (u x * φ x) := fun x => by ring_nf
    simp_rw [this]
    rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul, h0]
    ring
  rw [e] at h
  exact h

theorem NN_facts (hu : BM u) (hφ : BM φ) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1)
    (h0 : ∫ x, 1 * (u x * φ x) ∂haar 1 = 0) :
    HasDerivAt (NN u φ) 0 0 ∧ NN u φ 0 = 1 := by
  obtain ⟨h1, h2⟩ := MM_hasDerivAt_zero (e := fun _ => 1) (BM.const 1) hu hφ h0
  refine ⟨h1, ?_⟩
  unfold NN
  rw [h2]; simpa using hmass


/-- The orthogonality hypotheses: `∫ e_j u φ = 0` for the five test functions. -/
structure Orth (u φ : Torus 1 → ℝ) : Prop where
  o0 : ∫ x, 1 * (u x * φ x) ∂haar 1 = 0
  oC : ∫ x, eC x * (u x * φ x) ∂haar 1 = 0
  oS : ∫ x, eS x * (u x * φ x) ∂haar 1 = 0
  oP : ∫ x, eP x * (u x * φ x) ∂haar 1 = 0
  oQ : ∫ x, eQ x * (u x * φ x) ∂haar 1 = 0

theorem BM.eC : BM eC := BM.gCos
theorem BM.eS : BM eS := BM.sCos
theorem BM.eP : BM eP := BM.gCos.sq
theorem BM.eQ : BM eQ := BM.sCos.mul BM.gCos

/-- Derivative of the profile at `0`. -/
theorem Fb_hasDerivAt (hu : BM u) (hφ : BM φ) (hmass : ∫ x, u x ^ 2 ∂haar 1 = 1)
    (hg : MemLp (fun x => weakGrad u x 0) 2 (haar 1)) (hφ' : BM (dpart_appA φ 0))
    (ho : Orth u φ) :
    HasDerivAt (Fb u φ)
      (8 * (∫ x, weakGrad u x 0 * dpart_appA φ 0 x ∂haar 1) -
        4 * realRate * ∫ x, u x * φ x * Real.log (u x ^ 2) ∂haar 1) 0 := by
  have hu0 : ∫ x, u x * φ x ∂haar 1 = 0 := by simpa using ho.o0
  obtain ⟨hN, hN0⟩ := NN_facts hu hφ hmass ho.o0
  obtain ⟨hW, hW0⟩ := Wd_hasDerivAt_zero (u := u) (φ := φ) hg hφ'
  obtain ⟨hE, hE0⟩ := EE_hasDerivAt_zero hu hφ hu0
  obtain ⟨hMC, _⟩ := MM_hasDerivAt_zero BM.eC hu hφ ho.oC
  obtain ⟨hMS, _⟩ := MM_hasDerivAt_zero BM.eS hu hφ ho.oS
  obtain ⟨hMP, _⟩ := MM_hasDerivAt_zero BM.eP hu hφ ho.oP
  obtain ⟨hMQ, _⟩ := MM_hasDerivAt_zero BM.eQ hu hφ ho.oQ
  have hN1 : NN u φ 0 ≠ 0 := by rw [hN0]; exact one_ne_zero
  have hdiv : ∀ {M : ℝ → ℝ}, HasDerivAt M 0 0 → HasDerivAt (fun t => M t / NN u φ t) 0 0 := by
    intro M hM
    have := hM.div hN hN1
    convert this using 1
    simp
  have hC := hdiv hMC
  have hS := hdiv hMS
  have hP := hdiv hMP
  have hQ := hdiv hMQ
  have hI : HasDerivAt (fun t => interaction (MM u φ eC t / NN u φ t) (MM u φ eS t / NN u φ t)
      (MM u φ eP t / NN u φ t) (MM u φ eQ t / NN u φ t)) 0 0 := by
    have := (((hC.pow 2).add (hS.pow 2)).const_mul (2 * aCos - realRate)).add
      (((((hS.pow 2).mul hP).sub (((hC.const_mul 2).mul hS).mul hQ)).add
        ((hC.pow 2).mul (hP.const_sub 1))).const_mul aCos)
    convert this using 1
    · funext t; simp [interaction]
    · simp
  have hT1 := (hW.div hN hN1).const_mul 4
  have hT2 := ((hE.div hN hN1).sub (hN.log hN1)).const_mul (2 * realRate)
  have hF := (hT1.sub hT2).add hI
  convert hF using 1
  · funext t; simp [Fb]
  · rw [hN0, hW0, hE0]
    simp
    ring

end Calculus

end SharpLSI.FL.Prop82
