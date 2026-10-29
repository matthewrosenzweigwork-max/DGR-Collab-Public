import FullLabeledLSI.Paper.Prop23Defs
import FullLabeledLSI.Defs.F05_FiniteRank
import SharpSymmetricLSI.Statements.R31_Force_Approximation

/-!
# Proposition 2.3, WP-D: replacing `U_N` by `U_{N,R}` (SKELETON: statements with proof sketches)

Manuscript lines 1000-1010 (`eq:energy-root-error`, and the sentence after it).  Everything is
`N`-indexed, `N ≥ 1` wherever a ground-state transform `psiG` or a division by `N` occurs, and the
reference measure is `QN μ N = μ^{⊗N}` (`Prop23Defs.lean`).  Notation: `U_N = Ucentered W μ N`,
`U_{N,R} = URN A R N` (F05), `P_N = gibbs V W N`, `Ψ = psiG W μ N f`.

## Contents (dependency order)

* `shEn μ Ψ U = ∫⁻ ofReal (∑ᵢ ∑ₖ (∂ᵢₖΨ + ½ Ψ ∂ᵢₖU)²) dQ_N`: the "shifted energy".  WP-B
  (`energy_ground_identity`) says `energy V W N f = shEn μ (psiG W μ N f) (Ucentered W μ N)`; if
  WP-B's right-hand side is written with exactly the integrand above, this is `rfl` (the `ofReal`
  is applied to the whole double sum, as in the plan); otherwise a one-line `simp`/`congr`.
* **D(a)** `URN_eq_Ukernel` (algebra, no hypotheses, all `N` including `0`), then `TR`, `gradURN`
  (the explicit gradient of `U_{N,R}`), `isWeakGrad_URN`, `weakGradC_URN_ae`, `hasWeakGrad_URN`.
* **D(b)** `shEn_rpow_half_le` (Minkowski), `force_error_eventually` (R31), `energy_replace`.
* **D(c)** `holder_sq_mul` (Hölder), `entropy_terms_replace` (uses S23(1), S23(2), `K_N → K_∞`
  as HYPOTHESES).

## Conventions and design decisions

* `A : FiniteRankApprox W μ e` has `μ : Measure (Torus d)`; in the statements that need the
  minimizer, `μ : ProbabilityMeasure (Torus d)` and `A : FiniteRankApprox W (μ : Measure _) e`
  (as in S23).
* `e` is the given eigenbasis (only a weak gradient); `eC` is a `C¹` representative
  (`exists_c1_reps`, ForceApprox4:26, gives `∀ j, ContDiff ℝ 1 (eC j ∘ liftT) ∧ eC j =ᵐ[haar d] e j
  ∧ eC j =ᵐ[μ] e j`).  `URN` is built from `e` (F05), and its classical gradient `gradURN` from
  `eC`; they agree a.e. (`isWeakGrad_URN`).
* No `hd`/`hr`/`hyp`/`hμ` is assumed where it is not used.

## Doubts / corrections to the plan (see also the final report)

1. The plan's (b) says "roots differ by `(B/2)(∫|∇(U_N-U_{N,R})|² dP_N)^{1/2}`".  This is true
   exactly as stated (Minkowski in `L²(Q_N;ℝ^{N×d})` and `Ψ² dQ_N = f² dP_N ≤ B² dP_N`).  We state
   it in `ℝ≥0∞` with `rpow (1/2)` so that no finiteness hypothesis is needed (`shEn_rpow_half_le`).
2. `Ent`/`log K_N` replacement: the plan's wording "`K_N → K_∞`, `κ_R → K_∞`" is encoded as the
   hypotheses `hKN`, `hκ`, `hK0` of `entropy_terms_replace` (the callers supply them from
   `gaussian_limit_law` (R27, first two conjuncts) and `rank_errors` (S23, 2nd conjunct)).
3. `entropy_terms_replace` is stated for the *difference* `∫Ψ²(U_N - U_{N,R})`, not for the two
   integrals separately: separately they need integrability of `Ψ² U_N` and `Ψ² U_{N,R}`
   (true for bounded `U_N` and `μ`-a.e. bounded `URN`, but irrelevant for the Hölder estimate).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

variable {d : ℕ}

/-! ### The shifted energy -/

/-- `shEn μ Ψ U = ∫ |∇Ψ + ½ Ψ ∇U|² dQ_N` (as an `ℝ≥0∞`-valued lower integral; `weakGradC` is the
chosen weak gradient, junk `0` if none exists, so every use must assume `HasWeakGrad`). -/
noncomputable def shEn (μ : Measure (Torus d)) {N : ℕ} (Ψ U : Config N d → ℝ) : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (∑ i, ∑ k, (weakGradC Ψ X i k + (1 / 2) * Ψ X * weakGradC U X i k) ^ 2)
    ∂QN μ N

section DA

variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}

/-- `(T_R z)_i = ∑_{j ∈ s_R} a^R_{ij} z_j` (Lean index `i` = manuscript mode `i+1`). -/
noncomputable def TR (A : FiniteRankApprox W μ e) (R : ℕ) (z : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ A.s R, A.a R i j * z j

/-- The classical gradient of `U_{N,R} = u_R(Z_N)`:
`∇_l U_{N,R}(X) = N^{-1/2} ∑_{i ∈ s_R} (T_R Z_N)_i ∇e_{i+1}(X_l)`, where `Z_N = fluct eC N` and
`∇e_{i+1}` is the classical gradient `cgrad` of the `C¹` representative `eC (i+1)`. -/
noncomputable def gradURN (A : FiniteRankApprox W μ e) (eC : ℕ → Torus d → ℝ) (R N : ℕ)
    (X : Config N d) (l : Fin N) (k : Fin d) : ℝ :=
  (N : ℝ) ^ (-(1 / 2 : ℝ)) *
    ∑ i ∈ A.s R, TR A R (fun n => fluct eC N n X) i * cgrad (eC (i + 1)) (X l) k

/-- `(N^{-1/2})² = N⁻¹` (also for `N = 0`, where both sides are `0`). -/
theorem prop23_rpow_half_mul_self (N : ℕ) : ((N : ℝ) ^ (-(1 / 2 : ℝ))) * ((N : ℝ) ^ (-(1 / 2 : ℝ))) = (N : ℝ)⁻¹ := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · rw [← Real.rpow_add (by exact_mod_cast h)]; norm_num [Real.rpow_neg_one]

/-- Reordering a four-fold finite sum `∑ a ∑ b ∑ c ∑ d = ∑ c ∑ d ∑ a ∑ b`. -/
theorem prop23_sum4_comm {α β γ δ : Type*} (s1 : Finset α) (s2 : Finset β) (s3 : Finset γ) (s4 : Finset δ)
    (H : α → β → γ → δ → ℝ) :
    ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, H a b c d =
      ∑ c ∈ s3, ∑ d ∈ s4, ∑ a ∈ s1, ∑ b ∈ s2, H a b c d := by
  calc ∑ a ∈ s1, ∑ b ∈ s2, ∑ c ∈ s3, ∑ d ∈ s4, H a b c d
      = ∑ a ∈ s1, ∑ c ∈ s3, ∑ b ∈ s2, ∑ d ∈ s4, H a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a ∈ s1, ∑ c ∈ s3, ∑ d ∈ s4, ∑ b ∈ s2, H a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c ∈ s3, ∑ a ∈ s1, ∑ d ∈ s4, ∑ b ∈ s2, H a b c d := Finset.sum_comm
    _ = ∑ c ∈ s3, ∑ d ∈ s4, ∑ a ∈ s1, ∑ b ∈ s2, H a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- **D(a).  `U_{N,R} = Ukernel(K_R)`** (plan item D(a)), `K_R(x,y) = ∑_{i,j∈s_R} a_{ij} e_{i+1}(x)
e_{j+1}(y)`.  True for every `N` (for `N = 0` both sides are `0`).

Proof (PROVED below, about 25 lines): unfold `URN, uR, fluct, Ukernel`; `Z_i Z_j = N^{-1} ∑_l ∑_m e_{i+1}(X_l)
e_{j+1}(X_m)` from `(N:ℝ)^(-1/2) * (N:ℝ)^(-1/2) = (N:ℝ)⁻¹` (`Real.rpow_add` for `N > 0`,
`Real.zero_rpow` for `N = 0`, or `← Real.rpow_add`/`Real.rpow_neg_one`), then
`Finset.mul_sum`, `Finset.sum_comm` to move `∑_{i,j∈s}` inside `∑_l ∑_m`. -/
theorem URN_eq_Ukernel (A : FiniteRankApprox W μ e) (R N : ℕ) (X : Config N d) :
    URN A R N X =
      Ukernel (fun x y => ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * e (i + 1) x * e (j + 1) y) N X := by
  unfold URN uR Ukernel fluct
  set c : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ)) with hc
  have hN := prop23_rpow_half_mul_self N
  rw [← hc] at hN
  have key : ∀ i j, A.a R i j * (c * ∑ l, e (i + 1) (X l)) * (c * ∑ m, e (j + 1) (X m)) =
      (N : ℝ)⁻¹ * ∑ l, ∑ m, A.a R i j * e (i + 1) (X l) * e (j + 1) (X m) := by
    intro i j
    have : ∑ l, ∑ m, A.a R i j * e (i + 1) (X l) * e (j + 1) (X m) =
        A.a R i j * ((∑ l, e (i + 1) (X l)) * ∑ m, e (j + 1) (X m)) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [this, ← hN]; ring
  simp_rw [key]
  have e1 : ∀ x : ℝ, 1 / (2 * (N : ℝ)) * x = 1 / 2 * ((N : ℝ)⁻¹ * x) := by
    intro x; rw [one_div, one_div, mul_inv]; ring
  rw [e1]
  congr 1
  simp only [Finset.mul_sum]
  exact prop23_sum4_comm (A.s R) (A.s R) Finset.univ Finset.univ
    (fun i j l m => (N : ℝ)⁻¹ * (A.a R i j * e (i + 1) (X l) * e (j + 1) (X m)))

/-- **D(a'), the weak gradient of `U_{N,R}`.**  No minimizer hypotheses: only `C¹` representatives
`eC` of the `e_j` (Haar-a.e. equal).  `y ↦ URN A R N (unflat y)` lives on `𝕋^{N×d}`.

Proof (about 40 lines): `isWeakGrad_Ukernel_finKer` (ForceApprox2:115; with `φ := fun i => eC (i+1)`,
`s := A.s R`, `a := A.a R`, symmetry `A.symm R`) gives the weak gradient
`(N⁻¹) ∑_b finKerD … (projBlock p.1 y) (projBlock b y) p.2` of `UkernelF (finKer φ s a) N ∘ unflat`;
`Ukernel_ae_finKer` (ForceApprox4:41, with `hK` from the definition of `URN_eq_Ukernel`) says
`UkernelF K_R N ∘ unflat =ᵐ UkernelF (finKer …) N ∘ unflat`; transfer with `IsWeakGrad.congr_ae`
(R37Particle:71).  Finally the gradient formulas agree *pointwise* (algebra,
`N^{-1/2} · N^{-1/2} = N⁻¹`, `Finset.sum_comm`): `finKerD … (X c) (X b) k = ∑_{ij} a_ij ∇e_i(X_c)_k e_j(X_b)`
and `∑_b e_j(X_b) = N^{1/2} fluct eC N j X`. -/
theorem isWeakGrad_URN (A : FiniteRankApprox W μ e) {eC : ℕ → Torus d → ℝ}
    (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT)) (heC : ∀ j, eC j =ᵐ[haar d] e j) (R : ℕ) {N : ℕ}
    (hN : 1 ≤ N) :
    IsWeakGrad (fun y : UnitAddTorus (Fin N × Fin d) => URN A R N (unflat y))
      (fun y p => gradURN A eC R N (unflat y) p.1 p.2) := by
  have hφ' : ∀ i, ContDiff ℝ 1 ((fun i => eC (i + 1)) i ∘ liftT) := fun i => hφ (i + 1)
  have h1 := SharpLSI.isWeakGrad_Ukernel_finKer (φ := fun i => eC (i + 1)) hφ' (A.s R)
    (a := A.a R) (A.symm R) (N := N) hN
  have h2 := SharpLSI.Ukernel_ae_finKer (e := e) (eC := eC) heC (A.s R) (A.a R)
    (KR := fun x y => ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * e (i + 1) x * e (j + 1) y)
    (fun x y => rfl) N
  have h3 := h1.congr_ae h2.symm
  have h4 : (fun y : UnitAddTorus (Fin N × Fin d) => URN A R N (unflat y)) =
      fun y => SharpLSI.UkernelF (fun x y => ∑ i ∈ A.s R, ∑ j ∈ A.s R,
        A.a R i j * e (i + 1) x * e (j + 1) y) N (unflat y) := by
    funext y; exact URN_eq_Ukernel A R N (unflat y)
  rw [h4]
  convert h3 using 1
  funext y p
  obtain ⟨c, k⟩ := p
  simp only [gradURN, TR, SharpLSI.finKerD, fluct]
  set cc : ℝ := (N : ℝ) ^ (-(1 / 2 : ℝ)) with hcc
  have hN2 := prop23_rpow_half_mul_self N
  rw [← hcc] at hN2
  show cc * _ = (N : ℝ)⁻¹ * _
  rw [← hN2]
  have hR : ∀ i j, ∑ b : Fin N, A.a R i j * cgrad (eC (i + 1)) (projBlock c y) k *
      eC (j + 1) (projBlock b y) =
      A.a R i j * cgrad (eC (i + 1)) (unflat y c) k * ∑ l : Fin N, eC (j + 1) (unflat y l) := by
    intro i j; rw [Finset.mul_sum]; rfl
  have hR2 : ∑ b : Fin N, ∑ x ∈ A.s R, ∑ x_1 ∈ A.s R, A.a R x x_1 *
      cgrad (eC (x + 1)) (projBlock c y) k * eC (x_1 + 1) (projBlock b y) =
      ∑ i ∈ A.s R, ∑ j ∈ A.s R, A.a R i j * cgrad (eC (i + 1)) (unflat y c) k *
        ∑ l : Fin N, eC (j + 1) (unflat y l) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hR i j
  rw [hR2, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **D(a'')**: `weakGradC (URN A R N) = gradURN` `Q_N`-a.e. (needs only `μ ≪ Haar`).

Proof (about 15 lines): `weakGrad_ae_eq (isWeakGrad_URN …)` (EntFinite:112) a.e. `volume`, then
`ae_pi_of_ae_volume` (GroundT5:45; its proof only uses `pi_ac_volume hac N`, ForceExp:22) and
`unfold weakGradC`. -/
theorem weakGradC_URN_ae [IsProbabilityMeasure μ] (hac : μ ≪ haar d) (A : FiniteRankApprox W μ e)
    {eC : ℕ → Torus d → ℝ} (hφ : ∀ j, ContDiff ℝ 1 (eC j ∘ liftT))
    (heC : ∀ j, eC j =ᵐ[haar d] e j) (R : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ X ∂QN μ N, ∀ (l : Fin N) (k : Fin d),
      weakGradC (URN A R N) X l k = gradURN A eC R N X l k := by
  have h := SharpLSI.weakGrad_ae_eq (isWeakGrad_URN A hφ heC R hN)
  have hmp : MeasureTheory.MeasurePreserving
      (flat : Config N d → UnitAddTorus (Fin N × Fin d)) volume volume :=
    ⟨measurable_flat, map_flat_volume N⟩
  have h' := (SharpLSI.pi_ac_volume hac N).ae_le (hmp.quasiMeasurePreserving.ae h)
  unfold QN
  filter_upwards [h'] with X hX l k
  exact congrFun hX (l, k)

end DA

end SharpLSI.FL
