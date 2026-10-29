import FullLabeledLSI.Paper.HybridLSIAltC

/-!
# Hybrid tilted log-Sobolev inequality (alternative route), part D: the hybrid instance on the flat
# Gaussian space

* `Xf`, `Yf`: the factorisation `polyB e c B (x, y) = ∑_j c_j X_j(x) Y_j(reshape y)`;
* temperate growth of `Yf` and of the tilt exponent `uT`; `C¹` of `Xf`;
* `hgl_hybrid`: the Gaussian log-Sobolev hypothesis of `core_lsi`, from `gauss_lsi_smooth`,
  `tilted_law` and `Sig_le_mobility`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal ContDiff

noncomputable section

namespace SharpLSI.FL.HLA

open SharpLSI SharpLSI.FL.Gross

variable {d N J : ℕ}

/-- The torus factor `∏_{i ∈ B} e_{j_i}(x_i)`. -/
def Xf (e : ℕ → Torus d → ℝ) (B : Finset (Fin N)) (j : Fin N → Fin (J + 1)) (x : Config N d) : ℝ :=
  ∏ i, (if i ∈ B then e (j i) (x i) else 1)

/-- The Gaussian factor of label `i`. -/
def yfac (B : Finset (Fin N)) (j : Fin N → Fin (J + 1)) (i : Fin N) (g : Fin (N * J) → ℝ) : ℝ :=
  if i ∈ B then 1 else if h : (j i : ℕ) = 0 then 1
  else g (finProdFinEquiv (i, ⟨(j i : ℕ) - 1, by omega⟩))

/-- The Gaussian factor `∏_{i ∉ B} y_{i, j_i}` on the flat Gaussian space. -/
def Yf (B : Finset (Fin N)) (j : Fin N → Fin (J + 1)) (g : Fin (N * J) → ℝ) : ℝ :=
  ∏ i, yfac B j i g

theorem tg_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ}
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (fun x => f x * g x).HasTemperateGrowth :=
  Function.HasTemperateGrowth.mul hf hg

theorem tg_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ) :
    (fun _ : E => a).HasTemperateGrowth := Function.HasTemperateGrowth.const a

theorem tg_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) {f : ι → E → ℝ} (h : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x => ∑ i ∈ s, f i x).HasTemperateGrowth :=
  Function.HasTemperateGrowth.sum h

theorem tg_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) {f : ι → E → ℝ} (h : ∀ i ∈ s, (f i).HasTemperateGrowth) :
    (fun x => ∏ i ∈ s, f i x).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact tg_const (E := E) (1 : ℝ)
  | insert a s ha ih =>
    have h1 := tg_mul (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.prod_insert ha] using h1

theorem tg_yfac (B : Finset (Fin N)) (j : Fin N → Fin (J + 1)) (i : Fin N) :
    (yfac B j i).HasTemperateGrowth := by
  unfold yfac
  split_ifs with h1 h2
  · exact Function.HasTemperateGrowth.const 1
  · exact Function.HasTemperateGrowth.const 1
  · exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (N * J) => ℝ)
      (finProdFinEquiv (i, ⟨(j i : ℕ) - 1, by omega⟩))).hasTemperateGrowth

theorem tg_Yf (B : Finset (Fin N)) (j : Fin N → Fin (J + 1)) : (Yf B j).HasTemperateGrowth :=
  tg_prod _ fun i _ => tg_yfac B j i

theorem C1C_Xf {e : ℕ → Torus d → ℝ} (hC1 : ∀ m, C1T (e m)) (B : Finset (Fin N))
    (j : Fin N → Fin (J + 1)) : C1C (Xf e B j) := by
  unfold Xf
  refine C1C.prod _ fun i _ => ?_
  split_ifs
  · exact C1C.eval (hC1 _) i
  · show ContDiff ℝ 1 _
    exact contDiff_const

theorem tg_proj {M : ℕ} (a : Fin M) : (fun y : Fin M → ℝ => y a).HasTemperateGrowth :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin M => ℝ) a).hasTemperateGrowth

theorem tg_quad {M : ℕ} (X : Matrix (Fin M) (Fin M) ℝ) :
    (fun y : Fin M → ℝ => (y ⬝ᵥ (X *ᵥ y)) / 2).HasTemperateGrowth := by
  have h1 : (fun y : Fin M → ℝ => ∑ a, y a * ∑ b, X a b * y b).HasTemperateGrowth := by
    refine tg_sum _ fun a _ => tg_mul (tg_proj a) (tg_sum _ fun b _ => ?_)
    exact tg_mul (tg_const (X a b)) (tg_proj b)
  have h2 := tg_mul (tg_const (E := Fin M → ℝ) (1 / 2 : ℝ)) h1
  convert h2 using 1
  funext y
  simp only [dotProduct, mulVec]
  ring


/-! ### The polynomial `polyB` on the hybrid space -/

theorem polyB_eq (e : ℕ → Torus d → ℝ) (c : (Fin N → Fin (J + 1)) → ℝ) (B : Finset (Fin N))
    (x : Config N d) (y : Fin N → Fin J → ℝ) :
    polyB e c B (x, y) = aF c (fun j => Yf B j) (fun j => Xf e B j) x (reshape N J y) := by
  unfold polyB aF
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : ∏ i, hybFactor e B i (j i) (x, y) =
      Yf B j (reshape N J y) * Xf e B j x := by
    unfold Yf Xf
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold hybFactor yfac
    by_cases hi : i ∈ B
    · simp [hi]
    · by_cases h0 : (j i : ℕ) = 0
      · simp [hi, h0]
      · simp [hi, h0, reshape_apply]
  rw [h]; ring

/-! ### The Gaussian hypothesis of the core inequality -/

section gauss
variable {W : Torus d → Torus d → ℝ} {μ : Measure (Torus d)} {e : ℕ → Torus d → ℝ}
  (A : FiniteRankApprox W μ e) {R : ℕ} {B : Finset (Fin N)}

theorem tg_uT (hJ : ∀ i ∈ A.s R, i < J) :
    (uT A R J B).HasTemperateGrowth := by
  have h := tg_quad ((Gcm J B)ᵀ * Tm A R J * Gcm J B)
  have : uT A R J B = fun y => (y ⬝ᵥ (((Gcm J B)ᵀ * Tm A R J * Gcm J B) *ᵥ y)) / 2 := by
    funext y; exact uT_eq hJ y
  rw [this]; exact h

theorem tPt_eq (A : FiniteRankApprox W μ e) :
    tPt (uT A R J B) (kappaR A R) = Pt A R J B := rfl

variable {A} (hJ : ∀ i ∈ A.s R, i < J) {σ : ℝ} (hσ : 0 < σ) (hpos : PosTm A R J σ)
  (hB : B.card < N) {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (A.a R) C)
  [IsProbabilityMeasure μ] {lam : ℕ → ℝ} (he : IsRefEigenbasis μ e lam)
  (hrl : rLS μ ≤ ENNReal.ofReal (lam 1))

include hJ hσ hpos hB hC he hrl in
/-- The Gaussian log-Sobolev inequality for the tilted block, in the form used by `core_lsi`. -/
theorem hgl_hybrid (f : (Fin (N * J) → ℝ) → ℝ) (hf : ContDiff ℝ ∞ f)
    (hL2 : MemLp f 2 (tPt (uT A R J B) (kappaR A R)))
    (hE : Integrable (fun g => Eyy (fun k : Fin (N * J) => lam ((flatMode k : ℕ) + 1)) f g)
      (tPt (uT A R J B) (kappaR A R))) :
    ENNReal.ofReal ((bRate μ lam C).toReal / 2) * ent (tPt (uT A R J B) (kappaR A R))
        (fun g => f g ^ 2) ≤
      ENNReal.ofReal (∫ g, Eyy (fun k : Fin (N * J) => lam ((flatMode k : ℕ) + 1)) f g
        ∂tPt (uT A R J B) (kappaR A R)) := by
  rw [tPt_eq]
  rw [tPt_eq] at hL2 hE
  have hlaw := tilted_law hJ hσ hpos hB hC
  have hS := Smat_posSemidef hB (CJ_transpose A hJ hC) (CJ_quad_nonneg A hJ hC hσ hpos)
  rw [hlaw] at hL2 hE ⊢
  exact gauss_lsi_smooth hS ENNReal.toReal_nonneg
    (fun v => Sig_le_mobility he hrl hB C v) hf hL2 hE

end gauss

end SharpLSI.FL.HLA

end
