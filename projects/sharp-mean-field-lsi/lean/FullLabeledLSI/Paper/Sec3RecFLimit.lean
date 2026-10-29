import FullLabeledLSI.Paper.Sec3RecFisher3
import FullLabeledLSI.Paper.Sec3RecComb
import FullLabeledLSI.Paper.Sec3RecAssign
import FullLabeledLSI.Paper.Sec3RecLimit
import FullLabeledLSI.Paper.Sec3RecLimit2

/-!
# Proposition 3.2: the Fisher information of the nonidentical products in terms of group sizes
-/

noncomputable section
open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal

namespace SharpLSI.FL

open SharpLSI

variable {d : ℕ} {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ} {q : ℕ}

def FA2 (V : Torus d → ℝ) (ρ : Fin q → Torus d → ℝ) (s : Fin q) (k : Fin d) : ℝ :=
  ∫ x, aGrad V (ρ s) x k ^ 2 ∂densMeasure (ρ s)

def FM (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Fin q → Torus d → ℝ) (s t : Fin q)
    (k : Fin d) : ℝ :=
  ∫ x, aGrad V (ρ s) x k * mForce W (densMeasure (ρ t)) x k ∂densMeasure (ρ s)

def FQ (W : Torus d → Torus d → ℝ) (ρ : Fin q → Torus d → ℝ) (s t : Fin q) (k : Fin d) : ℝ :=
  ∫ x, ∫ y, bGrad W x y k ^ 2 ∂densMeasure (ρ t) ∂densMeasure (ρ s)

def FR (W : Torus d → Torus d → ℝ) (ρ : Fin q → Torus d → ℝ) (s t u : Fin q) (k : Fin d) : ℝ :=
  ∫ x, mForce W (densMeasure (ρ t)) x k * mForce W (densMeasure (ρ u)) x k ∂densMeasure (ρ s)

/-- The per-label value of the Fisher information, in terms of the group sizes `n`. -/
def tauN (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Fin q → Torus d → ℝ) (N : ℕ)
    (n : Fin q → ℕ) (k : Fin d) (s : Fin q) : ℝ :=
  FA2 V ρ s k + 2 * (1 / (N : ℝ)) * ∑ t, ((n t : ℝ) - if s = t then 1 else 0) * FM V W ρ s t k +
    (1 / (N : ℝ)) ^ 2 * ∑ t, ((n t : ℝ) - if s = t then 1 else 0) * FQ W ρ s t k +
    (1 / (N : ℝ)) ^ 2 * (∑ t, ∑ u, ((n t : ℝ) - if s = t then 1 else 0) *
      ((n u : ℝ) - if s = u then 1 else 0) * FR W ρ s t u k -
      ∑ t, ((n t : ℝ) - if s = t then 1 else 0) * FR W ρ s t t k)

theorem fisher_counts (hyp : Hyp V W KV KW) {N : ℕ} (hN : 1 ≤ N) (ρ : Fin q → Torus d → ℝ)
    (hρ : ∀ s, IsSmoothT (ρ s) ∧ (∀ x, 0 < ρ s x) ∧ ∫ x, ρ s x ∂haar d = 1)
    (a : Fin N → Fin q) (n : Fin q → ℕ)
    (hfib : ∀ s, (Finset.univ.filter fun i => a i = s).card = n s) :
    fisherInfoC (Measure.pi fun i : Fin N => densMeasure (ρ (a i))) (gibbs V W N) ≠ ⊤ ∧
    (fisherInfoC (Measure.pi fun i : Fin N => densMeasure (ρ (a i))) (gibbs V W N)).toReal / N =
      ∑ k : Fin d, (1 / (N : ℝ)) * ∑ s, (n s : ℝ) * tauN V W ρ N n k s := by
  obtain ⟨hne, hval⟩ := product_fisher_gen hyp hN ρ hρ a
  refine ⟨hne, ?_⟩
  rw [hval]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have hterm : ∀ i : Fin N, (∫ x, aGrad V (ρ (a i)) x k ^ 2 ∂densMeasure (ρ (a i)))
        + 2 * (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
            ∫ x, aGrad V (ρ (a i)) x k * mForce W (densMeasure (ρ (a j))) x k ∂densMeasure (ρ (a i))
        + (1 / (N : ℝ)) ^ 2 * ∑ j ∈ Finset.univ.erase i,
            ∫ x, ∫ y, bGrad W x y k ^ 2 ∂densMeasure (ρ (a j)) ∂densMeasure (ρ (a i))
        + (1 / (N : ℝ)) ^ 2 * ∑ j ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase j,
            ∫ x, mForce W (densMeasure (ρ (a j))) x k * mForce W (densMeasure (ρ (a l))) x k
              ∂densMeasure (ρ (a i)) = tauN V W ρ N n k (a i) := fun i => by
    have c2 := card_erase_fiber a n hfib i
    have e1 : ∑ j ∈ Finset.univ.erase i,
        ∫ x, aGrad V (ρ (a i)) x k * mForce W (densMeasure (ρ (a j))) x k ∂densMeasure (ρ (a i)) =
        ∑ t, ((n t : ℝ) - if a i = t then 1 else 0) * FM V W ρ (a i) t k := by
      have := sum_fiber_finset (Finset.univ.erase i) a (fun t => FM V W ρ (a i) t k)
      simp only [c2] at this
      exact this
    have e2 : ∑ j ∈ Finset.univ.erase i,
        ∫ x, ∫ y, bGrad W x y k ^ 2 ∂densMeasure (ρ (a j)) ∂densMeasure (ρ (a i)) =
        ∑ t, ((n t : ℝ) - if a i = t then 1 else 0) * FQ W ρ (a i) t k := by
      have := sum_fiber_finset (Finset.univ.erase i) a (fun t => FQ W ρ (a i) t k)
      simp only [c2] at this
      exact this
    have e3 : ∑ j ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase i).erase j,
        ∫ x, mForce W (densMeasure (ρ (a j))) x k * mForce W (densMeasure (ρ (a l))) x k
          ∂densMeasure (ρ (a i)) =
        ∑ t, ∑ u, ((n t : ℝ) - if a i = t then 1 else 0) * ((n u : ℝ) - if a i = u then 1 else 0) *
          FR W ρ (a i) t u k - ∑ t, ((n t : ℝ) - if a i = t then 1 else 0) * FR W ρ (a i) t t k := by
      have := sum_erase_pairs (Finset.univ.erase i) a (fun t u => FR W ρ (a i) t u k)
      simp only [c2] at this
      exact this
    rw [e1, e2, e3]
    unfold tauN FA2
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [sum_fiber a n hfib (fun s => tauN V W ρ N n k s)]


/-- The limit value of the per-label Fisher quantity. -/
def tauInf (V : Torus d → ℝ) (W : Torus d → Torus d → ℝ) (ρ : Fin q → Torus d → ℝ)
    (θ : Fin q → ℝ) (k : Fin d) (s : Fin q) : ℝ :=
  FA2 V ρ s k + 2 * ∑ t, θ t * FM V W ρ s t k + ∑ t, ∑ u, θ t * θ u * FR W ρ s t u k

theorem tendsto_tauN (θ : Fin q → ℝ) (p : ℕ → Fin q → ℝ)
    (hp : ∀ s, Tendsto (fun N => p N s) atTop (𝓝 (θ s))) (ρ : Fin q → Torus d → ℝ)
    (k : Fin d) (s : Fin q) :
    Tendsto (fun N : ℕ => FA2 V ρ s k + 2 * ∑ t, (p N t - (1 / (N : ℝ)) * if s = t then 1 else 0) *
        FM V W ρ s t k + (1 / (N : ℝ)) * ∑ t, (p N t - (1 / (N : ℝ)) * if s = t then 1 else 0) *
        FQ W ρ s t k + (∑ t, ∑ u, (p N t - (1 / (N : ℝ)) * if s = t then 1 else 0) *
          (p N u - (1 / (N : ℝ)) * if s = u then 1 else 0) * FR W ρ s t u k -
        (1 / (N : ℝ)) * ∑ t, (p N t - (1 / (N : ℝ)) * if s = t then 1 else 0) * FR W ρ s t t k))
      atTop (𝓝 (tauInf V W ρ θ k s)) := by
  have hc : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hq : ∀ t, Tendsto (fun N : ℕ => p N t - (1 / (N : ℝ)) * if s = t then 1 else 0) atTop
      (𝓝 (θ t)) := fun t => by
    have := (hp t).sub (hc.mul_const (if s = t then (1 : ℝ) else 0))
    simpa using this
  have h1 : Tendsto (fun N : ℕ => ∑ t, (p N t - (1 / (N : ℝ)) * if s = t then 1 else 0) *
      FM V W ρ s t k) atTop (𝓝 (∑ t, θ t * FM V W ρ s t k)) :=
    tendsto_finsetSum _ fun t _ => (hq t).mul_const _
  have h2 : Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ t, (p N t - (1 / (N : ℝ)) * if s = t then 1 else 0) *
      FQ W ρ s t k) atTop (𝓝 (0 * ∑ t, θ t * FQ W ρ s t k)) :=
    hc.mul (tendsto_finsetSum _ fun t _ => (hq t).mul_const _)
  have h3 : Tendsto (fun N : ℕ => ∑ t, ∑ u, (p N t - (1 / (N : ℝ)) * if s = t then 1 else 0) *
      (p N u - (1 / (N : ℝ)) * if s = u then 1 else 0) * FR W ρ s t u k) atTop
      (𝓝 (∑ t, ∑ u, θ t * θ u * FR W ρ s t u k)) :=
    tendsto_finsetSum _ fun t _ => tendsto_finsetSum _ fun u _ => ((hq t).mul (hq u)).mul_const _
  have h4 : Tendsto (fun N : ℕ => (1 / (N : ℝ)) * ∑ t, (p N t - (1 / (N : ℝ)) * if s = t then 1 else 0) *
      FR W ρ s t t k) atTop (𝓝 (0 * ∑ t, θ t * FR W ρ s t t k)) :=
    hc.mul (tendsto_finsetSum _ fun t _ => (hq t).mul_const _)
  have := (((tendsto_const_nhds (x := FA2 V ρ s k)).add (h1.const_mul 2)).add h2).add (h3.sub h4)
  simp only [zero_mul, add_zero, sub_zero] at this
  exact this


theorem tauN_eq_pform {N : ℕ} (hN : 1 ≤ N) (ρ : Fin q → Torus d → ℝ) (n : Fin q → ℕ) (k : Fin d)
    (s : Fin q) : tauN V W ρ N n k s =
    FA2 V ρ s k + 2 * ∑ t, (((n t : ℝ) / N) - (1 / (N : ℝ)) * if s = t then 1 else 0) *
        FM V W ρ s t k + (1 / (N : ℝ)) * ∑ t, (((n t : ℝ) / N) - (1 / (N : ℝ)) * if s = t then 1 else 0) *
        FQ W ρ s t k + (∑ t, ∑ u, (((n t : ℝ) / N) - (1 / (N : ℝ)) * if s = t then 1 else 0) *
          (((n u : ℝ) / N) - (1 / (N : ℝ)) * if s = u then 1 else 0) * FR W ρ s t u k -
        (1 / (N : ℝ)) * ∑ t, (((n t : ℝ) / N) - (1 / (N : ℝ)) * if s = t then 1 else 0) *
          FR W ρ s t t k) := by
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  unfold tauN
  have e : ∀ t, (((n t : ℝ) / N) - (1 / (N : ℝ)) * if s = t then 1 else 0) =
      (1 / (N : ℝ)) * ((n t : ℝ) - if s = t then 1 else 0) := fun t => by
    field_simp
  simp_rw [e]
  have f1 : ∀ (g : Fin q → ℝ), ∑ t, (1 / (N : ℝ)) * ((n t : ℝ) - if s = t then 1 else 0) * g t =
      (1 / (N : ℝ)) * ∑ t, ((n t : ℝ) - if s = t then 1 else 0) * g t := fun g => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
  have f2 : ∑ t, ∑ u, (1 / (N : ℝ)) * ((n t : ℝ) - if s = t then 1 else 0) *
      ((1 / (N : ℝ)) * ((n u : ℝ) - if s = u then 1 else 0)) * FR W ρ s t u k =
      (1 / (N : ℝ)) ^ 2 * ∑ t, ∑ u, ((n t : ℝ) - if s = t then 1 else 0) *
        ((n u : ℝ) - if s = u then 1 else 0) * FR W ρ s t u k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  rw [f1 (fun t => FM V W ρ s t k), f1 (fun t => FQ W ρ s t k), f1 (fun t => FR W ρ s t t k), f2]
  ring

theorem fisher_limit_real (hyp : Hyp V W KV KW) (s0 : Fin q) (θ : Fin q → ℝ)
    (ρ : Fin q → Torus d → ℝ) (hθ0 : ∀ s, 0 ≤ θ s) (hθ1 : ∑ s, θ s = 1)
    (hρ : ∀ s, IsSmoothT (ρ s) ∧ (∀ x, 0 < ρ s x) ∧ ∫ x, ρ s x ∂haar d = 1) :
    Tendsto (fun N : ℕ => (fisherInfoC (Measure.pi fun i : Fin N =>
        densMeasure (ρ (assignOf s0 θ hθ0 hθ1 N i))) (gibbs V W N)).toReal / N) atTop
      (𝓝 (∑ k : Fin d, ∑ s, θ s * tauInf V W ρ θ k s)) := by
  have hp : ∀ s, Tendsto (fun N : ℕ => (groupSize s0 θ N s : ℝ) / N) atTop (𝓝 (θ s)) :=
    tendsto_groupSize s0 θ hθ0 hθ1
  have hpair : ∀ k s, Tendsto (fun N : ℕ => ((groupSize s0 θ N s : ℝ) / N) *
      tauN V W ρ N (groupSize s0 θ N) k s) atTop (𝓝 (θ s * tauInf V W ρ θ k s)) := fun k s => by
    refine (hp s).mul ?_
    refine (tendsto_tauN θ (fun N s => (groupSize s0 θ N s : ℝ) / N) hp ρ k s).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (tauN_eq_pform hN ρ (groupSize s0 θ N) k s).symm
  have hsum : Tendsto (fun N : ℕ => ∑ k : Fin d, ∑ s, ((groupSize s0 θ N s : ℝ) / N) *
      tauN V W ρ N (groupSize s0 θ N) k s) atTop
      (𝓝 (∑ k : Fin d, ∑ s, θ s * tauInf V W ρ θ k s)) :=
    tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun s _ => hpair k s
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  obtain ⟨-, hval⟩ := fisher_counts hyp hN ρ hρ (assignOf s0 θ hθ0 hθ1 N) (groupSize s0 θ N)
    (assignOf_fiber s0 θ hθ0 hθ1 N)
  rw [hval]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

end SharpLSI.FL
