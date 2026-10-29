import FullLabeledLSI.Infra.HypercontrOde
import FullLabeledLSI.Infra.HypercontrPoly

/-!
# Gross's lemma: differentiating `Φ(t) = ∫ (u_t² + ε²)^{q(t)/2}` under the integral

`u_t = ∑_k e^{-tν_k} c_k M_k`, `q(t) = 1 + e^{2at}`. If every `M_k` lies in every `L^p` (`p < ∞`)
then `Φ` is differentiable on all of `ℝ` with the expected derivative; the dominating function is a
polynomial in `∑_k |M_k|`, produced by the `PolyDom` calculus.
-/

noncomputable section

namespace SharpLSI.FL.Gross

open MeasureTheory Real Filter Topology

variable {Ω : Type*} {K : Type*} [Fintype K]

/-- `u_c = ∑_k c_k M_k`. -/
def uFun (M : K → Ω → ℝ) (c : K → ℝ) (ω : Ω) : ℝ := ∑ k, c k * M k ω

/-- The flowed coefficients `c(t)_k = e^{-tν_k} c_k`. -/
def flow (ν : K → ℝ) (t : ℝ) (c : K → ℝ) : K → ℝ := fun k => Real.exp (-(t * ν k)) * c k

/-- `A u_c = u_{νc} = ∑_k ν_k c_k M_k`. -/
def Afun (M : K → Ω → ℝ) (ν c : K → ℝ) (ω : Ω) : ℝ := uFun M (fun k => ν k * c k) ω

/-- The base function `∑_k |M_k|`. -/
def Sbase (M : K → Ω → ℝ) (ω : Ω) : ℝ := ∑ k, |M k ω|

lemma Sbase_nonneg (M : K → Ω → ℝ) (ω : Ω) : 0 ≤ Sbase M ω :=
  Finset.sum_nonneg fun k _ => abs_nonneg _

lemma abs_uFun_le (M : K → Ω → ℝ) {c : K → ℝ} {A : ℝ} (hA : ∀ k, |c k| ≤ A) (ω : Ω) :
    |uFun M c ω| ≤ A * Sbase M ω := by
  unfold uFun Sbase
  calc |∑ k, c k * M k ω| ≤ ∑ k, |c k * M k ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, A * |M k ω| := Finset.sum_le_sum fun k _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hA k) (abs_nonneg _)
    _ = A * ∑ k, |M k ω| := by rw [Finset.mul_sum]

section Time

variable (M : K → Ω → ℝ) (ν c : K → ℝ) (a ε : ℝ)

/-- `u_t(ω)`. -/
def uT (t : ℝ) (ω : Ω) : ℝ := uFun M (flow ν t c) ω

/-- `(A u_t)(ω)`. -/
def vT (t : ℝ) (ω : Ω) : ℝ := Afun M ν (flow ν t c) ω

/-- `B_t = u_t² + ε²`. -/
def Bt (t : ℝ) (ω : Ω) : ℝ := uT M ν c t ω ^ 2 + ε ^ 2

/-- The integrand `B_t^{q(t)/2}`. -/
def Ft (t : ℝ) (ω : Ω) : ℝ := Bt M ν c ε t ω ^ (qexp a t / 2)

/-- Its `t`-derivative. -/
def Dt (t : ℝ) (ω : Ω) : ℝ :=
  -(qexp a t * uT M ν c t ω * vT M ν c t ω * Bt M ν c ε t ω ^ (qexp a t / 2 - 1)) +
    a * (qexp a t - 1) * Bt M ν c ε t ω ^ (qexp a t / 2) * Real.log (Bt M ν c ε t ω)

lemma Bt_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) (ω : Ω) : 0 < Bt M ν c ε t ω := by
  unfold Bt; positivity

lemma hasDerivAt_uT (ω : Ω) (t : ℝ) :
    HasDerivAt (fun s => uT M ν c s ω) (-(vT M ν c t ω)) t := by
  simp only [uT, vT, uFun, Afun, flow]
  have hterm : ∀ k ∈ (Finset.univ : Finset K), HasDerivAt
      (fun s => Real.exp (-(s * ν k)) * c k * M k ω)
      (-(ν k * (Real.exp (-(t * ν k)) * c k) * M k ω)) t := by
    intro k _
    have h0 : HasDerivAt (fun s : ℝ => s * ν k) (ν k) t := by
      simpa using (hasDerivAt_id t).mul_const (ν k)
    have h1 : HasDerivAt (fun s : ℝ => -(s * ν k)) (-ν k) t := h0.neg
    have h2 := ((h1.exp).mul_const (c k)).mul_const (M k ω)
    convert h2 using 1; ring
  have := HasDerivAt.fun_sum hterm
  convert this using 1
  rw [Finset.sum_neg_distrib]

lemma hasDerivAt_Ft {ε : ℝ} (hε : 0 < ε) (t : ℝ) (ω : Ω) :
    HasDerivAt (fun s => Ft M ν c a ε s ω) (Dt M ν c a ε t ω) t := by
  have hu := hasDerivAt_uT M ν c ω t
  have hB : HasDerivAt (fun s => Bt M ν c ε s ω)
      (2 * uT M ν c t ω * (-(vT M ν c t ω))) t := by
    refine ((hu.pow 2).add_const (ε ^ 2)).congr_deriv ?_
    norm_num
  have hg : HasDerivAt (fun s => qexp a s / 2) (a * (qexp a t - 1)) t := by
    refine ((hasDerivAt_qexp a t).div_const 2).congr_deriv ?_
    ring
  have := hB.rpow hg (Bt_pos M ν c hε t ω)
  refine this.congr_deriv ?_
  unfold Dt; ring

end Time

section Dom

variable (M : K → Ω → ℝ) (ν c : K → ℝ) (a ε : ℝ)

lemma abs_flow_le {T t : ℝ} (ht : |t| ≤ T) (k : K) :
    |flow ν t c k| ≤ Real.exp (T * |ν k|) * |c k| := by
  unfold flow
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  calc -(t * ν k) ≤ |t * ν k| := neg_le_abs _
    _ = |t| * |ν k| := abs_mul _ _
    _ ≤ T * |ν k| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)

/-- Index type for times with `|t| ≤ T`. -/
abbrev Ix (T : ℝ) := {s : ℝ // |s| ≤ T}

lemma polyDom_uT (T : ℝ) :
    PolyDom (Sbase M) (fun (i : Ix T) ω => uT M ν c i.1 ω) := by
  set A1 := ∑ k, Real.exp (T * |ν k|) * |c k| with hA1
  have hA1nn : 0 ≤ A1 := Finset.sum_nonneg fun k _ => by positivity
  refine PolyDom.of_bound (Sbase_nonneg M) A1 1 fun i ω => ?_
  have hk : ∀ k, |flow ν i.1 c k| ≤ A1 := fun k =>
    (abs_flow_le ν c i.2 k).trans (Finset.single_le_sum
      (f := fun k => Real.exp (T * |ν k|) * |c k|) (fun j _ => by positivity) (Finset.mem_univ k))
  have := abs_uFun_le M hk ω
  calc |uT M ν c i.1 ω| ≤ A1 * Sbase M ω := this
    _ ≤ A1 * (1 + Sbase M ω) ^ 1 := by
        rw [pow_one]; exact mul_le_mul_of_nonneg_left (by linarith) hA1nn

lemma polyDom_vT (T : ℝ) :
    PolyDom (Sbase M) (fun (i : Ix T) ω => vT M ν c i.1 ω) := by
  set A2 := ∑ k, |ν k| * (Real.exp (T * |ν k|) * |c k|) with hA2
  have hA2nn : 0 ≤ A2 := Finset.sum_nonneg fun k _ => by positivity
  refine PolyDom.of_bound (Sbase_nonneg M) A2 1 fun i ω => ?_
  have hk : ∀ k, |ν k * flow ν i.1 c k| ≤ A2 := fun k => by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_flow_le ν c i.2 k) (abs_nonneg _)).trans
      (Finset.single_le_sum (f := fun k => |ν k| * (Real.exp (T * |ν k|) * |c k|))
        (fun j _ => by positivity) (Finset.mem_univ k))
  have := abs_uFun_le M hk ω
  calc |vT M ν c i.1 ω| ≤ A2 * Sbase M ω := this
    _ ≤ A2 * (1 + Sbase M ω) ^ 1 := by
        rw [pow_one]; exact mul_le_mul_of_nonneg_left (by linarith) hA2nn

lemma polyDom_B (T : ℝ) :
    PolyDom (Sbase M) (fun (i : Ix T) ω => Bt M ν c ε i.1 ω) :=
  ((polyDom_uT M ν c T).pow (Sbase_nonneg M) 2).add (Sbase_nonneg M) (PolyDom.const (ε ^ 2))

lemma qexp_le_of_abs_le {a : ℝ} (ha : 0 < a) {T s : ℝ} (hs : |s| ≤ T) : qexp a s ≤ qexp a T := by
  unfold qexp
  have h1 : s ≤ T := (abs_le.mp hs).2
  have : 2 * a * s ≤ 2 * a * T := by nlinarith
  linarith [Real.exp_le_exp.mpr this]

lemma polyDom_Ft (ha : 0 < a) (hε : 0 < ε) (T : ℝ) :
    PolyDom (Sbase M) (fun (i : Ix T) ω => Ft M ν c a ε i.1 ω) :=
  PolyDom.rpow (Sbase_nonneg M) (polyDom_B M ν c ε T) (fun i ω => (Bt_pos M ν c hε i.1 ω).le)
    (p := fun i => qexp a i.1 / 2) (P := qexp a T / 2)
    (fun i => div_nonneg (qexp_pos a _).le zero_le_two)
    (fun i => div_le_div_of_nonneg_right (qexp_le_of_abs_le ha i.2) zero_le_two)

lemma abs_mul_rpow_le {u B : ℝ} (hB : 0 < B) (hu : u ^ 2 ≤ B) (q : ℝ) :
    |u| * B ^ (q / 2 - 1) ≤ B ^ ((q - 1) / 2) := by
  have h1 : |u| ≤ B ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.abs_le_sqrt hu
  calc |u| * B ^ (q / 2 - 1) ≤ B ^ ((1 : ℝ) / 2) * B ^ (q / 2 - 1) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hB.le _)
    _ = B ^ ((q - 1) / 2) := by
        rw [← Real.rpow_add hB]; congr 1; ring

lemma abs_log_le {ε B : ℝ} (hε : 0 < ε) (hB : ε ^ 2 ≤ B) :
    |Real.log B| ≤ |Real.log (ε ^ 2)| + B := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hB0 : 0 < B := lt_of_lt_of_le hε2 hB
  have h1 : Real.log (ε ^ 2) ≤ Real.log B := Real.log_le_log hε2 hB
  have h2 : Real.log B ≤ B - 1 := Real.log_le_sub_one_of_pos hB0
  have h3 : -|Real.log (ε ^ 2)| ≤ Real.log (ε ^ 2) := neg_abs_le _
  have h4 := abs_nonneg (Real.log (ε ^ 2))
  rw [abs_le]; constructor <;> linarith

lemma polyDom_Dt (ha : 0 < a) (hε : 0 < ε) (T : ℝ) :
    PolyDom (Sbase M) (fun (i : Ix T) ω => Dt M ν c a ε i.1 ω) := by
  have hS := Sbase_nonneg M
  have hqT : ∀ i : Ix T, qexp a i.1 ≤ qexp a T := fun i => qexp_le_of_abs_le ha i.2
  have hB0 : ∀ (i : Ix T) ω, 0 < Bt M ν c ε i.1 ω := fun i ω => Bt_pos M ν c hε i.1 ω
  -- first term
  have hA : PolyDom (Sbase M) (fun (i : Ix T) ω => qexp a i.1 * uT M ν c i.1 ω * vT M ν c i.1 ω *
      Bt M ν c ε i.1 ω ^ (qexp a i.1 / 2 - 1)) := by
    have hv := (polyDom_vT M ν c T).abs
    have hBr : PolyDom (Sbase M) (fun (i : Ix T) ω =>
        Bt M ν c ε i.1 ω ^ ((qexp a i.1 - 1) / 2)) :=
      PolyDom.rpow hS (polyDom_B M ν c ε T) (fun i ω => (hB0 i ω).le)
        (p := fun i => (qexp a i.1 - 1) / 2) (P := qexp a T / 2)
        (fun i => div_nonneg (by linarith [one_lt_qexp a i.1]) zero_le_two)
        (fun i => div_le_div_of_nonneg_right (by linarith [hqT i]) zero_le_two)
    have hq : PolyDom (Sbase M) (fun (i : Ix T) (_ : Ω) => |qexp a i.1|) :=
      PolyDom.const_family _ (qexp a T) (qexp_pos a T).le (fun i => by
        rw [abs_abs, abs_of_pos (qexp_pos a _)]; exact hqT i)
    refine (hq.mul hS (hv.mul hS hBr)).mono fun i ω => ?_
    have hBi := hB0 i ω
    have hu2 : uT M ν c i.1 ω ^ 2 ≤ Bt M ν c ε i.1 ω := by unfold Bt; nlinarith [sq_nonneg ε]
    have key := abs_mul_rpow_le hBi hu2 (qexp a i.1)
    have hnn : 0 ≤ |qexp a i.1| * (|vT M ν c i.1 ω| * Bt M ν c ε i.1 ω ^ ((qexp a i.1 - 1) / 2)) :=
      by positivity
    rw [abs_of_nonneg hnn]
    calc |qexp a i.1 * uT M ν c i.1 ω * vT M ν c i.1 ω *
          Bt M ν c ε i.1 ω ^ (qexp a i.1 / 2 - 1)|
        = |qexp a i.1| * |vT M ν c i.1 ω| *
          (|uT M ν c i.1 ω| * Bt M ν c ε i.1 ω ^ (qexp a i.1 / 2 - 1)) := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hBi.le _)]; ring
      _ ≤ |qexp a i.1| * |vT M ν c i.1 ω| * Bt M ν c ε i.1 ω ^ ((qexp a i.1 - 1) / 2) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring
  -- second term
  have hBterm : PolyDom (Sbase M) (fun (i : Ix T) ω => a * (qexp a i.1 - 1) *
      Bt M ν c ε i.1 ω ^ (qexp a i.1 / 2) * Real.log (Bt M ν c ε i.1 ω)) := by
    have hF := polyDom_Ft M ν c a ε ha hε T
    have hlog : PolyDom (Sbase M) (fun (i : Ix T) ω => |Real.log (ε ^ 2)| + Bt M ν c ε i.1 ω) :=
      (PolyDom.const (|Real.log (ε ^ 2)|)).add hS (polyDom_B M ν c ε T)
    have hqa : PolyDom (Sbase M) (fun (i : Ix T) (_ : Ω) => a * (qexp a i.1 - 1)) :=
      PolyDom.const_family _ (a * qexp a T) (by have := qexp_pos a T; positivity)
        (fun i => by
          rw [abs_of_nonneg (mul_nonneg ha.le (by linarith [one_lt_qexp a i.1]))]
          exact mul_le_mul_of_nonneg_left (by linarith [hqT i]) ha.le)
    refine (hqa.mul hS (hF.mul hS hlog)).mono fun i ω => ?_
    have hBi := hB0 i ω
    have hlogB := abs_log_le hε (show ε ^ 2 ≤ Bt M ν c ε i.1 ω by unfold Bt; nlinarith [sq_nonneg (uT M ν c i.1 ω)])
    have hnn : 0 ≤ a * (qexp a i.1 - 1) * (Ft M ν c a ε i.1 ω *
        (|Real.log (ε ^ 2)| + Bt M ν c ε i.1 ω)) := by
      have : 0 ≤ Ft M ν c a ε i.1 ω := Real.rpow_nonneg hBi.le _
      have := one_lt_qexp a i.1
      have : 0 ≤ |Real.log (ε ^ 2)| + Bt M ν c ε i.1 ω := by positivity
      positivity
    rw [abs_of_nonneg hnn]
    have hF0 : 0 ≤ Ft M ν c a ε i.1 ω := Real.rpow_nonneg hBi.le _
    have hqm : 0 ≤ a * (qexp a i.1 - 1) := mul_nonneg ha.le (by linarith [one_lt_qexp a i.1])
    calc |a * (qexp a i.1 - 1) * Bt M ν c ε i.1 ω ^ (qexp a i.1 / 2) *
          Real.log (Bt M ν c ε i.1 ω)|
        = a * (qexp a i.1 - 1) * (Ft M ν c a ε i.1 ω * |Real.log (Bt M ν c ε i.1 ω)|) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hqm, abs_of_nonneg (Real.rpow_nonneg hBi.le _)]
          unfold Ft; ring
      _ ≤ a * (qexp a i.1 - 1) * (Ft M ν c a ε i.1 ω *
          (|Real.log (ε ^ 2)| + Bt M ν c ε i.1 ω)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogB hF0) hqm
  exact hA.neg.add hS hBterm

end Dom

section Measurability

variable [MeasurableSpace Ω] {P : Measure Ω} (M : K → Ω → ℝ) (ν c : K → ℝ) (a ε : ℝ)

lemma aem_uT (hM : ∀ k, AEMeasurable (M k) P) (t : ℝ) : AEMeasurable (uT M ν c t) P := by
  unfold uT uFun
  exact Finset.aemeasurable_fun_sum Finset.univ fun k _ => (hM k).const_mul _

lemma aem_vT (hM : ∀ k, AEMeasurable (M k) P) (t : ℝ) : AEMeasurable (vT M ν c t) P := by
  unfold vT Afun uFun
  exact Finset.aemeasurable_fun_sum Finset.univ fun k _ => (hM k).const_mul _

lemma aem_Bt (hM : ∀ k, AEMeasurable (M k) P) (t : ℝ) : AEMeasurable (Bt M ν c ε t) P := by
  unfold Bt
  exact ((aem_uT M ν c hM t).pow_const 2).add_const _

lemma aem_Ft (hM : ∀ k, AEMeasurable (M k) P) (t : ℝ) : AEMeasurable (Ft M ν c a ε t) P := by
  unfold Ft
  exact (aem_Bt M ν c ε hM t).pow_const _

lemma aem_Dt (hM : ∀ k, AEMeasurable (M k) P) (t : ℝ) : AEMeasurable (Dt M ν c a ε t) P := by
  unfold Dt
  have hB := aem_Bt M ν c ε hM t
  have hu := aem_uT M ν c hM t
  have hv := aem_vT M ν c hM t
  exact (((hu.const_mul _).mul hv |>.mul (hB.pow_const _))).neg.add
    (((hB.pow_const _).const_mul _).mul hB.log)

end Measurability

section Main

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (M : K → Ω → ℝ) (ν c : K → ℝ) (a ε : ℝ)

lemma memLp_Sbase (hM : ∀ k (n : ℕ), MemLp (M k) n P) (n : ℕ) : MemLp (Sbase M) n P := by
  have : MemLp (fun ω => ∑ k, ‖M k ω‖) n P :=
    memLp_finsetSum Finset.univ fun k _ => (hM k n).norm
  have e : Sbase M = fun ω => ∑ k, |M k ω| := rfl
  rw [e]
  simpa [Real.norm_eq_abs] using this

/-- Differentiation of `Φ(t) = ∫ (u_t² + ε²)^{q(t)/2}` under the integral sign. -/
theorem hasDerivAt_Phi (hM : ∀ k (n : ℕ), MemLp (M k) n P) (ha : 0 < a) (hε : 0 < ε) (t : ℝ) :
    Integrable (Dt M ν c a ε t) P ∧
      HasDerivAt (fun s => ∫ ω, Ft M ν c a ε s ω ∂P) (∫ ω, Dt M ν c a ε t ω ∂P) t := by
  have hS := Sbase_nonneg M
  have hSm := memLp_Sbase M hM
  have hMe : ∀ k, AEMeasurable (M k) P := fun k => (hM k 1).aestronglyMeasurable.aemeasurable
  set T : ℝ := |t| + 1 with hT
  obtain ⟨C, hC, N, hb⟩ := polyDom_Dt M ν c a ε ha hε T
  have htT : |t| ≤ T := by rw [hT]; linarith
  have hFint : Integrable (Ft M ν c a ε t) P :=
    (polyDom_Ft M ν c a ε ha hε T).integrable hS hSm ⟨t, htT⟩
      (aem_Ft M ν c a ε hMe t).aestronglyMeasurable
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.Ioo (t - 1) (t + 1))
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Filter.Eventually.of_forall fun s => (aem_Ft M ν c a ε hMe s).aestronglyMeasurable) hFint
    (aem_Dt M ν c a ε hMe t).aestronglyMeasurable ?_
    ((integrable_one_add_pow hS hSm N).const_mul C)
    (Filter.Eventually.of_forall fun ω s _ => hasDerivAt_Ft M ν c a hε s ω)
  refine Filter.Eventually.of_forall fun ω s hs => ?_
  have hsT : |s| ≤ T :=
    abs_le.mpr ⟨by linarith [hs.1, neg_abs_le t], by linarith [hs.2, le_abs_self t]⟩
  simpa [Real.norm_eq_abs] using hb ⟨s, hsT⟩ ω

end Main

end SharpLSI.FL.Gross

end
