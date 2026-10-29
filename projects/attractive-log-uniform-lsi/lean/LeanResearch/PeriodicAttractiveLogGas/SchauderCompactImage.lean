import LeanResearch.Imported.Brouwer.brouwer
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-! A compact-image Schauder theorem for an arbitrary real normed space.
The finite-dimensional approximation uses a finite coefficient simplex;
finite dimensionality is never imposed on the ambient space. The source
application is the reference-family existence proof at lines 2386--2391.
See the development note for the exact central verification status.
-/

noncomputable section
open Set Filter Metric
open scoped BigOperators Topology

namespace PeriodicAttractiveLogGas.SchauderCompactImage

variable {E : Type*} [NormedAddCommGroup E]
variable {ι : Type*} [Fintype ι]

/-- The literal finite coefficient simplex. Its definition avoids the
deprecated set-valued `stdSimplex` interface. -/
def coefficientSimplex (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {w | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1}

theorem coefficientSimplex_convex (ι : Type*) [Fintype ι] :
    Convex ℝ (coefficientSimplex ι) := by
  intro w hw v hv a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hw.1 i)) (mul_nonneg hb (hv.1 i)), ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, hw.2, hv.2, mul_one, hab]

theorem coefficientSimplex_isClosed (ι : Type*) [Fintype ι] :
    IsClosed (coefficientSimplex ι) := by
  have he : coefficientSimplex ι =
      (⋂ i, {w : ι → ℝ | 0 ≤ w i}) ∩ {w : ι → ℝ | ∑ i, w i = 1} := by
    ext w
    simp only [coefficientSimplex, mem_ofPred_eq, mem_inter_iff, mem_iInter]
  rw [he]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_eq (by fun_prop) continuous_const)

theorem coefficientSimplex_isCompact (ι : Type*) [Fintype ι] :
    IsCompact (coefficientSimplex ι) := by
  apply (isCompact_univ_pi fun _ : ι => (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).of_isClosed_subset
    (coefficientSimplex_isClosed ι)
  intro w hw i _
  refine ⟨hw.1 i, ?_⟩
  calc
    w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
    _ = 1 := hw.2

theorem coefficientSimplex_nonempty (ι : Type*) [Fintype ι] [Nonempty ι] :
    (coefficientSimplex ι).Nonempty := by
  classical
  let i : ι := Classical.choice inferInstance
  refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
  · intro j
    by_cases h : j = i <;> simp [h]
  · simp

/-- Centers remain in the original compact set, including the nonemptiness
needed for the finite coefficient simplex. -/
theorem exists_finite_centers {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Set E, t.Finite ∧ t.Nonempty ∧ t ⊆ K ∧
      ∀ y ∈ K, ∃ i : t, dist y (i : E) < ε := by
  obtain ⟨t, htK, ht, hcover⟩ := hK.finite_cover_balls hε
  have hc (y : E) (hy : y ∈ K) : ∃ i : t, dist y (i : E) < ε := by
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hcover hy)
    exact ⟨⟨i, hi⟩, hyi⟩
  have htne : t.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨i, _⟩ := hc y hy
    exact ⟨i.val, i.property⟩
  exact ⟨t, ht, htne, htK, hc⟩

def bump (ε : ℝ) (c : ι → E) (i : ι) (y : E) : ℝ :=
  max 0 (ε - dist y (c i))

def bumpTotal (ε : ℝ) (c : ι → E) (y : E) : ℝ := ∑ i, bump ε c i y

def weight (ε : ℝ) (c : ι → E) (y : E) (i : ι) : ℝ :=
  bump ε c i y / bumpTotal ε c y

omit [Fintype ι] in
theorem bump_nonneg (ε : ℝ) (c : ι → E) (i : ι) (y : E) : 0 ≤ bump ε c i y :=
  le_max_left _ _

theorem bumpTotal_nonneg (ε : ℝ) (c : ι → E) (y : E) : 0 ≤ bumpTotal ε c y :=
  Finset.sum_nonneg fun i _ => bump_nonneg ε c i y

theorem bumpTotal_pos {ε : ℝ} {c : ι → E} {y : E}
    (hcover : ∃ i, dist y (c i) < ε) : 0 < bumpTotal ε c y := by
  obtain ⟨i, hi⟩ := hcover
  have hp : 0 < bump ε c i y := (sub_pos.mpr hi).trans_le (le_max_right _ _)
  exact hp.trans_le (Finset.single_le_sum (fun j _ => bump_nonneg ε c j y) (Finset.mem_univ i))

theorem weight_nonneg (ε : ℝ) (c : ι → E) (y : E) (i : ι) : 0 ≤ weight ε c y i :=
  div_nonneg (bump_nonneg ε c i y) (bumpTotal_nonneg ε c y)

theorem sum_weight {ε : ℝ} {c : ι → E} {y : E}
    (hcover : ∃ i, dist y (c i) < ε) : ∑ i, weight ε c y i = 1 := by
  unfold weight
  rw [← Finset.sum_div]
  exact div_self (bumpTotal_pos hcover).ne'

theorem weight_eq_zero_of_le {ε : ℝ} {c : ι → E} {y : E} {i : ι}
    (hi : ε ≤ dist y (c i)) : weight ε c y i = 0 := by
  simp only [weight, bump, max_eq_left (sub_nonpos.mpr hi), zero_div]

theorem weight_mem_coefficientSimplex {ε : ℝ} {c : ι → E} {y : E}
    (hcover : ∃ i, dist y (c i) < ε) : weight ε c y ∈ coefficientSimplex ι :=
  ⟨weight_nonneg ε c y, sum_weight hcover⟩

omit [Fintype ι] in
theorem continuous_bump (ε : ℝ) (c : ι → E) (i : ι) : Continuous (bump ε c i) := by
  unfold bump
  fun_prop

theorem continuous_bumpTotal (ε : ℝ) (c : ι → E) : Continuous (bumpTotal ε c) :=
  continuous_finsetSum _ fun i _ => continuous_bump ε c i

theorem continuous_weight_on {K : Set E} {ε : ℝ} {c : ι → E}
    (hcover : ∀ y ∈ K, ∃ i, dist y (c i) < ε) :
    Continuous (fun y : K => weight ε c (y : E)) := by
  apply continuous_pi
  intro i
  change Continuous (fun y : K => bump ε c i (y : E) / bumpTotal ε c (y : E))
  exact ((continuous_bump ε c i).comp continuous_subtype_val).div
    ((continuous_bumpTotal ε c).comp continuous_subtype_val)
    (fun y => (bumpTotal_pos (hcover y.val y.property)).ne')

/-- Compactness of the actual ambient image supplies a convergent subsequence.
Approximate fixed points converge to that same limit; continuity then identifies
it as a fixed point. The final Schauder theorem below will construct the
approximate fixed points rather than assuming this intermediate premise. -/
theorem exists_fixedPoint_of_approximation {C : Set E} (hC : IsClosed C)
    (f : C → C) (hf : Continuous f)
    (hcompact : IsCompact (closure (Set.range (fun x : C => (f x : E)))))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x : C, dist (f x : E) (x : E) ≤ ε) :
    ∃ x : C, f x = x := by
  classical
  choose u hu using fun n : ℕ => happrox (1 / ((n : ℝ) + 1)) (by positivity)
  let K : Set E := closure (Set.range (fun x : C => (f x : E)))
  have hKC : K ⊆ C := closure_minimal (by
    rintro y ⟨x, rfl⟩
    exact (f x).property) hC
  have hseqK (n : ℕ) : (f (u n) : E) ∈ K := subset_closure ⟨u n, rfl⟩
  obtain ⟨z, hz, k, hk, hkz⟩ := hcompact.tendsto_subseq hseqK
  let zC : C := ⟨z, hKC hz⟩
  have heps : Tendsto (fun n : ℕ => 1 / ((k n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk.tendsto_atTop
  have hz0 : Tendsto (fun n => dist (f (u (k n)) : E) z) atTop (𝓝 0) := by
    simpa only [Function.comp_def, dist_eq_norm] using
      tendsto_iff_norm_sub_tendsto_zero.mp hkz
  have hx0 : Tendsto (fun n => dist (u (k n) : E) z) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
      (by simpa only [add_zero] using heps.add hz0)
    calc
      dist (u (k n) : E) z ≤ dist (u (k n) : E) (f (u (k n)) : E) +
          dist (f (u (k n)) : E) z := dist_triangle _ _ _
      _ ≤ 1 / ((k n : ℝ) + 1) + dist (f (u (k n)) : E) z := by
        apply add_le_add _ le_rfl
        rw [dist_comm]
        exact hu (k n)
  have hxE : Tendsto (fun n => (u (k n) : E)) atTop (𝓝 z) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [dist_eq_norm] using hx0)
  have hxC : Tendsto (fun n => u (k n)) atTop (𝓝 zC) := tendsto_subtype_rng.mpr hxE
  have hfxE : Tendsto (fun n => (f (u (k n)) : E)) atTop (𝓝 (f zC : E)) :=
    ((continuous_subtype_val.comp hf).tendsto zC).comp hxC
  refine ⟨zC, Subtype.ext ?_⟩
  exact tendsto_nhds_unique hfxE (by simpa only [Function.comp_def] using hkz)

variable [NormedSpace ℝ E]

def barycenter (c : ι → E) (w : ι → ℝ) : E := ∑ i, w i • c i

theorem continuous_barycenter (c : ι → E) : Continuous (barycenter c) := by
  unfold barycenter
  fun_prop

theorem barycenter_mem {C : Set E} (hC : Convex ℝ C) {c : ι → E}
    (hc : ∀ i, c i ∈ C) {w : ι → ℝ} (hw : w ∈ coefficientSimplex ι) :
    barycenter c w ∈ C :=
  hC.sum_mem (fun i _ => hw.1 i) hw.2 (fun i _ => hc i)

def approximation (ε : ℝ) (c : ι → E) (y : E) : E := barycenter c (weight ε c y)

theorem continuous_approximation_on {K : Set E} {ε : ℝ} {c : ι → E}
    (hcover : ∀ y ∈ K, ∃ i, dist y (c i) < ε) :
    Continuous (fun y : K => approximation ε c (y : E)) :=
  (continuous_barycenter c).comp (continuous_weight_on hcover)

theorem approximation_mem {C : Set E} (hC : Convex ℝ C) {ε : ℝ} {c : ι → E}
    (hc : ∀ i, c i ∈ C) {y : E} (hcover : ∃ i, dist y (c i) < ε) :
    approximation ε c y ∈ C :=
  barycenter_mem hC hc (weight_mem_coefficientSimplex hcover)

/-- Only centers less than `ε` from the evaluation point have nonzero weight.
The normalized convex combination therefore approximates that point. -/
theorem dist_approximation_le {ε : ℝ} {c : ι → E} {y : E}
    (hcover : ∃ i, dist y (c i) < ε) : dist (approximation ε c y) y ≤ ε := by
  have hs := sum_weight hcover
  have he : (∑ i, weight ε c y i • (c i - y)) = approximation ε c y - y := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul,
      approximation, barycenter]
  rw [dist_eq_norm, ← he]
  calc
    ‖∑ i, weight ε c y i • (c i - y)‖ ≤ ∑ i, ‖weight ε c y i • (c i - y)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, weight ε c y i * ε := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : ε ≤ dist y (c i)
      · rw [weight_eq_zero_of_le hi, zero_smul, norm_zero, zero_mul]
      · rw [norm_smul, Real.norm_of_nonneg (weight_nonneg ε c y i)]
        exact mul_le_mul_of_nonneg_left (by
          simpa only [dist_eq_norm, norm_sub_rev] using (lt_of_not_ge hi).le)
          (weight_nonneg ε c y i)
    _ = ε := by rw [← Finset.sum_mul, hs, one_mul]

/-- Brouwer is applied only in a finite coefficient space. Every center lies
in the actual compact image closure, and every denominator is positive there.
The resulting barycenter is an approximate fixed point of the original map. -/
theorem exists_approximate_fixedPoint {C : Set E} (hne : C.Nonempty)
    (hclosed : IsClosed C) (hconvex : Convex ℝ C) (f : C → C) (hf : Continuous f)
    (hcompact : IsCompact (closure (Set.range (fun x : C => (f x : E)))))
    {ε : ℝ} (hε : 0 < ε) : ∃ x : C, dist (f x : E) (x : E) ≤ ε := by
  classical
  let K : Set E := closure (Set.range (fun x : C => (f x : E)))
  have hKC : K ⊆ C := closure_minimal (by
    rintro y ⟨x, rfl⟩
    exact (f x).property) hclosed
  have hKne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨(f ⟨x, hx⟩ : E), subset_closure ⟨⟨x, hx⟩, rfl⟩⟩
  obtain ⟨t, ht, htne, htK, hcover⟩ := exists_finite_centers (K := K) hcompact hKne hε
  let : Finite t := ht.to_subtype
  let : Fintype t := Fintype.ofFinite t
  let : Nonempty t := htne.coe_sort
  let c : t → E := fun i => (i : E)
  have hc (i : t) : c i ∈ C := hKC (htK i.property)
  let b : ContinuousMap ↥(coefficientSimplex t) ↥C :=
    { toFun := fun w => ⟨barycenter c w.val, barycenter_mem hconvex hc w.property⟩
      continuous_toFun :=
        ((continuous_barycenter c).comp continuous_subtype_val).subtype_mk _ }
  let v : ContinuousMap ↥(coefficientSimplex t) ↥K :=
    { toFun := fun w => ⟨(f (b w) : E), subset_closure ⟨b w, rfl⟩⟩
      continuous_toFun :=
        (continuous_subtype_val.comp (hf.comp b.continuous)).subtype_mk _ }
  let g : ContinuousMap ↥(coefficientSimplex t) ↥(coefficientSimplex t) :=
    { toFun := fun w => ⟨weight ε c (v w : E),
        weight_mem_coefficientSimplex (hcover (v w) (v w).property)⟩
      continuous_toFun :=
        ((continuous_weight_on hcover).comp v.continuous).subtype_mk _ }
  obtain ⟨w, hw⟩ := brouwer_fixed_point (coefficientSimplex t)
    (coefficientSimplex_convex t) (coefficientSimplex_isCompact t)
    (coefficientSimplex_nonempty t) g
  let x : C := b w
  have hw' : weight ε c (f x : E) = w.val := congrArg Subtype.val hw
  have he : approximation ε c (f x : E) = (x : E) := by
    change barycenter c (weight ε c (f x : E)) = barycenter c w.val
    rw [hw']
  refine ⟨x, ?_⟩
  have hd := dist_approximation_le (c := c) (hcover (f x) (subset_closure ⟨x, rfl⟩))
  rw [he, dist_comm] at hd
  exact hd

/-- Schauder's compact-image fixed-point theorem in an arbitrary real normed
space. The ambient space need not be finite-dimensional or complete. The
approximate fixed points are constructed above from the proved Brouwer theorem,
so no fixed-point, approximation, or desired conclusion is an extra premise. -/
theorem exists_fixedPoint {C : Set E} (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconvex : Convex ℝ C) (f : C → C) (hf : Continuous f)
    (hcompact : IsCompact (closure (Set.range (fun x : C => (f x : E))))) :
    ∃ x : C, f x = x :=
  exists_fixedPoint_of_approximation hclosed f hf hcompact
    (fun _ hε => exists_approximate_fixedPoint hne hclosed hconvex f hf hcompact hε)

end PeriodicAttractiveLogGas.SchauderCompactImage
