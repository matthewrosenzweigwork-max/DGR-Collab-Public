import FullLabeledLSI.Defs.F06_Hybrid

/-!
# The hybrid polynomial as a sum over retained/replaced multi-indices

For a coefficient array `c : (Fin N → Fin (J+1)) → ℝ` and a set `B` of retained labels, the multi-indices
`j` factor as `j = merge jB jC` with `jB` supported on `B` and `jC` supported off `B`, and
`hybPoly e c B (x, y) = ∑_{jB} (∏_i e_{jB i}(x_i)) * P_{jB}(y)`,
`P_{jB}(y) = ∑_{jC} c_{merge jB jC} ∏_i gamF (jC i) (y_i)`.
-/

open MeasureTheory

noncomputable section

namespace SharpLSI.FL.Hyb

variable {d N J : ℕ}

/-- The polynomial `F̃_N` on the hybrid space (same body as `hybEval`, with the coefficient array and
the retained set as independent data). -/
def hybPoly (e : ℕ → Torus d → ℝ) (c : (Fin N → Fin (J + 1)) → ℝ) (B : Finset (Fin N))
    (ω : Config N d × (Fin N → Fin J → ℝ)) : ℝ :=
  ∑ j, c j * ∏ i, hybFactor e B i (j i) ω

/-- The Gaussian factor: `1` for the index `0`, the coordinate `y_{m-1}` for `m ≥ 1`. -/
def gamF (m : Fin (J + 1)) (yi : Fin J → ℝ) : ℝ :=
  if h : (m : ℕ) = 0 then 1 else yi ⟨(m : ℕ) - 1, by omega⟩

variable (B : Finset (Fin N))

/-- Multi-indices supported on `B`. -/
def SB : Finset (Fin N → Fin (J + 1)) :=
  Finset.univ.filter fun j => ∀ i, i ∉ B → j i = 0

/-- Multi-indices supported off `B`. -/
def SC : Finset (Fin N → Fin (J + 1)) :=
  Finset.univ.filter fun j => ∀ i, i ∈ B → j i = 0

/-- Merge a `B`-supported and a `Bᶜ`-supported multi-index. -/
def mergeJ (jB jC : Fin N → Fin (J + 1)) : Fin N → Fin (J + 1) :=
  fun i => if i ∈ B then jB i else jC i

/-- Restriction of a multi-index to `B`. -/
def projB (j : Fin N → Fin (J + 1)) : Fin N → Fin (J + 1) :=
  fun i => if i ∈ B then j i else 0

/-- Restriction of a multi-index to `Bᶜ`. -/
def projC (j : Fin N → Fin (J + 1)) : Fin N → Fin (J + 1) :=
  fun i => if i ∈ B then 0 else j i

lemma merge_proj (j : Fin N → Fin (J + 1)) : mergeJ B (projB B j) (projC B j) = j := by
  funext i; unfold mergeJ projB projC; split_ifs <;> rfl

lemma projB_mem (j : Fin N → Fin (J + 1)) : projB B j ∈ SB B := by
  simp only [SB, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i hi; simp [projB, hi]

lemma projC_mem (j : Fin N → Fin (J + 1)) : projC B j ∈ SC B := by
  simp only [SC, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i hi; simp [projC, hi]

lemma projB_merge {jB jC : Fin N → Fin (J + 1)} (hB : jB ∈ SB B) (hC : jC ∈ SC B) :
    projB B (mergeJ B jB jC) = jB := by
  funext i
  simp only [SB, Finset.mem_filter, Finset.mem_univ, true_and] at hB
  by_cases hi : i ∈ B
  · simp [projB, mergeJ, hi]
  · simp [projB, hi, hB i hi]

lemma projC_merge {jB jC : Fin N → Fin (J + 1)} (hB : jB ∈ SB B) (hC : jC ∈ SC B) :
    projC B (mergeJ B jB jC) = jC := by
  funext i
  simp only [SC, Finset.mem_filter, Finset.mem_univ, true_and] at hC
  by_cases hi : i ∈ B
  · simp [projC, hi, hC i hi]
  · simp [projC, mergeJ, hi]

/-- Sum over all multi-indices = double sum over the two supports. -/
lemma sum_split {M : Type*} [AddCommMonoid M] (f : (Fin N → Fin (J + 1)) → M) :
    ∑ j, f j = ∑ jB ∈ SB B, ∑ jC ∈ SC B, f (mergeJ B jB jC) := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij' (fun j _ => (projB B j, projC B j)) (fun p _ => mergeJ B p.1 p.2)
    ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_product.mpr ⟨projB_mem B j, projC_mem B j⟩
  · intro p hp
    exact Finset.mem_univ _
  · intro j _; exact merge_proj B j
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    exact Prod.ext (projB_merge B h1 h2) (projC_merge B h1 h2)
  · intro j _; rw [merge_proj]

/-- The factor at label `i` splits into a torus part and a Gaussian part. -/
lemma hybFactor_merge (e : ℕ → Torus d → ℝ) (he0 : e 0 = fun _ => 1) {jB jC : Fin N → Fin (J + 1)}
    (hB : jB ∈ SB B) (hC : jC ∈ SC B) (i : Fin N) (ω : Config N d × (Fin N → Fin J → ℝ)) :
    hybFactor e B i (mergeJ B jB jC i) ω = e (jB i) (ω.1 i) * gamF (jC i) (ω.2 i) := by
  simp only [SB, SC, Finset.mem_filter, Finset.mem_univ, true_and] at hB hC
  by_cases hi : i ∈ B
  · have h0 : jC i = 0 := hC i hi
    simp [hybFactor, mergeJ, hi, h0, gamF]
  · have h0 : jB i = 0 := hB i hi
    simp [hybFactor, mergeJ, hi, h0, gamF, he0]

/-- Torus part of a product. -/
def torusFac (e : ℕ → Torus d → ℝ) (jB : Fin N → Fin (J + 1)) (x : Config N d) : ℝ :=
  ∏ i, e (jB i) (x i)

/-- Gaussian part of a product. -/
def gaussFac (jC : Fin N → Fin (J + 1)) (y : Fin N → Fin J → ℝ) : ℝ := ∏ i, gamF (jC i) (y i)

/-- The Gaussian polynomial `P_{jB}(y)`. -/
def Pfun (c : (Fin N → Fin (J + 1)) → ℝ) (jB : Fin N → Fin (J + 1)) (y : Fin N → Fin J → ℝ) : ℝ :=
  ∑ jC ∈ SC B, c (mergeJ B jB jC) * gaussFac jC y

/-- **Decomposition.** -/
theorem hybPoly_eq (e : ℕ → Torus d → ℝ) (he0 : e 0 = fun _ => 1)
    (c : (Fin N → Fin (J + 1)) → ℝ) (x : Config N d) (y : Fin N → Fin J → ℝ) :
    hybPoly e c B (x, y) = ∑ jB ∈ SB B, torusFac e jB x * Pfun B c jB y := by
  unfold hybPoly
  rw [sum_split B]
  refine Finset.sum_congr rfl fun jB hjB => ?_
  unfold Pfun
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun jC hjC => ?_
  have : ∏ i, hybFactor e B i (mergeJ B jB jC i) (x, y) = torusFac e jB x * gaussFac jC y := by
    unfold torusFac gaussFac
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hybFactor_merge B e he0 hjB hjC i (x, y)
  rw [this]; ring

end SharpLSI.FL.Hyb

end
