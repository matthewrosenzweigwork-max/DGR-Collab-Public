import Mathlib

/-!
# A diagonal argument for double sequences in a first-countable space
-/

open Filter Topology

namespace SharpLSI.FL

/-- If `x n N → y n` as `N → ∞` for each `n`, and `y n → z`, then there is `φ` with
`x (φ N) N → z`. -/
theorem exists_diag_tendsto {α : Type*} [TopologicalSpace α] [FirstCountableTopology α]
    (x : ℕ → ℕ → α) (y : ℕ → α) (z : α) (hx : ∀ n, Tendsto (x n) atTop (𝓝 (y n)))
    (hy : Tendsto y atTop (𝓝 z)) : ∃ φ : ℕ → ℕ, Tendsto (fun N => x (φ N) N) atTop (𝓝 z) := by
  obtain ⟨U, hU⟩ := (𝓝 z).exists_antitone_basis
  have hint : ∀ m, interior (U m) ∈ 𝓝 z := fun m =>
    isOpen_interior.mem_nhds ((mem_interior_iff_mem_nhds.2 (hU.mem m)))
  -- choose `n m` with `y (n m) ∈ interior (U m)`
  have hn : ∀ m, ∃ n, y n ∈ interior (U m) := fun m => (hy.eventually (hint m)).exists
  choose n hn using hn
  -- choose `N0 m` with `x (n m) N ∈ U m` for `N ≥ N0 m`
  have hN : ∀ m, ∃ N0, ∀ N ≥ N0, x (n m) N ∈ U m := fun m => by
    have := (hx (n m)).eventually (isOpen_interior.mem_nhds (hn m))
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 this
    exact ⟨N0, fun N hN => interior_subset (hN0 N hN)⟩
  choose N0 hN0 using hN
  -- monotone thresholds
  set T : ℕ → ℕ := fun m => m + ∑ j ∈ Finset.range (m + 1), N0 j with hT
  have hTmono : Monotone T := fun a b hab => by
    simp only [hT]
    have : ∑ j ∈ Finset.range (a + 1), N0 j ≤ ∑ j ∈ Finset.range (b + 1), N0 j :=
      Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    omega
  have hTge : ∀ m, N0 m ≤ T m := fun m => by
    simp only [hT]
    have := Finset.single_le_sum (f := N0) (fun _ _ => Nat.zero_le _)
      (show m ∈ Finset.range (m + 1) by simp)
    omega
  have hTm : ∀ m, m ≤ T m := fun m => by simp [hT]
  refine ⟨fun N => n (Nat.findGreatest (fun m => T m ≤ N) N), ?_⟩
  rw [hU.tendsto_right_iff]
  intro m0 _
  rw [eventually_atTop]
  refine ⟨T m0, fun N hN => ?_⟩
  set P : ℕ → Prop := fun m => T m ≤ N with hP
  have hm0N : m0 ≤ N := (hTm m0).trans hN
  have hge : m0 ≤ Nat.findGreatest P N := Nat.le_findGreatest hm0N hN
  have hspec : P (Nat.findGreatest P N) := Nat.findGreatest_spec (P := P) hm0N hN
  have hxm : x (n (Nat.findGreatest P N)) N ∈ U (Nat.findGreatest P N) :=
    hN0 _ N ((hTge _).trans hspec)
  exact hU.antitone hge hxm

end SharpLSI.FL
