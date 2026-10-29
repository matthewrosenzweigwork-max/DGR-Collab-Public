import DGPS.Foundations.Torus

/-!
# Periodic Hölder spaces on the circle as Banach spaces (FOU017)

For `0 < α < 1` and `k : ℕ`, `PH α k` is the space of `1`-periodic real functions `f : ℝ → ℝ`
(equivalently functions on the circle `ℝ/ℤ = 𝕋¹`) of class `C^{k,α}`, with the norm
`‖f‖ = ∑_{j ≤ k} ‖∂ʲ f‖_∞ + [∂ᵏ f]_α`.
-/

open Function

namespace DGPS.Analysis.PeriodicHolder

/-! ### Sup norm and Hölder seminorm -/

/-- The sup norm of a real function (junk value `0` for unbounded functions). -/
noncomputable def supNorm (g : ℝ → ℝ) : ℝ := ⨆ x, |g x|

/-- `g` is bounded. -/
def Bdd (g : ℝ → ℝ) : Prop := ∃ M : ℝ, ∀ x, |g x| ≤ M

theorem supNorm_nonneg (g : ℝ → ℝ) : 0 ≤ supNorm g := Real.iSup_nonneg fun _ => abs_nonneg _

theorem Bdd.abs_le_supNorm {g : ℝ → ℝ} (h : Bdd g) (x : ℝ) : |g x| ≤ supNorm g := by
  obtain ⟨M, hM⟩ := h
  exact le_ciSup (f := fun x => |g x|) ⟨M, by rintro _ ⟨y, rfl⟩; exact hM y⟩ x

theorem supNorm_le {g : ℝ → ℝ} {M : ℝ} (h : ∀ x, |g x| ≤ M) : supNorm g ≤ M := ciSup_le h

/-- The α-Hölder seminorm `[g]_α = sup_{x ≠ y} |g x - g y| / |x - y|^α` (junk if unbounded). -/
noncomputable def holderSeminorm (α : ℝ) (g : ℝ → ℝ) : ℝ :=
  ⨆ p : ℝ × ℝ, |g p.1 - g p.2| / |p.1 - p.2| ^ α

/-- `g` is α-Hölder continuous with some finite constant. -/
def HolderBdd (α : ℝ) (g : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, |g x - g y| ≤ C * |x - y| ^ α

theorem holderSeminorm_nonneg (α : ℝ) (g : ℝ → ℝ) : 0 ≤ holderSeminorm α g :=
  Real.iSup_nonneg fun _ => div_nonneg (abs_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)

theorem holderSeminorm_le {α : ℝ} {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, |g x - g y| ≤ C * |x - y| ^ α) : holderSeminorm α g ≤ C := by
  refine ciSup_le fun p => ?_
  by_cases hp : p.1 = p.2
  · simp [hp, hC]
  · have : 0 < |p.1 - p.2| ^ α := Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr hp)) _
    rw [div_le_iff₀ this]
    exact h _ _

theorem HolderBdd.le_holderSeminorm_mul {α : ℝ} {g : ℝ → ℝ} (h : HolderBdd α g) (x y : ℝ) :
    |g x - g y| ≤ holderSeminorm α g * |x - y| ^ α := by
  obtain ⟨C, hC, hg⟩ := h
  by_cases hxy : x = y
  · subst hxy
    simp only [sub_self, abs_zero]
    exact mul_nonneg (holderSeminorm_nonneg _ _) (Real.rpow_nonneg le_rfl _)
  · have hpos : 0 < |x - y| ^ α := Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr hxy)) _
    have hb : BddAbove (Set.range fun p : ℝ × ℝ => |g p.1 - g p.2| / |p.1 - p.2| ^ α) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨p, rfl⟩
      by_cases hp : p.1 = p.2
      · simp [hp, hC]
      · have : 0 < |p.1 - p.2| ^ α := Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr hp)) _
        rw [div_le_iff₀ this]
        exact hg _ _
    have := le_ciSup hb (x, y)
    rw [← div_le_iff₀ hpos]
    exact this

theorem HolderBdd.of_le {α : ℝ} {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, |g x - g y| ≤ C * |x - y| ^ α) : HolderBdd α g := ⟨C, hC, h⟩

/-! ### The recursive regularity predicate and norm -/

/-- `IsPH α k f`: `f` is `1`-periodic, `k` times differentiable, and its `k`-th derivative is
α-Hölder continuous. -/
noncomputable def IsPH (α : ℝ) : ℕ → (ℝ → ℝ) → Prop
  | 0, f => Periodic f 1 ∧ Continuous f ∧ HolderBdd α f
  | k + 1, f => Periodic f 1 ∧ Differentiable ℝ f ∧ IsPH α k (deriv f)

/-- The norm `∑_{j ≤ k} ‖∂ʲ f‖_∞ + [∂ᵏ f]_α`, defined recursively. -/
noncomputable def phNorm (α : ℝ) : ℕ → (ℝ → ℝ) → ℝ
  | 0, f => supNorm f + holderSeminorm α f
  | k + 1, f => supNorm f + phNorm α k (deriv f)

section Basic

variable {α : ℝ}

theorem IsPH.periodic : ∀ {k : ℕ} {f : ℝ → ℝ}, IsPH α k f → Periodic f 1
  | 0, _, h => h.1
  | _ + 1, _, h => h.1

theorem IsPH.continuous : ∀ {k : ℕ} {f : ℝ → ℝ}, IsPH α k f → Continuous f
  | 0, _, h => h.2.1
  | _ + 1, _, h => h.2.1.continuous

theorem periodic_bdd {f : ℝ → ℝ} (hp : Periodic f 1) (hc : Continuous f) : Bdd f := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ one_pos x
  rw [hxy]
  exact (hM y ⟨hy.1, hy.2.le⟩).trans (le_max_left _ _)

theorem IsPH.bdd {k : ℕ} {f : ℝ → ℝ} (h : IsPH α k f) : Bdd f :=
  periodic_bdd h.periodic h.continuous

theorem periodic_deriv {f : ℝ → ℝ} (hp : Periodic f 1) : Periodic (deriv f) 1 := by
  intro x
  have h := deriv_comp_add_const (f := f) (a := 1) (x := x)
  have e : (fun x => f (x + 1)) = f := funext hp
  rw [e] at h
  exact h.symm

theorem isPH_const (k : ℕ) (c : ℝ) : IsPH α k (fun _ => c) := by
  induction k generalizing c with
  | zero =>
    exact ⟨fun x => rfl, continuous_const, ⟨0, le_rfl, fun x y => by simp⟩⟩
  | succ k ih =>
    refine ⟨fun x => rfl, differentiable_const c, ?_⟩
    have : deriv (fun _ : ℝ => c) = fun _ => (0 : ℝ) := by ext x; simp
    rw [this]
    exact ih 0

theorem IsPH.add : ∀ {k : ℕ} {f g : ℝ → ℝ}, IsPH α k f → IsPH α k g → IsPH α k (f + g)
  | 0, f, g, hf, hg => by
    obtain ⟨C₁, h₁, hC₁⟩ := hf.2.2
    obtain ⟨C₂, h₂, hC₂⟩ := hg.2.2
    refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, C₁ + C₂, add_nonneg h₁ h₂, fun x y => ?_⟩
    have := abs_add_le (f x - f y) (g x - g y)
    simp only [Pi.add_apply]
    calc |f x + g x - (f y + g y)| = |(f x - f y) + (g x - g y)| := by ring_nf
      _ ≤ _ := this
      _ ≤ _ := by nlinarith [hC₁ x y, hC₂ x y]
  | k + 1, f, g, hf, hg => by
    have hd : deriv (f + g) = deriv f + deriv g := by
      ext x; exact deriv_add (hf.2.1 x) (hg.2.1 x)
    exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, by rw [hd]; exact IsPH.add hf.2.2 hg.2.2⟩

theorem IsPH.smul : ∀ {k : ℕ} {f : ℝ → ℝ} (c : ℝ), IsPH α k f → IsPH α k (c • f)
  | 0, f, c, hf => by
    obtain ⟨C₁, h₁, hC₁⟩ := hf.2.2
    refine ⟨hf.1.smul c, hf.2.1.const_smul c, |c| * C₁, mul_nonneg (abs_nonneg _) h₁,
      fun x y => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    calc |c * f x - c * f y| = |c| * |f x - f y| := by rw [← mul_sub, abs_mul]
      _ ≤ |c| * (C₁ * |x - y| ^ α) := mul_le_mul_of_nonneg_left (hC₁ x y) (abs_nonneg _)
      _ = _ := by ring
  | k + 1, f, c, hf => by
    have hd : deriv (c • f) = c • deriv f := by
      ext x; exact deriv_const_smul c (hf.2.1 x)
    exact ⟨hf.1.smul c, hf.2.1.const_smul c, by rw [hd]; exact IsPH.smul c hf.2.2⟩

theorem IsPH.neg {k : ℕ} {f : ℝ → ℝ} (hf : IsPH α k f) : IsPH α k (-f) := by
  have := hf.smul (-1)
  simpa using this

theorem IsPH.sub {k : ℕ} {f g : ℝ → ℝ} (hf : IsPH α k f) (hg : IsPH α k g) :
    IsPH α k (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-! ### Norm facts -/

theorem phNorm_nonneg : ∀ (k : ℕ) (f : ℝ → ℝ), 0 ≤ phNorm α k f
  | 0, _ => add_nonneg (supNorm_nonneg _) (holderSeminorm_nonneg _ _)
  | k + 1, _ => add_nonneg (supNorm_nonneg _) (phNorm_nonneg k _)

theorem supNorm_le_phNorm : ∀ (k : ℕ) (f : ℝ → ℝ), supNorm f ≤ phNorm α k f
  | 0, f => by simp [phNorm, holderSeminorm_nonneg]
  | k + 1, f => by simp [phNorm, phNorm_nonneg]

theorem supNorm_add_le {f g : ℝ → ℝ} (hf : Bdd f) (hg : Bdd g) :
    supNorm (f + g) ≤ supNorm f + supNorm g :=
  supNorm_le fun x => (abs_add_le _ _).trans (add_le_add (hf.abs_le_supNorm x) (hg.abs_le_supNorm x))

theorem supNorm_smul_le {f : ℝ → ℝ} (hf : Bdd f) (c : ℝ) : supNorm (c • f) ≤ |c| * supNorm f :=
  supNorm_le fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.abs_le_supNorm x) (abs_nonneg _)

theorem holderSeminorm_add_le {f g : ℝ → ℝ} (hf : HolderBdd α f) (hg : HolderBdd α g) :
    holderSeminorm α (f + g) ≤ holderSeminorm α f + holderSeminorm α g := by
  refine holderSeminorm_le (add_nonneg (holderSeminorm_nonneg _ _) (holderSeminorm_nonneg _ _))
    fun x y => ?_
  have h1 := hf.le_holderSeminorm_mul x y
  have h2 := hg.le_holderSeminorm_mul x y
  simp only [Pi.add_apply]
  calc |f x + g x - (f y + g y)| = |(f x - f y) + (g x - g y)| := by ring_nf
    _ ≤ |f x - f y| + |g x - g y| := abs_add_le _ _
    _ ≤ _ := by nlinarith

theorem holderSeminorm_smul_le {f : ℝ → ℝ} (hf : HolderBdd α f) (c : ℝ) :
    holderSeminorm α (c • f) ≤ |c| * holderSeminorm α f := by
  refine holderSeminorm_le (mul_nonneg (abs_nonneg _) (holderSeminorm_nonneg _ _)) fun x y => ?_
  have h1 := hf.le_holderSeminorm_mul x y
  simp only [Pi.smul_apply, smul_eq_mul]
  calc |c * f x - c * f y| = |c| * |f x - f y| := by rw [← mul_sub, abs_mul]
    _ ≤ |c| * (holderSeminorm α f * |x - y| ^ α) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = _ := by ring

theorem phNorm_add_le : ∀ {k : ℕ} {f g : ℝ → ℝ}, IsPH α k f → IsPH α k g →
    phNorm α k (f + g) ≤ phNorm α k f + phNorm α k g
  | 0, f, g, hf, hg => by
    have := supNorm_add_le hf.bdd hg.bdd
    have := holderSeminorm_add_le hf.2.2 hg.2.2
    simp only [phNorm]; linarith
  | k + 1, f, g, hf, hg => by
    have hd : deriv (f + g) = deriv f + deriv g := by
      ext x; exact deriv_add (hf.2.1 x) (hg.2.1 x)
    have h1 := supNorm_add_le hf.bdd hg.bdd
    have h2 := phNorm_add_le hf.2.2 hg.2.2
    simp only [phNorm, hd]; linarith

theorem phNorm_smul_le : ∀ {k : ℕ} {f : ℝ → ℝ} (c : ℝ), IsPH α k f →
    phNorm α k (c • f) ≤ |c| * phNorm α k f
  | 0, f, c, hf => by
    have h1 := supNorm_smul_le hf.bdd c
    have h2 := holderSeminorm_smul_le hf.2.2 c
    simp only [phNorm]; nlinarith
  | k + 1, f, c, hf => by
    have hd : deriv (c • f) = c • deriv f := by
      ext x; exact deriv_const_smul c (hf.2.1 x)
    have h1 := supNorm_smul_le hf.bdd c
    have h2 := phNorm_smul_le c hf.2.2
    simp only [phNorm, hd]; nlinarith

theorem phNorm_neg {k : ℕ} {f : ℝ → ℝ} (hf : IsPH α k f) : phNorm α k (-f) = phNorm α k f := by
  apply le_antisymm
  · have := phNorm_smul_le (-1) hf
    simpa using this
  · have := phNorm_smul_le (-1) hf.neg
    simpa using this

theorem eq_zero_of_phNorm_eq_zero {k : ℕ} {f : ℝ → ℝ} (hf : IsPH α k f)
    (h : phNorm α k f = 0) : f = 0 := by
  have h1 := supNorm_le_phNorm (α := α) k f
  have h2 := hf.bdd
  ext x
  have := h2.abs_le_supNorm x
  have h3 : |f x| ≤ 0 := by linarith
  simpa using abs_nonpos_iff.mp h3

end Basic


section Mult

variable {α : ℝ}

theorem holder_of_lip {u : ℝ → ℝ} {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (hlip : ∀ x y, |u x - u y| ≤ L * |x - y|) (hbd : ∀ x, |u x| ≤ M) :
    ∀ x y, |u x - u y| ≤ (L + 2 * M) * |x - y| ^ α := by
  intro x y
  have hb : |u x - u y| ≤ 2 * M :=
    calc |u x - u y| ≤ |u x| + |u y| := abs_sub _ _
      _ ≤ M + M := add_le_add (hbd x) (hbd y)
      _ = 2 * M := by ring
  have ht0 : 0 ≤ |x - y| := abs_nonneg _
  have hpa : 0 ≤ |x - y| ^ α := Real.rpow_nonneg ht0 _
  by_cases h1 : |x - y| ≤ 1
  · have : |x - y| ≤ |x - y| ^ α := by
      rcases ht0.eq_or_lt with h | h
      · rw [← h]; exact Real.rpow_nonneg le_rfl _
      · have := Real.rpow_le_rpow_of_exponent_ge h h1 hα1
        simpa using this
    calc |u x - u y| ≤ L * |x - y| := hlip x y
      _ ≤ L * |x - y| ^ α := mul_le_mul_of_nonneg_left this hL
      _ ≤ (L + 2 * M) * |x - y| ^ α := by nlinarith
  · rw [not_le] at h1
    have : 1 ≤ |x - y| ^ α := Real.one_le_rpow h1.le hα0
    calc |u x - u y| ≤ 2 * M := hb
      _ ≤ 2 * M * |x - y| ^ α := by nlinarith
      _ ≤ (L + 2 * M) * |x - y| ^ α := by nlinarith

theorem lip_bound {f : ℝ → ℝ} (hd : Differentiable ℝ f) (hb : Bdd (deriv f)) (x y : ℝ) :
    |f x - f y| ≤ supNorm (deriv f) * |x - y| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := f) (s := Set.univ)
    (C := supNorm (deriv f)) (fun z _ => hd z) (fun z _ => by
      rw [Real.norm_eq_abs]; exact hb.abs_le_supNorm z) convex_univ (Set.mem_univ y)
    (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

theorem holderSeminorm_le_succ (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {f : ℝ → ℝ}
    (hd : Differentiable ℝ f) (hb : Bdd f) (hb' : Bdd (deriv f)) :
    holderSeminorm α f ≤ supNorm (deriv f) + 2 * supNorm f :=
  holderSeminorm_le (add_nonneg (supNorm_nonneg _) (mul_nonneg two_pos.le (supNorm_nonneg _)))
    (holder_of_lip (supNorm_nonneg _) (supNorm_nonneg _) hα0 hα1 (lip_bound hd hb')
      hb.abs_le_supNorm)

theorem IsPH.of_succ (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∀ {k : ℕ} {f : ℝ → ℝ}, IsPH α (k + 1) f → IsPH α k f
  | 0, f, h => by
    obtain ⟨hp, hd, h0⟩ := h
    have hb : Bdd f := periodic_bdd hp hd.continuous
    refine ⟨hp, hd.continuous, HolderBdd.of_le
      (C := supNorm (deriv f) + 2 * supNorm f) (add_nonneg (supNorm_nonneg _)
      (mul_nonneg two_pos.le (supNorm_nonneg _))) ?_⟩
    exact holder_of_lip (supNorm_nonneg _) (supNorm_nonneg _) hα0 hα1 (lip_bound hd h0.bdd)
      hb.abs_le_supNorm
  | k + 1, f, h => ⟨h.1, h.2.1, IsPH.of_succ hα0 hα1 h.2.2⟩

theorem phNorm_le_succ (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∀ {k : ℕ} {f : ℝ → ℝ}, IsPH α (k + 1) f → phNorm α k f ≤ 3 * phNorm α (k + 1) f
  | 0, f, h => by
    obtain ⟨hp, hd, h0⟩ := h
    have hb : Bdd f := periodic_bdd hp hd.continuous
    have := holderSeminorm_le_succ hα0 hα1 hd hb h0.bdd
    have h2 := holderSeminorm_nonneg α (deriv f)
    have h3 := supNorm_nonneg f
    have h4 := supNorm_nonneg (deriv f)
    simp only [phNorm]; linarith
  | k + 1, f, h => by
    have ih := phNorm_le_succ hα0 hα1 h.2.2
    have h3 := supNorm_nonneg f
    simp only [phNorm] at ih ⊢; linarith

theorem mul_aux (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ f g : ℝ → ℝ, IsPH α k f → IsPH α k g →
      IsPH α k (f * g) ∧ phNorm α k (f * g) ≤ C * (phNorm α k f * phNorm α k g)
  | 0 => by
    refine ⟨1, zero_le_one, fun f g hf hg => ?_⟩
    have hfb := hf.bdd
    have hgb := hg.bdd
    have hfH := hf.2.2
    have hgH := hg.2.2
    have key : ∀ x y, |(f * g) x - (f * g) y| ≤
        (supNorm f * holderSeminorm α g + supNorm g * holderSeminorm α f) * |x - y| ^ α := by
      intro x y
      have h1 := hfH.le_holderSeminorm_mul x y
      have h2 := hgH.le_holderSeminorm_mul x y
      have e : (f * g) x - (f * g) y = f x * (g x - g y) + g y * (f x - f y) := by
        simp only [Pi.mul_apply]; ring
      rw [e]
      calc _ ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
        _ = |f x| * |g x - g y| + |g y| * |f x - f y| := by rw [abs_mul, abs_mul]
        _ ≤ supNorm f * (holderSeminorm α g * |x - y| ^ α) +
            supNorm g * (holderSeminorm α f * |x - y| ^ α) :=
          add_le_add (mul_le_mul (hfb.abs_le_supNorm x) h2 (abs_nonneg _) (supNorm_nonneg _))
            (mul_le_mul (hgb.abs_le_supNorm y) h1 (abs_nonneg _) (supNorm_nonneg _))
        _ = _ := by ring
    have hC : 0 ≤ supNorm f * holderSeminorm α g + supNorm g * holderSeminorm α f :=
      add_nonneg (mul_nonneg (supNorm_nonneg _) (holderSeminorm_nonneg _ _))
        (mul_nonneg (supNorm_nonneg _) (holderSeminorm_nonneg _ _))
    refine ⟨⟨hf.1.mul hg.1, hf.2.1.mul hg.2.1, HolderBdd.of_le hC key⟩, ?_⟩
    have hs : supNorm (f * g) ≤ supNorm f * supNorm g := supNorm_le fun x => by
      simp only [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hfb.abs_le_supNorm x) (hgb.abs_le_supNorm x) (abs_nonneg _)
        (supNorm_nonneg _)
    have hh := holderSeminorm_le hC key
    simp only [phNorm]
    nlinarith [holderSeminorm_nonneg α f, holderSeminorm_nonneg α g, supNorm_nonneg f,
      supNorm_nonneg g, mul_nonneg (holderSeminorm_nonneg α f) (holderSeminorm_nonneg α g)]
  | k + 1 => by
    obtain ⟨C, hC0, hC⟩ := mul_aux hα0 hα1 k
    refine ⟨1 + 6 * C, by positivity, fun f g hf hg => ?_⟩
    have hfk : IsPH α k f := hf.of_succ hα0 hα1
    have hgk : IsPH α k g := hg.of_succ hα0 hα1
    have hd : deriv (f * g) = deriv f * g + f * deriv g := by
      ext x; exact deriv_mul (hf.2.1 x) (hg.2.1 x)
    obtain ⟨m1, n1⟩ := hC _ _ hf.2.2 hgk
    obtain ⟨m2, n2⟩ := hC _ _ hfk hg.2.2
    refine ⟨⟨hf.1.mul hg.1, hf.2.1.mul hg.2.1, by rw [hd]; exact m1.add m2⟩, ?_⟩
    have h3 := phNorm_add_le m1 m2
    have hs : supNorm (f * g) ≤ supNorm f * supNorm g := supNorm_le fun x => by
      simp only [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hf.bdd.abs_le_supNorm x) (hg.bdd.abs_le_supNorm x) (abs_nonneg _)
        (supNorm_nonneg _)
    have hNf : 0 ≤ phNorm α (k + 1) f := phNorm_nonneg _ _
    have hNg : 0 ≤ phNorm α (k + 1) g := phNorm_nonneg _ _
    have a1 : phNorm α k (deriv f) ≤ phNorm α (k + 1) f := by
      simp only [phNorm]; linarith [supNorm_nonneg f]
    have b1 : phNorm α k (deriv g) ≤ phNorm α (k + 1) g := by
      simp only [phNorm]; linarith [supNorm_nonneg g]
    have a2 := phNorm_le_succ hα0 hα1 hf
    have b2 := phNorm_le_succ hα0 hα1 hg
    have a3 : supNorm f ≤ phNorm α (k + 1) f := supNorm_le_phNorm _ _
    have b3 : supNorm g ≤ phNorm α (k + 1) g := supNorm_le_phNorm _ _
    have p1 : phNorm α k (deriv f * g) ≤ C * (phNorm α (k + 1) f * (3 * phNorm α (k + 1) g)) :=
      n1.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul a1 b2 (phNorm_nonneg _ _) hNf) hC0)
    have p2 : phNorm α k (f * deriv g) ≤ C * ((3 * phNorm α (k + 1) f) * phNorm α (k + 1) g) :=
      n2.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul a2 b1 (phNorm_nonneg _ _) (by positivity)) hC0)
    have p3 : supNorm f * supNorm g ≤ phNorm α (k + 1) f * phNorm α (k + 1) g :=
      mul_le_mul a3 b3 (supNorm_nonneg _) hNf
    simp only [phNorm, hd]
    simp only [phNorm] at p1 p2 p3 a1 b1 a2 b2 a3 b3 hNf hNg
    nlinarith

theorem IsPH.mul (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {k : ℕ} {f g : ℝ → ℝ} (hf : IsPH α k f)
    (hg : IsPH α k g) : IsPH α k (f * g) := by
  obtain ⟨C, _, h⟩ := mul_aux hα0 hα1 k
  exact (h f g hf hg).1

theorem exists_pos_lower {f : ℝ → ℝ} (hp : Periodic f 1) (hc : Continuous f)
    (hpos : ∀ x, 0 < f x) : ∃ m, 0 < m ∧ ∀ x, m ≤ f x := by
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    ⟨0, by simp⟩ hc.continuousOn
  refine ⟨f x0, hpos x0, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ one_pos x
  rw [hxy]
  exact hmin ⟨hy.1, hy.2.le⟩

theorem IsPH.inv (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∀ {k : ℕ} {f : ℝ → ℝ}, IsPH α k f → (∀ x, 0 < f x) → IsPH α k (fun x => (f x)⁻¹)
  | 0, f, hf, hpos => by
    obtain ⟨m, hm, hmf⟩ := exists_pos_lower hf.1 hf.2.1 hpos
    obtain ⟨C, hC0, hC⟩ := hf.2.2
    refine ⟨?_, hf.2.1.inv₀ fun x => (hpos x).ne', C / m ^ 2, by positivity, fun x y => ?_⟩
    · intro x; simp only [hf.1 x]
    · have hx := hpos x
      have hy := hpos y
      rw [inv_sub_inv hx.ne' hy.ne', abs_div, abs_mul, abs_of_pos hx, abs_of_pos hy,
        div_le_iff₀ (mul_pos hx hy), abs_sub_comm]
      have h2 : m ^ 2 ≤ f x * f y := by nlinarith [hmf x, hmf y]
      have h3 : 0 ≤ |x - y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
      calc |f x - f y| ≤ C * |x - y| ^ α := hC x y
        _ = C / m ^ 2 * |x - y| ^ α * m ^ 2 := by field_simp
        _ ≤ C / m ^ 2 * |x - y| ^ α * (f x * f y) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  | k + 1, f, hf, hpos => by
    have hfk : IsPH α k f := hf.of_succ hα0 hα1
    have ihk := IsPH.inv hα0 hα1 hfk hpos
    have hdiff : Differentiable ℝ (fun x => (f x)⁻¹) := hf.2.1.inv fun x => (hpos x).ne'
    have hd : deriv (fun x => (f x)⁻¹) =
        -(deriv f * ((fun x => (f x)⁻¹) * (fun x => (f x)⁻¹))) := by
      ext x
      have hh : HasDerivAt (fun y => (f y)⁻¹) (-deriv f x / f x ^ 2) x :=
        (hf.2.1 x).hasDerivAt.inv (hpos x).ne'
      rw [hh.deriv]
      have := (hpos x).ne'
      simp only [Pi.neg_apply, Pi.mul_apply]
      field_simp
    refine ⟨?_, hdiff, ?_⟩
    · intro x; simp only [hf.1 x]
    · rw [hd]
      exact (hf.2.2.mul hα0 hα1 (ihk.mul hα0 hα1 ihk)).neg

end Mult


/-! ### Completeness (function level) -/

section Complete

open Filter Topology

variable {α : ℝ}

theorem exists_uniform_limit {f : ℕ → ℝ → ℝ}
    (h : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ x, |f n x - f m x| ≤ ε) :
    ∃ F : ℝ → ℝ, (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) ∧
      ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |f n x - F x| ≤ ε := by
  have hc : ∀ x, CauchySeq fun n => f n x := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    exact ⟨N, fun m hm n hn => by rw [Real.dist_eq]; linarith [hN m hm n hn x]⟩
  choose F hF using fun x => cauchySeq_tendsto_of_complete (hc x)
  refine ⟨F, hF, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := h ε hε
  refine ⟨N, fun n hn x => ?_⟩
  have : Tendsto (fun m => |f n x - f m x|) atTop (𝓝 |f n x - F x|) :=
    (tendsto_const_nhds.sub (hF x)).abs
  exact le_of_tendsto this (eventually_atTop.mpr ⟨N, fun m hm => hN n hn m hm x⟩)

theorem periodic_of_tendsto {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} (hf : ∀ n, Periodic (f n) 1)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x))) : Periodic F 1 := fun x => by
  have h2 : Tendsto (fun n => f n (x + 1)) atTop (𝓝 (F x)) := by
    have : (fun n => f n (x + 1)) = fun n => f n x := funext fun n => hf n x
    rw [this]; exact hlim x
  exact tendsto_nhds_unique (hlim (x + 1)) h2

theorem complete_aux : ∀ (k : ℕ) (f : ℕ → ℝ → ℝ), (∀ n, IsPH α k (f n)) →
    (∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, phNorm α k (f n - f m) < ε) →
    ∃ F, IsPH α k F ∧ ∀ ε > 0, ∃ N, ∀ n ≥ N, phNorm α k (f n - F) < ε
  | 0, f, hf, hC => by
    have hsup : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ x, |f n x - f m x| ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hC ε hε
      refine ⟨N, fun n hn m hm x => ?_⟩
      have h1 := ((hf n).sub (hf m)).bdd.abs_le_supNorm x
      have h2 := supNorm_le_phNorm (α := α) 0 (f n - f m)
      have h3 := hN n hn m hm
      simp only [Pi.sub_apply] at h1
      linarith
    obtain ⟨F, hlim, hunif⟩ := exists_uniform_limit hsup
    have hhol : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x y,
        |(f n x - F x) - (f n y - F y)| ≤ ε * |x - y| ^ α := by
      intro ε hε
      obtain ⟨N, hN⟩ := hC ε hε
      refine ⟨N, fun n hn x y => ?_⟩
      have key : ∀ m ≥ N, |(f n x - f m x) - (f n y - f m y)| ≤ ε * |x - y| ^ α := by
        intro m hm
        have h1 := ((hf n).sub (hf m)).2.2.le_holderSeminorm_mul x y
        have h2 : holderSeminorm α (f n - f m) ≤ phNorm α 0 (f n - f m) := by
          simp only [phNorm]; linarith [supNorm_nonneg (f n - f m)]
        have h3 := hN n hn m hm
        have h4 : 0 ≤ |x - y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
        simp only [Pi.sub_apply] at h1
        calc _ ≤ holderSeminorm α (f n - f m) * |x - y| ^ α := h1
          _ ≤ ε * |x - y| ^ α := mul_le_mul_of_nonneg_right (by linarith) h4
      have : Tendsto (fun m => |(f n x - f m x) - (f n y - f m y)|) atTop
          (𝓝 |(f n x - F x) - (f n y - F y)|) :=
        ((tendsto_const_nhds.sub (hlim x)).sub (tendsto_const_nhds.sub (hlim y))).abs
      exact le_of_tendsto this (eventually_atTop.mpr ⟨N, key⟩)
    have hFper : Periodic F 1 := periodic_of_tendsto (fun n => (hf n).periodic) hlim
    have hFc : Continuous F := by
      refine TendstoUniformly.continuous (F := f) (p := atTop) ?_
        (Eventually.of_forall fun n => (hf n).continuous).frequently
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
      filter_upwards [eventually_ge_atTop N] with n hn x
      rw [Real.dist_eq, abs_sub_comm]; linarith [hN n hn x]
    have hFH : HolderBdd α F := by
      obtain ⟨N, hN⟩ := hhol 1 one_pos
      obtain ⟨C, hC0, hCf⟩ := (hf N).2.2
      refine ⟨C + 1, by linarith, fun x y => ?_⟩
      have h1 := hN N le_rfl x y
      have h2 := hCf x y
      calc |F x - F y| = |(f N x - f N y) - ((f N x - F x) - (f N y - F y))| := by
            congr 1; ring
        _ ≤ |f N x - f N y| + |(f N x - F x) - (f N y - F y)| := abs_sub _ _
        _ ≤ _ := by nlinarith
    refine ⟨F, ⟨hFper, hFc, hFH⟩, fun ε hε => ?_⟩
    obtain ⟨N1, h1⟩ := hunif (ε / 3) (by positivity)
    obtain ⟨N2, h2⟩ := hhol (ε / 3) (by positivity)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have hs : supNorm (f n - F) ≤ ε / 3 := supNorm_le fun x => by
      simpa only [Pi.sub_apply] using h1 n (le_trans (le_max_left _ _) hn) x
    have hh : holderSeminorm α (f n - F) ≤ ε / 3 := holderSeminorm_le (by positivity)
      fun x y => by
        simpa only [Pi.sub_apply] using h2 n (le_trans (le_max_right _ _) hn) x y
    simp only [phNorm]; linarith
  | k + 1, f, hf, hC => by
    have hgk : ∀ n, IsPH α k (deriv (f n)) := fun n => (hf n).2.2
    have hdsub : ∀ n m, deriv (f n - f m) = deriv (f n) - deriv (f m) := fun n m => by
      ext x; exact deriv_sub ((hf n).2.1 x) ((hf m).2.1 x)
    have hgC : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N,
        phNorm α k (deriv (f n) - deriv (f m)) < ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hC ε hε
      refine ⟨N, fun n hn m hm => ?_⟩
      have h3 := hN n hn m hm
      have : phNorm α (k + 1) (f n - f m) =
          supNorm (f n - f m) + phNorm α k (deriv (f n) - deriv (f m)) := by
        simp only [phNorm, hdsub]
      linarith [supNorm_nonneg (f n - f m)]
    obtain ⟨G, hG, hGlim⟩ := complete_aux k (fun n => deriv (f n)) hgk hgC
    have hsup : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ x, |f n x - f m x| ≤ ε := by
      intro ε hε
      obtain ⟨N, hN⟩ := hC ε hε
      refine ⟨N, fun n hn m hm x => ?_⟩
      have h1 := ((hf n).sub (hf m)).bdd.abs_le_supNorm x
      have h2 := supNorm_le_phNorm (α := α) (k + 1) (f n - f m)
      have h3 := hN n hn m hm
      simp only [Pi.sub_apply] at h1
      linarith
    obtain ⟨F, hlim, hunif⟩ := exists_uniform_limit hsup
    have hgunif : TendstoUniformly (fun n => deriv (f n)) G atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hGlim ε hε
      filter_upwards [eventually_ge_atTop N] with n hn x
      have h1 := ((hgk n).sub hG).bdd.abs_le_supNorm x
      have h2 := supNorm_le_phNorm (α := α) k (deriv (f n) - G)
      have h3 := hN n hn
      rw [Real.dist_eq, abs_sub_comm]
      simp only [Pi.sub_apply] at h1
      linarith
    have hderiv : ∀ x, HasDerivAt F (G x) x :=
      hasDerivAt_of_tendstoUniformly hgunif
        (Eventually.of_forall fun n x => ((hf n).2.1 x).hasDerivAt) hlim
    have hFd : Differentiable ℝ F := fun x => (hderiv x).differentiableAt
    have hFdG : deriv F = G := funext fun x => (hderiv x).deriv
    have hFper : Periodic F 1 := periodic_of_tendsto (fun n => (hf n).periodic) hlim
    refine ⟨F, ⟨hFper, hFd, by rw [hFdG]; exact hG⟩, fun ε hε => ?_⟩
    obtain ⟨N1, h1⟩ := hunif (ε / 2) (half_pos hε)
    obtain ⟨N2, h2⟩ := hGlim (ε / 2) (half_pos hε)
    refine ⟨max N1 N2, fun n hn => ?_⟩
    have hs : supNorm (f n - F) ≤ ε / 2 := supNorm_le fun x => by
      simpa only [Pi.sub_apply] using h1 n (le_trans (le_max_left _ _) hn) x
    have hd2 : deriv (f n - F) = deriv (f n) - G := by
      rw [← hFdG]; ext x; exact deriv_sub ((hf n).2.1 x) (hFd x)
    have := h2 n (le_trans (le_max_right _ _) hn)
    simp only [phNorm, hd2]; linarith

end Complete

/-! ### The Banach space -/

section Space

open Filter Topology

/-- The exponent hypothesis `0 < α < 1` as a class, so that instances can use it. -/
class HolderExponent (α : ℝ) : Prop where
  pos : 0 < α
  lt_one : α < 1

section NoExp

variable (α : ℝ)

theorem phNorm_zero (k : ℕ) : phNorm α k (0 : ℝ → ℝ) = 0 := by
  induction k with
  | zero =>
    have h1 : supNorm (0 : ℝ → ℝ) = 0 := by simp [supNorm]
    have h2 : holderSeminorm α (0 : ℝ → ℝ) = 0 := by simp [holderSeminorm]
    simp [phNorm, h1, h2]
  | succ k ih =>
    have h1 : supNorm (0 : ℝ → ℝ) = 0 := by simp [supNorm]
    have h2 : deriv (0 : ℝ → ℝ) = 0 := by ext x; simp
    simp [phNorm, h1, h2, ih]

/-- The sum formula for the norm: `∑_{j ≤ k} ‖∂^j f‖∞ + [∂^k f]_α`. -/
theorem phNorm_eq_sum (k : ℕ) (f : ℝ → ℝ) :
    phNorm α k f = (∑ j ∈ Finset.range (k + 1), supNorm (deriv^[j] f)) +
      holderSeminorm α (deriv^[k] f) := by
  induction k generalizing f with
  | zero => simp [phNorm]
  | succ k ih =>
    rw [phNorm, ih (deriv f), Finset.sum_range_succ' _ (k + 1)]
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id]
    ring

end NoExp

variable (α : ℝ) [HolderExponent α]

/-- The periodic `C^{k,α}` functions as a subalgebra of all functions `ℝ → ℝ`. -/
def phSubalgebra (k : ℕ) : Subalgebra ℝ (ℝ → ℝ) where
  carrier := {f | IsPH α k f}
  mul_mem' := fun hf hg =>
    IsPH.mul (HolderExponent.pos (α := α)).le (HolderExponent.lt_one (α := α)).le hf hg
  add_mem' := fun hf hg => IsPH.add hf hg
  algebraMap_mem' := fun r => isPH_const k r

/-- The Banach space of 1-periodic `C^{k,α}` functions on the circle. -/
def PH (k : ℕ) : Type := ↥(phSubalgebra α k)

instance (k : ℕ) : CommRing (PH α k) := inferInstanceAs (CommRing ↥(phSubalgebra α k))

instance (k : ℕ) : Algebra ℝ (PH α k) := inferInstanceAs (Algebra ℝ ↥(phSubalgebra α k))

variable {α}

/-- The underlying function of an element of `PH α k`. -/
def PH.val {k : ℕ} (f : PH α k) : ℝ → ℝ := Subtype.val f

/-- Build an element of `PH α k` from a function with the regularity property. -/
def PH.mk {k : ℕ} (f : ℝ → ℝ) (h : IsPH α k f) : PH α k := Subtype.mk f h

theorem PH.isPH {k : ℕ} (f : PH α k) : IsPH α k f.val := Subtype.property f

@[ext] theorem PH.ext {k : ℕ} {f g : PH α k} (h : f.val = g.val) : f = g := Subtype.ext h

@[simp] theorem PH.val_mk {k : ℕ} (f : ℝ → ℝ) (h : IsPH α k f) : (PH.mk f h).val = f := rfl
@[simp] theorem PH.val_add {k : ℕ} (f g : PH α k) : (f + g).val = f.val + g.val := rfl
@[simp] theorem PH.val_sub {k : ℕ} (f g : PH α k) : (f - g).val = f.val - g.val := rfl
@[simp] theorem PH.val_neg {k : ℕ} (f : PH α k) : (-f).val = -f.val := rfl
@[simp] theorem PH.val_mul {k : ℕ} (f g : PH α k) : (f * g).val = f.val * g.val := rfl
@[simp] theorem PH.val_zero {k : ℕ} : (0 : PH α k).val = 0 := rfl
@[simp] theorem PH.val_one {k : ℕ} : (1 : PH α k).val = 1 := rfl
@[simp] theorem PH.val_smul {k : ℕ} (c : ℝ) (f : PH α k) : (c • f).val = c • f.val := rfl

noncomputable instance (k : ℕ) : NormedAddCommGroup (PH α k) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun f => phNorm α k f.val
      map_zero' := phNorm_zero α k
      add_le' := fun f g => phNorm_add_le f.isPH g.isPH
      neg' := fun f => phNorm_neg f.isPH
      eq_zero_of_map_eq_zero' := fun f h => PH.ext (eq_zero_of_phNorm_eq_zero f.isPH h) }

theorem PH.norm_def {k : ℕ} (f : PH α k) : ‖f‖ = phNorm α k f.val := rfl

theorem PH.dist_def {k : ℕ} (f g : PH α k) : dist f g = phNorm α k (f.val - g.val) := dist_eq_norm f g

noncomputable instance (k : ℕ) : NormedSpace ℝ (PH α k) where
  norm_smul_le c f := by
    rw [PH.norm_def, PH.norm_def, Real.norm_eq_abs]
    exact phNorm_smul_le c f.isPH

instance (k : ℕ) : CompleteSpace (PH α k) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  rw [Metric.cauchySeq_iff] at hu
  obtain ⟨F, hF, hlim⟩ := complete_aux (α := α) k (fun n => (u n).val) (fun n => (u n).isPH) (by
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    exact ⟨N, fun n hn m hm => by have := hN n hn m hm; rwa [PH.dist_def] at this⟩)
  refine ⟨PH.mk F hF, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hlim ε hε
  exact ⟨N, fun n hn => by rw [PH.dist_def]; exact hN n hn⟩

end Space

/-! ### Banach algebra structure after rescaling the norm -/

section Alg

variable (α : ℝ) [HolderExponent α]

theorem PH.mul_bound (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : PH α k, ‖f * g‖ ≤ C * (‖f‖ * ‖g‖) := by
  obtain ⟨C, hC, h⟩ := mul_aux (HolderExponent.pos (α := α)).le
    (HolderExponent.lt_one (α := α)).le k
  exact ⟨C, hC, fun f g => (h f.val g.val f.isPH g.isPH).2⟩

/-- The constant by which the norm is rescaled to make it submultiplicative. -/
noncomputable def PH.scale (k : ℕ) : ℝ := (PH.mul_bound α k).choose + 1

theorem PH.one_le_scale (k : ℕ) : 1 ≤ PH.scale α k := by
  have := (PH.mul_bound α k).choose_spec.1
  unfold PH.scale; linarith

theorem PH.norm_mul_le_scale (k : ℕ) (f g : PH α k) : ‖f * g‖ ≤ PH.scale α k * (‖f‖ * ‖g‖) := by
  have h1 := (PH.mul_bound α k).choose_spec.2 f g
  have h2 : 0 ≤ ‖f‖ * ‖g‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  unfold PH.scale; nlinarith

/-- A type synonym for `PH α k` carrying the rescaled, submultiplicative norm. -/
def PHAlg (k : ℕ) : Type := PH α k

variable {α}

/-- Identity from the rescaled model back to `PH`. -/
def PHAlg.toPH {k : ℕ} (f : PHAlg α k) : PH α k := f

/-- Identity from `PH` into the rescaled model. -/
def PHAlg.ofPH {k : ℕ} (f : PH α k) : PHAlg α k := f

variable (α)

instance (k : ℕ) : CommRing (PHAlg α k) := inferInstanceAs (CommRing (PH α k))

instance (k : ℕ) : Algebra ℝ (PHAlg α k) := inferInstanceAs (Algebra ℝ (PH α k))

variable {α}

@[simp] theorem PHAlg.toPH_add {k : ℕ} (f g : PHAlg α k) :
    (f + g).toPH = f.toPH + g.toPH := rfl
@[simp] theorem PHAlg.toPH_neg {k : ℕ} (f : PHAlg α k) : (-f).toPH = -f.toPH := rfl
@[simp] theorem PHAlg.toPH_zero {k : ℕ} : (0 : PHAlg α k).toPH = 0 := rfl
@[simp] theorem PHAlg.toPH_mul {k : ℕ} (f g : PHAlg α k) :
    (f * g).toPH = f.toPH * g.toPH := rfl
@[simp] theorem PHAlg.toPH_smul {k : ℕ} (c : ℝ) (f : PHAlg α k) :
    (c • f).toPH = c • f.toPH := rfl

noncomputable instance (k : ℕ) : NormedAddCommGroup (PHAlg α k) :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun f => PH.scale α k * ‖f.toPH‖
      map_zero' := by simp
      add_le' := fun f g => by
        rw [PHAlg.toPH_add, ← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _)
          (zero_le_one.trans (PH.one_le_scale α k))
      neg' := fun f => by simp
      eq_zero_of_map_eq_zero' := fun f h => by
        have h1 := PH.one_le_scale α k
        have : ‖f.toPH‖ = 0 := by
          rcases mul_eq_zero.mp h with h | h
          · linarith
          · exact h
        exact norm_eq_zero.mp this }

theorem PHAlg.norm_def {k : ℕ} (f : PHAlg α k) : ‖f‖ = PH.scale α k * ‖f.toPH‖ := rfl

noncomputable instance (k : ℕ) : NormedCommRing (PHAlg α k) :=
  { (inferInstance : NormedAddCommGroup (PHAlg α k)), (inferInstance : CommRing (PHAlg α k)) with
    norm_mul_le := fun f g => by
      simp only [PHAlg.norm_def, PHAlg.toPH_mul]
      have := PH.norm_mul_le_scale α k f.toPH g.toPH
      have h1 := PH.one_le_scale α k
      nlinarith }

noncomputable instance (k : ℕ) : NormedAlgebra ℝ (PHAlg α k) where
  norm_smul_le c f := by
    have h1 := PH.one_le_scale α k
    rw [PHAlg.norm_def, PHAlg.norm_def, PHAlg.toPH_smul, Real.norm_eq_abs]
    have := norm_smul_le c f.toPH
    rw [Real.norm_eq_abs] at this
    nlinarith

/-- The identity as a linear equivalence from `PH` to its rescaled model. -/
def PHAlg.linearEquiv (k : ℕ) : PH α k ≃ₗ[ℝ] PHAlg α k where
  toFun := PHAlg.ofPH
  invFun := PHAlg.toPH
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The continuous linear equivalence between `PH` and its rescaled model. -/
noncomputable def PHAlg.equiv (k : ℕ) : PH α k ≃L[ℝ] PHAlg α k :=
  (PHAlg.linearEquiv k).toContinuousLinearEquivOfBounds (PH.scale α k) 1
    (fun f => by
      show PH.scale α k * ‖f‖ ≤ PH.scale α k * ‖f‖
      exact le_rfl)
    (fun g => by
      have h1 := PH.one_le_scale α k
      show ‖g.toPH‖ ≤ 1 * ‖g‖
      rw [PHAlg.norm_def]
      have := norm_nonneg g.toPH
      nlinarith)

theorem PHAlg.norm_toPH_le {k : ℕ} (f : PHAlg α k) : ‖f.toPH‖ ≤ ‖f‖ := by
  have h1 := PH.one_le_scale α k
  rw [PHAlg.norm_def]
  have := norm_nonneg f.toPH
  nlinarith

instance (k : ℕ) : CompleteSpace (PHAlg α k) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  rw [Metric.cauchySeq_iff] at hu
  have hs := PH.one_le_scale α k
  obtain ⟨F, hF, hlim⟩ := complete_aux (α := α) k (fun n => (u n).toPH.val)
    (fun n => (u n).toPH.isPH) (by
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨N, fun n hn m hm => ?_⟩
      have h := hN n hn m hm
      rw [dist_eq_norm] at h
      exact lt_of_le_of_lt (PHAlg.norm_toPH_le (u n - u m)) h)
  refine ⟨PHAlg.ofPH (PH.mk F hF), Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hlim (ε / PH.scale α k) (div_pos hε (by linarith))
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [dist_eq_norm, PHAlg.norm_def]
  have h2 : ‖(u n - PHAlg.ofPH (PH.mk F hF)).toPH‖ < ε / PH.scale α k := h
  rw [lt_div_iff₀ (by linarith)] at h2
  linarith

/-- Evaluation at a point, as a ring homomorphism on the rescaled algebra. -/
def PHAlg.evalHom {k : ℕ} (x : ℝ) : PHAlg α k →+* ℝ where
  toFun f := f.toPH.val x
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem PHAlg.evalHom_continuous {k : ℕ} (x : ℝ) : Continuous (PHAlg.evalHom (α := α) (k := k) x) := by
  refine AddMonoidHomClass.continuous_of_bound (PHAlg.evalHom (α := α) (k := k) x) 1 fun f => ?_
  rw [one_mul, Real.norm_eq_abs]
  exact ((f.toPH.isPH.bdd.abs_le_supNorm x).trans (supNorm_le_phNorm k _)).trans
    (PHAlg.norm_toPH_le f)

end Alg

/-! ### Chart maps: exp, reciprocal, normalization -/

section Charts

open Filter Topology

variable {α : ℝ} [HolderExponent α]

/-- The exponential map `f ↦ e^f` on `PH α k`, via the exponential of the Banach algebra. -/
noncomputable def PH.expMap (k : ℕ) (f : PH α k) : PH α k :=
  (PHAlg.equiv k).symm (NormedSpace.exp (PHAlg.equiv k f))

theorem PH.expMap_val {k : ℕ} (f : PH α k) (x : ℝ) :
    (PH.expMap k f).val x = Real.exp (f.val x) := by
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (PHAlg.evalHom (α := α) (k := k) x)
    (PHAlg.evalHom_continuous x) (PHAlg.equiv k f)
    ((NormedSpace.expSeries_radius_eq_top ℝ (PHAlg α k)).symm ▸ edist_lt_top _ _)
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h

theorem PH.contDiff_expMap (k : ℕ) (n : WithTop ℕ∞) : ContDiff ℝ n (PH.expMap (α := α) k) := by
  refine contDiff_iff_contDiffAt.2 fun f => ?_
  exact (PHAlg.equiv k).symm.contDiff.contDiffAt.comp f
    (((NormedSpace.exp_analytic (𝕂 := ℝ) (PHAlg.equiv k f)).contDiffAt).comp f
      (PHAlg.equiv k).contDiff.contDiffAt)

/-- The open set of strictly positive elements. -/
def PH.posSet (α : ℝ) [HolderExponent α] (k : ℕ) : Set (PH α k) := {f | ∀ x, 0 < f.val x}

theorem PH.isOpen_posSet (k : ℕ) : IsOpen (PH.posSet α k) := by
  rw [Metric.isOpen_iff]
  intro f hf
  obtain ⟨m, hm, hmf⟩ := exists_pos_lower f.isPH.periodic f.isPH.continuous hf
  refine ⟨m, hm, fun g hg x => ?_⟩
  have h1 : dist g f < m := hg
  rw [PH.dist_def] at h1
  have h2 := ((g - f).isPH.bdd.abs_le_supNorm x).trans (supNorm_le_phNorm (α := α) k _)
  have h3 : |g.val x - f.val x| < m := lt_of_le_of_lt (by simpa using h2) h1
  have := (abs_lt.mp h3).1
  linarith [hmf x]

open scoped Classical in
/-- The reciprocal map, junk value `0` off the positive set. -/
noncomputable def PH.recipMap (k : ℕ) (f : PH α k) : PH α k :=
  if h : f ∈ PH.posSet α k then
    PH.mk (fun x => (f.val x)⁻¹)
      (IsPH.inv (HolderExponent.pos (α := α)).le (HolderExponent.lt_one (α := α)).le f.isPH h)
  else 0

theorem PH.recipMap_val {k : ℕ} {f : PH α k} (h : f ∈ PH.posSet α k) (x : ℝ) :
    (PH.recipMap k f).val x = (f.val x)⁻¹ := by
  simp [PH.recipMap, h]

theorem PH.contDiffOn_recipMap (k : ℕ) (n : WithTop ℕ∞) :
    ContDiffOn ℝ n (PH.recipMap (α := α) k) (PH.posSet α k) := by
  intro f hf
  have hunit : (PHAlg.equiv k f) * PHAlg.equiv k (PH.recipMap k f) = 1 := by
    refine PH.ext (funext fun x => ?_)
    show f.val x * (PH.recipMap k f).val x = 1
    rw [PH.recipMap_val hf]
    exact mul_inv_cancel₀ (hf x).ne'
  have hunit' : (PHAlg.equiv k (PH.recipMap k f)) * PHAlg.equiv k f = 1 := by
    rw [mul_comm]; exact hunit
  let u : (PHAlg α k)ˣ := ⟨PHAlg.equiv k f, PHAlg.equiv k (PH.recipMap k f), hunit, hunit'⟩
  have hinv : ∀ g ∈ PH.posSet α k, PH.recipMap k g =
      (PHAlg.equiv k).symm (Ring.inverse (PHAlg.equiv k g)) := by
    intro g hg
    have hu : (PHAlg.equiv k g) * PHAlg.equiv k (PH.recipMap k g) = 1 := by
      refine PH.ext (funext fun x => ?_)
      show g.val x * (PH.recipMap k g).val x = 1
      rw [PH.recipMap_val hg]
      exact mul_inv_cancel₀ (hg x).ne'
    have hu' : (PHAlg.equiv k (PH.recipMap k g)) * PHAlg.equiv k g = 1 := by
      rw [mul_comm]; exact hu
    let v : (PHAlg α k)ˣ := ⟨PHAlg.equiv k g, PHAlg.equiv k (PH.recipMap k g), hu, hu'⟩
    have : Ring.inverse (PHAlg.equiv k g) = PHAlg.equiv k (PH.recipMap k g) :=
      Ring.inverse_unit v
    rw [this]; rfl
  have hat : ContDiffAt ℝ n (fun g => (PHAlg.equiv k).symm (Ring.inverse (PHAlg.equiv k g))) f :=
    (PHAlg.equiv k).symm.contDiff.contDiffAt.comp f
      ((contDiffAt_ringInverse ℝ u).comp f (PHAlg.equiv k).contDiff.contDiffAt)
  exact hat.contDiffWithinAt.congr (fun g hg => hinv g hg) (hinv f hf)

/-- Integration over one period, as a continuous linear functional on `PH`. -/
noncomputable def PH.integral (k : ℕ) : PH α k →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x in (0 : ℝ)..1, f.val x
      map_add' := fun f g => by
        simp only [PH.val_add, Pi.add_apply]
        exact intervalIntegral.integral_add (f.isPH.continuous.intervalIntegrable _ _)
          (g.isPH.continuous.intervalIntegrable _ _)
      map_smul' := fun c f => by
        simp only [PH.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        exact intervalIntegral.integral_const_mul c _ } 1 (fun f => by
    have key : ‖∫ x in (0 : ℝ)..1, f.val x‖ ≤ ‖f‖ * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => by
        rw [Real.norm_eq_abs]
        exact (f.isPH.bdd.abs_le_supNorm x).trans (supNorm_le_phNorm (α := α) k _))
    simpa using key)

theorem PH.integral_apply {k : ℕ} (f : PH α k) :
    PH.integral k f = ∫ x in (0 : ℝ)..1, f.val x := rfl

/-- Normalization `f ↦ e^f / ∫ e^f`. -/
noncomputable def PH.normMap (k : ℕ) (f : PH α k) : PH α k :=
  (PH.integral k (PH.expMap k f))⁻¹ • PH.expMap k f

theorem PH.integral_expMap_pos {k : ℕ} (f : PH α k) : 0 < PH.integral k (PH.expMap k f) := by
  rw [PH.integral_apply]
  refine intervalIntegral.intervalIntegral_pos_of_pos
    ((PH.expMap k f).isPH.continuous.intervalIntegrable _ _) (fun x => ?_) one_pos
  rw [PH.expMap_val]; exact Real.exp_pos _

theorem PH.contDiff_normMap (k : ℕ) (n : WithTop ℕ∞) : ContDiff ℝ n (PH.normMap (α := α) k) := by
  have h1 : ContDiff ℝ n (fun f : PH α k => PH.integral k (PH.expMap k f)) :=
    (PH.integral k).contDiff.comp (PH.contDiff_expMap k n)
  exact (h1.inv fun f => (PH.integral_expMap_pos f).ne').smul (PH.contDiff_expMap k n)

end Charts

/-! ### Fourier modes and projections -/

section Fourier

open Filter Topology

variable {α : ℝ} [HolderExponent α]

/-- `a cos(2π n x) + b sin(2π n x)`. -/
noncomputable def trigFun (n : ℕ) (a b : ℝ) : ℝ → ℝ :=
  fun x => a * Real.cos (2 * Real.pi * n * x) + b * Real.sin (2 * Real.pi * n * x)

theorem trigFun_periodic (n : ℕ) (a b : ℝ) : Periodic (trigFun n a b) 1 := by
  intro x
  have h : 2 * Real.pi * n * (x + 1) = 2 * Real.pi * n * x + n * (2 * Real.pi) := by ring
  simp only [trigFun, h, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

theorem trigFun_hasDerivAt (n : ℕ) (a b x : ℝ) :
    HasDerivAt (trigFun n a b) (trigFun n (b * (2 * Real.pi * n)) (-(a * (2 * Real.pi * n))) x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * Real.pi * n * x) (2 * Real.pi * n) x := by
    simpa using (hasDerivAt_id x).const_mul (2 * Real.pi * n)
  have h2 := (h1.cos.const_mul a).add (h1.sin.const_mul b)
  refine h2.congr_deriv ?_
  simp only [trigFun]; ring

theorem trigFun_deriv (n : ℕ) (a b : ℝ) :
    deriv (trigFun n a b) = trigFun n (b * (2 * Real.pi * n)) (-(a * (2 * Real.pi * n))) :=
  funext fun x => (trigFun_hasDerivAt n a b x).deriv

theorem trigFun_continuous (n : ℕ) (a b : ℝ) : Continuous (trigFun n a b) := by
  unfold trigFun; fun_prop

theorem trigFun_bdd (n : ℕ) (a b : ℝ) : Bdd (trigFun n a b) :=
  periodic_bdd (trigFun_periodic n a b) (trigFun_continuous n a b)

omit [HolderExponent α] in
theorem isPH_zero_of_lip (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {f : ℝ → ℝ} (hp : Periodic f 1)
    (hd : Differentiable ℝ f) (hb : Bdd (deriv f)) : IsPH α 0 f := by
  have hbf : Bdd f := periodic_bdd hp hd.continuous
  exact ⟨hp, hd.continuous, HolderBdd.of_le
    (C := supNorm (deriv f) + 2 * supNorm f) (add_nonneg (supNorm_nonneg _)
      (mul_nonneg two_pos.le (supNorm_nonneg _)))
    (holder_of_lip (supNorm_nonneg _) (supNorm_nonneg _) hα0 hα1 (lip_bound hd hb)
      hbf.abs_le_supNorm)⟩

theorem isPH_trigFun (n : ℕ) :
    ∀ (k : ℕ) (a b : ℝ), IsPH α k (trigFun n a b) := by
  intro k
  induction k with
  | zero =>
    intro a b
    refine isPH_zero_of_lip (HolderExponent.pos (α := α)).le (HolderExponent.lt_one (α := α)).le
      (trigFun_periodic n a b) (fun x => (trigFun_hasDerivAt n a b x).differentiableAt) ?_
    rw [trigFun_deriv]; exact trigFun_bdd _ _ _
  | succ k ih =>
    intro a b
    refine ⟨trigFun_periodic n a b, fun x => (trigFun_hasDerivAt n a b x).differentiableAt, ?_⟩
    rw [trigFun_deriv]; exact ih _ _

theorem PH.val_sum {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → PH α k) (x : ℝ) :
    (∑ i ∈ s, f i).val x = ∑ i ∈ s, (f i).val x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PH.val_add, Pi.add_apply, ih]

/-- The trigonometric element `a cos(2π n x) + b sin(2π n x)` of `PH α k`. -/
noncomputable def PH.trig (k n : ℕ) (a b : ℝ) : PH α k := PH.mk (trigFun n a b) (isPH_trigFun n k a b)

@[simp] theorem PH.val_trig {k : ℕ} (n : ℕ) (a b : ℝ) : (PH.trig (α := α) k n a b).val = trigFun n a b :=
  rfl

/-- Pairing over one period with a bounded continuous test function. -/
noncomputable def PH.pair (k : ℕ) (g : ℝ → ℝ) (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) :
    PH α k →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x in (0 : ℝ)..1, f.val x * g x
      map_add' := fun f h => by
        simp only [PH.val_add, Pi.add_apply, add_mul]
        exact intervalIntegral.integral_add
          ((f.isPH.continuous.mul hg).intervalIntegrable _ _)
          ((h.isPH.continuous.mul hg).intervalIntegrable _ _)
      map_smul' := fun c f => by
        simp only [PH.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact intervalIntegral.integral_const_mul c _ } 1 (fun f => by
    have key : ‖∫ x in (0 : ℝ)..1, f.val x * g x‖ ≤ ‖f‖ * |(1 : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |f.val x| ≤ ‖f‖ :=
          (f.isPH.bdd.abs_le_supNorm x).trans (supNorm_le_phNorm (α := α) k _)
        have h2 := hb x
        have h3 := abs_nonneg (f.val x)
        nlinarith [abs_nonneg (g x)])
    simpa using key)

theorem PH.pair_apply {k : ℕ} (g : ℝ → ℝ) (hg : Continuous g) (hb : ∀ x, |g x| ≤ 1) (f : PH α k) :
    PH.pair k g hg hb f = ∫ x in (0 : ℝ)..1, f.val x * g x := rfl

/-- The weight `1` for the constant mode and `2` for the others. -/
def modeWeight (n : ℕ) : ℝ := if n = 0 then 1 else 2

/-- Fourier cosine coefficient `∫₀¹ f(x) cos(2π n x) dx`. -/
noncomputable def PH.cosCoeff (k n : ℕ) : PH α k →L[ℝ] ℝ :=
  PH.pair k (fun x => Real.cos (2 * Real.pi * n * x)) (by fun_prop) (fun _ => Real.abs_cos_le_one _)

/-- Fourier sine coefficient `∫₀¹ f(x) sin(2π n x) dx`. -/
noncomputable def PH.sinCoeff (k n : ℕ) : PH α k →L[ℝ] ℝ :=
  PH.pair k (fun x => Real.sin (2 * Real.pi * n * x)) (by fun_prop) (fun _ => Real.abs_sin_le_one _)

theorem PH.cosCoeff_apply {k : ℕ} (n : ℕ) (f : PH α k) :
    PH.cosCoeff k n f = ∫ x in (0 : ℝ)..1, f.val x * Real.cos (2 * Real.pi * n * x) := rfl

theorem PH.sinCoeff_apply {k : ℕ} (n : ℕ) (f : PH α k) :
    PH.sinCoeff k n f = ∫ x in (0 : ℝ)..1, f.val x * Real.sin (2 * Real.pi * n * x) := rfl

/-- The projection onto the single Fourier mode `n` (cosine and sine part). -/
noncomputable def PH.modeCLM (k n : ℕ) : PH α k →L[ℝ] PH α k :=
  (modeWeight n • PH.cosCoeff k n).smulRight (PH.trig k n 1 0) +
    (modeWeight n • PH.sinCoeff k n).smulRight (PH.trig k n 0 1)

/-- The projection onto a finite set of Fourier modes. -/
noncomputable def PH.modeProj (k : ℕ) (S : Finset ℕ) : PH α k →L[ℝ] PH α k :=
  ∑ n ∈ S, PH.modeCLM k n

theorem PH.modeCLM_val {k : ℕ} (n : ℕ) (f : PH α k) (x : ℝ) :
    (PH.modeCLM k n f).val x =
      trigFun n (modeWeight n * PH.cosCoeff k n f) (modeWeight n * PH.sinCoeff k n f) x := by
  simp [PH.modeCLM, trigFun]

theorem PH.modeProj_val {k : ℕ} (S : Finset ℕ) (f : PH α k) (x : ℝ) :
    (PH.modeProj k S f).val x =
      ∑ n ∈ S, trigFun n (modeWeight n * PH.cosCoeff k n f) (modeWeight n * PH.sinCoeff k n f) x := by
  unfold PH.modeProj
  rw [sum_apply, PH.val_sum]
  exact Finset.sum_congr rfl fun n _ => PH.modeCLM_val n f x

theorem int_cos : ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * x) = 0 := by
  have hc : (2 * Real.pi) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) (fun u => Real.cos u) hc
  rw [this]; simp [integral_cos]

theorem int_sin : ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * x) = 0 := by
  have hc : (2 * Real.pi) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1) (fun u => Real.sin u) hc
  rw [this]; simp [integral_sin]

theorem int_cos_sq : ∫ x in (0 : ℝ)..1, Real.cos (2 * Real.pi * x) ^ 2 = 1 / 2 := by
  have hc : (2 * Real.pi) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u => Real.cos u ^ 2) hc
  rw [this]; simp [integral_cos_sq]
  field_simp

theorem int_sin_sq : ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * x) ^ 2 = 1 / 2 := by
  have hc : (2 * Real.pi) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u => Real.sin u ^ 2) hc
  rw [this]; simp [integral_sin_sq]
  field_simp

theorem int_sin_mul_cos :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x) = 0 := by
  have hc : (2 * Real.pi) ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := 1)
    (fun u => Real.sin u * Real.cos u) hc
  rw [this]; simp [integral_sin_mul_cos₁]

theorem int_comb3 {p q r : ℝ → ℝ} (hp : Continuous p) (hq : Continuous q) (hr : Continuous r)
    (A B C : ℝ) :
    ∫ x in (0 : ℝ)..1, (A * p x + B * q x + C * r x) =
      A * (∫ x in (0 : ℝ)..1, p x) + B * (∫ x in (0 : ℝ)..1, q x) +
        C * (∫ x in (0 : ℝ)..1, r x) := by
  have e1 : IntervalIntegrable (fun x => A * p x) MeasureTheory.volume 0 1 :=
    (hp.const_mul A).intervalIntegrable _ _
  have e2 : IntervalIntegrable (fun x => B * q x) MeasureTheory.volume 0 1 :=
    (hq.const_mul B).intervalIntegrable _ _
  have e3 : IntervalIntegrable (fun x => C * r x) MeasureTheory.volume 0 1 :=
    (hr.const_mul C).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (e1.add e2) e3, intervalIntegral.integral_add e1 e2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-- The projection onto the modes `1, cos, sin` (frequencies `0` and `1`), in closed form. -/
theorem PH.modeProj01_val {k : ℕ} (f : PH α k) (x : ℝ) :
    (PH.modeProj k {0, 1} f).val x =
      PH.integral k f + 2 * PH.cosCoeff k 1 f * Real.cos (2 * Real.pi * x) +
        2 * PH.sinCoeff k 1 f * Real.sin (2 * Real.pi * x) := by
  rw [PH.modeProj_val, Finset.sum_pair (by norm_num)]
  have h0 : PH.cosCoeff k 0 f = PH.integral k f := by
    simp [PH.cosCoeff_apply, PH.integral_apply]
  simp [trigFun, modeWeight, h0]
  ring

/-- The closed subspace of `PH α k` orthogonal to `1`, `cos(2π x)`, `sin(2π x)`. -/
noncomputable def PH.orthSub (α : ℝ) [HolderExponent α] (k : ℕ) : Submodule ℝ (PH α k) where
  carrier := {f | PH.integral k f = 0 ∧ PH.cosCoeff k 1 f = 0 ∧ PH.sinCoeff k 1 f = 0}
  add_mem' := fun {f g} hf hg => ⟨by simp [hf.1, hg.1], by simp [hf.2.1, hg.2.1],
    by simp [hf.2.2, hg.2.2]⟩
  zero_mem' := ⟨by simp, by simp, by simp⟩
  smul_mem' := fun c f hf => ⟨by simp [hf.1], by simp [hf.2.1], by simp [hf.2.2]⟩

theorem PH.mem_orthSub {k : ℕ} (f : PH α k) :
    f ∈ PH.orthSub α k ↔
      PH.integral k f = 0 ∧ PH.cosCoeff k 1 f = 0 ∧ PH.sinCoeff k 1 f = 0 := Iff.rfl

theorem PH.isClosed_orthSub (k : ℕ) : IsClosed (PH.orthSub α k : Set (PH α k)) := by
  have : (PH.orthSub α k : Set (PH α k)) =
      {f | PH.integral k f = 0} ∩ {f | PH.cosCoeff k 1 f = 0} ∩ {f | PH.sinCoeff k 1 f = 0} := by
    ext f; simp [PH.mem_orthSub, and_assoc]
  rw [this]
  exact ((isClosed_eq (PH.integral k).continuous continuous_const).inter
    (isClosed_eq (PH.cosCoeff k 1).continuous continuous_const)).inter
    (isClosed_eq (PH.sinCoeff k 1).continuous continuous_const)

theorem PH.modeProj01_orth {k : ℕ} (f : PH α k) :
    PH.integral k (PH.modeProj k {0, 1} f) = PH.integral k f ∧
    PH.cosCoeff k 1 (PH.modeProj k {0, 1} f) = PH.cosCoeff k 1 f ∧
    PH.sinCoeff k 1 (PH.modeProj k {0, 1} f) = PH.sinCoeff k 1 f := by
  have hc : Continuous fun x : ℝ => Real.cos (2 * Real.pi * x) := by fun_prop
  have hs : Continuous fun x : ℝ => Real.sin (2 * Real.pi * x) := by fun_prop
  have h1 : Continuous fun _ : ℝ => (1 : ℝ) := continuous_const
  refine ⟨?_, ?_, ?_⟩
  · rw [PH.integral_apply]
    have : (fun x => (PH.modeProj k {0, 1} f).val x) = fun x =>
        PH.integral k f * 1 + (2 * PH.cosCoeff k 1 f) * Real.cos (2 * Real.pi * x) +
          (2 * PH.sinCoeff k 1 f) * Real.sin (2 * Real.pi * x) := by
      funext x; rw [PH.modeProj01_val]; ring
    rw [this, int_comb3 h1 hc hs]
    simp
  · rw [PH.cosCoeff_apply]
    have : (fun x => (PH.modeProj k {0, 1} f).val x * Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) * x)) =
        fun x => PH.integral k f * Real.cos (2 * Real.pi * x) +
          (2 * PH.cosCoeff k 1 f) * Real.cos (2 * Real.pi * x) ^ 2 +
          (2 * PH.sinCoeff k 1 f) * (Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x)) := by
      funext x; rw [PH.modeProj01_val]; simp only [Nat.cast_one, mul_one]; ring
    rw [this]
    refine (int_comb3 (p := fun x => Real.cos (2 * Real.pi * x))
      (q := fun x => Real.cos (2 * Real.pi * x) ^ 2)
      (r := fun x => Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x)) hc (hc.pow 2)
      (hs.mul hc) _ _ _).trans ?_
    rw [int_cos, int_cos_sq, int_sin_mul_cos]
    ring
  · rw [PH.sinCoeff_apply]
    have : (fun x => (PH.modeProj k {0, 1} f).val x * Real.sin (2 * Real.pi * ((1 : ℕ) : ℝ) * x)) =
        fun x => PH.integral k f * Real.sin (2 * Real.pi * x) +
          (2 * PH.cosCoeff k 1 f) * (Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x)) +
          (2 * PH.sinCoeff k 1 f) * Real.sin (2 * Real.pi * x) ^ 2 := by
      funext x; rw [PH.modeProj01_val]; simp only [Nat.cast_one, mul_one]; ring
    rw [this]
    refine (int_comb3 (p := fun x => Real.sin (2 * Real.pi * x))
      (q := fun x => Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x))
      (r := fun x => Real.sin (2 * Real.pi * x) ^ 2) hs (hs.mul hc)
      (hs.pow 2) _ _ _).trans ?_
    rw [int_sin, int_sin_mul_cos, int_sin_sq]
    ring

theorem PH.modeProj01_eq_zero {k : ℕ} {f : PH α k} (hf : f ∈ PH.orthSub α k) :
    PH.modeProj k {0, 1} f = 0 := by
  refine PH.ext (funext fun x => ?_)
  rw [PH.modeProj01_val, hf.1, hf.2.1, hf.2.2]
  simp

/-- The subspace orthogonal to `1, cos, sin` is complemented by a continuous projection. -/
theorem PH.orthSub_closedComplemented (k : ℕ) : (PH.orthSub α k).ClosedComplemented := by
  let Q : PH α k →L[ℝ] PH α k := ContinuousLinearMap.id ℝ _ - PH.modeProj k {0, 1}
  have hQ : ∀ f, Q f ∈ PH.orthSub α k := fun f => by
    obtain ⟨a, b, c⟩ := PH.modeProj01_orth f
    refine ⟨?_, ?_, ?_⟩
    · show PH.integral k (f - PH.modeProj k {0, 1} f) = 0
      rw [map_sub, a, sub_self]
    · show PH.cosCoeff k 1 (f - PH.modeProj k {0, 1} f) = 0
      rw [map_sub, b, sub_self]
    · show PH.sinCoeff k 1 (f - PH.modeProj k {0, 1} f) = 0
      rw [map_sub, c, sub_self]
  refine ⟨Q.codRestrict (PH.orthSub α k) hQ, fun f => ?_⟩
  apply Subtype.ext
  show f.1 - PH.modeProj k {0, 1} f.1 = f.1
  rw [PH.modeProj01_eq_zero f.2, sub_zero]

end Fourier

end DGPS.Analysis.PeriodicHolder

namespace DGPS.Analysis

open DGPS.Analysis.PeriodicHolder

/-- **Periodic Holder Banach charts.**  Fix `0 < α < 1` (the instance `HolderExponent α`) and `k : ℕ`.
(i) `PH α k`, the 1-periodic `C^{k,α}` functions with norm `∑_{j ≤ k} ‖∂^j f‖∞ + [∂^k f]_α`,
is a real Banach space; (ii) the Fourier projection onto any finite set of modes is a bounded
linear map; (iii) the subspace orthogonal to `1, cos, sin` is closed and complemented;
(iv) products are in the space and obey a norm bound; (v) `exp`, the reciprocal on the open set
of positive functions, and the normalization `f ↦ e^f / ∫ e^f` are `C^r` for every finite `r`. -/
theorem periodic_holder_banach_charts (α : ℝ) [HolderExponent α] (k : ℕ) :
    -- (i) Banach space with the stated norm
    ((∀ f : PH α k, ‖f‖ = (∑ j ∈ Finset.range (k + 1), supNorm (deriv^[j] f.val)) +
        holderSeminorm α (deriv^[k] f.val)) ∧ CompleteSpace (PH α k)) ∧
    -- (ii) bounded Fourier projections onto finitely many modes
    (∀ S : Finset ℕ, ∃ P : PH α k →L[ℝ] PH α k, P = PH.modeProj k S ∧
      ∀ (f : PH α k) (x : ℝ), (P f).val x = ∑ n ∈ S,
        trigFun n (modeWeight n * ∫ t in (0 : ℝ)..1, f.val t * Real.cos (2 * Real.pi * n * t))
          (modeWeight n * ∫ t in (0 : ℝ)..1, f.val t * Real.sin (2 * Real.pi * n * t)) x) ∧
    -- (iii) the orthogonal subspace is closed and complemented
    (IsClosed (PH.orthSub α k : Set (PH α k)) ∧ (PH.orthSub α k).ClosedComplemented ∧
      ∀ f : PH α k, f ∈ PH.orthSub α k ↔
        ((∫ t in (0 : ℝ)..1, f.val t) = 0 ∧
         (∫ t in (0 : ℝ)..1, f.val t * Real.cos (2 * Real.pi * t)) = 0 ∧
         (∫ t in (0 : ℝ)..1, f.val t * Real.sin (2 * Real.pi * t)) = 0)) ∧
    -- (iv) product norm bound
    (∃ C : ℝ, 0 ≤ C ∧ ∀ f g : PH α k, (f * g).val = f.val * g.val ∧
        ‖f * g‖ ≤ C * (‖f‖ * ‖g‖)) ∧
    -- (v) smooth charts
    (∀ r : ℕ,
      ContDiff ℝ (r : WithTop ℕ∞) (PH.expMap (α := α) k) ∧
      (∀ f : PH α k, (∀ x, Real.exp (f.val x) = (PH.expMap k f).val x)) ∧
      IsOpen (PH.posSet α k) ∧
      ContDiffOn ℝ (r : WithTop ℕ∞) (PH.recipMap (α := α) k) (PH.posSet α k) ∧
      (∀ f ∈ PH.posSet α k, ∀ x, (PH.recipMap k f).val x = (f.val x)⁻¹) ∧
      ContDiff ℝ (r : WithTop ℕ∞) (PH.normMap (α := α) k) ∧
      (∀ (f : PH α k) (x : ℝ), (PH.normMap k f).val x =
        Real.exp (f.val x) / ∫ t in (0 : ℝ)..1, Real.exp (f.val t))) := by
  refine ⟨⟨fun f => phNorm_eq_sum α k f.val, inferInstance⟩, ?_, ?_, ?_, ?_⟩
  · intro S
    refine ⟨PH.modeProj k S, rfl, fun f x => ?_⟩
    rw [PH.modeProj_val]
    rfl
  · refine ⟨PH.isClosed_orthSub k, PH.orthSub_closedComplemented k, fun f => ?_⟩
    rw [PH.mem_orthSub, PH.integral_apply, PH.cosCoeff_apply, PH.sinCoeff_apply]
    simp
  · obtain ⟨C, hC, h⟩ := PH.mul_bound α k
    exact ⟨C, hC, fun f g => ⟨rfl, h f g⟩⟩
  · intro r
    refine ⟨PH.contDiff_expMap k _, fun f x => (PH.expMap_val f x).symm, PH.isOpen_posSet k,
      PH.contDiffOn_recipMap k _, fun f hf x => PH.recipMap_val hf x, PH.contDiff_normMap k _,
      fun f x => ?_⟩
    have hI : PH.integral k (PH.expMap k f) = ∫ t in (0 : ℝ)..1, Real.exp (f.val t) := by
      rw [PH.integral_apply]
      exact intervalIntegral.integral_congr fun t _ => PH.expMap_val f t
    show ((PH.integral k (PH.expMap k f))⁻¹ • PH.expMap k f).val x = _
    simp [PH.expMap_val, hI, div_eq_inv_mul]

end DGPS.Analysis
