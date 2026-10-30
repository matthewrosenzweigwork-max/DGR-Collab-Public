import DGPS.Lipschitz.T01TighteningBridge
import DGPS.Basic.EventualExactLSI

/-!
# Canonical particle domains for the existing abstract tightening theorem

The raw energy is the actual Sobolev energy on its domain; its off-domain value is unused.
Measurable representatives recover every original particle test and its a.e. symmetry.
A single defective inequality on one fixed particle tail supplies all weaker defective
coefficients needed by the abstract record on that same tail.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

open Classical in
private def t01RawParticleEnergy (A : InteractionData d) (N : ℕ+)
    (f : ParticleSpace d N → ℝ) : ℝ :=
  if hf : MemParticleH1 A N f then particleEnergy A N ⟨f, hf⟩ else 0

private theorem t01RawParticleEnergy_eq (A : InteractionData d) (N : ℕ+)
    {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) :
    t01RawParticleEnergy A N f = particleEnergy A N ⟨f, hf⟩ := by
  simp only [t01RawParticleEnergy, dif_pos hf]

/-- The raw extension has the energy of every genuine weak-gradient witness. -/
private theorem t01_raw_particle_energy_witness_independent (A : InteractionData d) (N : ℕ+)
    {f : ParticleSpace d N → ℝ} {G : ParticleSpace d N → Fin N → Tangent d}
    (hG : IsParticleWeakGradient A N f G) :
    t01RawParticleEnergy A N f = ∫ x, particleTangentNormSq (G x) ∂particleLaw A N := by
  rw [t01RawParticleEnergy_eq A N ⟨G, hG⟩]
  exact particleEnergy_eq_of_isParticleWeakGradient ⟨f, ⟨G, hG⟩⟩ hG

private theorem t01RawParticleEnergy_nonneg (A : InteractionData d) (N : ℕ+)
    {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) :
    0 ≤ t01RawParticleEnergy A N f := by
  rw [t01RawParticleEnergy_eq A N hf]
  exact particleEnergy_nonneg _

private theorem t01RawParticleEnergy_abs (A : InteractionData d) (N : ℕ+)
    {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) :
    t01RawParticleEnergy A N (fun x => |f x|) ≤ t01RawParticleEnergy A N f := by
  rw [t01RawParticleEnergy_eq A N hf.abs, t01RawParticleEnergy_eq A N hf]
  exact particleEnergy_abs_le ⟨f, hf⟩ ⟨_, hf.abs⟩ rfl

private theorem t01RawParticleEnergy_max (A : InteractionData d) (N : ℕ+)
    {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) (c : ℝ) :
    t01RawParticleEnergy A N (fun x => max (f x) c) ≤ t01RawParticleEnergy A N f := by
  rw [t01RawParticleEnergy_eq A N (hf.max_const c), t01RawParticleEnergy_eq A N hf]
  exact particleEnergy_max_const_le ⟨f, hf⟩ ⟨_, hf.max_const c⟩ c rfl

private theorem t01RawParticleEnergy_min (A : InteractionData d) (N : ℕ+)
    {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) (c : ℝ) :
    t01RawParticleEnergy A N (fun x => min (f x) c) ≤ t01RawParticleEnergy A N f := by
  rw [t01RawParticleEnergy_eq A N (hf.min_const c), t01RawParticleEnergy_eq A N hf]
  exact particleEnergy_min_const_le ⟨f, hf⟩ ⟨_, hf.min_const c⟩ c rfl

private theorem t01RawParticleEnergy_affine (A : InteractionData d) (N : ℕ+)
    {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) (a b : ℝ) :
    t01RawParticleEnergy A N (fun x => a * f x + b) = a ^ 2 * t01RawParticleEnergy A N f := by
  rw [t01RawParticleEnergy_eq A N (hf.affine a b), t01RawParticleEnergy_eq A N hf]
  exact particleEnergy_affine ⟨f, hf⟩ ⟨_, hf.affine a b⟩ a b rfl

private theorem t01RawParticleEnergy_split (A : InteractionData d) (N : ℕ+)
    {f : ParticleSpace d N → ℝ} (hf : MemParticleH1 A N f) (c : ℝ) :
    t01RawParticleEnergy A N (fun x => min (f x) c) +
      t01RawParticleEnergy A N (fun x => max (f x - c) 0) ≤ t01RawParticleEnergy A N f := by
  have ht : MemParticleH1 A N (fun x => max (f x - c) 0) := by
    simpa only [one_mul, ← sub_eq_add_neg] using (hf.affine 1 (-c)).max_const 0
  rw [t01RawParticleEnergy_eq A N (hf.min_const c), t01RawParticleEnergy_eq A N ht,
    t01RawParticleEnergy_eq A N hf]
  exact particleEnergy_truncation_split ⟨f, hf⟩ ⟨_, hf.min_const c⟩ ⟨_, ht⟩ c rfl rfl

private def t01ParticleIndex (B : ℕ+) (n : ℕ) : ℕ+ :=
  ⟨(B : ℕ) + n, by have := B.pos; omega⟩

private theorem t01ParticleIndex_ge (B : ℕ+) (n : ℕ) : B ≤ t01ParticleIndex B n := by
  change (B : ℕ) ≤ (B : ℕ) + n
  omega

private theorem t01ParticleIndex_tendsto (B : ℕ+) : Tendsto (t01ParticleIndex B) atTop atTop := by
  rw [tendsto_atTop]
  intro N
  filter_upwards [eventually_ge_atTop (N : ℕ)] with n hn
  change (N : ℕ) ≤ (B : ℕ) + n
  omega

private def t01FullParticleClass (A : InteractionData d) (N : ℕ+) :
    Set (ParticleSpace d N → ℝ) := {f | Measurable f ∧ MemParticleH1 A N f}

private def t01SymParticleClass (A : InteractionData d) (N : ℕ+) :
    Set (ParticleSpace d N → ℝ) :=
  {f | Measurable f ∧ MemParticleH1 A N f ∧ IsSymmetricParticleFun A N f}

private theorem t01_defective_coefficient_mono {E R r0 C m : ℝ}
    (hE : 0 ≤ E) (hr0 : 0 < r0) (hrR : r0 < R) :
    2 * E / R + C * m ≤ 2 * E / r0 + C * m := by
  have hd : 2 * E / R ≤ 2 * E / r0 :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hE) hr0 hrR.le
  linarith

private theorem t01FullParticleTighteningHyp (A : InteractionData d)
    {R : ℝ} (hR : 0 < R) (B : ℕ+) (C : ℝ)
    (hdef : ∀ N ≥ B, ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal
        (2 * particleEnergy A N f / R + C * ∫ x, f x ^ 2 ∂particleLaw A N))
    (hcomp : ∃ a : ℝ, R ≤ a ∧ ∀ M E0 ε : ℝ, 0 < M → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N,
        (∀ x, |f x| ≤ M) → particleEnergy A N f ≤ E0 →
        ENNReal.ofReal (a / 2) * particleEntropy A N f ≤
          ENNReal.ofReal (particleEnergy A N f + ε))
    (hpoin : ∀ ρ : ℝ, ρ < R → ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N,
      ρ * ((∫ x, f x ^ 2 ∂particleLaw A N) - (∫ x, f x ∂particleLaw A N) ^ 2) ≤
        particleEnergy A N f) :
    Analysis.TighteningHyp (fun n => particleLaw A (t01ParticleIndex B n))
      (fun n => t01RawParticleEnergy A (t01ParticleIndex B n))
      (fun n => t01FullParticleClass A (t01ParticleIndex B n)) R := by
  refine {
    measurable := fun n f hf => hf.1
    sq_integrable := fun n f hf => hf.2.choose_spec.memLp.integrable_sq
    energy_nonneg := fun n f hf => t01RawParticleEnergy_nonneg A _ hf.2
    abs_mem := fun n f hf => ⟨hf.1.abs, hf.2.abs⟩
    max_mem := fun n f hf c => ⟨hf.1.max measurable_const, hf.2.max_const c⟩
    min_mem := fun n f hf c => ⟨hf.1.min measurable_const, hf.2.min_const c⟩
    affine_mem := fun n f hf a b => ⟨(hf.1.const_mul a).add measurable_const, hf.2.affine a b⟩
    energy_abs_le := fun n f hf => t01RawParticleEnergy_abs A _ hf.2
    energy_max_le := fun n f hf c => t01RawParticleEnergy_max A _ hf.2 c
    energy_min_le := fun n f hf c => t01RawParticleEnergy_min A _ hf.2 c
    energy_affine := fun n f hf a b => t01RawParticleEnergy_affine A _ hf.2 a b
    R_pos := hR
    defective := ?_
    bounded_comparison := ?_
    poincare := ?_ }
  · intro r0 hr0 hr0R
    refine ⟨C, fun n f hf => ?_⟩
    rw [t01RawParticleEnergy_eq A _ hf.2]
    exact (hdef _ (t01ParticleIndex_ge B n) ⟨f, hf.2⟩).trans
      (ENNReal.ofReal_le_ofReal (t01_defective_coefficient_mono (particleEnergy_nonneg _)
        hr0 hr0R))
  · obtain ⟨a, ha, hc⟩ := hcomp
    refine ⟨a, ha, fun M E0 ε hM hE0 hε => ?_⟩
    obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1
      ((t01ParticleIndex_tendsto B).eventually (hc M E0 ε hM hE0 hε))
    refine ⟨n0, fun n hn f hf hbound henergy => ?_⟩
    rw [t01RawParticleEnergy_eq A _ hf.2] at henergy ⊢
    exact hn0 n hn ⟨f, hf.2⟩ hbound henergy
  · intro ρ hρ
    obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1
      ((t01ParticleIndex_tendsto B).eventually (hpoin ρ hρ))
    refine ⟨n0, fun n hn f hf => ?_⟩
    rw [t01RawParticleEnergy_eq A _ hf.2]
    exact hn0 n hn ⟨f, hf.2⟩

private theorem t01SymParticleTighteningHyp (A : InteractionData d)
    {R : ℝ} (hR : 0 < R) (B : ℕ+) (C : ℝ)
    (hdef : ∀ N ≥ B, ∀ f : ParticleH1 A N, IsSymmetricParticleTest f →
      particleEntropy A N f ≤ ENNReal.ofReal
        (2 * particleEnergy A N f / R + C * ∫ x, f x ^ 2 ∂particleLaw A N))
    (hcomp : ∃ a : ℝ, R ≤ a ∧ ∀ M E0 ε : ℝ, 0 < M → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N, Measurable f.1 →
        IsSymmetricParticleTest f → (∀ x, |f x| ≤ M) → particleEnergy A N f ≤ E0 →
        ENNReal.ofReal (a / 2) * particleEntropy A N f ≤
          ENNReal.ofReal (particleEnergy A N f + ε))
    (hpoin : ∀ ρ : ℝ, ρ < R → ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N,
      IsSymmetricParticleTest f →
      ρ * ((∫ x, f x ^ 2 ∂particleLaw A N) - (∫ x, f x ∂particleLaw A N) ^ 2) ≤
        particleEnergy A N f) :
    Analysis.TighteningHyp (fun n => particleLaw A (t01ParticleIndex B n))
      (fun n => t01RawParticleEnergy A (t01ParticleIndex B n))
      (fun n => t01SymParticleClass A (t01ParticleIndex B n)) R := by
  refine {
    measurable := fun n f hf => hf.1
    sq_integrable := fun n f hf => hf.2.1.choose_spec.memLp.integrable_sq
    energy_nonneg := fun n f hf => t01RawParticleEnergy_nonneg A _ hf.2.1
    abs_mem := fun n f hf => ⟨hf.1.abs, hf.2.1.abs, hf.2.2.comp_scalar (fun x : ℝ => |x|)⟩
    max_mem := fun n f hf c => ⟨hf.1.max measurable_const, hf.2.1.max_const c,
      hf.2.2.comp_scalar (fun x => max x c)⟩
    min_mem := fun n f hf c => ⟨hf.1.min measurable_const, hf.2.1.min_const c,
      hf.2.2.comp_scalar (fun x => min x c)⟩
    affine_mem := fun n f hf a b => ⟨(hf.1.const_mul a).add measurable_const, hf.2.1.affine a b,
      hf.2.2.comp_scalar (fun x => a * x + b)⟩
    energy_abs_le := fun n f hf => t01RawParticleEnergy_abs A _ hf.2.1
    energy_max_le := fun n f hf c => t01RawParticleEnergy_max A _ hf.2.1 c
    energy_min_le := fun n f hf c => t01RawParticleEnergy_min A _ hf.2.1 c
    energy_affine := fun n f hf a b => t01RawParticleEnergy_affine A _ hf.2.1 a b
    R_pos := hR
    defective := ?_
    bounded_comparison := ?_
    poincare := ?_ }
  · intro r0 hr0 hr0R
    refine ⟨C, fun n f hf => ?_⟩
    rw [t01RawParticleEnergy_eq A _ hf.2.1]
    exact (hdef _ (t01ParticleIndex_ge B n) ⟨f, hf.2.1⟩ hf.2.2).trans
      (ENNReal.ofReal_le_ofReal (t01_defective_coefficient_mono (particleEnergy_nonneg _)
        hr0 hr0R))
  · obtain ⟨a, ha, hc⟩ := hcomp
    refine ⟨a, ha, fun M E0 ε hM hE0 hε => ?_⟩
    obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1
      ((t01ParticleIndex_tendsto B).eventually (hc M E0 ε hM hE0 hε))
    refine ⟨n0, fun n hn f hf hbound henergy => ?_⟩
    rw [t01RawParticleEnergy_eq A _ hf.2.1] at henergy ⊢
    exact hn0 n hn ⟨f, hf.2.1⟩ hf.1 hf.2.2 hbound henergy
  · intro ρ hρ
    obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.1
      ((t01ParticleIndex_tendsto B).eventually (hpoin ρ hρ))
    refine ⟨n0, fun n hn f hf => ?_⟩
    rw [t01RawParticleEnergy_eq A _ hf.2.1]
    exact hn0 n hn ⟨f, hf.2.1⟩ hf.2.2

/-- Concrete full-domain tightening on one fixed particle tail. The conclusion includes
all original canonical H1 tests, via measurable a.e. representatives. -/
theorem eventual_particle_lsi_after_concrete_tightening (A : InteractionData d)
    {R : ℝ} (hR : 0 < R) (B : ℕ+) (C : ℝ)
    (hdef : ∀ N ≥ B, ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal
        (2 * particleEnergy A N f / R + C * ∫ x, f x ^ 2 ∂particleLaw A N))
    (hcomp : ∃ a : ℝ, R ≤ a ∧ ∀ M E0 ε : ℝ, 0 < M → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N,
        (∀ x, |f x| ≤ M) → particleEnergy A N f ≤ E0 →
        ENNReal.ofReal (a / 2) * particleEntropy A N f ≤
          ENNReal.ofReal (particleEnergy A N f + ε))
    (hpoin : ∀ ρ : ℝ, ρ < R → ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N,
      ρ * ((∫ x, f x ^ 2 ∂particleLaw A N) - (∫ x, f x ∂particleLaw A N) ^ 2) ≤
        particleEnergy A N f)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N,
      particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) := by
  have hyp := t01FullParticleTighteningHyp A hR B C hdef hcomp hpoin
  obtain ⟨n0, hn0⟩ := Analysis.abstract_eventual_exact_lsi_after_defect_removal hyp
    (fun n f hf _ c _ => t01RawParticleEnergy_split A _ hf.2 c) hr hrR
  refine eventually_atTop.mpr ⟨t01ParticleIndex B n0, fun N hN f => ?_⟩
  have hN' : (B : ℕ) + n0 ≤ (N : ℕ) := hN
  let n : ℕ := (N : ℕ) - (B : ℕ)
  have hn : n0 ≤ n := by dsimp only [n]; omega
  have he : t01ParticleIndex B n = N := by
    apply Subtype.ext
    change (B : ℕ) + n = (N : ℕ)
    dsimp only [n]
    omega
  have hraw := hn0 n hn
  rw [he] at hraw
  obtain ⟨g, hm, hfg, hE, hEnt, hs⟩ := exists_measurable_particleH1_representative f
  have h := hraw g.1 ⟨hm, g.2⟩
  change particleEntropy A N g ≤ ENNReal.ofReal (2 * t01RawParticleEnergy A N g.1 / r) at h
  rw [t01RawParticleEnergy_eq A N g.2] at h
  change particleEntropy A N g ≤ ENNReal.ofReal (2 * particleEnergy A N g / r) at h
  rw [← hE, ← hEnt] at h
  exact h.trans_eq (congrArg ENNReal.ofReal (by ring))

/-- Concrete symmetric tightening retains the original a.e. permutation-invariant
canonical H1 domain. Measurability is required only of comparison representatives. -/
theorem eventual_symmetric_particle_lsi_after_concrete_tightening (A : InteractionData d)
    {R : ℝ} (hR : 0 < R) (B : ℕ+) (C : ℝ)
    (hdef : ∀ N ≥ B, ∀ f : ParticleH1 A N, IsSymmetricParticleTest f →
      particleEntropy A N f ≤ ENNReal.ofReal
        (2 * particleEnergy A N f / R + C * ∫ x, f x ^ 2 ∂particleLaw A N))
    (hcomp : ∃ a : ℝ, R ≤ a ∧ ∀ M E0 ε : ℝ, 0 < M → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N, Measurable f.1 →
        IsSymmetricParticleTest f → (∀ x, |f x| ≤ M) → particleEnergy A N f ≤ E0 →
        ENNReal.ofReal (a / 2) * particleEntropy A N f ≤
          ENNReal.ofReal (particleEnergy A N f + ε))
    (hpoin : ∀ ρ : ℝ, ρ < R → ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N,
      IsSymmetricParticleTest f →
      ρ * ((∫ x, f x ^ 2 ∂particleLaw A N) - (∫ x, f x ∂particleLaw A N) ^ 2) ≤
        particleEnergy A N f)
    {r : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 A N, IsSymmetricParticleTest f →
      particleEntropy A N f ≤ ENNReal.ofReal ((2 / r) * particleEnergy A N f) := by
  have hyp := t01SymParticleTighteningHyp A hR B C hdef hcomp hpoin
  obtain ⟨n0, hn0⟩ := Analysis.abstract_eventual_exact_lsi_after_defect_removal hyp
    (fun n f hf _ c _ => t01RawParticleEnergy_split A _ hf.2.1 c) hr hrR
  refine eventually_atTop.mpr ⟨t01ParticleIndex B n0, fun N hN f hf => ?_⟩
  have hN' : (B : ℕ) + n0 ≤ (N : ℕ) := hN
  let n : ℕ := (N : ℕ) - (B : ℕ)
  have hn : n0 ≤ n := by dsimp only [n]; omega
  have he : t01ParticleIndex B n = N := by
    apply Subtype.ext
    change (B : ℕ) + n = (N : ℕ)
    dsimp only [n]
    omega
  have hraw := hn0 n hn
  rw [he] at hraw
  obtain ⟨g, hm, hfg, hE, hEnt, hs⟩ := exists_measurable_particleH1_representative f
  have h := hraw g.1 ⟨hm, g.2, hs.mp hf⟩
  change particleEntropy A N g ≤ ENNReal.ofReal (2 * t01RawParticleEnergy A N g.1 / r) at h
  rw [t01RawParticleEnergy_eq A N g.2] at h
  change particleEntropy A N g ≤ ENNReal.ofReal (2 * particleEnergy A N g / r) at h
  rw [← hE, ← hEnt] at h
  exact h.trans_eq (congrArg ENNReal.ofReal (by ring))

end DGPS.Lipschitz
