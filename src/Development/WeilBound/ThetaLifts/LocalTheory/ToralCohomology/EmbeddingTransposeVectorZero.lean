module

public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.SumPlSingle
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCyc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.PiInfUnitNe
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.ParZero

section

@[expose] public section

noncomputable section

open FockH1Action PositivityTheory.KReal

namespace PositivityTheory.ThKG.CayleyTransformDarboux

variable {R S R₁ S₁ : ℕ}

structure Emb (R S R₁ S₁ : ℕ) where
  e : Ix R₁ S₁ → Ix R S
  i : Fin R
  j : Fin S
  ε : ℝ
  ε_ne : ε ≠ 0
  inj : Function.Injective e
  cover : ∀ a, a = .inl i ∨ a = .inr j ∨ ∃ b, e b = a
  ne_i : ∀ b, e b ≠ .inl i
  ne_j : ∀ b, e b ≠ .inr j
  sb : ∀ a b, sameBlock (e a) (e b) ↔ sameBlock a b
  pos : ∀ a b, posC a b → posC (e a) (e b)
  ext : ∀ a b, (a = .inl i ∨ a = .inr j) → sameBlock a (e b) → (0 < ε → posC a (e b)) ∧ (ε < 0 → posC (e b) a)


open Classical in
def Emb.h (m : Emb R S R₁ S₁) (a : Ix R S) : ℝ := if a = .inl m.i ∨ a = .inr m.j then m.ε else 0

theorem Emb.h_e (m : Emb R S R₁ S₁) (b) : m.h (m.e b) = 0 := if_neg (not_or.2 ⟨m.ne_i b, m.ne_j b⟩)

theorem Emb.h_s (m : Emb R S R₁ S₁) {a} (h : a = .inl m.i ∨ a = .inr m.j) : m.h a = m.ε := if_pos h

theorem Emb.cases (m : Emb R S R₁ S₁) (a : Ix R S) : (a = .inl m.i ∨ a = .inr m.j) ∨ ∃ b, m.e b = a := or_assoc.2 (m.cover a)

theorem Emb.eq_of (m : Emb R S R₁ S₁) {a b : Ix R S} (ha : a = .inl m.i ∨ a = .inr m.j) (hb : b = .inl m.i ∨ b = .inr m.j)
    (h : sameBlock a b) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> first | rfl | exact h.elim

theorem Emb.sum (m : Emb R S R₁ S₁) {N : Type} [AddCommMonoid N] (g : Ix R S → N) :
    ∑ a, g a = g (.inl m.i) + g (.inr m.j) + ∑ b, g (m.e b) := by
  classical
  have : (Finset.univ : Finset (Ix R S)) = insert (.inl m.i) (insert (.inr m.j) (Finset.univ.image m.e)) := by
    ext a; simpa using m.cover a
  rw [this, Finset.sum_insert, Finset.sum_insert, Finset.sum_image fun a _ b _ h => m.inj h, add_assoc]
  · simpa using m.ne_j
  · simpa using m.ne_i

variable {ι M M₁ : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] [AddCommGroup M₁] [Module ℂ M₁]

structure IsPar (m : Emb R S R₁ S₁) (act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M) (act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁)
    (c c' : ι → ℂ) (D : M →ₗ[ℂ] M₁) : Prop where
  levi : ∀ w a b x, D (act (un w (m.e a) (m.e b)) x) = act₁ (un w a b) (D x)
  cpt : ∀ w x, D (act (un w (.inl m.i) (.inl m.i) + un w (.inr m.j) (.inr m.j)) x) = c w • D x
  hyp : ∀ w x, D (act (un w (.inl m.i) (.inr m.j) + un w (.inr m.j) (.inl m.i)) x) = c' w • D x
  cen : ∀ w x, D (act (un w (.inl m.i) (.inl m.i) - un w (.inl m.i) (.inr m.j) + un w (.inr m.j) (.inl m.i) -
    un w (.inr m.j) (.inr m.j)) x) = 0
  n₁ : ∀ w b x, D (act (un w (m.e b) (.inl m.i) - un w (m.e b) (.inr m.j)) x) = 0
  n₂ : ∀ w b x, D (act (un w (.inl m.i) (m.e b) + un w (.inr m.j) (m.e b)) x) = 0

theorem IsPar.sub {m : Emb R S R₁ S₁} {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M}
    {act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁} {c c' : ι → ℂ} {D D' : M →ₗ[ℂ] M₁} (h : IsPar m act act₁ c c' D)
    (h' : IsPar m act act₁ c c' D') (t : ℂ) : IsPar m act act₁ c c' (D' - t • D) := by
  refine ⟨fun w a b x => ?_, fun w x => ?_, fun w x => ?_, fun w x => ?_, fun w b x => ?_, fun w b x => ?_⟩ <;>
    rw [LinearMap.sub_apply, LinearMap.smul_apply]
  · rw [h.levi, h'.levi, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul]
  · rw [h.cpt, h'.cpt, LinearMap.sub_apply, LinearMap.smul_apply, smul_sub, smul_comm t]
  · rw [h.hyp, h'.hyp, LinearMap.sub_apply, LinearMap.smul_apply, smul_sub, smul_comm t]
  · rw [h.cen, h'.cen, smul_zero, sub_zero]
  · rw [h.n₁, h'.n₁, smul_zero, sub_zero]
  · rw [h.n₂, h'.n₂, smul_zero, sub_zero]

theorem HWMod.centre {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M} {Λ : ι → Ix R S → ℂ} {f : M} (h : HWMod act Λ f) (w : ι) (x : M) :
    ∑ a, act (un w a a) x = (∑ a, Λ w a) • x := by
  have e : ∑ a, un w a a = (Pi.single w 1 : ι → Mat R S) := by
    funext i
    by_cases h : i = w
    · subst h
      simp only [un, Finset.sum_apply, Pi.single_eq_same]
      ext a b
      simp only [Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply]
      split_ifs with e
      · subst e; simp
      · exact Finset.sum_eq_zero fun c _ => if_neg fun h => e (h.1.symm.trans h.2)
    · simp [un, Pi.single_eq_of_ne h]
  have : (act (Pi.single w 1)).eigenspace (∑ a, Λ w a) = ⊤ := by
    refine h.gen _ ?_ fun Z _ y hy => ?_
    · rw [Module.End.mem_eigenspace_iff, ← e]

      simp only [map_sum, LinearMap.sum_apply, h.wt, Finset.sum_smul]
    · have := shift_eig h.lie (H := Pi.single w 1) (Z := Z) (k := 0) (by
        funext i
        by_cases h : i = w
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]) hy
      rwa [add_zero] at this
  have hx : x ∈ (act (Pi.single w 1)).eigenspace (∑ a, Λ w a) := this ▸ Submodule.mem_top

  rw [Module.End.mem_eigenspace_iff, ← e, map_sum, LinearMap.sum_apply] at hx
  exact hx

theorem par_zero {m : Emb R S R₁ S₁} {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M}
    {act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁} {Λ : ι → Ix R S → ℂ} {f : M} (hM : HWMod act Λ f) {c c' : ι → ℂ}
    {D : M →ₗ[ℂ] M₁} (hD : IsPar m act act₁ c c' D) (hc : ∀ w, c w = Λ w (.inl m.i) + Λ w (.inr m.j)) (h0 : D f = 0) :
    D = 0 := by
  have hs : ∀ (g : Ix R S → ℂ), ∑ a, (m.h a : ℂ) * g a = m.ε * (g (.inl m.i) + g (.inr m.j)) := fun g => by
    rw [m.sum, m.h_s (.inl rfl), m.h_s (.inr rfl)]; simp [m.h_e, mul_add]
  have hlow : low (act (dg ι m.h)) (∑ w, ∑ a, m.h a * Λ w a) ≤ LinearMap.ker D := by
    refine low_ker D fun x => ?_
    rw [dg_eq]

    simp only [map_sum, LinearMap.sum_apply, Finset.sum_smul, hs]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← hc, mul_smul, ← hD.cpt, m.sum, m.h_s (.inl rfl), m.h_s (.inr rfl)]
    simp [m.h_e]
  obtain ⟨V, hV1, hV2, hV3⟩ := cyc_le hM.lie (sb := sameBlock) (pos := posC)
    (z := fun a b => sameBlock a b ∧ ∃ a' b', m.e a' = a ∧ m.e b' = b) (fun _ _ _ => sb_trans) sb_refl (fun _ _ => sb_of_pos) m.h
    (fun a b e => by
      rcases m.cases a with ha | ⟨a, rfl⟩ <;> rcases m.cases b with hb | ⟨b, rfl⟩
      · rw [m.h_s ha, m.h_s hb]
      · rw [m.h_s ha, m.h_e]
        exact not_lt.1 fun h => pos_asymm e ((m.ext a b ha (sb_of_pos e)).2 h)
      · rw [m.h_s hb, m.h_e]
        exact not_lt.1 fun h => pos_asymm e ((m.ext b a hb (sb_symm (sb_of_pos e))).1 h)
      · rw [m.h_e, m.h_e])
    (by rintro _ _ ⟨e, a, b, rfl, rfl⟩; exact ⟨e, by rw [m.h_e, m.h_e]⟩)
    (fun a b e e' => by
      rcases m.cases a with ha | ⟨a, rfl⟩ <;> rcases m.cases b with hb | ⟨b, rfl⟩
      · exact .inl (.inl (m.eq_of ha hb e))
      · rw [m.h_s ha, m.h_e] at e'
        exact .inl (.inr ((m.ext a b ha e).1 (e'.lt_of_ne m.ε_ne.symm)))
      · rw [m.h_s hb, m.h_e] at e'
        exact .inl (.inr ((m.ext b a hb (sb_symm e)).2 (e'.lt_of_ne m.ε_ne)))
      · exact .inr ⟨e, a, b, rfl, rfl⟩)
    hM.wt hM.pos (N := LinearMap.ker D) h0
    (by
      rintro w _ _ ⟨-, a, b, rfl, rfl⟩ x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hD.levi, hx, map_zero])
  have hVk : V ≤ LinearMap.ker D := hV2.trans (sup_le le_rfl hlow)
  set K := alg ι (sameBlock (p := R) (q := S))
  set P := stab act (LinearMap.ker D)
  have mP : ∀ Z (t : ℂ), (∀ x, D (act Z x) = t • D x) → Z ∈ K ⊔ P := fun Z t h => Submodule.mem_sup_right fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢; rw [h, hx, smul_zero]
  have mK : ∀ w {a b : Ix R S}, sameBlock a b → un w a b ∈ K ⊔ P := fun w _ _ e => Submodule.mem_sup_left (un_mem w e)
  have hij : ∀ w, un w (.inl m.i) (.inr m.j) ∈ K ⊔ P ∧ un w (.inr m.j) (.inl m.i) ∈ K ⊔ P := fun w => by
    have a1 := mP _ _ (hD.hyp w)
    have a2 := mP _ 0 fun x => (hD.cen w x).trans (zero_smul _ _).symm
    have a3 := mK w (sb_refl (.inl m.i : Ix R S))
    have a4 := mK w (sb_refl (.inr m.j : Ix R S))
    constructor
    · convert Submodule.smul_mem _ (1 / 2 : ℂ) (sub_mem (add_mem (sub_mem a1 a2) a3) a4) using 1
      module
    · convert Submodule.smul_mem _ (1 / 2 : ℂ) (add_mem (sub_mem (add_mem a1 a2) a3) a4) using 1
      module
  have tri : ∀ b : Ix R S, sameBlock b (.inl m.i) ∨ sameBlock b (.inr m.j) := fun b => by cases b <;> simp [sameBlock]
  have hb : ∀ w b, (un w (m.e b) (.inl m.i) ∈ K ⊔ P ∧ un w (m.e b) (.inr m.j) ∈ K ⊔ P) ∧
      un w (.inl m.i) (m.e b) ∈ K ⊔ P ∧ un w (.inr m.j) (m.e b) ∈ K ⊔ P := fun w b => by
    have a1 := mP _ 0 fun x => (hD.n₁ w b x).trans (zero_smul _ _).symm
    have a2 := mP _ 0 fun x => (hD.n₂ w b x).trans (zero_smul _ _).symm
    rcases tri (m.e b) with e | e
    · have a3 := mK w e
      have a4 := mK w (sb_symm e)
      exact ⟨⟨a3, by simpa using sub_mem a3 a1⟩, a4, by simpa using sub_mem a2 a4⟩
    · have a3 := mK w e
      have a4 := mK w (sb_symm e)
      exact ⟨⟨by simpa using add_mem a1 a3, a3⟩, by simpa using sub_mem a2 a4, a4⟩
  have top : (⊤ : Submodule ℂ (ι → Mat R S)) ≤ K ⊔ P := by
    refine le_trans (fun Z _ => ?_ : _ ≤ alg ι fun _ _ => True) (alg_le fun w a b _ => ?_)
    · exact fun _ _ _ h => (h trivial).elim
    · rcases m.cover a with rfl | rfl | ⟨a, rfl⟩ <;> rcases m.cover b with rfl | rfl | ⟨b, rfl⟩
      exacts [mK w (sb_refl _), (hij w).1, (hb w b).2.1, (hij w).2, mK w (sb_refl _), (hb w b).2.2, (hb w a).1.1, (hb w a).1.2,
        Submodule.mem_sup_right fun x hx => by rw [LinearMap.mem_ker] at hx ⊢; rw [hD.levi, hx, map_zero]]
  obtain ⟨W, hW1, hW2, hW3⟩ := gen_le hM.lie (g := ⊤) (q := K) (l := P) (fun _ _ _ _ => trivial) le_top le_top top hV3 hVk
    fun Z hZ => hZ
  rw [hM.gen W (hW1 hV1) hW3] at hW2
  exact LinearMap.ker_eq_top.1 (top_le_iff.1 hW2)

theorem par_line {m : Emb R S R₁ S₁} {act : (ι → Mat R S) →ₗ[ℂ] Module.End ℂ M}
    {act₁ : (ι → Mat R₁ S₁) →ₗ[ℂ] Module.End ℂ M₁} {Λ : ι → Ix R S → ℂ} {Λ₁ : ι → Ix R₁ S₁ → ℂ} {f : M} {f₁ : M₁}
    (hM : HWMod act Λ f) (hM₁ : HWMod act₁ Λ₁ f₁) (hΛ : ∀ w b, Λ w (m.e b) = Λ₁ w b) {c c' : ι → ℂ}
    {D D' : M →ₗ[ℂ] M₁} (hD : IsPar m act act₁ c c' D) (hD' : IsPar m act act₁ c c' D') (h0 : D ≠ 0) :
    ∃ t : ℂ, D' = t • D := by
  obtain ⟨x, hx⟩ : ∃ x, D x ≠ 0 := by
    by_contra h
    exact h0 (LinearMap.ext fun x => not_not.1 fun e => h ⟨x, e⟩)
  have hc : ∀ w, c w = Λ w (.inl m.i) + Λ w (.inr m.j) := fun w => by
    have e := congrArg D (hM.centre w x)

    rw [m.sum, m.sum, map_add (f := _), ← LinearMap.add_apply, ← map_add act, hD.cpt, map_sum, map_smul] at e
    simp only [hD.levi, hM₁.centre, hΛ] at e
    rw [← add_smul] at e
    exact add_right_cancel (smul_left_injective ℂ hx e)
  have val : ∀ {E : M →ₗ[ℂ] M₁}, IsPar m act act₁ c c' E → ∃ t : ℂ, E f = t • f₁ := fun {E} hE =>
    hM₁.one _ (fun w a => by rw [← hE.levi, hM.wt, map_smul, hΛ]) fun w a b e => by
      rw [← hE.levi, hM.pos w _ _ (m.pos a b e), map_zero]
  obtain ⟨t, ht⟩ := val hD
  obtain ⟨t', ht'⟩ := val hD'
  have t0 : t ≠ 0 := fun e => h0 (par_zero hM hD hc (by rw [ht, e, zero_smul]))
  refine ⟨t' / t, sub_eq_zero.1 (par_zero hM (hD.sub hD' _) hc ?_)⟩
  rw [LinearMap.sub_apply, LinearMap.smul_apply, ht, ht', smul_smul, div_mul_cancel₀ _ t0, sub_self]

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end
end

-- Source module: Development.WeilBound.ThetaLifts.LocalTheory.ToralCohomology.EmbeddingTransposeVectorZero

section

@[expose] public section

noncomputable section

open scoped Matrix Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open FockH1Action (Mat Ix sameBlock posC)
open Formalism.BasicNotions.TH (upq Jm)

namespace PositivityTheory.ThKG.CayleyTransformDarboux

section Exp

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem hasSum_exp (A : Matrix I I ℂ) (v : I → ℂ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (A ^ n *ᵥ v)) (NormedSpace.exp A *ᵥ v) := by
  letI := Matrix.linftyOpNormedRing (n := I) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := I) (R := ℂ) (α := ℂ)
  have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  let L : Matrix I I ℂ →ₗ[ℂ] (I → ℂ) := (Matrix.mulVecBilin ℂ ℂ).flip v
  have := h.map L L.continuous_of_finiteDimensional
  convert (preTransparency := .reducible) this using 1
  · funext n
    exact (Matrix.smul_mulVec _ _ _).symm
  · rfl

theorem exp_int {A : Matrix I I ℂ} {B : Matrix J J ℂ} {P : Matrix I J ℂ} (h : A * P = P * B) (u : J → ℂ) :
    NormedSpace.exp A *ᵥ (P *ᵥ u) = P *ᵥ (NormedSpace.exp B *ᵥ u) := by
  have hn : ∀ n : ℕ, A ^ n * P = P * B ^ n := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, pow_succ, Matrix.mul_assoc]
  have h2 := (hasSum_exp B u).map P.mulVecLin P.mulVecLin.continuous_of_finiteDimensional
  refine (hasSum_exp A _).unique ?_
  simpa [Function.comp_def, hn, Matrix.mulVec_smul] using h2

theorem exp_eig {A : Matrix I I ℂ} {v : I → ℂ} {c : ℂ} (h : A *ᵥ v = c • v) : NormedSpace.exp A *ᵥ v = Complex.exp c • v := by
  have hn : ∀ n : ℕ, A ^ n *ᵥ v = c ^ n • v := fun n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  refine (hasSum_exp A v).unique ?_
  have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const v
  rw [← Complex.exp_eq_exp_ℂ] at this
  simpa [hn, smul_smul] using this

theorem exp_nil {A : Matrix I I ℂ} {v : I → ℂ} (h : A *ᵥ (A *ᵥ v) = 0) : NormedSpace.exp A *ᵥ v = v + A *ᵥ v := by
  refine (hasSum_exp A v).unique ?_
  have := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (A ^ n *ᵥ v)) (s := Finset.range 2) (fun n hn => by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ n from not_lt.1 (mt Finset.mem_range.2 hn))
      rw [pow_succ, pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero, smul_zero])
  simpa [Finset.sum_range_succ] using this

end Exp

variable {R S R₁ S₁ : ℕ}

def sg : Ix R S → ℂ := Sum.elim (fun _ => 1) fun _ => -1

theorem Jm_sg (r s : ℕ) : Jm r s = Matrix.diagonal sg := Jm_eq r s

theorem star_sg (a : Ix R S) : star (sg a) = sg a := by cases a <;> simp [sg]

theorem sg_sq (a : Ix R S) : sg a * sg a = 1 := by cases a <;> simp [sg]

def Emb.P (m : Emb R S R₁ S₁) : Matrix (Ix R S) (Ix R₁ S₁) ℂ := fun a b => if a = m.e b then 1 else 0

def Emb.x (m : Emb R S R₁ S₁) : Ix R S → ℂ := Pi.single (.inl m.i) 1 + Pi.single (.inr m.j) 1

def Emb.y (m : Emb R S R₁ S₁) : Ix R S → ℂ := Pi.single (.inl m.i) 1 - Pi.single (.inr m.j) 1

def embA (R S : ℕ) : Emb (R + 1) (S + 1) R S where
  e := Sum.map Fin.succ Fin.succ
  i := 0
  j := 0
  ε := 1
  ε_ne := one_ne_zero
  inj := (Fin.succ_injective _).sumMap (Fin.succ_injective _)
  cover := by
    rintro (a | a) <;> refine Fin.cases ?_ (fun b => ?_) a
    exacts [.inl rfl, .inr (.inr ⟨.inl b, rfl⟩), .inr (.inl rfl), .inr (.inr ⟨.inr b, rfl⟩)]
  ne_i := by rintro (b | b) <;> simp [Fin.succ_ne_zero]
  ne_j := by rintro (b | b) <;> simp [Fin.succ_ne_zero]
  sb := by rintro (a | a) (b | b) <;> simp [sameBlock]
  pos := by rintro (a | a) (b | b) <;> simp [posC]
  ext := by rintro a (b | b) (rfl | rfl) <;> simp [posC, sameBlock] <;> norm_num

def embB (R S : ℕ) : Emb (R + 1) (S + 1) R S where
  e := Sum.map Fin.castSucc Fin.castSucc
  i := Fin.last R
  j := Fin.last S
  ε := -1
  ε_ne := by norm_num
  inj := (Fin.castSucc_injective _).sumMap (Fin.castSucc_injective _)
  cover := by
    rintro (a | a) <;> refine Fin.lastCases ?_ (fun b => ?_) a
    exacts [.inl rfl, .inr (.inr ⟨.inl b, rfl⟩), .inr (.inl rfl), .inr (.inr ⟨.inr b, rfl⟩)]
  ne_i := by rintro (b | b) <;> simp [Fin.castSucc_ne_last]
  ne_j := by rintro (b | b) <;> simp [Fin.castSucc_ne_last]
  sb := by rintro (a | a) (b | b) <;> simp [sameBlock]
  pos := by rintro (a | a) (b | b) <;> simp [posC]
  ext := by rintro a (b | b) (rfl | rfl) <;> simp [posC, sameBlock, Fin.castSucc_lt_last] <;> norm_num

theorem sg_embA (R S : ℕ) (b) : sg ((embA R S).e b) = sg b := by cases b <;> rfl

theorem sg_embB (R S : ℕ) (b) : sg ((embB R S).e b) = sg b := by cases b <;> rfl

theorem Emb.embeddingMatrix_mulVec (m : Emb R S R₁ S₁) (u : Ix R₁ S₁ → ℂ) :
    (m.P *ᵥ u) (.inl m.i) = 0 ∧ (m.P *ᵥ u) (.inr m.j) = 0 ∧ ∀ b, (m.P *ᵥ u) (m.e b) = u b := by
  refine ⟨?_, ?_, fun b => ?_⟩ <;> simp [Emb.P, Matrix.mulVec, dotProduct, (m.ne_i _).symm, (m.ne_j _).symm, m.inj.eq_iff]

theorem Emb.tP (m : Emb R S R₁ S₁) (v : Ix R S → ℂ) (b) : (m.Pᵀ *ᵥ v) b = v (m.e b) := by
  simp [Emb.P, Matrix.mulVec, dotProduct]

theorem Emb.embedding_transpose_vector_zero (m : Emb R S R₁ S₁) : m.Pᵀ *ᵥ m.x = 0 := by
  funext b; simp [m.tP, Emb.x, Pi.single_eq_of_ne (m.ne_i b), Pi.single_eq_of_ne (m.ne_j b)]

theorem Emb.transpose_mulVec_y_eq_zero (m : Emb R S R₁ S₁) : m.Pᵀ *ᵥ m.y = 0 := by
  funext b; simp [m.tP, Emb.y, Pi.single_eq_of_ne (m.ne_i b), Pi.single_eq_of_ne (m.ne_j b)]

theorem Emb.tPP (m : Emb R S R₁ S₁) : m.Pᵀ * m.P = 1 := by
  ext a b; simp [Emb.P, Matrix.mul_apply, m.inj.eq_iff, Matrix.one_apply, eq_comm]

theorem Emb.conj_single (m : Emb R S R₁ S₁) (a b) : m.P * Matrix.single a b (1 : ℂ) * m.Pᵀ = Matrix.single (m.e a) (m.e b) 1 := by
  ext c d
  simp only [Matrix.mul_apply, Matrix.single_apply, Emb.P, Matrix.transpose_apply]
  rw [Finset.sum_eq_single b, Finset.sum_eq_single a] <;> simp +contextual [eq_comm, ite_and]
  split_ifs <;> rfl

theorem Emb.JP (m : Emb R S R₁ S₁) (hs : ∀ b, sg (m.e b) = sg b) : Jm R S * m.P = m.P * Jm R₁ S₁ := by
  ext a b
  rw [Jm_sg, Jm_sg, Matrix.diagonal_mul, Matrix.mul_diagonal, Emb.P]
  split_ifs with h
  · rw [h, hs, mul_comm]
  · simp

theorem Emb.conj_upq (m : Emb R S R₁ S₁) (hs : ∀ b, sg (m.e b) = sg b) {Y : Mat R₁ S₁} (h : Y ∈ upq R₁ S₁) :
    m.P * Y * m.Pᵀ ∈ upq R S := by
  have h1 : m.Pᴴ = m.Pᵀ := by ext a b; simp [Emb.P]
  have h2 : m.Pᵀᴴ = m.P := by ext a b; simp [Emb.P]
  have h3 : m.Pᵀ * Jm R S = Jm R₁ S₁ * m.Pᵀ := by
    have := congrArg Matrix.conjTranspose (m.JP hs)
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Jm_star, Jm_star, h1] at this
  have h4 : Yᴴ * Jm R₁ S₁ + Jm R₁ S₁ * Y = 0 := h
  change (m.P * Y * m.Pᵀ)ᴴ * _ + _ = 0
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, h1, h2]
  calc _ = m.P * (Yᴴ * Jm R₁ S₁ + Jm R₁ S₁ * Y) * m.Pᵀ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, h3]
        rw [← Matrix.mul_assoc (Jm R S), m.JP hs, Matrix.mul_assoc]
    _ = 0 := by rw [h4]; simp

theorem single_mulVec' (a b : Ix R S) (v : Ix R S → ℂ) : Matrix.single a b (1 : ℂ) *ᵥ v = v b • Pi.single a 1 := by
  funext c
  by_cases e : c = a
  · subst e; simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, Ne.symm e, Pi.single_eq_of_ne e]

theorem J_single (a b : Ix R S) : Jm R S * Matrix.single a b (1 : ℂ) = sg a • Matrix.single a b 1 := by
  ext c d; rw [Jm_sg, Matrix.diagonal_mul]; simp only [Matrix.smul_apply, Matrix.single_apply]; split_ifs with h <;> simp [h]

theorem single_J (a b : Ix R S) : Matrix.single a b (1 : ℂ) * Jm R S = sg b • Matrix.single a b 1 := by
  ext c d; rw [Jm_sg, Matrix.mul_diagonal]; simp only [Matrix.smul_apply, Matrix.single_apply]; split_ifs with h <;> simp [h]

theorem sg_l (i : Fin R) : sg (.inl i : Ix R S) = 1 := rfl

theorem sg_r (i : Fin S) : sg (.inr i : Ix R S) = -1 := rfl

def hf {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (u v : Fin d → ℂ) : ℂ := u ⬝ᵥ M *ᵥ star v

theorem gram_apply {d : ℕ} {I : Type} (M : Matrix (Fin d) (Fin d) ℂ) (C : Matrix (Fin d) I ℂ) (a b : I) :
    (Cᵀ * M * C.map star) a b = hf M (fun r => C r a) (fun r => C r b) := by
  rw [Matrix.mul_assoc]; rfl

theorem exists_frame (m : Emb R S R₁ S₁) (hs : ∀ b, sg (m.e b) = sg b) {d d₁ : ℕ} (hd : d = R + S)
    {M θ : Matrix (Fin d) (Fin d) ℂ} {M₁ θ₁ : Matrix (Fin d₁) (Fin d₁) ℂ} (hM : ∀ i j, M j i = star (M i j)) (hθ : IsCartan M θ)
    {x y : Fin d → ℂ} {ι : Matrix (Fin d) (Fin d₁) ℂ} (x0 : x ≠ 0) (xx : hf M x x = 0) {c : ℂ} (c0 : c ≠ 0) (hy : y = c • θ *ᵥ x)
    (ox : ∀ k, hf M (fun r => ι r k) x = 0) (oy : ∀ k, hf M (fun r => ι r k) y = 0) (hg : ιᵀ * M * ι.map star = M₁)
    (hθι : θ * ι = ι * θ₁) {C₁ : Matrix (Fin d₁) (Ix R₁ S₁) ℂ} (hC₁ : IsFrame M₁ C₁) (hθ₁ : θ₁ * C₁ = C₁ * Jm R₁ S₁) :
    ∃ (C : Matrix (Fin d) (Ix R S) ℂ) (n n' : ℂ), IsFrame M C ∧ θ * C = C * Jm R S ∧ n ≠ 0 ∧ x = n • C *ᵥ m.x ∧
      y = n' • C *ᵥ m.y ∧ C * m.P = ι * C₁ := by
  have herm : ∀ u v, hf M v u = star (hf M u v) := fun u v => by
    simp only [hf, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum, ← hM]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have iso : ∀ u v, hf M (θ *ᵥ u) (θ *ᵥ v) = hf M u v := fun u v => by
    conv_rhs => rw [← hθ.2.1]
    rw [hf, hf, show star (θ *ᵥ v) = θ.map star *ᵥ star v by
      funext i; simp [Matrix.mulVec, dotProduct, star_sum], Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]
  have θθ : ∀ u, θ *ᵥ (θ *ᵥ u) = u := fun u => by rw [Matrix.mulVec_mulVec, hθ.1, Matrix.one_mulVec]
  have addl : ∀ u u' v (s : ℂ), hf M (u + s • u') v = hf M u v + s * hf M u' v := fun u u' v s => by simp [hf]
  have addr : ∀ u v v' (s : ℂ), hf M u (v + s • v') = hf M u v + star s * hf M u v' := fun u v v' s => by
    simp [hf, Matrix.mulVec_add, Matrix.mulVec_smul]
  have sml : ∀ u v (s : ℂ), hf M (s • u) v = s * hf M u v := fun u v s => by simp [hf]
  have smr : ∀ u v (s : ℂ), hf M u (s • v) = star s * hf M u v := fun u v s => by simp [hf, Matrix.mulVec_smul]
  set z := θ *ᵥ x with hz
  have zz : hf M z z = 0 := (iso x x).trans xx
  have zx : hf M x z = hf M z x := by rw [← iso x z, hz, θθ]
  set k := (hf M z x).re with hk
  have k0 : 0 < k := hθ.2.2 x x0
  have zk : hf M z x = k := by
    have := herm z x
    rw [zx] at this
    exact (Complex.conj_eq_iff_re.1 this.symm).symm
  set N : ℂ := (((Real.sqrt (2 * k))⁻¹ : ℝ) : ℂ) with hN
  have sN : star N = N := Complex.conj_ofReal _
  have NN : N * N * (2 * k) = 1 := by
    rw [hN]; norm_cast
    rw [← mul_inv, Real.mul_self_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  have N0 : N ≠ 0 := fun e => by rw [e] at NN; simp at NN
  have oz : ∀ k, hf M (fun r => ι r k) z = 0 := fun k => by
    have := oy k
    rw [hy, smr, mul_eq_zero] at this
    exact this.resolve_left (star_ne_zero.2 c0)
  have col : ∀ (v) (b), (∀ k, hf M (fun r => ι r k) v = 0) → hf M (fun r => (ι * C₁) r b) v = 0 := fun v b h => by
    have : hf M (fun r => (ι * C₁) r b) v = ∑ k, C₁ k b * hf M (fun r => ι r k) v := by
      simp only [hf, dotProduct, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    simp [this, h]
  let cl : Ix R S → Fin d → ℂ := fun a => if a = .inl m.i then N • (x + (1 : ℂ) • z) else if a = .inr m.j then
    N • (x + (-1 : ℂ) • z) else Function.extend m.e (fun b r => (ι * C₁) r b) 0 a
  have ci : cl (.inl m.i) = N • (x + (1 : ℂ) • z) := if_pos rfl
  have cj : cl (.inr m.j) = N • (x + (-1 : ℂ) • z) := by simp [cl]
  have ce : ∀ b, cl (m.e b) = fun r => (ι * C₁) r b := fun b => by
    simp only [cl, if_neg (m.ne_i b), if_neg (m.ne_j b), m.inj.extend_apply]
  have o1 : ∀ b (s : ℂ), hf M (fun r => (ι * C₁) r b) (N • (x + s • z)) = 0 := fun b s => by
    rw [smr, addr, col _ b ox, col _ b oz]; simp
  have gram : (Matrix.of fun r a => cl a r)ᵀ * M * (Matrix.of fun r a => cl a r).map star = Jm R S := by
    ext a b
    rw [gram_apply, Jm_sg]
    change hf M (cl a) (cl b) = _
    rcases m.cover a with rfl | rfl | ⟨a, rfl⟩ <;> rcases m.cover b with rfl | rfl | ⟨b, rfl⟩ <;>
      simp only [ci, cj, ce]
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, Matrix.diagonal_apply_eq, sg_l, star_one]
      linear_combination NN
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, star_neg, star_one]
      rw [Matrix.diagonal_apply_ne _ (by simp)]; ring
    · rw [herm, o1, Matrix.diagonal_apply_ne _ (m.ne_i b).symm, star_zero]
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, star_neg, star_one]
      rw [Matrix.diagonal_apply_ne _ (by simp)]; ring
    · simp only [sml, smr, addl, addr, xx, zz, zx, zk, sN, Matrix.diagonal_apply_eq, sg_r, star_neg, star_one]
      linear_combination -NN
    · rw [herm, o1, Matrix.diagonal_apply_ne _ (m.ne_j b).symm, star_zero]
    · rw [o1, Matrix.diagonal_apply_ne _ (m.ne_i a)]
    · rw [o1, Matrix.diagonal_apply_ne _ (m.ne_j a)]
    · rw [← gram_apply, Matrix.transpose_mul, show (ι * C₁).map star = ι.map star * C₁.map star from
        Matrix.map_mul (f := starRingEnd ℂ), show C₁ᵀ * ιᵀ * M * (ι.map star * C₁.map star) =
          C₁ᵀ * (ιᵀ * M * ι.map star) * C₁.map star by simp only [Matrix.mul_assoc], hg, hC₁.1, Jm_sg]
      by_cases e : a = b
      · subst e; simp [hs]
      · rw [Matrix.diagonal_apply_ne _ e, Matrix.diagonal_apply_ne _ (m.inj.ne e)]
  refine ⟨Matrix.of fun r a => cl a r, (2 * N)⁻¹, c * (2 * N)⁻¹, ⟨gram, ?_⟩, ?_, by simp [N0], ?_, ?_, ?_⟩
  · set C : Matrix (Fin d) (Ix R S) ℂ := Matrix.of fun r a => cl a r
    have h1 : (Jm R S * (Cᵀ * M)) * C.map star = 1 := by rw [Matrix.mul_assoc, gram, Jm_sq]
    have h2 := (Matrix.mul_eq_one_comm_of_card_eq _ _ ℂ (by simp [hd])).1 h1
    refine ⟨(Jm R S * (Cᵀ * M)).map star, ?_⟩
    have h3 := congrArg (fun A : Matrix (Fin d) (Fin d) ℂ => A.map (starRingEnd ℂ)) h2
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h3
    rw [← h3, ← Matrix.map_mul, ← Matrix.map_mul]
    congr 1
    ext; simp
  · ext r a
    rw [Jm_sg, Matrix.mul_diagonal]
    change (θ *ᵥ cl a) r = cl a r * sg a
    rcases m.cover a with rfl | rfl | ⟨a, rfl⟩
    · rw [ci, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, θθ]; simp only [sg_l, hz, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    · rw [cj, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_smul, θθ]; simp [sg_r, hz]; ring
    · rw [ce, hs]
      change (θ * (ι * C₁)) r a = _
      rw [← Matrix.mul_assoc, hθι, Matrix.mul_assoc, hθ₁, ← Matrix.mul_assoc, Jm_sg, Matrix.mul_diagonal]
  · funext r
    simp only [Emb.x, Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.smul_apply, Pi.add_apply, Matrix.col_apply,
      Matrix.of_apply, ci, cj, smul_eq_mul]
    field_simp; ring
  · funext r
    simp only [hy, Emb.y, Matrix.mulVec_sub, Matrix.mulVec_single_one, Pi.smul_apply, Pi.add_apply, Pi.sub_apply,
      Matrix.col_apply, Matrix.of_apply, ci, cj, smul_eq_mul]
    field_simp; ring
  · ext r b
    simp [Matrix.mul_apply (M := Matrix.of _), Emb.P, ce]

end PositivityTheory.ThKG.CayleyTransformDarboux

end
end
end
