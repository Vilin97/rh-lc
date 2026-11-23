module

public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompEq

section

@[expose] public section

namespace GlobalTheory.AbsolutelyIrreduciblePullback

open Formalism.MainNotions.N

def pullSub {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (W : Submodule L (Fin n → L)) : Submodule K (Fin n → K) where
  carrier := {v | f ∘ v ∈ W}
  add_mem' := by
    intro a b ha hb
    have : f ∘ (a + b) = f ∘ a + f ∘ b := by
      funext i; simp
    show f ∘ (a + b) ∈ W
    rw [this]
    exact W.add_mem ha hb
  zero_mem' := by
    have : f ∘ (0 : Fin n → K) = 0 := by
      funext i; simp
    show f ∘ (0 : Fin n → K) ∈ W
    rw [this]
    exact W.zero_mem
  smul_mem' := by
    intro c v hv
    have : f ∘ (c • v) = f c • (f ∘ v) := by
      funext i; simp
    show f ∘ (c • v) ∈ W
    rw [this]
    exact W.smul_mem _ hv

theorem mem_pullSub {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (W : Submodule L (Fin n → L)) (v : Fin n → K) : v ∈ pullSub f W ↔ f ∘ v ∈ W := by
  exact Iff.rfl

theorem exists_comp_eq {K L : Type} [Field K] [Field L] (f : K →+* L) (hf : Function.Surjective f)
    {n : ℕ} (w : Fin n → L) : ∃ v : Fin n → K, f ∘ v = w := by
  choose v hv using fun i => hf (w i)
  exact ⟨v, funext hv⟩

theorem isInv_pullSub {Γ : Type} [Group Γ] {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (ρ : Γ →* GL (Fin n) K) (W : Submodule L (Fin n → L)) (hW : IsInv (mapRep f ρ) W) :
    IsInv ρ (pullSub f W) := by
  intro g v hv
  rw [mem_pullSub] at hv ⊢
  have heq : f ∘ ((ρ g : Matrix (Fin n) (Fin n) K).mulVec v) =
      ((mapRep f ρ g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec (f ∘ v) := by
    funext i
    exact RingHom.map_mulVec f _ v i
  rw [heq]
  exact hW g (f ∘ v) hv

theorem absIrrSub_top {Γ : Type} [Group Γ] {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    (hn : 1 ≤ n) (ρ : Γ →* GL (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), IsInv ρ W → W = ⊥ ∨ W = ⊤) : AbsIrrSub ρ ⊤ := by
  have hsurj : Function.Surjective (algebraMap K (AlgebraicClosure K)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := AlgebraicClosure K)).2
  have hspan : Submodule.span (AlgebraicClosure K)
      ((fun v => (algebraMap K (AlgebraicClosure K)) ∘ v) '' ((⊤ : Submodule K (Fin n → K)) : Set (Fin n → K))) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
    exact Submodule.subset_span ⟨v, Submodule.mem_top, rfl⟩
  unfold AbsIrrSub IsIrrSub
  rw [hspan]
  refine ⟨?_, fun _ _ _ => trivial, ?_⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    exact top_ne_bot
  · intro W' _ hW'
    rcases h _ (isInv_pullSub (algebraMap K (AlgebraicClosure K)) ρ W' hW') with h0 | h1
    · left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
      have hv : v ∈ pullSub (algebraMap K (AlgebraicClosure K)) W' := (mem_pullSub _ _ _).mpr hw
      rw [h0, Submodule.mem_bot] at hv
      subst hv
      rw [Submodule.mem_bot]
      funext i
      simp
    · right
      rw [eq_top_iff]
      intro w _
      obtain ⟨v, rfl⟩ := exists_comp_eq (algebraMap K (AlgebraicClosure K)) hsurj w
      have hv : v ∈ pullSub (algebraMap K (AlgebraicClosure K)) W' := by
        rw [h1]
        trivial
      exact (mem_pullSub _ _ _).mp hv

end GlobalTheory.AbsolutelyIrreduciblePullback
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsSide

section

@[expose] public section

namespace GlobalTheory.SatakeMainTheorem

theorem main {K : Type} [Field K] (W : Submodule K (Fin (1 : ℕ) → K)) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  · right
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).mp h
    have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv0
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simpa using h0
    rw [eq_top_iff]
    intro w _
    have hw : w = (w 0 / v 0) • v := by
      funext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp [div_mul_cancel₀ _ h0]
    rw [hw]
    exact W.smul_mem _ hv

end GlobalTheory.SatakeMainTheorem
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCountOfSsRank

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.ResidualRankCount

section Alg

variable {Γ : Type} [Group Γ]

theorem absIrr_id {K : Type} [Field K] [IsAlgClosed K] {n : ℕ} (hn : 1 ≤ n) (ρ : Γ →* GL (Fin n) K)
    (h : ∀ W : Submodule K (Fin n → K), IsInv ρ W → W = ⊥ ∨ W = ⊤) : AbsIrrSub ρ ⊤ := by
  first
  | exact @_root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top
  | exact _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top
  | (apply _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AbsolutelyIrreduciblePullback.absIrrSub_top ..)

theorem twGL_val {K : Type} [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K) =
      (χ g : K) • ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) := by
  show algebraMap K (Matrix (Fin a) (Fin a) K) (χ g : K) * ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem isInv_of_twGL {K : Type} [Field K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ)
    (W : Submodule K (Fin a → K)) (h : IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W) : IsInv ρ W := by
  intro g v hv
  have h1 := W.smul_mem ((χ g : K)⁻¹) (h g v hv)
  rwa [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h1

theorem charpoly_smul_inf {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) : (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem charpoly_twGL {K : Type} [Field K] [Infinite K] {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K).charpoly =
      ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K).charpoly.scaleRoots (χ g : K) := by
  rw [twGL_val, charpoly_smul_inf _ (Units.ne_zero _)]

theorem charpoly_scal {K : Type} [Field K] (c : K) :
    (algebraMap K (Matrix (Fin 1) (Fin 1) K) c).charpoly = X - C c := by
  rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal, Fin.prod_univ_one]

theorem sub_fin_one {K : Type} [Field K] (W : Submodule K (Fin 1 → K)) : W = ⊥ ∨ W = ⊤ := by
  first
  | exact @_root_.GlobalTheory.SatakeMainTheorem.main
  | exact _root_.GlobalTheory.SatakeMainTheorem.main
  | (apply _root_.GlobalTheory.SatakeMainTheorem.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SatakeMainTheorem.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SatakeMainTheorem.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SatakeMainTheorem.main ..)

theorem scaleRoots_list_prod {K : Type} [Field K] (l : List K[X]) (s : K) :
    l.prod.scaleRoots s = (l.map fun p => p.scaleRoots s).prod := by
  induction l with
  | nil => rw [List.prod_nil, one_scaleRoots, List.map_nil, List.prod_nil]
  | cons p l ih => rw [List.prod_cons, mul_scaleRoots_of_noZeroDivisors, ih, List.map_cons, List.prod_cons]

theorem charpoly_list_monic {K : Type} [Field K] (L : List (Σ m : ℕ, Γ →* GL (Fin m) K)) (g : Γ) :
    (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod.Monic ∧
    (L.map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) K).charpoly).prod.natDegree =
      (L.map fun p => p.1).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    refine ⟨(Matrix.charpoly_monic _).mul ih.1, ?_⟩
    rw [(Matrix.charpoly_monic _).natDegree_mul ih.1, ih.2, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

end Alg

section Lists

theorem prod_map_flatMap {α β M : Type} [CommMonoid M] (l : List α) (f : α → List β) (F : β → M) :
    ((l.flatMap f).map F).prod = (l.map fun a => ((f a).map F).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.prod_append, ih, List.map_cons, List.prod_cons]

theorem coe_flatMap {α β : Type} (l : List α) (f : α → List β) :
    ((l.flatMap f : List β) : Multiset β) = (l.map fun a => ((f a : List β) : Multiset β)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, ← Multiset.coe_add, ih, List.map_cons, List.sum_cons]

theorem prod_range_list {M : Type} [CommMonoid M] (f : ℕ → M) : ∀ d : ℕ,
    ∏ a ∈ Finset.range d, f a = ((List.range d).map f).prod
  | 0 => by simp
  | d + 1 => by
    rw [Finset.prod_range_succ, prod_range_list f d, List.range_succ, List.map_append, List.prod_append]
    simp

theorem sum_range_const {M : Type} [AddCommMonoid M] (x : M) : ∀ d : ℕ,
    ((List.range d).map fun _ => x).sum = d • x
  | 0 => by simp
  | d + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_const x d, succ_nsmul]
    simp

end Lists

section Psi

theorem exists_psi {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (NA : NAut N) (i : N.Loc)
    {B : Type} [CommRing B] [IsLocalRing B] (j : B →+* Qbar (N.l i)) (hj : Function.Injective j)
    (hran : Set.range j = {x : Qbar (N.l i) | ‖x‖ ≤ 1})
    (hmax : ∀ x : B, x ∈ IsLocalRing.maximalIdeal B ↔ ‖j x‖ < 1) :
    ∃ ψ : N.O i →+* B, (∀ a, j (ψ a) = iotaOQ N NA i a) ∧
      ∃ φ : IsLocalRing.ResidueField (N.O i) →+* IsLocalRing.ResidueField B,
        ∀ a, φ (IsLocalRing.residue (N.O i) a) = IsLocalRing.residue B (ψ a) := by
  have hmem : ∀ a, ∃ b, j b = iotaOQ N NA i a := fun a => by
    have : iotaOQ N NA i a ∈ Set.range j := by
      rw [hran]; exact Formalism.MainNotions.SumRepresentations.norm_iotaOQ_le_one N NA i a
    exact this
  choose f hf using hmem
  let ψ : N.O i →+* B :=
    { toFun := f
      map_one' := hj (by rw [hf, map_one, map_one])
      map_mul' := fun a b => hj (by rw [hf, map_mul, map_mul, hf, hf])
      map_zero' := hj (by rw [hf, map_zero, map_zero])
      map_add' := fun a b => hj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }
  have hψ : ∀ a, j (ψ a) = iotaOQ N NA i a := hf
  refine ⟨ψ, hψ, Ideal.Quotient.lift (IsLocalRing.maximalIdeal (N.O i)) ((IsLocalRing.residue B).comp ψ)
    fun a ha => ?_, fun a => Ideal.Quotient.lift_mk _ _ _⟩
  rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, hmax, hψ]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at ha
  obtain ⟨b, rfl⟩ := ha
  rw [map_mul, norm_mul]
  calc ‖iotaOQ N NA i b‖ * ‖iotaOQ N NA i ϖ‖ ≤ 1 * ‖iotaOQ N NA i ϖ‖ := by
        gcongr; exact Formalism.MainNotions.SumRepresentations.norm_iotaOQ_le_one N NA i b
    _ < 1 := by rw [one_mul]; exact Formalism.MainNotions.SumRepresentations.norm_iotaOQ_irreducible N NA i hϖ

end Psi

end GlobalTheory.ResidualRankCount
end
end
end
