module

public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
public import Mathlib.Data.Sym.Card

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyRegularRelationsEqKoszulRelations

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open RingTheory.Sequence in
theorem weaklyRegular_relations_koszul :
    ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∀ a : Fin g → O, ∑ i, a i * f i = 0 → ∃ c : Matrix (Fin g) (Fin g) O, (∀ i, c i i = 0) ∧ (∀ i j, c i j = - c j i) ∧ a = c.mulVec f := by
  intro O _ g
  induction g with
  | zero =>
    intro f _ a _
    exact ⟨0, by simp, by simp, funext fun i => i.elim0⟩
  | succ g ih =>
    intro f hf a ha
    have hsplit : List.ofFn f =
        List.ofFn (fun i : Fin g => f i.castSucc) ++ [f (Fin.last g)] := by
      rw [List.ofFn_succ_last]
    rw [hsplit, isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hf
    obtain ⟨hf1, hf2⟩ := hf
    rw [Fin.sum_univ_castSucc] at ha
    have hIt : (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) =
        Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) := by
      rw [smul_eq_mul, Ideal.mul_top]
    have hmem : a (Fin.last g) ∈
        (Ideal.ofList (List.ofFn fun i : Fin g => f i.castSucc) • ⊤ : Submodule O O) := by
      rw [← Submodule.Quotient.mk_eq_zero]
      apply hf2
      simp only [smul_zero]
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hIt, smul_eq_mul, mul_comm,
        eq_neg_of_add_eq_zero_right ha, neg_mem_iff]
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    rw [hIt, Ideal.ofList, show {r | r ∈ List.ofFn fun i : Fin g => f i.castSucc}
        = Set.range (fun i : Fin g => f i.castSucc) by ext; simp [List.mem_ofFn],
      Ideal.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨b, hb⟩ := hmem
    obtain ⟨c', hc0, hcs, hca⟩ := ih (fun i => f i.castSucc) hf1
      (fun i => a i.castSucc + b i * f (Fin.last g)) (by
        simp only [add_mul, Finset.sum_add_distrib]
        rw [← ha, ← hb, Finset.sum_mul, add_right_inj]
        exact Finset.sum_congr rfl fun i _ => by ring)
    refine ⟨fun i j => Fin.lastCases (Fin.lastCases 0 (fun j => b j) j)
      (fun i => Fin.lastCases (-b i) (fun j => c' i j) j) i, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.lastCases with
      | last => simp
      | cast i => simp [hc0]
    · intro i j
      cases i using Fin.lastCases <;> cases j using Fin.lastCases <;> simp <;> exact hcs _ _
    · funext i
      cases i using Fin.lastCases with
      | last => simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hb]
      | cast i =>
        have := congrFun hca i
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.lastCases_castSucc,
          Fin.lastCases_last]
        rw [← this]
        ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeaklyRegularRelationsEqKoszulRelationsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.weaklyRegular_relations_eq_koszulRelations : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∀ a : Fin g → O, ∑ i, a i * f i = 0 → ∃ c : Matrix (Fin g) (Fin g) O, (∀ i, c i i = 0) ∧ (∀ i j, c i j = - c j i) ∧ a = c.mulVec f := by
  first | exact @GlobalTheory.weaklyRegular_relations_koszul | exact GlobalTheory.weaklyRegular_relations_koszul | (intros; apply GlobalTheory.weaklyRegular_relations_koszul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulResolutionThreeTermsExact

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Koszul

noncomputable def pairEquiv (g : ℕ) : {z : Sym2 (Fin g) // ¬ z.IsDiag} ≃ Fin (g.choose 2) :=
  Fintype.equivFinOfCardEq (by rw [Sym2.card_subtype_not_diag, Fintype.card_fin])

variable {O : Type} [CommRing O] {g : ℕ}

noncomputable def upper (x : Fin (g.choose 2) → O) : Matrix (Fin g) (Fin g) O :=
  fun i j => if h : i < j then
    x (pairEquiv g ⟨s(i, j), by rw [Sym2.mk_isDiag_iff]; exact h.ne⟩) else 0

noncomputable def skew (x : Fin (g.choose 2) → O) : Matrix (Fin g) (Fin g) O :=
  fun i j => upper x i j - upper x j i

lemma upper_add (x x' : Fin (g.choose 2) → O) : upper (x + x') = upper x + upper x' := by
  ext i j; simp only [upper, Matrix.add_apply]; split_ifs <;> simp

lemma upper_smul (a : O) (x : Fin (g.choose 2) → O) : upper (a • x) = a • upper x := by
  ext i j; simp only [upper, Matrix.smul_apply]; split_ifs <;> simp

lemma skew_add (x x' : Fin (g.choose 2) → O) : skew (x + x') = skew x + skew x' := by
  ext i j; simp only [skew, upper_add, Matrix.add_apply]; ring

lemma skew_smul (a : O) (x : Fin (g.choose 2) → O) : skew (a • x) = a • skew x := by
  ext i j; simp only [skew, upper_smul, Matrix.smul_apply, smul_eq_mul]; ring

noncomputable def d₂ (f : Fin g → O) : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O) where
  toFun x := (skew x).mulVec f
  map_add' x x' := by rw [skew_add, Matrix.add_mulVec]
  map_smul' a x := by
    rw [skew_smul]; ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

lemma d₂_apply (f : Fin g → O) (x : Fin (g.choose 2) → O) : d₂ f x = (skew x).mulVec f := rfl

lemma sum_skew_mulVec (f : Fin g → O) (x : Fin (g.choose 2) → O) :
    ∑ i, (skew x).mulVec f i * f i = 0 := by
  simp only [Matrix.mulVec, dotProduct, skew, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [sub_eq_zero, Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

lemma exists_skew_eq (c : Matrix (Fin g) (Fin g) O) (hd : ∀ i, c i i = 0)
    (hs : ∀ i j, c i j = - c j i) : ∃ x : Fin (g.choose 2) → O, skew x = c := by
  let F : Sym2 (Fin g) → O :=
    Sym2.lift ⟨fun i j => c (min i j) (max i j), fun i j => show c (min i j) (max i j) = c (min j i) (max j i) by rw [min_comm, max_comm]⟩
  refine ⟨fun k => F ((pairEquiv g).symm k).1, ?_⟩
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [skew, upper, h, lt_asymm h, F, min_eq_left h.le, max_eq_right h.le]
  · simp [skew, upper, hd]
  · simp [skew, upper, h, lt_asymm h, F, min_eq_left h.le, max_eq_right h.le, ← hs i j]

end GlobalTheory.Koszul


open GlobalTheory.Koszul in
theorem GlobalTheory.koszul_resolution_three_terms : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∃ (e₁ : (Fin g → O) →ₗ[O] O) (e₂ : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O)), Function.Exact e₁ (Ideal.span (Set.range f)).mkQ ∧ Function.Exact e₂ e₁ ∧ (∀ x, e₁ x ∈ Ideal.span (Set.range f)) ∧ ∀ x i, e₂ x i ∈ Ideal.span (Set.range f) := by
  intro O _ g f hreg
  refine ⟨Fintype.linearCombination O f, d₂ f, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.exact_iff, Submodule.ker_mkQ, Fintype.range_linearCombination]
  · intro y
    constructor
    · intro hy
      rw [Fintype.linearCombination_apply] at hy
      obtain ⟨c, hd, hs, rfl⟩ := GlobalTheory.T.weaklyRegular_relations_eq_koszulRelations O g f hreg y (by simpa [smul_eq_mul] using hy)
      obtain ⟨x, hx⟩ := exists_skew_eq c hd hs
      exact ⟨x, by rw [d₂_apply, hx]⟩
    · rintro ⟨x, rfl⟩
      rw [Fintype.linearCombination_apply, d₂_apply]
      simpa [smul_eq_mul] using sum_skew_mulVec f x
  · intro x
    show _ ∈ Submodule.span O (Set.range f)
    rw [← Fintype.range_linearCombination]
    exact LinearMap.mem_range_self _ x
  · intro x i
    rw [d₂_apply]
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KoszulResolutionThreeTermsExactStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.koszul_resolution_three_terms_exact : ∀ (O : Type) [CommRing O] (g : ℕ) (f : Fin g → O), RingTheory.Sequence.IsWeaklyRegular O (List.ofFn f) → ∃ (e₁ : (Fin g → O) →ₗ[O] O) (e₂ : (Fin (g.choose 2) → O) →ₗ[O] (Fin g → O)), Function.Exact e₁ (Ideal.span (Set.range f)).mkQ ∧ Function.Exact e₂ e₁ ∧ (∀ x, e₁ x ∈ Ideal.span (Set.range f)) ∧ ∀ x i, e₂ x i ∈ Ideal.span (Set.range f) := by
  first | exact @GlobalTheory.koszul_resolution_three_terms | exact GlobalTheory.koszul_resolution_three_terms | (intros; apply GlobalTheory.koszul_resolution_three_terms <;> assumption)
end
end
