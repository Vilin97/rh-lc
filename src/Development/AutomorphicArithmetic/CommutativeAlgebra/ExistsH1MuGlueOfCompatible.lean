module

public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicArithmetic.CommutativeAlgebra.H1PlEqZeroOfLeISupOfLocalZero
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OffDiagonalContinuationInductive
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.FunctionField.PlaceDefs

-- Source module: Development.EtaleCohomology.EtaleTrace.LCoprodInjPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

theorem chains_zero (R : Type) [CommRing R] (E : Scheme.{0}) (hZ : IsZero ((free R).obj (yoneda.obj E))) (p : ℤ) :
    IsZero (((chains R).obj (sch.obj E)).X p) := by
  rcases le_or_gt p 0 with h | h
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = -(m : ℤ) := ⟨p.natAbs, by omega⟩
    exact hZ.of_iso (chainsXIso R (sch.obj E) m)
  · apply HomologicalComplex.isZero_extend_X
    intro i hi
    have : (ComplexShape.embeddingDownNat).f i = -(i : ℤ) := rfl
    omega

theorem H_sub (R : Type) [CommRing R] (E : Scheme.{0}) (hZ : IsZero ((free R).obj (yoneda.obj E))) (F : Shv R) (n : ℤ) :
    Subsingleton (H R (sch.obj E) F n) := by
  have : Subsingleton (CochainComplex.HomComplex.Cochain ((chains R).obj (sch.obj E)) (res R F) n) :=
    ⟨fun a b => CochainComplex.HomComplex.Cochain.ext _ _ (fun p q _ => (chains_zero R E hZ p).eq_of_src _ _)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective y
  have hab : a = b := Subtype.ext (@Subsingleton.elim _ this _ _)
  rw [hab]

end LateralTheory.EtaleTrace

end
end
end

-- Source module: Development.EtaleCohomology.WeilConjectures.EmptyVan2

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.EWeil.EmptyVan₂

instance isEmpty_bot : IsEmpty (⊥_ Scheme.{0}) := by
  infer_instance

theorem sec_subsingleton {R : Type} [CommRing R] (G : Shv R) {U : Scheme.{0}} (f : U ⟶ ⊥_ Scheme.{0}) :
    Subsingleton (G.obj.obj (op U)) := by
  have : IsEmpty U := ⟨fun x => isEmptyElim (f.base x)⟩
  exact (ModuleCat.isZero_iff_subsingleton).1
    (IsTerminal.isZero (Sheaf.isTerminalOfBotCover G U (Scheme.bot_mem_grothendieckTopology U)))

theorem free_hom_subsingleton {R : Type} [CommRing R] (G : Shv R) :
    Subsingleton ((free R).obj (yoneda.obj (⊥_ Scheme.{0})) ⟶ G) := by
  constructor
  intro f g
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv _ _).injective
  ext U x
  by_cases h : Nonempty (U.unop ⟶ ⊥_ Scheme.{0})
  · obtain ⟨φ⟩ := h
    exact @Subsingleton.elim _ (sec_subsingleton G φ) _ _
  · have : IsEmpty (U.unop ⟶ ⊥_ Scheme.{0}) := not_nonempty_iff.1 h
    have hx : x = 0 := Finsupp.ext fun a => isEmptyElim (a.down : U.unop ⟶ ⊥_ Scheme.{0})
    subst hx
    simp only [map_zero]

theorem isZero_free {R : Type} [CommRing R] : IsZero ((free R).obj (yoneda.obj (⊥_ Scheme.{0}))) := by
  rw [IsZero.iff_id_eq_zero]
  have := free_hom_subsingleton (R := R) ((free R).obj (yoneda.obj (⊥_ Scheme.{0})))
  exact Subsingleton.elim _ _

end LateralTheory.EWeil.EmptyVan₂
end
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsH1MuGlueOfCompatible

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

namespace UpperTheory.Cb.MuCohomologyGluing

private theorem sub_empty (q : ℕ) (Y : Scheme.{0}) [IsEmpty Y] (n i : ℤ) :
    Subsingleton (Ht q (sch.obj Y) n i) := by
  have e : Y ≅ ⊥_ Scheme.{0} := (isInitialOfIsEmpty (X := Y)).uniqueUpToIso initialIsInitial
  exact LateralTheory.EtaleTrace.H_sub (ZMod q) Y
    (LateralTheory.EWeil.EmptyVan₂.isZero_free.of_iso ((free (ZMod q)).mapIso (yoneda.mapIso e))) (tw q i) n

private theorem pl_le (q : ℕ) {X : Scheme.{0}} {A B C : X.Opens} (h1 : A ≤ B) (h2 : B ≤ C) (h3 : A ≤ C)
    (z : Ht q (sch.obj C) 1 1) :
    pl q 1 (X.homOfLE h1) 1 (pl q 1 (X.homOfLE h2) 1 z) = pl q 1 (X.homOfLE h3) 1 z := by
  rw [← pl_comp, Scheme.homOfLE_homOfLE]

private theorem van (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X] (hζ : Nonempty (Prim q Γ(X, ⊤)))
    (hq : IsUnit (q : Γ(X, ⊤))) (n : ℕ) (A : Fin n → X.Opens) (P : X.Opens) (hP : P ≤ ⨆ i, A i)
    (d : Ht q (sch.obj P) 1 1)
    (hd : ∀ i, pl q 1 (X.homOfLE (inf_le_right : A i ⊓ P ≤ P)) 1 d = 0) : d = 0 := by
  have hmem : ∀ x : P.toScheme, P.ι x ∈ P := fun x => by
    rw [← SetLike.mem_coe, ← P.range_ι]
    exact ⟨x, rfl⟩
  by_cases hne : Nonempty P.toScheme
  · haveI : IsIntegral P.toScheme := isIntegral_of_isOpenImmersion P.ι
    have hζ' : Nonempty (Prim q Γ(P.toScheme, ⊤)) := hζ.map (Prim.map P.ι.appTop.hom)
    have hq' : IsUnit (q : Γ(P.toScheme, ⊤)) := by simpa using hq.map P.ι.appTop.hom
    have key := UpperTheory.h1_pl_eq_zero_of_le_iSup_of_local_zero q P.toScheme hζ' hq' n (fun i => P.ι ⁻¹ᵁ A i) ⊤ (by
      intro x _
      have hx : P.ι x ∈ ⨆ i, A i := hP (hmem x)
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩) d (fun i => by
        have e : P.ι ⁻¹ᵁ A i ≤ P.ι ⁻¹ᵁ (A i ⊓ P) := by
          intro x hx
          exact ⟨hx, hmem x⟩
        have w : P.ι.resLE (A i ⊓ P) (P.ι ⁻¹ᵁ A i) e ≫ X.homOfLE (inf_le_right : A i ⊓ P ≤ P) =
            (P.ι ⁻¹ᵁ A i).ι := by
          rw [← cancel_mono P.ι]
          simp
        rw [← w, pl_comp, hd i, map_zero])
    have w : P.toScheme.topIso.inv ≫ (⊤ : P.toScheme.Opens).ι = 𝟙 _ := P.toScheme.topIso.inv_hom_id
    have := congrArg (pl q 1 P.toScheme.topIso.inv 1) key
    rw [← pl_comp, w, map_zero] at this
    simpa [pl, pull_id] using this
  · haveI : IsEmpty P.toScheme := not_nonempty_iff.1 hne
    haveI := sub_empty q P.toScheme 1 1
    exact Subsingleton.elim _ _

end UpperTheory.Cb.MuCohomologyGluing

open UpperTheory.Cb.MuCohomologyGluing in
theorem UpperTheory.exists_h1Mu_glue_of_compatible :
    ∀ (q : ℕ) [NeZero q] (X : Scheme.{0}) [IsIntegral X], Nonempty (Prim q Γ(X, ⊤)) → IsUnit (q : Γ(X, ⊤)) → ∀ (n : ℕ) (U : Fin n → X.Opens) (x : ∀ i, Ht q (sch.obj (U i)) 1 1), (∀ i j, pl q 1 (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) 1 (x i) = pl q 1 (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) 1 (x j)) → ∃ y : Ht q (sch.obj (⨆ i, U i : X.Opens)) 1 1, ∀ i, pl q 1 (X.homOfLE (le_iSup U i)) 1 y = x i := by
  intro q _ X _ hζ hq n
  induction n with
  | zero =>
    intro U x _
    exact ⟨0, fun i => i.elim0⟩
  | succ n ih =>
    intro U x hx
    set W : X.Opens := ⨆ i : Fin n, U i.castSucc with hW
    have hAW : ∀ i : Fin n, U i.castSucc ≤ W := fun i => le_iSup (fun i : Fin n => U i.castSucc) i
    obtain ⟨y, hy⟩ : ∃ y : Ht q (sch.obj W) 1 1, ∀ i : Fin n, pl q 1 (X.homOfLE (hAW i)) 1 y = x i.castSucc :=
      ih (fun i => U i.castSucc) (fun i => x i.castSucc) (fun i j => hx _ _)
    set B : X.Opens := U (Fin.last n) with hB
    have c : UpperTheory.Cb.OffDiagonalContinuation.Sq W B (W ⊔ B) (W ⊓ B) := ⟨rfl, rfl⟩
    obtain ⟨dd, hdd, -⟩ := UpperTheory.Cb.OffDiagonalContinuation.mv q 1
    have hex := (hdd c 1).2.2
    have d0 : pl q 1 (X.homOfLE (inf_le_left : W ⊓ B ≤ W)) 1 y -
        pl q 1 (X.homOfLE (inf_le_right : W ⊓ B ≤ B)) 1 (x (Fin.last n)) = 0 := by
      refine van q X hζ hq n (fun i => U i.castSucc) (W ⊓ B) inf_le_left _ (fun i => ?_)
      have h1 : U i.castSucc ⊓ (W ⊓ B) ≤ U i.castSucc ⊓ B := inf_le_inf_left _ inf_le_right
      rw [map_sub, pl_le q _ _ (inf_le_right.trans inf_le_left), pl_le q _ _ (inf_le_right.trans inf_le_right),
        ← pl_le q (inf_le_left : U i.castSucc ⊓ (W ⊓ B) ≤ U i.castSucc) (hAW i),
        ← pl_le q h1 (inf_le_right : U i.castSucc ⊓ B ≤ B), hy i, ← hx i.castSucc (Fin.last n),
        pl_le q h1 inf_le_left inf_le_left, sub_self]
    obtain ⟨z, hz⟩ := (hex (y, x (Fin.last n))).1 d0
    have hz1 : pl q 1 (X.homOfLE (le_sup_left : W ≤ W ⊔ B)) 1 z = y := congrArg Prod.fst hz
    have hz2 : pl q 1 (X.homOfLE (le_sup_right : B ≤ W ⊔ B)) 1 z = x (Fin.last n) := congrArg Prod.snd hz
    have hle : (⨆ i, U i : X.Opens) ≤ W ⊔ B := by
      refine iSup_le fun i => ?_
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact le_sup_right
      · exact (hAW j).trans le_sup_left
    refine ⟨pl q 1 (X.homOfLE hle) 1 z, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [pl_le q _ _ le_sup_right, hz2]
    · rw [pl_le q _ _ ((hAW j).trans le_sup_left), ← pl_le q (hAW j) (le_sup_left : W ≤ W ⊔ B), hz1]
      exact hy j
end
end
