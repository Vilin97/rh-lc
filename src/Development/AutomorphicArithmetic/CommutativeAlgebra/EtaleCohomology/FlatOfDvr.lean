module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PhiKOfNil
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtIdBC
import Mathlib.Tactic.Lemma

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCorrPull

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

open CategoryTheory.Limits in
theorem UpperTheory.Gal.crystallineComparison.corrPull_of :
    CorrPull := by
  intro l S S' Y Y' u f f' h hY T hT
  have Q := IsPullback.of_hasPullback T.p h
  have hw : (pullback.fst T.p h ≫ T.r) ≫ f = (pullback.snd T.p h ≫ f') ≫ u := by
    rw [Category.assoc, hT, ← Category.assoc, pullback.condition, Category.assoc, hY.w,
      Category.assoc]
  have hfin : IsFinite (pullback.snd T.p h) := by
    have := T.fin
    exact MorphismProperty.of_isPullback Q this
  have het : Etale (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) := by
    have hle : Y'.basicOpen (l : Γ(Y', ⊤)) ≤ h ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) :=
      le_of_eq (by rw [Scheme.preimage_basicOpen_top, map_natCast])
    let k := Y'.homOfLE hle ≫ h ∣_ Y.basicOpen (l : Γ(Y, ⊤))
    have e1 : k ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι = (Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ h := by
      simp only [k, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    have A := (isPullback_morphismRestrict (pullback.snd T.p h) (Y'.basicOpen (l : Γ(Y', ⊤)))).flip
    have outer := A.paste_horiz Q
    have R := (isPullback_morphismRestrict T.p (Y.basicOpen (l : Γ(Y, ⊤)))).flip
    have hw2 : ((pullback.snd T.p h ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ pullback.fst T.p h) ≫ T.p
        = (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤)) ≫ k) ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      simp only [Category.assoc, pullback.condition, e1, morphismRestrict_ι_assoc]
    have outer' : IsPullback (R.lift _ _ hw2 ≫ (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι)
        (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) T.p (k ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι) := by
      rw [R.lift_fst, e1]
      exact outer
    have L := IsPullback.of_right outer' (R.lift_snd _ _ _) R
    exact MorphismProperty.of_isPullback L T.et
  have hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K], (l : K) ≠ 0 →
      ∀ (y : Spec (CommRingCat.of K) ⟶ Y'),
        Nat.card { z // z ≫ pullback.snd T.p h = y } = T.d := by
    intro K _ _ hl y
    rw [← T.deg K hl (y ≫ h)]
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1 ≫ pullback.fst T.p h, by rw [Category.assoc, pullback.condition, ← Category.assoc, z.2]⟩
        invFun := fun z => ⟨Q.lift z.1 y z.2, Q.lift_snd _ _ _⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro z
      apply Subtype.ext
      apply Q.hom_ext
      · simp
      · simp [z.2]
    · intro z
      apply Subtype.ext
      simp
  refine ⟨⟨pullback T.p h, pullback.snd T.p h, hY.lift _ _ hw, T.d, hfin, het, hdeg⟩,
    pullback.fst T.p h, Q.flip, hY.lift_fst _ _ _, hY.lift_snd _ _ _, rfl⟩
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FlatOfDvr

section

@[expose] public section

open CategoryTheory AlgebraicGeometry

private lemma flat_of_dvr {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
    (φ : O →+* O') (ϖ : O) (hϖ : Irreducible ϖ) (h0 : φ ϖ ≠ 0) : φ.Flat := by
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
    rw [map_mul, map_pow] at ha
    rcases mul_eq_zero.1 ha with h | h
    · exact (u.isUnit.map φ).ne_zero h
    · exact pow_ne_zero k h0 h
  algebraize [φ]
  have : FaithfulSMul O O' := (faithfulSMul_iff_algebraMap_injective O O').2 hinj
  have : Module.IsTorsionFree O O' := inferInstance
  exact (inferInstance : Module.Flat O O')

theorem UpperTheory.Ru.crystallineComparison.ptIdBC :
    UpperTheory.Ru.crystallineComparison.PtIdBC := by
  intro l q n O O' _ _ _ _ _ _ φ ϖ hϖ hϖ' hq Y Y' p p' g hpb T hT hId
  have hflat : φ.Flat := flat_of_dvr φ ϖ hϖ hϖ'.ne_zero
  choose T' κ h1 h2 h3 _ using fun j => UpperTheory.Gal.crystallineComparison.corrPull_of l _ _ Y Y' _ p p' g hpb (T j) (hT j)
  refine ⟨T', κ, fun j => ⟨(h1 j).flip, (h2 j).symm, h3 j⟩, ?_⟩
  exact UpperTheory.Gal.crystallineComparison.ptIdBC_of l q n O O' φ hflat ϖ (φ ϖ) (fun _ _ => Iff.rfl)
    (fun a => Ideal.mem_span_singleton.2 (hq a)) Y Y' p p' g hpb T T' κ h1 h2 h3 hId
end
end
