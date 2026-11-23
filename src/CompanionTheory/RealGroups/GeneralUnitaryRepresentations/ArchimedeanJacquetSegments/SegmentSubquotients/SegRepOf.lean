module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.HasFiniteLengthJacSub
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.AutomorphicTheory.SegmentRepresentations.IrreducibleSegments.IsIrreduciblePiTensorSegTerm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodChevalley
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import GroundTheory.LocalFields.PadicLogSeries
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.IsSubquotientJacMultiProdOfSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentationIff
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.JhMultRevJacSub
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SrMult
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SrPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvector

-- Source module: CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegTwo

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def SegTwo : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ → Concl σ.ρ 2

end CompanionTheory.Pf1.SegRepC

end
end
end

-- Source module: CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.ExistsUniqueIrredSub

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published

namespace CompanionTheory.Pf1.SegRepC.Uniq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option synthInstance.maxHeartbeats 400000 in
theorem exists_unique_irred_sub {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ)
    (h1 : jhMult (piTensor (segTerm σ.ρ l))
      (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) = 1) :
    ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
        S'.toRepresentation.IsIrreducible → S' = S) ∧
      jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) S.toRepresentation) = 1 := by
  have hρ := CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  have hsπ : IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _
  have := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp (consecBlocks l d) hρ hsρ
  have hfl : HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)
  have hone : ∀ T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)), IsAtom T →
      1 ≤ jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) T.toRepresentation) :=
    GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac_atom _ hρ
  have hjm : jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) ≤ 1 := h1.le
  have hsoc : ∃ τ : IrrRep (GL (Fin (l * d)) k), IsSocle τ.ρ (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_forall_isAtom (π := multiProd (consecBlocks l d) (segTerm σ.ρ l)) (consecBlocks l d) hρ hsπ hfl hone hjm
  obtain ⟨τ, hτ, f, hf, hS⟩ := hsoc
  have hat : IsAtom f.range := isAtom_range hτ f hf
  have hatom : ∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible → IsAtom S' := fun S' hS' => by
    let g : S'.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨S'.toSubmodule.subtype, fun _ => rfl⟩
    have hr : g.range = S' := Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)
    have h := isAtom_range hS' g Subtype.val_injective
    rwa [hr] at h
  refine ⟨f.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat,
    fun S' hS' => hS S' (hatom S' hS'), le_antisymm ?_ ?_⟩
  · let ι : f.range.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨f.range.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (jacMap (consecBlocks l d) ι) :=
      GlobalTheory.JacInj.jacMap_injective k _ _ _ (consecBlocks l d) _ _ f.range.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)) ι hsπ
        Subtype.val_injective
    exact (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hρ (jacMap (consecBlocks l d) ι) hinj).trans hjm
  · exact hone _ hat

end CompanionTheory.Pf1.SegRepC.Uniq

end
end
end

-- Source module: CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.IsSubquotientJacOfLe

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.PiLocalization₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]



set_option synthInstance.maxHeartbeats 400000 in
theorem isSubquotient_jac_of_le {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    {S T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))} (hST : S.toSubmodule ≤ T.toSubmodule)
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) T)
    (IsSubquotient.of_injective ⟨Submodule.inclusion hST, fun _ => rfl⟩ (Submodule.inclusion_injective hST)))

end CompanionTheory.Pf1.SegRepC.PiLocalization₂

end
end
end

-- Source module: CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SrEasy

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.RgGu.SRC

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace SrEasy

theorem isSmooth_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _

theorem hasFiniteLength_prod {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) :
    HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := by
  have hρ := CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  exact GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)

theorem isSmooth_sub {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) : IsSmooth S.toRepresentation := by
  intro v
  have : {g : G | S.toRepresentation g v = v} = {g : G | π g v.1 = v.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact hπ v.1

end SrEasy

open SrEasy



theorem exists_irred_le {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ) (T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  let ι : T.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  have hnt : Nontrivial T.toSubmodule := Submodule.nontrivial_iff_ne_bot.2 hT
  obtain ⟨S, f, hf⟩ := GlobalTheory.T.exists_injective_irreducible_subrepresentation k _ _ _ T.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))
    (isSmooth_sub (isSmooth_prod σ) T) hnt (IsSubquotient.of_injective ι Subtype.val_injective)
    (hasFiniteLength_prod σ)
  let g : S.ρ.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ι.comp f
  have hg : Function.Injective g := Subtype.val_injective.comp hf
  have hat : IsAtom g.range := isAtom_range S.irr g hg
  refine ⟨g.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (f x).2



theorem isIrreducible_segTensor {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ 2)).IsIrreducible :=
  CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ 2


set_option synthInstance.maxHeartbeats 400000 in
theorem hasFiniteLength_jac_sub {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2))) :
    HasFiniteLength (jac (consecBlocks 2 d) S.toRepresentation) := by
  let ι : S.toRepresentation.IntertwiningMap (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)) :=
    ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have hS : HasFiniteLength S.toRepresentation :=
    GlobalTheory.ProdLength.hasFiniteLength_of_injective ι Subtype.val_injective (hasFiniteLength_prod σ)
  exact GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks 2 d) _ S.toRepresentation
    (isSmooth_sub (isSmooth_prod σ) S) hS

end CompanionTheory.RgGu.SRC

end
end
end

-- Source module: CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegRepOf

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel
open CompanionTheory.Pf1.SegRepC CompanionTheory.Pf1.SegRepC.SegTwo

namespace CompanionTheory.RgGu.SRC


set_option synthInstance.maxHeartbeats 400000 in
def StageP : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GeometricLemma → CompanionTheory.Pf1.SegRepC.SegTwo → ∀ {d l : ℕ}, 0 < d → 0 < l → ∀ (σ : IrrRep (GL (Fin d) k)),
    IsCuspidal σ.ρ → ∀ (i : ℕ) (hi : i + 1 < l),
    ∃ T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)), T.toSubmodule ≠ ⊥ ∧
      ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X),
        π.IsIrreducible → IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) →
        ∀ (w : Equiv.Perm (Fin l)), π.Equiv (piTensor fun a => segTerm σ.ρ l (w a)) →
        w.symm ⟨i, by omega⟩ < w.symm ⟨i + 1, hi⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem segTwo_of (hG : GeometricLemma) (hR : RhoNuRhoReducible) : CompanionTheory.Pf1.SegRepC.SegTwo := by
  intro k _ _ _ _ d hd σ hσ
  have h2 : (0 : ℕ) < 2 := by decide
  obtain ⟨S, hS, hU, h1⟩ := Uniq.exists_unique_irred_sub hd h2 σ hσ (SRC.jhMult_jac_multiProd hG hd h2 σ hσ)
  refine ⟨S, hS, hU, ?_⟩
  refine GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one _ _ (SRC.isIrreducible_segTensor hd σ) (SRC.hasFiniteLength_jac_sub hd σ hσ S) h1 fun X _ _ ρ hρ hs => ?_
  rcases SRC.constituents_jac_sub hG hd σ hσ S ρ hρ hs with h | h'
  · exact h
  · obtain ⟨φ⟩ := h'
    exfalso
    refine jhMult_ne_zero_iff.2 ?_ (SRC.jhMult_rev_jac_sub hG hR hd σ hσ S hS h1)
    exact (IsSubquotient.of_surjective φ.toIntertwiningMap fun w => ⟨φ.symm w, φ.apply_symm_apply w⟩).trans hs

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem segRep_of (hT : StageP) (hG : GeometricLemma) (h2 : CompanionTheory.Pf1.SegRepC.SegTwo) : SegmentRepresentation := by
  intro k _ _ _ _ d l hd hl σ hσ
  obtain ⟨S, hS, huniq, h1⟩ := Uniq.exists_unique_irred_sub hd hl σ hσ (SRC.jhMult_jac_multiProd hG hd hl σ hσ)
  refine ⟨S, hS, huniq, ?_⟩
  have hfl : HasFiniteLength (jac (consecBlocks l d) S.toRepresentation) :=
    GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ (consecBlocks l d) _ S.toRepresentation
      (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (Lift.isSmooth_multiProd_segTerm σ l) S) (hasFiniteLength_of_isIrreducible hS)
  refine GlobalTheory.CompanionTheory.FineStep.nonempty_equiv_of_jhMult_eq_one _ _
    (CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l) hfl h1 fun X _ _ π hπ h => ?_
  obtain ⟨w, ⟨φ⟩⟩ := SRC.exists_perm_of_isSubquotient_jac hG hd hl σ hσ π hπ (Lift.isSubquotient_jac_multiProd_of_sub σ S h)
  obtain rfl : w = 1 := Lift.perm_eq_one_of_lt_succ w fun i hi => by
    obtain ⟨T, hT0, hTw⟩ := hT k hG h2 hd hl σ hσ i hi
    obtain ⟨S', hS', hle⟩ := SRC.exists_irred_le hd hl σ hσ T hT0
    obtain rfl := huniq S' hS'
    exact hTw π hπ (PiLocalization₂.isSubquotient_jac_of_le σ hle h) w φ
  exact ⟨φ⟩

end CompanionTheory.RgGu.SRC

end
end
end
