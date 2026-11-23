module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodIdempotentBadPlaces
public import Mathlib.Algebra.Field.IsField
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Formalism.LocalRingCardinality.DataHost
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharacterOnStabilizerEqProdResidueCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceCharacterArgumentSignedSumStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueLevelCharacterArgumentAtTypePlaceStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharEqMulShiftUnitOfIsField

section

@[expose] public section

namespace GlobalTheory.Twist

theorem addChar_eq_mulShift_unit_of_isField :
    ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ ψ φ : AddChar κf ℂ, ψ ≠ 1 → φ ≠ 1 →
      ∃ c : κfˣ, ∀ t, φ t = ψ ((c : κf) * t) := by
  intro κf _ _ hF ψ φ hψ _
  classical
  let _ : Field κf := hF.toField
  have _ : Fintype κf := Fintype.ofFinite κf

  have hinj : Function.Injective ψ.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one hψ)

  have hbij : Function.Bijective ψ.mulShift :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, AddChar.card_eq.symm⟩
  obtain ⟨a, ha⟩ := hbij.2 φ
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact ‹φ ≠ 1› (by rw [← ha, AddChar.mulShift_zero])
  refine ⟨Units.mk0 a ha0, fun t => ?_⟩
  rw [← ha, AddChar.mulShift_apply, Units.val_mk0]

end GlobalTheory.Twist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharEqMulShiftUnitOfIsFieldStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.exists_unit_addChar_eq_mulShift_of_isField : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ ψ φ : AddChar κf ℂ, ψ ≠ 1 → φ ≠ 1 → ∃ c : κfˣ, ∀ t, φ t = ψ ((c : κf) * t) := by
  first | exact @GlobalTheory.Twist.addChar_eq_mulShift_unit_of_isField | exact GlobalTheory.Twist.addChar_eq_mulShift_unit_of_isField | (intros; apply GlobalTheory.Twist.addChar_eq_mulShift_unit_of_isField <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjCharacterEqProdSymmetricEdgeCharacters

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

theorem GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∃ (ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (a : ∀ PP : Pl D.host.E, Fin D.R.r → Fin D.R.r → (kP PP)ˣ), IsGenericPsi R.Pg ψ' ∧ ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = ∏ PP ∈ R.Pg, ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hIs hGrp β hβ hred
  classical
  obtain ⟨ψ, hψ, hdec⟩ := GlobalTheory.T.levelCharacter_on_stabilizer_eq_prod_residue_characters_alt R F X h hIs hGrp
  have hc : ∀ PP ∈ R.Pg, ∃ c : (kP PP)ˣ, ∀ t, ψ (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.conjRes PP t) = ψ PP ((c : kP PP) * t) := by
    intro PP hP
    refine GlobalTheory.T.exists_unit_addChar_eq_mulShift_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 PP.isMaximal) (ψ PP)
      ((ψ (GlobalTheory.IdemSupport.cP PP)).compAddMonoidHom (GlobalTheory.SeeConjChar.conjRes PP).toAddMonoidHom) (hψ PP hP).1 ?_
    intro h1
    apply (hψ PP hP).2
    ext t
    obtain ⟨s, rfl⟩ := (GlobalTheory.SeeConjChar.conjRes PP).surjective t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ s) h1
    simpa using this
  choose! c hc using hc
  refine ⟨fun PP => (ψ PP).mulShift (-1), fun PP i j =>
    if (i.1 < D.R.rS ∨ (i.1 + 1 < D.R.rS + D.R.k ∧ GlobalTheory.SeeConjChar.sideAt X h PP = true)) then 1
    else if i.1 = D.R.rS + D.R.k then c PP else -c PP, ?_, ?_⟩
  · intro PP hP h1
    apply (hψ PP hP).1
    ext t
    have := congrArg (fun χ : AddChar (kP PP) ℂ => χ (-t)) h1
    simpa [AddChar.mulShift_apply] using this
  · intro κ hS hK2
    have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
    rw [hdec κ hK, ← starRingEnd_apply, map_prod]
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [GlobalTheory.T.residue_levelCharacterArgument_at_typePlace R F X h hIs hGrp β hβ hred PP hP κ hS, GlobalTheory.T.residue_conjugatePlace_characterArgument_signedSum R F X h hIs hGrp β hβ hred PP hP κ hS hK2, hc PP hP,
      map_mul, ← AddChar.map_neg_eq_conj, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, AddChar.mulShift_apply]
    congr 1
    rw [Finset.mul_sum, ← neg_add, ← Finset.sum_add_distrib, neg_one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hE
    · unfold GlobalTheory.SeeConjChar.wA GlobalTheory.SeeConjChar.wB
      simp only [apply_ite (fun u : (kP PP)ˣ => (u : kP PP)), Units.val_one, Units.val_neg]
      split_ifs <;> first | (exfalso; tauto) | (push_cast; ring1) | omega | (simp_all <;> omega)
    · simp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjCharacterEqProdSymmetricEdgeCharactersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead


theorem _root_.GlobalTheory.T.conjCharacter_eq_prod_symmetricEdge_characters_alt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∃ (ψ' : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (a : ∀ PP : Pl D.host.E, Fin D.R.r → Fin D.R.r → (kP PP)ˣ), IsGenericPsi R.Pg ψ' ∧ ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → star (X.chi2 ((iotaX X h).toMulEquiv κ).2) = ∏ PP ∈ R.Pg, ψ' PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a PP i j : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  first | exact @GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters | exact GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters | (intros; apply GlobalTheory.SeeConjChar.conjCharacter_eq_prod_symmetricEdge_characters <;> assumption)
end
end
