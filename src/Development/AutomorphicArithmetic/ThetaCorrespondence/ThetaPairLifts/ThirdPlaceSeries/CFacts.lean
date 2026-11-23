module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.OptInEqSome
public import Formalism.LocalRingCardinality.DataNChTie
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Tie0CutOfTie0
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisPreconditions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMemAdjoin
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleOfTheorem
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Tie0CutOfTie0
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleJOfRestricted
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeRhamPointsWeightJumps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsGood
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvG6OfAdmStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SParts

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.FactsOfPre

section

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory Tr

variable {D : D7}



@[reducible] def nchCut (c : CutD D) (x : NChoice D) : NChoice (cut D c) := { x with }


theorem nct_cut (c : CutD D) {x : NChoice D} (h : NChTie D x) : NChTie (cut D c) (nchCut c x) :=
  { h with
    twOf_eq := fun a => h.twOf_eq a.1
    twSide_eq := fun a => h.twSide_eq a.1
    Q_eq := fun a => h.Q_eq a.1
    psi_eq := h.psi_eq.imp fun _ k => ⟨k.1, k.2.1, fun a => k.2.2 a.1⟩ }

end UpperTheory.GalC
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointCondition

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.StringRepresentationDecomposition

theorem rbEx_of_jointCond_rho : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  intro D hrho i hHG
  obtain ⟨x, hx⟩ := hHG
  have hx' := hx
  obtain ⟨-, Sig, hSig, hgood⟩ := hx'
  obtain ⟨ρ₀, ξ, -, -, hρx⟩ := hrho i x hx Sig hSig hgood
  exact ⟨_, isRhoBar_of_isRhoOf D i x _ hρx⟩

end GlobalTheory.StringRepresentationDecomposition
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointConditionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

theorem _root_.GlobalTheory.T.residualRankPartExists_of_jointCondition : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | exact GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | (intros; apply GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.CompatibilityTiesEigenRestriction

section

@[expose] public section

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Alg

def descHom {O X M B : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Semiring B] [Algebra O B]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (S : Set X) (z : B →ₐ[O] Module.End O M)
    (h : ∀ b (f : T), z b * act f = act f * z b) : B →ₐ[O] Module.End O (cutM T act S) where
  toFun b := desc T act S (z b) (h b)
  map_one' := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, map_one]; rfl
  map_mul' a b := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [Module.End.mul_apply, desc_mk, desc_mk, desc_mk, map_mul]; rfl
  map_zero' := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, map_zero]; rfl
  map_add' a b := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [LinearMap.add_apply, desc_mk, desc_mk, desc_mk, map_add (f := _), LinearMap.add_apply, map_add (f := _)]
  commutes' a := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]

variable {D : D7} (c : CutD D)

def zCut (Q : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (S : Set (D.nd.X i)) :
    ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i]
      Module.End (D.nd.O i) (cutM (D.nd.T i) (D.nd.act i) S) :=
  descHom (D.nd.T i) (D.nd.act i) S (Q.zO i) (Q.zO_comm i)



def pendCut (Q : PairedCharacterCondition.Pend D) : PairedCharacterCondition.Pend (cut D c) where
  lz := Q.lz
  eSer_eq := Q.eSer_eq
  eSer_LL := Q.eSer_LL
  zetaPrimitiveRoot := fun i => Q.zetaPrimitiveRoot i.1
  om := Q.om
  om_one := Q.om_one
  om_mul := Q.om_mul
  tameInertiaChar_mul_root := Q.tameInertiaChar_mul_root
  om_wild := Q.om_wild
  om_open := Q.om_open
  om_inj := Q.om_inj
  om_tg := Q.om_tg
  inertiaCharpoly_eigenvalues := Q.inertiaCharpoly_eigenvalues
  inertiaCharpoly_character := Q.inertiaCharpoly_character
  zO := fun i => zCut Q i.1 (c.Xs i.1)
  zO_comm := fun i z f => desc_comm (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) f
  zL_stable := fun i => Q.zL_stable i.1
  zO_act := fun i z x y h =>
    (congrArg (qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)) (Q.zO_act i.1 z x y h)).trans
      (qK_desc (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) _).symm
  prMt_type := fun i PI x hx => by
    obtain ⟨a, b⟩ := Q.prMt_type i.1 PI x hx
    refine ⟨fun p hp => qK_mem (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (x := p) (a p.1 (optIn_eq_some.1 hp)), fun hn => ?_⟩
    show qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.prMt i.1 x) = 0
    cases hp : D.naut.ptV i.1 PI with
    | none => rw [b hp, map_zero]
    | some p =>
      refine qK_out (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.T_sep i.1) (x := p) (fun hm => ?_) (a p hp)
      have := (optIn_eq_some (S := c.Xs i.1) (x := ⟨p, hm⟩)).2 hp
      exact Option.some_ne_none _ (this.symm.trans hn)
  Par_surj := fun i x Sig h => Q.Par_surj i.1 x.1 Sig (h.imp fun _ k => ⟨optIn_eq_some.1 k.1, k.2⟩)
  kty := fun i => Q.kty i.1
  kty_spec := fun i => Q.kty_spec i.1

theorem eigSpan_cut {Q : PairedCharacterCondition.Pend D} (h : GlobalTheory.Pass.EigSpan Q) : GlobalTheory.Pass.EigSpan (pendCut c Q) := by
  intro i z x a ha u hu
  have hu' : u ∈ (heckeEig (D.nd.T i.1) (D.nd.act i.1) x.1).map (qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)) := by
    rw [map_eig _ _ _ (D.nd.T_sep i.1) x]; exact hu
  obtain ⟨v, hv, rfl⟩ := hu'
  have e := h i.1 z x.1 a (fun PI hP => ha PI (optIn_eq_some.2 hP)) v hv
  refine (qK_desc (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) v).trans ?_
  rw [e]
  have k : ∀ (b : D.nd.O i.1) (w : TensorProduct (D.nd.O i.1) (FractionRing (D.nd.O i.1)) (D.nd.Mt i.1)),
      qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (b • w) = b • qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) w := fun b w => by
    rw [← algebraMap_smul (FractionRing (D.nd.O i.1)) b w, map_smul, algebraMap_smul]
  exact k a v

theorem compatibilityTies_eigenRestriction (h : Tie4 D) : Tie4 (cut D c) := by
  obtain ⟨a, ⟨Q, hDZ, hE⟩, b, d⟩ := h
  exact ⟨fun i => a i.1, ⟨pendCut c Q, fun i => hDZ i.1, eigSpan_cut c hE⟩, fun i => b i.1, fun i => d i.1⟩

end UpperTheory.GalC
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GaloisAdmissibleOfRestrictedCmDatum

section

@[expose] public section

namespace UpperTheory.GalC.Tr

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem galois_admissible_of_restricted_cmDatum {D : D7} {c : CutD D} (h : UpperTheory.GalS.AutomorphicGaloisAdmissible D.nd D.naut) :
    UpperTheory.GalS.AutomorphicGaloisAdmissible (cut D c).nd (cut D c).naut := fun i =>
  ⟨fun a ha π hc hr => by
    obtain ⟨ρ, c1, s, o, u, e⟩ := (h i.1).1 a ha π hc hr
    exact ⟨ρ, c1, s, fun w hw => ⟨(o w hw).dim, (o w hw).eq_of_unr, (o w hw).ine, (o w hw).mono⟩,
      fun w hw g => ⟨(u w hw g).1, (u w hw g).2.1, ⟨(u w hw g).2.2.rel.dim, (u w hw g).2.2.rel.mono, (u w hw g).2.2.rel.ine⟩,
        (u w hw g).2.2.one⟩, e⟩, (h i.1).2⟩

end UpperTheory.GalC.Tr
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NoG4Restrict

section

@[expose] public section



section
namespace UpperTheory.GalC.Tr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
theorem no_g4_restrict_alt {D : D7} {c : CutD D} (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (_ : ∀ i, UpperTheory.GalS.UnusedSlot55 D.nd D.naut i) :
    ∀ i, UpperTheory.GalS.UnusedSlot55 (cut D c).nd (cut D c).naut i := fun _ => trivial
end UpperTheory.GalC.Tr
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleSevenRestrict

section

@[expose] public section



section
noncomputable section
namespace UpperTheory.GalC.Tr
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.NRows
variable {D : D7} {c : CutD D}
theorem admissible_seven_restrict_alt (h : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D) : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt (cut D c) := h
theorem admA_cut (h : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt (cut D c) :=
  ⟨tie0_cut_of_tie0 h.1, hypO_cut h.2.1, fun i => h.2.2.1 i.1, _root_.UpperTheory.GalC.Tr.galois_admissible_of_restricted_cmDatum h.2.2.2.1, fun i => h.2.2.2.2.1 i.1,
    fourthAdmissible_restrictToPoints h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
theorem admissible_cut (h : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum (cut D c) :=
  ⟨⟨_root_.UpperTheory.GalC.Tr.admA_cut h.1.1, _root_.UpperTheory.GalC.Tr.admissible_seven_restrict_alt h.1.2⟩, rhoBar_cut h.2.1, h.2.2⟩
theorem rsA_cut_of_aux41 (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (h : _root_.GlobalTheory.NRows.RowsAAlt D) : _root_.GlobalTheory.NRows.RowsAAlt (cut D c) :=
  { tieLab := h.tieLab, hecke := h.hecke, tie0 := tie0_cut_of_tie0 h.tie0, a2 := _root_.UpperTheory.GalC.Tr.galois_admissible_of_restricted_cmDatum h.a2, an1 := h.an1, an2 := h.an2
    a5 := h.a5, temp := _root_.UpperTheory.GalC.Tr.admissible_seven_restrict_alt h.temp, g4p := _root_.UpperTheory.GalC.Tr.no_g4_restrict_alt h41 h.g4p, gsp := h.gsp }
theorem rs_cut_of_good_aux41 (hc : c.Good) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (h : _root_.GlobalTheory.NRows.PointConditions' D) : _root_.GlobalTheory.NRows.PointConditions' (cut D c) :=
  { a := _root_.UpperTheory.GalC.Tr.rsA_cut_of_aux41 h41 h.a, b := rowsB_cut h.b, c := rowsC_cut hc h.c
    typeNZ := fun i x hx F hF => h.typeNZ i.1 x.1 ((zg_iff i x).1 hx) F (eigC_eq i x ▸ hF)
    rank := fun L => h.rank (ledBack L) }
theorem admissible_tame_eigenvalues_of_cut (h : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D) : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues (cut D c) :=
  fun i Sig hx => h i.1 Sig (hx.elim fun x k => ⟨x.1, (par_iff i x Sig).1 k⟩)
end UpperTheory.GalC.Tr
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CFacts

section

@[expose] public section



section
noncomputable section
namespace UpperTheory.GalC
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory Tr
variable {D : D7}

theorem pre_cut_alt {c : CutD D} (hc : c.Good) {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) : _root_.UpperTheory.GalC.GaloisPreconditions (cut D c) (nchCut c x) :=
  have R := _root_.UpperTheory.GalC.Tr.rs_cut_of_good_aux41 hc h.Conclusion1.1 h.what₂
  have A := _root_.UpperTheory.GalC.Tr.admissible_cut (c := c) h.adm
  have lam : GlobalTheory.NRows.LamUsed (cut D c) := h.lam
  { what₂ := R
    adm := A
    Conclusion1 := _root_.UpperTheory.GalS.Parts.main_alt_alt _ A.1 R.a.tieLab R.b.rowSize R.a.hecke lam.loc R.b.thetaOne R.a.g4p
    z := pointsAdmissible_restrictToPoints hc h.z
    rhoBar := rhoBar_cut h.rhoBar
    g3p := _root_.UpperTheory.GalC.Tr.admissible_tame_eigenvalues_of_cut h.g3p
    weight := fun i => h.weight i.1
    block := fun i => h.block i.1
    muUnr := fun i => h.muUnr i.1
    depthG := fun i => h.depthG i.1
    bc := h.bc
    lam := lam
    c2 := jointCondition_restrictToPoints h.c2
    large := large_cut h.large
    nct := nct_cut c h.nct
    trip := fun a => h.trip a.1
    same := fun a => h.same a.1
    good := h.good }
theorem facts_of_galois_preconditions_of_cutRec (hCh : GlobalTheory.TwSys.Cheb) (lf : LocalFiniteness) (ltd : LocalTateDuality) (lec : LocalEulerChar)
    {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) (hC : CutRec D) : _root_.GlobalTheory.NFacts.NormChoiceFacts D x :=
  have ex : GlobalTheory.StringRepresentationDecomposition.RbEx D := GlobalTheory.T.residualRankPartExists_of_jointCondition D h.what₂.c.rho
  have h0 : SumRepresentations.tie0 D := h.adm.1.1.1
  have h1 : SumRepresentations.adm1 D := h.adm.1.1.2.2.1
  have g2 := _root_.UpperTheory.GalS.de_rham_points_weight_jumps_alt D h0 h1 h.what₂.a.a2 h.what₂.a.a5 hC
  { what₂ := h.what₂, adm := h.adm, Conclusion1 := h.Conclusion1
    Conclusion2 := ⟨_root_.UpperTheory.GalS.prvG5_of_admissible_cutRec lf ltd lec D h.adm ex hC, _root_.GlobalTheory.T.prvG6_of_admissible' D h.adm ex, h.z⟩
    rhoBar := h.rhoBar, g3p := h.g3p, weight := h.weight, block := h.block, g2 := g2
    admJ := fun L hL => _root_.UpperTheory.GalS.admJ_of_admPar D L h0 h1 h.what₂.a.a2 h.what₂.a.a5 hC h.weight h.block hL
    muUnr := h.muUnr, depthG := h.depthG, bc := h.bc, lam := h.lam, c2 := h.c2, large := h.large
    duties := _root_.UpperTheory.GalS.duties_of_large_aux41 hCh D h.large h.Conclusion1.1 g2.2 h.rhoBar
    nct := h.nct, trip := h.trip, same := h.same, good := h.good }
theorem exists_good_cut_facts_tie4 (hCh : GlobalTheory.TwSys.Cheb) (lf : LocalFiniteness) (ltd : LocalTateDuality) (lec : LocalEulerChar)
    {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) (hT : Tie4 D) :
    ∃ c : CutD D, c.Good ∧ _root_.GlobalTheory.NFacts.NormChoiceFacts (cut D c) (nchCut c x) ∧ Tie4 (cut D c) := by
  obtain ⟨c, hc⟩ := _root_.UpperTheory.GalC.exists_good_alt (GlobalTheory.T.central_elements_from_idempotent_coeffs GlobalTheory.CentralIdem.centralIdemCoeff) h hT
  exact ⟨c, hc, _root_.UpperTheory.GalC.facts_of_galois_preconditions_of_cutRec hCh lf ltd lec (_root_.UpperTheory.GalC.pre_cut_alt hc h) (cutRec_cut hc), compatibilityTies_eigenRestriction c hT⟩
end UpperTheory.GalC
end
end
end
end
