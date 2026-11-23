module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryPosDefHermitianSameRank
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomMapApply
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorIsometryMovedOrthonormal
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOrientedVacuumIsometryMovedLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilDatumSignedHomPairTransportIsometriesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMovedRiggingIsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFirstMemberHalfIsometryMoved
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondMemberHalfIsometryMoved
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaAtIdempotentHermitianHomIsometryTransport

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryPosDefHermitianSameRankStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank : ∀ {D : D7} {V V' : HSp D}, V.rank = V'.rank → NegIdx V 0 → NegIdx V' 0 → Nonempty (GlobalTheory.Mem.Isom.IsoMat V V') := by
  first | exact @GlobalTheory.BottomIsom.isoMat_of_posDef | exact GlobalTheory.BottomIsom.isoMat_of_posDef | (intros; apply GlobalTheory.BottomIsom.isoMat_of_posDef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainMapIsometryConj

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.haar_fundamentalDomain_map_isometry_conj : ∀ {D : D7} {S S' : HSp D} (I : GlobalTheory.Mem.Isom.IsoMat S S') (m : MeasureTheory.Measure (GA D S)) (fd : Set (GA D S)),
  m.IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ S) fd m →
  (m.map I.kap).IsHaarMeasure ∧ MeasureTheory.IsFundamentalDomain (GQ S') (I.kap.symm ⁻¹' fd) (m.map I.kap) := by
  intro D S S' I m fd ⟨h1, h2⟩
  haveI : IsTopologicalGroup (GA D S) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GA D S') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (GA D S') := ⟨rfl⟩
  refine ⟨I.kap.isHaarMeasure_map m I.continuous_kap I.continuous_kap_symm, ?_⟩
  have hm : Measurable I.kap := I.continuous_kap.measurable
  have hm' : Measurable I.kap.symm := I.continuous_kap_symm.measurable
  have hq : MeasureTheory.Measure.QuasiMeasurePreserving I.kap.symm (m.map I.kap) m := by
    refine ⟨hm'.aemeasurable, ?_⟩
    rw [MeasureTheory.Measure.map_map hm' hm]
    have : (I.kap.symm : GA D S' → GA D S) ∘ I.kap = id := funext fun x => I.kap.symm_apply_apply x
    rw [this, MeasureTheory.Measure.map_id]
  let e : GQ S ≃ GQ S' :=
    { toFun := fun γ => ⟨I.kap γ, I.kap_mem_GQ γ.2⟩
      invFun := fun γ => ⟨I.kap.symm γ, I.symm.kap_mem_GQ γ.2⟩
      left_inv := fun γ => Subtype.ext (I.kap.symm_apply_apply _)
      right_inv := fun γ => Subtype.ext (I.kap.apply_symm_apply _) }
  refine h2.preimage_of_equiv hq (e := e) e.bijective fun γ x => ?_
  show I.kap.symm (I.kap γ * x) = (γ : GA D S) * I.kap.symm x
  rw [map_mul, MulEquiv.symm_apply_apply]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSeesawTripleTransportIsometries

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory GlobalTheory.TriMove GlobalTheory.Mem.Isom

namespace GlobalTheory.TriMoveConst

variable {D : D7}

def kapME {V V' : HSp D} (I : IsoMat V V') : GA D V ≃ᵐ GA D V' :=
  (Homeomorph.mk I.kap.toEquiv I.continuous_kap I.continuous_kap_symm).toMeasurableEquiv

theorem kapME_apply {V V' : HSp D} (I : IsoMat V V') (g : GA D V) : kapME I g = I.kap g := rfl

theorem preimage_kapME {V V' : HSp D} (I : IsoMat V V') (s : Set (GA D V)) : kapME I ⁻¹' (I.kap.symm ⁻¹' s) = s := by
  ext g
  simp only [Set.mem_preimage, kapME_apply, MulEquiv.symm_apply_apply]

theorem trH_symm_trH {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T') (F : WO S T → ℂ) :
    trH IS.symm IT.symm (trH IS IT F) = F := by
  funext w
  show F ((homMap IS IT).symm (homMap IS IT w)) = F w
  rw [AddEquiv.symm_apply_apply]

theorem thetaKO_omH {S S' T T' : HSp D} (IS : IsoMat S S') (IT : IsoMat T T')
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T) (F : WO S T → ℂ) :
    thetaKO (omH IS IT om) (IS.kap g) (IT.kap h) (trH IS IT F) = thetaKO om g h F := by
  unfold thetaKO
  rw [omH_apply, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, trH_symm_trH]
  show (om (g, h) F) ((homMap IS IT).symm 0) = _
  rw [map_zero]

variable {T₀ : Type} {A A' WW B B' WW₁ : HSp D}

theorem ker_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) (g : GA D B) :
    (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) (IA.kap g) = Y.ker ψ θ t P h g := by
  have hF := GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal ψ θ hθ true IA IW Y.rA.s Y.rA.B Y.rW.s Y.rW.B (Y.f t) P
  have hs : ∀ {k : ℕ} (s : Matrix (Fin k) (Fin k) ℂ), GlobalTheory.Grid.sgnM true s = -s := fun _ => rfl
  simp only [hs] at hF
  exact (congrArg (thetaKO (omH IA IW (Y.ω t)) (IA.kap g) (IW.kap h)) hF).trans (thetaKO_omH IA IW (Y.ω t) g h _)

theorem ker'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) (g : GA D B') :
    (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) (IA'.kap g) = Y.ker' ψ θ t P h g := by
  have hF := GlobalTheory.T.fockPureTensor_isometry_moved_orthonormal ψ θ hθ false IA' IW Y.rA'.s Y.rA'.B Y.rW.s Y.rW.B (Y.f' t) P
  show thetaKO (omH IA' IW (Y.ω' t)) (IA'.kap g) (IW.kap h) (pureTensorO ψ θ (GlobalTheory.Grid.sgn false A') WW
      (fun τ => GlobalTheory.Grid.sgnM false (cartMove IA' τ (Y.rA'.s τ))) (fun τ => cartMove IW τ (Y.rW.s τ))
      (fun τ => basMove IA' τ (Y.rA'.B τ)) (fun τ => basMove IW τ (Y.rW.B τ)) (trH IA' IW (Y.f' t))
      (polMove IW.rank_eq IA'.rank_eq P)) =
    thetaKO (Y.ω' t) g h (pureTensorO ψ θ (GlobalTheory.Grid.sgn false B') WW₁ (fun τ => GlobalTheory.Grid.sgnM false (Y.rA'.s τ)) Y.rW.s Y.rA'.B
      Y.rW.B (Y.f' t) P)
  rw [hF, thetaKO_omH]

theorem I_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) :
    (triMove IA IA' IW Y).I ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) = Y.I ψ θ t P h := by
  show ∫ g in IA.kap.symm ⁻¹' Y.fd, (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) g
      ∂(Y.m.map (kapME IA)) = _
  rw [setIntegral_map_equiv (kapME IA), preimage_kapME]
  exact congrArg (fun F => ∫ g in Y.fd, F g ∂Y.m) (funext fun g => ker_move IA IA' IW Y ψ θ hθ t P h g)

theorem I'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) :
    (triMove IA IA' IW Y).I' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) = Y.I' ψ θ t P h := by
  show ∫ g in IA'.kap.symm ⁻¹' Y.fd', (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) g
      ∂(Y.m'.map (kapME IA')) = _
  rw [setIntegral_map_equiv (kapME IA'), preimage_kapME]
  exact congrArg (fun F => ∫ g in Y.fd', F g ∂Y.m') (funext fun g => ker'_move IA IA' IW Y ψ θ hθ t P h g)

theorem integrableOn_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B.rank)
    (h : GA D WW₁) :
    IntegrableOn ((triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h)) (triMove IA IA' IW Y).fd
      (triMove IA IA' IW Y).m ↔ IntegrableOn (Y.ker ψ θ t P h) Y.fd Y.m := by
  show IntegrableOn ((triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h)) (IA.kap.symm ⁻¹' Y.fd)
      (Y.m.map (kapME IA)) ↔ _
  rw [IntegrableOn, (kapME IA).restrict_map, integrable_map_equiv, preimage_kapME]
  have e : (triMove IA IA' IW Y).ker ψ θ t (polMove IW.rank_eq IA.rank_eq P) (IW.kap h) ∘ kapME IA = Y.ker ψ θ t P h :=
    funext fun g => ker_move IA IA' IW Y ψ θ hθ t P h g
  rw [e]
  rfl

theorem integrableOn'_move (IA : IsoMat B A) (IA' : IsoMat B' A') (IW : IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (hθ : IsInfFam θ) (t : T₀) (P : PolF D WW₁.rank B'.rank)
    (h : GA D WW₁) :
    IntegrableOn ((triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h)) (triMove IA IA' IW Y).fd'
      (triMove IA IA' IW Y).m' ↔ IntegrableOn (Y.ker' ψ θ t P h) Y.fd' Y.m' := by
  show IntegrableOn ((triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h)) (IA'.kap.symm ⁻¹' Y.fd')
      (Y.m'.map (kapME IA')) ↔ _
  rw [IntegrableOn, (kapME IA').restrict_map, integrable_map_equiv, preimage_kapME]
  have e : (triMove IA IA' IW Y).ker' ψ θ t (polMove IW.rank_eq IA'.rank_eq P) (IW.kap h) ∘ kapME IA' = Y.ker' ψ θ t P h :=
    funext fun g => ker'_move IA IA' IW Y ψ θ hθ t P h g
  rw [e]
  rfl

theorem isConst_triMove : ∀ {D : D7} {T₀ : Type} {A A' WW B B' WW₁ : HSp D} (IA : GlobalTheory.Mem.Isom.IsoMat B A) (IA' : GlobalTheory.Mem.Isom.IsoMat B' A') (IW : GlobalTheory.Mem.Isom.IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ →
  ∀ c : T₀ → ℂ, Y.IsConst ψ θ c → (GlobalTheory.TriMove.triMove IA IA' IW Y).IsConst ψ θ c := by
  intro D T₀ A A' WW B B' WW₁ IA IA' IW Y ψ θ hθ c hY
  obtain ⟨hc, P, P', H⟩ := hY
  refine ⟨hc, polMove IW.rank_eq IA.rank_eq P, polMove IW.rank_eq IA'.rank_eq P', fun t => ?_⟩
  obtain ⟨hint, ⟨h0, hne⟩, heq⟩ := H t
  refine ⟨fun h' => ?_, ⟨IW.kap h0, ?_⟩, fun h' => ?_⟩
  · obtain ⟨h, rfl⟩ := IW.kap.surjective h'
    exact ⟨(integrableOn_move IA IA' IW Y ψ θ hθ t P h).2 (hint h).1,
      (integrableOn'_move IA IA' IW Y ψ θ hθ t P' h).2 (hint h).2⟩
  · rw [I'_move IA IA' IW Y ψ θ hθ t P' h0]
    exact hne
  · obtain ⟨h, rfl⟩ := IW.kap.surjective h'
    rw [I_move IA IA' IW Y ψ θ hθ t P h, I'_move IA IA' IW Y ψ θ hθ t P' h]
    exact heq h

end GlobalTheory.TriMoveConst

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstSeesawTripleTransportIsometriesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isConst_seesawTriple_transport_isometries : ∀ {D : D7} {T₀ : Type} {A A' WW B B' WW₁ : HSp D} (IA : GlobalTheory.Mem.Isom.IsoMat B A) (IA' : GlobalTheory.Mem.Isom.IsoMat B' A') (IW : GlobalTheory.Mem.Isom.IsoMat WW₁ WW) (Y : Tri T₀ B B' WW₁) (ψ : AddChar (AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D), IsInfFam θ →
  ∀ c : T₀ → ℂ, Y.IsConst ψ θ c → (GlobalTheory.TriMove.triMove IA IA' IW Y).IsConst ψ θ c := by
  first | exact @GlobalTheory.TriMoveConst.isConst_triMove | exact GlobalTheory.TriMoveConst.isConst_triMove | (intros; apply GlobalTheory.TriMoveConst.isConst_triMove <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomStageTransportSameConstants

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.TriMove in
theorem GlobalTheory.TriMove.transport_bottom : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (W : G.Weil) (i j : Fin D.R.m) {A A' WW B B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T B B' WW₁),
  IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ Y' : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j 0 0 Y' ∧ ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Y'.IsConst W.ψ W.θ c := by
  intro D T Lc sc G W i j A A' WW B B' WW₁ X Y hX hY
  obtain ⟨hp, hq, rX1, negRightMulLetterShift, nX1, nX2, nX3, isX⟩ := GlobalTheory.SqTower.IsBottomTri.isStageC hX
  obtain ⟨-, -, rY1, rY2, nY1, nY2, nY3, isY⟩ := hY
  have e1 : B.rank = A.rank := by omega
  have e2 : B'.rank = A'.rank := by omega
  have e3 : WW₁.rank = WW.rank := by rw [← isY.rank, ← isX.rank, e1, e2]
  obtain ⟨IA⟩ := GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank e1 nY1 nX1
  obtain ⟨IA'⟩ := GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank e2 nY2 nX2
  obtain ⟨IW⟩ := GlobalTheory.T.exists_isometry_posDef_hermitian_same_rank e3 nY3 nX3
  refine ⟨triMove IA IA' IW Y, ⟨hp, hq, rX1, negRightMulLetterShift, nX1, nX2, nX3, ?_⟩,
    fun c hc => GlobalTheory.T.isConst_seesawTriple_transport_isometries IA IA' IW Y W.ψ W.θ isY.isVac.2.inf c hc⟩
  exact
    { rank := isX.rank
      rigA := GlobalTheory.T.isometryMovedRigging_is IA _ isY.rigA
      rigA' := GlobalTheory.T.isometryMovedRigging_is IA' _ isY.rigA'
      rigW := GlobalTheory.T.isometryMovedRigging_is IW _ isY.rigW
      weil := fun t => GlobalTheory.T.isWeilDatumSignedHomPair_transport_isometries W.ψ true IA IW _ _ (Y.ω t) (isY.weil t)
      weil' := fun t => GlobalTheory.T.isWeilDatumSignedHomPair_transport_isometries W.ψ false IA' IW _ _ (Y.ω' t) (isY.weil' t)
      isVac := GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices W.ψ W.θ true IA IW Y.rA.s Y.rW.s Y.rA.Λ Y.rW.Λ Y.vac isY.isVac
      isVac' := GlobalTheory.T.isOrientedVacuum_isometry_moved_lattices W.ψ W.θ false IA' IW Y.rA'.s Y.rW.s Y.rA'.Λ Y.rW.Λ Y.vac' isY.isVac'
      idem := isY.idem
      expo := isY.expo
      fst := fun t => by
        have h5 := GlobalTheory.T.thetaAtIdempotent_hermitianHomIsometry_transport W.ψ true IA IW (Y.e t) Y.rA.Λ Y.rW.Λ Y.vac _ (Y.f t) (isY.fst t)
        rw [← GlobalTheory.T.standardPairFirstMemberHalf_isometry_moved] at h5
        exact h5
      snd := fun t => by
        have h5 := GlobalTheory.T.thetaAtIdempotent_hermitianHomIsometry_transport W.ψ false IA' IW _ Y.rA'.Λ Y.rW.Λ Y.vac' _ (Y.f' t) (isY.snd t)
        rw [← GlobalTheory.T.standardPairSecondMemberHalf_isometry_moved, e1] at h5
        exact h5
      meas := GlobalTheory.T.haar_fundamentalDomain_map_isometry_conj IA Y.m Y.fd isY.meas
      meas' := GlobalTheory.T.haar_fundamentalDomain_map_isometry_conj IA' Y.m' Y.fd' isY.meas' }
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomStageTransportSameConstantsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.definiteBottom_stage_transport_same_constants : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (W : G.Weil) (i j : Fin D.R.m) {A A' WW B B' WW₁ : HSp D} (X : Tri T A A' WW) (Y : Tri T B B' WW₁),
  IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ Y' : Tri T A A' WW, GlobalTheory.SqTower.IsStageC W i j 0 0 Y' ∧ ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Y'.IsConst W.ψ W.θ c := by
  first | exact @GlobalTheory.TriMove.transport_bottom | exact GlobalTheory.TriMove.transport_bottom | (intros; apply GlobalTheory.TriMove.transport_bottom <;> assumption)
end
end
