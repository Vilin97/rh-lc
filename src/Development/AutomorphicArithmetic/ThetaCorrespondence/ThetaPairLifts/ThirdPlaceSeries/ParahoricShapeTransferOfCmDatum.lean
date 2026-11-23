module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelByPlacesParahoricAtConductorPlaceTameCharac
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterSplitPlaceLocalComponent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CellPlacesDisjointOfSeparated
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThirdLevelOfGoodTwists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComapRealSubfieldEqIffEqOrIsConjPlace
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfPlane
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConductorValuationDeltaComparison
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConductorValuationQComparison
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameLevelValueTrivialAtWildPlace

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelByPlacesParahoricAtConductorPlaceTameCharacStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)


theorem _root_.GlobalTheory.T.levelByPlaces_parahoric_at_conductorPlace_tameCharacter : ∀ (D : D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (e₀ : ℤ) (W₀ : Type) [AddCommGroup W₀] [Module (FractionRing (D.ntw.O i)) W₀] (ρ₀ : Representation (FractionRing (D.ntw.O i)) (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) W₀) (τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ) (M : NX.MtVReal D i j b k Q ψ e₀ W₀ ρ₀ τ) (ek : NX.Kk D i k →+* ℂ) (P : PlE D.host) (ξ : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), (P ∈ M.QP ∨ P ∈ M.DP) → ¬ (P ∈ M.QP ∧ P ∈ M.DP) → (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P).v) → (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P).v → P'' = P) → (∀ P'' ∈ M.QP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal ψ P'' e₀ u = 1) → (∀ P'' ∈ M.DP, ∀ u : 𝓞 D.host.E, u - 1 ∈ P''.asIdeal → NX.tameVal (D.ntw.delta i) P'' (if b then e₀ else -e₀) u = 1) → (P ∈ M.QP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofOk D i k (NX.tameVal ψ P e₀ a).1)) → (P ∈ M.DP → ∀ (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))ˣ) (a : 𝓞 D.host.E), a ∉ P.asIdeal → Valued.v (y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) = 1 → Valued.v ((y : ((M.sp P).v.adicCompletion (maximalRealSubfield D.host.E))) - (M.sp P).i (a : D.host.E)) < 1 → ((ξ y : ℂˣ) : ℂ) = ek (NX.ofO0 D i k (NX.tameVal (D.ntw.delta i) P (if b then e₀ else -e₀) a).1)) → NG.LevelPara M.J (cx ek M.χ) (M.sp P) D.R.r ξ := by
  first | exact @GlobalTheory.LevParaLoc.levelPara_loc | exact GlobalTheory.LevParaLoc.levelPara_loc | (intros; apply GlobalTheory.LevParaLoc.levelPara_loc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QPlacesOfAdmissibleTwist

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.ParaPlace

theorem unr_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt u) (h' : χ'.UnrAt u) : (χ * χ').UnrAt u := fun y hy => by
  change χ.loc u y * χ'.loc u y = 1
  rw [h y hy, h' y hy, one_mul]

end GlobalTheory.LevCmp.ParaPlace
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConductorLevelComparisonParamodularPlace

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
namespace GlobalTheory.LevCmp.ParaPlace
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ u ∈ qPl (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j), ∃ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v = u := by
  intro _ hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j htw hl hok
  have hQ : QOf P v = T.Q v := GlobalTheory.HeightCounting.Up.Model.qOf_eq v
  have h2 := P.q.mu.tw v
  intro u hu
  obtain ⟨hg, w', hw'u, hun⟩ := hu
  have hmu : ((cfOf x).mu0 j).UnrAt w' :=
    ((cfOf x).isMu0 j).unr w' fun k hk => hg ⟨w', hw'u, k, hk⟩
  have hxi : ¬ (T.xiTw f v).UnrAt w' := by
    intro hx
    rw [← h2] at hx
    exact hun (unr_mul hmu hx)
  unfold TwDat.xiTw at hxi
  set M := cell (D := Dof x) l.b.Bs.exp b hA j
  have fin : ∀ P' : PlE (Dof x).host, (P' ∈ M.QP ∨ P' ∈ M.DP) → (w' = P' ∨ IsConjPl (Dof x).host w' P') →
      ∃ P' : PlE (Dof x).host, (P' ∈ M.QP ∨ P' ∈ M.DP) ∧ (M.sp P').v = u := by
    intro P' hP' hc
    refine ⟨P', hP', ?_⟩
    have hw := M.sp_w P' (hP'.elim Or.inl (fun h => Or.inr (Or.inl h)))
    have hov : NG.OverPl P' u := by
      have e := (GlobalTheory.PlacePair.comap_eq_iff (Dof x) w' P').2 hc
      exact e.symm.trans hw'u
    apply HeightOneSpectrum.ext
    exact (M.sp P').w_under.symm.trans (by rw [hw]; exact hov)
  by_cases hq : w' ∈ T.Q v
  · obtain ⟨P', hP', hc⟩ := M.QP_cover w' (hQ ▸ hq)
    exact fin P' (Or.inl hP') (hc.imp Eq.symm id)
  · have hψ : (T.psi v).UnrAt w' := ((T.psi_is v).ram w').2 hq
    have hd := fun h => hxi (unr_mul h hψ)
    have hp : w' ∈ (Dof x).ntw.pD i := by
      rw [← Finset.mem_coe, (Dof x).ntw.pD_eq i, hl]
      change w' ∈ placesOver B.host.E (if B.places.resChar v = B.host.pde then B.host.pde' else B.host.pde)
      split_ifs at hd ⊢
      · by_contra ho; exact hd (f.isDel'.unr w' ho)
      · by_contra ho; exact hd (f.isDel.unr w' ho)
    obtain ⟨P', hP', hc⟩ := M.DP_cover w' hp
    exact fin P' (Or.inr hP') (hc.imp Eq.symm id)
end GlobalTheory.LevCmp.ParaPlace
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

theorem _root_.GlobalTheory.T.conductor_level_le_at_twisted_place_of_twOK : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ u ∈ qPl (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j), ∃ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) ∧ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').v = u := by
  first | exact @_root_.GlobalTheory.LevCmp.ParaPlace.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LevCmp.ParaPlace.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LevCmp.ParaPlace.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesMembershipTwist

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TwTameCell

theorem tameAt_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (h : χ.TameAt v) (h' : χ'.TameAt v) : (χ * χ').TameAt v := fun y hy hy1 => by
  change χ.loc v y * χ'.loc v y = 1
  rw [h y hy hy1, h' y hy hy1, mul_one]

theorem tameAt_one {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).TameAt v :=
  fun _ _ _ => rfl

end GlobalTheory.TwTameCell

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistCharacterTamelyRamifiedAtPlace

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.TwTameCell
theorem twist_character_tame_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → (eta (D := Dof x) (cfOf x) w.I.xi v j).TameAt P' := by
  intro _ hL
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j _ _ _ P' _
  have h1 := ((cfOf x).isMu0 j).tame P'
  have hx : w.I.xi ((Dof x).what₂.muTw v) ∈ T.set f := w.xi_range ▸ Set.mem_range_self _
  simp only [TwDat.set, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range] at hx
  have h2 : (w.I.xi ((Dof x).what₂.muTw v)).TameAt P' := by
    rcases hx with (h | h | h) | ⟨w', h⟩
    · rw [h]; exact tameAt_one P'
    · rw [h]; exact f.isDel.tame P'
    · rw [h]; exact f.isDel'.tame P'
    · rw [← h]
      unfold TwDat.xiTw
      split_ifs
      · exact tameAt_mul (f.isDel'.tame P') ((T.psi_is w').tame P')
      · exact tameAt_mul (f.isDel.tame P') ((T.psi_is w').tame P')
  exact tameAt_mul h1 h2
end GlobalTheory.TwTameCell
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

theorem _root_.GlobalTheory.T.twist_character_tamely_ramified_at_place' : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ P' : PlE (Dof x).host, (P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).QP ∨ P' ∈ (cell (D := Dof x) l.b.Bs.exp b hA j).DP) → (eta (D := Dof x) (cfOf x) w.I.xi v j).TameAt P' := by
  first | exact @_root_.GlobalTheory.TwTameCell.twist_character_tame_at_place_alt | exact _root_.GlobalTheory.TwTameCell.twist_character_tame_at_place_alt | (intros; apply _root_.GlobalTheory.TwTameCell.twist_character_tame_at_place_alt <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParahoricShapeTransferOfCmDatum

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)
noncomputable section
namespace GlobalTheory.XPara
theorem parahoric_shape_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ParaShape (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) := by
  intro hPr hL
  refine (StepW.and (_root_.GlobalTheory.T.conductor_level_le_at_twisted_place_of_twOK hPr hL) (StepW.and (_root_.GlobalTheory.T.cell_places_disjoint_of_admTw hPr hL) (StepW.and (_root_.GlobalTheory.T.twist_character_tamely_ramified_at_place' hPr hL)
    (StepW.and (_root_.GlobalTheory.T.conductor_valuation_q_le_of_sideRead hPr hL) (StepW.and (_root_.GlobalTheory.T.conductor_valuation_delta_le_of_sideRead hPr hL) (_root_.GlobalTheory.T.tw_ok_value_trivial_at_twisted_place hPr hL)))))).trans
    (StepW.of_all fun K B f T w _ _ H P x l v i b ψ hA j htw hl hok e hS hR => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H
  intro u hu
  obtain ⟨P', hP', hPu⟩ := h1 P x l v i b ψ hA j htw hl hok u hu
  obtain ⟨hex, hg, hq, hd⟩ := h2 P x l v i b ψ hA j htw hl hok P' hP'
  obtain ⟨hwq, hwd⟩ := h6 P x l v i b ψ hA j htw hl hok
  have hT := h3 P x l v i b ψ hA j htw hl hok P' hP'
  have hw : ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P').w = P' :=
    (cell (D := Dof x) l.b.Bs.exp b hA j).sp_w P' (hP'.elim Or.inl fun h => Or.inr (Or.inl h))
  rw [← hw] at hT
  obtain ⟨ξ, hξc, hξv⟩ := GlobalTheory.HeckeSplitComp.main _ ((cell (D := Dof x) l.b.Bs.exp b hA j).sp P') _ hT
  refine ⟨(cell (D := Dof x) l.b.Bs.exp b hA j).sp P', ξ, hPu, hξc, ?_⟩
  have hne : ∀ a : 𝓞 (Dof x).host.E, a ∉ P'.asIdeal → (a : (Dof x).host.E) ≠ 0 := fun a ha h0 =>
    ha (by rw [show a = 0 from by exact_mod_cast h0]; exact Ideal.zero_mem _)
  refine GlobalTheory.T.levelByPlaces_parahoric_at_conductorPlace_tameCharacter _ _ _ _ _ _ _ _ _ _ _ _ e P' ξ hP' hex hg hq hd hwq hwd ?_ ?_
  · intro hq' y a ha hy1 hya
    rw [hξv y a (Units.mk0 _ (hne a ha)) rfl hy1 hya, hw]
    exact (h4 P x l v i b ψ hA j htw hl hok e hS hR P' hq' a _ ha rfl).symm
  · intro hd' y a ha hy1 hya
    rw [hξv y a (Units.mk0 _ (hne a ha)) rfl hy1 hya, hw]
    exact (h5 P x l v i b ψ hA j htw hl hok e hS hR P' hd' a _ ha rfl).symm
end GlobalTheory.XPara
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

theorem _root_.GlobalTheory.T.paraShape_of_twisted_sideRead_readsHecke : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ B _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → ∀ e, SideRead i b (T.k v) e → ReadsHecke e ψ (T.psi v) → ParaShape (Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (cell (D := Dof x) l.b.Bs.exp b hA j).J (cx e (cell (D := Dof x) l.b.Bs.exp b hA j).χ) := by
  first | exact @_root_.GlobalTheory.XPara.parahoric_shape_transfer_alt | exact _root_.GlobalTheory.XPara.parahoric_shape_transfer_alt | (intros; apply _root_.GlobalTheory.XPara.parahoric_shape_transfer_alt <;> assumption)
end
end
end
end
