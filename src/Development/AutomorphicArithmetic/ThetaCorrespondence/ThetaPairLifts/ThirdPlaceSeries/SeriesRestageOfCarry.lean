module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepsMatHeqRefl
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesOfLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceOfLocalAdmissible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealMoveOfLink
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Lb1OfRestagingBound

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar



namespace GlobalTheory.HeightCounting.SerCarry

open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr

theorem sideB_facts {D : D7} {cf Rw Pq} {S : RatDat D.ntw} {hL eig θ} (B : SideB D cf Rw (lowAll D) Pq S hL eig θ) {eF}
    (h : eF = B.eF) : HkLaw D S eF hL B.hs B.cHk ∧ LowIn D ∧ PqLaw B.exp Pq := by
  subst h
  refine ⟨B.hkEq, fun i p hp P hP => ?_, B.pq⟩
  rw [B.tw.ringSpec_excludedPlaces_eq i]
  exact Or.inr (B.tw.concreteTwistFrame_extraExcluded_over_smallPrimes i p hp hP)

end GlobalTheory.HeightCounting.SerCarry

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeoExtN

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.StateChecks

namespace GlobalTheory.HeightCounting.SerMove.ReGeo

variable {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {hX : B.fields.Ok} {Wt : Set B.places.Pl}



theorem geo_copy {Z Z' : w.Lt} (z₀ : Dat (w.st Z) w.I hX T Wt) (z : Dat (w.st Z') w.I hX T Wt) (h1 : z.Xg = z₀.Xg)
    (h2 : z.tr = z₀.tr) (h3 : HEq z.core (coreJ (a := Z) Z' z₀.core)) (h4 : HEq z.R (real3 (a := Z) Z' (iK := z₀.alg) z₀.R))
    (hg : GlobalTheory.RealGeo.InGeo z₀.geo) :
    ∃ g : GlobalTheory.RealGeo.GeoHalf z.core z.R.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo g ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z₀ z' → ExtN { z with geo := g } z') ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z' z₀ → ExtN z' { z with geo := g }) := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4 ⊢
  subst h1 h2
  obtain rfl : core = coreJ (a := Z) Z' z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg (a := Z) Z' z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR (a := Z) Z' z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR (a := Z) Z' z₀)) :))))
  refine ⟨?_, ?_, ?_, ?_⟩
  · with_unfolding_all
      exact GlobalTheory.Mem.R3.Tr.geoHalf (a := Z) Z' (iK := z₀.alg) z₀.geo
  · with_unfolding_all
      exact GlobalTheory.Mem.R3.Tr.inGeo_tr (a := Z) Z' (iK := z₀.alg) hg
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }

end GlobalTheory.HeightCounting.SerMove.ReGeo

namespace GlobalTheory.HeightCounting.SerMove

theorem exists_geo_extN : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}, Ext P.z P'.z → ∀ (x : St P) (x' : St P'), ∃ (g : Geo x) (g' : Geo x'), GlobalTheory.RealGeo.InGeo g ∧ GlobalTheory.RealGeo.InGeo g' ∧ ExtN (datAt x g) (datAt x' g') := by
  intro K B B' f f' T T' w w' P P' e x x'
  obtain ⟨g, hg, hL, -⟩ := ReGeo.geo_copy (Z := P.Z₀) (Z' := x.o.Z) P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :))) P.inGeo
  obtain ⟨g', hg', -, hR⟩ :=
    ReGeo.geo_copy (Z := P'.Z₀) (Z' := x'.o.Z) P'.z x'.m.z x'.m.Xg x'.m.tr ((by with_unfolding_all exact (x'.copy.core :))) ((by with_unfolding_all exact (x'.copy.R :))) P'.inGeo
  exact ⟨g, g', hg, hg', hR _ (hL _ e.extN)⟩

end GlobalTheory.HeightCounting.SerMove
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMove

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove GlobalTheory.HeightCounting.SideCopy GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.SerGlue

theorem copyAll_ex {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}
    (h : CopyN D N ι e) (hp : HEq D.naut.plGw D'.naut.plGw) {D'' : D7} (hD : D'' = N.toD7) :
    ∃ ι' e', CopyAll D D'' ι' e' := by
  subst hD
  exact ⟨ι, e, h.cp, h.jL, h.s2, h.lamG, h.Xv, h.qs, hp⟩

theorem fr_same {A A' : Pre} (h : A' = A) {f : Top.Fr A} {f' : Top.Fr A'} (hf : HEq f' f) :
    HEq f.mu0 f'.mu0 ∧ HEq f.eta f'.eta ∧ HEq f.del f'.del ∧ HEq f.del' f'.del' := by
  subst h; cases hf; exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem choice_heq {A A' : Pre} (h : A' = A)
    {p : HeightOneSpectrum (𝓞 (maximalRealSubfield A.host.E)) → HeightOneSpectrum (𝓞 A.host.E)}
    {p' : HeightOneSpectrum (𝓞 (maximalRealSubfield A'.host.E)) → HeightOneSpectrum (𝓞 A'.host.E)}
    (hp : ∀ v, NG.OverPl (p v) v) (hp' : ∀ v, NG.OverPl (p' v) v)
    {s : HeightOneSpectrum (𝓞 A.host.F) → HeightOneSpectrum (𝓞 A.host.E)}
    {s' : HeightOneSpectrum (𝓞 A'.host.F) → HeightOneSpectrum (𝓞 A'.host.E)} (hs : HEq s' s)
    (r : Set.range p = Set.range s) (r' : Set.range p' = Set.range s') : HEq p p' := by
  subst h; cases hs
  refine heq_of_eq (funext fun v => ?_)
  obtain ⟨u, hu⟩ : p v ∈ Set.range p' := by rw [r', ← r]; exact ⟨v, rfl⟩
  have h1 := hp' u
  rw [hu] at h1
  obtain rfl : u = v := HeightOneSpectrum.ext (h1.symm.trans (hp v))
  exact hu.symm

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B}
  {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}

theorem bigHost_st (hO : K.Over B.toPre)
    (hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV)
    (x : St P) : BigHost (Dof x) :=
  ⟨(hB (w.st x.o.Z) hO).1, GlobalTheory.HeightCounting.FirstFacts.vstd_of_over (w.st x.o.Z) hO, (hB (w.st x.o.Z) hO).2⟩

end GlobalTheory.HeightCounting.SerGlue

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsMove

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.HeightCounting.SerMove GlobalTheory.HeightCounting.SideCopy GlobalTheory.Mem.R3.Tr
namespace GlobalTheory.HeightCounting.SerGlue
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B}
  {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}
theorem exists_move_alt (hKP : KPx B' f') (hF : Forced K B' T') (hS' : Start K B' f' T' w') (hO : K.Over B'.toPre)
    (hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV)
    (hE : Enl B B') (hf : HEq f' f) (hSt : Start K B f T w) (hpx : HEq w'.px w.px) (hsel : HEq w'.I.sel w.I.sel)
    (hJ : HEq w'.I.J w.I.J) (hδ : HEq w'.δ w.δ) (x : St P) (l : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x) (hExt : Ext P.z P'.z) (x' : St P')
    (hG : SameGal (Dof x) (Dof x')) (N : TwNew (Dof x')) {ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL}
    {e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0} (hN : CopyN (Dof x) N ι e) (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x'') (ho : x''.o = oTw x' N) :
    ∃ (ι' : (Dof x).what₂.LL →+* (Dof x'').what₂.LL) (e' : ↥(Dof x'').LL0 ≃+* ↥(Dof x).LL0), CopyAll (Dof x) (Dof x'') ι' e' ∧
      SameFrame (cfOf x) (cfOf x'') ∧ HEq l.Pq l''.Pq ∧
      ∃ (g : Geo x) (g'' : Geo x'') (hg : GlobalTheory.RealGeo.InGeo g) (hg'' : GlobalTheory.RealGeo.InGeo g'') (a : BigHost (Dof x))
        (a'' : BigHost (Dof x'')), Nonempty (GlobalTheory.TwInputs.Move.RealMove (sideAt x g hg a) (sideAt x'' g'' hg'' a'') ι') := by
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]; rfl
  obtain ⟨ι', e', h⟩ := copyAll_ex hN hG.pl hD
  obtain ⟨h1, h2, h3, h4⟩ := fr_same hE.1 ((heq_of_eq w'.C_eq).trans (hf.trans (heq_of_eq w.C_eq).symm))
  obtain ⟨g, g'', hg, hg'', hX⟩ := GlobalTheory.HeightCounting.SerMove.exists_geo_extN hExt x x''
  have hO' : K.Over B.toPre := hE.1 ▸ hO
  exact ⟨ι', e', h, ⟨(by with_unfolding_all exact (h1 :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (h4 :))⟩,
    (by with_unfolding_all exact ((choice_heq hE.1 (p := (l.Pq)) (p' := (l''.Pq)) ((l.Pq_over)) ((l''.Pq_over)) (s := (w.I.sel)) (s' := (w'.I.sel)) ((hsel)) ((l.sel)) ((l''.sel))) : _)),
    g, g'', hg, hg'', bigHost_st hO' hB x, bigHost_st hO hB x'',
    GlobalTheory.HeightCounting.SerMove.realMove_of_link x x'' ι' e' g g'' ⟨hO, hKP, hF, hS', hE, hf, hSt, hpx, hsel, hJ, hδ, hExt, h.cp, ⟨h.cp.gal, h.pl⟩, hX⟩ hg hg'' _ _⟩
end GlobalTheory.HeightCounting.SerGlue
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StFacts

section

@[expose] public section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.HeightCounting.SerCarry
open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr
theorem st_facts_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (l : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x) (g : Geo x) (hg : GlobalTheory.RealGeo.InGeo g) (a : BigHost (Dof x)) :
    HkAd (sideAt x g hg a) l.rat.In.Sb ((l.rat.In.hL)) ∧ KeepsMat (D := Dof x) fun i => (l.mt.ad.PV i).ψ :=
  ⟨(l.rat.rat.hecke), x.r.Y.hF, l.mt.ad.id⟩
end GlobalTheory.HeightCounting.SerCarry
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesRestageOfCarry

section

@[expose] public section



section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.HeightCounting.SerCarry
open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr
theorem series_restage_of_carry_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) → ∃ (YS : NExpRealS x''.m.z.R x''.m.z.cG l''.rat.S) (X : NExpTied (Dof x'')), (∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (hadm : NX.AdmTw (Dof x'') i k Q ψ), (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf (Dof x'') l''.Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf (Dof x'') l''.Pq ((Dof x'').ntw.pD i)) ∧ (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (k : ℕ) (P : PlE (Dof x'').host) (y : (Dof x'').nexp.Fm i j b), P ∉ (Dof x'').ntw.S0 i → IsSplitPl (Dof x'').host P → k ≤ (Dof x'').R.r → YS.eF i j b h1 h2 ((Dof x'').nexp.hkF i j b k P y) = algebraMap ((Dof x'').ntw.O i) (FractionRing ((Dof x'').ntw.O i)) (cHk i b P) ^ k • hkF (Dof x'') l''.rat.S i j b (l''.rat.In.hL j) (l''.rat.In.hs j h1 h2) k P (YS.eF i j b h1 h2 y)) ∧ (∀ i x, HEq ((YS.fi i).e x) x) ∧ Nonempty (SerAt YS x''.m.z.geo.v₀ X l''.mt.ad.PV (cfOf x'') l''.Pq) ∧ TauTrue X := by
  intro hPr hSer hL K B' f' T' w' hKP hF hS' hO hB B f T w hE hf hSt hpx hsel hJ hδ P x lb P' hExt x' l' hG N ι e hN x'' l'' ho _ _ _ _ _ _ _ _ cHk hc
  obtain ⟨ι', e', h, hcf, hPq, g, g'', hg, hg'', a, a'', ⟨m⟩⟩ := _root_.GlobalTheory.HeightCounting.SerGlue.exists_move_alt hKP hF hS' hO hB hE hf hSt hpx hsel hJ hδ
    x lb.toLI.toLA hExt x' hG N hN x'' l''.toLA ho
  obtain ⟨H, hp⟩ := _root_.GlobalTheory.HeightCounting.SerCarry.st_facts_alt lb.toLI g hg a
  obtain ⟨H', hp'⟩ := _root_.GlobalTheory.HeightCounting.SerCarry.st_facts_alt l'' g'' hg'' a''
  obtain ⟨L, hl, hq⟩ := sideB_facts lb.b.Bs lb.b.eF
  exact (by with_unfolding_all exact ((series_move h m ((x.m.z.geo)) ((x''.m.z.geo)) (kKs := (lb.rat.kKs)) (hk := (lb.rat.hk)) ((l''.rat.kKs))
    ((l''.rat.hk)) ((lb.b.YS)) ((lb.b.fi)) hl lb.rat.rat.Sb_le l''.rat.rat.Sb_le H H' (hs := (lb.b.Bs.hs)) (c := lb.b.Bs.cHk)
    ((l''.rat.In.hs)) (c' := cHk) hc ((L)) hcf lb.a.A.chr l''.a.A.chr hp hp' hPq hq lb.b.tau ((lb.b.ser))) : _))
end GlobalTheory.HeightCounting.SerCarry
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.mem_of_series_carry_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → K.Over B'.toPre → (∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV) → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : _root_.GlobalTheory.HeightCounting.Up.IntermediateLevel hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ (cHk : ∀ (i : (Dof x'').ntw.Tw) (_b : Bool) (_P : PlE (Dof x'').host), ((Dof x'').ntw.O i)ˣ), (∀ (i : (Dof x).ntw.Tw) (i' : (Dof x'').ntw.Tw) (b : Bool) (P : PlE (Dof x).host) (P' : PlE (Dof x'').host), HEq i i' → HEq P P' → HEq (cHk i' b P') (lb.b.Bs.cHk i b P)) → ∃ (YS : NExpRealS x''.m.z.R x''.m.z.cG l''.rat.S) (X : NExpTied (Dof x'')), (∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (hadm : NX.AdmTw (Dof x'') i k Q ψ), (X.mtV i j b k Q ψ h1 h2 hadm).QP = qpOf (Dof x'') l''.Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = qpOf (Dof x'') l''.Pq ((Dof x'').ntw.pD i)) ∧ (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ (Dof x'').R.m) (k : ℕ) (P : PlE (Dof x'').host) (y : (Dof x'').nexp.Fm i j b), P ∉ (Dof x'').ntw.S0 i → IsSplitPl (Dof x'').host P → k ≤ (Dof x'').R.r → YS.eF i j b h1 h2 ((Dof x'').nexp.hkF i j b k P y) = algebraMap ((Dof x'').ntw.O i) (FractionRing ((Dof x'').ntw.O i)) (cHk i b P) ^ k • hkF (Dof x'') l''.rat.S i j b (l''.rat.In.hL j) (l''.rat.In.hs j h1 h2) k P (YS.eF i j b h1 h2 y)) ∧ (∀ i x, HEq ((YS.fi i).e x) x) ∧ Nonempty (SerAt YS x''.m.z.geo.v₀ X l''.mt.ad.PV (cfOf x'') l''.Pq) ∧ TauTrue X := by
  first | exact @_root_.GlobalTheory.HeightCounting.SerCarry.series_restage_of_carry_alt | exact _root_.GlobalTheory.HeightCounting.SerCarry.series_restage_of_carry_alt | (intros; apply _root_.GlobalTheory.HeightCounting.SerCarry.series_restage_of_carry_alt <;> assumption)
end
end
end
end
