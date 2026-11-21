module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LargeFor
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PadTrueNormDetConst
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotIsBettiZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

variable {D : D7}

abbrev StFams (D : D7) : Type 1 := ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A), StFam S κ

section One

variable {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (F : StFam S κ) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D)

abbrev PolOf {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) : Type := PolDat s Φ (metsOf x Φ) (refMet x Φ)

abbrev padWith {s : FinalTheorems S κ} (x : ToroidalCompactificationData s) (Φ : s.Flag) (cts : Ats S κ) {jC : JC D} (hj : jC.Pinned) (hA : AdmEx S κ) :
    PadPkg D N j s.Comp jC ngTrue :=
  padTrue s Φ (metsOf x Φ) jC hj hA (locStOf F cts) (globStOf F cts)

structure IsKitWith (k : KitT s L jC) (d : s.Comp → D.what₂.Tau → ℝ) (x : ToroidalCompactificationData s) (P : PolOf x k.Φ) (cts : Ats S κ)
    (hj : jC.Pinned) (hA : AdmEx S κ) : Prop where

variable {s jC} in

variable {s L jC} in

namespace IsKitWith

variable {F s L jC} {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} {x : ToroidalCompactificationData s} {P : PolOf x k.Φ} {cts : Ats S κ}
  {hj : jC.Pinned} {hA : AdmEx S κ} (h : IsKitWith F s L jC k d x P cts hj hA)
include h

open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain in

end IsKitWith

end One

def IsKitOf (st : StFams D) : KitClass D := fun A N j S κ s L jC k d =>
  ∃ x P cts hj hA, IsKitWith (st A N j S κ) s L jC k d x P cts hj hA

namespace IsKitOf

variable {st : StFams D} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} {L : CmList A} {jC : JC D}
  {k : KitT s L jC} {d : s.Comp → D.what₂.Tau → ℝ} (h : IsKitOf st A N j S κ s L jC k d)
include h

end IsKitOf

end GlobalTheory.ShFam
