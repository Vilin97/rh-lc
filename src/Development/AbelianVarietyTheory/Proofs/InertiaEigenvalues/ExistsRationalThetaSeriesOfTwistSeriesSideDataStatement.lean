module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesBaseTwistedUniversalRationalStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf

-- Source module: Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure TwJoin (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (nch : NChoice D) (xd : ThData D) (first : Prop) {G : Type}
    [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL]
    (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (S : RatDat D.ntw) (YS : NExpRealS R cG S)
    (cf : CharFrame D) : Type 1 where
  X : RealSide D
  Γ_eq : X.Γ = G
  grp_eq : HEq X.grp iG
  fin_eq : HEq X.fin fG
  Pl0_eq : X.Pl0 = Pl0
  I0_eq : X.I0 = I0
  T_eq : X.T = T
  core_eq : X.core = C
  alg_eq : HEq X.alg aC
  R_eq : HEq X.R R
  F_eq : HEq X.F F
  cG_eq : HEq X.cG cG
  geo_eq : HEq X.geo geo
  A3_eq : HEq X.A3 A3
  Y : SerSide X (twEOf xd)
  S_eq : Y.S = S
  YS_eq : HEq Y.YS YS
  gal : GalSide D
  cf_eq : gal.cf = cf
  lam_eq : gal.lam.C = cf
  C_eq : X.R.C = cf
  field : FieldOk X
  cg : CGTrue hL D gal.wd
  base : first → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)

theorem TwJoin.Sb_eq {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop} {G : Type}
    [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D}
    [aC : Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} {S : RatDat D.ntw} {YS : NExpRealS R cG S}
    {cf : CharFrame D} (a : TwJoin hL D nch xd first R F cG geo S YS cf) : a.X.R.Sb = R.Sb := by
  obtain ⟨X, h1, h2, h3, h4, h5, h6, h7, h8, hR, -, -, -, hA, -⟩ := a
  cases X
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 hR hA ⊢
  subst h1 h4 h5 h6 h7
  cases h2; cases h3; cases h8; cases hA; cases hR
  rfl

end GlobalTheory.TwInputs

end
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyExtAnd

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RealSide.Framed {D : D7} (X : RealSide D) : Prop :=
  ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV

theorem RealSide.space_eq {D : D7} (X : RealSide D) (j : Fin D.R.m) :
    X.core.V ((j : ℕ) + 1) X.core.σ₀ = Wc D j :=
  X.geo.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ X.core.toCore.good_σ₀

section At

variable (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (nch : NChoice D) (xd : ThData D) (first : Prop) {G : Type}
  [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL]
  (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
  (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (S : RatDat D.ntw) (YS : NExpRealS R cG S)

def TwAt (_H : NExpRealH R cG S YS) (cf : CharFrame D) : Type 1 :=
  TwJoin hL D nch xd first R F cG geo S YS cf

variable {hL D nch xd first R F cG geo S YS}

theorem TwAt.Sb_eq {H : NExpRealH R cG S YS} {cf : CharFrame D} (a : TwAt hL D nch xd first R F cG geo S YS H cf) :
    a.X.R.Sb = R.Sb := TwJoin.Sb_eq a

end At

def TwExt (hL : GlobalTheory.Published.LocalLanglandsGL) : NExt hL := fun _ B _ T w Z _ _ t nch _ xd c =>
  TwAt hL (w.st Z).toD7 nch xd (T = TwDat.untw B T.pl) t.r.z.R t.r.z.F t.r.z.cG t.r.z.geo _ c.row.nexp c.row.hecke (TC.cf w.I w.l Z)

section Rows

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)}

end Rows

end GlobalTheory.TwInputs

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalThetaSeriesOfTwistSeriesSideData

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatBundles

theorem ratHyp {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D} (Y : SerSide X E) (hF : FieldOk X)
    (hP : ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (j : Fin D.R.m) : GlobalTheory.BigOn.Exp.RatHyp X.core X.R X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O i j (X.space_eq j) :=
  have hC := X.char
  { size := X.size
    host := X.host
    std := X.std j
    laws := X.geo.fw.laws
    core := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.chain, hC.thP⟩
    unif := X.unif
    fw := ⟨X.geo.fw⟩
    tieIn := ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
    io := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
    guard := X.guard
    fin := X.finT
    pins := X.geo.pins j
    phase := by
      convert X.geo.phase j X.unif using 2
      rename_i k
      rw [X.phs k]
      simp
    frame := hP j _
    galois := hF.galois
    small := ⟨hF.vals, hF.ray, hF.roots⟩
    inUse := hi
    low := Y.low i }

theorem levelOf {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) : Y.Z.ρ.LevelOf D.nexp :=
  ⟨fun i j b => (Y.Z.tie i j b).U_eq, fun i j b => (Y.Z.tie i j b).psiU_eq⟩

theorem rat_of_split (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hS : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat) {D : D7} (X : RealSide D) {E : IntegralHeckeForms.XD D}
    (Y : SerSide X E) (hF : FieldOk X) (hsp : D.host.cls D.host.pde = .splitK ∧ D.host.cls D.host.pde' = .splitK)
    (hP : ∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) {i : D.ntw.Tw} (hi : D.ntw.NonzeroIndexPlace i)
    (j : Fin D.R.m) (b : Bool) : RatRow Y.YS X.geo.v₀ Y.Z.good i j b :=
  GlobalTheory.T.thetaSeries_base_twisted_universal_rational hA hA.rayClassFieldSt (GlobalTheory.SerStd.seriesRatS_of hS) D X.Γ X.Pl0 X.I0 X.T X.A3 X.core X.R X.cG Y.S Y.YS
    X.F.lv2 X.geo.κ X.geo.v₀ X.geo.O Y.Z.ρ Y.Z.good i j b (X.space_eq j) Y.Z.pin (levelOf Y) hsp (ratHyp X Y hF hP hi j)

theorem rat_bundles : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b :=
  fun hA hS _ X _ Y hF hP _ hi j b => rat_of_split hA hS X Y hF hF.split hP hi j b

end GlobalTheory.RatBundles
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalThetaSeriesOfTwistSeriesSideDataStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_rational_thetaSeries_of_twistSeriesSideData : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), FieldOk X → (∀ (j : Fin D.R.m) hV, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin X.core X.R.toRealDat j X.core.σ₀ hV) → ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b := by
  first | exact @GlobalTheory.RatBundles.rat_bundles | exact GlobalTheory.RatBundles.rat_bundles | (intros; apply GlobalTheory.RatBundles.rat_bundles <;> assumption)
end
end
