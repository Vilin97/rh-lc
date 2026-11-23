module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIoExtensionOfWeakCharacterisationFramesStatement
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormReadingsIndependentSpanningAllEmbeddingsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastPosOfKapIs
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PbEqOfPins
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisation

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRowCoreFormsOfGeometricAction

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem lUnif_topR_of_geoAct : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GeoAct T R κ v₀ → (topR T R κ v₀).LUnif := by
  intro hC hV D G _ _ Pl0 T0 A T _ R κ v₀ hI hM hT hpb hκ hn hg
  exact lUnif_topN T R κ v₀ (nTop T κ) (hasB_nTop T hT.laws κ) hM.HW
    (GlobalTheory.T.cuspFormReadings_independent_spanning_all_embeddings hC hV D G Pl0 T0 A T R κ v₀ hI hM hT hpb hκ hn) hg

end GlobalTheory.HolDict
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRowCoreFormsOfGeometricActionStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.uniformisationRow_coreForms_of_geometricAction : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → (∀ i, (κ i).LastPos) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → GeoAct T R κ v₀ → (topR T R κ v₀).LUnif := by
  first | exact @GlobalTheory.HolDict.lUnif_topR_of_geoAct | exact GlobalTheory.HolDict.lUnif_topR_of_geoAct | (intros; apply GlobalTheory.HolDict.lUnif_topR_of_geoAct <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.JUnifAndLUnifOfTieIn

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem jUnif_and_lUnif_of_tieIn : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → JUnif T R κ v₀ ∧ (GeoAct T R κ v₀ → (topR T R κ v₀).LUnif) := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ hL hM hT hpb hnV
  have hlp := GlobalTheory.HolDict.lastPos_of_kapIs D κ hT.kap
  exact ⟨GlobalTheory.T.cuspFormReadings_independent_spanning_all_embeddings h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb hlp hnV,
    GlobalTheory.T.uniformisationRow_coreForms_of_geometricAction h1 h2 D G Pl0 T0 A T R κ v₀ hL hM hT hpb hlp hnV⟩

end GlobalTheory.HolDict
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TieInOfFwTie

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Div

theorem tieIn_of_fwTie : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), FWTie T R κ v₀ → TieIn T R κ v₀ :=
  fun _ _ _ _ _ t => ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

end GlobalTheory.Div
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfPins

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TiedUnif

theorem lUnif_of_pins : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), ∀ (F : Face D A) (fw : FWTie T R κ v₀), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → BarTie fw → (∀ i, OMPins T R κ v₀ O i) → RhoGeo fw O → EquivAll T R κ O → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.LUnif := by
  intro h1 h2 D G _ _ Pl0 T0 A T _ R κ v₀ O F fw hI hG hM hb hO hr ha hn
  have hT : TieIn T R κ v₀ := GlobalTheory.Div.tieIn_of_fwTie T R κ v₀ fw
  have hpb : T.pb = R.C.P.pb := GlobalTheory.PinsFixHalf.pb_eq_of_pins T R κ v₀ O hI fw.laws hO
  have hu : JUnif T R κ v₀ := (GlobalTheory.HolDict.jUnif_and_lUnif_of_tieIn h1 h2 D G Pl0 T0 A T R κ v₀ hI hM hT hpb hn).1
  exact lUnif_of_rhoGeo_equivAll fw hM hG hb hr ha (GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R κ v₀ O hI hT hpb hO) hu

end GlobalTheory.TiedUnif
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEveryEmbeddingThirdKind

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TiedUnif

theorem uniformisation_every_embedding_thirdKind : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (fw : FWTie T R.toRealDat κ v₀), ∀ (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)), R.WeakCharacterisation F → BarTie fw → (∀ i, OMPins T R.toRealDat κ v₀ O i) → RhoGeo fw O → EquivAll T R.toRealDat κ O → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.toRealDat.LUnif := by
  intro h1 h2 D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ fw O hC hb hO hr ha hn
  exact lUnif_of_pins h1 h2 T R.toRealDat κ v₀ O F.lv2 fw hC.base.lev hC.base.grp hC.base.models hb hO hr ha hn

end GlobalTheory.TiedUnif
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LUnifRealTB

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LocalUniformizerReal
theorem lUnif_of_nV_ge_of_bundle : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.LUnif := by
  intro h1 D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn
  exact GlobalTheory.TiedUnif.uniformisation_every_embedding_thirdKind h1 GlobalTheory.Mem.VolFin.finVol B.T B.Q.Rl _ B.κ B.v₀ B.fw B.O B.Q.charW B.bar B.pins B.rhoGeo B.equivAll hn
end GlobalTheory.LocalUniformizerReal
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LUnifRealTBStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lUnif_of_nV_ge : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.LUnif := by
  first | exact @_root_.GlobalTheory.LocalUniformizerReal.lUnif_of_nV_ge_of_bundle | exact _root_.GlobalTheory.LocalUniformizerReal.lUnif_of_nV_ge_of_bundle | (intros; apply _root_.GlobalTheory.LocalUniformizerReal.lUnif_of_nV_ge_of_bundle <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormMapRowThreeLevelOfCharacterisationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.oneMapRowR_of_weakCharacterisation : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (ph : Fin D.R.m → ℂ), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → R.WeakCharacterisation F → R.toRealDat.ExAt → Nonempty (FWTie T R.toRealDat κ v₀) → IoExt R.toRealDat → ∀ i, OMPins T R.toRealDat κ v₀ O i → PhaseTie T R.toRealDat κ v₀ O ph i → OneMapRowR T R.toRealDat κ v₀ O ph i := by
  first | exact @GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation | exact GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation | (intros; apply GlobalTheory.OneMapRow3.oneFormMapRow_threeLevel_of_characterisation <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfClauses

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj Formalism.L2 Formalism.L2.Rows Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowsAtRealTB

theorem rowsB_of_clauses_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.ExAt → B.Q.Rl.toRealDat.LUnif → IoExt B.Q.Rl.toRealDat → _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows B := by
  intro D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn hEx hUnif hIo
  exact ⟨hIo, fun i => GlobalTheory.T.oneMapRowR_of_weakCharacterisation D _ _ _ _ P.A3 B.T B.Q.Rl (faceT P Dcf Spf Zscf) B.κ B.v₀ B.O (phEff B.Q.Rl)
    hn B.Q.charW hEx ⟨B.fw⟩ hIo i (B.pins i) (B.phase i hUnif)⟩
end GlobalTheory.RowsAtRealTB
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBOfDecay

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowsAtRealTBClose
theorem rowsB_of_decay_alt : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (Rc : _root_.Formalism.L2.RecTAlt ex) (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)) (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc) (B : _root_.Formalism.IndefR.RealTBAlt Rc P Dcf Spf Zscf S), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → B.Q.Rl.toRealDat.ExAt → _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows B := by
  intro hDec D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn hEx
  have hUnif := _root_.GlobalTheory.T.lUnif_of_nV_ge hDec D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn
  have hIo := GlobalTheory.T.ioExt_of_weakCharacterisation_of_orthonormal_frames D _ _ _ _ P.A3 _ B.Q.Rl (faceT P Dcf Spf Zscf) B.Q.charW hEx B.Q.stdV
  exact _root_.GlobalTheory.RowsAtRealTB.rowsB_of_clauses_alt D L hT Gi Gl K Y cX ex Rc P Dcf Spf Zscf S B hn hEx hUnif hIo
end GlobalTheory.RowsAtRealTBClose
end
end
end
