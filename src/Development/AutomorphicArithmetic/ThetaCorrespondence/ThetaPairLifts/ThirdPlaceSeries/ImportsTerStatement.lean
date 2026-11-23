module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanLevelVolumeMulRelIndexStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousLocHom
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletioStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProdStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsFurtherStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InKMemLevSphStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemLevSph
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSph
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesInjectiveStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StabOrd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOneComb
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
public import Formalism.LocalRingCardinality.PosOfIsomEmb
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevSphBTCompactOpen

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.TopVol
theorem levSph_bT_compact_open_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ≤ GfC _ ∧ IsCompact (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) ∧ IsOpen (((_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT).subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _
  have hx : a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := ha.top.2.1
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA (I.rec7 l Z).sp.cm.sig (I.rec7 l Z).sp.X'.gram
  have hmem : ∀ h, h ∈ _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ↔
      a.g.bT⁻¹ * h * a.g.bT ∈ Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W) := fun h => _root_.GlobalTheory.TopVol.mem_level_sphere_iff_conj_mem_levS h
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    have h1 : a.g.bT⁻¹ * h * a.g.bT ∈ GfC (I.rec7 l Z).sp.X' := ((hmem h).1 hh).1
    have h2 : h = a.g.bT * (a.g.bT⁻¹ * h * a.g.bT) * a.g.bT⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hx h1) (inv_mem hx)
  · have he : (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) =
        (fun k => a.g.bT * k * a.g.bT⁻¹) '' (Formalism.IndefR.Lev.levG _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W) : Set _) := by
      ext h
      constructor
      · intro hh
        exact ⟨_, (hmem h).1 hh, by group⟩
      · rintro ⟨k, hk, rfl⟩
        refine (hmem _).2 ?_
        have : a.g.bT⁻¹ * (a.g.bT * k * a.g.bT⁻¹) * a.g.bT = k := by group
        rw [this]; exact hk
    rw [he]
    exact (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _).image (by fun_prop)
  · have ho := GlobalTheory.ParahoricCompact.isOpen_comap_lev _ (_root_.GlobalTheory.Fam.pk_z W).βX (_root_.GlobalTheory.TopVol.datSph_alt W)
    have hc : Continuous fun k : GfC (I.rec7 l Z).sp.X' => a.g.bT⁻¹ * (k : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') * a.g.bT := by
      fun_prop
    convert ho.preimage hc using 1
    ext k
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    rw [hmem]
    constructor
    · intro hk; exact hk.2
    · intro hk
      exact ⟨(GfC (I.rec7 l Z).sp.X').mul_mem ((GfC (I.rec7 l Z).sp.X').mul_mem ((GfC (I.rec7 l Z).sp.X').inv_mem hx) k.2) hx, hk⟩
end GlobalTheory.TopVol
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevSphBTCompactOpenStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.true_geometry_level_spherical_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT ≤ GfC _ ∧ IsCompact (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) ∧ IsOpen (((_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT).subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) := by
  first | exact @_root_.GlobalTheory.TopVol.levSph_bT_compact_open_alt | exact _root_.GlobalTheory.TopVol.levSph_bT_compact_open_alt | (intros; apply _root_.GlobalTheory.TopVol.levSph_bT_compact_open_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspaceProperty

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.TopVol

theorem volLev_ne_zero_of_isCompact {D : D7} (V : HSp D) (hK : IsCompact (GinfC V : Set (GA D V))) (v : GlobalTheory.Unf.Vol V)
    (U : Subgroup (GA D V)) (hle : U ≤ GfC V) (hc : IsCompact (U : Set (GA D V)))
    (ho : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V))) : GlobalTheory.SeeSaw.volLev v U ≠ 0 := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.1
  haveI := hT.2.1
  haveI := hT.2.2.1
  haveI := hT.2.2.2.1
  haveI := hT.2.2.2.2.1
  haveI := v.haar
  haveI : (GinfC V).Normal := inferInstanceAs ((finHom V).ker.Normal)
  let K : Subgroup (GA D V) := GinfC V ⊔ U
  have hKset : (K : Set (GA D V)) = {g | ∃ k ∈ GinfC V, ∃ κ ∈ U, g = k * κ} := by
    show ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V)) = _
    rw [Subgroup.normal_mul]
    ext g
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
    · rintro ⟨k, hk, κ, hκ, rfl⟩
      exact ⟨k, hk, κ, hκ, rfl⟩
  have hvol : GlobalTheory.SeeSaw.volLev v U = (v.μ K).toReal := by
    unfold GlobalTheory.SeeSaw.volLev
    rw [← hKset]
  have hKc : IsCompact (K : Set (GA D V)) := by
    show IsCompact ((GinfC V ⊔ U : Subgroup (GA D V)) : Set (GA D V))
    rw [Subgroup.normal_mul]
    exact hK.mul hc
  have hKo : IsOpen (K : Set (GA D V)) := by
    have ho' : IsOpen (((U.subgroupOf (GfC V)).comap (GlobalTheory.AutMult.toFin V) : Subgroup (GA D V)) : Set (GA D V)) :=
      ho.preimage (GlobalTheory.AutMult.continuous_toFin V)
    refine Subgroup.isOpen_mono (fun g hg => ?_) ho'
    show g ∈ (K : Set (GA D V))
    rw [hKset]
    exact ⟨GlobalTheory.AutMult.toInf V g, (GlobalTheory.AutMult.toInf V g).2, GlobalTheory.AutMult.toFin V g,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_comap.mp hg), (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  have hKfin : v.μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < v.μ K := hKo.measure_pos v.μ ⟨1, K.one_mem⟩
  rw [hvol]
  exact (ENNReal.toReal_pos hKpos.ne' hKfin).ne'

end GlobalTheory.TopVol
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VolLevTopNeZero

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
namespace GlobalTheory.TopVol
theorem volLev_top_ne_zero_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ U : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), U ≤ GfC _ → IsCompact (U : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) → volLev a.g.volT U ≠ 0 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ U hle hc ho
  exact volLev_ne_zero_of_isCompact _
    (Formalism.IndefR.Eqv.isCompact_GinfC (I.rec7 l Z).sp.X'_sig fun τ => Or.inl ((I.rec7 l Z).X'_posDef τ)) _ U hle hc ho
end GlobalTheory.TopVol
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VolLevTopNeZeroStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.true_geometry_subspace_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ U : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), U ≤ GfC _ → IsCompact (U : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) → volLev a.g.volT U ≠ 0 := by
  first | exact @_root_.GlobalTheory.TopVol.volLev_top_ne_zero_alt | exact _root_.GlobalTheory.TopVol.volLev_top_ne_zero_alt | (intros; apply _root_.GlobalTheory.TopVol.volLev_top_ne_zero_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTer

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl
noncomputable section
theorem GlobalTheory.TopVol.main_alt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ VT : ℂ, VT ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.VolT VT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT
  obtain ⟨hle, hc, ho⟩ := _root_.GlobalTheory.T.true_geometry_level_spherical_alt W hW u a ha haT
  have hv := _root_.GlobalTheory.T.true_geometry_subspace_property_alt W hW u a ha haT _ hle hc ho
  refine ⟨(volLev a.g.volT (_root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT) : ℂ), Complex.ofReal_ne_zero.2 hv, fun t J hJ => ?_⟩
  have hA := _root_.GlobalTheory.T.true_geometry_twist_chain_identity_alt W hW u a ha haT t J hJ
  have hK := _root_.GlobalTheory.T.mem_levSph_of_inK_of_quadraticExtensionData W hW u a ha haT t J hJ
  have hM := _root_.GlobalTheory.T.true_geometry_twist_chain_relation_alt W hW u a ha haT t J hJ
  have hinj := _root_.GlobalTheory.T.injective_q_v_of_reads W hW u a ha haT t J hJ
  set S := (I.rec7 l Z).sp.X'
  set U := _root_.GlobalTheory.TopVol.sphericalLevelSubgroup W a.g.bT
  set U' := _root_.GlobalTheory.TopVol.twistedLevelSubgroup W a.g.bT t
  let Jf : (i : Fin J.r) → Subgroup (GL _ (J.G i).k) := fun i => ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).levTop.J
  let φ : GA (I.rec7 l Z) S →* ((i : Fin J.r) → GL _ (J.G i).k) :=
    MonoidHom.pi fun i => GlobalTheory.LevIdx.locHom (J.G i).q S (J.G i).FT
  have hφi : ∀ g i, φ g i = GlobalTheory.LevIdx.locHom (J.G i).q S (J.G i).FT g := fun _ _ => rfl
  have hU'' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ Jf i := by
    intro g
    rw [hA g]
    refine and_congr_right fun _ => forall_congr' fun i => ?_
    refine ⟨fun h => h _ ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl), fun h x hx => ?_⟩
    rw [(GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 hx]; exact h
  have hle' : U' ≤ U := fun g hg => ((hU'' g).1 hg).1
  have hidx : U'.relIndex U = ∏ i, (Jf i).relIndex (GlobalTheory.SplitWeil.KO (J.G i).k _) := by
    refine GlobalTheory.T.relIndex_eq_prod_relIndex_of_surjective_pi φ U U' (fun i => GlobalTheory.SplitWeil.KO (J.G i).k _) Jf (fun i => (J.E i).leT) ?_ ?_ hU''
    · intro g hg i
      exact GlobalTheory.T.mem_integralGL_split_place_of_carries_latticeCompletion (J.G i).q S (J.G i).FT a.v.NT _ ⟨i, rfl⟩ (J.G i).latT g (hM g hg) _
        ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
    · intro x hx
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_selfDual_stabilizer_with_prescribed_splitPlace_matrices S a.v.NT ha.vis.sdT (fun i => (J.G i).k) (fun i => (J.G i).q) _
        (fun i => (J.G i).FT) hinj (fun i => (J.G i).latT) x hx
      refine ⟨g, hK g hg, funext fun i => ?_⟩
      rw [hφi]; exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgx i)).symm
  have hU'o : IsOpen ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) := by
    have e : ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) =
        ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) ∩
          ⋂ i, (fun g : GfC S => GlobalTheory.LevIdx.locHom (J.G i).q S (J.G i).FT g.1) ⁻¹' (Jf i : Set (GL _ (J.G i).k)) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rw [hU'']
      rfl
    rw [e]
    exact ho.inter (isOpen_iInter_of_finite fun i =>
      ((J.E i).openT).preimage ((GlobalTheory.LevIdx.continuous_locHom (J.G i).q S (J.G i).FT).comp continuous_subtype_val))
  have hvol := GlobalTheory.T.archimedeanLevelVolume_mul_relIndex (I.rec7 l Z) S a.g.volT U' U hle' hle hc hU'o
  refine ⟨U', fun h => _root_.GlobalTheory.TopVol.mem_level_twist_iff_conj_mem_levS_datXP h, fun β => ?_⟩
  have hw : ∀ i, (J.E i).wt B.R.m (β i) = (((Jf i).relIndex (GlobalTheory.SplitWeil.KO (J.G i).k _) : ℕ) : ℂ) := by
    intro i
    have key : ∀ j (e : (J.G i).s + 1 + 1 = j) (y : (J.E i).Ch j), (J.E i).wt j y = ((J.E i).idx j : ℂ) := by
      rintro j rfl y; exact (J.E i).wt_top y
    have e2 : (J.E i).wt B.R.m (β i) = ((J.E i).idx B.R.m : ℂ) := key _ (J.G i).hs (β i)
    have e3 : (J.E i).idx B.R.m = (J.E i).idx ((J.G i).s + 1 + 1) := congrArg (J.E i).idx (J.G i).hs.symm
    rw [e2, e3, (J.E i).idx_top]
  rw [← hvol, _root_.GlobalTheory.Fam.QuadraticExtensionData.wt]
  simp only [hw]
  rw [hidx]
  push_cast
  ring
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_volume_constant_of_true_geometry : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∃ VT : ℂ, VT ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → J.VolT VT := by
  first | exact @_root_.GlobalTheory.TopVol.main_alt_alt | exact _root_.GlobalTheory.TopVol.main_alt_alt | (intros; apply _root_.GlobalTheory.TopVol.main_alt_alt <;> assumption)
end
end
end
