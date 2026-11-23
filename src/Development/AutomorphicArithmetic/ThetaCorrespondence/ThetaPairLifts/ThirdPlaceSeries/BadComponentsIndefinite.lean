module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeOfPullbackLePowFiniteEtale
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteInvLeft
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittakerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActLevIffLevelActionOver
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AutomorphicArithmetic.LocalEmbeddings.KeepsOfGood
public import Development.AutomorphicArithmetic.LocalEmbeddings.RankCover
import Development.AutomorphicArithmetic.LocalEmbeddings.RootInCore
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoversOfLifts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalShareCountLeExp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RegularEmbeddingsCoverBadEmbeddingLocus

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadAtFromInputs

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BadIndef

theorem finiteDimensional_of_lat {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hL : L.FG)
    (hs : Submodule.span K (L : Set V) = ⊤) : FiniteDimensional K V := by
  obtain ⟨s, rfl⟩ := hL
  refine Module.finite_def.2 ⟨s, ?_⟩
  rw [← Submodule.span_span_of_tower (𝓞 K) K (s : Set V)]
  exact hs


end GlobalTheory.BadIndef
end
end
end

-- Source module: Development.AutomorphicArithmetic.LocalEmbeddings.BadRepAt

section

@[expose] public section

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.BadRep

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.BadCount
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed typeEmb grpHR grpGHR transl levelGU)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU unitri superDiag)
open GlobalTheory.LevPull (CongMod)
open Formalism.MainNotions.ArithmeticCylinders
open scoped TensorProduct

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}


set_option maxHeartbeats 2000000 in
theorem badRep_at (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) (hY : GoodCov p i Y) :
    ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g D.nd) (s : G0g D.nd →* (LevelAut (dat p i) Y.d.l₂)) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g D.nd)), IsSplit π s ∧ IsWhit D Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf D k (H k)) ∧ Pb.comap π = grpHR fr ∧ (∀ k, (H k).comap π = grpGHR fr k) ∧ (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g D.nd) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) D.ntypes.e0) : Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) := by
  refine (frame_data p i Y hY.1).elim fun fr h => h.elim fun ε h => h.elim fun iso' h => h.elim fun t h => ?_
  refine p.grpRecPin.elim fun plg h' => h'.elim fun iso h' => ?_
  have hl₂ := h.1
  have hpin := h'.2.2.2
  let c : p.P.Gp ≃* G0g D.nd := p.R.eG.trans p.cG
  let θ : LevelAut (dat p i) Y.d.l₂ →* p.P.Gp := t.toMonoidHom.comp (typeRed fr)
  let π : LevelAut (dat p i) Y.d.l₂ →* G0g D.nd := c.toMonoidHom.comp θ
  let s : G0g D.nd →* LevelAut (dat p i) Y.d.l₂ := (typeEmb hl₂ fr).comp (t.symm.toMonoidHom.comp c.symm.toMonoidHom)
  have hs : ∀ g, θ (s (c g)) = g := fun g => by
    show t (typeRed fr (typeEmb hl₂ fr (t.symm (c.symm (c g))))) = g
    rw [GlobalTheory.LevDesc.typeRed_typeEmb, MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
  have hsp : IsSplit π s := by
    refine ⟨fun g => ?_, fun g γ hγ => ?_⟩
    · show c (t (typeRed fr (typeEmb hl₂ fr (t.symm (c.symm g))))) = g
      rw [GlobalTheory.LevDesc.typeRed_typeEmb, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    · have h0 : c (t (typeRed fr γ)) = 1 := hγ
      rw [EmbeddingLike.map_eq_one_iff, EmbeddingLike.map_eq_one_iff, GlobalTheory.LevDesc.typeRed_eq_one] at h0
      exact hl₂.commute (GlobalTheory.LevDesc.typeEmb_mem hl₂ fr _) h0
  refine (whit_data p.R.toRealDat p.F.lv2 p.charW.base.grp.levels c plg iso hpin).elim fun Pb w => w.elim fun lam w =>
    w.elim fun ψ w => ?_
  have hH := fun k => half_data p.R.toRealDat c plg iso hpin ε iso' t h.2.2.2.1 k
  have hQ : ∀ γ, γ ∈ Pb.comap π ↔ θ γ ∈ (p.F.lv2.lvl false).P := fun γ => w.2.1 (θ γ)
  refine (rank_data p i Y hY.1 θ h.2.1 (fun γ hγ => (congrArg t (h.2.2.1 γ hγ)).trans (map_one t)) c s hs (Pb.comap π) hQ
    (lam.comp (π.subgroupComap Pb)) (fun γ => w.2.2 (θ γ) γ.2 _) D.ntypes.e0 h'.2.1).elim fun ρ r => r.elim fun χ r => ?_
  exact ⟨fr, π, s, ρ, χ, Pb, lam, ψ, lam.comp (π.subgroupComap Pb), fun k => (hH k).choose, hsp, w.1, fun _ => rfl,
    fun k => (hH k).choose_spec.1, Subgroup.ext fun γ => (hQ γ).trans (h.2.2.2.2 _),
    fun k => Subgroup.ext fun γ => (hH k).choose_spec.2 _, r⟩

end Point

end GlobalTheory.CovTop.BadRep
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoverTypeLatticeComparison

section

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_type_lattice_comparison_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y _ _ => ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (π : (LevelAut (dat p i) Y.d.l₂) →* G0g (Fm.D x ι).nd) (s : G0g (Fm.D x ι).nd →* (LevelAut (dat p i) Y.d.l₂)) (ρ : Representation ℂ (LevelAut (dat p i) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (χ : (LevelAut (dat p i) Y.d.l₂) →* ℂˣ) (Pb : Subgroup (G0g (Fm.D x ι).nd)) (lam : Pb →* ℂˣ) (ψ : ∀ kv : (Σ k : Fin 2, (Fm.D x ι).nd.PlG k), AddChar (ZMod ((Fm.D x ι).host.g kv.1)) ℂ) (lamb : Pb.comap π →* ℂˣ) (H : Fin 2 → Subgroup (G0g (Fm.D x ι).nd)), IsSplit π s ∧ IsWhit (Fm.D x ι) Pb lam ψ ∧ (∀ γ : Pb.comap π, lamb γ = lam ⟨π γ, γ.2⟩) ∧ (∀ k, IsHalf (Fm.D x ι) k (H k)) ∧ Pb.comap π = grpHR fr ∧ (∀ k, (H k).comap π = grpGHR fr k) ∧ (∀ (g : (LevelAut (dat p i) Y.d.l₂)) (v w : Y.V (Gk p i)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v → ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) ∧ Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb) ∧ Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) = Module.finrank ℂ (eig ρ (Pb.comap π) lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ (G0g (Fm.D x ι).nd) (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) (Fm.D x ι).ntypes.e0) : Submodule ℂ (ℂ ⊗[Y.d.c₂.F] Y.V (Gk p i))) := by
  intro _ _ _
  refine _root_.GlobalTheory.CovTop.CovSz.covers_of_lifts_alt (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 0) ?_
  intro eps Fm x hx ι p i C _ hN _ Y hY
  exact GlobalTheory.CovTop.BadRep.badRep_at p i Y hY
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BadComponentsIndefinite

section

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.BadIndef
set_option maxHeartbeats 1000000 in
theorem bad_components_indefinite_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i _ _ _ => BadAt p i := by
  intro hX hP hGD hQ hS hT hSA hGr hG hDG hSz hFD hDg hSh
  have hB := _root_.GlobalTheory.T.cover_type_lattice_comparison_alt hP hG hDG
  have hW := _root_.GlobalTheory.T.local_share_number_bound_alt hP hGr
  have hE := _root_.GlobalTheory.T.bad_embedding_locus_covered_by_regular_alt hX hP hGD hQ hS hT hSA hG hDG hSz hFD hDg hSh
  refine Formalism.MainNotions.Closed.imp (((hB.and hW).and hE).and hDG) ?_
  rintro eps Fm CH - ⟨⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩, ⟨C4, -, x4, h4⟩⟩
  refine ⟨0, le_rfl, max (max x1 x4) (max x2 x3), fun x hx hle ι p hp i hi Y hY => ?_⟩
  have l1 : x1 ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hle
  have l4 : x4 ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hle
  have l2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have l3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨ψ₀, hψ₀, hsh⟩ := h2 x hx l2 ι p hp i
  obtain ⟨fr, π, s, ρ, χ, Pb, lam, ψ, lamb, H, hsp, hwh, hlb, hhalf, hPb, hH, hρ, hrkT, hrkB⟩ :=
    h1 x hx l1 ι p hp i hi Y hY
  have hemb := fun k => h3 x hx l3 ι p hp i hi Y hY fr π ρ χ Pb lamb H hPb hH hρ k
  choose n hn1 hn2 using hemb
  have hgd := (h4 x hx l4 ι p hp i hi Y hY).1
  haveI : FiniteDimensional Y.d.c₂.F (Y.V (Gk p i)) := finiteDimensional_of_lat _ hgd.2.1 hgd.2.2
  obtain ⟨S, hSg, hbd⟩ := GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker (Fm.D x ι) _ _ π s hsp ρ Pb lam ψ hwh lamb hlb H hhalf n (3 / 2) hn1 hn2 ψ₀ hψ₀
  have hs := hsh S hSg
  have e0 : (0 : ℝ) ≤ Module.finrank ℂ (eig ρ (Pb.comap π) lamb) := Nat.cast_nonneg _
  have e1 : 0 ≤ Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) := (Real.exp_pos _).le
  have k1 := mul_le_mul_of_nonneg_right hs e0
  have k2 := mul_nonneg e1 e0
  have key : (Formalism.HN.rkK (CovTop.latBad p.R.toRealDat p.F.lv2 i) : ℝ) ≤
      3 * Real.exp (-((Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 7))) * Formalism.HN.rkK (latType p.R.toRealDat p.F.lv2 i) := by
    rw [hrkT, hrkB]
    refine hbd.trans ?_
    linarith
  exact key
end GlobalTheory.BadIndef
end
end
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

theorem _root_.GlobalTheory.T.covers_badAt_of_deep_good_size_flat_degree : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → GlobalTheory.Published.GreenCuspidal → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.ShareCondition → _root_.GlobalTheory.CovTop.CoversCondition fun _ _ _ _ p i _ _ _ => BadAt p i := by
  first | exact @_root_.GlobalTheory.BadIndef.bad_components_indefinite_alt | exact _root_.GlobalTheory.BadIndef.bad_components_indefinite_alt | (intros; apply _root_.GlobalTheory.BadIndef.bad_components_indefinite_alt <;> assumption)
end
end
end
end
