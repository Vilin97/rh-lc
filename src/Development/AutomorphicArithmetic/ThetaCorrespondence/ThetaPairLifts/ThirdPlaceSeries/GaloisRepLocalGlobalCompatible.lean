module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocComp
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCharLab
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectors
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTameInflationCharacterOfPadicIsoStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfBlockTypeVectorPadicIsoStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntertwiningFunctional
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicPartSpannedBySplitPlaceLocalComponent
import Mathlib.Tactic.TypeStar
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockEig
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreLastStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalLanglandsSplitQp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectorsStatement

section

@[expose] public section

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

theorem _root_.GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin (r + t)) F) V) (u : V), u ∈ fixK1 (ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) → ∀ (h : GL (Fin r) (ZMod g)) (h' : GL (Fin (r + t)) F), GlobalTheory.PendOf.IsLiftN h h' → ρ h' u = ρ (Matrix.GeneralLinearGroup.map e.toRingHom (lift g (r + t) (blk r t (r + t) h 1))) u := by
  first | exact @GlobalTheory.SerSys.BlockLift.blockLift_act | exact GlobalTheory.SerSys.BlockLift.blockLift_act | (intros; apply GlobalTheory.SerSys.BlockLift.blockLift_act <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleSmoothPullbackPadicRingIso

section

@[expose] public section

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

namespace GlobalTheory.SerSys

theorem continuous_glMap {g : ℕ} [Fact g.Prime] {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map he
  · have : (fun x : GL (Fin n) ℚ_[g] => ((Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom x)⁻¹ : GL (Fin n) F).val) =
        fun x => (x⁻¹).val.map e := by
      funext x; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map he

theorem irrSm_pullback (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F) (he : Continuous e) (n : ℕ)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)) :
    IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  set φ := Matrix.GeneralLinearGroup.map (n := Fin n) e.toRingHom with hφ
  have hsurj : Function.Surjective φ := fun y =>
    ⟨Matrix.GeneralLinearGroup.map (n := Fin n) e.symm.toRingHom y, by
      ext i j; simp [hφ]⟩
  refine ⟨⟨GlobalTheory.SmGL.nontrivial_of_irreducible σ.irr, fun W hW => ?_⟩, fun v => ?_⟩
  · have hW' : ∀ y, ∀ v ∈ W, σ.ρ y v ∈ W := fun y v hv => by
      obtain ⟨x, rfl⟩ := hsurj y
      exact hW x v hv
    haveI : IsSimpleOrder (Subrepresentation σ.ρ) := σ.irr
    let S : Subrepresentation σ.ρ := ⟨W, fun y v hv => hW' y v hv⟩
    rcases eq_bot_or_eq_top S with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  · exact (σ.smooth v).preimage (continuous_glMap e he n)

end GlobalTheory.SerSys
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleSmoothPullbackPadicRingIsoStatement

section

@[expose] public section

open GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys

theorem _root_.GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso : ∀ (g : ℕ) [Fact g.Prime] (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (e : ℚ_[g] ≃+* F), Continuous e → ∀ (n : ℕ) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) F)), IrrSm (Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) : QRep g n) := by
  first | exact @GlobalTheory.SerSys.irrSm_pullback | exact GlobalTheory.SerSys.irrSm_pullback | (intros; apply GlobalTheory.SerSys.irrSm_pullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicLocalComponentFixed

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SepLoc

theorem exists_sep {K F V : Type*} [AddCommGroup F] [Module ℂ F] [AddCommGroup V] [Module ℂ V]
    (r : K → F →ₗ[ℂ] F) (ρ : K → V →ₗ[ℂ] V)
    (hirr : ∀ W : Submodule ℂ V, (∀ k, ∀ v ∈ W, ρ k v ∈ W) → W = ⊥ ∨ W = ⊤)
    (P : (V →ₗ[ℂ] F) → Prop) (hP : ∀ T, P T → ∀ k v, T (ρ k v) = r k (T v))
    (f : F) (hf : f ∈ ⨆ (T : V →ₗ[ℂ] F) (_ : P T), LinearMap.range T) (hf0 : f ≠ 0) :
    ∃ φ : F →ₗ[ℂ] V, φ f ≠ 0 ∧ ∀ k, ∀ f' ∈ ⨆ (T : V →ₗ[ℂ] F) (_ : P T), LinearMap.range T,
      φ (r k f') = ρ k (φ f') := by
  first
  | exact @_root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional
  | exact _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional
  | (apply _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntertwiningFunctional.exists_intertwining_functional ..)

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] σ.V, φ f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f' ∈ NG.isoTyp a.ρ S, φ (NG.rt L n x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (φ f') := by
  intro L _ _ _ n a S hS s σ hloc c hc hcL f hf hf0
  have hle := GlobalTheory.SpanLoc.main L n a S hS s σ hloc c hc hcL
  have hirr : ∀ W : Submodule ℂ σ.V, (∀ k : {x : GAf L n // TrivOutside {s.v} x}, ∀ v ∈ W,
      σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n k.1)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let R : Subrepresentation σ.ρ := ⟨W, fun g v hv => by
      obtain ⟨x, hx, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq n s
        (Matrix.GeneralLinearGroup.map c.symm.toRingHom g)
      have hg : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) = g := by
        rw [hxe]; ext i j; simp
      have := hW ⟨x, hx⟩ v hv
      rwa [hg] at this⟩
    haveI := σ.irr
    rcases eq_bot_or_eq_top R with h | h
    · left; exact congrArg Subrepresentation.toSubmodule h
    · right; exact congrArg Subrepresentation.toSubmodule h
  obtain ⟨φ, hφf, hφ⟩ := exists_sep (K := {x : GAf L n // TrivOutside {s.v} x}) (fun k => NG.rt L n k.1)
    (fun k => σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n k.1))) hirr
    (fun (T : σ.V →ₗ[ℂ] (GAf L n → a.W)) => (∀ v, T v ∈ NG.AFall L n a.ρ) ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ v,
      T (σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) v) = NG.rt L n x (T v))
    (fun T hT k v => hT.2 k.1 k.2 v) f (hle hf) hf0
  exact ⟨φ, hφf, fun x hx f' hf' => hφ ⟨x, hx⟩ f' (hle hf')⟩

end GlobalTheory.SepLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicLocalComponentFixedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT Formalism.L2.Host NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isotypic_local_component_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), GlobalTheory.HeightCounting.IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → ∃ φ : (GAf L n → a.W) →ₗ[ℂ] σ.V, φ f ≠ 0 ∧ ∀ x : GAf L n, TrivOutside {s.v} x → ∀ f' ∈ NG.isoTyp a.ρ S, φ (NG.rt L n x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) (φ f') := by
  first | exact @GlobalTheory.SepLoc.main | exact GlobalTheory.SepLoc.main | (intros; apply GlobalTheory.SepLoc.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCompatibilityOfClassMaps

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host

namespace GlobalTheory.LocCompTy

open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (h : GAf L n) {f : GAf L n → a.W}
    (hf : f ∈ NG.isoTyp a.ρ S) : NG.rt L n h f ∈ NG.isoTyp a.ρ S := by
  have : NG.isoTyp a.ρ S ≤ (NG.isoTyp a.ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun S' hS' => ?_
    intro y hy
    exact le_sSup hS' (hS'.1.1.stable h y hy)
  exact this hf



end GlobalTheory.LocCompTy
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepLocalGlobalCompatible

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host
namespace GlobalTheory.LocCompTy
open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

theorem localGlobal_compatible_at_place_alt (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (hCen : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (w : PlE D.host)
    (hw : w = D.naut.plGw k v) (e : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E) (he : Continuous e)
    (rcw : ∀ n, QRep (D.host.g k) n → D.naut.LP w)
    (hrc : ∀ n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E))) (π : QRep (D.host.g k) n),
      Nonempty (π ≅ Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) →
      P.T.e w (rcw n π) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)) :
    ∃ (μ : ℚ_[D.host.g k]ˣ →* ℂˣ) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ), TamePart μ χ ∧
      D.naut.locG (D.naut.muC i) w = rcw 1 (Rep.of (Model.detRep 1 μ)) ∧
      ∀ Q : D.naut.AV i, ∃ π : QRep (D.host.g k) D.R.nV, IrrSm π ∧ D.naut.locV i Q w = rcw D.R.nV π ∧
        ActsThrough π D.R.r D.R.t χ (D.naut.typeV i Q)
          fun a => D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) := by
  classical
  have hjr := D.nd.j_range i
  let j0 : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj0 : j0.1 + 1 = D.nd.j i := by simp only [j0]; omega
  have hsp : IsSplitPl D.host w := hw ▸ GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
  obtain ⟨s, hs⟩ := GlobalTheory.TypeBlockPf.splitAt D _ hsp
  subst hs
  have htame : GlobalTheory.SplitWeil.IsTame ((P.tp.tup (D.nd.mu i) j0).loc s.w) :=
    GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j0).tame _) (P.tp.xi_tame _ _))
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_tameInflationCharacter_of_padic_iso _ _ e he _ htame
  refine ⟨_, χ, hχ, _root_.GlobalTheory.T.local_langlands_split_qp_alt_alt hPr hL D P i j0 hj0 k s.w e rcw hrc, fun Q => ?_⟩
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i Q) s
  have hσ' : IsLocS (n := D.R.nV) (P.H.av.S i Q) s σ := hσ
  refine ⟨Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)), GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso _ _ e he _ σ, ?_, ?_⟩
  · apply (P.T.e s.w).injective
    rw [hrc _ σ _ ⟨CategoryTheory.Iso.refl _⟩, D.nbc.embAV_loc, P.H.emb]
    exact P.au _ _ _ _ s _ hσ'
  obtain ⟨c, T, hc, hci, -, -, -⟩ := hσ
  set ξ := (P.tp.tup (D.nd.mu i) j0).loc s.w with hξ
  have hT : ∀ F, F ∈ D.naut.typeV i Q ↔
      (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := fun F => by
    rw [P.H.av.typeV]; exact Submodule.mem_comap
  let J := {φ : (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) →ₗ[ℂ] σ.V // ∀ x, TrivOutside {s.v} x →
    ∀ f' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q),
      φ (NG.rt D.host.E D.R.nV x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) (φ f')}
  let ι : D.naut.typeV i Q →ₗ[ℂ] (J → σ.V) :=
    LinearMap.pi fun φ => φ.1.comp ((P.M.loc i).real.comp (D.naut.typeV i Q).subtype)
  have hpar : ∀ (φ : J) (F : D.naut.typeV i Q),
      IsParVec (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t χ (φ.1 ((P.M.loc i).real F)) := by
    intro φ F
    refine GlobalTheory.T.isParahoricTypeVector_of_blockTypeVector_padic_iso _ _ e he ξ χ hχ D.R.r D.R.t σ.V σ.ρ _ ?_
    refine GlobalTheory.BlockType.isBlockVec_of (r := D.R.r) (t := D.R.t) ξ σ.ρ _ fun h hh => ?_
    obtain ⟨x, hx, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
    have hmap : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) = h := by
      rw [hxe]; exact Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
    have hF := (hT F).1 F.2
    have hh2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈
        GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := by rw [hmap]; exact hh
    have h3 := φ.2 x hx _ hF
    rw [_root_.GlobalTheory.LocCompTy.blockEig_alt hL D P i Q k v j0 hj0 s hw c hc hci F x hx hh2, map_smul] at h3
    rw [← hmap]; exact h3.symm
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro F hF
    by_contra hne
    have h1 : (P.M.loc i).real F ≠ 0 := fun h0 =>
      hne (Subtype.ext ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)))
    obtain ⟨φ, hφ, hφe⟩ := GlobalTheory.T.isotypic_local_component_fixed D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s σ hσ' c hc hci _
      ((hT F).1 F.2) h1
    exact hφ (congrFun (LinearMap.mem_ker.1 hF) ⟨φ, hφe⟩)
  refine ⟨J, ι, hinj, fun F φ => hpar φ F, fun a ha F => ?_⟩
  have hzc : ∀ b, a * b = b * a := fun b => (Subalgebra.mem_center_iff.1 ha b).symm
  have hcz := GlobalTheory.SeriesSupportTest.atPlace_central D k v a hzc
  obtain ⟨L, hLift, hCL⟩ := hCen i
  have e0 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) =
      actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) := by
    rw [NTypes.onMt, dite_eq_left hcz]; exact hCL ⟨_, hcz⟩ F
  let g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd := fun h =>
    Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h
  have hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) =
      ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) := by
    unfold actSum Formalism.MainNotions.ArithmeticCylinders.atPlace
    rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index
      (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧
      IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧
      NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := fun h =>
    _root_.GlobalTheory.T.lift_through_completion_iso_alt hL D P i Q k v s hw c hc hci L hLift F F.2 h (g h) (by simp [g])
      (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])
  choose xs hxs using hg
  have hF := (hT F).1 F.2
  have e1 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) =
      ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F) := by
    rw [e0, hsum]; exact Finset.sum_congr rfl fun h _ => by rw [(hxs h).2.2]
  have hmem : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F ∈ D.naut.typeV i Q := by
    rw [hT, e1]
    exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (rt_mem_isoTyp _ _ _ hF)
  refine ⟨hmem, fun φ => ?_⟩
  have hu := (hpar φ F).1
  change φ.1 ((P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F)) =
    actTop (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t a (φ.1 ((P.M.loc i).real F))

  rw [e1, map_sum, actTop, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, φ.2 _ (hxs h).1 _ hF, LinearMap.smul_apply, MonoidHom.comp_apply]
  congr 1
  exact GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors _ _ e he D.R.r D.R.t σ.V σ.ρ _ hu h _ (hxs h).2.1
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL P.T I rc → (∀ k v, _root_.GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → _root_.GlobalTheory.SerSys.LocalCompatibility D rc := by
  intro hPr hL D P I rc hRc hCM hCen
  exact ⟨hCM, fun i k v => _root_.GlobalTheory.LocCompTy.localGlobal_compatible_at_place_alt hPr hL D P hCen i k v _ rfl (I.i k v) (I.cont k v) (rc k v)
    fun n σ π h => hRc k v n σ π h⟩
end GlobalTheory.LocCompTy
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.locComp_of_isRc_of_classMap_of_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL P.T I rc → (∀ k v, _root_.GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → _root_.GlobalTheory.SerSys.LocalCompatibility D rc := by
  first | exact @_root_.GlobalTheory.LocCompTy.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LocCompTy.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LocCompTy.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end
