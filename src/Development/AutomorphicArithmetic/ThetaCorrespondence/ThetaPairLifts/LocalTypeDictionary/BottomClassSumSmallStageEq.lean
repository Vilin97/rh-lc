module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassSignature
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicUnitaryTopCong
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.LevelADef
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.IntegralLeaf.LeafINTFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPureTensorO
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumIntegral
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleLevelFixesVector
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerMinorMulRealOfRealInvariant
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantFirst

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotClassSumSmall

open scoped ComplexOrder


open GlobalTheory.DefiniteClassAvg in
theorem openCompact {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (hstd : X.rA'.IsStd) :
    IsOpen (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) ∧
    IsCompact (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
  have hJo : IsOpen (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ A' X.rA'.β ∅] with κ h1
    exact h1.2.1
  have hV : ∀ φ : D.host.E →+* ℂ, (A'.gram.map φ).PosDef := fun φ => by
    rw [hstd.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A' with sig := fun _ => (A'.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A' : Set (GA D A')) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  have hLc : IsCompact ((Lev.levA A' (Formalism.L2.DIV.St X.rA'.β) : Subgroup (GA D A')) : Set (GA D A')) := by
    obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact A' X.rA'.β
    refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC A').inter
      (Subgroup.isClosed_of_isOpen _ hJo)) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact hCm k hk1 hk2
  refine ⟨hJo, (hLc.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hJo) ?_⟩
  intro k hk
  exact ⟨finPart A' k, finPart_mem_levA A' hk, realPart A' k, realPart_mem A' k, finPart_mul_realPart A' k⟩


end GlobalTheory.BotClassSumSmall
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.standardLattice_doubleCosetClasses_stabilisers : ∀ {D : D7} (A' : HSp D) (r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig A'), r.Is → r.IsStd → ∀ {n : ℕ}, n = A'.rank →
    ∀ gx : GlobalTheory.NormSum.Cls D n (GlobalTheory.NormSum.intG D n) → GA D A', (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) →
      (∀ g : GA D A', ∃! x, ∃ γ ∈ GQ A', ∃ k ∈ (Formalism.L2.DIV.St r.β).comap (Lev.finE A'), g = γ * gx x * k) ∧
      ∀ x, {γ : GA D A' | γ ∈ GQ A' ∧ (gx x)⁻¹ * γ * gx x ∈ (Formalism.L2.DIV.St r.β).comap (Lev.finE A')}.ncard =
        GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D n) x.out := by
  first | exact @GlobalTheory.BotClassDict.classes_and_stabilisers | exact GlobalTheory.BotClassDict.classes_and_stabilisers | (intros; apply GlobalTheory.BotClassDict.classes_and_stabilisers <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFiniteLevelFixed

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section
namespace GlobalTheory.BotFinLevel
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter GlobalTheory.RowVacScalar Formalism.L2.DIV
open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (frG intM)
variable {D : D7}
end GlobalTheory.BotFinLevel
theorem GlobalTheory.BotFinLevel.bottom_finite_level_fixed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T), ∀ k ∈ Lev.levA A' (Formalism.L2.DIV.St X.rA'.β), X.ω' s (k, 1) (X.f' s) = X.f' s := by
  intro _ _ _ _ _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ hμ G => ?_⟩⟩
  intro W _ i j A A' WW X hX s k hk
  exact GlobalTheory.BotFinLevel.fix_of_unram hX.is s (fun v hv => GlobalTheory.BotFinLevel.unram_off G hμ s i j _ hv) hk
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottom_layer_finite_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW), IsBottomTri W i j X → ∀ (s : T), ∀ k ∈ Lev.levA A' (Formalism.L2.DIV.St X.rA'.β), X.ω' s (k, 1) (X.f' s) = X.f' s := by
  first | exact @_root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed | exact _root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed | (intros; apply _root_.GlobalTheory.BotFinLevel.bottom_finite_level_fixed <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomClassSumSmallStageEq

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.BotClassSumSmall
open scoped ComplexOrder

theorem classSum_smallStage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
          ∀ (gx : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a) → GA D A'),
            (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) → ∀ T' : Tup D P'.a P'.d P'.n,
              X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g =
                Ω₁ * ∑ᶠ x, ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ *
                  X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (gx x) := by
  intro hPr hK hM hI hB
  obtain ⟨c1, h1⟩ := _root_.GlobalTheory.T.bottom_layer_finite_level hPr hK hM hI hB
  obtain ⟨c2, h2⟩ := _root_.GlobalTheory.T.minor_kernel_real_invariant hPr hK hM hI hB
  refine ⟨max c1 c2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, h1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, h2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC0 D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  have h1 := h1 C (le_trans (le_max_left _ _) hC0) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hL G
  have h2 := h2 C (le_trans (le_max_right _ _) hC0) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hL G
  intro W hψ i j A A' WW X δ t0 hX
  obtain ⟨hJo, hJc⟩ := openCompact X hX.std'
  haveI : X.m'.IsHaarMeasure := hX.is.meas'.1
  have hJtop : X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) ≠ ⊤ := hJc.measure_lt_top.ne
  have hJ0 : X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) ≠ 0 :=
    (hJo.measure_pos X.m' ⟨1, Subgroup.one_mem _⟩).ne'
  refine ⟨((X.m' ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))).toReal : ℂ),
    by exact_mod_cast (ENNReal.toReal_pos hJ0 hJtop).ne', fun s Q P P' hP ea ed h g hg gx hgx T' => ?_⟩
  obtain ⟨hu, hcard⟩ := GlobalTheory.T.standardLattice_doubleCosetClasses_stabilisers A' X.rA' hX.is.rigA' hX.std' ea gx hgx
  haveI : Finite (GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a)) := (GlobalTheory.NormSum.cls_finite_card_le D P'.a).1
  letI : Fintype (GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a)) := Fintype.ofFinite _
  have hfin : ∀ x, {γ : GA D A' | γ ∈ GQ A' ∧
      (gx x)⁻¹ * γ * gx x ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))}.Finite := fun x => by
    have h1 := GlobalTheory.InnerClassSum.finite_stab_of_measure X.m' (GQ A') _ hX.is.meas'.2 hJ0 hJtop (gx x)
    have him : {γ : GA D A' | γ ∈ GQ A' ∧
        (gx x)⁻¹ * γ * gx x ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))} =
        Subtype.val '' {γ : GQ A' | (gx x)⁻¹ * (γ : GA D A') * gx x ∈
          ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A'))} := by
      ext γ
      simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
      exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
    rw [him]
    exact h1.image _
  have hl := GlobalTheory.SqTower.Normal.ker'_left hX.is s (GlobalTheory.BotFormula.minorF ea ed T') g
  have hr : ∀ k ∈ ((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')), ∀ x,
      X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (x * k) = X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g x := by
    rw [GlobalTheory.Mass.Levels.comap_finE]
    refine GlobalTheory.DefiniteClassSum.invariant_sup ?_ ?_
    · intro k hk x
      obtain ⟨hk1, -⟩ := Lev.mem_levA.1 hk
      have hW : IsWeilDatumO W.ψ A' WW _ _ (X.ω' s) := hX.is.weil' s
      have hf' : IsThetaFunO W.ψ A' WW (X.f' s) :=
        GlobalTheory.GalLift.Vec.theta_of_thetaAt hX.is.isVac.1 hX.is.isVac.2.inf (hX.is.snd s) hX.is.isVac'.2.theta
      show X.ω' s (x * k, g) _ 0 = X.ω' s (x, g) _ 0
      have e : ((x * k, g) : GA D A' × GA D WW) = (x, g) * (k, 1) := by simp
      rw [e, map_mul, Module.End.mul_apply, GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ A' WW _ _ _ hW W.θ hX.is.isVac'.2.inf k hk1 1
        (GfC WW).one_mem _ _ _ _ _ _ hf', h1 W hψ i j A A' WW X hX s k hk]
    · intro k hk x
      exact h2 W hψ i j A A' WW X δ t0 hX s Q P P' hP ea ed T' g k hk x
  obtain ⟨-, -, heq⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset (GA D A') X.m' (GQ A') _ X.fd' hX.is.meas'.2 hJo hJtop
    _ gx hu hfin _ hl hr
  rw [Tri.I', heq, finsum_eq_sum_of_fintype]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcard x]
end GlobalTheory.BotClassSumSmall
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottom_classSum_smallStage_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
          ∀ (gx : GlobalTheory.NormSum.Cls D P'.a (GlobalTheory.NormSum.intG D P'.a) → GA D A'),
            (∀ x, GlobalTheory.BotFormula.IsFinPt A' (gx x) x.out) → ∀ T' : Tup D P'.a P'.d P'.n,
              X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g =
                Ω₁ * ∑ᶠ x, ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P'.a) x.out : ℂ))⁻¹ *
                  X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g (gx x) := by
  first | exact @_root_.GlobalTheory.BotClassSumSmall.classSum_smallStage | exact _root_.GlobalTheory.BotClassSumSmall.classSum_smallStage | (intros; apply _root_.GlobalTheory.BotClassSumSmall.classSum_smallStage <;> assumption)
end
end
end
