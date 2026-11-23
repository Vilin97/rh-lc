module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFirstStepFlatMapSupportAllStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliserStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLawStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlacesStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeVacuumIffPlacewiseStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForallStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapMovedCoreLatticeVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapUnipotentStabilizerTranslateScalarStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapVacuumTranslateIsVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThreeOrbitsGluedCoreAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplitStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicEqComponentAtPlaceMulOffPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicTrivialAtPlacesSubgroupAntitoneStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumFixedByLevelPairAtSelfDualPlaces
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepLinearInSecondDatum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.DoubleStep

theorem hand0_smul_snd_of_bessel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ) (c : ℂ), hand0 s₁ s₂ l vL φ Ξ₁ (c • Ξ₂) = c • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ := by
  intro D ψ σ B J B' s₁ s₂ l vL φ Ξ₁ Ξ₂ c
  funext h₁
  simp only [hand0, handFB, pairKer, contractT, thPair, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
    MeasureTheory.integral_const_mul]

end GlobalTheory.DoubleStep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselDoubleStepLinearInSecondDatumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.besselDoubleStep_linear_in_secondDatum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ) (Ξ₁ : WO B.V₀ J.W₀ → ℂ) (Ξ₂ : WO J.W₀ B'.V₀ → ℂ) (c : ℂ), hand0 s₁ s₂ l vL φ Ξ₁ (c • Ξ₂) = c • hand0 s₁ s₂ l vL φ Ξ₁ Ξ₂ := by
  first | exact @GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel | exact GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel | (intros; apply GlobalTheory.DoubleStep.hand0_smul_snd_of_bessel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlaceStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.doubleUnfoldingStep_at_glued_finite_place : ∀ D : D7, GlobalTheory.FinPl.VertexGlued D := by
  first | exact @GlobalTheory.FinPl.Vertex.vertexGlued | exact GlobalTheory.FinPl.Vertex.vertexGlued | (intros; apply GlobalTheory.FinPl.Vertex.vertexGlued <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceDoubleStepVanishTargetCoreLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.gluedPlace_doubleStep_vanish_targetCoreLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank), IsStdChar D ψ (-1) → UnrAt s₁ p.v → UnrAt s₂ p.v → ∀ (M₀ : Lat B.V₀) (M₁ : Lat J.W₀) (M : Lat B'.V₀) (α : Frame p B.A n') (α₀ : Frame p B.V₀ (n' ⊕ Fin 1)) (β : Frame p J.W₀ n) (γ : Frame p B'.A n'') (γ₀ : Frame p B'.V₀ (n'' ⊕ Fin 1)) (P : Pair k n') (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k], IsSelfDualC B.V₀ M₀ → IsSelfDualC J.W₀ M₁ → IsSelfDualC B'.V₀ M → GluedCore B M₀ q α α₀ P → β.IsLat M₁ Q.lat → IsSumFrame B'.o B'.ζ γ γ₀ → (γ₀.IsLat M (lastKer Λ) ∨ γ₀.IsLat M (lastPair q Λ).lat) → ∀ Ξ₁ Ξ₂, Vac ψ B.V₀ J.W₀ M₀ M₁ (· = p.v) Ξ₁ → Vac ψ J.W₀ B'.V₀ M₁ M (· = p.v) Ξ₂ → ∀ φ, IsRam α φ → hand0 s₁ s₂ l vL (φ P) Ξ₁ Ξ₂ = 0 := by
  intro D k _ _ _ _ p n n' n'' _ _ _ _ _ _ q ψ σ B J B' s₁ s₂ l vL hψ hs₁ hs₂ M₀ M₁ M α α₀ β γ γ₀ P Q Λ _ hM₀ hM₁ hM hG hβ hγ hγ₀ Ξ₁ Ξ₂ hΞ₁ hΞ₂ φ hφ
  obtain ⟨χ, hχ, -, -, hcond⟩ := (GlobalTheory.T.exists_splitPoint_frame_character D).2 k p |>.2 ψ hψ
  have hc := hcond hG.unit
  have hVex := GlobalTheory.T.doubleUnfoldingStep_at_glued_finite_place D k p q ψ χ hc hχ
  have hV := (Classical.choose_spec hVex).2
  have hO := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D
  have h₁ := (hO k p n (n' ⊕ Fin 1) ψ hψ B.V₀ J.W₀ α₀ β M₀ M₁ hM₀ hM₁ Ξ₁ hΞ₁).2.2 hG.unit _ _ hG.lat hβ
  have hO₂ := hO k p (n'' ⊕ Fin 1) n ψ hψ J.W₀ B'.V₀ β γ₀ M₁ M hM₁ hM Ξ₂ hΞ₂
  refine (hV n n' n'' σ B J B' s₁ s₂ l vL hs₁ hs₂ α α₀ β γ γ₀ hG.sum hγ P P Q).2 Λ M₀ M₁ M₁ M Ξ₁ Ξ₁ Ξ₂ Ξ₂ h₁ ?_ φ hφ
  exact hγ₀.elim (fun h => Or.inl (hO₂.2.2 hG.unit _ _ hβ h))
    (fun h => Or.inr (hO₂.2.2 hG.unit _ _ hβ h))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapMovedCoreLatticeVacuumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.secondFlatMap_moved_core_lattice_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ γ ∈ grpAt B.V₀ (· = v), ∃ M : Lat B.V₀, IsSelfDualC B.V₀ M ∧ Moves B.V₀ γ LW₀ M (· = v) ∧ Vac ψ J.W₀ B.V₀ LV₀ M (· = v) (flatFB s (s.om (1, B.d.emb0 γ) f)) := by
  first | exact @GlobalTheory.FinPl.movedVac | exact GlobalTheory.FinPl.movedVac | (intros; apply GlobalTheory.FinPl.movedVac <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceFrameLatticeOfMovedLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.splitPlaceFrameLattice_of_movedLattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (γ : GA D S) (L M : Lat S) (Λ : Submodule 𝒪[k] (n → k)), Moves S γ L M (· = p.v) → β.IsLatMoved γ L Λ → β.IsLat M Λ := by
  first | exact @GlobalTheory.FinPl.Frame.isLat_of_isLatMoved | exact GlobalTheory.FinPl.Frame.isLat_of_isLatMoved | (intros; apply GlobalTheory.FinPl.Frame.isLat_of_isLatMoved <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumFixedByLevelPairAtSelfDualPlacesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.vacuum_fixed_by_levelPair_at_selfDualPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (LS : Lat S) (LT : Lat T) (P : Pl D → Prop), (∀ v, P v → IsSelfDualC S LS ∧ IsSelfDualC T LT ∧ Tame D v ∧ CharUnramAt D χS v ∧ CharUnramAt D χT v) → ∀ f, Vac ψ S T LS LT P f → ∀ κ κ', InK S LS P κ → InK T LT P κ' → om (κ, κ') f = f := by
  first | exact @GlobalTheory.VacFixP.vac_fix_on | exact GlobalTheory.VacFixP.vac_fix_on | (intros; apply GlobalTheory.VacFixP.vac_fix_on <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselSecondStepFlatSupportRamified

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)

namespace GlobalTheory.FinPl

theorem suppSecond_holds : ∀ D : D7, SuppSecond D := by
  intro D k _ _ _ _ ι p n n' n'' _ _ _ _ _ _ q ψ σ B J B' s₁ s₂ l vL Λ P a b a' sh sd₂ Φ₁ Φ₂ hΦ₁ hΦ₂
  have tameP : ∀ v, P v → Tame D v := fun v hv => (sh.good v hv).tame
  refine ⟨?_, fun h₁ hh₁ => ⟨?_, ?_⟩⟩
  · exact GlobalTheory.T.vacuum_fixed_by_levelPair_at_selfDualPlaces D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ P
      (fun v hv => ⟨(sh.good v hv).sdW, sd₂, tameP v hv, (sh.unr v hv).2.1, (sh.unr v hv).2.2⟩) Φ₂ hΦ₂
  · intro h₂ hh₂
    exact GlobalTheory.T.secondFlatMap_vacuum_translate_isVacuum D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ P (fun v hv => ⟨sh.adapt v hv, (sh.unr v hv).2⟩) Φ₂ hΦ₂
      h₁ hh₁ h₂ hh₂
  · intro g hg φ hφ h₂ hne
    have key := GlobalTheory.T.placewise_to_adelicDecomposition_forall D B'.V Λ.L₂ P sd₂ (besGrp B'.d B'.o) h₂ ?_
    · exact key
    intro v hv
    obtain ⟨hv', hhv, h', hh', rfl⟩ := GlobalTheory.T.unitaryAdelic_eq_componentAtPlace_mul_offPlace D B'.V h₂ v
    refine ⟨hv', hhv, h', hh', rfl, ?_⟩
    have gd := sh.good v hv
    have ad := sh.adapt v hv
    have sdL₁ : IsSelfDualC J.W Λ.L₁ := gd.sdW

    have hΦ₂v : Vac ψ J.W B'.V Λ.L₁ Λ.L₂ (· = v) Φ₂ :=
      ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ sdL₁ sd₂ P tameP Φ₂).1.mp hΦ₂).2 v hv
    set f := s₂.om (h₁, h') Φ₂ with hfdef
    have hf : Vac ψ J.W B'.V Λ.L₁ Λ.L₂ (· = v) f :=
      (GlobalTheory.T.latticeVacuum_iff_placewise D ψ J.W B'.V s₂.χV s₂.χW s₂.om s₂.weil Λ.L₁ Λ.L₂ sdL₁ sd₂ (· = v)
        (fun w hw => hw ▸ gd.tame) Φ₂).2.1 hΦ₂v h₁ (GlobalTheory.T.unitaryAdelicTrivialAtPlacesSubgroup_antitone D J.W P (· = v) (fun w hw => hw ▸ hv) hh₁) h' hh'

    set Ξ₁ := flatBF s₁ (s₁.om (g, h₁) Φ₁) with hΞ₁def
    have hΞ₁P : Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ P Ξ₁ :=
      ((GlobalTheory.T.besselToJacobiFirstStepFlatMapSupport_all D ψ (σ + 1) B J s₁ Λ.L₀ Λ.M₀ Λ.L₁ Λ.M₁ P (fun w hw => sh.good w hw)
        (fun w hw => (sh.unr w hw).1) sdL₁ Φ₁ hΦ₁).2 g hg).2 h₁ hh₁
    have hΞ₁ : Vac ψ B.V₀ J.W₀ Λ.M₀ Λ.M₁ (· = v) Ξ₁ :=
      ((GlobalTheory.T.latticeVacuum_iff_placewise D ψ B.V₀ J.W₀ s₁.χV s₁.χW s₁.om₀ s₁.weil₀ Λ.M₀ Λ.M₁ gd.sdV₀ gd.sdW₀ P tameP Ξ₁).1.mp
        hΞ₁P).2 v hv

    have hom : s₂.om (h₁, hv' * h') Φ₂ = s₂.om (1, hv') f := by
      rw [hfdef, show ((h₁, hv' * h') : GA D J.W × GA D B'.V) = (1, hv') * (h₁, h') by simp, map_mul]
      rfl
    have hand_eq : Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g h₁ (hv' * h') =
        hand0 s₁ s₂ l vL φ Ξ₁ (flatFB s₂ (s₂.om (1, hv') f)) := by
      simp only [Chain.hand, hand0, hom, hΞ₁def]
    rw [hand_eq] at hne
    have hne' : flatFB s₂ (s₂.om (1, hv') f) ≠ 0 := by
      intro h0
      apply hne
      rw [h0, show (0 : WO J.W₀ B'.V₀ → ℂ) = (0 : ℂ) • (0 : WO J.W₀ B'.V₀ → ℂ) by simp, GlobalTheory.T.besselDoubleStep_linear_in_secondDatum, zero_smul]
    obtain ⟨nn, hnF, hnv, γ, hγ, κ, hκ, hdec, hγp⟩ :=
      (GlobalTheory.T.jacobiToBesselFlatMapSupport_proof D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ v ad (sh.unr v hv).2 (flatFB s₂)
        ((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D ψ (· = v)).2 σ J B' s₂) ((GlobalTheory.T.flatMaps_heisenbergTranslation_law D ψ (· = v)).2 σ J B' s₂) f hf).2 hv' hhv hne'
    by_cases hgl : ∃ i, v = (p i).v
    · obtain ⟨i, rfl⟩ := hgl
      rcases GlobalTheory.T.threeOrbits_gluedCore_atPlace D k (p i) n'' q σ B' Λ.M₂ (a'.α i) (a'.α₀ i) (a'.P i) ad.sdW₀ (sh.gl' i) γ hγ hγp with
        ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ | ⟨Λ₀, hΛ₀, hmov⟩
      · obtain ⟨r, hr, hrv, κ', hκ', heq⟩ :=
          GlobalTheory.T.besselUnfolding_orbit_mem_parabolic_mul_stabiliser D σ B' Λ.L₂ Λ.M₂ (p i).v ad.monoW nn hnF hnv a₀ ha₀ κ₀ hκ₀ κ hκ
        exact ⟨r, hr, hrv, κ', hκ', hdec.trans heq⟩
      · exfalso
        apply hne
        obtain ⟨M, sdM, hMov, hvacM⟩ :=
          GlobalTheory.T.secondFlatMap_moved_core_lattice_vacuum D ψ σ J B' s₂ Λ.L₁ Λ.M₁ Λ.L₂ Λ.M₂ (p i).v ad (sh.unr _ hv).2 f hf γ hγ
        have hlat : (a'.α₀ i).IsLat M (lastKer Λ₀) ∨ (a'.α₀ i).IsLat M (lastPair q Λ₀).lat := by
          rcases hmov with h | h
          · exact Or.inl (GlobalTheory.T.splitPlaceFrameLattice_of_movedLattice D k (p i) B'.V₀ (n'' ⊕ Fin 1) (a'.α₀ i) γ Λ.M₂ M _ hMov h)
          · exact Or.inr (GlobalTheory.T.splitPlaceFrameLattice_of_movedLattice D k (p i) B'.V₀ (n'' ⊕ Fin 1) (a'.α₀ i) γ Λ.M₂ M _ hMov h)
        obtain ⟨φf, hφf, hφP⟩ := hφ.2 i
        have hz := GlobalTheory.T.gluedPlace_doubleStep_vanish_targetCoreLattice D k (p i) n n' n'' q ψ σ B J B' s₁ s₂ l vL s₂.weil.std (sh.unr _ hv).1
          (sh.unr _ hv).2 Λ.M₀ Λ.M₁ M (a.α i) (a.α₀ i) (b.β i) (a'.α i) (a'.α₀ i) (a.P i) (b.Q i) Λ₀ gd.sdV₀ gd.sdW₀
          sdM (sh.gl i) (sh.mid i) (sh.gl' i).sum hlat Ξ₁ _ hΞ₁ hvacM φf hφf
        rw [hφP] at hz
        rw [hdec, GlobalTheory.T.secondFlatMap_unipotent_stabilizer_translate_scalar D ψ σ J B' s₂ Λ.L₁ Λ.L₂ (p i).v sdL₁ sd₂ gd.tame (sh.unr _ hv).2 f hf nn hnF hnv _ κ hκ,
          GlobalTheory.T.besselDoubleStep_linear_in_secondDatum, hz, smul_zero]
    · obtain ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ := GlobalTheory.T.unitNormVectors_one_orbit_selfDualLattice_split D σ B' Λ.M₂ v gd.tame ad.sdW₀
        (sh.split v hv fun i h => hgl ⟨i, h⟩) γ hγ hγp
      obtain ⟨r, hr, hrv, κ', hκ', heq⟩ := GlobalTheory.T.besselUnfolding_orbit_mem_parabolic_mul_stabiliser D σ B' Λ.L₂ Λ.M₂ v ad.monoW nn hnF hnv a₀ ha₀ κ₀ hκ₀ κ hκ
      exact ⟨r, hr, hrv, κ', hκ', hdec.trans heq⟩

end GlobalTheory.FinPl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselSecondStepFlatSupportRamifiedStatement

section

@[expose] public section

open Formalism.BasicNotions

theorem _root_.GlobalTheory.T.jacobiToBessel_second_step_flat_support_ramified : ∀ D : D7, GlobalTheory.FinPl.SuppSecond D := by
  first | exact @GlobalTheory.FinPl.suppSecond_holds | exact GlobalTheory.FinPl.suppSecond_holds | (intros; apply GlobalTheory.FinPl.suppSecond_holds <;> assumption)
end
end
