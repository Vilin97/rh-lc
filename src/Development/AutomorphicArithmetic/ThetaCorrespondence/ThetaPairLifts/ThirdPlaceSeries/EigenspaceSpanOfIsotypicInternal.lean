module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsEigAdOfState
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionHoldsAllStages
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StableHeckeLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadWMemGoodW
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.NormNum.Parity
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemGoodLIffOfStateStatement

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHkDatAtState

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeckeDataAtState
theorem exists_hkDat_at_state_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x →
    ∀ (i : Fin (Dof x).R.m) (k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ k → k ≤ (Dof x).R.r → IsSplitPl (Dof x).host Pl →
      Pl ∉ SbD (Dof x) → ∃ α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr := by
  intro hL
  refine StepW.of_all fun K B f T w _ _ _ P x _ i k Pl _ hk hs hP => ?_
  obtain ⟨α, Rr, h, -⟩ := GlobalTheory.TwInputs.Eig.exists_hkDat (R := x.m.z.R) x.m.z.F x.m.z.pins.char.base.lev (subset_refl _)
    (GlobalTheory.TwInputs.Eig.low_SbD (Dof x)) i hs hP hk
  exact ⟨α, Rr, h⟩
end GlobalTheory.HeckeDataAtState
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHkDatAtStateStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_hkDat_at_split_place : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (i : Fin (Dof x).R.m) (k : ℕ) (Pl : PlE (Dof x).host), 1 ≤ k → k ≤ (Dof x).R.r → IsSplitPl (Dof x).host Pl → Pl ∉ SbD (Dof x) → ∃ α Rr, HkDat x.m.z.R (SbD (Dof x)) i k Pl α Rr := by
  first | exact @_root_.GlobalTheory.HeckeDataAtState.exists_hkDat_at_state_alt | exact _root_.GlobalTheory.HeckeDataAtState.exists_hkDat_at_state_alt | (intros; apply _root_.GlobalTheory.HeckeDataAtState.exists_hkDat_at_state_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenSpanInclusionInjective

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem iotaR_injective_of (R : RealDat3 D A3 Ks) (hM : R.toRealDat.IsModels) (hU : R.toRealDat.LUnif) (i : Fin D.R.m) :
    Function.Injective (iotaR R i) := by
  have hj : Function.Injective ((R.FW i).j (sg0 D A3.A)) := by
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
    by_contra hne
    exact ((hU i _).1 1 (fun _ => v) (linearIndependent_unique_iff.2 hne)).ne_zero 0 hv
  exact (hM.HW i _).1.comp hj

end Gen

end GlobalTheory.EigSpanDesc
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IotaRInjectiveStates

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.EigSpanDesc
section Gen
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Gen
theorem iotaR_injective_states_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ i : Fin (Dof x).R.m, Function.Injective (GlobalTheory.EigSpanDesc.iotaR x.m.z.R i) := by
  intro hL
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all fun K B f T w _ _ _ => ?_
  intro P x _ i
  exact iotaR_injective_of x.m.z.R x.m.z.pins.char.base.models x.m.intersectionNumber_baseChange.prim.unif i
end GlobalTheory.EigSpanDesc
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IotaRInjectiveStatesStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.iotaR_injective_at_level_a : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ i : Fin (Dof x).R.m, Function.Injective (GlobalTheory.EigSpanDesc.iotaR x.m.z.R i) := by
  first | exact @_root_.GlobalTheory.EigSpanDesc.iotaR_injective_states_alt | exact _root_.GlobalTheory.EigSpanDesc.iotaR_injective_states_alt | (intros; apply _root_.GlobalTheory.EigSpanDesc.iotaR_injective_states_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpanCOfState

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.EigSpanDesc
section Core
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
end Core
theorem spanC_of_state_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x →
    Rows.IsotInternal (Dof x).what₂ → GlobalTheory.EigRows.OccGood (Dof x) →
    ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ)
      (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) →
      LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) →
      HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' →
      ∀ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig →
        SpanC (SOf x) (SbD (Dof x)) θ hL' eig := by
  intro hL
  refine (((_root_.GlobalTheory.T.mem_goodL_iff_iotaR_mem_goodW hL).and (_root_.GlobalTheory.T.iotaR_injective_at_level_a hL)).and (_root_.GlobalTheory.T.exists_hkDat_at_split_place hL)).trans (StepW.of_all fun K B f T w _ _ h => ?_)
  obtain ⟨⟨htie, hinj⟩, hhk⟩ := h
  intro P x hLA hI hG θ hL' hθ hlv _ _ hRd eig hEig
  exact spanC_core x.m.z.R x.m.z.F x.r.Y x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) θ hL' eig hI hG
    (htie P x hLA θ hθ hlv) (hinj P x hLA) (hhk P x hLA) hRd hEig
end GlobalTheory.EigSpanDesc
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpanCOfStateStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.span_c_of_stab_c_hecke_rd_eig_ad : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → Rows.IsotInternal (Dof x).what₂ → GlobalTheory.EigRows.OccGood (Dof x) → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) → LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∀ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig → SpanC (SOf x) (SbD (Dof x)) θ hL' eig := by
  exact _root_.GlobalTheory.EigSpanDesc.spanC_of_state_alt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigenspaceSpanOfIsotypicInternal

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.RatSide
theorem eigenspace_span_of_isotypicInternal_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → (AllSt fun _ _ _ _ _ _ x => Formalism.BasicNotions.Rows.IsotInternal (Dof x).what₂) → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevel hL x → ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ) (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) → LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) → HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' → ∃ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig ∧ SpanC (SOf x) (SbD (Dof x)) θ hL' eig := by
  intro hN hIso hL
  refine (StepW.and (StepW.and (_root_.GlobalTheory.HeightCounting.RatSide.exists_eigAd_of_state_alt hL) (_root_.GlobalTheory.T.span_c_of_stab_c_hecke_rd_eig_ad hL)) (StepW.and (_root_.GlobalTheory.T.allSt_goodFTAll_of_levelA hN hL) hIso)).trans
    (StepW.of_all fun K B f T w _ _ H => ?_)
  intro P x hx θ hL' h1 h2 h3 h4 h5
  obtain ⟨eig, he⟩ := H.1.1 P x hx hL' h3 h5
  exact ⟨eig, he, H.1.2 P x hx (H.2.2 P x) (GlobalTheory.EigRows.occGood_of_all _ (H.2.1 P x hx)) θ hL' h1 h2 h3 h4 h5 eig he⟩
end GlobalTheory.HeightCounting.RatSide
end
end
end
end
