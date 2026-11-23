module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatIndLastKerRow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroMemCompletedLatticeSource
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroSourceTensorColumnProductStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionByZeroMapsCompletedHomLatticeStatement
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeIndicatorOnSplitHalfEqHalfIndicatorStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorHomSelfDualComponentsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfSourceBoxLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatHalfTargetBoxDualIndicatorStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOSourceSliceStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunOTargetSliceOrthogonalSumStatement
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroMemCompletedLatticeSourceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extendByZero_mem_completed_lattice_source : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (β : Frame p T n) (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛT : Submodule 𝒪[k] (n → k)), (∀ u : WO A T, MxAt (· = p.v) u → (u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), ψ (symplO A T u u') = 1)) → (∀ u : WO S T, MxAt (· = p.v) u → (u ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v), ψ (symplO S T u u') = 1)) → halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) = o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (GlobalTheory.FinPl.ExtZero.colFun β ζ (vecInd ΛT)) → ∀ u ∈ latO A T (LA : Set _) (LT : Set _) (· = p.v), (o.resS T).symm (u, 0) ∈ latO S T (LS : Set _) (LT : Set _) (· = p.v) := by
  first | exact @GlobalTheory.FinPl.ExtZero.extZero_mem_latO | exact GlobalTheory.FinPl.ExtZero.extZero_mem_latO | (intros; apply GlobalTheory.FinPl.ExtZero.extZero_mem_latO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroTargetTensorRowProductStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.extendByZero_target_tensor_row_product : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (Ψ : Matrix n' n k → ℂ) (b : (n → k) → ℂ), extFun β α₀ (tensRow Ψ b) = o.boxT T (extFun β α Ψ) (GlobalTheory.FinPl.ExtZero.rowFun β ζ b) := by
  exact @GlobalTheory.FinPl.ExtZero.extFun_tensRow
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroSourceSlice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem comb_extS_slice :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO A T →₀ ℂ) (f : WO S T → ℂ) (y : WO L T) (w : WO A T), comb ψ A T c (fun w' => f ((o.resS T).symm (w', y))) w = comb ψ S T (extS o T c) f ((o.resS T).symm (w, y)) := by
  intro D ψ S A L T o c f y w
  classical
  have hinj : Function.Injective (fun a : WO A T => (o.resS T).symm (a, 0)) := fun a b h => by
    simpa using h
  unfold comb extS
  rw [Finsupp.mapDomain_support_of_injective hinj, Finset.sum_image (fun a _ b _ h => hinj h),
    Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finsupp.mapDomain_apply_of_injective hinj, Pi.smul_apply, Pi.smul_apply, heisO_resS_symm]

end GlobalTheory.FinPl.ExtZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroSourceSliceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergCombination_extendByZero_source_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO A T →₀ ℂ) (f : WO S T → ℂ) (y : WO L T) (w : WO A T), comb ψ A T c (fun w' => f ((o.resS T).symm (w', y))) w = comb ψ S T (extS o T c) f ((o.resS T).symm (w, y)) := by
  first | exact @GlobalTheory.FinPl.ExtZero.comb_extS_slice | exact GlobalTheory.FinPl.ExtZero.comb_extS_slice | (intros; apply GlobalTheory.FinPl.ExtZero.comb_extS_slice <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroTargetSlice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem comb_extT_resT_symm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO T A →₀ ℂ) (f : WO T S → ℂ) (y : WO T L) (w : WO T A), comb ψ T A c (fun w' => f ((o.resT T).symm (w', y))) w = comb ψ T S (extT o T c) f ((o.resT T).symm (w, y)) := by
  intro D ψ S A L T o c f y w
  have h1 : ∀ (X Y : HSp D) (d : WO X Y →₀ ℂ) (g : WO X Y → ℂ) (x : WO X Y),
      comb ψ X Y d g x = d.sum fun u a => a * heisO ψ X Y u g x := by
    intro X Y d g x
    simp only [comb, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h1, extT, Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  exact Finsupp.sum_congr fun u _ => by rw [heisO_resT_symm]

end GlobalTheory.FinPl.ExtZero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationExtendByZeroTargetSliceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.heisenbergCombination_extendByZero_target_slice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (c : WO T A →₀ ℂ) (f : WO T S → ℂ) (y : WO T L) (w : WO T A), comb ψ T A c (fun w' => f ((o.resT T).symm (w', y))) w = comb ψ T S (extT o T c) f ((o.resT T).symm (w, y)) := by
  first | exact @GlobalTheory.FinPl.ExtZero.comb_extT_resT_symm | exact GlobalTheory.FinPl.ExtZero.comb_extT_resT_symm | (intros; apply GlobalTheory.FinPl.ExtZero.comb_extT_resT_symm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerIntertwinerSliceRestrictionPlaceMode

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem restrModel_isPlaceModel : ∀ (D : D7) {m n m' n' m'' n'' : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (BS : Mx D m n → Mx D m n → AF D.host.F) (hsS : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (BA : Mx D m' n' → Mx D m' n' → AF D.host.F) (hsA : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)) (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (e : AE D) (ΛS : AddSubgroup (Mx D m n)) (ΛA : AddSubgroup (Mx D m' n')) (h : Mx D m'' n'' → ℂ) (f₀ : Mx D m n → ℂ) (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)), IsPlaceModel ψ BS hsS e ΛS 1 f₀ T' → (∀ a F w y, hsS (r.symm (a, 0)) F (r.symm (w, y)) = hsA a (fun w' => F (r.symm (w', y))) w) → (∀ t a, BS t (r.symm (a, 0)) = BA (r t).1 a) → (∀ a, IsHalf e a → IsHalf e (r.symm (a, 0))) → (∀ a, IsHalf (cA D e) a → IsHalf (cA D e) (r.symm (a, 0))) → (∀ Φ, IsSBHalf e ΛA Φ → IsSBHalf e ΛS (fun t => Φ (r t).1 * h (r t).2)) → halfInd e ΛS = (fun t => halfInd e ΛA (r t).1 * h (r t).2) → ∀ y, IsPlaceModel ψ BA hsA e ΛA 1 (fun w => f₀ (r.symm (w, y))) (GlobalTheory.FinPl.ExtZero.restrModel r h T' y) := by
  intro D m n m' n' m'' n'' ψ BS hsS BA hsA r e ΛS ΛA h f₀ T' hT hcomp hB hhalf hhalfc hSB hInd y
  refine ⟨?_, ?_, ?_⟩
  · intro Φ hΦ x hx
    funext w
    rw [restrModel_apply]
    have hfun : (fun t => (fun t => Φ (t + x)) (r t).1 * h (r t).2) =
        fun t => (fun t => Φ (r t).1 * h (r t).2) (t + r.symm (x, 0)) := by
      funext t
      simp only [map_add (f := _), AddEquiv.apply_symm_apply, Prod.fst_add, Prod.snd_add, add_zero]
    rw [hfun, hT.trans _ (hSB Φ hΦ) _ (hhalf x hx), hcomp]
    rfl
  · intro Φ hΦ y' hy'
    funext w
    rw [restrModel_apply]
    have hfun : (fun t => (fun t => ψ (BA t y') * Φ t) (r t).1 * h (r t).2) =
        fun t => ψ (BS t (r.symm (y', 0))) * (fun t => Φ (r t).1 * h (r t).2) t := by
      funext t
      simp only [hB, mul_assoc]
    rw [hfun, hT.modul _ (hSB Φ hΦ) _ (hhalfc y' hy'), hcomp]
    rfl
  · funext w
    rw [restrModel_apply]
    have hfun : (fun t => ((1 : ℂ) • halfInd e ΛA) (r t).1 * h (r t).2) = (1 : ℂ) • halfInd e ΛS := by
      rw [hInd]; funext t; simp
    rw [hfun, hT.vac]

end GlobalTheory.FinPl.ExtZero
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchroedingerIntertwinerSliceRestrictionPlaceModeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.schroedinger_intertwiner_slice_restriction_placeModel : ∀ (D : D7) {m n m' n' m'' n'' : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (BS : Mx D m n → Mx D m n → AF D.host.F) (hsS : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ)) (BA : Mx D m' n' → Mx D m' n' → AF D.host.F) (hsA : Mx D m' n' → (Mx D m' n' → ℂ) → (Mx D m' n' → ℂ)) (r : Mx D m n ≃+ Mx D m' n' × Mx D m'' n'') (e : AE D) (ΛS : AddSubgroup (Mx D m n)) (ΛA : AddSubgroup (Mx D m' n')) (h : Mx D m'' n'' → ℂ) (f₀ : Mx D m n → ℂ) (T' : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ)), IsPlaceModel ψ BS hsS e ΛS 1 f₀ T' → (∀ a F w y, hsS (r.symm (a, 0)) F (r.symm (w, y)) = hsA a (fun w' => F (r.symm (w', y))) w) → (∀ t a, BS t (r.symm (a, 0)) = BA (r t).1 a) → (∀ a, IsHalf e a → IsHalf e (r.symm (a, 0))) → (∀ a, IsHalf (cA D e) a → IsHalf (cA D e) (r.symm (a, 0))) → (∀ Φ, IsSBHalf e ΛA Φ → IsSBHalf e ΛS (fun t => Φ (r t).1 * h (r t).2)) → halfInd e ΛS = (fun t => halfInd e ΛA (r t).1 * h (r t).2) → ∀ y, IsPlaceModel ψ BA hsA e ΛA 1 (fun w => f₀ (r.symm (w, y))) (GlobalTheory.FinPl.ExtZero.restrModel r h T' y) := by
  first | exact @GlobalTheory.FinPl.ExtZero.restrModel_isPlaceModel | exact GlobalTheory.FinPl.ExtZero.restrModel_isPlaceModel | (intros; apply GlobalTheory.FinPl.ExtZero.restrModel_isPlaceModel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCombinationExtendByZeroOrthSumLine

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer InDual)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.ExtZero

theorem ext_zero : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∀ (LA : Lat A) (LS : Lat S) (LT : Lat T) (ΛA : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC T LT → α.IsLat LA ΛA → α₀.IsLat LS (lastKer ΛA) → β.IsLat LT ΛT → (∀ (Ψ : Matrix n n' k → ℂ) (c : WO A T →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ A T LA LT (· = p.v) f₀ → Over ψ α β LA LT f₀ Ψ (comb ψ A T c f₀)) → ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α₀ β LS LT f₀ (tensCol Ψ (vecInd ΛT)) (comb ψ S T (extS o T c) f₀)) ∧ ∀ (Ψ : Matrix n' n k → ℂ) (c : WO T A →₀ ℂ), CombAt (· = p.v) c → (∀ f₀, Vac ψ T A LT LA (· = p.v) f₀ → Over ψ β α LT LA f₀ Ψ (comb ψ T A c f₀)) → ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → Over ψ β α₀ LT LS f₀ (tensRow Ψ (dualInd ΛT)) (comb ψ T S (extT o T c) f₀) := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ hψ hU S A L T o ζ hζ α α₀ β hsum LA LS LT ΛA ΛT hA hS hT hαA hα₀ hβ
  have : ΛT.IsFullLattice k := GlobalTheory.FinPl.isLattice_of_isLat_selfDual β LT hT ΛT hβ
  have sdA := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ A T LA LT hA hT (· = p.v)
  have sdS := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ S T LS LT hS hT (· = p.v)
  have sdA' := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ T A LT LA hT hA (· = p.v)
  have sdS' := GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hψ T S LT LS hT hS (· = p.v)
  have facS : halfInd p.e (latO S T (LS : Set _) (LT : Set _) (· = p.v)) =
      o.boxS T (halfInd p.e (latO A T (LA : Set _) (LT : Set _) (· = p.v))) (colFun β ζ (vecInd ΛT)) := by
    rw [← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n (n' ⊕ Fin 1) S T α₀ β LS LT hS hT hU _ _ hα₀ hβ,
      ← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n n' A T α β LA LT hA hT hU _ _ hαA hβ, latInd_lastKer,
      GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' S A L T o ζ α α₀ β hsum]
  have facT : halfInd p.e (latO T S (LT : Set _) (LS : Set _) (· = p.v)) =
      o.boxT T (halfInd p.e (latO T A (LT : Set _) (LA : Set _) (· = p.v))) (rowFun β ζ (dualInd ΛT)) := by
    rw [← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p (n' ⊕ Fin 1) n T S β α₀ LT LS hT hS hU _ _ hβ hα₀,
      ← GlobalTheory.T.homLatticeIndicator_on_split_half_eq_half_indicator D k p n' n T A β α LT LA hT hA hU _ _ hβ hαA, latInd_lastKer_row,
      GlobalTheory.T.extendByZero_target_tensor_row_product D k p n n' S A L T o ζ hζ α α₀ β hsum]
  have latS := GlobalTheory.T.extendByZero_mem_completed_lattice_source D k p n ψ S A L T o ζ β LA LS LT ΛT sdA sdS facS
  have latT := GlobalTheory.T.extension_by_zero_maps_completed_hom_lattice D k p n ψ S A L T o ζ β LA LS LT ΛT sdA' sdS' facT
  have vacS : ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → ∀ y,
      Vac ψ A T LA LT (· = p.v) (fun w => f₀ ((o.resS T).symm (w, y))) := by
    intro f₀ hf y
    refine ⟨GlobalTheory.T.isThetaFunO_source_slice D ψ S A L T o f₀ y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · funext w
      rw [← heisO_resS_symm ψ o (2 • u) f₀ w y]
      have h2 : (o.resS T).symm (2 • u, 0) = 2 • (o.resS T).symm (u, 0) := by
        rw [← map_nsmul]; simp
      rw [h2, hf.2.1 _ (latS u hu)]
    · funext w
      rw [← heisO_resS_symm ψ o u f₀ w y, hf.2.2 e' he' _ (latS u hu) (half_resS_symm o hh)]
  have vacT : ∀ f₀, Vac ψ T S LT LS (· = p.v) f₀ → ∀ y,
      Vac ψ T A LT LA (· = p.v) (fun w => f₀ ((o.resT T).symm (w, y))) := by
    intro f₀ hf y
    refine ⟨GlobalTheory.T.isThetaFunO_target_slice_orthogonal_sum D ψ S A L T o f₀ y hf.1, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · funext w
      rw [← heisO_resT_symm ψ o (2 • u) f₀ w y]
      have h2 : (o.resT T).symm (2 • u, 0) = 2 • (o.resT T).symm (u, 0) := by
        rw [← map_nsmul]; simp
      rw [h2, hf.2.1 _ (latT u hu)]
    · funext w
      rw [← heisO_resT_symm ψ o u f₀ w y, hf.2.2 e' he' _ (latT u hu) (half_resT_symm o hh)]
  refine ⟨fun Ψ c _ hyp f₀ hf₀ => ?_, fun Ψ c _ hyp f₀ hf₀ => ?_⟩
  · have hΨ : Ψ ∈ SB (Matrix n n' k) := (hyp _ (vacS f₀ hf₀ 0)).2.2.2.1
    have hΨ' : tensCol Ψ (vecInd ΛT) ∈ SB (Matrix n (n' ⊕ Fin 1) k) :=
      GlobalTheory.FinPl.Comm.tensCol_mem hΨ (GlobalTheory.FinPl.Comm.vecInd_mem ΛT)
    obtain ⟨f, hf, -⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hψ S T α₀ β LS LT hS hT f₀ hf₀).1 _ hΨ'
    refine ⟨hS, hT, hf₀, hΨ', hf.2.2.2.2.1, fun T' hT' => ?_⟩
    funext t
    obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resS T).symm q = t := ⟨_, (o.resS T).symm_apply_apply t⟩
    have hmod := GlobalTheory.T.schroedinger_intertwiner_slice_restriction_placeModel D ψ (symplO S T) (heisO ψ S T) (symplO A T) (heisO ψ A T) (o.resS T) p.e _ _
      (colFun β ζ (vecInd ΛT)) f₀ T' hT' (fun a F w y => heisO_resS_symm ψ o a F w y)
      (fun t a => symplO_resS_symm o t a) (fun a ha => half_resS_symm o ha) (fun a ha => half_resS_symm o ha)
      (GlobalTheory.T.isSchwartzBruhatHalf_source_box_lattice D k p n S A L T o ζ β LA LS LT ΛT facS) facS y
    have key := congrFun ((hyp _ (vacS f₀ hf₀ y)).2.2.2.2.2 _ hmod) w
    rw [GlobalTheory.T.heisenbergCombination_extendByZero_source_slice] at key
    rw [key, restrModel_apply, GlobalTheory.T.extendByZero_source_tensor_column_product D k p n n' S A L T o ζ α α₀ β hsum]
    rfl
  · have hΨ : Ψ ∈ SB (Matrix n' n k) := (hyp _ (vacT f₀ hf₀ 0)).2.2.2.1
    have hΨ' : tensRow Ψ (dualInd ΛT) ∈ SB (Matrix (n' ⊕ Fin 1) n k) :=
      GlobalTheory.FinPl.Comm.tensRow_mem hΨ (GlobalTheory.FinPl.Comm.dualInd_mem ΛT)
    obtain ⟨f, hf, -⟩ := (GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p (n' ⊕ Fin 1) n ψ hψ T S β α₀ LT LS hT hS f₀ hf₀).1 _ hΨ'
    refine ⟨hT, hS, hf₀, hΨ', hf.2.2.2.2.1, fun T' hT' => ?_⟩
    funext t
    obtain ⟨⟨w, y⟩, rfl⟩ : ∃ q, (o.resT T).symm q = t := ⟨_, (o.resT T).symm_apply_apply t⟩
    have hmod := GlobalTheory.T.schroedinger_intertwiner_slice_restriction_placeModel D ψ (symplO T S) (heisO ψ T S) (symplO T A) (heisO ψ T A) (o.resT T) p.e _ _
      (rowFun β ζ (dualInd ΛT)) f₀ T' hT' (fun a F w y => heisO_resT_symm ψ o a F w y)
      (fun t a => symplO_resT_symm o t a) (fun a ha => half_resT_symm o ha) (fun a ha => half_resT_symm o ha)
      (GlobalTheory.T.isSchwartzBruhatHalf_target_box_dualIndicator D k p n S A L T o ζ β LA LS LT ΛT facT) facT y
    have key := congrFun ((hyp _ (vacT f₀ hf₀ y)).2.2.2.2.2 _ hmod) w
    rw [GlobalTheory.T.heisenbergCombination_extendByZero_target_slice] at key
    rw [key, restrModel_apply, GlobalTheory.T.extendByZero_target_tensor_row_product D k p n n' S A L T o ζ hζ α α₀ β hsum]
    rfl

end GlobalTheory.FinPl.ExtZero

end
end
end
