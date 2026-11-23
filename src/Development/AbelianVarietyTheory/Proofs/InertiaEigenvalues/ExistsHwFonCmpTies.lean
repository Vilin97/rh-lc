module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicKernelTiltInvariantsFaithfulStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiGamPowNeOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCoeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResEqOneIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRangeMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichPow
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticesExistAllLayersOfBhattScholzeStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalWachFunctor

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
namespace GlobalTheory.HWL.Assembly

theorem exists_wach (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : LocTied l P AI)
    (hF : FaithH AI) (hW : WachEx AI) :
    ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by
  obtain ⟨ht, hπ, -⟩ := GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI hT
  refine exists_of_layers P AI (fun K s LL g => ?_) ht hπ
  obtain ⟨Γ⟩ := GlobalTheory.HWL.GroupLayer.nonempty_gamS l P K s LL g
  obtain ⟨R⟩ := GlobalTheory.HWL.Ser.nonempty_wSer l P K s LL g Γ
  obtain ⟨I, hI⟩ := GlobalTheory.HWL.IoLayer.main l P AI K s LL g Γ R
  obtain ⟨E⟩ := GlobalTheory.HWL.EtMod.nonempty_wEt l P AI K s LL g Γ R I hI (GlobalTheory.EtaleBasis.exists_etBasis l P AI hF K s LL g Γ R I hI)
  obtain ⟨Mo⟩ := hW K s LL g Γ R I hI E
  obtain ⟨Cl⟩ := GlobalTheory.HerrClassMaps.exists_classMaps l P AI K s LL g Γ R I hI E
  obtain ⟨Cm⟩ := GlobalTheory.HWL.Cmp.nonempty_cmpS l P AI hT K s LL g Γ R I hI E Mo
  exact ⟨⟨Γ, R, I, hI, E, Mo, Cl, Cm⟩⟩

end GlobalTheory.HWL.Assembly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalWachFunctorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.exists_local_wach_functor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → FaithH AI → WachEx AI → ∃ H : LocHW l P, ∃ F : LocFon l P AI H, Nonempty (LocCmpT l P AI H F) := by
  first | exact @GlobalTheory.HWL.Assembly.exists_wach | exact GlobalTheory.HWL.Assembly.exists_wach | (intros; apply GlobalTheory.HWL.Assembly.exists_wach <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwOfFonOfCmpOf

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL

theorem exists_hwOf_fonOf_cmpOf : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) → (∀ (l : ℕ) [Fact l.Prime], WachEx (A l)) → ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) := by
  intro L A hT hW
  have key : ∀ (l : ℕ) [Fact l.Prime], ∃ H : LocHW l (L l), ∃ F : LocFon l (L l) (A l) H,
      Nonempty (LocCmpT l (L l) (A l) H F) := fun l _ =>
    GlobalTheory.T.exists_local_wach_functor l (L l) (A l) (hT l) (GlobalTheory.T.cyclotomicKernel_tilt_invariants_faithful l (L l) (A l)) (hW l)
  choose H F hC using key
  exact ⟨fun l _ => H l, fun l _ => F l, ⟨fun l _ => (hC l).some⟩⟩

end GlobalTheory.HWL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwOfFonOfCmpOfStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.exists_hwOf_fonOf_cmpOf' : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) → (∀ (l : ℕ) [Fact l.Prime], WachEx (A l)) → ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) := by
  first | exact @GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf | exact GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf | (intros; apply GlobalTheory.HWL.exists_hwOf_fonOf_cmpOf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriodStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem _root_.GlobalTheory.T.nonempty_theta_deRhamFil_zero_concretePeriod : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → Nonempty (Formalism.MainNotions.LocalSituation.ThetaL P AI) := by
  first | exact @GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL | exact GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL | (intros; apply GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwFonCmpTies

section

@[expose] public section

namespace GlobalTheory.HWL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem exists_hw_fon_cmp_ties : GlobalTheory.Published.BhattScholzeCrystallineLattices →
    ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
      (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) →
      ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) ∧ Nonempty (Formalism.MainNotions.LocalSituation.Ties L A H F) := by
  intro hBS L A hT
  obtain ⟨H, F, hC⟩ := GlobalTheory.T.exists_hwOf_fonOf_cmpOf' L A hT (fun l _ => GlobalTheory.T.wachLatticesExistAllLayers_of_bhattScholze hBS l (L l) (A l) (hT l))
  exact ⟨H, F, hC, ⟨⟨fun l _ => Classical.choice (GlobalTheory.T.nonempty_theta_deRhamFil_zero_concretePeriod l (L l) (A l) (hT l))⟩⟩⟩

end GlobalTheory.HWL
end
end
