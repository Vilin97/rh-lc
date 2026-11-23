module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisConditionFourOf
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoCharacterOffsetUnramified

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut

namespace GlobalTheory.UnrNoChi

variable {D : D7} (i : D.nd.Loc)

theorem mapM_twistM' {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (χ : GE D.nd →* (D.nd.O i)ˣ)
    (g : GE D.nd) :
    mapM (toK D.nd i) (twistM M χ) g = toK D.nd i ((χ g : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) M g := by
  ext a b
  simp [mapM, twistM, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem chi_one_eq_one (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)) (hρ : GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ)
    {γ : GE D.nd} (hγ : r π γ = 1) : chiU D.nd i 1 γ = 1 := by
  obtain ⟨-, e, he⟩ := hρ
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set u := e.symm (0, Pi.single (⟨0, ht⟩ : Fin D.R.t) 1) with hu
  have h := congrArg (fun p => p.2 (⟨0, ht⟩ : Fin D.R.t)) (he γ u)
  simp only [hγ, Units.val_one, Matrix.map_one (toK D.nd i) (map_zero _) (map_one _), Matrix.one_mulVec, hu,
    LinearEquiv.apply_symm_apply, Pi.single_eq_same, mul_one] at h
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
  simpa using h.symm

end GlobalTheory.UnrNoChi
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraFurther

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut
namespace GlobalTheory.UnrNoChi
variable {D : D7} (i : D.nd.Loc)
end GlobalTheory.UnrNoChi
theorem GlobalTheory.UnrNoChi.main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → NoChiOff i r Set.univ ∧ UnrOut i r Set.univ := by
  intro D L nch i r π ρ hF _ _ hHG hr _ hρ
  have hUnr := _root_.Formalism.MainNotions.N.admG4_of_goodR D i r hF.Conclusion1.1 hr
  have hSub := Formalism.MainNotions.N.galois_condition_six_of D i r hF.Conclusion2.2.1 hHG hr
  refine ⟨?_, ?_⟩
  · intro x _ hxZ u hu
    by_contra hu0
    refine hxZ (hSub x ⟨u, hu0, fun g => ?_⟩)
    have h := hu g
    rw [rTwO, GlobalTheory.UnrNoChi.mapM_twistM', Matrix.smul_mulVec] at h
    conv_rhs => rw [← h]
    rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
      one_smul]
  · intro v hvl hvS hvQ x _ γ hγ
    have hχ := GlobalTheory.UnrNoChi.chi_one_eq_one i r π ρ hρ (hUnr π v hvl hvS hvQ γ hγ)
    have hx : rO D.nd i r x γ = 1 := by simp [rO, hUnr x v hvl hvS hvQ γ hγ]
    rw [rTwO, twistM]
    simp [hx, hχ]
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraFurtherStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

theorem _root_.GlobalTheory.T.noChiOff_and_unrOut_of_large_good_place : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → NoChiOff i r Set.univ ∧ UnrOut i r Set.univ := by
  first | exact @_root_.GlobalTheory.UnrNoChi.main_alt_alt | exact _root_.GlobalTheory.UnrNoChi.main_alt_alt | (intros; apply _root_.GlobalTheory.UnrNoChi.main_alt_alt <;> assumption)
end
end
end
