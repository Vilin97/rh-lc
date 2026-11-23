module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickening
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeLiftWithPrincipalLineBundleStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundleStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.KernelTrivialOfEveryPointCovered
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaGroupKernelTrivialOfOpenCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfMumfordBundleLiftSqZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum



theorem GlobalTheory.Mum.exists_lift_of_lam_lift_sq : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left) (l : (Y₀ ⊗ Y₀).left ⟶ (Y ⊗ Y).left), IsAbelianScheme Y₀ → IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → IsSquare i l → ∀ (L₀ : LB Y₀.left) (Q : LB (Y ⊗ Y).left), L₀.IsLB → Q.IsLB → GlobalTheory.AbDual.IsAdditive Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → LBIso (Q.pull l) (abelian₂ Y₀ L₀) → ∃ L : LB Y.left, L.IsLB ∧ LBIso L₀ (L.pull i) := by
  intro R R₀ _ _ _ _ _ π hπ hI Y₀ _ Y _ i l hY₀ hY hgp hsq L₀ Q hL₀ hQ _ _ hΛ
  haveI : IsCommMonObj Y₀ := hY₀.comm
  obtain ⟨L, hL, hiso⟩ := GlobalTheory.T.exists_lineBundle_lift_squareZero_of_mumfordBundle R R₀ π hπ (by rw [hI]; rfl) Y Y₀ i l hY hgp hsq Q L₀
    hQ hL₀ (LBIso.symm hΛ)
  exact ⟨L, hL, LBIso.symm hiso⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfMumfordBundleLiftSqZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_lineBundle_lift_of_mumfordBundle_lift_sqZero : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left) (l : (Y₀ ⊗ Y₀).left ⟶ (Y ⊗ Y).left), IsAbelianScheme Y₀ → IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → IsSquare i l → ∀ (L₀ : LB Y₀.left) (Q : LB (Y ⊗ Y).left), L₀.IsLB → Q.IsLB → GlobalTheory.AbDual.IsAdditive Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → LBIso (Q.pull l) (abelian₂ Y₀ L₀) → ∃ L : LB Y.left, L.IsLB ∧ LBIso L₀ (L.pull i) := by
  first | exact @GlobalTheory.Mum.exists_lift_of_lam_lift_sq | exact GlobalTheory.Mum.exists_lift_of_lam_lift_sq | (intros; apply GlobalTheory.Mum.exists_lift_of_lam_lift_sq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPolarisationTrivialLiftsSqZero

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.KTrivSqZero

theorem exists_specializes_of_surjective {R R₀ : Type} [CommRing R] [CommRing R₀] {π : R →+* R₀}
    (hπ : Function.Surjective π) (hJ : RingHom.ker π ≤ Ideal.jacobson ⊥) (p : PrimeSpectrum R) :
    ∃ q : PrimeSpectrum R₀, p ⤳ PrimeSpectrum.comap π q := by
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.2.ne_top
  have hJm : RingHom.ker π ≤ m := hJ.trans (sInf_le ⟨bot_le, hm⟩)
  have : (⟨m, hm.isPrime⟩ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap π) := by
    rw [range_comap_of_surjective _ _ hπ]
    exact hJm
  obtain ⟨q, hq⟩ := this
  refine ⟨q, ?_⟩
  rw [hq, ← PrimeSpectrum.le_iff_specializes]
  exact hpm

theorem le_jacobson_of_sq_eq_bot {R : Type} [CommRing R] {J : Ideal R} (h : J ^ 2 = ⊥) : J ≤ Ideal.jacobson ⊥ := by
  intro x hx
  have hx2 : x ∈ (⊥ : Ideal R).radical := ⟨2, by
    have : x ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow hx 2
    rw [h] at this
    exact this⟩
  exact Ideal.radical_le_jacobson hx2

theorem kTriv_lift : ∀ (R R₀ : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → ∀ (L₀ : LB Y₀.left) (L : LB Y.left), L₀.IsLB → L.IsLB → RelAmple Y L → LBIso L₀ (L.pull i) → KTriv Y₀ L₀ → KTriv Y L := by
  intro R R₀ _ _ _ π hπ hsq Y₀ _ Y _ i hY hi L₀ L hL₀ hL hA e hK
  have hJ := le_jacobson_of_sq_eq_bot hsq
  have key : ∀ p : Sp R, ∃ U : (Sp R).Opens, p ∈ U ∧
      KTriv ((Over.pullback U.ι).obj Y) (L.pull (pullback.fst Y.hom U.ι)) := fun p => by
    obtain ⟨q, hq⟩ := exists_specializes_of_surjective hπ hJ p
    obtain ⟨U, hU, H⟩ := GlobalTheory.KTrivGlob.exists_open hL hL₀ hY hA hi e hK q
    exact ⟨U, hq.mem_open U.2 hU, H⟩
  choose U hU hK using key
  have hL' := fun p => pull_isLB hL (pullback.fst Y.hom (U p).ι)
  exact GlobalTheory.CoverGlue.kTriv_of_cover _ _ U Y _ _
    (top_le_iff.1 fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hU p⟩)
    (fun p => isGrpPullback_pullback Y (U p).ι) _ _ hL hL' (fun p => GlobalTheory.lbIso_refl (hL' p)) hY
    (fun p => by
      have := hY.comm
      have := hY.smooth
      have := hY.proper
      have := hY.geomConnected
      refine ⟨inferInstance, ?_, ?_, ?_⟩
      · change Smooth (pullback.snd Y.hom (U p).ι)
        infer_instance
      · change IsProper (pullback.snd Y.hom (U p).ι)
        infer_instance
      · change GeometricallyConnected (pullback.snd Y.hom (U p).ι)
        infer_instance) hK

end GlobalTheory.KTrivSqZero
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelPolarisationTrivialLiftsSqZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.kernelPolarisation_trivial_lifts_sqZero : ∀ (R R₀ : Type) [CommRing R] [IsNoetherianRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀] (Y : Over (Sp R)) [GrpObj Y] (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y → IsGrpPullback Y₀ Y (spMap π) i → ∀ (L₀ : LB Y₀.left) (L : LB Y.left), L₀.IsLB → L.IsLB → RelAmple Y L → LBIso L₀ (L.pull i) → KTriv Y₀ L₀ → KTriv Y L := by
  first | exact @GlobalTheory.KTrivSqZero.kTriv_lift | exact GlobalTheory.KTrivSqZero.kTriv_lift | (intros; apply GlobalTheory.KTrivSqZero.kTriv_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianLiftAmpleBundle

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.SqStep.exists_lift : ∀ (R R₀ : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R₀] [IsLocalRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (Y₀ : Over (Sp R₀)) [GrpObj Y₀], IsAbelianScheme Y₀ → ∀ L₀ : LB Y₀.left, L₀.IsLB → RelAmple Y₀ L₀ → KTriv Y₀ L₀ → ∃ (Y : Over (Sp R)) (_ : GrpObj Y) (L : LB Y.left) (i : Y₀.left ⟶ Y.left), IsAbelianScheme Y ∧ L.IsLB ∧ RelAmple Y L ∧ KTriv Y L ∧ IsGrpPullback Y₀ Y (spMap π) i ∧ LBIso L₀ (L.pull i) := by
  intro R R₀ _ _ _ _ _ π hπ hsq Y₀ _ hY₀ L₀ hL₀ hamp hK
  obtain ⟨Y, _, i, l, Q, hY, hpb, hsqr, hQ, a₁, a₂, hQi⟩ :=
    GlobalTheory.T.exists_abelianScheme_lift_with_principal_lineBundle R R₀ π hπ hsq Y₀ hY₀ L₀ hL₀ hamp hK
  obtain ⟨L, hL, hLi⟩ := GlobalTheory.T.exists_lineBundle_lift_of_mumfordBundle_lift_sqZero R R₀ π hπ hsq Y₀ Y i l hY₀ hY hpb hsqr L₀ Q hL₀ hQ a₁ a₂ hQi
  haveI : Smooth Y.hom := hY.smooth
  have hamp' : RelAmple Y L :=
    GlobalTheory.AmpleThickening.relAmple_of_sq_zero R R₀ π hπ hsq Y Y₀ i hpb.1 inferInstance L L₀ hL hL₀ hLi hamp
  exact ⟨Y, inferInstance, L, i, hY, hL, hamp',
    GlobalTheory.T.kernelPolarisation_trivial_lifts_sqZero R R₀ π hπ hsq Y₀ Y i hY hpb L₀ L hL₀ hL hamp' hLi hK, hpb, hLi⟩
end
end
