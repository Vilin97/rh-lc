module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlaceStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimensionStatement
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinPairNumJoinLeft
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
import Mathlib.NumberTheory.Height.NumberField
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishOfTrivialFlags

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ZTop

theorem isFibreComp_variety {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {W : Ideal (MRing ι O)} (hW : IsFibreComp P W) :
    IsMultiProjPrime (specialIdeal W) ∧
      ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hmin, hrel⟩ := hW
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hmin
  refine PairNumberJoinLeft.verticalComponentFibre O ϖ hϖ K ι P d hP (C ϖ) 0
    (isWeightedHomogeneous_C _ _) (fun h => hϖ.ne_zero ?_) W hmin hrel
    (hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  exact Ideal.mem_bot.mp (hP.noTorsion ▸ Ideal.mem_comap.mpr h)

theorem cast_classNum {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ : Type} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    ((classNum cls H Q W : ℤ) : ℝ) =
      genNum (IsLocalRing.ResidueField O) (specialIdeal W) cls (MvPolynomial.map (Int.castRingHom ℝ) H) Q := by
  unfold classNum genNum
  rw [MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℝ))]
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_map]
  rfl

theorem powerSumsVanish_of_trivFlagAt :
    NumericalSegre.Statement → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
      Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (N : ℕ) (x : Fin N → K → ℤ),
      (∀ W, IsFibreComp P W → TrivFlagAt W x) → PowerSumsVanish P d x := by
  intro hS O _ _ _ ϖ hϖ K _ _ ι _ P d hP N x hx W hW k hk Q hQ
  obtain ⟨Ω, _, _, y, w, hy, hflag⟩ := hx W hW
  obtain ⟨hprime, hdim⟩ := isFibreComp_variety hϖ hP hW
  have h := GlobalTheory.T.flag_frame_point_dimension hS (IsLocalRing.ResidueField O) Ω K ι y d (hy ▸ hprime) (hy ▸ hdim) N w x hflag
    k hk Q hQ
  have hmap : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin N) ℤ k) = ∑ i, X i ^ k := by
    simp [psum]
  have h2 := cast_classNum x (psum (Fin N) ℤ k) Q W
  rw [hmap, ← hy, h] at h2
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.Num.ZTop
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishOfTrivialFlagsStatement

section

@[expose] public section

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem _root_.GlobalTheory.T.power_sums_vanish_of_trivial_flags : NumericalSegre.Statement → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (N : ℕ) (x : Fin N → K → ℤ), (∀ W, IsFibreComp P W → TrivFlagAt W x) → PowerSumsVanish P d x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt | exact GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompRootModelPrimes

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem linked_two_levels : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → HodgeLatticeFlagBound → TrivFlagOnHodge → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S S₀ : Finset ℕ) [Fintype (CMType H)] [DecidableEq (CMType H)] (M : RootModel (CMType H) (D.p + D.q)) [DecidableEq M.K] (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (R : SecondRoots M), Fl.TwoLevels S₀ R.pairs → (∀ p ∈ S, p ∉ S₀ → HT.HTFree 𝔐 p ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ NumberField.discr E) → ∀ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p ∈ S, p ∉ S₀ → IsFrobLabels c p (φ p)) → R.pairs.IsVertOff M.P ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧ R.LocalAtPlaces D.p ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) φ := by
  intro hseg hM3 hTriv E _ _ _ H D l Xo c O₀ _ β Y S S₀ _ _ M instK 𝔐 Fl R hTL hloc φ hφ
  obtain rfl : instK = (fun a b => Classical.propDecidable (a = b) : DecidableEq M.K) := Subsingleton.elim _ _
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, _, hvert⟩ := hTL
    exact hvert
  · obtain ⟨hded, hfin, hinj, hcst, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 (dimFl (CMType H) (D.p + D.q)) M.arith (integralClosure ℤ M.Ω)
    refine ⟨integralClosure ℤ M.Ω, inferInstance, hded, hfin, inferInstance, hinj, hcst, ?_⟩
    intro p hp m _ hpm O _ _ _ _ _ _ _
    have hp' : (p : ℕ) ∈ S ∧ (p : ℕ) ∉ S₀ := Finset.mem_sdiff.1 (Finset.mem_preimage.1 hp)
    obtain ⟨hHT, h2, hd⟩ := hloc p hp'.1 hp'.2
    obtain ⟨_, _, _, e₀, e, _, hrl, _, _⟩ := id hTL
    refine ⟨?_, ?_⟩
    · exact hM3 E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 _ M.arith Fl S₀ R.pairs hTL p hp'.1 hp'.2 hHT h2 hd (φ p) (hφ p hp'.1 hp'.2) (integralClosure ℤ M.Ω) m hpm O
    · intro τ
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
      have hmod := (GlobalTheory.T.localization_model_over_place M.K M.ι M.Ω M.y (integralClosure ℤ M.Ω) hinj hcst _ M.arith m O).2.1
      exact GlobalTheory.T.power_sums_vanish_of_trivial_flags hseg O ϖ hϖ M.K M.ι _ _ hmod _ _ fun W hW =>
        hTriv E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 _ M.arith Fl R.pairs.x' e hrl p hp'.1 hHT (integralClosure ℤ M.Ω) m hpm O τ W hW

end GlobalTheory.CompanionTheory.Ar.Num
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompRootModelPrimesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

theorem _root_.GlobalTheory.T.hodge_comp_root_model_primes : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → HodgeLatticeFlagBound → TrivFlagOnHodge → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S S₀ : Finset ℕ) [Fintype (CMType H)] [DecidableEq (CMType H)] (M : RootModel (CMType H) (D.p + D.q)) [DecidableEq M.K] (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (R : SecondRoots M), Fl.TwoLevels S₀ R.pairs → (∀ p ∈ S, p ∉ S₀ → HT.HTFree 𝔐 p ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ NumberField.discr E) → ∀ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p ∈ S, p ∉ S₀ → IsFrobLabels c p (φ p)) → R.pairs.IsVertOff M.P ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧ R.LocalAtPlaces D.p ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels | exact GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels <;> assumption)
end
end
