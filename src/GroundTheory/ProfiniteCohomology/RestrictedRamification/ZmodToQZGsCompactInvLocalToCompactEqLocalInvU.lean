module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseClassIdele
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFormal
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseKummerDelta
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsDiscreteRepResIntRepTrivGs
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupFormula
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupKummer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MkFiniteEmbeddingGlobalUniformizer
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupGlobal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCupNat
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ClassFieldGSPresentation
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
import Mathlib.Tactic.TypeStar

-- Source module: GroundTheory.ProfiniteCohomology.RestrictedRamification.GsRootsToUnitsCompactComparisonCup

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh GroundTheory.Global.IdeleGroup

attribute [local instance 2000] Rep.hV2

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

omit [NeZero n] in
theorem linearMap_apply_add_apply {R M N P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P] (f : M →ₗ[R] N →ₗ[R] P) (a b : M) (c : N) :
    f (a + b) c = f a c + f b c := by
  rw [map_add (f := _), LinearMap.add_apply]



theorem gsRootsToUnitsCompact_comparison_cup (h : gsUnitsCompact S ιs 1)
    (x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
      (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
        (show 2 + 1 = 3 from rfl) ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom h))
        x)) =
      compactCup (gsFinFamily S ιs) (gsPairingμ S n) (gsPairingμᵥ S ιs n) (gsPairingμ_hμ S ιs n)
        (show 1 + 1 + 1 = 2 + 1 from rfl) ((gsKummerCompactδ S ιs n hnS 1).hom h) x := by
  have ea := gsRootsComparison_compactCupRes S ιs n
    ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom h)) x
  have ea' : (gsRootsComparison S ιs n 2).hom ((gsRootsComparisonIso S ιs n hnS 2).inv.hom
      ((gsKummerCompactδ S ιs n hnS 1).hom h)) = (gsKummerCompactδ S ιs n hnS 1).hom h :=
    hom_apply_hom_apply_of_comp_eq (gsRootsComparisonIso S ιs n hnS 2).inv_hom_id _
  have eb := compactCohomologyMap_compactCup (gsFinFamily S ιs) (A := gsRoots S n)
    (B := zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) (C := gsRoots S n) (C' := galSUnitsMax K.1 ℚ̄ S)
    (Aᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (Cᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (C'ᵥ := fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (a := gsRootsOmegaMor S ιs n) (c := gsRootsOmegaMor S ιs n) (c' := gsSUnitsLocalMor S ιs)
    (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f
    (fun v => (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f)
    (fun v => (gsKummerLocalMap S ιs n v).comm₁₂) (gsPairingμ_hμ S ιs n) (show 1 + 1 + 1 = 2 + 1 from rfl)
    ((gsKummerCompactδ S ιs n hnS 1).hom h) x
  exact (congrArg (gsRootsToUnitsCompact S ιs n 3).hom (ea.trans (congrArg (fun w =>
    compactCup (gsFinFamily S ιs) (gsZmodPairing S n) (gsZmodPairingᵥ S ιs n) (gsZmodPairing_hμ S ιs n)
      (show 2 + 1 = 3 from rfl) w x) ea'))).trans eb



theorem gsRootsToUnitsCompact_cup_eq (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    ∃ W : cocycles (galUnits K.1 (maxUnramifiedOutside K.1 ℚ̄ S)) 2,
      (∀ g h, (Additive.toMul (cochainOf _ (cocycleι _ 2 W) ![g, h]) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) *
        (((Additive.toMul d.1 : sInvariantSubgroup (F := K.1) ℚ̄ S) : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ) ^
          bockInt (zmodCocycleHom z) g h)⁻¹ ∈ sUnitsMax K.1 ℚ̄ S) ∧
      (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
        (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n))
          (show 2 + 1 = 3 from rfl)
          ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom (gsUnitsData S ιs d)))
          (cohomologyπ _ 1 z))) =
        (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
          (fun v => (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
              (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 W) +
            cupPairing (mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (show 0 + 2 = 2 from rfl)
              ((H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
              ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom
                ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom
                  (cohomologyπ _ 1 z)))) := by
  have ex := exists_gsUnitsData_cup_bock S ιs n ℓ k hℓ hnk hS (Additive.toMul d.1) z
  refine ⟨ex.choose, ex.choose_spec.1, ?_⟩
  have hd : gsUnitsData S ιs d = gsUnitsData S ιs (Additive.ofMul (Additive.toMul d.1), 0) +
      gsUnitsData S ιs (0, d.2) :=
    (congrArg (gsUnitsData S ιs) (Prod.ext (add_zero _).symm (zero_add _).symm)).trans (map_add _ _ _)
  have eloc := compactCup_localToCompact (gsFinFamily S ιs) (gsPairingU S)
    (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
    (show 0 + 2 = 2 from rfl) (show 0 + 1 + 2 = 2 + 1 from rfl)
    (fun v => (H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
    ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z))
  refine (gsRootsToUnitsCompact_comparison_cup S ιs n hnS (gsUnitsData S ιs d) (cohomologyπ _ 1 z)).trans
    ((gsKummerCompactδ_cup S ιs n hnS (gsUnitsData S ιs d) (cohomologyπ _ 1 z)).trans ?_)
  refine (congrArg (fun w => compactCup (gsFinFamily S ιs) (gsPairingU S)
      (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
      (show 1 + (1 + 1) = 2 + 1 from rfl) w
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))
    hd).trans ((linearMap_apply_add_apply _ _ _ _).trans ?_)
  refine (congrArg₂ (· + ·) ex.choose_spec.2 ((congrArg (fun w => compactCup (gsFinFamily S ιs) (gsPairingU S)
      (fun v => mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (gsPairingU_hμ S ιs)
      (show 1 + (1 + 1) = 2 + 1 from rfl) w
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))
    (gsUnitsData_zero_local S ιs d.2)).trans eloc)).trans ?_
  exact (map_add _ _ _).symm

section Idele

variable [Fintype S] (hodd : Odd n ∨ IsTotallyComplex K.1)

omit [NeZero n] in
theorem prod_ofFinite_eq {M : Type*} [CommMonoid M] (f : S → M) :
    (letI := Fintype.ofFinite S; ∏ w : S, f w) = ∏ w : S, f w := by
  congr
  exact Subsingleton.elim _ _


omit [NeZero n] in
theorem sPresentation_fst (a : ∀ w : S, ((w : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)ˣ) :
    sPresentation S (a, 1) = ∏ w : S, SIdeleClassGroup.mk S (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (a w)) := by
  rw [sPresentation_apply, toAdd_one, map_zero, toMul_zero, mul_one, placesIdele_apply, map_prod]
  exact prod_ofFinite_eq S _



theorem zmodToQZ_charEquiv_gsUnitsClass
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n))) (d : GsUnitsDatum S) :
    zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ (Additive.toMul (gsUnitsClass S d)))) =
      ∑ v : S, zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
        (SIdeleClassGroup.mk S (finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 v)))))) -
      divChar S hodd χ (divAbove S d.1) := by
  have e1 : Additive.toMul (gsUnitsClass S d) =
      sPresentation S (fun w => Additive.toMul (d.2 w), 1) *
        sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1)) :=
    (congrArg Additive.toMul (gsUnitsClass_apply S d)).trans
      ((congrArg (sPresentation S) (Prod.ext (mul_one _).symm (one_mul _).symm)).trans (map_mul _ _ _))
  set ψ := charEquiv ℚ̄ (Set.toFinite S) hodd χ with hψ
  have e2 : ψ (Additive.toMul (gsUnitsClass S d)) =
      (∏ w : S, ψ (SIdeleClassGroup.mk S (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w))))) *
        ψ (sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1))) :=
    (congrArg ψ e1).trans ((map_mul ψ _ _).trans (congrArg (· * _)
      ((congrArg ψ (sPresentation_fst S _)).trans (map_prod ψ _ _))))
  have e3 : zmodToQZ n (Multiplicative.toAdd (ψ (sPresentation S (1, Multiplicative.ofAdd (-divAbove S d.1))))) =
      -divChar S hodd χ (divAbove S d.1) :=
    (divChar_apply S hodd χ (-divAbove S d.1)).symm.trans (map_neg _ _)
  have e4 : zmodToQZ n (Multiplicative.toAdd (∏ w : S, ψ (SIdeleClassGroup.mk S
      (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w)))))) =
      ∑ w : S, zmodToQZ n (Multiplicative.toAdd (ψ (SIdeleClassGroup.mk S
        (finiteEmbedding (w : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 w)))))) :=
    (congrArg (zmodToQZ n) (toAdd_prod _ _)).trans (map_sum (zmodToQZ n) _ _)
  exact (congrArg (fun u => zmodToQZ n (Multiplicative.toAdd u)) e2).trans
    ((congrArg (zmodToQZ n) (toAdd_mul _ _)).trans ((map_add (zmodToQZ n) _ _).trans
      ((congrArg₂ (· + ·) e4 e3).trans (sub_eq_add_neg _ _).symm)))

end Idele

end

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.RestrictedRamification.ZmodToQZGsCompactInvLocalToCompactEqLocalInvU

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory IsDedekindDomain NumberField GroundTheory.Global GroundTheory.GroupCoh GroundTheory.Global.IdeleGroup

attribute [local instance 2000] Rep.hV2

noncomputable section

local notation "ℚ̄" => AlgebraicClosure ℚ

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)

omit [NeZero n] in
theorem nsmul_zmodToQZ (x : ZMod n) : n • zmodToQZ n x = 0 := by
  rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]

def gsCupClass (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) :
    compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 3 :=
  compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n) (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl)
    ((gsRootsComparisonIso S ιs n hnS 2).inv.hom ((gsKummerCompactδ S ιs n hnS 1).hom (gsUnitsData S ιs d)))
    (cohomologyπ _ 1 z)

def gsLocalUnitsImage (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) (v : S) :
    cohomology (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) 2 :=
  (cohomologyMap (gsRootsOmegaMor S ιs n v ≫ rootsOfUnityToUnits _ _ n) 2).hom (ξ v)



theorem zmodToQZ_gsCompactInv_localToCompact_eq_localInvU (hodd : Odd n ∨ IsTotallyComplex K.1)
    (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    zmodToQZ n (gsCompactInv S ιs n hodd h3
      ((localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom ξ)) =
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalUnitsImage S ιs n ξ v) :=
  (congrArg (zmodToQZ n) ((gsCompactInv_localToCompact S ιs n hodd h3 ξ).trans (gsSumInvRoots_apply S ιs n ξ))).trans
    ((map_sum (zmodToQZ n) _ _).trans
      (Finset.sum_congr rfl fun v _ => zmodToQZ_gsLocalInvRoots_eq_localInvU S ιs n v (ξ v)))


omit [Fintype S] in

theorem gsRootsToUnitsCompact_comparison_localToCompact
    (ξ : ∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 2) :
    (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom
      ((localToCompact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 2).hom ξ)) =
      (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
        (gsLocalUnitsImage S ιs n ξ) := by
  have hg : ∀ v, 𝟙 (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v =
      (Rep.resFunctor (gsFinFamily S ιs v).toMonoidHom).map (𝟙 (gsRoots S n)) ≫ gsRootsOmegaMor S ιs n v :=
    fun _ => Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  have e1 := hom_apply_hom_apply_eq_of_comp_eq (localToCompact_compactCohomologyMap (gsFinFamily S ιs)
    (A := gsRoots S n) (B := gsRoots S n) (Aᵥ := fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
    (Bᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n) (a := fun _ => 𝟙 _) (b := gsRootsOmegaMor S ιs n)
    (𝟙 (gsRoots S n)) (gsRootsOmegaMor S ιs n) hg 2) ξ
  have e2 := hom_apply_hom_apply_eq_of_comp_eq (localToCompact_compactCohomologyMap (gsFinFamily S ιs)
    (A := gsRoots S n) (B := galSUnitsMax K.1 ℚ̄ S) (Aᵥ := fun v => galRootsOfUnity.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n)
    (Bᵥ := fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (a := gsRootsOmegaMor S ιs n) (b := gsSUnitsLocalMor S ιs)
    (sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) n).f
    (fun v => (kummerSequence ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)
      (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) n).f)
    (fun v => (gsKummerLocalMap S ιs n v).comm₁₂) 2) (fun v => (cohomologyMap (gsRootsOmegaMor S ιs n v) 2).hom (ξ v))
  refine (congrArg (gsRootsToUnitsCompact S ιs n 3).hom e1).trans (e2.trans ?_)
  refine congrArg (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))
    (gsSUnitsLocalMor S ιs) 2).hom (funext fun v => ?_)
  exact (hom_apply_hom_apply_of_comp_eq (cohomologyMap_comp _ _ 2).symm (ξ v))

def gsLocalCup (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) (v : S) :
    cohomology (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) 2 :=
  cupPairing (mulIntRight (gsFinFamily S ιs v).toMonoidHom (galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)))) (show 0 + 2 = 2 from rfl)
    ((H0Iso _).inv.hom (unitsToInvariants _ _ (d.2 v)))
    ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _) (𝟙 _) 2).hom
      ((δ (bockSeq_shortExact (galUnramifiedOutside K.1 ℚ̄ S) n (NeZero.ne n)) 1 2 rfl).hom (cohomologyπ _ 1 z)))

omit [Fintype S] [NeZero n] in
theorem sub_sub_eq_neg_sub_add {M : Type*} [AddCommGroup M] (a b c : M) : b - (a - c) = -(a - (b + c)) := by
  abel

omit [Fintype S] [NeZero n] in
theorem sum_map_eq_sum_map_sub_add {ι : Type*} (s : Finset ι) {M : ι → Type*} [∀ v, AddCommGroup (M v)] {N : Type*}
    [AddCommGroup N] (F : ∀ v, M v →+ N) (a b : ∀ v, M v) :
    ∑ v ∈ s, F v (a v) = ∑ v ∈ s, F v (a v - b v) + ∑ v ∈ s, F v (b v) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => by rw [map_sub, sub_add_cancel]

omit [Fintype S] [NeZero n] in
theorem nsmul_sum_map_sub {ι : Type*} (s : Finset ι) {M : ι → Type*} [∀ v, AddCommGroup (M v)] {N : Type*}
    [AddCommGroup N] (F : ∀ v, M v →+ N) (a b : ∀ v, M v) (ha : ∀ v, n • F v (a v) = 0)
    (hb : ∀ v, n • F v (b v) = 0) : n • ∑ v ∈ s, F v (a v - b v) = 0 := by
  rw [Finset.smul_sum]
  exact Finset.sum_eq_zero fun v _ => by rw [map_sub, smul_sub, ha, hb, sub_zero]



theorem zmodToQZ_gsCompactInv_gsCupClass (ℓ k : ℕ) (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))
    (d : GsUnitsDatum S) (z : cocycles (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1)
    (χ : ContinuousMonoidHom (galUnramifiedOutside K.1 ℚ̄ S) (Multiplicative (ZMod n)))
    (hχ : ∀ g, Multiplicative.toAdd (χ g) = zmodCocycleHom z g) :
    zmodToQZ n (gsCompactInv S ιs n hodd h3 (gsCupClass S ιs n hnS d z)) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ (Additive.toMul (gsUnitsClass S d)))) := by
  have hsurj := localToCompact_two_surjective S ιs n h3 (gsCupClass S ιs n hnS d z)
  have hT := (congrArg (fun w => zmodToQZ n (gsCompactInv S ιs n hodd h3 w)) hsurj.choose_spec).symm.trans
    (zmodToQZ_gsCompactInv_localToCompact_eq_localInvU S ιs n hodd h3 hsurj.choose)
  have L1 := gsRootsToUnitsCompact_cup_eq S ιs n hnS ℓ k hℓ hnk hS d z
  have hL2 := (congrArg (fun w => (gsRootsToUnitsCompact S ιs n 3).hom ((gsRootsComparison S ιs n 3).hom w))
    hsurj.choose_spec).symm.trans (gsRootsToUnitsCompact_comparison_localToCompact S ιs n hsurj.choose)
  have h0 : (localToCompact (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) (fun v => galUnits.{0, 0} ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))) (gsSUnitsLocalMor S ιs) 2).hom
      (gsLocalUnitsImage S ιs n hsurj.choose - fun v =>
        (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
          (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 L1.choose) + gsLocalCup S ιs n d z v) = 0 := by
    exact (map_sub _ _ _).trans (sub_eq_zero.2 (hL2.symm.trans L1.choose_spec.2))
  have hex := (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
    (compactCohomology_exact_local (gsFinFamily S ιs) (galSUnitsMax K.1 ℚ̄ S) _ (gsSUnitsLocalMor S ιs) 2) h0
  have hy : ∀ v : S, (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
      (gsUnitsLocalMor S ιs v) 2).hom (cohomologyπ _ 2 L1.choose) -
        (gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) =
      (cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom (-hex.choose) := fun v =>
    (sub_sub_eq_neg_sub_add _ _ _).trans ((congrArg Neg.neg (congrFun hex.choose_spec v).symm).trans
      (map_neg ((cohomologyMapAlong (gsFinFamily S ιs v).toMonoidHom (continuous_toMonoidHom _)
        (gsSUnitsLocalMor S ιs v) 2).hom) hex.choose).symm)
  have hloc : ∀ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalCup S ιs n d z v) =
      zmodToQZ n (Multiplicative.toAdd (charEquiv ℚ̄ (Set.toFinite S) hodd χ
        (SIdeleClassGroup.mk S (finiteEmbedding (v : HeightOneSpectrum (𝓞 K.1)) (Additive.toMul (d.2 v)))))) :=
    fun v => localInvU_cupPairing_δ_bockSeq S ιs hodd v (Additive.toMul (d.2 v)) z χ hχ
  have hβ : n • ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1))
      (gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) = 0 :=
    nsmul_sum_map_sub n Finset.univ (fun v : S => localInvU (v : HeightOneSpectrum (𝓞 K.1)))
      (gsLocalUnitsImage S ιs n hsurj.choose) (gsLocalCup S ιs n d z)
      (fun v => (congrArg (n • ·) (zmodToQZ_gsLocalInvRoots_eq_localInvU S ιs n v (hsurj.choose v)).symm).trans
        (nsmul_zmodToQZ n _))
      (fun v => (congrArg (n • ·) (hloc v)).trans (nsmul_zmodToQZ n _))
  have hT1 := sum_localInvU_eq_neg_divChar S ιs hodd (Additive.toMul d.1) z χ hχ L1.choose L1.choose_spec.1
    (fun v => gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) (-hex.choose) hy hβ
  have hsum : ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalUnitsImage S ιs n hsurj.choose v) =
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1))
        (gsLocalUnitsImage S ιs n hsurj.choose v - gsLocalCup S ιs n d z v) +
      ∑ v : S, localInvU (v : HeightOneSpectrum (𝓞 K.1)) (gsLocalCup S ιs n d z v) :=
    sum_map_eq_sum_map_sub_add Finset.univ (fun v : S => localInvU (v : HeightOneSpectrum (𝓞 K.1)))
      (gsLocalUnitsImage S ιs n hsurj.choose) (gsLocalCup S ιs n d z)
  exact hT.trans (hsum.trans ((congrArg₂ (· + ·) hT1 (Finset.sum_congr rfl fun v _ => hloc v)).trans
    ((neg_add_eq_sub _ _).trans (zmodToQZ_charEquiv_gsUnitsClass S n hodd χ d).symm)))

end

end GroundTheory.ProfCoh
end
end
