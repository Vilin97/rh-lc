module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulEqUnit
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Order.CompletePartialOrder
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreGenericPointDvrOfPrime

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

theorem exists_fibre_generic_of_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (π : R), Prime π → ∃ ξ : X, (q ξ).asIdeal = Ideal.span {π} ∧ (∀ x : X, (q x).asIdeal = Ideal.span {π} → ξ ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧ Irreducible (X.presheaf.germ ⊤ ξ trivial (constFn q ⊤ π)) := by
  intro R _ _ _ _ X _ q _ _ π hπp
  have hP : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπp.ne_zero).2 hπp
  let v : Sp R := ⟨Ideal.span {π}, hP⟩
  let V := Localization.AtPrime v.asIdeal
  have hmax : IsLocalRing.maximalIdeal V = Ideal.span {algebraMap R V π} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_span, Set.image_singleton]
  have hne : algebraMap R V π ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective V v.asIdeal.primeCompl_le_nonZeroDivisors)).2 hπp.ne_zero
  have : IsNoetherianRing V := IsLocalization.isNoetherianRing v.asIdeal.primeCompl V inferInstance
  have hnf : ¬ IsField V := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact hne
  have hpr : Submodule.IsPrincipal (IsLocalRing.maximalIdeal V) := ⟨⟨_, hmax⟩⟩
  have : IsDiscreteValuationRing V :=
    ((IsDiscreteValuationRing.TFAE V hnf).out 1 5).mpr hpr
  have hπ : Irreducible (algebraMap R V π) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmax
  let l := spMap (algebraMap R V)
  have : Flat l := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : IsPreimmersion l := IsPreimmersion.of_isLocalization v.asIdeal.primeCompl
  have H := IsPullback.of_hasPullback q l
  set ψ := pullback.fst q l
  set f := pullback.snd q l
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks ψ
  obtain ⟨h₁, h₂⟩ := DvrModel.isDiscreteValuationRing_stalk_generic hπ hs
  have h₃ := DvrModel.notMem_basicOpen_iff_specializes hπ hs
  have hlv : l (IsLocalRing.closedPoint V) = v :=
    PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := v.asIdeal))
  have h₄ := (DvrModel.notMem_basicOpen_iff f hπ _).1 ((h₃ _).2 specializes_rfl)
  generalize (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))) (genericPoint _) = ξ
    at h₁ h₂ h₃ h₄
  let E := (asIso (ψ.stalkMap ξ)).commRingCatIsoToRingEquiv
  refine ⟨ψ ξ, ?_, fun x hx => ?_,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing E.symm, ?_⟩
  · rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply, h₄, hlv]
  · obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback H x (IsLocalRing.closedPoint V)
      ((PrimeSpectrum.ext hx).trans hlv.symm)
    exact ((h₃ y).1 ((DvrModel.notMem_basicOpen_iff f hπ y).2 hy)).map ψ.continuous
  · rw [← MulEquiv.irreducible_iff E.toMulEquiv]
    convert h₂ using 1
    exact (ψ.germ_stalkMap_apply ⊤ ξ trivial _).trans
      (congrArg _ ((app_constFn H.w π).trans (constFn_top _ _)))

end GlobalTheory.VerticalUnit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFibreGenericPointDvrOfPrimeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_fibre_genericPoint_dvr_of_prime : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (π : R), Prime π → ∃ ξ : X, (q ξ).asIdeal = Ideal.span {π} ∧ (∀ x : X, (q x).asIdeal = Ideal.span {π} → ξ ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧ Irreducible (X.presheaf.germ ⊤ ξ trivial (constFn q ⊤ π)) := by
  first | exact @GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime | exact GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime | (intros; apply GlobalTheory.VerticalUnit.exists_fibre_generic_of_prime <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeEqSpanOfCoheightLeOne

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_prime_eq_span_of_coheight_le_one (R : Type) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R) (hq : GeneralizingMap q)
    (x : X) (hx : Order.coheight x ≤ 1) (hne : (q x).asIdeal ≠ ⊥) :
    ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  obtain ⟨π, hπP, hπ⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (q x).isPrime hne
  refine ⟨π, hπ, ?_⟩
  by_contra hQP
  have hQle : Ideal.span {π} ≤ (q x).asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hπP
  have hQprime : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  let Q : PrimeSpectrum R := ⟨_, hQprime⟩
  have hQsp : Q ⤳ q x := (PrimeSpectrum.le_iff_specializes Q (q x)).1 hQle
  obtain ⟨x', hx'x, hqx'⟩ := hq hQsp
  let B : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hBQ : B ⤳ Q := (PrimeSpectrum.le_iff_specializes B Q).1 bot_le
  obtain ⟨x'', hx''x', hqx''⟩ := hq (hqx' ▸ hBQ)
  have h1 : x < x' := by
    refine lt_of_le_not_ge hx'x ?_
    intro h
    have h' : q x ⤳ q x' := h.map q.continuous
    rw [hqx'] at h'
    exact hQP (le_antisymm ((PrimeSpectrum.le_iff_specializes (q x) Q).2 h') hQle)
  have h2 : x' < x'' := by
    refine lt_of_le_not_ge hx''x' ?_
    intro h
    have h' : q x' ⤳ q x'' := h.map q.continuous
    rw [hqx', hqx''] at h'
    have hle : Ideal.span {π} ≤ ⊥ := (PrimeSpectrum.le_iff_specializes Q B).2 h'
    exact hπ.ne_zero (Ideal.span_singleton_eq_bot.1 (le_bot_iff.1 hle))
  have c1 := Order.coheight_add_one_le h1
  have c2 := Order.coheight_add_one_le h2
  have : (2 : ℕ∞) ≤ Order.coheight x := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight x'' + 1 + 1 := by gcongr; exact bot_le
      _ ≤ Order.coheight x' + 1 := by gcongr
      _ ≤ Order.coheight x := c1
  have := this.trans hx
  norm_num at this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeEqSpanOfCoheightLeOneStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' : ∀ (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (X : Scheme.{0}) (q : X ⟶ Sp R), GeneralizingMap q → ∀ x : X, Order.coheight x ≤ 1 → (q x).asIdeal ≠ ⊥ → ∃ π : R, Prime π ∧ (q x).asIdeal = Ideal.span {π} := by
  first | exact @GlobalTheory.exists_prime_eq_span_of_coheight_le_one | exact GlobalTheory.exists_prime_eq_span_of_coheight_le_one | (intros; apply GlobalTheory.exists_prime_eq_span_of_coheight_le_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpenGenericPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.VerticalUnit

theorem finite_coheight_one_notMem (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (S : Set X) (hS : IsOpen S) (hη : genericPoint X ∈ S) :
    {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  classical
  obtain ⟨T, hT, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS.isClosed_compl
  refine (hT.image fun Z => if h : IsIrreducible Z then h.genericPoint else genericPoint X).subset ?_
  rintro x ⟨h1, hxS⟩
  obtain ⟨Z, hZ, hxZ⟩ := hU.le hxS
  have hg := (hi Z hZ).isGenericPoint_genericPoint (hc Z hZ)
  set z := (hi Z hZ).genericPoint
  have hzS : z ∉ S := hU.ge (Set.subset_sUnion_of_mem hZ hg.mem)
  have hxz : x ≤ z := hg.specializes hxZ
  have hzη : z < genericPoint X := lt_of_le_not_ge (genericPoint_specializes z)
    fun h => hzS ((show z ⤳ genericPoint X from h).mem_open hS hη)
  refine ⟨Z, hZ, ?_⟩
  simp only [dif_pos (hi Z hZ)]
  by_contra hne
  have hxlt : x < z := lt_of_le_not_ge hxz fun h =>
    hne ((show x ⤳ z from h).antisymm (show z ⤳ x from hxz)).eq.symm
  have a1 := Order.coheight_add_one_le hxlt
  have a2 := Order.coheight_add_one_le hzη
  rw [h1] at a1
  have : (2 : ℕ∞) ≤ 1 := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ Order.coheight (genericPoint X) + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight z + 1 := by gcongr
      _ ≤ 1 := a1
  exact absurd this (by decide)

end GlobalTheory.VerticalUnit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoheightOneNotMemOpenGenericPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint : ∀ (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (S : Set X), IsOpen S → genericPoint X ∈ S → {x : X | Order.coheight x = 1 ∧ x ∉ S}.Finite := by
  first | exact @GlobalTheory.VerticalUnit.finite_coheight_one_notMem | exact GlobalTheory.VerticalUnit.finite_coheight_one_notMem | (intros; apply GlobalTheory.VerticalUnit.finite_coheight_one_notMem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulUnitAtCodimOneOfFactorialBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VerticalUnit

theorem UnitAt.zpow {X : Scheme.{0}} [IsIntegral X] {x : X} {s : X.functionField} (hs : UnitAt x s) (n : ℤ) :
    UnitAt x (s ^ n) := by
  obtain ⟨u, rfl⟩ := hs
  refine ⟨u ^ n, ?_⟩
  have := congrArg Units.val (map_zpow (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom) u n)
  rw [Units.val_zpow_eq_zpow_val, Units.coe_map] at this
  exact this

theorem UnitAt.prod {X : Scheme.{0}} [IsIntegral X] {x : X} {ι : Type} (s : Finset ι) (f : ι → X.functionField)
    (h : ∀ b ∈ s, UnitAt x (f b)) : UnitAt x (∏ b ∈ s, f b) :=
  Finset.prod_induction f (UnitAt x) (fun _ _ => UnitAt.mul) ⟨1, by simp⟩ h

theorem eq_of_specializes_of_coheight {X : Scheme.{0}} {x y : X} (h : y ⤳ x) (hx : Order.coheight x = 1)
    (hy : Order.coheight y = 1) : x = y := by
  by_contra hne
  have hlt : x < y := lt_of_le_not_ge (show x ≤ y from h) fun h' => hne (h.antisymm (show x ⤳ y from h')).eq.symm
  have := Order.coheight_add_one_le hlt
  rw [hx, hy] at this
  exact absurd this (by decide)

theorem unitAt_constFn {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (q : X ⟶ Sp R) (x : X) (b : R)
    (hb : b ∉ (q x).asIdeal) : IsUnit (X.presheaf.germ ⊤ x trivial (constFn q ⊤ b)) := by
  rw [← Scheme.mem_basicOpen_top, constFn_top, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hb

theorem exists_const_mul_unitAt_coheight_one : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [UniqueFactorizationMonoid R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X] (q : X ⟶ Sp R) [Smooth q] [GeometricallyIntegral q] (κ : K →+* X.functionField), (∀ b : R, κ (algebraMap R K b) = X.presheaf.germ ⊤ (genericPoint X) trivial (constFn q ⊤ b)) → ∀ (I : Type) (U : I → X.Opens) (t : I → X.functionField), (∀ x, ∃ i, x ∈ U i) → (∀ i x, x ∈ U i → t i ≠ 0) → (∀ i j x (s : X.functionField), x ∈ U i → x ∈ U j → GlobalTheory.VerticalUnit.UnitAt x (s * t j) → GlobalTheory.VerticalUnit.UnitAt x (s * t i)) → (∀ x, (q x).asIdeal = ⊥ → ∃ i, x ∈ U i ∧ GlobalTheory.VerticalUnit.UnitAt x (t i)) → ∃ a : Kˣ, ∀ i x, x ∈ U i → Order.coheight x = 1 → GlobalTheory.VerticalUnit.UnitAt x (κ a * t i) := by
  intro R K _ _ _ _ _ _ _ X _ _ q _ _ κ hκ I U t hcov ht0 htr hgen
  classical
  have hgz : GeneralizingMap q := Flat.generalizingMap q
  have hinj := IsFractionRing.injective R K
  have hunit : ∀ (x : X) (b : R), b ∉ (q x).asIdeal → UnitAt x (κ (algebraMap R K b)) := fun x b hb =>
    ⟨(unitAt_constFn q x b hb).unit, by
      rw [IsUnit.unit_spec, hκ]
      exact X.presheaf.germ_stalkSpecializes_apply _ _ _⟩
  let S : Set X := {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}
  have hS : IsOpen S := by
    change IsOpen {x | ∃ i, x ∈ U i ∧ UnitAt x (t i)}
    rw [Set.setOf_exists]
    exact isOpen_iUnion fun i => (U i).isOpen.inter (isOpen_unitAt _)
  have hg : genericPoint X ∈ S := by
    let p₀ : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
    obtain ⟨y, -, hy⟩ := hgz ((PrimeSpectrum.le_iff_specializes p₀ (q (genericPoint X))).1 bot_le)
    exact (genericPoint_specializes y).mem_open hS (hgen y (by rw [hy]))
  have hB := GlobalTheory.T.finite_coheight_one_notMem_open_genericPoint X S hS hg
  set B : Set X := {x : X | Order.coheight x = 1 ∧ x ∉ S} with hBdef
  have key : ∀ b ∈ B, ∃ π : R, Prime π ∧ (q b).asIdeal = Ideal.span {π} ∧
      (∀ x : X, (q x).asIdeal = Ideal.span {π} → b ⤳ x) ∧ IsDiscreteValuationRing (X.presheaf.stalk b) ∧
      Irreducible (X.presheaf.germ ⊤ b trivial (constFn q ⊤ π)) := by
    rintro b ⟨h1, hbS⟩
    have hb0 : (q b).asIdeal ≠ ⊥ := fun h => hbS (hgen b h)
    obtain ⟨π, hπ, hqb⟩ := GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz b h1.le hb0
    obtain ⟨ξ, -, hξ, hd, hirr⟩ := GlobalTheory.T.exists_fibre_genericPoint_dvr_of_prime R X q π hπ
    have hξ1 : Order.coheight ξ = 1 := by
      have e := IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk ξ)
      rw [ringKrullDim_stalk_eq_coheight] at e
      exact_mod_cast e
    obtain rfl : b = ξ := eq_of_specializes_of_coheight (hξ b hqb) h1 hξ1
    exact ⟨π, hπ, hqb, hξ, hd, hirr⟩
  choose! π hπ hqπ hsp hdvr hirr using key
  have hstar : ∀ b ∈ B, ∀ x : X, Order.coheight x = 1 → π b ∈ (q x).asIdeal → x = b := by
    intro b hb x hx hmem
    have hx0 : (q x).asIdeal ≠ ⊥ := fun h => (hπ b hb).ne_zero (by rw [h, Ideal.mem_bot] at hmem; exact hmem)
    obtain ⟨π', hπ', hqx⟩ := GlobalTheory.T.exists_prime_eq_span_of_coheight_le_one' R X q hgz x hx.le hx0
    have hdvd : π' ∣ π b := Ideal.mem_span_singleton.1 (hqx ▸ hmem)
    have hq : (q x).asIdeal = Ideal.span {π b} :=
      hqx.trans (Ideal.span_singleton_eq_span_singleton.2 (hπ'.associated_of_dvd (hπ b hb) hdvd))
    exact eq_of_specializes_of_coheight (hsp b hb x hq) hx hb.1
  have hne : ∀ b ∈ B, algebraMap R K (π b) ≠ 0 := fun b hb => (map_ne_zero_iff _ hinj).2 (hπ b hb).ne_zero
  have key2 : ∀ b ∈ B, ∃ (i : I) (n : ℤ), b ∈ U i ∧ UnitAt b (κ (algebraMap R K (π b)) ^ (-n) * t i) := by
    intro b hb
    obtain ⟨i, hi⟩ := hcov b
    have := hdvr b hb
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible (hirr b hb) (ht0 i b hi)
    have e : algebraMap _ X.functionField (X.presheaf.germ ⊤ b trivial (constFn q ⊤ (π b))) =
        κ (algebraMap R K (π b)) := by
      rw [hκ]; exact X.presheaf.germ_stalkSpecializes_apply _ _ _
    have hπ' : κ (algebraMap R K (π b)) ≠ 0 := (map_ne_zero κ).2 (hne b hb)
    refine ⟨i, n, hi, u, ?_⟩
    rw [hu, e, Units.smul_def, Algebra.smul_def, mul_left_comm, ← zpow_add₀ hπ', neg_add_cancel, zpow_zero,
      _root_.mul_one]
  have : Nonempty I := ⟨(hcov (genericPoint X)).choose⟩
  choose! ib n hUi hunitb using key2
  let F := hB.toFinset
  let a : Kˣ := ∏ b ∈ F.attach, (Units.mk0 _ (hne b.1 (hB.mem_toFinset.1 b.2))) ^ (-n b.1)
  have hκa : κ (a : K) = ∏ b ∈ F, κ (algebraMap R K (π b)) ^ (-n b) := by
    simp only [a, Units.coe_prod, map_prod, Units.val_zpow_eq_zpow_val, map_zpow₀, Units.val_mk0]
    exact Finset.prod_attach F (fun b => κ (algebraMap R K (π b)) ^ (-n b))
  refine ⟨a, fun i x hx h1 => ?_⟩
  rw [hκa]
  have hother : ∀ b ∈ F, b ≠ x → UnitAt x (κ (algebraMap R K (π b)) ^ (-n b)) := fun b hb hbx =>
    (hunit x (π b) fun hm => hbx (hstar b (hB.mem_toFinset.1 hb) x h1 hm).symm).zpow _
  by_cases hxS : x ∈ S
  · obtain ⟨j, hj, hu⟩ := hxS
    refine htr i j x _ hx hj ((UnitAt.prod F _ fun b hb => hother b hb ?_).mul hu)
    rintro rfl
    exact (hB.mem_toFinset.1 hb).2 ⟨j, hj, hu⟩
  · have hxB : x ∈ B := ⟨h1, hxS⟩
    have hxF : x ∈ F := hB.mem_toFinset.2 hxB
    rw [← Finset.mul_prod_erase F (fun b => κ (algebraMap R K (π b)) ^ (-n b)) hxF]
    refine htr i (ib x) x _ hx (hUi x hxB) ?_
    rw [mul_comm (κ (algebraMap R K (π x)) ^ (-n x)), mul_assoc]
    exact (UnitAt.prod _ _ fun b hb => hother b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)).mul
      (hunitb x hxB)

end GlobalTheory.VerticalUnit
end
end
