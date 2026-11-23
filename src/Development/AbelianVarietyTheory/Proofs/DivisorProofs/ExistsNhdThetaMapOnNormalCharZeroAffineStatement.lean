module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsAtUniformisedTrait
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsGenSecNear
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapAffineNormalBaseUniversalGeneratorStatement
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeneratingSectionAllFibres

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_basicOpen_genSec_fibres : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB →
    ∀ (g : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), PolFib G L g x →
    ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧
      ∃ θ : SecAt G L (spMap (algebraMap R (Localization.Away r)) ≫ x),
        ∀ (K : Type) [Field K] (i : Localization.Away r →+* K), IsGenSec G L _ (SecAt.pull G L θ i) := by
  intro S G _ L hL g R _ _ x hx p
  obtain ⟨P, α, -, hp, w, hw⟩ := hx
  have hS : SecBaseChangeAnySt := GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny
  obtain ⟨V, hpV, hV⟩ := GlobalTheory.EmbLocal.exists_isGenSec_near hS P p
  obtain ⟨_, ⟨r, rfl⟩, hpr, hrV⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := ((V : Set (Sp R)) : Set (PrimeSpectrum R))) hpV V.isOpen
  let j := algebraMap R (Localization.Away r)
  have hrange : Set.range (spMap j) ⊆ (V : Set (Sp R)) := by
    intro y hy
    apply hrV
    obtain ⟨z, rfl⟩ := hy
    have hz : PrimeSpectrum.comap j z ∈ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨z, rfl⟩
    exact hz
  obtain ⟨th, hth⟩ := hV (Localization.Away r) (spMap j) hrange
  have hτ : (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) ≫
      (Over.mk (spMap j ≫ x)).hom = (Over.mk (spMap j)).hom ≫ x := Category.id_comp _
  obtain ⟨θ, hθ⟩ := GlobalTheory.ThetaPtMove.exists_secRel_up hp (T := Over.mk (spMap j)) (T₀ := Over.mk (spMap j ≫ x))
    (𝟙 _) hτ hw hL P.isLB (a := ((1 : ℕ) : ℤ)) th
  refine ⟨r, hpr, θ, fun K _ i => ?_⟩
  have hτ' : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫
      (Over.mk (spMap i ≫ spMap j ≫ x)).hom = (Over.mk (spMap i ≫ spMap j)).hom ≫ x := by
    simp [Category.assoc]
  let ξ : Over.mk (spMap i ≫ spMap j) ⟶ Over.mk (spMap j) := Over.homMk (spMap i) rfl
  let ξ₀ : Over.mk (spMap i ≫ spMap j ≫ x) ⟶ Over.mk (spMap j ≫ x) := Over.homMk (spMap i) rfl
  have hξ : (𝟙 (Sp K) : (Over.mk (spMap i ≫ spMap j)).left ⟶ (Over.mk (spMap i ≫ spMap j ≫ x)).left) ≫ ξ₀.left =
      ξ.left ≫ (𝟙 (Sp (Localization.Away r)) : (Over.mk (spMap j)).left ⟶ (Over.mk (spMap j ≫ x)).left) :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have hrel : GlobalTheory.ThetaPtMove.SecRel hp _ hτ' w (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th)
      (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.Ex.OneGen.SecRel.pullS hp _ hτ hθ (T' := Over.mk (spMap i ≫ spMap j))
      (T₀' := Over.mk (spMap i ≫ spMap j ≫ x)) _ hτ' ξ ξ₀ hξ
  have : IsAffine (Over.mk (spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap i ≫ spMap j)).left := inferInstanceAs (IsAffine (Spec _))
  have hg : IsGenSec P.A P.L 1 (VVRank.pullS P.A 1 ξ th) :=
    GlobalTheory.EmbPull.isGenSec_pullS P hS ξ hth
  have hg' : IsGenSec P.A P.L ((1 : ℕ) : ℤ) (VVRank.pullS P.A ((1 : ℕ) : ℤ) ξ th) := hg
  have : IsIso (C := Scheme.{0}) (X := (Over.mk (spMap i ≫ spMap j)).left)
      (Y := (Over.mk (spMap i ≫ spMap j ≫ x)).left) (𝟙 (Sp K)) := IsIso.id _
  have h2 : IsGenSec G L ((1 : ℕ) : ℤ) (VVRank.pullS G ((1 : ℕ) : ℤ) ξ₀ θ) :=
    GlobalTheory.ThetaPtUp.isGenSec_up hp _ hτ' hw hL P.isLB hrel hg'
  exact h2

end GlobalTheory.UMin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenGeneratingSectionAllFibresStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_basicOpen_generating_section_all_fibres : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → ∀ (g : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), PolFib G L g x → ∀ p : PrimeSpectrum R, ∃ r : R, r ∉ p.asIdeal ∧ ∃ θ : SecAt G L (spMap (algebraMap R (Localization.Away r)) ≫ x), ∀ (K : Type) [Field K] (i : Localization.Away r →+* K), IsGenSec G L _ (SecAt.pull G L θ i) := by
  first | exact @GlobalTheory.UMin.exists_basicOpen_genSec_fibres | exact GlobalTheory.UMin.exists_basicOpen_genSec_fibres | (intros; apply GlobalTheory.UMin.exists_basicOpen_genSec_fibres <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdThetaMapOnNormalCharZeroAffine

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem exists_nbhd_thetaMap : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    ∀ (U : X.affineOpens), IsDomain Γ(X, U) → IsNoetherianRing Γ(X, U) → IsIntegrallyClosed Γ(X, U) → CharZero Γ(X, U) →
    ∀ x ∈ (U : X.Opens), ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧ ThMap G L ρ m (W.ι ≫ q) h := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hu hn hP U hD hN hI hC x hx
  let R : Type := Γ(X, U)
  have hU : IsAffineOpen (U : X.Opens) := U.2

  let β : o →+* R := (Spec.preimage (hU.fromSpec ≫ s)).hom
  have hβ : spMap β = hU.fromSpec ≫ s := Spec.map_preimage _
  let p : PrimeSpectrum R := hU.primeIdealOf ⟨x, hx⟩
  obtain ⟨r, hr, θ, hθ⟩ := GlobalTheory.T.exists_basicOpen_generating_section_all_fibres S G L hL g R (hU.fromSpec ≫ q) (hP R hU.fromSpec) p
  let Rr := Localization.Away r
  have hr0 : r ≠ 0 := fun h => hr (h ▸ p.asIdeal.zero_mem)
  have hle : Submonoid.powers r ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hr0
  haveI : IsDomain Rr := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing Rr := IsLocalization.isNoetherianRing (Submonoid.powers r) Rr hN
  haveI : IsIntegrallyClosed Rr := isIntegrallyClosed_of_isLocalization Rr _ hle
  have hinj : Function.Injective (algebraMap R Rr) := IsLocalization.injective Rr hle
  haveI : CharZero Rr := charZero_of_injective_algebraMap hinj
  let β' : o →+* Rr := (algebraMap R Rr).comp β
  have hu' : IsUnit (m : Rr) := by
    have := hu.map β'
    simpa using this
  have hP' : PolFib G L g (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) := by
    have := hP Rr (spMap (algebraMap R Rr) ≫ hU.fromSpec)
    simpa [Category.assoc] using this
  obtain ⟨f, hf, hT⟩ := GlobalTheory.T.exists_thetaMap_affineNormalBase_universalGenerator S G L ρ hL hρ g m n o Rr β' (spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) θ
    hmo hm3 hu' hn hP' hθ

  let Wo : X.Opens := X.basicOpen r
  have hW : IsAffineOpen Wo := hU.basicOpen r
  have hxW : x ∈ Wo := by
    have h1 : hU.fromSpec p ∈ X.basicOpen r := by
      show p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen r
      rw [hU.fromSpec_preimage_basicOpen]; exact hr
    rwa [hU.fromSpec_primeIdealOf] at h1
  have hle' : Wo ≤ (U : X.Opens) := X.basicOpen_le r
  let res : R →+* Γ(X, Wo) := (X.presheaf.map (homOfLE hle').op).hom
  have hres : IsUnit (res r) := RingedSpace.isUnit_res_basicOpen X.toRingedSpace r
  let lft : Rr →+* Γ(X, Wo) := IsLocalization.Away.lift r hres
  have hlft : lft.comp (algebraMap R Rr) = res := IsLocalization.Away.lift_comp r hres
  let e : Wo.toScheme ⟶ Sp Rr := hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom lft)
  have he : e ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec = Wo.ι := by
    have : Spec.map (CommRingCat.ofHom lft) ≫ spMap (algebraMap R Rr) =
        Spec.map (X.presheaf.map (homOfLE hle').op) := by
      rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hlft]
      rfl
    simp only [e, Category.assoc]
    rw [reassoc_of% this, hU.map_fromSpec hW, hW.isoSpec_hom_fromSpec]
  refine ⟨Wo, e ≫ f, hxW, ?_, ?_⟩
  · rw [Category.assoc, hf, show spMap β' = spMap (algebraMap R Rr) ≫ spMap β from by
      rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl, hβ, ← he]
    simp only [Category.assoc]
  · intro K _ x' c hc
    have hc' : HasTh G L ρ m ((x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q) c := by
      have : (x' ≫ e) ≫ spMap (algebraMap R Rr) ≫ hU.fromSpec ≫ q = x' ≫ Wo.ι ≫ q := by
        rw [← he]; simp only [Category.assoc]
      rw [this]; exact hc
    have := hT K (x' ≫ e) c hc'
    simpa [Category.assoc] using this

end GlobalTheory.UMin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdThetaMapOnNormalCharZeroAffineStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_nhd_thetaMap_on_normal_charZero_affine : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    ∀ (U : X.affineOpens), IsDomain Γ(X, U) → IsNoetherianRing Γ(X, U) → IsIntegrallyClosed Γ(X, U) → CharZero Γ(X, U) →
    ∀ x ∈ (U : X.Opens), ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧ ThMap G L ρ m (W.ι ≫ q) h := by
  first | exact @GlobalTheory.UMin.exists_nbhd_thetaMap | exact GlobalTheory.UMin.exists_nbhd_thetaMap | (intros; apply GlobalTheory.UMin.exists_nbhd_thetaMap <;> assumption)
end
end
