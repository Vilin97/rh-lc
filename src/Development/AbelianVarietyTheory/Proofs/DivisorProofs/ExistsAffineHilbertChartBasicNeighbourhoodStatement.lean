module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertCoordinateMapBasicOpenBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertCoordinateMapRestrictBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsBasisSpanEqTopStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEmbeddingBijectiveLocalizedModuleMapOfRankStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsFiniteFlat

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem sec_finite_flat (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) :
    Module.Finite Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) ∧ Module.Flat Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) := by
  obtain ⟨h1, h2, -⟩ := y.2.2
  haveI : IsFinite (subStr A B y) := h1
  haveI : Flat (subStr A B y) := h2
  constructor
  · exact IsFinite.finite_app (subStr A B y) W W.2
  · have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := W.2.preimage (subStr A B y)
    have h := Scheme.Hom.flat_appLE (subStr A B y) W.2 hV le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at h
    exact h

end GlobalTheory.HilbAff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsFiniteFlatStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.affineHilbertSections_finite_flat : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens), Module.Finite Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) ∧ Module.Flat Γ(Z, W) (GlobalTheory.HilbAff.Sec A B y W) := by
  first | (exact @GlobalTheory.HilbAff.sec_finite_flat) | (exact GlobalTheory.HilbAff.sec_finite_flat) | (intros; apply GlobalTheory.HilbAff.sec_finite_flat  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsRankAtStalk

section

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

theorem isPullback_fromSpec_app_rank {X Y : Scheme.{0}} (π : X ⟶ Y) {W : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen (π ⁻¹ᵁ W)) :
    IsPullback hV.fromSpec (Spec.map (π.app W)) π hW.fromSpec :=
  (IsOpenImmersion.isPullback _ _ _ _ (by
    rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec π hW hV]) (by simp)).flip

theorem rankAtStalk_sec (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ)
    (Z : Scheme.{0}) (y : (functor A B r).obj (op Z)) (W : Z.affineOpens)
    (P : PrimeSpectrum Γ(Z, W)) : Module.rankAtStalk (Sec A B y W) P = r := by
  obtain ⟨_hfin, _hflat, h3⟩ := y.2.2
  have hW : IsAffineOpen (W : Z.Opens) := W.2
  have hV : IsAffineOpen (subStr A B y ⁻¹ᵁ (W : Z.Opens)) := hW.preimage _
  haveI : Module.Finite Γ(Z, W) (Sec A B y W) := by
    have := IsFinite.finite_app (subStr A B y) (W : Z.Opens) hW
    exact this
  haveI : Module.Flat Γ(Z, W) (Sec A B y W) := by
    have := Scheme.Hom.flat_appLE (subStr A B y) hW hV le_rfl
    rw [Scheme.Hom.appLE_eq_app] at this
    exact this
  have e := Scheme.Hom.finrank_of_isPullback _ _ _ _
    (isPullback_fromSpec_app_rank (subStr A B y) hW hV) P
  rw [h3] at e
  rw [← Scheme.Hom.finrank_SpecMap_algebraMap]
  exact e

end GlobalTheory.HilbAff
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsRankAtStalkStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.affineHilbertSections_rankAtStalk : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) (P : PrimeSpectrum Γ(Z, W)), Module.rankAtStalk (GlobalTheory.HilbAff.Sec A B y W) P = r := by
  first | (exact @GlobalTheory.HilbAff.rankAtStalk_sec) | (exact GlobalTheory.HilbAff.rankAtStalk_sec) | (intros; apply GlobalTheory.HilbAff.rankAtStalk_sec  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertCoordinateMapBijectiveOfLeAffine

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem coord_bijective_of_le_affine : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W W' : Z.affineOpens), (W' : Z.Opens) ≤ W → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W) → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W') := by
  intro A B _ _ _ N r e σ Z y W W' hle hW
  have hbas : ∀ f : Γ(Z, W), Function.Bijective (coord A B e σ y (Z.basicOpen f)) := by
    intro f
    rw [GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W f]
    exact ⟨LocalizedModule.map_injective _ _ hW.1, LocalizedModule.map_surjective _ _ hW.2⟩
  let s : Set Γ(Z, W') := {g | Function.Bijective (coord A B e σ y (Z.basicOpen g))}
  have hspan : Ideal.span s = ⊤ := by
    rw [← W'.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter W.2 W'.2 x ⟨hle hx, hx⟩
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, ?_⟩, ?_⟩
    · show Function.Bijective _
      rw [← hfg]; exact hbas f
    · show x ∈ Z.basicOpen g
      rw [← hfg]; exact hxf
  exact bijective_of_localized_span s hspan _ fun g => (GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W' g.1).1 g.2

end GlobalTheory.HilbAff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertCoordinateMapBijectiveOfLeAffineStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.hilbertCoordinateMap_bijective_of_le_affine : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W W' : Z.affineOpens), (W' : Z.Opens) ≤ W → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W) → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W') := by
  first | (exact @GlobalTheory.HilbAff.coord_bijective_of_le_affine) | (exact GlobalTheory.HilbAff.coord_bijective_of_le_affine) | (intros; apply GlobalTheory.HilbAff.coord_bijective_of_le_affine  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHilbertChartBasicNeighbourhood

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem exists_basic_nhd : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (z : Z), ∃ (σ : Fin r ↪ Fin N) (U : Z.Opens), z ∈ U ∧ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) := by
  intro A B _ _ _ N r e Z y z
  obtain ⟨W₀, hW₀, hzW₀, -⟩ := exists_isAffineOpen_mem_and_subset (show z ∈ (⊤ : Z.Opens) from trivial)
  let W : Z.affineOpens := ⟨W₀, hW₀⟩
  obtain ⟨hfin, hflat⟩ := GlobalTheory.T.affineHilbertSections_finite_flat A B r Z y W
  obtain ⟨σ, f, hf, hbij⟩ := GlobalTheory.T.exists_localizedModule_map_bijective_of_rankAtStalk_eq Γ(Z, W₀) (GlobalTheory.HilbAff.Sec A B y W) N r
    (fun j => GlobalTheory.HilbAff.gen A B y W (e j)) (GlobalTheory.T.affineHilbertSections_basis_span_eq_top A B N r e Z y W) (GlobalTheory.T.affineHilbertSections_rankAtStalk A B r Z y W)
    (hW₀.primeIdealOf ⟨z, hzW₀⟩)
  have hD := (GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W f).2 hbij
  have hzf : z ∈ Z.basicOpen f := by
    have h1 : hW₀.primeIdealOf ⟨z, hzW₀⟩ ∈ hW₀.fromSpec ⁻¹ᵁ Z.basicOpen f := by
      rw [hW₀.fromSpec_preimage_basicOpen]; exact hf
    have h2 := hW₀.fromSpec_primeIdealOf ⟨z, hzW₀⟩
    have h3 : hW₀.fromSpec (hW₀.primeIdealOf ⟨z, hzW₀⟩) ∈ Z.basicOpen f := h1
    rw [h2] at h3
    exact h3
  refine ⟨σ, Z.basicOpen f, hzf, ?_⟩
  rw [GlobalTheory.HilbAff.basic_iff]
  intro W'
  apply GlobalTheory.T.affineHilbertCoordinateMap_restrict_bijective
  exact GlobalTheory.T.hilbertCoordinateMap_bijective_of_le_affine A B N r e σ Z y ⟨Z.basicOpen f, hW₀.basicOpen f⟩
    ⟨_, W'.2.image_of_isOpenImmersion (Z.basicOpen f).ι⟩ (Scheme.Opens.ι_image_le _ _) hD

end GlobalTheory.HilbAff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineHilbertChartBasicNeighbourhoodStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

theorem _root_.GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (z : Z), ∃ (σ : Fin r ↪ Fin N) (U : Z.Opens), z ∈ U ∧ GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map U.ι.op y) := by
  first | (exact @GlobalTheory.HilbAff.exists_basic_nhd) | (exact GlobalTheory.HilbAff.exists_basic_nhd) | (intros; apply GlobalTheory.HilbAff.exists_basic_nhd  <;> assumption)
end
end
