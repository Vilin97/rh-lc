module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.RingTheory.Kaehler.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.AlgebraicGeometry.Morphisms.Etale

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKaehlerEqOfUniversalTangent

section

@[expose] public section

open TrivSqZeroExt

namespace GlobalTheory

theorem finrank_kaehler_eq_of_universal_tangent :
    ∀ (R A k : Type) [CommRing R] [CommRing A] [Algebra R A] [Field k] (n d : ℕ)
    [Module.Free A (Ω[A⁄R])] [Module.Finite A (Ω[A⁄R])], Module.finrank A (Ω[A⁄R]) = n →
    ∀ (φ : A →+* k) (ψ : A →+* TrivSqZeroExt k (Fin d → k)),
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ →
    ψ.comp (algebraMap R A) = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (algebraMap R A)) →
    (∀ v : A →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
      v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) →
      ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ) → d = n := by
  intro R A k _ _ _ _ n d _ _ hn φ ψ hfst hR huniv
  classical
  haveI : Nontrivial A := φ.domain_nontrivial
  letI : Algebra A k := φ.toAlgebra
  letI : Algebra R k := (φ.comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A k := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hψf : ∀ a, (ψ a).fst = φ a := fun a => by
    simpa using RingHom.congr_fun hfst a
  have hψR : ∀ r, (ψ (algebraMap R A r)).snd = 0 := fun r => by
    have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hR r)
    simpa [TrivSqZeroExt.algebraMap_eq_inl] using this
  have hsA : ∀ (a : A) (x : k), a • x = φ a * x := fun a x => rfl
  have hsR : ∀ (r : R) (x : k), r • x = φ (algebraMap R A r) * x := fun r x => rfl

  let E : Derivation R A (Fin d → k) := Derivation.mk'
    { toFun := fun a => (ψ a).snd
      map_add' := fun a b => by simp
      map_smul' := fun r a => by
        funext i
        simp [Algebra.smul_def, hψR, hψf, hsR, RingHom.algebraMap_toAlgebra] }
    (fun a b => by
      funext i
      simp [hψf, hsA, mul_comm])
  have hE : ∀ a, E a = (ψ a).snd := fun a => rfl
  let El : Ω[A⁄R] →ₗ[A] (Fin d → k) := E.liftKaehlerDifferential
  have hEl : ∀ a, El (KaehlerDifferential.D R A a) = (ψ a).snd := fun a => by
    simp [El, hE]
  let b : Module.Basis (Fin n) A (Ω[A⁄R]) := Module.finBasisOfFinrankEq A _ hn
  have hcA : ∀ (c : (Fin d → k) →ₗ[k] k) (a : A) (x : Fin d → k), c (a • x) = a • c x :=
    fun c a x => by
      have : a • x = φ a • x := rfl
      rw [this, c.map_smul]; rfl
  let cA : ((Fin d → k) →ₗ[k] k) → ((Fin d → k) →ₗ[A] k) := fun c =>
    { toFun := c, map_add' := c.map_add, map_smul' := hcA c }
  have hcA' : ∀ c x, cA c x = c x := fun _ _ => rfl
  have hc1 : ∀ c : (Fin d → k) →ₗ[k] k,
      (TrivSqZeroExt.fstHom k k k).toRingHom.comp ((TrivSqZeroExt.map c).toRingHom.comp ψ) = φ :=
    fun c => by
      ext a
      simp [hψf]
  have hc2 : ∀ c : (Fin d → k) →ₗ[k] k,
      ((TrivSqZeroExt.map c).toRingHom.comp ψ).comp (algebraMap R A) =
        (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) := fun c => by
    ext r
    · simp [hψf, TrivSqZeroExt.algebraMap_eq_inl]
    · simp [hψR, TrivSqZeroExt.algebraMap_eq_inl]
  let L : ((Fin d → k) →ₗ[k] k) →ₗ[k] (Fin n → k) :=
    LinearMap.pi (fun i => LinearMap.applyₗ (R := k) (El (b i)))
  have hL : ∀ c i, L c i = c (El (b i)) := fun _ _ => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have h0 : (cA c).comp El = 0 := b.ext fun i => by
      simpa [hL, hcA'] using congrFun hc i
    have h0' : ∀ a, c (ψ a).snd = 0 := fun a => by
      have := LinearMap.congr_fun h0 (KaehlerDifferential.D R A a)
      simpa [hEl, hcA'] using this
    have heq : (TrivSqZeroExt.map c).toRingHom.comp ψ = (TrivSqZeroExt.map 0).toRingHom.comp ψ := by
      ext a
      · simp
      · simp [h0']
    exact (huniv _ (hc1 c) (hc2 c)).unique rfl heq
  have hsurj : Function.Surjective L := by
    intro f
    let g : Ω[A⁄R] →ₗ[A] k := b.constr A f
    let Df : Derivation R A k := g.compDer (KaehlerDifferential.D R A)
    let v : A →+* DualNumber k :=
      { toFun := fun a => TrivSqZeroExt.inl (φ a) + TrivSqZeroExt.inr (Df a)
        map_one' := by ext <;> simp
        map_mul' := fun a a' => by ext <;> simp [hsA, mul_comm, add_comm]
        map_zero' := by ext <;> simp
        map_add' := fun a a' => by ext <;> simp [add_add_add_comm] }
    have hv1 : (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ := by
      ext a
      simp [v]
    have hv2 : v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) := by
      ext r
      · simp [v, TrivSqZeroExt.algebraMap_eq_inl]
      · simp [v, TrivSqZeroExt.algebraMap_eq_inl]
    obtain ⟨c, hc, -⟩ := huniv v hv1 hv2
    have key : ∀ a, Df a = c (ψ a).snd := fun a => by
      have := congrArg TrivSqZeroExt.snd (RingHom.congr_fun hc a)
      simpa [v] using this
    have hg : (cA c).comp El = g := Derivation.liftKaehlerDifferential_unique _ _
      (Derivation.ext fun a => by simp [hEl, hcA', ← key, Df])
    refine ⟨c, funext fun i => ?_⟩
    rw [hL, ← hcA' c, ← LinearMap.comp_apply, hg]
    simp [g]
  have e := (LinearEquiv.ofBijective L ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_linearMap, Module.finrank_fin_fun, Module.finrank_fin_fun, Module.finrank_self] at e
  simpa using e

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKaehlerEqOfUniversalTangentStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.eq_of_universal_tangent_dualNumber : ∀ (R A k : Type) [CommRing R] [CommRing A] [Algebra R A] [Field k] (n d : ℕ)
    [Module.Free A (Ω[A⁄R])] [Module.Finite A (Ω[A⁄R])], Module.finrank A (Ω[A⁄R]) = n →
    ∀ (φ : A →+* k) (ψ : A →+* TrivSqZeroExt k (Fin d → k)),
    (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ →
    ψ.comp (algebraMap R A) = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (algebraMap R A)) →
    (∀ v : A →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
      v.comp (algebraMap R A) = (algebraMap k (DualNumber k)).comp (φ.comp (algebraMap R A)) →
      ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ) → d = n := by
  first | exact @GlobalTheory.finrank_kaehler_eq_of_universal_tangent | exact GlobalTheory.finrank_kaehler_eq_of_universal_tangent | (intros; apply GlobalTheory.finrank_kaehler_eq_of_universal_tangent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstOrderPointIffRingHomAffineOpenSectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.firstOrderPoint_iff_ringHom_affineOpen_sections : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (U : (Sp B).Opens) (V : X.Opens),
    IsAffineOpen U → IsAffineOpen V → ∀ (e : V ≤ s ⁻¹ᵁ U) (d : ℕ) (k : Type) [Field k] (x : Sp k ⟶ X),
    Set.range x.base ⊆ (V : Set X) → (∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) →
    ∃ (φ : Γ(X, V) →+* k) (ψ : Γ(X, V) →+* TrivSqZeroExt k (Fin d → k)),
      (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom.comp ψ = φ ∧
      ψ.comp (s.appLE U V e).hom = (algebraMap k (TrivSqZeroExt k (Fin d → k))).comp (φ.comp (s.appLE U V e).hom) ∧
      ∀ v : Γ(X, V) →+* DualNumber k, (TrivSqZeroExt.fstHom k k k).toRingHom.comp v = φ →
        v.comp (s.appLE U V e).hom = (algebraMap k (DualNumber k)).comp (φ.comp (s.appLE U V e).hom) →
        ∃! c : (Fin d → k) →ₗ[k] k, v = (TrivSqZeroExt.map c).toRingHom.comp ψ := by
  first | exact @GlobalTheory.SchRing.deformation_on_sections | exact GlobalTheory.SchRing.deformation_on_sections | (intros; apply GlobalTheory.SchRing.deformation_on_sections <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfUniversalFirstOrderTa

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SmoothDimTangent

theorem smoothOfRelativeDimension_of_universal_tangent : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (d : ℕ), Smooth s → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), ∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) → SmoothOfRelativeDimension d s := by
  intro B _ X s d hs H
  have loc : ∀ p : X, ∃ W : X.Opens, p ∈ W ∧ SmoothOfRelativeDimension d (W.ι ≫ s) := by
    intro p
    obtain ⟨U, hU, V, hV, hx, e, h⟩ := Smooth.exists_isStandardSmooth s p
    let _ := (s.appLE U V e).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V) := h
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    have hP : Algebra.IsStandardSmoothOfRelativeDimension P.dimension Γ(Sp B, U) Γ(X, V) := ⟨_, _, _, ‹_›, P, rfl⟩
    let k := AlgebraicClosure (X.residueField p)
    let x : Sp k ⟶ X := spMap (algebraMap (X.residueField p) k) ≫ X.fromSpecResidueField p
    have hr : Set.range x.base ⊆ (V : Set X) := by
      rintro _ ⟨y, rfl⟩
      have : x.base y ∈ Set.range (X.fromSpecResidueField p).base := ⟨_, (Scheme.Hom.comp_apply _ _ y).symm⟩
      rw [Scheme.range_fromSpecResidueField] at this
      rw [Set.mem_singleton_iff.1 this]
      exact hx
    obtain ⟨φ, ψ, h1, h2, h3⟩ := GlobalTheory.T.firstOrderPoint_iff_ringHom_affineOpen_sections B X s U V hU hV e d k x hr (H k x)
    have : Nontrivial Γ(X, V) := φ.domain_nontrivial
    have : Algebra.IsStandardSmooth Γ(Sp B, U) Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth P.dimension
    have : Module.Free Γ(X, V) Ω[Γ(X, V)⁄Γ(Sp B, U)] := Algebra.IsStandardSmooth.free_kaehlerDifferential
    have hrank : Module.finrank Γ(X, V) (Ω[Γ(X, V)⁄Γ(Sp B, U)]) = P.dimension :=
      Module.finrank_eq_of_rank_eq hP.rank_kaehlerDifferential
    have hd : d = P.dimension := GlobalTheory.T.eq_of_universal_tangent_dualNumber _ _ k P.dimension d hrank φ ψ h1 h2 h3
    have h' : RingHom.IsStandardSmoothOfRelativeDimension P.dimension (s.appLE U V e).hom := hP
    have : IsAffine U := hU
    have : IsAffine V := hV
    have : SmoothOfRelativeDimension P.dimension (s.resLE U V e) :=
      (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension P.dimension)).2
        (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
          ((RingHom.isStandardSmoothOfRelativeDimension_respectsIso.arrow_mk_iso_iff (arrowResLEAppIso s U V e)).2 h'))
    have : SmoothOfRelativeDimension (P.dimension + 0) (V.ι ≫ s) := by
      rw [← Scheme.Hom.resLE_comp_ι s e]; infer_instance
    refine ⟨V, hx, ?_⟩
    rw [hd]; exact this
  choose W hW hd using loc
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) := HasRingHomProperty.instIsZariskiLocalAtSource
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) hd

end GlobalTheory.SmoothDimTangent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfUniversalFirstOrderTaStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_of_universal_firstOrder_tangent : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (s : X ⟶ Sp B) (d : ℕ), Smooth s → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), ∃ u : Sp (TrivSqZeroExt k (Fin d → k)) ⟶ X, spMap (TrivSqZeroExt.fstHom k k (Fin d → k)).toRingHom ≫ u = x ∧ u ≫ s = spMap (algebraMap k (TrivSqZeroExt k (Fin d → k))) ≫ x ≫ s ∧ ∀ v : Sp (DualNumber k) ⟶ X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = x → v ≫ s = spMap (algebraMap k (DualNumber k)) ≫ x ≫ s → ∃! c : (Fin d → k) →ₗ[k] k, v = spMap (TrivSqZeroExt.map c).toRingHom ≫ u) → SmoothOfRelativeDimension d s := by
  first | exact @GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent | exact GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent | (intros; apply GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent <;> assumption)
end
end
