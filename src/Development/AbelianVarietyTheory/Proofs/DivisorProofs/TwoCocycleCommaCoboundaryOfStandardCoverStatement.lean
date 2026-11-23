module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueCommaOfBasis
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleInvertibleLocusIsCoboundary

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc.Basis

theorem oneCocycle_invertibleLocus_isCoboundary : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e y hy
  obtain ⟨L, l, hl, -, -, huniv⟩ := H T e
  have hunit : ∀ t (w : L ⟶ G.obj t), IsUnit (mp F (l ≫ w) e) := by
    intro t w
    rw [mp_comp]
    exact hl.map _
  obtain ⟨gL, hgL⟩ := oneCocycle_coboundary_comma_localBasis F G H hcov hdir L (fun t t' w a ↦ y t t' (l ≫ w) a)
    (fun t t' t'' w a b ↦ by
      have h := hy t t' t'' (l ≫ w) a b (hunit t w)
      rw [Category.assoc] at h
      exact h)
  classical
  refine ⟨fun t u ↦ if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0, ?_⟩
  have hg : ∀ t (u : T ⟶ G.obj t) (w : L ⟶ G.obj t), l ≫ w = u →
      (if h : ∃ w : L ⟶ G.obj t, l ≫ w = u then gL t h.choose else 0) = gL t w := by
    intro t u w hw
    have h : ∃ w : L ⟶ G.obj t, l ≫ w = u := ⟨w, hw⟩
    rw [dite_eq_left h]
    exact congrArg (gL t) (Subsingleton.elim _ _)
  intro t t' u a hu
  obtain ⟨w, hw, -⟩ := huniv (G.obj t) u hu
  have hw' : l ≫ (w ≫ G.map a) = u ≫ G.map a := by rw [← Category.assoc, hw]
  simp only []
  rw [hg t u w hw, hg t' (u ≫ G.map a) (w ≫ G.map a) hw', hgL t t' w a, hw]

end GlobalTheory.CatCoh.Desc.Basis
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleInvertibleLocusIsCoboundaryStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.oneCocycle_invertibleLocus_isCoboundary_alt : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  first | exact @GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary | exact GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary | (intros; apply GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsInvertibleLocusOfBasisFunctor

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

theorem sec_of_basis_unit : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : ∀ S, (T ⟶ S) → F.obj S, Desc.IsSec F (fun S u ↦ IsUnit (mp F u e)) x ∧ ∀ t (u : T ⟶ G.obj t), IsUnit (mp F u e) → x (G.obj t) u = s t u := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e s hs
  have uniq : ∀ (S : C) (y : F.obj S), (∀ t (w : S ⟶ G.obj t), mp F w y = 0) → y = 0 := by
    intro S y hy
    obtain ⟨n, b, hb, hb'⟩ := hcov S
    refine sep_std (H := H) (hb := hb) y fun S'' u' ⟨i, hi⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' i S'' u' hi
    rw [mp_comp, hy t v, map_zero]
  have hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, IsUnit (mp F u e) →
      ∀ t (w : S ⟶ G.obj t), mp F w y = s t (u ≫ w) := by
    intro S u
    by_cases h : IsUnit (mp F u e)
    · obtain ⟨y, hy⟩ := glue_comma_of_basis F G H hcov hdir S (fun t w ↦ s t (u ≫ w))
        fun t t' w a ↦ by
          rw [← Category.assoc]
          exact hs t t' (u ≫ w) a (isUnit_comp w h)
      exact ⟨y, fun _ ↦ hy⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose x hx using hex
  refine ⟨x, fun S S' u ψ hu ↦ sub_eq_zero.1 (uniq S' _ fun t w ↦ ?_), fun t u hu ↦ ?_⟩
  · rw [map_sub, hx S' (u ≫ ψ) (isUnit_comp ψ hu) t w, ← mp_comp, hx S u hu t (ψ ≫ w),
      Category.assoc, sub_self]
  · have := hx (G.obj t) u hu t (𝟙 _)
    rwa [mp_id, Category.comp_id] at this

end GlobalTheory.CatCoh.Desc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsInvertibleLocusOfBasisFunctorStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.sections_invertibleLocus_of_basisFunctor : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : ∀ S, (T ⟶ S) → F.obj S, Desc.IsSec F (fun S u ↦ IsUnit (mp F u e)) x ∧ ∀ t (u : T ⟶ G.obj t), IsUnit (mp F u e) → x (G.obj t) u = s t u := by
  first | exact @GlobalTheory.CatCoh.Desc.sec_of_basis_unit | exact GlobalTheory.CatCoh.Desc.sec_of_basis_unit | (intros; apply GlobalTheory.CatCoh.Desc.sec_of_basis_unit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCommaCoboundaryOfStandardCover

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CatCoh.Desc


open Classical in
theorem twoCocycle_comma_coboundary_of_standardCover : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → (∀ i : Fin n, ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u (d i)) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), (∃ i, IsUnit (mp F u (d i))) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  intro R _ C _ C' _ F G _ _ H hcov hfil T n d hd z hz hy
  choose y hy using hy
  have hu : ∀ {t t' : C'} {u : T ⟶ G.obj t} (a : t ⟶ t') {x : F.obj T}, IsUnit (mp F u x) →
      IsUnit (mp F (u ≫ G.map a) x) := fun a _ h ↦ isUnit_comp _ h
  have h1 := fun i j : Fin n ↦ GlobalTheory.T.oneCocycle_invertibleLocus_isCoboundary_alt F G H hcov hfil T (d i * d j)
    (fun t t' u a ↦ y j t t' u a - y i t t' u a) fun t t' t'' u a b h ↦ by
      rw [map_mul, IsUnit.mul_iff] at h
      rw [map_sub]
      linear_combination hy i t t' t'' u a b h.1 - hy j t t' t'' u a b h.2
  choose β hβ' using h1
  have hβ : ∀ i j t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u (d i)) →
      IsUnit (mp F u (d j)) →
      β i j t' (u ≫ G.map a) - mp F (G.map a) (β i j t u) = y j t t' u a - y i t t' u a :=
    fun i j t t' u a hi hj ↦ hβ' i j t t' u a (by rw [map_mul]; exact hi.mul hj)
  have h2 := fun i j k : Fin n ↦ GlobalTheory.T.sections_invertibleLocus_of_basisFunctor F G H hcov hfil T (d i * d j * d k)
    (fun t u ↦ β j k t u - β i k t u + β i j t u) fun t t' u a h ↦ by
      rw [map_mul, map_mul, IsUnit.mul_iff, IsUnit.mul_iff] at h
      rw [map_add (f := _), map_sub]
      linear_combination hβ j k t t' u a h.1.2 h.2 - hβ i k t t' u a h.1.1 h.2 +
        hβ i j t t' u a h.1.1 h.1.2
  choose x hx' hxs' using h2
  have hx : ∀ i j k, IsSec F (fun S u ↦ (IsUnit (mp F u (d i)) ∧ IsUnit (mp F u (d j))) ∧
      IsUnit (mp F u (d k))) (x i j k) := fun i j k S S' u ψ h ↦
    hx' i j k S S' u ψ (by
      show IsUnit _
      rw [map_mul, map_mul]; exact (h.1.1.mul h.1.2).mul h.2)
  have hxs : ∀ i j k t (u : T ⟶ G.obj t), IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      IsUnit (mp F u (d k)) → x i j k (G.obj t) u = β j k t u - β i k t u + β i j t u :=
    fun i j k t u hi hj hk ↦ hxs' i j k t u (by rw [map_mul, map_mul]; exact (hi.mul hj).mul hk)
  obtain ⟨e, he, he'⟩ := cech2 H hd x hx (fun l i j k S u hl hi hj hk ↦ by
    obtain ⟨m, b, hb, hb'⟩ := hcov S
    refine sep_std H hb _ fun S' ψ ⟨r, hr⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' r S' ψ hr
    have hl' := isUnit_comp v hl
    have hi' := isUnit_comp v hi
    have hj' := isUnit_comp v hj
    have hk' := isUnit_comp v hk
    rw [mp_comp, map_sub (mp F v), map_add (mp F v), map_sub (mp F v),
      ← hx i j k S _ u v ⟨⟨hi, hj⟩, hk⟩, ← hx l j k S _ u v ⟨⟨hl, hj⟩, hk⟩,
      ← hx l i k S _ u v ⟨⟨hl, hi⟩, hk⟩, ← hx l i j S _ u v ⟨⟨hl, hi⟩, hj⟩,
      hxs _ _ _ _ _ hi' hj' hk', hxs _ _ _ _ _ hl' hj' hk', hxs _ _ _ _ _ hl' hi' hk',
      hxs _ _ _ _ _ hl' hi' hj']
    ring_nf
    exact map_zero _)
  obtain ⟨γ, hγ⟩ : ∃ γ : Fin n → ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ i j t u,
      IsUnit (mp F u (d i)) → IsUnit (mp F u (d j)) →
      γ j t u - γ i t u = β i j t u - e i j (G.obj t) u := by
    refine ⟨fun i t u ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      β h.choose i t u - e h.choose i _ u else 0, fun i j t u hi hj ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    linear_combination -he' _ i j _ u h.choose_spec hi hj + hxs _ i j t u h.choose_spec hi hj
  obtain ⟨α, hα⟩ : ∃ α : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ i t t' u a,
      IsUnit (mp F u (d i)) →
      α t t' u a = y i t t' u a - (γ i t' (u ≫ G.map a) - mp F (G.map a) (γ i t u)) := by
    refine ⟨fun t t' u a ↦ if h : ∃ i, IsUnit (mp F u (d i)) then
      y h.choose t t' u a - (γ h.choose t' (u ≫ G.map a) - mp F (G.map a) (γ h.choose t u)) else 0,
      fun i t t' u a hi ↦ ?_⟩
    have h : ∃ i, IsUnit (mp F u (d i)) := ⟨i, hi⟩
    simp only [dif_pos h]
    have k1 := congrArg (mp F (G.map a)) (hγ i _ t u hi h.choose_spec)
    have k2 := hγ i _ t' (u ≫ G.map a) (hu a hi) (hu a h.choose_spec)
    have k3 := he i _ _ _ u (G.map a) ⟨hi, h.choose_spec⟩
    have k4 := hβ i _ t t' u a hi h.choose_spec
    simp only [map_sub] at k1
    linear_combination k1 - k2 + k3 - k4
  refine ⟨α, fun t t' t'' u a b ⟨i, hi⟩ ↦ ?_⟩
  rw [hα i _ _ _ _ hi, hα i _ _ _ _ hi, hα i _ _ _ _ (hu a hi)]
  simp only [map_sub, mp_comp, Category.assoc, G.map_comp]
  linear_combination hy i t t' t'' u a b hi

end GlobalTheory.CatCoh.Desc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCommaCoboundaryOfStandardCoverStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

theorem _root_.GlobalTheory.T.twoCocycle_comma_coboundary_of_standardCover_alt : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (n : ℕ) (d : Fin n → F.obj T), Ideal.span (Set.range d) = ⊤ → ∀ (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → F.obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp F (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → (∀ i : Fin n, ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u (d i)) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), (∃ i, IsUnit (mp F u (d i))) → mp F (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b := by
  first | exact @GlobalTheory.CatCoh.Desc.twoCocycle_comma_coboundary_of_standardCover | exact GlobalTheory.CatCoh.Desc.twoCocycle_comma_coboundary_of_standardCover | (intros; apply GlobalTheory.CatCoh.Desc.twoCocycle_comma_coboundary_of_standardCover <;> assumption)
end
end
