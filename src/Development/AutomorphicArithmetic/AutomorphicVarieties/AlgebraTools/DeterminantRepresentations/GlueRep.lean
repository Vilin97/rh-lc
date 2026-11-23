module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCoefMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Descend
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepCont
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.AmitsurSub

section

@[expose] public section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.amitsurSub :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
    AddMonoidAlgebra.coeff (D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) β ∈
      Subring.closure {a | ∃ i ≤ n, ∃ s : G, a = D.lam i (MonoidAlgebra.single s 1)} := by
  intro n A G _ _ D m g β
  have h := UpperTheory.V.CA.d_coef_mem D.toDet (MonoidHom.mrange (MonoidAlgebra.of A G))
    (Subring.closure {a | ∃ i ≤ n, ∃ s : G, a = D.lam i (MonoidAlgebra.single s 1)})
    (by
      rintro x ⟨s, rfl⟩ i - h2
      rw [(UpperTheory.V.CA.d_toDet D _).2.1]
      exact Subring.subset_closure ⟨i, h2, s, rfl⟩)
    (fun j => MonoidAlgebra.single (g j) 1) (fun j => ⟨g j, rfl⟩) β
  have e : D.toDet.poly (fun j => MonoidAlgebra.single (g j) (1 : A)) =
      D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1) := by
    change D.D _ (ofT A G _ (Det.gen _)) = _
    congr 1

    simp only [Det.gen, GDet.gen, map_sum, ofT_tmul, MvPolynomial.algebraMap_eq]
  rwa [e] at h
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.DescendLam

section

@[expose] public section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.descendLam :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] {A' : Type} [CommRing A'] (ι : A →+* A') (D' : GDet n A' G), Function.Injective ι →
    (∀ i ≤ n, ∀ g : G, D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range) → ∃! D : GDet n A G, D.map ι = D' := by
  intro n A G _ _ A' _ ι D' hι h
  refine UpperTheory.V.AlgebraTools.Det.descend ι D' hι fun m g β => ?_
  refine (Subring.closure_le (t := ι.range)).2 ?_ (UpperTheory.V.AlgebraTools.Det.amitsurSub D' m g β)
  rintro a ⟨i, hi, s, rfl⟩
  exact h i hi s
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Imports

section

@[expose] public section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.glue :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [CompactSpace A] [TopologicalSpace G] {A' : Type} [CommRing A'] [TopologicalSpace A'] [T2Space A']
    (ι : A →+* A') (D' : GDet n A' G) (S : Set G), Continuous ι → Function.Injective ι → Dense S →
    (∀ i ≤ n, Continuous fun g : G => D'.lam i (MonoidAlgebra.single g 1)) →
    (∀ g ∈ S, ∀ i ≤ n, D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range) →
    ∃ D : GDet n A G, D.map ι = D' ∧ ∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ A' _ _ _ ι D' S hι hinj hS hcont hmem
  have hemb := hι.isClosedEmbedding hinj
  have hall : ∀ i ≤ n, ∀ g : G, D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range := by
    intro i hi g
    have hcl : IsClosed {g : G | D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range} := by
      have hr : IsClosed (Set.range ι) := hemb.isClosed_range
      rw [← RingHom.coe_range] at hr
      exact hr.preimage (hcont i hi)
    have hsub : S ⊆ {g : G | D'.lam i (MonoidAlgebra.single g 1) ∈ ι.range} :=
      fun g hg => hmem g hg i hi
    have h1 := closure_minimal hsub hcl
    rw [hS.closure_eq] at h1
    exact h1 (Set.mem_univ g)
  obtain ⟨D, hD, -⟩ := UpperTheory.V.AlgebraTools.Det.descendLam ι D' hinj hall
  refine ⟨D, hD, fun i hi => ?_⟩
  rw [hemb.isEmbedding.continuous_iff]
  have heq : (⇑ι ∘ fun g : G => D.lam i (MonoidAlgebra.single g 1)) =
      fun g => D'.lam i (MonoidAlgebra.single g 1) := by
    funext g
    simp only [Function.comp]
    have hchi : ∀ y, (D.map ι).chi (MonoidAlgebra.mapRingHom G ι y) = (D.chi y).map ι := by
      intro y
      have e : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.mapRingHom G ι y) =
          MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom ι) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y) := by
        rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
          ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
          ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
      show (D.map ι).D A'[X] _ = _
      rw [e]
      have hφ : ∀ a, Polynomial.mapRingHom ι (algebraMap A A[X] a) = algebraMap A' A'[X] (ι a) := by
        intro a
        simp
      let : Algebra A A'[X] := ((algebraMap A' A'[X]).comp ι).toAlgebra
      exact D.nat A[X] A'[X] { Polynomial.mapRingHom ι with commutes' := hφ } _
    have hlam : ∀ i y, (D.map ι).lam i (MonoidAlgebra.mapRingHom G ι y) = ι (D.lam i y) := by
      intro i y
      simp only [GDet.lam, hchi, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
    have hs : (D.map ι).lam i (MonoidAlgebra.single g 1) = ι (D.lam i (MonoidAlgebra.single g 1)) := by
      simpa using hlam i (MonoidAlgebra.single g 1)
    rw [← hs, hD]
  rw [heq]
  exact hcont i hi
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.GlueRep

section

@[expose] public section

open Polynomial UpperTheory.V.W

private def UpperTheory.V.AlgebraTools.Det.piRep {n : ℕ} {G X : Type} [Group G] (K : X → Type) [∀ x, CommRing (K x)]
    (ρ : ∀ x, G →* Matrix (Fin n) (Fin n) (K x)) : G →* Matrix (Fin n) (Fin n) (∀ x, K x) where
  toFun g := Matrix.of fun i j x => ρ x g i j
  map_one' := by
    ext i j x
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  map_mul' g h := by
    ext i j x
    simp [Matrix.mul_apply, Finset.sum_apply]

theorem UpperTheory.V.AlgebraTools.Det.glueRep :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [CompactSpace A] [TopologicalSpace G] {X : Type} (K : X → Type) [∀ x, CommRing (K x)]
    [∀ x, TopologicalSpace (K x)] [∀ x, IsTopologicalRing (K x)] [∀ x, T2Space (K x)] (f : ∀ x, A →+* K x)
    (ρ : ∀ x, G →* Matrix (Fin n) (Fin n) (K x)) (S : Set G), (∀ x, Continuous (f x)) → (∀ a, (∀ x, f x a = 0) → a = 0) → Dense S →
    (∀ x, Continuous (ρ x)) → (∀ g ∈ S, ∃ p : A[X], ∀ x, p.map (f x) = (ρ x g).charpoly) →
    ∃ D : GDet n A G, (∀ x, D.map (f x) = GDet.ofRep (ρ x)) ∧ ∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1) := by
  intro n A G _ _ _ _ _ X K _ _ _ _ f ρ S hf hinj hS hρ hp
  let ι : A →+* (∀ x, K x) := Pi.ringHom f
  have hιc : Continuous ι := continuous_pi fun x => hf x
  have hιi : Function.Injective ι := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    exact hinj a fun x => congrFun ha x
  let R := UpperTheory.V.AlgebraTools.Det.piRep K ρ
  have hR : Continuous R := by
    apply continuous_matrix
    intro i j
    apply continuous_pi
    intro x
    exact ((hρ x).matrix_elem i j)
  obtain ⟨D, hD, hDc⟩ := UpperTheory.V.AlgebraTools.Det.glue ι (GDet.ofRep R) S hιc hιi hS
    (fun i _ => UpperTheory.V.AlgebraTools.Det.repCont R hR i)
    (by
      intro g hg i _
      obtain ⟨p, hp⟩ := hp g hg
      have hchar : (R g).charpoly = p.map ι := by
        ext k x
        have h1 := congrArg (fun q : (K x)[X] => q.coeff k)
          (Matrix.charpoly_map (R g) (Pi.evalRingHom K x))
        have h2 : (R g).map (Pi.evalRingHom K x) = ρ x g := by
          ext i j
          rfl
        rw [h2, ← hp x, Polynomial.coeff_map, Polynomial.coeff_map] at h1
        rw [Polynomial.coeff_map]
        exact h1.symm
      refine ⟨(-1) ^ i * p.coeff (n - i), ?_⟩
      show ι ((-1) ^ i * p.coeff (n - i)) = (-1) ^ i * ((GDet.ofRep R).chi (MonoidAlgebra.single g 1)).coeff (n - i)
      rw [(UpperTheory.V.AlgebraTools.Det.repApi R).2.1 g, hchar, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one])
  refine ⟨D, ?_, hDc⟩
  intro x
  have hfx : f x = (Pi.evalRingHom K x).comp ι := by
    ext a
    rfl
  rw [hfx, ← (UpperTheory.V.AlgebraTools.Det.mapApi D ι).2.2.2.2.2.2.1 (Pi.evalRingHom K x), hD, (UpperTheory.V.AlgebraTools.Det.repApi R).2.2.2.2.2.1 (Pi.evalRingHom K x)]
  congr 1
end
end
