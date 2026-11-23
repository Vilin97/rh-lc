module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyHomOfGraphsOverRingInvertingElement
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsInversionEndomorphismsThetaLevelFamily
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GraphInversionEndomorphismCutBoundedDegreeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjProperRelAmpleOfProjectiveCoordinateRepStatement
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.ExtremalEpi

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyHomOfGraphsOverRingInvertingElementStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

theorem _root_.GlobalTheory.T.exists_familyHom_of_graphs_over_ring_inverting_element : ∀ (R σ₁ σ₂ Hh : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] [Finite σ₁] [Finite σ₂] [Finite Hh] (Z₁ Z₂ : Over (Sp R)) (I₁ : Ideal (MvPolynomial σ₁ R)) (I₂ : Ideal (MvPolynomial σ₂ R)) (M₁ : LB Z₁.left) (M₂ : LB Z₂.left) (th₁ : σ₁ → M₁.Sec) (th₂ : σ₂ → M₂.Sec) (p₁ : Hh → σ₁ → R) (p₂ : Hh → σ₂ → R) (Q : Polynomial ℚ) (d : ℕ) (G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z₁.hom (spMap x) ⟶ Z₂.left) → Prop), ProjRep I₁ Z₁.hom M₁ th₁ → ProjRep I₂ Z₂.hom M₂ th₂ → IsProper Z₁.hom → IsProper Z₂.hom → Smooth Z₁.hom → (∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → φ ≫ Z₂.hom = pullback.snd _ _ ≫ spMap x ∧ CutBy (graphIdeal (pullback.snd Z₁.hom (spMap x)) M₁ th₁ (pullback.fst _ _) M₂ th₂ φ) Q d (fun h i => x (p₁ h i.1 * p₂ h i.2))) → DenseP {q | ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ} → ∀ (K₀ : Type) [Field K₀] (x₀ : R →+* K₀) φ₀, G K₀ x₀ φ₀ → ∃ f : R, x₀ f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Y : Scheme.{0}) (π : Y ⟶ Z₁.left) (sY : Y ⟶ Sp R'), π ≫ Z₁.hom = sY ≫ spMap ρ → ∃ F : Y ⟶ Z₂.left, F ≫ Z₂.hom = sY ≫ spMap ρ ∧ ∀ (K : Type) [Field K] (x : R →+* K) φ, G K x φ → ∀ io : pullback Z₁.hom (spMap x) ⟶ Y, io ≫ π = pullback.fst _ _ → φ = io ≫ F := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit | exact GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit | (intros; apply GlobalTheory.ZM.NearBuild.exists_hom_of_graphs_of_isUnit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEndomorphismsExtendNearGoodPrime

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild
open GlobalTheory.ZM.EndBuild

theorem exists_endomorphism_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R) (i : Option J), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ F : Z' ⟶ Z', EndOk b Mat κ β v (n ^ 2) M th sc ρ π i F := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.graph_inversion_endomorphism_cut_bounded_degree hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b R _ _ _ β v Z M th sc q₀ i hden hfam hsm => ?_⟩
  have : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨⟨I, p, hrep, hp⟩, -, hfib⟩ := hfam
  have hprop := (GlobalTheory.T.isProj_proper_relAmple_of_projectiveCoordinateRep R _ I Z M th hrep).2.1
  obtain ⟨Q, d, hQ⟩ := hj₀ j hj o b i
  let G : ∀ (K : Type) [Field K] (x : R →+* K), (pullback Z.hom (spMap x) ⟶ Z.left) → Prop := fun K _ x f =>
    ∃ (_ : IsAlgClosed K) (s : Sp K ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s) (φ : t.A.left ⟶ Z.left)
      (hφ : Fib (n ^ 2) M th sc x t φ), Good b Mat κ β v x t ∧
      f = hφ.1.isoPullback.inv ≫ (i.elim (𝟙 t.A)⁻¹ t.act : t.A ⟶ t.A).left ≫ φ
  have hG : ∀ q ∈ objPrimes b Mat κ β v,
      ∃ (K : Type) (_ : Field K) (x : R →+* K) (φ : _), RingHom.ker x = q ∧ G K x φ := by
    intro q hq
    obtain ⟨K, _, _, x, s, t, hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t ht
    exact ⟨K, inferInstance, x, _, hx, inferInstance, s, t, φ, hφ, ht, rfl⟩
  obtain ⟨K₀, _, x₀, φ₀, hx₀, hG₀⟩ := hG q₀ hden.2
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.exists_familyHom_of_graphs_over_ring_inverting_element R _ _ (Ix g ((n ^ j) ^ 2)) Z Z I I M M th th p (fun h => p (labMap _ Mat i h)) Q d G
    hrep hrep hprop hprop hsm (by
      rintro K _ x f ⟨_, s, t, φ, ⟨hφ, ⟨σ, hE, hσ⟩, hb, hl⟩, ⟨hs, ht, -⟩, rfl⟩
      refine ⟨?_, cut_fibre (m := n ^ 2) i Q d t ht σ ?_ Z M hrep.1 th sc p hp x φ hφ hσ hl⟩
      · rw [Category.assoc, Category.assoc, hφ.w, ← Category.assoc (Option.elim _ _ _ : t.A ⟶ t.A).left, Over.w,
          ← Category.assoc, IsPullback.isoPullback_inv_snd]
      · rw [← spMap_comp] at hs
        subst hs
        exact fun p' q' f hf h => hQ K (x.comp β) t σ p' q' f ht hf hE h)
    (fun r hr => hden.1 r fun q hq hqp => hr q (hG q hq) hqp) K₀ x₀ φ₀ hG₀
  refine ⟨f, fun h => hf (by rw [← hx₀] at h; exact h), fun R' _ ρ hu Z' π hpb => ?_⟩
  obtain ⟨F₀, hF₀, hF⟩ := H R' ρ hu Z'.left π Z'.hom hpb.w
  refine ⟨Over.homMk (hpb.lift F₀ Z'.hom hF₀) (hpb.lift_snd _ _ _), ?_⟩
  intro K _ _ x s t φ ht hφ hw
  have e := hF K (x.comp ρ) _ ⟨inferInstance, s, t, φ ≫ π, hφ, ht, rfl⟩ (hφ.1.isoPullback.inv ≫ φ)
    (by rw [Category.assoc, IsPullback.isoPullback_inv_fst])
  rw [Category.assoc, cancel_epi] at e
  refine hpb.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, e]
    exact congrArg (φ ≫ ·) (hpb.lift_fst _ _ _)
  · rw [Category.assoc, Category.assoc, Over.w, hw, ← Category.assoc, Over.w]

end GlobalTheory.ZM.NearBuild
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEndomorphismsExtendNearGoodPrimeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

theorem _root_.GlobalTheory.T.exists_endomorphisms_extend_near_good_prime : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R) (i : Option J), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ F : Z' ⟶ Z', EndOk b Mat κ β v (n ^ 2) M th sc ρ π i F := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_endomorphism_near | exact GlobalTheory.ZM.NearBuild.exists_endomorphism_near | (intros; apply GlobalTheory.ZM.NearBuild.exists_endomorphism_near <;> assumption)
end
end
