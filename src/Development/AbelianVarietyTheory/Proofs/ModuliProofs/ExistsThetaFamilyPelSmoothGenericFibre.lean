module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteTypeOfIsQProjOverAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankTangentPELFamilyLeSymmetricDomain
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
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGoodThetaComplexClassUnitaryFullLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPELPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyOverThetaPointSchemeStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaCoordinateSchemeData
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBaseStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullbackStatement
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalProperty
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneousStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibresStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinrankTangentPELFamilyLeSymmetricDomainStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.finrank_tangent_PEL_family_le_symmetricDomain : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (ρ : o) (R : Type) [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (t : TObj g (N' ^ 2) J b (spMap (algebraMap o R))) (τ : SAB H (Sp R)), ρ ^ 2 = -(H.d : o) → IsPEL D a bas ρ t τ → Algebra.FiniteType o R → (∀ (x : Sp (DualNumber ℂ) ⟶ Sp R) (t' : TObj g (N' ^ 2) J b (x ≫ spMap (algebraMap o R))), x ≫ spMap (algebraMap o R) = constPt x ≫ spMap (algebraMap o R) → TMap t' t x → TMap t' t (constPt x) → x = constPt x) → Module.finrank ℂ (Derivation o R ℂ) ≤ D.dim := by
  first | exact @GlobalTheory.PelTan.finrank_derivation_le | exact GlobalTheory.PelTan.finrank_derivation_le | (intros; apply GlobalTheory.PelTan.finrank_derivation_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentVectorZeroOfObjectConstantAlong

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem tangent_eq_constPt_of_tMap : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (u : TObj g (N' ^ 2) J b Y.s), Odd N' → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ Y.MM) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), x ≫ Y.s = constPt x ≫ Y.s → TMap t u x → TMap t u (constPt x) → x = constPt x := by
  intro hL hL2 o _ g n N' J b I Y u hN hu K _ x t hs h1 h2
  have hsub : Subsingleton (PrimeSpectrum (DualNumber K)) := by
    have key : ∀ p : PrimeSpectrum (DualNumber K),
        p.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom := by
      intro p
      have hp := p.isPrime
      have hle : RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom ≤ p.asIdeal := by
        intro a ha
        have ha' : a.fst = 0 := ha
        apply hp.mem_of_pow_mem 2
        have : a ^ 2 = 0 := by
          rw [sq]; ext <;> simp [ha']
        rw [this]; exact p.asIdeal.zero_mem
      have hmax : (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom).IsMaximal :=
        RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨TrivSqZeroExt.inl c, rfl⟩)
      exact (hmax.eq_of_le hp.ne_top hle).symm
    exact ⟨fun p q => PrimeSpectrum.ext ((key p).trans (key q).symm)⟩
  have hsub' : Subsingleton (Sp (DualNumber K)) := hsub
  obtain ⟨p⟩ : Nonempty (Sp (DualNumber K)) := inferInstanceAs (Nonempty (PrimeSpectrum (DualNumber K)))
  obtain ⟨R, _, j, v, hj, ⟨q, _⟩, hv⟩ := GlobalTheory.T.exists_thetaConstants_locally_on_base hL hL2 o g N' J b _ _ t hN p
  have hsurj : Function.Surjective j := fun y => ⟨q, Subsingleton.elim _ _⟩
  have hiso : IsIso j := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext y
    simpa using hsurj y
  have c1 := (hu R _ v).1 ((GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ u _ _ t x R j v h1).1 hv)
  have c2 := (hu R _ v).1 ((GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ _ u _ _ t (constPt x) R j v h2).1 hv)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (R := CommRingCat.of o) (S := CommRingCat.of R) (j ≫ x ≫ Y.s)
  have e1 : (j ≫ x) ≫ Y.s = spMap β.hom := by
    rw [Category.assoc]; exact hβ.symm
  have e2 : (j ≫ constPt x) ≫ Y.s = spMap β.hom := by
    rw [Category.assoc, ← hs]; exact hβ.symm
  have h := (Y.pts R β.hom v (Y.loc R β.hom _ v e1 c1)).unique ⟨e1, c1⟩ ⟨e2, c2⟩
  exact (cancel_epi j).1 h

end GlobalTheory.ZM
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.TangentVectorZeroOfObjectConstantAlongStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.tangentVector_zero_of_object_constant_along : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (u : TObj g (N' ^ 2) J b Y.s), Odd N' → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → ∀ (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ Y.MM) (t : TObj g (N' ^ 2) J b (x ≫ Y.s)), x ≫ Y.s = constPt x ≫ Y.s → TMap t u x → TMap t u (constPt x) → x = constPt x := by
  first | exact @GlobalTheory.ZM.tangent_eq_constPt_of_tMap | exact GlobalTheory.ZM.tangent_eq_constPt_of_tMap | (intros; apply GlobalTheory.ZM.tangent_eq_constPt_of_tMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaIdealFamilyUniversalPropertyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.thetaIdealFamily_universal_property : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (u : TObj g ((n ^ j) ^ 2) J b Y.s), (∀ (R : Type) [CommRing R] (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), u.HasTh x v ↔ SecCoord Y.de Y.th x v) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Y.MM) (t' : TObj g ((n ^ j) ^ 2) J b (x ≫ Y.s)) v, t'.Shape Mat κ → t'.HasTh (𝟙 _) v → SecCoord Y.de Y.th x v → TMap t' u x) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (t : TObj g ((n ^ j) ^ 2) J b s'), IsReduced S → Dense (fromSet em C t) → ∃! f : S ⟶ Y.MM, f ≫ Y.s = s' ∧ TMap t u f := by
  first | exact @GlobalTheory.FamRep.family_universal | exact GlobalTheory.FamRep.family_universal | (intros; apply GlobalTheory.FamRep.family_universal <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaObjectFamilyOpenClosure

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.ThetaFamily

theorem exists_coord_of_isLocalRing {X : Scheme.{0}} {M : LB X} {σ : Type} (th : σ → M.Sec) (hM : M.IsLB)
    {R : Type} [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X) : ∃ v, SecCoord M th x v := by
  obtain ⟨k, hk⟩ : ∃ k, x (IsLocalRing.closedPoint R) ∈ M.U k :=
    TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge trivial)
  refine GlobalTheory.SegreCoord.exists_secCoord hM (k := k) fun y => ?_
  exact ((IsLocalRing.specializes_closedPoint y).map x.continuous).mem_open (M.U k).isOpen hk

theorem nonempty_thetaFam : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → Nonempty (ThetaFam n em C) := by
  intro h₁ h₂ hcrit g J _ Mat κ n w w' hn hodd
  obtain ⟨j₁, hglue⟩ := GlobalTheory.T.exists_thetaFamily_over_thetaPointScheme h₁ h₂ hcrit g J Mat κ n w w' hn hodd
  obtain ⟨j₂, hrep⟩ := GlobalTheory.T.thetaIdealFamily_universal_property h₁ h₂ g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em C d hb hC => ?_⟩
  have := hb.1
  obtain ⟨i₁, i₂, i₃⟩ := GlobalTheory.T.thetaPointsVanishingIdeal_radical_homogeneous o g (n ^ j) J b em C hb.2.2
  obtain ⟨Y⟩ := GlobalTheory.ZM.nonempty_MMPre o g n (n ^ j) (thIdeal em C) (pow_pos hn.pos j) i₁ i₂ i₃
  obtain ⟨t, hd, -, hth, hfib⟩ := hglue j (le_of_max_le_left hj) o b em C d hb hC Y
  refine ⟨{ MM := Y.MM
            s := Y.s
            qproj := Y.qproj
            flat := Y.flat
            reduced := Y.reduced
            univ := t
            dense := hd
            loc := fun R _ _ β x hx => ?_
            pts := fun R _ β v hv => ?_
            rep := hrep j (le_of_max_le_right hj) o b em C d hb hC Y t hth hfib
            unram := GlobalTheory.T.tangentVector_zero_of_object_constant_along h₁ h₂ o g n (n ^ j) J b _ Y t hodd.pow hth }⟩
  · obtain ⟨v, hv⟩ := exists_coord_of_isLocalRing Y.th Y.isLB x
    exact ⟨v, (hth R x v).2 hv, Y.loc R β x v hx hv⟩
  · simpa only [hth] using Y.pts R β v hv

end GlobalTheory.ZM.ThetaFamily
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyThetaObjectFamilyOpenClosureStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.nonempty_thetaObject_family_open_closure : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → Nonempty (ThetaFam n em C) := by
  first | exact @GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam | exact GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam | (intros; apply GlobalTheory.ZM.ThetaFamily.nonempty_thetaFam <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaFamIsPEL

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem GlobalTheory.thetaFam_isPEL : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ (n N' : ℕ) (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∀ F : ThetaFam n em (PELClass (b := b) D a bas ρ em), ∃ τ : SAB H F.MM, IsPEL D a bas ρ F.univ τ := by
  intro h1 h2 h3 E _ _ _ H D g J _ a w w' bas hpq hbas hw hw' hcl n N' o _ b em ρ hρ hem F
  obtain ⟨hded, -, hinj⟩ := hem
  have := F.reduced
  have : LocallyOfFiniteType F.s := by
    obtain ⟨N, i, hi, -, hs⟩ := F.qproj
    have := isProper_str o N
    rw [← hs]
    infer_instance
  have : IsLocallyNoetherian F.MM := LocallyOfFiniteType.isLocallyNoetherian F.s
  exact GlobalTheory.T.exists_isPELTriple_of_dense_fibres h1 h2 h3 E H D g J a bas w w' hpq hbas hw hw' hcl (N' ^ 2) o b em ρ F.MM F.s F.univ hρ hinj F.dense
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyPelSmoothGenericFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem ThetaFam.unram_of_mono {o : Type} [CommRing o] {g n N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {em : o →+* ℂ}
    {C : TObj g (N' ^ 2) J b (spMap em) → Prop} (F : ThetaFam n em C) {S : Scheme.{0}} (x : S ⟶ F.MM) [Mono x]
    {s : S ⟶ Sp o} (hs : x ≫ F.s = s) (t : TObj g (N' ^ 2) J b s) (ht : TMap t F.univ x) (K : Type) [Field K]
    (y : Sp (DualNumber K) ⟶ S) (t' : TObj g (N' ^ 2) J b (y ≫ s)) (hy : y ≫ s = constPt y ≫ s)
    (h₁ : TMap t' t y) (h₂ : TMap t' t (constPt y)) : y = constPt y := by
  subst hs
  have hc : constPt (y ≫ x) = constPt y ≫ x := by simp [constPt]
  rw [← cancel_mono x, ← hc]
  have key : ∀ (s' : Sp (DualNumber K) ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s'), s' = (y ≫ x) ≫ F.s →
      TMap t' F.univ (y ≫ x) → TMap t' F.univ (constPt (y ≫ x)) → y ≫ x = constPt (y ≫ x) := by
    rintro _ t' rfl h h'
    exact F.unram K (y ≫ x) t' (by rw [hc, Category.assoc, Category.assoc, hy]) h h'
  refine key _ t' (Category.assoc _ _ _).symm ?_ ?_
  · exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t t').2 x y ht).1 h₁
  · rw [hc]
    exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ F.univ t t').2 x (constPt y) ht).1 h₂

theorem exists_thetaFam_isPEL_smooth : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La), 1 ≤ D.p + D.q → IsSympBasis D bas → a w = H.w0 → a w' = H.bar H.w0 → Subring.closure (Set.range a) = ⊤ → ∀ n : ℕ, n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (ρ : o), em ρ = H.rt0 → ArBase em → ∃ (F : ThetaFam n em (PELClass (b := b) D a bas ρ em)) (τ : SAB H F.MM), IsPEL D a bas ρ F.univ τ ∧ SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap o (FractionRing o)))) := by
  intro h1 h2 hcrit hgen hU E _ _ _ H D g J _ a w w' bas hD hbas hw hw' ha n hn hodd
  obtain ⟨Mat, κ, hcl⟩ := GlobalTheory.T.isGoodThetaComplexClass_unitaryFullLevel h1 h2 hgen hU E H D g J a w w' bas hD hbas hw hw' ha
  obtain ⟨j₁, hj₁⟩ := hcl n hn hodd
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.T.nonempty_thetaObject_family_open_closure h1 h2 hcrit g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em ρ hρ hb => ?_⟩
  have hgood := hj₁ j (le_of_max_le_left hj) _ rfl o b em ρ hρ
  obtain ⟨F⟩ := hj₂ j (le_of_max_le_right hj) o b em _ _ hb hgood
  obtain ⟨τ, hτ⟩ := GlobalTheory.thetaFam_isPEL h1 h2 hgen E H D g J a w w' bas hD hbas hw hw' ha n _ o b em ρ hρ hb F
  refine ⟨F, τ, hτ, ThetaFam.smooth_genericFibre h1 h2 g n _ J Mat κ w w' o b em _ _ F hb hgood ?_⟩
  intro R _ _ _ _ _ x hx hs hem
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull o g _ J b _ _ F.s _ x F.univ hs
  obtain ⟨τ', hτ'⟩ := GlobalTheory.PELPull.isPEL_pull E H D g _ J a bas o b ρ _ _ F.s _ x F.univ t τ hs ht hτ
  have hρ2 : ρ ^ 2 = -(H.d : o) := hb.2.2 (by rw [map_pow, hρ, H.sqrt_neg_disc_sq, map_neg, map_natCast])
  have hft : Algebra.FiniteType o R := by
    have := ((GlobalTheory.isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB F.s).1 F.qproj).1
    have h : LocallyOfFiniteType (spMap (algebraMap o R)) := hs ▸ inferInstance
    exact RingHom.finiteType_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h)
  exact GlobalTheory.T.finrank_tangent_PEL_family_le_symmetricDomain h1 h2 hgen hU E H D g J a w w' bas hD hbas hw hw' ha _ o b ρ R t τ' hρ2 hτ' hft
    (fun y t' hy h₁ h₂ => F.unram_of_mono x hs t ht ℂ y t' hy h₁ h₂)

end GlobalTheory.ZM
end
end
