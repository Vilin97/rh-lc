module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.TotallySplit
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTheoryMu
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishAtPlaces
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharPStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham
open GlobalTheory.PDivGroup in

theorem _root_.GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charP : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
      (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
  intro p _ k _ _ _ B f _
  obtain ⟨G, -, ⟨t⟩⟩ := GlobalTheory.AVTower.exists_tower p k B
  let T := GlobalTheory.Dieu.theory p
  have : Module.Free (WittVector p k) (T.M G) := T.base.free G trivial
  have : Module.Finite (WittVector p k) (T.M G) := T.base.finite G trivial
  have hWitt := GlobalTheory.Dieu.CharpolyAV.charpoly_map_eq p T k B G t (End.of f)
  have hπ : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) := fun x =>
    ⟨WittVector.teichmuller p x, by simp⟩
  obtain ⟨hfin, hRed⟩ := GlobalTheory.DeRhamCharpolyP.charpoly_of_red
    (WittVector.constantCoeff : WittVector p k →+* k) hπ p
    (CharP.cast_eq_zero k p) (T.red G) (T.base.red_surjective G trivial) (T.base.red_eq_zero G trivial)
    (T.map (t.map t f.hom)) (rigExtMap (t.map t f.hom)) (fun m => by
      have h := T.base.red_smap trivial trivial (SemiHom.ofHom (t.map t f.hom)) m
      rw [SemiHom.ofHom_rig] at h
      exact h)
  obtain ⟨e, he, -, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hR : IsNilpotent (p : k) := by
    rw [CharP.cast_eq_zero]
    exact IsNilpotent.zero
  let E := e hR B.ab t
  have : Module.Finite k G.RigExt := hfin
  have : Module.Finite k (primDR B.X) := Module.Finite.equiv E.symm
  have : Module.Free k G.RigExt := Module.Free.of_divisionRing k G.RigExt
  have hConj : primPull (dp0 k) (𝟙 _) f.hom = E.symm.conj (rigExtMap (t.map t f.hom)) := by
    refine LinearMap.ext fun c => ?_
    change primPull (dp0 k) (𝟙 _) f.hom c = E.symm (rigExtMap (t.map t f.hom) (E c))
    exact E.eq_symm_apply.mpr (he.primPull hR B.ab B.ab t t f.hom c)
  calc
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
        ((primPull (dp0 k) (𝟙 _) f.hom).dualMap).charpoly := rfl
    _ = (primPull (dp0 k) (𝟙 _) f.hom).charpoly := GlobalTheory.DeRhamCharpolyP.charpoly_dualMap _
    _ = (rigExtMap (t.map t f.hom)).charpoly :=
      (congrArg (fun φ : Module.End k (primDR B.X) => φ.charpoly) hConj).trans
        (E.symm.charpoly_conj _)
    _ = ((GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom (WittVector p k))).map
        WittVector.constantCoeff := hRed.trans (congrArg (Polynomial.map WittVector.constantCoeff) hWitt)
    _ = (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
      rw [Polynomial.map_map]
      congr 1
      exact RingHom.ext_int _ _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LPowerTorsionEndomorphismEvaluation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.l_power_torsion_endomorphism_evaluation : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B)
    (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
    ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ B.X),
    (∀ j x y, ev j (x + y) = ev j x * ev j y) →
    (∀ j x, ev j (φ x) = ev j x ≫ f.hom) →
    (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
    (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ B.X), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
    LinearMap.charpoly φ = GlobalTheory.AV.AbVar.charpoly (End.of f) :=
  GlobalTheory.AV.AbVar.charpoly_eq_lattice_model
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyEndomorphismEqMapLadic

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

theorem charpoly_push_eq_map_charpoly (k : Type) [Field k] [IsAlgClosed k]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)] :
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
      (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with h | h
  · haveI : Fact p.Prime := ⟨h⟩
    exact GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charP p k B f
  · subst h
    have : CharZero k := CharP.charP_to_charZero k
    have hcharpoly := GlobalTheory.DeRhamCharpolyZero.charpoly_push k B f
    exact hcharpoly

theorem charpoly_push_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (f : A ⟶ A) [IsMonHom f] (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
      (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
      ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ A),
      (∀ j x y, ev j (x + y) = ev j x * ev j y) →
      (∀ j x, ev j (φ x) = ev j x ≫ f) →
      (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
      (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ A), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
      ∀ [Module.Finite k (HdR A)],
        LinearMap.charpoly (push (dp0 k) (𝟙 _) f) = (LinearMap.charpoly φ).map (Int.castRingHom k) := by
  intro k _ _ A _ _ hA f _ L _ _ _ φ l hl hlk ev hadd hφ hker him _
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k A hA
  let B : GlobalTheory.AV.AbVar k := ⟨A, hA, g, hg⟩
  let f' : B ⟶ B := GlobalTheory.AV.AbVar.Hom.mk (A := B) (B := B) f
  rw [GlobalTheory.T.l_power_torsion_endomorphism_evaluation k B f' L φ l hl hlk ev hadd hφ hker him]
  exact charpoly_push_eq_map_charpoly k B f'

end GlobalTheory.DeRham
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyEndomorphismEqMapLadicStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (f : A ⟶ A) [IsMonHom f] (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
      (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
      ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ A),
      (∀ j x y, ev j (x + y) = ev j x * ev j y) →
      (∀ j x, ev j (φ x) = ev j x ≫ f) →
      (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
      (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ A), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
      ∀ [Module.Finite k (HdR A)],
        LinearMap.charpoly (push (dp0 k) (𝟙 _) f) = (LinearMap.charpoly φ).map (Int.castRingHom k) := by
  first | (exact @GlobalTheory.DeRham.charpoly_push_eq) | (exact GlobalTheory.DeRham.charpoly_push_eq) | (intros; apply GlobalTheory.DeRham.charpoly_push_eq  <;> assumption)
end
end
