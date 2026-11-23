module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CauchyBinetPluckerAndCellCoordinatesStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverFiniteFibreProduct

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ProjFinProd

theorem exists_isProjOver_finite_prod : ∀ (O : Type) [CommRing O] (ι : Type) [Finite ι] (X : Scheme.{0}) (s : X ⟶ Sp O) (Y : ι → Scheme.{0}) (f : ∀ i, Y i ⟶ Sp O), IsProjOver s → (∀ i, IsProjOver (f i)) → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ i, P ⟶ Y i), IsProjOver (p0 ≫ s) ∧ (∀ i, p i ≫ f i = p0 ≫ s) ∧ ∀ (Z : Scheme.{0}) (a : Z ⟶ X) (b : ∀ i, Z ⟶ Y i), (∀ i, b i ≫ f i = a ≫ s) → ∃! h : Z ⟶ P, h ≫ p0 = a ∧ ∀ i, h ≫ p i = b i := by
  intro O _ ι _ X s
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro Y f hs hf
    rename_i α β
    obtain ⟨P, p0, p, hP, hp, hu⟩ := ih (fun i => Y (e i)) (fun i => f (e i)) hs (fun i => hf _)
    have key : ∀ j : β, ∃ q : P ⟶ Y j, q ≫ f j = p0 ≫ s ∧ ∀ i (h : e i = j), q = p i ≫ eqToHom (congrArg Y h) := by
      intro j
      obtain ⟨i, rfl⟩ := e.surjective j
      refine ⟨p i, hp i, fun i' h => ?_⟩
      obtain rfl := e.injective h
      simp
    choose q hq1 hq2 using key
    have hq : ∀ i, q (e i) = p i := fun i => by simpa using hq2 (e i) i rfl
    refine ⟨P, p0, q, hP, hq1, fun Z a b hb => ?_⟩
    obtain ⟨h, ⟨h1, h2⟩, h3⟩ := hu Z a (fun i => b (e i)) (fun i => hb _)
    refine ⟨h, ⟨h1, fun j => ?_⟩, fun h' hh => h3 h' ⟨hh.1, fun i => ?_⟩⟩
    · obtain ⟨i, rfl⟩ := e.surjective j
      rw [hq]; exact h2 i
    · rw [← hq]; exact hh.2 _
  | h_empty =>
    intro Y f hs hf
    refine ⟨X, 𝟙 X, fun i => i.elim, by simpa using hs, fun i => i.elim, fun Z a b _ => ?_⟩
    exact ⟨a, ⟨by simp, fun i => i.elim⟩, fun h hh => by simpa using hh.1⟩
  | h_option ih =>
    intro Y f hs hf
    obtain ⟨P, p0, p, hP, hp, hu⟩ := ih (fun i => Y (some i)) (fun i => f (some i)) hs (fun i => hf _)
    refine ⟨pullback (p0 ≫ s) (f none), pullback.fst _ _ ≫ p0,
      fun i => match i with
        | none => pullback.snd _ _
        | some i => pullback.fst _ _ ≫ p i, ?_, ?_, fun Z a b hb => ?_⟩
    · rw [Category.assoc]
      exact isProjOver_pullback hP (hf none)
    · rintro (_ | i)
      · simp only [Category.assoc]; exact pullback.condition.symm
      · simp only [Category.assoc]; rw [hp i]
    · obtain ⟨h, ⟨h1, h2⟩, h3⟩ := hu Z a (fun i => b (some i)) (fun i => hb _)
      refine ⟨pullback.lift h (b none) (by rw [reassoc_of% h1, hb]), ⟨?_, ?_⟩, fun h' hh => ?_⟩
      · rw [pullback.lift_fst_assoc, h1]
      · rintro (_ | i)
        · exact pullback.lift_snd _ _ _
        · exact (pullback.lift_fst_assoc _ _ _ _).trans (h2 i)
      · apply pullback.hom_ext
        · rw [pullback.lift_fst]
          refine h3 _ ⟨by simpa using hh.1, fun i => ?_⟩
          simpa using hh.2 (some i)
        · rw [pullback.lift_snd]; exact hh.2 none

end GlobalTheory.ProjFinProd
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsProjOverFiniteFibreProductStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.exists_isProjOver_finite_fibreProduct : ∀ (O : Type) [CommRing O] (ι : Type) [Finite ι] (X : Scheme.{0}) (s : X ⟶ Sp O) (Y : ι → Scheme.{0}) (f : ∀ i, Y i ⟶ Sp O), IsProjOver s → (∀ i, IsProjOver (f i)) → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ i, P ⟶ Y i), IsProjOver (p0 ≫ s) ∧ (∀ i, p i ≫ f i = p0 ≫ s) ∧ ∀ (Z : Scheme.{0}) (a : Z ⟶ X) (b : ∀ i, Z ⟶ Y i), (∀ i, b i ≫ f i = a ≫ s) → ∃! h : Z ⟶ P, h ≫ p0 = a ∧ ∀ i, h ≫ p i = b i := by
  first | exact @GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod | exact GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod | (intros; apply GlobalTheory.ProjFinProd.exists_isProjOver_finite_prod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBase

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem span_plk_uvec_eq_top {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens}
    {c D : Let m → Fin (M + 1) → Γ(X, U.1)} (h : LeftInv D c) (w : Pm m) (en : En m) :
    Ideal.span (Set.range (plk (uvec c w) en.2.1)) = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.mem_span_range_iff_exists_fun.2 ⟨_,
    (GlobalTheory.T.cauchyBinet_plucker_and_cellCoordinates.2 T m (CR m U) M _ _ w MvPolynomial.X
      (h.map (MvPolynomial.C : Γ(X, U.1) →+* CR m U))).1 en.1 en.2.1 en.2.2⟩)

theorem exists_isPlk : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))
    (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → IsCover β s V α c D →
    ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
      (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsPlk β s V α c p0 p h := by
  intro O K _ _ β X s T _ m M B V α c D hs hC
  obtain ⟨P, p0, p, hP, hp, univ⟩ := GlobalTheory.T.exists_isProjOver_finite_fibreProduct O (En m) X s (fun en => PSpace O (plN M en.1))
    (fun en => PSpace.str O _) hs fun en => ⟨_, 𝟙 _, inferInstance, Category.id_comp _⟩
  have hb : ∀ b, cbase m (V b) ≫ s =
      spMap ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) := fun b => by
    rw [cbase, Category.assoc, hC.ovr b, ← Spec.map_comp]
    rfl
  have pt_str : ∀ {A : Type} [CommRing A] {N : ℕ} (c : O →+* A)
      (v : Fin (N + 1) → A) (hv : Ideal.span (Set.range v) = ⊤),
      pt c v hv ≫ PSpace.str O N = spMap c := by
    intro A _ N c v hv
    rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
  choose h hh using fun (b : B) (w : Pm m) => (univ _ (cbase m (V b))
    (fun en => pt ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) (plk (uvec (c b) w) en.2.1)
      (span_plk_uvec_eq_top (hC.inv b) w en))
    fun en => (pt_str _ _ _).trans (hb b).symm).exists
  refine ⟨P, p0, p, h, ⟨fun b w => (hh b w).1, fun b w en => ⟨_, (hh b w).2 en⟩⟩, hP, hp, fun Z a a' h0 h1 => ?_⟩
  exact (univ Z (a ≫ p0) (fun en => a ≫ p en) fun en => by
    rw [Category.assoc, hp, Category.assoc]).unique ⟨rfl, fun _ => rfl⟩ ⟨h0.symm, fun en => (h1 en).symm⟩

end GlobalTheory.FlagEmb
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPluckerFlagEmbeddingOfProjectiveBaseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

theorem _root_.GlobalTheory.T.exists_pluckerFlagEmbedding_of_projective_base : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)), IsProjOver s → IsCover β s V α c D → ∃ (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsPlk β s V α c p0 p h := by
  first | exact @GlobalTheory.FlagEmb.exists_isPlk | exact GlobalTheory.FlagEmb.exists_isPlk | (intros; apply GlobalTheory.FlagEmb.exists_isPlk <;> assumption)
end
end
