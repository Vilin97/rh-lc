module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubePointsFstEqPartialSumsGrpPullback
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimitiveValueOfRingElementPsiRelation
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompLinCombGenerator
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorMumfordBundleIsoOfGeneratorStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubePointsFstEqPartialSumsGrpPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.cubePoints_fst_eq_partialSums_grpPullback : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (f : S₀ ⟶ S) (β : B₀.left ⟶ B.left) (β₂ : (G2 B₀).left ⟶ (G2 B).left), IsGrpPullback B₀ B f β → IsSquare β β₂ → ∀ (Y : Over S₀) (x y : Y ⟶ B₀) (x' y' : Y ⟶ (Over.pullback f).obj B), x'.left ≫ pullback.fst B.hom f = x.left ≫ β → y'.left ≫ pullback.fst B.hom f = y.left ≫ β → ∀ k : Fin 4, lamPts x' y' k ≫ pullback.fst B.hom f = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k)).left := by
  first | exact @GlobalTheory.PairPts.lamPts_fst_eq_psum | exact GlobalTheory.PairPts.lamPts_fst_eq_psum | (intros; apply GlobalTheory.PairPts.lamPts_fst_eq_psum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompPullbackIdValues

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.IsoPullIdComp

theorem exists_comp_val : ∀ {Y X₀ X : Scheme.{0}} {A : LB Y} {L₀ : LB X₀} {M : LB X} {K₀ K : Type} [Fintype K₀] [Fintype K] (φ₀ : K₀ → (Y ⟶ X₀)) (ε₀ : K₀ → ℤ) (φ : K → (Y ⟶ X)) (ε : K → ℤ), A.IsLB → L₀.IsLB → M.IsLB → ∀ (u : LB.Iso A (LB.LinComb L₀ φ₀ ε₀)), u.IsGen → ∀ (v : LB.Iso (LB.LinComb L₀ φ₀ ε₀) ((LB.LinComb M φ ε).pull (𝟙 Y))), v.IsGen → ∃ w : LB.Iso A (LB.LinComb M φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J₀ : (Z ⟶ X₀) → L₀.ι) (a : A.ι), q z ∈ A.U a → Good M z J → Good L₀ z J₀ → gm q z _ (w.s (fun k => J (q ≫ φ k), a)) = gm q z _ (u.s (fun k => J₀ (q ≫ φ₀ k), a)) * GlobalTheory.Mum.Two.isoVal v q z J J₀ := by
  intro Y X₀ X A L₀ M K₀ K _ _ φ₀ ε₀ φ ε hA hL₀ hM u hu v hv
  have eu := GlobalTheory.LinCombComp.gm_iso_linComb φ₀ ε₀ u hu
  have ev : ∀ (y : Y) (j j' : K → M.ι) (j₀ j₀' : K₀ → L₀.ι), y ∈ LB.wchart M φ j → y ∈ LB.wchart L₀ φ₀ j₀ →
      y ∈ LB.wchart M φ j' → y ∈ LB.wchart L₀ φ₀ j₀' →
      gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
          (v.s (fun _ => j, j₀)) =
        (trF φ ε (𝟙 Y) y j j' * (trF φ₀ ε₀ (𝟙 Y) y j₀ j₀')⁻¹) *
          gm (𝟙 Y) y ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀'))
            (v.s (fun _ => j', j₀')) := by
    intro y j j' j₀ j₀' h h0 h' h0'
    have hp : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) := ⟨mem_pull.2 h, h0⟩
    have hq : (𝟙 Y : Y ⟶ Y) y ∈
        (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j', j₀') := ⟨mem_pull.2 h', h0'⟩
    have e1 := GlobalTheory.LinCombComp.gm_gen hv (𝟙 Y) y hp hq
    rw [GlobalTheory.Mum.Two.gm_div_pull (𝟙 Y) y _ _ hp hq, Category.comp_id] at e1
    exact e1
  have glue : ∀ (j : K → M.ι) (a : A.ι), ∃ s : Γ(Y, LB.wchart M φ j ⊓ A.U a)ˣ,
      ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι), q z ∈ LB.wchart M φ j → q z ∈ A.U a →
        q z ∈ LB.wchart L₀ φ₀ j₀ →
        gm q z (LB.wchart M φ j ⊓ A.U a) s =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) := by
    intro j a
    obtain ⟨W, hW⟩ : ∃ W : (K₀ → L₀.ι) → Y.Opens, ∀ j₀, W j₀ = LB.wchart M φ j ⊓ A.U a ⊓ LB.wchart L₀ φ₀ j₀ :=
      ⟨_, fun _ => rfl⟩
    have memW : ∀ y j₀, y ∈ W j₀ ↔ (y ∈ LB.wchart M φ j ∧ y ∈ A.U a) ∧ y ∈ LB.wchart L₀ φ₀ j₀ := fun y j₀ => by
      rw [hW]; exact Iff.rfl
    have l₀ : ∀ j₀, W j₀ ≤ LB.wchart M φ j ⊓ A.U a := fun j₀ y hy => ((memW y j₀).1 hy).1
    have l₁ : ∀ j₀, W j₀ ≤ (LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀) :=
      fun j₀ y hy => ⟨mem_pull.2 ((memW y j₀).1 hy).1.1, ((memW y j₀).1 hy).2⟩
    have l₂ : ∀ j₀, W j₀ ≤ LB.wchart L₀ φ₀ j₀ ⊓ A.U a := fun j₀ y hy =>
      ⟨((memW y j₀).1 hy).2, ((memW y j₀).1 hy).1.2⟩
    obtain ⟨uu, hu'⟩ : ∃ uu : ∀ j₀, Γ(Y, W j₀)ˣ, ∀ (Z' : Scheme.{0}) (q : Z' ⟶ Y) (z : Z') (j₀ : K₀ → L₀.ι),
        q z ∈ W j₀ → gm q z (W j₀) (uu j₀) =
          gm q z ((LB.div ((LB.LinComb M φ ε).pull (𝟙 Y)) (LB.LinComb L₀ φ₀ ε₀)).U (fun _ => j, j₀))
              (v.s (fun _ => j, j₀)) *
            gm q z (LB.wchart L₀ φ₀ j₀ ⊓ A.U a) (u.s (j₀, a)) :=
      ⟨fun j₀ => res (l₁ j₀) (v.s (fun _ => j, j₀)) * res (l₂ j₀) (u.s (j₀, a)), fun Z' q z j₀ h =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res q z (l₁ j₀) h _) (gm_res q z (l₂ j₀) h _))⟩
    obtain ⟨s, hs⟩ := glue_unit (LB.wchart M φ j ⊓ A.U a) W l₀ (fun y hy => by
        choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨j₀, (memW y j₀).2 ⟨hy, Set.mem_iInter.2 hj₀⟩⟩) uu
      (fun j₀ j₀' y hy => by
        obtain ⟨⟨h1, ha⟩, h0⟩ := (memW y j₀).1 hy.1
        obtain ⟨-, h0'⟩ := (memW y j₀').1 hy.2
        refine (hu' Y (𝟙 Y) y j₀ hy.1).trans (Eq.trans ?_ (hu' Y (𝟙 Y) y j₀' hy.2).symm)
        rw [ev y j j j₀ j₀' h1 h0 h1 h0', eu y j₀ j₀' a a h0 ha h0' ha,
          GlobalTheory.LinCombComp.trF_self hM φ ε (𝟙 Y) y j h1, gm_self hA (𝟙 Y) y ha]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
    refine ⟨s, fun Z' q z j₀ h1 ha h0 => ?_⟩
    have hy : q z ∈ W j₀ := (memW _ j₀).2 ⟨⟨h1, ha⟩, h0⟩
    exact (gm_res q z (l₀ j₀) hy s).symm.trans ((congrArg (gm q z (W j₀)) (hs j₀)).trans (hu' Z' q z j₀ hy))
  choose s hs using glue
  refine ⟨⟨fun p => s p.1 p.2⟩, fun p p' => unit_ext fun y hy => ?_, fun Z q z J J₀ a ha hJ hJ₀ => ?_⟩
  · obtain ⟨⟨h1, ha⟩, h1', ha'⟩ := hy
    choose j₀ hj₀ using fun k => exists_chart hL₀ (φ₀ k y)
    have h0 : y ∈ LB.wchart L₀ φ₀ j₀ := Set.mem_iInter.2 hj₀
    have key : gm (𝟙 Y) y (LB.wchart M φ p.1 ⊓ A.U p.2) (s p.1 p.2) =
        (trF φ ε (𝟙 Y) y p.1 p'.1 * (gm (𝟙 Y) y (A.U p.2 ⊓ A.U p'.2) (A.g p.2 p'.2))⁻¹) *
          gm (𝟙 Y) y (LB.wchart M φ p'.1 ⊓ A.U p'.2) (s p'.1 p'.2) := by
      rw [hs p.1 p.2 Y (𝟙 Y) y j₀ h1 ha h0, hs p'.1 p'.2 Y (𝟙 Y) y j₀ h1' ha' h0,
        ev y p.1 p'.1 j₀ j₀ h1 h0 h1' h0, eu y j₀ j₀ p.2 p'.2 h0 ha h0 ha',
        GlobalTheory.LinCombComp.trF_self hL₀ φ₀ ε₀ (𝟙 Y) y j₀ h0]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    have hm : y ∈ (LB.div (LB.LinComb M φ ε) A).U p ⊓ (LB.div (LB.LinComb M φ ε) A).U p' :=
      ⟨⟨h1, ha⟩, h1', ha'⟩
    have ed := (GlobalTheory.LinCombComp.gm_div _ _ (𝟙 Y) y p p' hm.1 hm.2).trans
      (congrArg (· * _) (gm_linComb M φ ε (𝟙 Y) y p.1 p'.1 h1 h1'))
    exact (gm_res _ y _ hm _).trans (key.trans ((congrArg₂ (· * ·) ed.symm (gm_res _ y _ hm _).symm).trans
      (map_mul _ _ _).symm))
  · refine (hs _ a Z q z (fun k => J₀ (q ≫ φ₀ k)) (hJ.mem φ q) ha (hJ₀.mem φ₀ q)).trans
      ((mul_comm _ _).trans (congrArg _ ?_))
    have e : ∀ b b', b = b' → gm q z _ (v.s b) = gm q z _ (v.s b') := by rintro _ _ rfl; rfl
    exact e _ _ (Prod.ext (funext fun _ => funext fun k => by simp only [Category.id_comp]) rfl)

end GlobalTheory.IsoPullIdComp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoCompPullbackIdValuesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two


theorem _root_.GlobalTheory.T.exists_lineBundleIso_comp_pullback_id_values : ∀ {Y X₀ X : Scheme.{0}} {A : LB Y} {L₀ : LB X₀} {M : LB X} {K₀ K : Type} [Fintype K₀] [Fintype K] (φ₀ : K₀ → (Y ⟶ X₀)) (ε₀ : K₀ → ℤ) (φ : K → (Y ⟶ X)) (ε : K → ℤ), A.IsLB → L₀.IsLB → M.IsLB → ∀ (u : LB.Iso A (LB.LinComb L₀ φ₀ ε₀)), u.IsGen → ∀ (v : LB.Iso (LB.LinComb L₀ φ₀ ε₀) ((LB.LinComb M φ ε).pull (𝟙 Y))), v.IsGen → ∃ w : LB.Iso A (LB.LinComb M φ ε), w.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J₀ : (Z ⟶ X₀) → L₀.ι) (a : A.ι), q z ∈ A.U a → Good M z J → Good L₀ z J₀ → gm q z _ (w.s (fun k => J (q ≫ φ k), a)) = gm q z _ (u.s (fun k => J₀ (q ≫ φ₀ k), a)) * GlobalTheory.Mum.Two.isoVal v q z J J₀ := by
  exact @GlobalTheory.IsoPullIdComp.exists_comp_val
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefOfRefinesTensor

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.PowData

theorem sharpRef_of_tens : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (D₀ D : DegPre V₁) (e₀ : D₀.X ≃+ Q.X), Refines Q ρ D₀ e₀ → ∀ (T : Tens D₀ D W) (e : (Fin 8 → Q.X) ≃+ D.X), (∀ mu a, e₀ (T.xe (e mu) a) = mu a) → GlobalTheory.Poinc.Sep.SharpRef W Q ρ D e := by
  intro W V _ _ Q V₁ _ _ ρ D₀ D e₀ hR T e he
  obtain ⟨β, β₂, wR, hpb, hsq, hwR, hcR, htR⟩ := hR
  obtain ⟨io, hιm, hι⟩ := grpPullback_iso hpb (isGrpPullback_pullback Q.B (spMap ρ))
  have hprI : ∀ a, IsMonHom (T.pr a ≫ io.hom) := fun a => by
    haveI := T.pr_hom a; haveI := hιm; infer_instance
  have hpr' : ∀ a, (T.pr a ≫ io.hom).left ≫ pullback.fst Q.B.hom (spMap ρ) = (T.pr a).left ≫ β := fun a => by
    rw [Over.comp_left, Category.assoc, hι]
  let φQ : (Fin 8 × Fin 8) × Fin 4 → (D.P.A.left ⟶ Q.B.left) := fun k =>
    lamPts (T.pr k.1.1 ≫ io.hom) (T.pr k.1.2 ≫ io.hom) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)
  let εQ : (Fin 8 × Fin 8) × Fin 4 → ℤ := fun k => -(W k.1.1 k.1.2 * negε k.2)
  obtain ⟨v, hv, hvv⟩ := GlobalTheory.T.exists_tensor_mumfordBundle_iso_of_generator D₀.P.A Q.B D₀.P.L Q.M.L D₀.P.isLB Q.M.isLB β₂ wR hwR W D.P.A T.pr φQ εQ
    (fun k => GlobalTheory.T.cubePoints_fst_eq_partialSums_grpPullback D₀.P.A Q.B (spMap ρ) β β₂ hpb hsq D.P.A _ _ _ _ (hpr' _) (hpr' _) k.2)
    (fun k => by obtain ⟨⟨a, b⟩, i⟩ := k; fin_cases i <;> simp [εQ, negε, Oε])
  obtain ⟨w', hw', hwv⟩ := GlobalTheory.T.exists_lineBundleIso_comp_pullback_id_values (A := D.P.L) (tensφ T.pr) (tensε W) φQ εQ D.P.isLB D₀.P.isLB Q.M.isLB T.w T.w_gen v hv
  refine ⟨fun a => T.pr a ≫ io.hom, w', hprI, fun T' y => ?_, hw', fun mu a => ?_, fun κ hκ mu z J J' hJ hJ' => ?_⟩
  · refine ⟨Fan.IsLimit.lift T.lim (fun a => y a ≫ io.inv), fun a => ?_, fun x hx => ?_⟩
    · have h := Fan.IsLimit.fac T.lim (fun a => y a ≫ io.inv) a
      change _ ≫ T.pr a = _ at h
      show _ ≫ T.pr a ≫ io.hom = _
      rw [← Category.assoc, h]
      simp
    · refine Fan.IsLimit.hom_ext T.lim _ _ fun a => ?_
      have h := Fan.IsLimit.fac T.lim (fun a => y a ≫ io.inv) a
      change _ ≫ T.pr a = _ at h
      change x ≫ T.pr a = _ ≫ T.pr a
      rw [h, ← hx a]
      simp
  · show (D.c (e mu) ≫ T.pr a ≫ io.hom).left ≫ pullback.fst Q.B.hom (spMap ρ) = _
    rw [← Category.assoc, Over.comp_left, Category.assoc, hι, T.c_pr, hcR, he]
  · choose J₀ hJ₀ using fun s : (TK V₁).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (s z)
    have hJ₀' : Good D₀.P.L z J₀ := hJ₀
    have h1 := T.psi (e mu) z J₀ J' hJ₀' hJ'
    have h2 := hwv _ (D.xK (e mu)) z J J₀ (J' (D.xK (e mu))) (hJ' _) hJ hJ₀'
    have h3 := hvv _ (D.xK (e mu)) z J J₀ hJ hJ₀'
    have h4 : ∀ a b, D.xK (e mu) ≫ (lift (T.pr a) (T.pr b)).left =
        (lift (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) a)) (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) b))).left := by
      intro a b
      show (toUnit (TK V₁) ≫ D.c (e mu)).left ≫ _ = _
      rw [← Over.comp_left, comp_lift, Category.assoc, Category.assoc, T.c_pr, T.c_pr]
    have h5 : ∀ a b, val (D₀.tau (T.xe (e mu) a) (T.xe (e mu) b)) (𝟙 _) z J₀ =
        lamVal wR (lift (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) a)) (toUnit (TK V₁) ≫ D₀.c (T.xe (e mu) b))).left z J J₀ *
          val (Q.tau (mu a) (mu b)) κ z J := fun a b => by
      rw [htR κ hκ _ _ z J J₀ hJ hJ₀', he, he]
    rw [h1]
    erw [h2]
    rw [h3]
    simp only [h4, h5, mul_zpow, Finset.prod_mul_distrib, _root_.mul_assoc]

end GlobalTheory.Mum.PowData
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefOfRefinesTensorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

theorem _root_.GlobalTheory.T.sharpRef_of_refines_tensor : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁) (D₀ D : DegPre V₁) (e₀ : D₀.X ≃+ Q.X), Refines Q ρ D₀ e₀ → ∀ (T : Tens D₀ D W) (e : (Fin 8 → Q.X) ≃+ D.X), (∀ mu a, e₀ (T.xe (e mu) a) = mu a) → GlobalTheory.Poinc.Sep.SharpRef W Q ρ D e := by
  first | exact @GlobalTheory.Mum.PowData.sharpRef_of_tens | exact GlobalTheory.Mum.PowData.sharpRef_of_tens | (intros; apply GlobalTheory.Mum.PowData.sharpRef_of_tens <;> assumption)
end
end
