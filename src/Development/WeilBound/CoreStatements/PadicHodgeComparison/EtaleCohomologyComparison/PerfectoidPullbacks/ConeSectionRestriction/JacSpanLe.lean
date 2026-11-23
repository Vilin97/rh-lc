module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.SeamDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousRatioCocycleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusCoordinateIsUnit
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalRestrictSection

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeEval

theorem ev_rs_eq : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := by
  intro K _ X q T V W h hT hT' s
  have e : X.presheaf.map (homOfLE h).op ≫ (pt T).appLE V ⊤ hT = (pt T).appLE W ⊤ hT' :=
    Scheme.Hom.map_appLE _ _ _
  unfold ev rs GlobalTheory.Cris.evalAt
  rw [← e]
  rfl

end GlobalTheory.CompanionTheory.ConeEval
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalRestrictSectionStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.eval_restrict_section : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := by
  first | exact @GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq | exact GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq | (intros; apply GlobalTheory.CompanionTheory.ConeEval.ev_rs_eq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousRatioIsUnit

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.ConeUnit

theorem yQ_appLE_isUnit {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m)
    (W : X.Opens) (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k') :
    IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := by
  have ha : y k' ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y k')).2 (hy k')
  have hb : y k ∈ grK K N e := (MvPolynomial.mem_homogeneousSubmodule e (y k)).2 (hy k)
  have ha1 : y k' ∈ grK K N (1 • e) := by simpa using ha
  have hb1 : y k ∈ grK K N (1 • e) := by simpa using hb
  have hVx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k' * y k) := by
    rw [Proj.basicOpen_mul]
    exact le_inf h2 h1
  have e1 := congrArg (fun φ => φ.hom (HomogeneousLocalization.Away.mk _ ha 1 (y k) hb1))
    (Proj.awayMap_awayToSection (grK K N) hb (x := y k' * y k) rfl)
  have e2 := congrArg (fun φ => φ.hom (HomogeneousLocalization.Away.mk _ hb 1 (y k') ha1))
    (Proj.awayMap_awayToSection (grK K N) ha (x := y k' * y k) (mul_comm _ _))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at e1 e2
  have e3 : (i.appLE _ W h2).hom (yQ y hy k k') = (i.appLE _ W hVx).hom
      ((Proj.awayToSection (grK K N) (y k' * y k)).hom
        (HomogeneousLocalization.awayMap (grK K N) hb (x := y k' * y k) rfl
          (HomogeneousLocalization.Away.mk _ ha 1 (y k) hb1))) := by
    rw [e1, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    rfl
  refine IsUnit.of_mul_eq_one ((i.appLE _ W hVx).hom ((Proj.awayToSection (grK K N) (y k' * y k)).hom
        (HomogeneousLocalization.awayMap (grK K N) ha (x := y k' * y k) (mul_comm _ _)
          (HomogeneousLocalization.Away.mk _ hb 1 (y k') ha1)))) ?_
  rw [e3, ← map_mul, ← map_mul, GlobalTheory.CompanionTheory.GeoUnit.awayMap_ratio_mul ha hb hb1 ha1, map_one, map_one]

end GlobalTheory.CompanionTheory.ConeUnit
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousRatioIsUnitStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.homogeneous_ratio_isUnit : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m) (W : X.Opens)
    (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k'), IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := by
  first | exact @GlobalTheory.CompanionTheory.ConeUnit.yQ_appLE_isUnit | exact GlobalTheory.CompanionTheory.ConeUnit.yQ_appLE_isUnit | (intros; apply GlobalTheory.CompanionTheory.ConeUnit.yQ_appLE_isUnit <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobianSpanLeSubalgebra

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

theorem jacSpan_le_jacS : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := by
  intro K _ X V W h _ B hB d m D κ
  refine (AddSubgroup.closure_le _).2 ?_
  rintro y ⟨b, bs, rfl⟩
  have hm : ∀ c : Γ(X, W), rs h c ∈ B := fun c => by
    have : rs h c ∈ (B : Set Γ(X, V)) := hB ▸ Set.mem_range_self c
    exact this
  exact AddSubgroup.subset_closure ⟨⟨rs h b, hm b⟩, fun l => ⟨rs h (bs l), hm (bs l)⟩, rfl⟩

end GlobalTheory.CompanionTheory.Cone
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobianSpanLeSubalgebraStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.jacobian_span_le_subalgebra : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := by
  first | exact @GlobalTheory.CompanionTheory.Cone.jacSpan_le_jacS | exact GlobalTheory.CompanionTheory.Cone.jacSpan_le_jacS | (intros; apply GlobalTheory.CompanionTheory.Cone.jacSpan_le_jacS <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictAppLECompat

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeRs

theorem rs_appLE_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)) : rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := by
  change ((f.appLE U W hW) ≫ X.presheaf.map (homOfLE h).op).hom s = _
  rw [Scheme.Hom.appLE_map]

end GlobalTheory.CompanionTheory.ConeRs
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictAppLECompatStatement

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

theorem _root_.GlobalTheory.T.restrict_appLE_compat : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)), rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := by
  first | exact @GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply | exact GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply | (intros; apply GlobalTheory.CompanionTheory.ConeRs.rs_appLE_apply <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.JacSpanLe

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

theorem yQ_unit : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (k k' : Fin m) (W : X.Opens)
    (h1 : W ≤ uy i y k) (h2 : W ≤ uy i y k'), IsUnit ((i.appLE _ W h2).hom (yQ y hy k k')) := GlobalTheory.T.homogeneous_ratio_isUnit

theorem yQ_mul : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N m e : ℕ} (i : X ⟶ PSpace K N)
    (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (a b c : Fin m) (W : X.Opens)
    (ha : W ≤ uy i y a) (hb : W ≤ uy i y b) (hc : W ≤ uy i y c),
    (i.appLE _ W hb).hom (yQ y hy a b) * (i.appLE _ W hc).hom (yQ y hy b c) = (i.appLE _ W hc).hom (yQ y hy a c) ∧
    (i.appLE _ W ha).hom (yQ y hy a a) = 1 := GlobalTheory.T.homogeneous_ratio_cocycle

theorem ev_rs : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (T : Thick (smFun X q))
    {V W : X.Opens} (h : V ≤ W) (hT : InU V T) (hT' : InU W T) (s : Γ(X, W)), ev T hT (rs h s) = ev T hT' s := GlobalTheory.T.eval_restrict_section

theorem rs_appLE : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ f ⁻¹ᵁ U)
    (s : Γ(Y, U)), rs h ((f.appLE U W hW).hom s) = (f.appLE U V (h.trans hW)).hom s := GlobalTheory.T.restrict_appLE_compat

theorem jacSpan_le : ∀ {K : Type} [Field K] {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) [Algebra K Γ(X, V)]
    (B : Subalgebra K Γ(X, V)), (B : Set Γ(X, V)) = Set.range (rs h) →
    ∀ {d m : ℕ} (D : Fin d → Derivation K Γ(X, V) Γ(X, V)) (κ : Fin m → Fin d),
    jacSpan h (RingHom.id _) (fun k => D k) κ ≤ jacS B D κ := GlobalTheory.T.jacobian_span_le_subalgebra

end CrystallineSemistableComparison.Pb
end
end
end
