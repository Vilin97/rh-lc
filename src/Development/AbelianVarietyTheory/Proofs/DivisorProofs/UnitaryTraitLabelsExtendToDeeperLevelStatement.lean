module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SameGenericFibreChainRescaledDeeperRealisation
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartThetaSystemUnitaryModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperSetupStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperIdentificationChainAgreesGenerically

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.UPoinc.tied_chain_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), (∃ m : w₁.G.left ⟶ G.left, IsGrpPullback w₁.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = w₁.β ∧ ∀ x, ∃ w : Sp X₁.Ω₁ ⟶ w₁.G.left, w ≫ w₁.α = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) → ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), (∃ m : w₂.G.left ⟶ G₂.left, IsGrpPullback w₂.G G₂ (spMap (ratHull R₂).val.toRingHom) m ∧ m ≫ β₂ = w₂.β ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ w₂.G.left, w ≫ w₂.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left ∧ w ≫ m ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt x).left) → ∃ (P₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj P₀) (a : P₀.left ⟶ G.left) (a₂ : P₀.left ⟶ G₂.left), IsGrpPullback P₀ G (spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom)) a ∧ IsGrpPullback P₀ G₂ (spMap (ratHull R₂).val.toRingHom) a₂ ∧ a ≫ β = a₂ ≫ β₂ ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ P₀.left, w ≫ a ≫ α = spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) ≫ (ρ'.pt x).left ∧ w ≫ a₂ ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt (D.lab x)).left := by
  intro E _ _ _ H Dw l Xo cf C X₁ D w₁ w₂ hT c₀ hc R' fg frac hth hev ρ' G _ α β h1 c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ G₂ _
    α₂ β₂ h2
  obtain ⟨mT, pT, bT, tT⟩ := hT
  obtain ⟨m₁, p₁, b₁, t₁⟩ := h1
  obtain ⟨m₂, p₂, b₂, t₂⟩ := h2
  refine ⟨w₂.G, inferInstance, mT ≫ m₁, m₂, ?_, p₂, ?_, ?_⟩
  · exact (pT.comp p₁).congr (Geo.Tor.spMap_comp (ratHull R').val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁)).symm rfl
  · rw [Category.assoc, b₁, bT, b₂]
  · intro x
    obtain ⟨w, hw, hw'⟩ := tT x
    obtain ⟨w₁', hw₁, hw₁'⟩ := t₁ x
    obtain ⟨w₂', hw₂, hw₂'⟩ := t₂ (D.lab x)
    have s0 : w ≫ w₂.G.hom = 𝟙 _ := SameChain.sec_of_pt D.X.ρ w₂.α w₂.hα.1 w _ hw'
    have s1 : w₁' ≫ w₁.G.hom = 𝟙 _ := SameChain.sec_of_pt X₁.ρ w₁.α w₁.hα.1 w₁' _ hw₁
    have s2 : w₂' ≫ w₂.G.hom = 𝟙 _ := SameChain.sec_of_pt D.X.ρ w₂.α w₂.hα.1 w₂' _ hw₂
    have hwm : w ≫ mT = spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ w₁' := by
      apply w₁.hα.1.hom_ext
      · rw [Category.assoc, hw, Category.assoc, hw₁]
      · rw [Category.assoc, pT.1.w, ← Category.assoc, s0, Category.id_comp, Category.assoc, s1, Category.comp_id]
    have hwe : w = w₂' := by
      apply w₂.hα.1.hom_ext
      · rw [hw', hw₂]
      · rw [s0, s2]
    refine ⟨w, ?_, ?_⟩
    · rw [← Category.assoc, ← Category.assoc, hwm]
      simp only [Category.assoc]
      rw [hw₁', Geo.Tor.spMap_comp R'.val.toRingHom (algebraMap X₁.Ω₁ D.X.Ω₁), Category.assoc]
    · rw [hwe, hw₂']
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperIdentificationChainAgreesGenericallyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.deeper_identification_chain_agrees_generically : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), (∃ m : w₁.G.left ⟶ G.left, IsGrpPullback w₁.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = w₁.β ∧ ∀ x, ∃ w : Sp X₁.Ω₁ ⟶ w₁.G.left, w ≫ w₁.α = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) → ∀ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), (∃ m : w₂.G.left ⟶ G₂.left, IsGrpPullback w₂.G G₂ (spMap (ratHull R₂).val.toRingHom) m ∧ m ≫ β₂ = w₂.β ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ w₂.G.left, w ≫ w₂.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left ∧ w ≫ m ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt x).left) → ∃ (P₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj P₀) (a : P₀.left ⟶ G.left) (a₂ : P₀.left ⟶ G₂.left), IsGrpPullback P₀ G (spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (ratHull R').val.toRingHom)) a ∧ IsGrpPullback P₀ G₂ (spMap (ratHull R₂).val.toRingHom) a₂ ∧ a ≫ β = a₂ ≫ β₂ ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ P₀.left, w ≫ a ≫ α = spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp R'.val.toRingHom) ≫ (ρ'.pt x).left ∧ w ≫ a₂ ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt (D.lab x)).left := by
  first | exact @GlobalTheory.UPoinc.tied_chain_generic | exact GlobalTheory.UPoinc.tied_chain_generic | (intros; apply GlobalTheory.UPoinc.tied_chain_generic <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartThetaSystemUnitaryModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_affine_chart_thetaSystem_unitary_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (ρ'.pt x).left)) ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
  first | exact @GlobalTheory.UPoinc.exists_urechart_affine | exact GlobalTheory.UPoinc.exists_urechart_affine | (intros; apply GlobalTheory.UPoinc.exists_urechart_affine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperUnitarySetup

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ULiftW

theorem transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame X₁.ρ ρ' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → spMap (ratHull R').val.toRingHom ≫ u' = X₁.uΩ → R' ≤ X₁.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → (∃ m : w₁.G.left ⟶ G.left, IsGrpPullback w₁.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = w₁.β ∧ ∀ x, ∃ w : Sp X₁.Ω₁ ⟶ w₁.G.left, w ≫ w₁.α = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀), ∃ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (u₂' : Sp (ratHull R₂) ⟶ Xo.XF cf), USame D.X.ρ ρ₂ (fun x => x) (RingHom.id _) ∧ ρ₂.i₀ = D.X.ρ.i₀ ∧ spMap (ratHull R₂).val.toRingHom ≫ u₂' = D.X.uΩ ∧ R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) ∧ ∃ (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₂ ρ₂.P.A (spMap (toRat R₂)) α₂ ∧ IsGrpPullback G₂ Xo.univ.t.G (u₂' ≫ pullback.fst _ _) β₂ ∧ LBIso (ρ₂.P.L.pull α₂) (Xo.univ.t.PP.L.pull β₂) ∧ (∃ m : w₂.G.left ⟶ G₂.left, IsGrpPullback w₂.G G₂ (spMap (ratHull R₂).val.toRingHom) m ∧ m ≫ β₂ = w₂.β ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ w₂.G.left, w ≫ w₂.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left ∧ w ≫ m ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt x).left) ∧ ∃ y₂ : R₂ →+* PadicAlgCl p, (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) ∧ (∀ a : D.X.o₁, ‖y₂ (algebraMap D.X.o₁ R₂ a)‖ ≤ 1) ∧ ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧ (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧ (∀ x₂ (w₂ : Sp (PadicAlgCl p) ⟶ G₂.left), w₂ ≫ α₂ = x₂.left ≫ u₂.φ → ∃ w : Sp (PadicAlgCl p) ⟶ G.left, w ≫ α = (T x₂).left ≫ u.φ ∧ w ≫ β = w₂ ≫ β₂) ∧ (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧ (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p _ z₁ ct y h c₀ hc R' fg frac hth hev ρ' u' hS hi hu hR G _ α β hα hβ hL hm y₀ hy₀ u
  set w : D.X.M.Z := (gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)) with hw
  have hwr : D.X.π w ∈ Set.range C.i := by
    refine ⟨(spMap ct.ι ≫ ct.T.y) (IsLocalRing.closedPoint (PadicAlgCl p)), ?_⟩
    have h' := congrArg (fun f => f (IsLocalRing.closedPoint (PadicAlgCl p))) (D.lift ct y h).comm
    rw [hw]
    exact h'.symm
  obtain ⟨U, c₂, hc₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hUa, hwU, hS₂, hi₂, ⟨G₂, _, α₂, β₂, hα₂, hβ₂, hL₂, hm₂⟩, hu₂⟩ :=
    GlobalTheory.T.exists_affine_chart_thetaSystem_unitary_model E H Dw hpq l Xo cf C D.X w₂ w hwr
  have hle : D.X.M.ringOn (U : Set D.X.M.Z) ≤ D.X.M.O w := RatModel.ringOn_le_O hwU
  set y₂ : D.X.M.ringOn (U : Set D.X.M.Z) →+* PadicAlgCl p :=
    (D.X.M.valHom (gPt p ≫ y) w (RatModel.range_eq_singleton _ _)).comp (Subalgebra.inclusion hle).toRingHom with hy₂
  have hval : ∀ a : D.X.M.ringOn (U : Set D.X.M.Z), y₂ a = D.X.M.val (gPt p ≫ y) a := fun a => rfl
  have hint : ∀ a : D.X.o₁, ‖y₂ (algebraMap D.X.o₁ (D.X.M.ringOn (U : Set D.X.M.Z)) a)‖ ≤ 1 := by
    intro a
    rw [hval]
    exact RatModel.norm_val_le_one rfl (Subalgebra.algebraMap_mem _ a)
  have hch := GlobalTheory.T.deeper_identification_chain_agrees_generically E H Dw l Xo cf C X₁ D w₁ w₂ hT c₀ hc R' fg frac hth hev ρ' G inferInstance α β hm c₂ hc₂ _ fg₂ frac₂ hth₂ hev₂ ρ₂ G₂ inferInstance α₂ β₂ hm₂
  refine ⟨c₂, hc₂, D.X.M.ringOn (U : Set D.X.M.Z), fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hle, G₂, inferInstance, α₂, β₂, hα₂, hβ₂, hL₂, hm₂, y₂, hval, hint, ?_⟩
  exact GlobalTheory.T.uniformisedModel_transport_deeper_setup E H Dw l Xo cf C X₁ D p z₁ ct y h c₀ hc R' fg frac hth hev ρ' u' hS hi hu hR G inferInstance α β hα hβ hL y₀ hy₀ u c₂ hc₂ _ fg₂ frac₂ hth₂ hev₂ ρ₂ u₂' hS₂ hi₂ hu₂ hle G₂ inferInstance α₂ β₂ hα₂ hβ₂ hL₂ y₂ hval hint hch

end GlobalTheory.UPoinc.ULiftW
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperUnitarySetupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.uniformised_model_transport_deeper_unitary_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame X₁.ρ ρ' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → spMap (ratHull R').val.toRingHom ≫ u' = X₁.uΩ → R' ≤ X₁.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → (∃ m : w₁.G.left ⟶ G.left, IsGrpPullback w₁.G G (spMap (ratHull R').val.toRingHom) m ∧ m ≫ β = w₁.β ∧ ∀ x, ∃ w : Sp X₁.Ω₁ ⟶ w₁.G.left, w ≫ w₁.α = spMap X₁.S.R.val.toRingHom ≫ (X₁.ρ.pt x).left ∧ w ≫ m ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt x).left) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ ct.y) a) → ∀ (u : ρ'.UTest p y₀), ∃ (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (u₂' : Sp (ratHull R₂) ⟶ Xo.XF cf), USame D.X.ρ ρ₂ (fun x => x) (RingHom.id _) ∧ ρ₂.i₀ = D.X.ρ.i₀ ∧ spMap (ratHull R₂).val.toRingHom ≫ u₂' = D.X.uΩ ∧ R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) ∧ ∃ (G₂ : Over (Sp (ratHull R₂))) (_ : GrpObj G₂) (α₂ : G₂.left ⟶ ρ₂.P.A.left) (β₂ : G₂.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₂ ρ₂.P.A (spMap (toRat R₂)) α₂ ∧ IsGrpPullback G₂ Xo.univ.t.G (u₂' ≫ pullback.fst _ _) β₂ ∧ LBIso (ρ₂.P.L.pull α₂) (Xo.univ.t.PP.L.pull β₂) ∧ (∃ m : w₂.G.left ⟶ G₂.left, IsGrpPullback w₂.G G₂ (spMap (ratHull R₂).val.toRingHom) m ∧ m ≫ β₂ = w₂.β ∧ ∀ x, ∃ w : Sp D.X.Ω₁ ⟶ w₂.G.left, w ≫ w₂.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left ∧ w ≫ m ≫ α₂ = spMap R₂.val.toRingHom ≫ (ρ₂.pt x).left) ∧ ∃ y₂ : R₂ →+* PadicAlgCl p, (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) ∧ (∀ a : D.X.o₁, ‖y₂ (algebraMap D.X.o₁ R₂ a)‖ ≤ 1) ∧ ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧ (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧ (∀ x₂ (w₂ : Sp (PadicAlgCl p) ⟶ G₂.left), w₂ ≫ α₂ = x₂.left ≫ u₂.φ → ∃ w : Sp (PadicAlgCl p) ⟶ G.left, w ≫ α = (T x₂).left ≫ u.φ ∧ w ≫ β = w₂ ≫ β₂) ∧ (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧ (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  first | exact @GlobalTheory.UPoinc.ULiftW.transport | exact GlobalTheory.UPoinc.ULiftW.transport | (intros; apply GlobalTheory.UPoinc.ULiftW.transport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsExtendToDeeperLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.ULift

theorem psiQ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab) (q : u.D.toPre.X → ℝ) (hq : ∀ χ, u.PsiNorm χ (Real.exp (-q χ))) (χ : u.D.toPre.X) : l.q χ = q χ := by
  have h := Real.exp_injective (GlobalTheory.ZH.RealCase.psiNorm_unique u χ (l.q_eq χ) (hq χ))
  linarith



theorem labels_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLabW X₁ w₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLabW D.X w₂ (D.lift ct y h) yy ∧ D.Compat yy₁ yy := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p _ z₁ ct yy₁ hL y h
  unfold UIsLabW at hL
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', hS, hi, hu, hR, G, iG, α, β, hα, hβ, hLB, hm, y₀, hy₀, u, lb, j,
    hq, hyy, hcong⟩ := hL
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hR₂, G₂, iG₂, α₂, β₂, hα₂, hβ₂, hLB₂, hm₂,
    y₂, hy₂, hint₂, u₂, e, T, hpsi, hpt, hw, hfw, hbw⟩ :=
    GlobalTheory.T.uniformised_model_transport_deeper_unitary_setup E H Dw hpq l Xo cf C X₁ D w₁ w₂ hT p z₁ ct y h c₀ hc R' fg frac hth hev ρ' u' hS hi hu hR G iG α β
      hα hβ hLB hm y₀ hy₀ u
  obtain ⟨hLaws, hLaws2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨lb₂⟩ := GlobalTheory.ZH.labels_exist hLaws hLaws2 GlobalTheory.ZH.uTors_closed _ _ _ ρ₂ p y₂ u₂ hint₂
  have hmap : (nsmulAddMonoidHom (D.X.S.r * D.X.S.N) : u₂.D.toPre.X →+ u₂.D.toPre.X).range ≤
      AddSubgroup.comap (e.trans j).toAddMonoidHom
        (nsmulAddMonoidHom (D.X.S.r * D.X.S.N) : ct.T.P.D.toPre.X →+ ct.T.P.D.toPre.X).range := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(e.trans j) z, by simp [map_nsmul]⟩
  refine ⟨(QuotientAddGroup.map _ _ (e.trans j).toAddMonoidHom hmap).comp lb₂.yy, ?_, ?_⟩
  · unfold UIsLabW
    refine ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, u₂', hS₂, hi₂, hu₂, hR₂, G₂, iG₂, α₂, β₂, hα₂, hβ₂, hLB₂, hm₂,
      y₂, hy₂, u₂, lb₂, e.trans j, ?_, ?_, ?_⟩
    · intro χ
      rw [psiQ u₂ lb₂ (fun χ => lb.q (e χ)) (fun χ => hpsi χ _ (lb.q_eq (e χ))) χ]
      exact hq (e χ)
    · intro a χ hχ
      rw [AddMonoidHom.comp_apply, hχ, QuotientAddGroup.map_mk]
      rfl
    · intro k a pk pk' x x' w w' hk hx hx' hwx hwx' hww
      obtain ⟨q, hqy, hq'⟩ := hfw k pk x hk hx
      obtain ⟨q', hqy', hq''⟩ := hfw k pk' x' hk hx'
      obtain ⟨v, hvα, hvβ⟩ := hw x w hwx
      obtain ⟨v', hvα', hvβ'⟩ := hw x' w' hwx'
      have hc := hcong k a q q' (T x) (T x') v v' hk hq' hq'' hvα hvα'
        (by rw [hvβ', hww, ← Category.assoc v, hvβ, Category.assoc])
      rw [hqy, hqy'] at hc
      exact hc
  · unfold UDeep.Compat
    intro a μ hμ
    have hN₁ : 0 < X₁.S.N := by rw [X₁.ρ.N_eq]; exact pow_pos (pow_pos X₁.ρ.n_prime.pos _) _
    have hr₁ : 0 < X₁.S.r := by
      obtain ⟨i, -, hi'⟩ := X₁.ρ.r_eq
      rw [hi']; exact pow_pos X₁.ρ.n_prime.pos _
    have hN₂ : 0 < D.X.S.N := by rw [D.X.ρ.N_eq]; exact pow_pos (pow_pos D.X.ρ.n_prime.pos _) _
    have hr₂ : 0 < D.X.S.r := by
      obtain ⟨i, -, hi'⟩ := D.X.ρ.r_eq
      rw [hi']; exact pow_pos D.X.ρ.n_prime.pos _
    have hk1 : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos hr₁ hN₁
    have hk2 : 1 ≤ D.X.S.r * D.X.S.N := Nat.mul_pos hr₂ hN₂
    have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
      rw [D.sq]
      exact Dvd.dvd.mul_left (D.dvd.trans (dvd_pow_self _ two_ne_zero)) _
    have hd : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) * (X₁.S.r * X₁.S.N) = D.X.S.r * D.X.S.N :=
      Nat.div_mul_cancel hdvd
    have hd1 : 1 ≤ D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) := Nat.div_pos (Nat.le_of_dvd hk2 hdvd) hk1
    obtain ⟨pk₀, x₀, hx₀, hx₀φ⟩ := GlobalTheory.Poinc.exists_qkPt_of_utest _ _ _ ρ' p y₀ u a
    have h1 : lb.yy a = QuotientAddGroup.mk pk₀.y := lb.yy_eq a pk₀ x₀ hx₀ hx₀φ
    have h2 := hyy a pk₀.y h1
    obtain ⟨pk', hpk'y, hpk'⟩ := GlobalTheory.QLevelRescale.exists_qkPt_rescale _ _ _ ρ' p y₀ u (X₁.S.r * X₁.S.N)
      (D.X.S.r * D.X.S.N) (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) pk₀ x₀ hk1 hd1 hd.symm hx₀
    obtain ⟨pk₂, hpk₂y, hpk₂⟩ := hbw _ pk' x₀ hk2 hpk'
    have hx₂ : (T.symm x₀).left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left :=
      (hpt (T.symm x₀) a).2 (by rw [Equiv.apply_symm_apply]; exact hx₀φ)
    have h3 : lb₂.yy (D.lab a) = QuotientAddGroup.mk pk₂.y := lb₂.yy_eq (D.lab a) pk₂ (T.symm x₀) hpk₂ hx₂
    rw [AddMonoidHom.comp_apply, h3, QuotientAddGroup.map_mk]
    have h4 : (e.trans j).toAddMonoidHom pk₂.y = (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • j pk₀.y := by
      show j (e pk₂.y) = _
      rw [hpk₂y, hpk'y, map_nsmul]
    rw [h4]
    rw [h2] at hμ
    rw [QuotientAddGroup.eq] at hμ ⊢
    obtain ⟨z, hz⟩ := hμ
    refine ⟨z, ?_⟩
    rw [nsmulAddMonoidHom_apply] at hz ⊢
    calc (D.X.S.r * D.X.S.N) • z
        = (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) • (X₁.S.r * X₁.S.N) • z := by rw [smul_smul, hd]
      _ = _ := by rw [hz, smul_add, smul_neg]

end GlobalTheory.UPoinc.ULift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsExtendToDeeperLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) (w₂ : UWit D.X), D.Comparison₂ w₁ w₂ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLabW X₁ w₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLabW D.X w₂ (D.lift ct y h) yy ∧ D.Compat yy₁ yy := by
  first | exact @GlobalTheory.UPoinc.ULift.labels_lift | exact GlobalTheory.UPoinc.ULift.labels_lift | (intros; apply GlobalTheory.UPoinc.ULift.labels_lift <;> assumption)
end
end
