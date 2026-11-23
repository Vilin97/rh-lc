module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

-- Source module: Formalism.LocalToGlobal.ProjectiveLattices.TensPtsSt

section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {X : Scheme.{0}} (A : Over X)

def powO : ℕ → Over X
  | 0 => 𝟙_ (Over X)
  | k + 1 => A ⊗ powO k

def prj : (k : ℕ) → Fin k → (powO A k ⟶ A)
  | 0, j => j.elim0
  | k + 1, j => Fin.cases (fst A (powO A k)) (fun j' => snd A (powO A k) ≫ prj k j') j

def tup {T : Over X} : (k : ℕ) → (Fin k → (T ⟶ A)) → (T ⟶ powO A k)
  | 0, _ => toUnit T
  | k + 1, a => lift (a 0) (tup k fun j => a j.succ)

variable [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O] (act : OAct O A)

def matMap {k : ℕ} (e : Fin k → Fin k → O) : powO A k ⟶ powO A k :=
  tup A k fun i => psum A (fun j => prj A k j ≫ act.act (e i j)) Finset.univ

abbrev tensSch {k : ℕ} (e : Fin k → Fin k → O) : Scheme.{0} :=
  pullback (lift (matMap A act e) (𝟙 (powO A k))).left (lift (𝟙 (powO A k)) (𝟙 (powO A k))).left

def tensO {k : ℕ} (e : Fin k → Fin k → O) : Over X :=
  Over.mk (pullback.fst _ _ ≫ (powO A k).hom : tensSch A act e ⟶ X)

def tensIncl {k : ℕ} (e : Fin k → Fin k → O) : tensO A act e ⟶ powO A k :=
  Over.homMk (pullback.fst _ _) rfl

def tcoord {k : ℕ} (e : Fin k → Fin k → O) (j : Fin k) : tensO A act e ⟶ A :=
  tensIncl A act e ≫ prj A k j


end Formalism.L2.Pj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RankMulFinrank

section

@[expose] public section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LieRankSum

theorem sum_lieMult {E : Type} [Field E] [NumberField E] {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {g : ℕ} (hG : SmoothOfRelativeDimension g G.hom) (act : OAct (𝓞 E) G) {k : Type} [Field k] [IsAlgClosed k]
    [CharZero k] (t : Sp k ⟶ S) (rk : (𝓞 E →+* k) → ℕ) (h : ∀ σ, LieMult act t σ (rk σ)) :
    ∑ σ : E →+* k, rk (σ.comp (algebraMap (𝓞 E) E)) = g := by
  classical
  have hk := isGrpPullback_pullback G t
  have hd : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hk.1 hG
  obtain ⟨v, hv⟩ := GlobalTheory.KeyPow.exists_isLieBasis _ hd
  let actk := OAct.pullback t G act
  have hak : ∀ a, (actk.act a).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ (act.act a).left :=
    fun a => pullback.lift_fst _ _ _
  obtain ⟨ρ, hρ⟩ := LieEigen.exists_action hv actk
  have hinj : Function.Injective fun σ : E →+* k => σ.comp (algebraMap (𝓞 E) E) := fun σ σ' e =>
    IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => RingHom.congr_fun e x
  have hσ : EigenSplit.IsSplitting fun σ : E →+* k => (RingHom.id k).comp (σ.comp (algebraMap (𝓞 E) E)) :=
    EigenSplit.isSplitting_of_isDomain hinj (NumberField.Embeddings.card E k) _
      (EigenSplit.isUnit_discr_of_charZero k)
  have hint := EigenSplit.isInternal_eigenSub hσ ρ
  have e := (LinearEquiv.ofBijective (DirectSum.coeLinearMap _) hint).finrank_eq
  rw [Module.finrank_directSum, Module.finrank_fin_fun] at e
  rw [← e]
  exact Finset.sum_congr rfl fun σ _ => (LieEigen.finrank_of_lieMult hk hv hak hρ (h _)).symm

theorem rank_mul_finrank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (act : OAct (𝓞 E) G) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : Sp k ⟶ S) (rk : (𝓞 E →+* k) → ℕ) (r : ℕ), (∀ σ : 𝓞 E →+* k, LieMult act t σ (rk σ) ∧ rk σ + rk (σ.comp (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)) = r) → r * Module.finrank ℚ E = 2 * g := by
  intro E _ _ _ S G _ _ g hG act k _ _ _ t rk r h
  have h₁ := sum_lieMult hG act t rk fun σ => (h σ).1
  let c : (E →+* k) ≃ (E →+* k) :=
    ⟨fun σ => σ.comp (IsCMField.complexConj E : E →+* E), fun σ => σ.comp (IsCMField.complexConj E : E →+* E),
      fun σ => RingHom.ext fun a => by simp, fun σ => RingHom.ext fun a => by simp⟩
  have h₂ := (Equiv.sum_comp c fun σ => rk (σ.comp (algebraMap (𝓞 E) E))).trans h₁
  have h₃ : ∑ σ : E →+* k, (rk (σ.comp (algebraMap (𝓞 E) E)) + rk ((c σ).comp (algebraMap (𝓞 E) E))) =
      ∑ _σ : E →+* k, r := Finset.sum_congr rfl fun σ _ => (h _).2
  rw [Finset.sum_add_distrib, h₁, h₂, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    smul_eq_mul] at h₃
  rw [mul_comm, ← h₃, two_mul]

end GlobalTheory.LieRankSum
end
end
