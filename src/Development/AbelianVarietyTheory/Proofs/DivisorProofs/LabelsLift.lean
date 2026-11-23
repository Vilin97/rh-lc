module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.DeltaIsGreatest
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPoint
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemMovedToAffineOpenStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperThetaSetup
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointRescaleSameTorsionPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_levelPoint_rescale_same_torsionPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k k' d : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ k → 1 ≤ d → k' = d * k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → ∃ pk' : QkPt u.D.toPre (PadicAlgCl p) k', pk'.y = d • pk.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) k' pk' x := by
  first | exact @GlobalTheory.QLevelRescale.exists_qkPt_rescale | exact GlobalTheory.QLevelRescale.exists_qkPt_rescale | (intros; apply GlobalTheory.QLevelRescale.exists_qkPt_rescale <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaTorsionPreimageUniformisedModelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_thetaTorsion_preimage_uniformised_model : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : S.Gam), ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left := by
  first | exact @GlobalTheory.Poinc.exists_qkPt_of_utest | exact GlobalTheory.Poinc.exists_qkPt_of_utest | (intros; apply GlobalTheory.Poinc.exists_qkPt_of_utest <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupRescaleIntoLocalRingClassicalTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLiftRechart

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X.M.s → ∀ (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z), ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧ ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := by
  intro g n F W Z i X hg hn ho himm he8 hth hproj ε hε p _ z c
  set w : X.M.Z := (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) with hw
  have hwr : X.π w ∈ Set.range i := by
    refine ⟨(spMap c.ι ≫ c.T.y) (IsLocalRing.closedPoint (PadicAlgCl p)), ?_⟩
    have h := congrArg (fun f => f (IsLocalRing.closedPoint (PadicAlgCl p))) c.comm
    rw [hw]
    exact h.symm
  obtain ⟨U, c₀, hc, fg, frac, hth', hev, ρ', ε', u', hUa, hwU, hUi, hSame, hi₀, hdiag, hcomp⟩ :=
    GlobalTheory.T.exists_thetaSystem_moved_to_affineOpen g n F W Z i X hg hn ho himm he8 hth hproj ε hε w hwr
  have hle : X.M.ringOn (U : Set X.M.Z) ≤ X.M.O w := RatModel.ringOn_le_O hwU
  refine ⟨c₀, hc, X.M.ringOn (U : Set X.M.Z), fg, frac, hth', hev, ρ', ε', hSame, hi₀, hle, ?_⟩
  refine ⟨(X.M.valHom (gPt p ≫ c.y) w (RatModel.range_eq_singleton _ _)).comp
    (Subalgebra.inclusion hle).toRingHom, fun a => rfl, fun a => ?_⟩
  have hmem : algebraMap X.o₁ X.Ω₁ a ∈ X.M.O z := Subalgebra.algebraMap_mem _ a
  have h1 := c.norm_val_le ((X.M.stalkEquiv z).symm ⟨_, hmem⟩)
  simp only [CTrait.val] at h1
  rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply] at h1
  simpa using h1

end GlobalTheory.Poinc.GLiftRechart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupRescaleIntoLocalRingClassicalTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaSetup_rescale_into_localRing_classicalTrait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X.M.s → ∀ (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z), ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧ ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := by
  first | exact @GlobalTheory.Poinc.GLiftRechart.main | exact GlobalTheory.Poinc.GLiftRechart.main | (intros; apply GlobalTheory.Poinc.GLiftRechart.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedModelTransportDeeperThetaSetupStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.uniformisedModel_transport_deeperThetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y)
  (c₀ : X₁.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X₁.o₁ X₁.Ω₁) (fg : R'.FG) (frac : ∀ x : X₁.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X₁.S.th x ∈ R') (hev : ∀ x k, c₀ * X₁.S.ev x k ∈ R') (ρ' : (X₁.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X₁.ρ ε₁ ρ' ε' (fun x => x) (RingHom.id _) → ρ'.i₀ = X₁.ρ.i₀ → R' ≤ X₁.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : R' →+* PadicAlgCl p), (∀ a : R', y₀ a = X₁.M.val (gPt p ≫ c.y) a) → ∀ (u : ρ'.UTest p y₀)
  (c₂ : D.X.Ω₁) (hc₂ : c₂ ≠ 0) (R₂ : Subalgebra D.X.o₁ D.X.Ω₁) (fg₂ : R₂.FG) (frac₂ : ∀ x : D.X.Ω₁, ∃ a ∈ R₂, ∃ b ∈ R₂, x = a / b) (hth₂ : ∀ x, c₂ * D.X.S.th x ∈ R₂) (hev₂ : ∀ x k, c₂ * D.X.S.ev x k ∈ R₂) (ρ₂ : (D.X.S.rechart c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂).Real) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)), Same D.X.ρ D.ε ρ₂ ε₂ (fun x => x) (RingHom.id _) → ρ₂.i₀ = D.X.ρ.i₀ → R₂ ≤ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) → ∀ (y₂ : R₂ →+* PadicAlgCl p), (∀ a : R₂, y₂ a = D.X.M.val (gPt p ≫ y) a) →
  ∃ (u₂ : ρ₂.UTest p y₂) (e : u₂.D.toPre.X ≃+ u.D.toPre.X) (T : (TFK (R := u₂.V) (PadicAlgCl p) ⟶ u₂.A.A) ≃ (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)),
    (∀ χ r, u.PsiNorm (e χ) r → u₂.PsiNorm χ r) ∧
    (∀ x₂ a, x₂.left ≫ u₂.φ = spMap y₂ ≫ (ρ₂.pt (D.lab a)).left ↔ (T x₂).left ≫ u.φ = spMap y₀ ≫ (ρ'.pt a).left) ∧
    (∀ x₂ x₂' E, x₂'.left ≫ u₂.φ = x₂.left ≫ u₂.φ ≫ (ε₂ E).left → (T x₂').left ≫ u.φ = (T x₂).left ≫ u.φ ≫ (ε' E).left) ∧
    (∀ (m : ℕ) (pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m) x₂, 1 ≤ m → QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ x₂ → ∃ pk : QkPt u.D.toPre (PadicAlgCl p) m, pk.y = e pk₂.y ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk (T x₂)) ∧
    (∀ (m : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) m) x, 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → ∃ pk₂ : QkPt u₂.D.toPre (PadicAlgCl p) m, e pk₂.y = pk.y ∧ QkToAkU u₂.U.toUnifPre (PadicAlgCl p) m pk₂ (T.symm x)) := by
  first | exact @GlobalTheory.Poinc.GLift.transport | exact GlobalTheory.Poinc.GLift.transport | (intros; apply GlobalTheory.Poinc.GLift.transport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsLift

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLift

theorem psiQ : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (q : u.D.toPre.X → ℝ), (∀ χ, u.PsiNorm χ (Real.exp (-q χ))) → ∀ χ, l.q χ = q χ := by
  intro o Ω _ _ _ S ρ p _ y₀ u l q hq χ
  have := GlobalTheory.ZH.RealCase.psiNorm_unique u χ (l.q_eq χ) (hq χ)
  exact neg_injective (Real.exp_injective this)

theorem labels_lift : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), ∃ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy ∧ D.Compat yy₁ yy := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ c yy₁ hLab y h
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', hS, hi, hR, y₀, hy₀, u, l, j, hq, hyy, hmat⟩ := hLab
  obtain ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hS₂, hi₂, hR₂, y₂, hy₂, hint₂⟩ :=
    GlobalTheory.T.thetaSetup_rescale_into_localRing_classicalTrait g n F W Z i D.X hg hn hodd himm he8 hth D.proj D.ε D.diag p (y (cPt p)) (D.lift c y h)
  obtain ⟨u₂, e, T, hpsi, htor, heps, hfw, hbw⟩ := GlobalTheory.T.uniformisedModel_transport_deeperThetaSetup g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c y h
    c₀ hc R' fg frac hth' hev ρ' ε' hS hi hR y₀ hy₀ u c₂ hc₂ R₂ fg₂ frac₂ hth₂ hev₂ ρ₂ ε₂ hS₂ hi₂ hR₂ y₂ hy₂
  obtain ⟨l₂⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed _ _ _ ρ₂ p y₂ u₂ hint₂
  set L₂ : ℕ := D.X.S.r * D.X.S.N with hL₂
  set L₁ : ℕ := X₁.S.r * X₁.S.N with hL₁
  let jj : u₂.D.toPre.X ≃+ (Fin 8 → c.T.D.toPre.X) := e.trans j
  have hrange : (nsmulAddMonoidHom L₂ : u₂.D.toPre.X →+ u₂.D.toPre.X).range ≤
      ((nsmulAddMonoidHom L₂ : (Fin 8 → c.T.D.toPre.X) →+ (Fin 8 → c.T.D.toPre.X)).range).comap jj.toAddMonoidHom := by
    rintro _ ⟨z, rfl⟩
    exact ⟨jj z, by simp⟩
  let f := QuotientAddGroup.map _ _ jj.toAddMonoidHom hrange
  have hf : ∀ χ, f (QuotientAddGroup.mk χ) = QuotientAddGroup.mk (jj χ) := fun χ => rfl
  refine ⟨f.comp l₂.yy, ⟨c₂, hc₂, R₂, fg₂, frac₂, hth₂, hev₂, ρ₂, ε₂, hS₂, hi₂, hR₂, y₂, hy₂, u₂, l₂, jj, ?_, ?_, ?_⟩, ?_⟩
  · intro χ
    rw [GlobalTheory.Poinc.GLift.psiQ _ _ _ ρ₂ p y₂ u₂ l₂ (fun χ => l.q (e χ)) (fun χ => hpsi χ _ (l.q_eq (e χ))) χ]
    exact hq (e χ)
  · intro a χ ha
    simp only [AddMonoidHom.comp_apply, ha]
    rfl
  · intro m pk pk' x x' E hm hx hx' hxx
    obtain ⟨q₁, hq₁y, hq₁⟩ := hfw m pk x hm hx
    obtain ⟨q₁', hq₁y', hq₁'⟩ := hfw m pk' x' hm hx'
    have := hmat m q₁ q₁' (T x) (T x') E hm hq₁ hq₁' (heps x x' E hxx)
    rw [hq₁y, hq₁y'] at this
    exact this
  · intro a μ hμ
    obtain ⟨pk, x, hx, hxa⟩ := GlobalTheory.T.exists_thetaTorsion_preimage_uniformised_model _ _ _ ρ' p y₀ u a
    have h1 := l.yy_eq a pk x hx hxa
    have h2 := hyy a pk.y h1
    have hL₁pos : 1 ≤ L₁ := by
      obtain ⟨jr, hjr, hr⟩ := X₁.ρ.r_eq
      have h1' : 0 < X₁.S.r := by rw [hr]; exact pow_pos X₁.ρ.n_prime.pos _
      have h2' : 0 < X₁.S.N := by rw [X₁.ρ.N_eq]; exact pow_pos (pow_pos X₁.ρ.n_prime.pos _) _
      exact Nat.mul_pos h1' h2'
    have hdvd : L₁ ∣ L₂ := by
      obtain ⟨t, ht⟩ := D.dvd
      refine ⟨t * (D.m * D.X.S.r), ?_⟩
      rw [hL₂, D.sq, ht]; ring
    have hL₂pos : 1 ≤ L₂ := by
      obtain ⟨jr, hjr, hr⟩ := D.X.ρ.r_eq
      have h1' : 0 < D.X.S.r := by rw [hr]; exact pow_pos D.X.ρ.n_prime.pos _
      have h2' : 0 < D.X.S.N := by rw [D.X.ρ.N_eq]; exact pow_pos (pow_pos D.X.ρ.n_prime.pos _) _
      exact Nat.mul_pos h1' h2'
    have hdpos : 1 ≤ L₂ / L₁ := by
      rw [Nat.one_le_div_iff (by omega)]
      exact Nat.le_of_dvd (by omega) hdvd
    obtain ⟨pk', hpk'y, hpk'⟩ := GlobalTheory.T.exists_levelPoint_rescale_same_torsionPoint _ _ _ ρ' p y₀ u L₁ L₂ (L₂ / L₁) pk x hL₁pos hdpos
      (Nat.div_mul_cancel hdvd).symm hx
    obtain ⟨pk₂, hpk₂y, hpk₂⟩ := hbw L₂ pk' x hL₂pos hpk'
    have h3 := (htor (T.symm x) a).2 (by simpa using hxa)
    have h4 := l₂.yy_eq (D.lab a) pk₂ (T.symm x) hpk₂ h3
    show f (l₂.yy (D.lab a)) = _
    rw [h4, hf]
    have h5 : jj pk₂.y = (L₂ / L₁) • j pk.y := by
      show j (e pk₂.y) = _
      rw [hpk₂y, hpk'y, map_nsmul]
    rw [h5]
    rw [hμ] at h2
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq).1 h2.symm
    apply (QuotientAddGroup.eq).2
    refine ⟨z, ?_⟩
    simp only [nsmulAddMonoidHom_apply] at hz ⊢
    rw [← smul_neg, ← smul_add, ← hz, smul_smul, Nat.div_mul_cancel hdvd]

end GlobalTheory.Poinc.GLift
end
end
