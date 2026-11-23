module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendIntegralPadicEvaluationGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureGaloisFiniteAutGroupInvariantsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourierClassSumsMemIntegralClosureGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalTraitSystemAtClosedPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModule
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefMapIntOfPos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqLeOfForallNonneg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.thetaSetup_stalk_noetherian_normal_fractionRing : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra; IsDomain (X₁.M.Z.presheaf.stalk z₁) ∧ IsFractionRing (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ ∧ IsIntegrallyClosed (X₁.M.Z.presheaf.stalk z₁) ∧ IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  first | exact @GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing | exact GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing | (intros; apply GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourierClassSumsDeeperFiniteExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem classSums_deeper : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 8 → Φ.X y) → Q → PadicAlgCl p) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (X₁.M.Z.presheaf.stalk z₁) B) (_ : Module.Finite (X₁.M.Z.presheaf.stalk z₁) B) (_ : Finite (B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B)) (𝔷 : Ideal B), Function.Injective (algebraMap (X₁.M.Z.presheaf.stalk z₁) B) ∧ (∀ b : B, (∀ σ : B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B, σ b = b) → b ∈ Set.range (algebraMap (X₁.M.Z.presheaf.stalk z₁) B)) ∧ 𝔷.IsMaximal ∧ k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod ℤ N (k y)) ∧ Φ.IsTerms W t ∧ Φ.ClassSums (X₁.S.r * X₁.S.N) N y₀ k t B 𝔷 := by
  intro g n F W Z i X₁ p _ z₁ Φ hΦ y₀ N₀
  obtain ⟨N, hN₀, hdvd, Ω₂, _, _, _, _, hcore⟩ := GlobalTheory.T.thetaFourier_classSums_mem_integralClosure_galois g n F W Z i X₁ p z₁ Φ hΦ y₀ N₀
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  obtain ⟨hdom, hfr, hic, hno⟩ := GlobalTheory.T.thetaSetup_stalk_noetherian_normal_fractionRing g n F W Z i X₁ z₁
  obtain ⟨hfin, hfinA, hinj, hfix⟩ := GlobalTheory.T.integralClosure_galois_finite_autGroup_invariants (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ Ω₂
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra
  obtain ⟨𝔷, hmax⟩ := Ideal.exists_maximal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)
  have hext := fun y => GlobalTheory.T.extend_integral_padic_evaluation_galois p (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) 𝔷 hinj hfix hmax (Φ.ev y) (Φ.ev_le y) (Φ.ev_lt y)
  choose ev' h1 h2 h3 using hext
  obtain ⟨k, Q, t, f, hk₀, hk, ht, hf, hcs, hgal⟩ := hcore 𝔷 hmax ev' h1 h2 h3
  refine ⟨N, hN₀, hdvd, k, Q, t, (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), inferInstance, inferInstance, inferInstance, hfin, hfinA, 𝔷, hinj, hfix, hmax, hk₀, hk, ht, ev', f, h1, h2, h3, hf, hcs, fun σ hσ => ?_⟩
  obtain ⟨γ, hdet, hN₁, hσf⟩ := hgal σ hσ
  refine ⟨γ, fun c x => ⟨0, ?_⟩, hdet, hN₁, hσf⟩
  have hm : (Φ.mod y₀) = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  rw [smul_zero, add_zero]
  first
  | (rw [hm]; exact map_zsmul γ c x)
  | (simp only [hm]; exact map_zsmul γ c x)
  | exact map_smul γ c x

end GlobalTheory.Poinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourierClassSumsDeeperFiniteExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.thetaFourier_classSums_deeper_finite_extension : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 8 → Φ.X y) → Q → PadicAlgCl p) (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (X₁.M.Z.presheaf.stalk z₁) B) (_ : Module.Finite (X₁.M.Z.presheaf.stalk z₁) B) (_ : Finite (B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B)) (𝔷 : Ideal B), Function.Injective (algebraMap (X₁.M.Z.presheaf.stalk z₁) B) ∧ (∀ b : B, (∀ σ : B ≃ₐ[X₁.M.Z.presheaf.stalk z₁] B, σ b = b) → b ∈ Set.range (algebraMap (X₁.M.Z.presheaf.stalk z₁) B)) ∧ 𝔷.IsMaximal ∧ k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod ℤ N (k y)) ∧ Φ.IsTerms W t ∧ Φ.ClassSums (X₁.S.r * X₁.S.N) N y₀ k t B 𝔷 := by
  first | exact @GlobalTheory.Poinc.classSums_deeper | exact GlobalTheory.Poinc.classSums_deeper | (intros; apply GlobalTheory.Poinc.classSums_deeper <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitsFourierTermsAllLevels

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem Setup.isNoetherianRing_stalk {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} (X₁ : Setup F W i) (z₁ : X₁.M.Z) : IsNoetherianRing (X₁.M.Z.presheaf.stalk z₁) := by
  have : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  have := X₁.M.lft
  have : IsLocallyNoetherian (Sp X₁.o₁) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
  have : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  infer_instance

theorem four_of_classical : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), PosW W → (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → Φ.Four W (X₁.S.r * X₁.S.N) := by
  intro g n F W Z i X₁ p _ z₁ Φ hW h y₀ N₀
  obtain ⟨N, hN, hd, k, Q, t, B, _, _, _, _, _, 𝔷, hinj, hfix, hmax, hk, hu, ht, hc⟩ :=
    GlobalTheory.T.thetaFourier_classSums_deeper_finite_extension g n F W Z i X₁ p z₁ Φ h y₀ (N₀ + 1)
  have := X₁.normal.isDomain_stalk z₁
  have := X₁.normal.isIntegrallyClosed_stalk z₁
  have := X₁.isNoetherianRing_stalk z₁
  have hu' : ∀ y, @IsUnimodMod ℤ _ (Φ.X y₀) (Φ.X y) _ (Φ.mod y₀) _ (Φ.mod y) N (k y) := fun y => by
    convert hu y <;> exact Subsingleton.elim _ _
  exact ⟨N, by omega, hd, k, Q, t, hk, hu', ht,
    OrbTrace.orbitSums_of_classSums ℤ id g p _ Φ 8 W _ N y₀ k Q t B hinj hfix 𝔷 hmax (by omega) hW hu' hc⟩

end GlobalTheory.Poinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitsFourierTermsAllLevelsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.classical_traits_fourier_terms_all_levels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), PosW W → (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → Φ.Four W (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.Poinc.four_of_classical | exact GlobalTheory.Poinc.four_of_classical | (intros; apply GlobalTheory.Poinc.four_of_classical <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxPoincareSeriesAtThetaSetupPoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.GApprox

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem sc_pos {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) : 0 < c.sc := by
  set u := algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ with hu
  have h0 : c.T.ϖ ≠ 0 := c.T.irr.ne_zero
  have hu0 : u ≠ 0 := by
    rw [hu]; exact (IsFractionRing.injective c.T.V (FractionRing c.T.V)).ne_iff' (map_zero _) |>.2 h0
  have hι0 : c.ι u ≠ 0 := (map_ne_zero c.ι).2 hu0
  have hle : ‖c.ι u‖ ≤ 1 := (c.int u).2 ⟨_, rfl⟩
  have hlt : ‖c.ι u‖ < 1 := by
    refine lt_of_le_of_ne hle fun h1 => ?_
    have : ‖c.ι u⁻¹‖ ≤ 1 := by rw [map_inv₀, norm_inv, h1, inv_one]
    obtain ⟨v, hv⟩ := (c.int _).1 this
    apply c.T.irr.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective c.T.V (FractionRing c.T.V)
    rw [map_mul, hv, ← hu, mul_inv_cancel₀ hu0, map_one]
  have hpos : 0 < ‖c.ι u‖ := norm_pos_iff.2 hι0
  unfold CTrait.sc
  rw [← hu]
  linarith [Real.log_neg hpos hlt]

theorem sc_evalZ_eq_of_equiv {φ : InvFun ℤ} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [Module.Finite ℤ X]
    [Module.Finite ℤ Y] (hP : IsPolFanOn id φ X) {β : LinearMap.BilinForm ℤ X} (hs : ∀ a b, β a b = β b a)
    (hp : ∀ x, 0 ≤ β x x) {β' : LinearMap.BilinForm ℤ Y} {s s' : ℝ} (hs0 : 0 ≤ s) (hs' : 0 < s') (e : X ≃ₗ[ℤ] Y)
    (he : ∀ a b, s * β a b = s' * β' (e a) (e b)) : s * φ.evalZ β = s' * φ.evalZ β' := by
  have hmem : toReal β ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) :=
    StrictData.toReal_mem_psdCone (mem_balForms_int.2 hs) hp
  have hform : toReal (pull e.toLinearMap β') = (s / s') • toReal β := by
    refine LinearMap.ext₂ fun a b => ?_
    have := he a b
    simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul, LinearEquiv.coe_coe]
    field_simp
    linarith
  have h1 : φ.evalZ (pull e.toLinearMap β') = φ.evalZ β' := evalZ_pull φ e.surjective _
  rw [← h1, ← evalR_toReal φ (pull _ _), hform, hP.homog _ hmem _ (div_nonneg hs0 hs'.le), evalR_toReal]
  field_simp

theorem sc_evalZ_eq {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} {φ : InvFun ℤ} (hpol : IsPolFan id g φ)
    (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (c : CTrait X₁ p z₁)
    (e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X) (he : ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) :
    Φ.sc y * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y) = c.sc * φ.evalZ c.T.β := by
  have hm : Φ.mod y = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  have hrk : Module.finrank ℤ (Φ.X y) ≤ g := by
    convert Φ.rank_le y <;> first | rfl | exact hm.symm
  have hP : IsPolFanOn id φ (Φ.X y) := hpol _ hrk
  convert sc_evalZ_eq_of_equiv hP (Φ.bal y).1 (fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · exact (Φ.pos y x hx).le) (Φ.sc_pos y).le (sc_pos c) e he

end GlobalTheory.Poinc.GApprox

namespace GlobalTheory.Poinc.GApprox

theorem exists_hasSupports_int (q : ℕ) (φ : InvFun ℤ) (hpol : IsPolFan id q φ) :
    ∃ d, 1 ≤ d ∧ HasSupports (id : ℤ → ℤ) q φ d := by
  refine exists_hasSupports ℤ id q φ hpol fun X _ iM _ _ hX r γ hγ => ?_
  obtain rfl : iM = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  have : Module.Free ℤ X := inferInstance
  exact exists_supports_int φ X (hpol X hX) r γ hγ

end GlobalTheory.Poinc.GApprox

open GlobalTheory.Poinc.GApprox in
theorem GlobalTheory.Poinc.exists_approxAt : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W i), IsE8 W → ThetaInt F W i → 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ →
    ∃ d : ℕ, 1 ≤ d ∧ ApproxAt X₁ φ d := by
  intro g n F W Z i X₁ hE hT hg φ hpol
  obtain ⟨d₀, hd₀, hsup⟩ := exists_hasSupports_int g φ hpol
  have hW : 0 < W 0 0 := by
    have := hE.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at this
    have h2 : (0 : ℤ) < W 0 0 + W 0 0 := by exact_mod_cast this
    omega
  have hN : 3 ≤ X₁.S.r * X₁.S.N := by
    have h1 := X₁.big.2.2
    have h2 : 1 ≤ X₁.S.N ^ X₁.S.g * X₁.S.g.factorial :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by have := X₁.S.N_ge; omega))
        (Nat.factorial_ne_zero _))
    omega
  refine ⟨(W 0 0).toNat * d₀, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  intro p _ z₁ c₀ e
  have hcl : IsClosed ({z₁} : Set X₁.M.Z) := c₀.cen ▸ isClosed_singleton_cPt c₀.y
  obtain ⟨Φ, hM, hL, hR⟩ := GlobalTheory.T.exists_classicalTrait_system_at_closedPoint g n F W Z i hE hT X₁ p z₁ hcl
  have hF := GlobalTheory.T.classical_traits_fourier_terms_all_levels g n F W Z i X₁ p z₁ Φ hE.1 hR
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  have hA := approx_of_fpre ℤ id bddAct_int_and_cm.1 g φ hpol d₀ hsup 7 W hE.1 (X₁.S.r * X₁.S.N) p hN _ Φ hL hF
  obtain ⟨y₀, hev₀, e₀, he₀⟩ := hM c₀
  obtain ⟨f, hf1, hf2⟩ := hA y₀ e
  have key : ∀ (y : Φ.Y) (c : CTrait X₁ p z₁) (e' : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X),
      (∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e' a) (e' b)) →
      Φ.sc y * (((W 0 0).toNat * d₀ : ℕ) * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y)) = c.sc * (((W 0 0).toNat * d₀ : ℕ) * φ.evalZ c.T.β) := by
    intro y c e' h
    have := sc_evalZ_eq hpol Φ y c e' h
    calc Φ.sc y * (((W 0 0).toNat * d₀ : ℕ) * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y))
        = ((W 0 0).toNat * d₀ : ℕ) * (Φ.sc y * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y)) := by ring
      _ = c.sc * (((W 0 0).toNat * d₀ : ℕ) * φ.evalZ c.T.β) := by rw [this]; ring
  refine ⟨f, ?_, fun c => ?_⟩
  · rw [← hev₀ f, hf1, key y₀ c₀ e₀ he₀]
  · obtain ⟨y, hev, e', he'⟩ := hM c
    rcases hf2 y with h | ⟨h, hh, hle⟩
    · left; rw [← hev f, ← key y c e' he']; exact h
    · right; exact ⟨h, hh, by rw [← hev f, ← hev h]; exact hle⟩

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxPoincareSeriesAtThetaSetupPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_approxPoincareSeries_at_thetaSetup_points : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), IsE8 W → ThetaInt F W i → 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∃ d : ℕ, 1 ≤ d ∧ ApproxAt X₁ φ d := by
  first | exact @GlobalTheory.Poinc.exists_approxAt | exact GlobalTheory.Poinc.exists_approxAt | (intros; apply GlobalTheory.Poinc.exists_approxAt <;> assumption)
end
end
