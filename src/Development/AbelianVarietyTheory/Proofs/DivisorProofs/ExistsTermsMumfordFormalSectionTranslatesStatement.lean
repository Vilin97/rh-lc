module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedGeneratorOfFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarsInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFactorExistsUniqueConstMulIntegralGeneratStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValPowGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecRelationDefect
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordTermTranslateNormalisedGenerator

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.MumTerm

variable {X Y Z : Scheme.{0}}

theorem scal_spec {A B : Type} [CommRing A] [CommRing B] (q : Y ⟶ Sp B) (φ : A →+* B) (r : A) :
    scal q (φ r) = scal (q ≫ Spec.map (CommRingCat.ofHom φ)) r := by
  have e := congrArg (fun h => h.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [e]

theorem gs_scal {A : Type} [CommRing A] (p : Z ⟶ Y) (q : Y ⟶ Sp A) (z : Z) (r : A) :
    gs p z ⊤ (scal q r) = gs (p ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom r) :=
  gs_pull p q z ⊤ trivial _

theorem exists_smul {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (a : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) : ∃ t : LB.Sec (LB.LinComb L φ ε),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J → sval t r z J = gs r z ⊤ a * sval s r z J := by
  refine ⟨⟨fun i => (Y.presheaf.map (homOfLE le_top).op).hom a * s.f i, fun i j => ?_⟩, fun Z r z J hJ => ?_⟩
  · rw [map_mul, map_mul, s.compat i j, mul_left_comm]
    congr 2
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · have hm := hJ.mem φ r
    exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm a))

theorem exists_term : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) (s₀ : SecT D.toPre a N (-1) 0) (ν : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1)))), u₀.IsGen → ∀ ρ : R, (∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) ρ)) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val) → ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧ ∀ e : ℕ, ρ ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
  intro R _ _ _ D a h h' N s₀ ν u₀ hu₀ ρ H
  obtain ⟨p, hp⟩ := exists_sec D.toPre.P.isLB (φ' := tφ D.toPre a (shift h h' N (-1) ν)) (ε' := tε N (-1))
    (fun U _ g => by
      simp only [Fintype.prod_sum_type, dε, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
      rw [mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec s₀ (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left u₀ hu₀)
  obtain ⟨t, ht⟩ := exists_smul (scal D.toPre.P.A.hom ρ) p
  refine ⟨t, fun u hu Z x z J hJ => ?_, fun e he Z x z J hJ => ?_⟩
  · have e₁ : (DegPre.prB D.toPre (FractionRing R)).left ≫ (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left =
        (DegPre.trF D.toPre (FractionRing R) ν).left ≫ (DegPre.prB D.toPre (FractionRing R)).left := by
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      simp only [DegPre.trF, padd, lift_snd]
      rw [← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
    have e₂ : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom =
        ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left :
          (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) ≫ jK R := by
      have j : jFK (R := R) (FractionRing R) = 𝟙 _ := by
        simp [jFK]
      rw [Over.w]
      refine (Over.w (fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R))).symm.trans ?_
      congr 1
      show jFK (R := R) (FractionRing R) ≫ jK R = jK R
      rw [j, Category.id_comp]
    rw [ht _ _ z J hJ, hp _ _ z J hJ, sval_pullMulSec _ _ _ _ _ z hJ, H u hu Z x z J hJ, Category.assoc, e₁,
      scal_spec, gs_scal, gs_scal, Category.assoc, e₂, mul_left_comm]
  · rw [ht _ _ z J hJ, gs_scal, Category.assoc, pullback.condition, ← gs_scal, ← scal_spec,
      Ideal.Quotient.eq_zero_iff_mem.2 he]
    have : scal (pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (0 : R ⧸ maximalIdeal R ^ (e + 1)) = 0 := by
      simp only [scal, map_zero]
    exact (congrArg (· * _) ((congrArg (gs x z ⊤) this).trans (DVR.gs_zero x z ⊤ trivial))).trans (zero_mul _)

end GlobalTheory.MumTerm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordTermTranslateNormalisedGeneratorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_mumfordTerm_translate_normalisedGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) (s₀ : SecT D.toPre a N (-1) 0) (ν : D.toPre.X) (u₀ : LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (tφ D.toPre a (shift h h' N (-1) ν)) (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c ν)).left ≫ tφ D.toPre a 0 k)) (dε N (-1)))), u₀.IsGen → ∀ ρ : R, (∀ u, IsFac D.toPre a h N (-1) ν 0 (shift h h' N (-1) ν) u → ∀ (Z : Scheme.{0}) (x : Z ⟶ (DegPre.BF D.toPre (FractionRing R)).left) (z : Z) (J), Good D.toPre.P.L z J → (val u x z J).val = gs x z ⊤ (scal ((fst _ _ : DegPre.BF D.toPre (FractionRing R) ⟶ TF (R := R) (FractionRing R)).left : (DegPre.BF D.toPre (FractionRing R)).left ⟶ Sp (FractionRing R)) (algebraMap R (FractionRing R) ρ)) * (val u₀ (x ≫ (DegPre.prB D.toPre (FractionRing R)).left) z J).val) → ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧ ∀ e : ℕ, ρ ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
  first | exact @GlobalTheory.MumTerm.exists_term | exact GlobalTheory.MumTerm.exists_term | (intros; apply GlobalTheory.MumTerm.exists_term <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSectionRelatedAtZeroShift

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFac

theorem formEq_empty_dε {X Y : Scheme.{0}} (φ φ' : Fin 5 → (Y ⟶ X)) (e : φ' = φ) (n j : ℤ) :
    FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (Sum.elim φ φ') (dε n j) := by
  subst e
  intro U _ h
  simp only [dε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib,
    mul_inv_cancel, Finset.univ_eq_empty, Finset.prod_empty]

theorem val_tau_psi_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult)
    (z : (TF (R := R) (FractionRing R)).left) (J) (hJ : Good D.P.L z J) :
    val (D.tau 0 0) (jFK (R := R) (FractionRing R)) z J = 1 ∧
      val (D.psi 0) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J = 1 := by
  have C : IsCub (DVR.th D (T := TF (R := R) (FractionRing R)) z J) := isCub_cubV D.cub hJ
  have z0 : (0 : D.X) + 0 = 0 := add_zero 0
  have hτ := DVR.tau_mul (𝟙 (TF (R := R) (FractionRing R))) hJ hB 0 0 0
  have hψ := DVR.UUA.psi_add (𝟙 (TF (R := R) (FractionRing R))) hJ (0 : D.X) 0
  have hpt : ∀ a b c : D.X, a = b → ∀ (r : (TF (R := R) (FractionRing R)).left ⟶ _),
      val (D.tau a c) r z J = val (D.tau b c) r z J := by rintro a b c rfl r; rfl
  have hpp : ∀ a b : D.X, a = b → ∀ (r : (TF (R := R) (FractionRing R)).left ⟶ _),
      val (D.psi a) r z J = val (D.psi b) r z J := by rintro a b rfl r; rfl
  rw [hpt _ _ _ z0, cPoint_zero, C.face] at hτ
  have t00 := (mul_left_cancel hτ).symm
  rw [hpp _ _ z0, t00, _root_.one_mul] at hψ
  rw [Over.id_left, Category.id_comp] at t00 hψ
  refine ⟨t00, mul_left_cancel (a := val (D.psi 0) (jFK (R := R) (FractionRing R)) z J) ?_⟩
  rw [_root_.mul_one, ← _root_.mul_assoc]
  exact hψ.symm

theorem trel_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (s₀ : SecT D.toPre a N (-1) 0) (s' : SecT D.toPre a N (-1) (shift h h' N (-1) 0)), (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval s' x z J = sval s₀ x z J) → TRel h 0 s₀ s' := by
  intro R _ _ _ hR D a a' h h' hE N _ s₀
  have hs : shift h h' N (-1) 0 = 0 := by simp [shift]
  generalize shift h h' N (-1) 0 = β' at hs
  subst hs
  intro s' hv u hu Z x z J hJ
  have hL := D.toPre.P.isLB
  have htr : (DegPre.trF D.toPre (FractionRing R) 0).left = 𝟙 _ := by rw [DVR.UUA.trF_zero, Over.id_left]
  have hc0 : D.toPre.c 0 = 1 := by
    have h := D.toPre.c_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hp : padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c 0) = 𝟙 _ := by
    rw [hc0, MonObj.comp_one]
    exact _root_.mul_one (𝟙 D.toPre.P.A)
  obtain ⟨u₀, hu₀, -⟩ := exists_gen hL (formEq_empty_dε (tφ D.toPre a 0)
    (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c 0)).left ≫ tφ D.toPre a 0 k)
    (funext fun k => by rw [hp, Over.id_left, Category.id_comp]) (N : ℤ) (-1)) (LB.oneGen D.toPre.P.L)
    (LB.isGen_oneGen D.toPre.P.L)
  obtain ⟨u', hu', hv'⟩ := exists_gen hL (φ' := dφ D.toPre a 0 0 0) (formEq_empty_dε _ _
    (funext fun k => by rw [htr, Category.id_comp]) (N : ℤ) (-1)) (LB.oneGen D.toPre.P.L)
    (LB.isGen_oneGen D.toPre.P.L)
  have hf : IsFac D.toPre a h N (-1) 0 0 0 u' := by
    refine ⟨hu', fun y I hI => ?_⟩
    obtain ⟨t0, p0⟩ := val_tau_psi_zero D.tau_bimult y I hI
    have hh : val (D.toPre.psi (h 0)) (jFK (R := R) (FractionRing R)) y I =
        val (D.toPre.psi 0) (jFK (R := R) (FractionRing R)) y I :=
      congrArg (fun w => val (D.toPre.psi w) (jFK (R := R) (FractionRing R)) y I) (map_zero h)
    rw [hv' _ _ y I hI, val_one, hh, t0, _root_.mul_one, ← zpow_add, ← mul_zpow, p0, one_zpow]
  have key := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hR D a h hE.1 hE.2.2.2.1 N (-1) 0 0 0 u₀ hu₀).2.1 u u' hu hf Z x z J hJ
  rw [key, hv' _ _ z J hJ, val_one, htr, Category.id_comp, Units.val_one, _root_.mul_one]
  exact hv Z _ z J hJ

end GlobalTheory.TwFac
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSectionRelatedAtZeroShiftStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.twisted_section_related_at_zero_shift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (s₀ : SecT D.toPre a N (-1) 0) (s' : SecT D.toPre a N (-1) (shift h h' N (-1) 0)), (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval s' x z J = sval s₀ x z J) → TRel h 0 s₀ s' := by
  first | exact @GlobalTheory.TwFac.trel_zero | exact GlobalTheory.TwFac.trel_zero | (intros; apply GlobalTheory.TwFac.trel_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsMumfordFormalSectionTranslates

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

noncomputable section

namespace GlobalTheory.TwFam

theorem exists_secT_weight_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (N : ℕ) (σ₀ : LB.Sec (LB.LinComb D.P.L (K := Fin 2) ![𝟙 D.P.A.left, a.left] ![(N : ℤ), -1])) (β : D.X), β = 0 → ∃ s : SecT D a N (-1) β, ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J → sval s x z J = sval σ₀ x z J := by
  intro R _ _ D a N σ₀ β hβ
  subst hβ
  have hc : (toUnit D.P.A ≫ D.c 0) = (1 : D.P.A ⟶ D.P.A) := GlobalTheory.CoordToExt.c_zero D D.P.A
  have h1 : (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c 0)).left = 𝟙 D.P.A.left := by
    rw [hc]
    have e : padd D.P.A (𝟙 D.P.A) (1 : D.P.A ⟶ D.P.A) = 𝟙 D.P.A * 1 := rfl
    rw [e, _root_.mul_one]
    rfl
  have h2 : (toUnit D.P.A ≫ D.c 0).left = (toUnit D.P.A ≫ η[D.P.A]).left := by
    rw [hc]
    rfl
  obtain ⟨d, hd⟩ := GlobalTheory.exists_sec_relation_defect D.P.A.left D.P.A.left D.P.A.left D.P.L D.P.isLB _ _ _
    ![𝟙 D.P.A.left, a.left] ![(N : ℤ), -1] (tφ D a 0) (tε N (-1)) _ _ (𝟙 _) σ₀
    (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.secZero _) (LB.oneGen D.P.L) (-1) 0 GlobalTheory.CoordToExt.isGen_one
    (fun U _ f => by
      simp only [tφ, tε, h1, h2, Fin.prod_univ_five, Fin.prod_univ_two, Fintype.prod_sum_type,
        Sum.elim_inl, Sum.elim_inr, Category.id_comp, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]
      simp
      group)
  refine ⟨d, fun Z x z J hJ => ?_⟩
  have k0 : gs x z ⊤ (0 : Γ(D.P.A.left, ⊤)) = 0 := by
    rw [gs_eq x z ⊤ (by simp)]
    first
      | (rw [map_zero, map_zero]; done)
      | simp [map_zero]
  have k1 : gs x z ⊤ (-1 : Γ(D.P.A.left, ⊤)) = -1 := by
    rw [gs_eq x z ⊤ (by simp)]
    first
      | (rw [map_neg, map_one, map_neg, map_one]; done)
      | simp [map_neg, map_one]
  rw [hd Z x z J hJ, val_one, k0, k1, Category.comp_id]
  simp

theorem exists_terms : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ (s₀ : SecT D.toPre a N (-1) 0) (s : ∀ ν, SecT D.toPre a N (-1) (shift h h' N (-1) ν)), (∀ ν, TRel h ν s₀ (s ν)) ∧ Small (maximalIdeal R) s ∧ (∀ ν, ν ≠ 0 → Van (maximalIdeal R) (s ν) 0) ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (s 0) x z J = sval σ₀ x z J) := by
  intro R _ _ _ hB D a a' h h' hE N hN hP σ₀
  obtain ⟨r, g, hg, hr, hfin, hval⟩ := GlobalTheory.MumInt.main R hB D a a' h h' hE N hN hP
  obtain ⟨s₀, hs₀⟩ := exists_secT_weight_zero R D.toPre a N σ₀ 0 rfl
  have h0 : shift h h' (N : ℤ) (-1) (0 : D.toPre.X) = 0 := by simp [shift]
  obtain ⟨z₀, hz₀⟩ := exists_secT_weight_zero R D.toPre a N σ₀ _ h0
  have key : ∀ ν, ∃ t : SecT D.toPre a N (-1) (shift h h' N (-1) ν), TRel h ν s₀ t ∧
      ∀ e : ℕ, r ν ∈ maximalIdeal R ^ (e + 1) → Van (maximalIdeal R) t e := by
    intro ν
    obtain ⟨u₀, hu₀, hfac⟩ := GlobalTheory.T.exists_normalised_twistedGenerator_of_factor R hB D a a' h h' hE N hN r g hg hval ν
    exact GlobalTheory.T.exists_mumfordTerm_translate_normalisedGenerator R D a h h' N s₀ ν u₀ hu₀ (r ν) hfac
  choose t ht using key
  have hz : TRel h 0 s₀ z₀ :=
    GlobalTheory.T.twisted_section_related_at_zero_shift R hB D a a' h h' hE N hN s₀ z₀ fun Z x z J hJ => (hz₀ Z x z J hJ).trans (hs₀ Z x z J hJ).symm
  classical
  let s : ∀ ν, SecT D.toPre a N (-1) (shift h h' N (-1) ν) := fun ν =>
    if hν : ν = 0 then hν.symm ▸ z₀ else t ν
  have hs0 : s 0 = z₀ := dif_pos rfl
  have hsν : ∀ ν, ν ≠ 0 → s ν = t ν := fun ν hν => dif_neg hν
  refine ⟨s₀, s, fun ν => ?_, fun e => ?_, fun ν hν => ?_, fun Z x z J hJ => ?_⟩
  · by_cases hν : ν = 0
    · subst hν
      rw [hs0]
      exact hz
    · rw [hsν ν hν]
      exact (ht ν).1
  · refine ((hfin (e + 1)).insert 0).subset fun ν hν => ?_
    by_cases h0' : ν = 0
    · exact Or.inl h0'
    · refine Or.inr fun hm => hν ?_
      rw [hsν ν h0']
      exact (ht ν).2 e hm
  · rw [hsν ν hν]
    exact (ht ν).2 0 (by rw [zero_add, pow_one]; exact hr ν hν)
  · rw [hs0]
    exact hz₀ Z x z J hJ

end GlobalTheory.TwFam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsMumfordFormalSectionTranslatesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_terms_mumfordFormalSection_translates : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ (s₀ : SecT D.toPre a N (-1) 0) (s : ∀ ν, SecT D.toPre a N (-1) (shift h h' N (-1) ν)), (∀ ν, TRel h ν s₀ (s ν)) ∧ Small (maximalIdeal R) s ∧ (∀ ν, ν ≠ 0 → Van (maximalIdeal R) (s ν) 0) ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval (s 0) x z J = sval σ₀ x z J) := by
  first | exact @GlobalTheory.TwFam.exists_terms | exact GlobalTheory.TwFam.exists_terms | (intros; apply GlobalTheory.TwFam.exists_terms <;> assumption)
end
end
