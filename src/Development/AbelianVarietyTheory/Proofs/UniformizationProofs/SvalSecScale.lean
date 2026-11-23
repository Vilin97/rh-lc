module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
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
import Mathlib.Tactic.TypeStar
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenT
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecRelationDefect
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfThickeningsOfSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecRelationDescends
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuesNatural
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdicSumRel

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

set_option autoImplicit false

namespace GlobalTheory.UU

theorem finsum_rel {A : Type*} [CommRing A] {Ix Ix' : Type*} (σ : Ix ≃ Ix') (f : Ix → A) (g : Ix' → A)
    (a b v : A) (s : Finset Ix) (s' : Finset Ix') (hf : ∀ i ∉ s, f i = 0) (hg : ∀ i ∉ s', g i = 0)
    (h : ∀ i, a * g (σ i) = b * (f i * v)) :
    a * ∑ i ∈ s', g i = b * ((∑ i ∈ s, f i) * v) := by
  classical
  have h1 : ∑ i ∈ s, f i = ∑ i ∈ s ∪ s'.map σ.symm.toEmbedding, f i :=
    Finset.sum_subset Finset.subset_union_left (fun i _ hi => hf i hi)
  have h2 : ∑ i ∈ s', g i = ∑ i ∈ s'.map σ.symm.toEmbedding, g (σ i) := by
    rw [Finset.sum_map]; simp
  have h3 : ∑ i ∈ s'.map σ.symm.toEmbedding, g (σ i) = ∑ i ∈ s ∪ s'.map σ.symm.toEmbedding, g (σ i) :=
    Finset.sum_subset Finset.subset_union_right (fun i _ hi => hg _ (fun hm => hi (by
      rw [Finset.mem_map]; exact ⟨σ i, hm, by simp⟩)))
  rw [h1, h2, h3, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => h i)

theorem adicSum_rel : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y Y₂ : Over (Spec (CommRingCat.of R))) (τ : Y ⟶ Y₂) (X : Scheme.{0}) (L : LB X) (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂.left ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y.left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → (Y.left ⟶ X)) (εu : K'' → ℤ) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ(Y.left, ⊤)) (Ix Ix' : Type) (σ : Ix ≃ Ix') (p : Ix → LB.Sec (LB.LinComb L φ ε)) (p' : Ix' → LB.Sec (LB.LinComb L φ' ε')) (S S'), AdicSum I p S → AdicSum I p' S' → (∀ i (Z : Scheme.{0}) (r : Z ⟶ Y.left) (z : Z) (J), Good L z J → gs r z ⊤ c' * sval (p' (σ i)) r z J = gs r z ⊤ c * (sval (p i) (r ≫ τ.left) z J * (val u r z J).val)) → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Y.left), Lvl I e (r ≫ Y.hom) → ∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval S' r z J = gs r z ⊤ c * (sval S (r ≫ τ.left) z J * (val u r z J).val) := by
  intro R _ I Y Y₂ τ X L K K' K'' _ _ _ φ ε φ' ε' φu εu u c c' Ix Ix' σ p p' S S' hS hS' h e Z r hr z J hJ
  obtain ⟨s, hs⟩ := hS e
  obtain ⟨s', hs'⟩ := hS' e
  have hr2 : Lvl I e ((r ≫ τ.left) ≫ Y₂.hom) := by
    rw [Category.assoc, Over.w τ]; exact hr
  obtain ⟨a1, a2⟩ := hs Z (r ≫ τ.left) hr2 z J hJ
  obtain ⟨b1, b2⟩ := hs' Z r hr z J hJ
  rw [a2, b2]
  exact finsum_rel σ _ _ _ _ _ s s' a1 b1 (fun i => h i Z r z J hJ)

end GlobalTheory.UU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TranslationUnitMul

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem cubN_mul_cubN_add {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
    (k l : ℕ) (b c m y : A) :
    cubN θ k b m y * cubN θ l c m y * θ (b * m ^ k) (c * m ^ l) y = cubN θ (k + l) (b * c) m y * θ b c y := by
  induction k with
  | zero =>
    induction l with
    | zero => simp [cubN]
    | succ l ih =>
      have e := h.coc b (c * m ^ l) m y
      simp only [cubN, Finset.prod_range_succ, Finset.prod_range_zero, Nat.zero_add, pow_zero, _root_.mul_one,
        _root_.one_mul] at ih ⊢
      rw [pow_succ m, ← _root_.mul_assoc c, _root_.mul_assoc b c]
      apply Additive.ofMul.injective
      have ih' := congrArg Additive.ofMul ih
      have e' := congrArg Additive.ofMul e
      simp only [_root_.mul_assoc b c] at ih'
      simp only [ofMul_mul, _root_.mul_assoc b c] at ih' e' ⊢
      linear_combination (norm := abel) ih' - e'
  | succ k ih =>
    have e := h.coc m (b * m ^ k) (c * m ^ l) y
    have p₁ : m * (b * m ^ k) = b * m ^ (k + 1) := by rw [pow_succ, mul_comm m, _root_.mul_assoc]
    have p₂ : b * m ^ k * (c * m ^ l) = b * c * m ^ (k + l) := by rw [pow_add, _root_.mul_mul_mul_comm]
    rw [p₁, p₂, h.s01 m, h.s01 m] at e
    rw [Nat.add_right_comm]
    simp only [cubN, Finset.prod_range_succ] at ih ⊢
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul] at ih' e' ⊢
    linear_combination (norm := abel) ih' + e'

theorem translationUnit_mul :
    ∀ (A U : Type) [CommGroup A] [CommGroup U] (θ : A → A → A → U), IsCub θ → ∀ (k l : ℕ) (b c m y : A), (cubN θ k b m y * (θ b y m)⁻¹) * (cubN θ l c m y * (θ c y m)⁻¹) * θ (b * m ^ k) (c * m ^ l) y * θ b c m = θ b c (y * m) * (cubN θ (k + l) (b * c) m y * (θ (b * c) y m)⁻¹) := by
  intro A U _ _ θ h k l b c m y
  have a := congrArg Additive.ofMul (cubN_mul_cubN_add h k l b c m y)
  have e := congrArg Additive.ofMul (h.compat b c y m)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a e ⊢
  linear_combination (norm := abel) a + e

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConvTermFe

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ConvTermFE
open ReciprocityTheory.ChartRestriction.G.DVR

theorem famFE_val (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (s : Raw D F k) (hs : DegPre.FamFE D F k s) (mu β : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    sval (s (β + k • mu)) r.left z J = sval (s β) (r ≫ DegPre.trF D F mu).left z J *
      (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu β
  rw [← hv u hu hc Z r z J hJ]
  exact (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (hs mu β u hu hc) _ r.left z J hJ

theorem val_powGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (GeneratorPullback.powGen L φ ε t n) r z J = val t r z J ^ n := map_pow _ _ _

theorem units_mul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (k l : ℕ) (mu β ga : D.X)
    (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    (uVal D F k β (cP D _ mu) r z J * val (DegPre.famMult D F k mu β) (r ≫ fst _ _).left z J) *
      (uVal D F l ga (cP D _ mu) r z J * val (DegPre.famMult D F l mu ga) (r ≫ fst _ _).left z J) *
      th D z J (cP D Z (β + k • mu)) (cP D Z (ga + l • mu)) (r ≫ DegPre.prB D F) =
    th D z J (cP D Z β) (cP D Z ga) ((r ≫ DegPre.trF D F mu) ≫ DegPre.prB D F) *
      (uVal D F (k + l) (β + ga) (cP D _ mu) r z J *
        val (DegPre.famMult D F (k + l) mu (β + ga)) (r ≫ fst _ _).left z J) := by
  have C : IsCub (th D (T := Z) z J) := isCub_cubV D.cub hJ
  have hm : r ≫ fst (TF (R := R) F) D.P.A ≫ cP D _ mu = cP D Z mu := by rw [comp_cP, comp_cP]
  have hy : (r ≫ DegPre.trF D F mu) ≫ DegPre.prB D F = (r ≫ DegPre.prB D F) * cP D Z mu := by
    rw [trF_eq, Category.assoc, tr_pr, MonObj.comp_mul, hm]
  have t := tau_mul (r ≫ fst (TF (R := R) F) D.P.A) hJ hB β ga mu
  rw [tau_symm _ hJ (β + ga), tau_symm _ hJ β, tau_symm _ hJ ga] at t
  have key := GlobalTheory.translationUnit_mul _ _ _ C k l (cP D Z β) (cP D Z ga) (cP D Z mu) (r ≫ DegPre.prB D F)
  rw [hy, uVal, uVal, uVal, hm, val_famMult _ hJ, val_famMult _ hJ, val_famMult _ hJ, cPoint_add, cPoint_add, cPoint_add,
    cPoint_nsmul, cPoint_nsmul]
  simp only [val_powGen, pow_add]
  apply Additive.ofMul.injective
  have key' := congrArg Additive.ofMul key
  have t' := congrArg Additive.ofMul t
  simp only [ofMul_mul, ofMul_inv] at key' t' ⊢
  linear_combination (norm := abel) key' - t'

theorem conv_term_fe : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k l : ℕ) (s : Raw D F k) (s' : Raw D F l), DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ∀ (mu α β ga β' ga' : D.X), β + ga = α → β' = β + k • mu → ga' = ga + l • mu → ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F (k + l) α mu) (DegPre.deltaε (k + l))), u.IsGen → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F (k + l) mu α) → ∀ (Z : Over (Spec (CommRingCat.of R))) (r : Z ⟶ DegPre.BF D F) (z : Z.left) (J), Good D.P.L z J → sval (s β') r.left z J * sval (s' ga') r.left z J * (cubV D.cub z J (toUnit Z ≫ D.c β') (toUnit Z ≫ D.c ga') (r ≫ snd _ _)).val = sval (s β) (r ≫ DegPre.trF D F mu).left z J * sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) ((r ≫ DegPre.trF D F mu) ≫ snd _ _)).val * (val u r.left z J).val := by
  rintro hG R _ _ D hB F _ _ k l s s' hs hs' mu _ β ga _ _ rfl rfl rfl u hu hc Z r z J hJ
  have e := congrArg Units.val (units_mul hB k l mu β ga Z r z J hJ)
  rw [famFE_val hG k s hs mu β Z r z J hJ, famFE_val hG l s' hs' mu ga Z r z J hJ,
    (gen_fe hG (k + l) mu (β + ga)).2 u hu hc Z r z J hJ]
  rw [Units.val_mul, Units.val_mul, Units.val_mul (th D z J _ _ _)] at e
  refine Eq.trans ?_ ((congrArg (sval (s β) (r ≫ DegPre.trF D F mu).left z J *
    sval (s' ga) (r ≫ DegPre.trF D F mu).left z J * ·) e).trans (_root_.mul_assoc _ _ _).symm)
  rw [_root_.mul_mul_mul_comm, _root_.mul_assoc]
  rfl

end GlobalTheory.ConvTermFE
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelationOfFiniteLevels

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem relation_of_finite_levels : ∀ (R : Type) [CommRing R] (I : Ideal R) (T B : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [IsNoetherianRing Γ(T.left, ⊤)] [GrpObj B] [Smooth B.hom] [GeometricallyConnected B.hom], (∀ r ∈ I, scal T.hom r ∈ Ideal.jacobson (⊥ : Ideal Γ(T.left, ⊤))) → ∀ (X Y₂ : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' K'' : Type) [Fintype K] [Fintype K'] [Fintype K''] (φ : K → (Y₂ ⟶ X)) (ε : K → ℤ) (φ' : K' → ((T ⊗ B).left ⟶ X)) (ε' : K' → ℤ) (φu : K'' → ((T ⊗ B).left ⟶ X)) (εu : K'' → ℤ) (τ : (T ⊗ B).left ⟶ Y₂) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (u : LB.Gen (LB.LinComb L φu εu)) (c c' : Γ((T ⊗ B).left, ⊤)), u.IsGen → FormEq φ' ε' (Sum.elim (fun k => τ ≫ φ k) φu) (Sum.elim ε εu) → (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (T ⊗ B).hom) → (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ B).left), (∀ (z : Z) (J), Good L z J → gs r z ⊤ c' * sval s' r z J = gs r z ⊤ c * (sval s (r ≫ τ) z J * (val u r z J).val)) := by
  intro R _ I T B _ _ _ _ _ hI X Y₂ L hL K K' K'' _ _ _ φ ε φ' ε' φu εu τ s s' u c c' hu hF h Z r z J hJ
  obtain ⟨d, hd⟩ := exists_sec_relation_defect _ X Y₂ L hL K K' K'' φ ε φ' ε' φu εu τ s s' u c c' hu hF
  have h0 := sec_eq_zero_of_sval_finite_level R I T B hI X L hL K' φ' ε' d (fun e Z r hr z J hJ => by
    rw [hd Z r z J hJ, h e Z r hr z J hJ, sub_self])
  rw [← sub_eq_zero, ← hd Z r z J hJ]
  exact (congrArg (gs r z _) (h0 _)).trans ((gs_eq r z _ (hJ.mem φ' r) _).trans ((congrArg _ (map_zero _)).trans (map_zero _)))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalSecScale

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section

namespace GlobalTheory.ConvFE
open ReciprocityTheory.ChartRestriction.G.DVR

def cst {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = cst (r ≫ p) z c :=
  (gs_pull r p z ⊤ trivial _).trans (gs_eq _ z ⊤ trivial _)

theorem cst_specMap {A R : Type} [CommRing A] [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of R)) (z : Z)
    (f : A →+* R) (c : A) : cst (q ≫ Spec.map (CommRingCat.ofHom f)) z c = cst q z (f c) := by
  have e := congrArg (fun t => t.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [e]

theorem sval_secScale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem pullB_val {T : Over (Spec (CommRingCat.of R))} {φ : TF (R := R) F ⟶ T} {k : ℕ} {f : ∀ α, SecBT D T k α}
    {s : Raw D F k} (h : PullB D F φ k f s) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval (s α) r z J = sval (f α) (r ≫ (φ ▷ D.P.A).left) z J := by
  have a := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (𝟙 (DegPre.BF D F).left) r z J hJ).2.1 (s α)
  have b := (values_natural _ _ _ _ D.P.L (Fin 4) _ _ (φ ▷ D.P.A).left r z J hJ).2.1 (f α)
  have hJ' : Good D.P.L (r z) (fun ψ => J (r ≫ ψ)) := fun ψ => hJ _
  rw [Category.comp_id] at a
  exact a.trans ((congrArg _ (h α _ _ hJ')).trans b.symm)

theorem whisker_trT {T : Over (Spec (CommRingCat.of R))} (φ : TF (R := R) F ⟶ T) (mu : D.X) :
    φ ▷ D.P.A ≫ trT D (toUnit T ≫ D.c mu) = DegPre.trF D F mu ≫ φ ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trT, DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerRight_snd, trT, DegPre.trF, lift_snd, lift_snd]
    refine (MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (fst T D.P.A ≫ cP D T mu)).trans ?_
    rw [whiskerRight_snd, comp_cP, comp_cP]
    rfl

theorem cst_unit {r : R} (hr : r ≠ 0) (z : (DegPre.BF D F).left) : IsUnit (cst (DegPre.BF D F).hom z r) := by
  have e : (DegPre.BF D F).hom = ((fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F) ≫ jK R :=
    (Over.w (fst (TF (R := R) F) D.P.A)).symm.trans (Category.assoc _ _ _).symm
  rw [e]
  refine (congrArg IsUnit ((cst_specMap _ z (algebraMap R (FractionRing R)) r).trans (cst_specMap _ z _ _))).mpr
    (IsUnit.map _ (IsUnit.map _ (Ne.isUnit ?_)))
  exact fun h => hr (IsFractionRing.injective R (FractionRing R) (h.trans (map_zero _).symm))

theorem form_delta {T : Over (Spec (CommRingCat.of R))} (k : ℕ) (α' α : D.X) (b : T ⟶ D.P.A) :
    FormEq (famφT D T α') (DegPre.famε k) (Sum.elim (fun i => (trT D b).left ≫ famφT D T α i) (deltaφT D α' α b))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) := fun U _ h => by
  refine Eq.symm (Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4 ⊕ Fin 4) (U := U) _
    (c := ∏ i, h ((trT D b).left ≫ famφT D T α i) ^ DegPre.famε k i) rfl
    (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _
      (c := ∏ i, h (famφT D T α' i) ^ DegPre.famε k i) rfl (prod_neg _ _ rfl))) ?_)
  exact (mul_comm _ _).trans (inv_mul_cancel_right _ _)

theorem noeth (V W : Type) [CommRing V] [IsNoetherianRing V] [CommRing W] [Algebra V W] [Module.Finite V W] :
    IsNoetherianRing Γ((TA V W).left, ⊤) := by
  haveI : IsNoetherianRing W := isNoetherian_of_tower V inferInstance
  exact isNoetherianRing_of_ringEquiv W (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm

theorem jac (V W : Type) [CommRing V] [IsLocalRing V] [CommRing W] [IsLocalRing W] [Algebra V W]
    [IsLocalHom (algebraMap V W)] (r : V) (hr : r ∈ IsLocalRing.maximalIdeal V) :
    scal (TA V W).hom r ∈ Ideal.jacobson (⊥ : Ideal Γ((TA V W).left, ⊤)) := by
  let E : W ≃+* Γ((TA V W).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).commRingCatIsoToRingEquiv.symm
  have e : scal (TA V W).hom r = E (algebraMap V W r) :=
    (congrArg (fun t => t.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V W)))).symm
  have hw : algebraMap V W r ∈ Ideal.jacobson (⊥ : Ideal W) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact map_nonunit (algebraMap V W) r hr
  rw [e, Ideal.mem_jacobson_bot]
  intro y
  have := (Ideal.mem_jacobson_bot.1 hw (E.symm y)).map E
  simpa using this

theorem sval_twist {W : Type} [CommRing W] [Algebra R W] {k : ℕ} (a : Multiplicative D.X →* Wˣ)
    (f : ∀ α, SecBT D (TA R W) k α) (α : D.X) {Z : Scheme.{0}} (r : Z ⟶ (TA R W ⊗ D.P.A).left) (z : Z) {J}
    (hJ : Good D.P.L z J) : sval (twist a f α) r z J =
      cst (R := W) (r ≫ (fst (TA R W) D.P.A).left) z (a (Multiplicative.ofAdd α)).val * sval (f α) r z J :=
  (sval_secScale _ _ r z hJ).trans (congrArg (· * _) (gs_scal (R := W) _ r z _))

theorem term_val {W : Type} [CommRing W] [Algebra R W] {φ : TF (R := R) F ⟶ TA R W} {k l : ℕ}
    {f : ∀ α, SecBT D (TA R W) k α} {g : ∀ α, SecBT D (TA R W) l α} {s : Raw D F k} {s' : Raw D F l}
    (hf : PullB D F φ k f s) (hg : PullB D F φ l g s') (a a' : Multiplicative D.X →* Wˣ) {β ga α : D.X}
    {p : SecBT D (TA R W) (k + l) α} (hp : IsProdB (twist a f β) (twist a' g ga) p)
    {Z : Over (Spec (CommRingCat.of R))} (r : Z ⟶ DegPre.BF D F) (z : Z.left) {J} (hJ : Good D.P.L z J) :
    sval p (r ≫ φ ▷ D.P.A).left z J =
      cst (R := W) (r ≫ fst _ _ ≫ φ).left z (a (Multiplicative.ofAdd β) * a' (Multiplicative.ofAdd ga)).val *
        (sval (s β) r.left z J * sval (s' ga) r.left z J *
          (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) (r ≫ snd _ _)).val) := by
  have e : (r ≫ φ ▷ D.P.A).left ≫ (fst (TA R W) D.P.A).left = (r ≫ fst _ _ ≫ φ).left := by
    rw [← Over.comp_left, Category.assoc, whiskerRight_fst]
  rw [hp Z _ z J hJ, sval_twist a f β _ z hJ, sval_twist a' g ga _ z hJ, e, pullB_val hf β _ z hJ,
    pullB_val hg ga _ z hJ, Category.assoc, whiskerRight_snd, Units.val_mul, map_mul, Over.comp_left _ _ _ r (φ ▷ D.P.A)]
  ring

theorem term_rel (hG : GlobalFnsSt) (hB : D.TauBimult) {W : Type} [CommRing W] [Algebra R W]
    {φ : TF (R := R) F ⟶ TA R W} {k l : ℕ}
    {f : ∀ α, SecBT D (TA R W) k α} {g : ∀ α, SecBT D (TA R W) l α} {s : Raw D F k} {s' : Raw D F l}
    (hf : PullB D F φ k f s) (hg : PullB D F φ l g s') (hs : DegPre.FamFE D F k s) (hs' : DegPre.FamFE D F l s')
    (a a' : Multiplicative D.X →* Wˣ) (mu α β : D.X)
    (ha : a (Multiplicative.ofAdd (k • mu)) * a' (Multiplicative.ofAdd (l • mu)) = 1)
    {p : SecBT D (TA R W) (k + l) α} (hp : IsProdB (twist a f β) (twist a' g (α - β)) p)
    {p' : SecBT D (TA R W) (k + l) (α + (k + l) • mu)}
    (hp' : IsProdB (twist a f (β + k • mu)) (twist a' g (α + (k + l) • mu - (β + k • mu))) p')
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F (k + l) α mu) (DegPre.deltaε (k + l)))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F (k + l) mu α))
    (z : (DegPre.BF D F).left) {J} (hJ : Good D.P.L z J) :
    sval p' (φ ▷ D.P.A).left z J =
      sval p ((φ ▷ D.P.A).left ≫ (trT D (toUnit _ ≫ D.c mu)).left) z J * (val u (𝟙 _) z J).val := by
  have hγ : α + (k + l) • mu - (β + k • mu) = α - β + l • mu := by rw [add_nsmul]; abel
  have e₁ := term_val hf hg a a' hp' (𝟙 (DegPre.BF D F)) z hJ
  have e₂ := term_val hf hg a a' hp (𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) z hJ
  have e₃ := ConvTermFE.conv_term_fe hG R D hB F k l s s' hs hs' mu α β (α - β) _ _ (add_sub_cancel _ _) rfl hγ u hu hc
    _ (𝟙 (DegPre.BF D F)) z J hJ
  have e₄ : (𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) ≫ fst _ _ ≫ φ = 𝟙 (DegPre.BF D F) ≫ fst _ _ ≫ φ := by
    rw [Category.id_comp, Category.id_comp, DegPre.trF, lift_fst_assoc]
  have e₅ : a (Multiplicative.ofAdd (β + k • mu)) * a' (Multiplicative.ofAdd (α + (k + l) • mu - (β + k • mu))) =
      a (Multiplicative.ofAdd β) * a' (Multiplicative.ofAdd (α - β)) := by
    rw [hγ, ofAdd_add, ofAdd_add, map_mul, map_mul, _root_.mul_mul_mul_comm, ha, _root_.mul_one]
  have e₆ : (φ ▷ D.P.A).left ≫ (trT D (toUnit _ ≫ D.c mu)).left =
      ((𝟙 (DegPre.BF D F) ≫ DegPre.trF D F mu) ≫ φ ▷ D.P.A).left := by
    rw [Category.id_comp, ← whisker_trT, Over.comp_left]
  rw [e₅, e₃, Category.id_comp (φ ▷ D.P.A)] at e₁
  rw [e₄] at e₂
  rw [e₆, e₁, e₂]
  exact (_root_.mul_assoc _ _ _).symm

theorem conv_famFE : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegPre V), D.TauBimult → ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W), Function.Injective φ.left.appTop.hom → ∀ (k l : ℕ) (f : ∀ α, SecBT D (TA V W) k α) (g : ∀ α, SecBT D (TA V W) l α) (h : ∀ α, SecBT D (TA V W) (k + l) α) (s : Raw D F k) (s' : Raw D F l) (s'' : Raw D F (k + l)) (a a' : Multiplicative D.X →* Wˣ), (∀ mu : D.X, a (Multiplicative.ofAdd (k • mu)) * a' (Multiplicative.ofAdd (l • mu)) = 1) → PullB D F φ k f s → PullB D F φ l g s' → PullB D F φ (k + l) h s'' → DegPre.FamFE D F k s → DegPre.FamFE D F l s' → ConvT (IsLocalRing.maximalIdeal V) (twist a f) (twist a' g) h → DegPre.FamFE D F (k + l) s'' := by
  intro hG V _ _ _ hV D hB W _ _ _ hW F _ _ φ hφ k l f g h s s' s'' a a' ha hf hg hh hs hs' hconv mu α u hu hc
  obtain ⟨u₀, r₁, r₂, hu₀, -, hr₂, hrel⟩ := GlobalTheory.UU.IntGen.main hG V D (TA V W) (k + l) α mu
  obtain ⟨p, hp, hS⟩ := hconv α
  obtain ⟨p', hp', hS'⟩ := hconv (α + (k + l) • mu)
  haveI := hV.1
  haveI := hW.1
  haveI := hW.2.2.2.1
  haveI := noeth V W
  haveI := D.P.isAb.smooth
  haveI := D.P.isAb.geomConnected
  haveI : IsAffine (TA V W).left := inferInstanceAs (IsAffine (Spec _))
  haveI : IsAffine (TF (R := V) F).left := inferInstanceAs (IsAffine (Spec _))
  have hcs : ∀ (z : (DegPre.BF D F).left) (c : V),
      gs (φ ▷ D.P.A).left z ⊤ (scal (TA V W ⊗ D.P.A).hom c) = cst (DegPre.BF D F).hom z c := fun z c => by
    rw [gs_scal, Over.w]
  have hu' : ∀ (z : (DegPre.BF D F).left) (J), Good D.P.L z J →
      cst (DegPre.BF D F).hom z r₂ * (val u (𝟙 _) z J).val =
        cst (DegPre.BF D F).hom z r₁ * (val u₀ (φ ▷ D.P.A).left z J).val := fun z J hJ => by
    have := hrel F φ u hu hc _ (𝟙 _) z J hJ
    rwa [gs_scal, gs_scal, Category.id_comp, Category.id_comp] at this
  have H := relation_of_finite_levels V (IsLocalRing.maximalIdeal V) (TA V W) D.P.A (jac V W) _ _ D.P.L D.P.isLB _ _ _
    _ _ _ _ _ _ (trT D (toUnit _ ≫ D.c mu)).left (h α) (h (α + (k + l) • mu)) u₀ (scal (TA V W ⊗ D.P.A).hom r₁)
    (scal (TA V W ⊗ D.P.A).hom r₂) hu₀ (form_delta _ _ _ _)
    (adicSum_rel V (IsLocalRing.maximalIdeal V) _ _ (trT D (toUnit _ ≫ D.c mu)) _ D.P.L _ _ _ _ _ _ _ _ _ u₀ _ _ _ _
      (Equiv.addRight (k • mu)) p p' _ _ hS hS' fun β =>
      sec_relation_descends _ D.P.A (TA V W) (TF (R := V) F) φ hφ _ _ D.P.L D.P.isLB _ _ _ _ _ _ _ _ _ _ (p β)
        (p' (β + k • mu)) u₀ _ _ hu₀ (form_delta _ _ _ _) fun z J hJ => by
          rw [hcs, hcs, term_rel hG hB hf hg hs hs' a a' mu α β (ha mu) (hp β) (hp' _) u hu hc z hJ, mul_left_comm,
            hu' z J hJ, mul_left_comm])
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun z J hJ => ?_
  have e := H _ (φ ▷ D.P.A).left z J hJ
  rw [hcs, hcs, mul_left_comm, ← hu' z J hJ, mul_left_comm, ← Over.comp_left, whisker_trT, Over.comp_left] at e
  rw [pullB_val hh _ _ z hJ, pullB_val hh _ _ z hJ, Category.id_comp, Category.id_comp]
  exact (cst_unit hr₂ z).mul_left_cancel e

end GlobalTheory.ConvFE
end
end
end
