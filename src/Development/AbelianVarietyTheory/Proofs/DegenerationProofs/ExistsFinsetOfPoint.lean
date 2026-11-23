module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenV
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdjoin

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefField
open TWM TWO CoefBasic

section
variable (R : Type) [CommRing R] [IsDomain R] (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E]
  [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] {X : Scheme.{0}} {L : LB X}

omit [IsDomain R] in
theorem comp_jFK : Spec.map (CommRingCat.ofHom (algebraMap E F)) ≫ jFK (R := R) E = jFK (R := R) F := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

def ιE : TF (R := R) F ⟶ TF (R := R) E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (comp_jFK R E F)))

omit [IsDomain R] in
theorem ι_inj : Function.Injective fun ψ : (TF (R := R) E).left ⟶ X => (ιE R E F).left ≫ ψ := by
  intro a b h
  have : Epi (ιE R E F).left := by
    show Epi (Spec.map (CommRingCat.ofHom (algebraMap E F)))
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap E F))) := inferInstance
    have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap E F))) :=
      ⟨fun u => ⟨IsLocalRing.closedPoint F, Subsingleton.elim _ _⟩⟩
    exact Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (ιE R E F).left).1 h

omit [IsDomain R] in
theorem gs_ι (z : (TF (R := R) F).left) (a : Γ(Spec (CommRingCat.of E), ⊤)) :
    gs (ιE R E F).left z ⊤ a = cst F z (algebraMap E F ((Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom a)) := by
  rw [cst_eq, gs_eq _ z ⊤ trivial]
  exact congrArg ((TF (R := R) F).left.presheaf.germ ⊤ z trivial).hom
    (appTop_specMap (CommRingCat.ofHom (algebraMap E F)) a)


omit [IsDomain R] in
theorem sec_rat (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → ((TF (R := R) E).left ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε))
    (hf : ∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ X) → U), ∏ i, h ((ιE R E F).left ≫ φ i) ^ ε i = 1) :
    ∃ a : E, ∀ z J, Good L z J → sval s (ιE R E F).left z J = cst F z (algebraMap E F a) := by
  obtain ⟨s₀, hs⟩ := exists_sec hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
    refine Eq.trans ?_ ((hf U (Function.extend (fun ψ => (ιE R E F).left ≫ ψ) h 1)).trans (Fintype.prod_empty _).symm)
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(ι_inj R E F).extend_apply]) s
  have le : (⊤ : (TF (R := R) E).left.Opens) ≤
      LB.wchart L (PEmpty.elim : PEmpty → ((TF (R := R) E).left ⟶ X)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of E)).hom.hom
    (((TF (R := R) E).left.presheaf.map (homOfLE le).op).hom (s₀.f PEmpty.elim)), fun z J hJ => ?_⟩
  rw [← hs _ _ z J hJ, sval_of s₀ _ z J PEmpty.elim (fun k => k.elim), ← gs_ι R E F]
  exact (gs_res _ z le trivial _).symm

def HE (L : LB X) (σ : CoefVal.FS R F X)
    (f : ∀ z : (TF (R := R) F).left, (((TF (R := R) F).left ⟶ X) → L.ι) → (TF (R := R) F).left.presheaf.stalk z)
    (x : F) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → ((TF (R := R) E).left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : ((TF (R := R) F).left ⟶ X) → U), ∏ i, h ((ιE R E F).left ≫ φ i) ^ ε i = σ U h) ∧
    ∀ z J, Good L z J → f z J = cst F z x * (val t (ιE R E F).left z J).val

variable {R E F}

theorem HE.mul {σ σ' : CoefVal.FS R F X} {f f'} {x x' : F} (H : HE R E F L σ f x) (H' : HE R E F L σ' f' x') :
    HE R E F L (fun U _ h => σ U h * σ' U h) (fun z J => f z J * f' z J) (x * x') := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht', fun U _ h => ?_,
    fun z J hJ => ?_⟩
  · rw [Fintype.prod_sum_type]
    exact congrArg₂ (· * ·) (hs U h) (hs' U h)
  · rw [val_mul hJ]
    simp only [e z J hJ, e' z J hJ, cst_eq, map_mul, Units.val_mul]
    ring

theorem HE.one : HE R E F L (fun _ _ _ => 1) (fun _ _ => 1) 1 :=
  ⟨PEmpty, inferInstance, _, _, LB.oneGen L (Y := (TF (R := R) E).left),
    fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun U _ h => Fintype.prod_empty _, fun z J _ => by rw [val_one, cst_eq, map_one, Units.val_one, _root_.mul_one]⟩

theorem HE.congr {σ σ' : CoefVal.FS R F X} {f f'} {x : F} (H : HE R E F L σ f x)
    (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) (hf : ∀ z J, Good L z J → f' z J = f z J) :
    HE R E F L σ' f' x := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  exact ⟨K, _, φ, ε, t, ht, fun U _ h => (hs U h).trans (hσ U h), fun z J hJ => (hf z J hJ).trans (e z J hJ)⟩

theorem HE.pow {σ : CoefVal.FS R F X} {f} {x : F} (H : HE R E F L σ f x) (n : ℕ) :
    HE R E F L (fun U _ h => σ U h ^ n) (fun z J => f z J ^ n) (x ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using HE.one
  | succ n ih => simpa only [pow_succ] using ih.mul H

theorem HE.ratio (hL : L.IsLB) {σ σ' : CoefVal.FS R F X} {f f'} {x x' : F} (H : HE R E F L σ f x)
    (H' : HE R E F L σ' f' x') (hσ : ∀ (U : Type) [CommGroup U] h, σ U h = σ' U h) :
    ∃ a : E, ∀ z J, Good L z J → cst F z x' * f z J = cst F z (x * algebraMap E F a) * f' z J := by
  obtain ⟨K, _, φ, ε, t, ht, hs, e⟩ := H
  obtain ⟨K', _, φ', ε', t', ht', hs', e'⟩ := H'
  have hu := mulGen_isGen _ _ _ _ _ _ _ ht (invGen_isGen _ _ _ _ ht')
  obtain ⟨a, hav⟩ := sec_rat R E F hL (Geo.Tor.genSec _ hu) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
    rw [hs, hs', hσ, mul_inv_cancel])
  refine ⟨a, fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_genSec _ hu _ z hJ, val_mul hJ, val_inv] at b
  have c : (val t (ιE R E F).left z J).val = cst F z (algebraMap E F a) * (val t' (ιE R E F).left z J).val := by
    rw [← b, Units.val_mul, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]
  rw [e z J hJ, e' z J hJ, c]
  simp only [cst_eq, map_mul]
  ring

variable {K : Type} [Fintype K] {ε : K → ℤ}

theorem he_gen {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (r₀ : (TF (R := R) E).left ⟶ Y) {r : (TF (R := R) F).left ⟶ Y} (hr : (ιE R E F).left ≫ r₀ = r) :
    HE R E F L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => (val t r z J).val) 1 := by
  subst hr
  exact ⟨K, _, _, ε, LB.pullGen L φ ε t r₀, pullGen_isGen _ _ _ _ ht _, fun U _ h => by simp only [Category.assoc],
    fun z J hJ => by rw [val_pull hJ, cst_eq, map_one, _root_.one_mul]⟩

theorem he_sec (hL : L.IsLB) {Y : Scheme.{0}} {φ : K → (Y ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε))
    (r₀ : (TF (R := R) E).left ⟶ Y) {r : (TF (R := R) F).left ⟶ Y} (hr : (ιE R E F).left ≫ r₀ = r) :
    ∃ a : E, HE R E F L (fun _ _ h => ∏ i, h (r ≫ φ i) ^ ε i) (fun z J => sval s r z J) (algebraMap E F a) := by
  subst hr
  obtain ⟨t, ht⟩ := exists_gen_of_local (V := E) L hL (fun i => r₀ ≫ φ i) ε
  have hi := invGen_isGen _ _ _ _ ht
  obtain ⟨a, hav⟩ := sec_rat R E F hL (pullMulSec s r₀ _ hi) (fun U _ h => by
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel])
  refine ⟨a, K, _, _, ε, t, ht, fun U _ h => by simp only [Category.assoc], fun z J hJ => ?_⟩
  have b := hav z J hJ
  rw [sval_pullMulSec _ _ _ hi _ z hJ, val_inv] at b
  rw [← b, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem exists_he (hL : L.IsLB) {φ : K → ((TF (R := R) F).left ⟶ X)} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen)
    (hφ : ∀ i, ∃ ψ, φ i = (ιE R E F).left ≫ ψ) :
    ∃ x : F, x ≠ 0 ∧ HE R E F L (fun _ _ h => ∏ i, h (φ i) ^ ε i) (fun z J => (val t (𝟙 _) z J).val) x := by
  choose φ₀ h₀ using hφ
  obtain ⟨t₀, ht₀⟩ := exists_gen_of_local (V := E) L hL φ₀ ε
  obtain ⟨c, hc, e⟩ := exists_ratio hL t ht (LB.pullGen L _ _ t₀ (ιE R E F).left) (pullGen_isGen _ _ _ _ ht₀ _)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by rw [h₀])
  refine ⟨c, hc, K, _, φ₀, ε, t₀, ht₀, fun U _ h => by simp only [h₀], fun z J hJ => ?_⟩
  have := e (TF (R := R) F).left (𝟙 (TF (R := R) F).left) z J hJ
  rw [val_pull hJ, Category.id_comp] at this
  exact this

end

theorem exists_adjoin {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]
    (A : Over (Spec (CommRingCat.of R))) [LocallyOfFiniteType A.hom] (b : TF (R := R) F ⟶ A) :
    ∃ (T : Finset F) (b₁ : TF (R := R) (IntermediateField.adjoin (FractionRing R) (T : Set F)) ⟶ A),
      ιE R _ F ≫ b₁ = b := by
  classical
  let a : Spec (CommRingCat.of F) ⟶ A.left := b.left
  obtain ⟨B, i, _, t, ht⟩ : ∃ (B : CommRingCat.{0}) (i : Spec B ⟶ A.left) (_ : IsOpenImmersion i)
      (t : Spec B), i t = a (IsLocalRing.closedPoint F) := by
    obtain ⟨n, t, ht⟩ := A.left.affineCover.exists_eq (a (IsLocalRing.closedPoint F))
    exact ⟨_, A.left.affineCover.f n, A.left.affineCover.map_prop n, t, ht⟩
  have hr : Set.range a ⊆ Set.range i := by
    rintro _ ⟨u, rfl⟩
    exact ⟨t, ht.trans (congrArg a (Subsingleton.elim _ _))⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i a hr)
  have hφa : Spec.map φ ≫ i = a := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (show Spec B ⟶ Spec (CommRingCat.of R) from i ≫ A.hom)
  have h₂ : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₂
  have hc : ψ ≫ φ = CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) F) := by
    rw [← Spec.map_inj, Spec.map_comp, hψ, ← Category.assoc, hφa, Spec.map_comp]
    exact Over.w b
  let : Algebra R B := ψ.hom.toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Subalgebra R B).FG := (show Algebra.FiniteType R B from h₂).out
  let K := IntermediateField.adjoin (FractionRing R) ((s.image φ.hom : Finset F) : Set F)
  have hm : ∀ x : B, φ.hom x ∈ K := fun x => by
    have hx : x ∈ Algebra.adjoin R (s : Set B) := by rw [hs]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap r =>
      have e : φ.hom (algebraMap R B r) = algebraMap (FractionRing R) F (algebraMap R _ r) := congr($hc r)
      rw [e]; exact K.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have e : (ιE R K F).left ≫ Spec.map (CommRingCat.ofHom (φ.hom.codRestrict K hm)) ≫ i = b.left := by
    refine Eq.trans ?_ hφa
    show Spec.map _ ≫ _ = _
    rw [← Spec.map_comp_assoc]
    rfl
  refine ⟨s.image φ.hom, Over.homMk (Spec.map (CommRingCat.ofHom (φ.hom.codRestrict K hm)) ≫ i) ?_,
    Over.OverMorphism.ext e⟩
  apply ι_inj R K F
  show (ιE R K F).left ≫ _ ≫ _ = (ιE R K F).left ≫ _
  rw [← Category.assoc, e, Over.w, Over.w]

end GlobalTheory.UT.CoefField
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFinsetOfPoint

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.CoefField
open TWM TWO CoefBasic

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {E F : Type} [Field E] [Field F]
  [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F]

theorem he_cub (x x' y : TF (R := R) E ⟶ D.P.A) :
    HE R E F D.P.L (fun _ _ h => h (ιE R E F ≫ x * ιE R E F ≫ x' * ιE R E F ≫ y).left *
      (h (ιE R E F ≫ x * ιE R E F ≫ x').left)⁻¹ * (h (ιE R E F ≫ x * ιE R E F ≫ y).left)⁻¹ *
      (h (ιE R E F ≫ x' * ιE R E F ≫ y).left)⁻¹ * h (ιE R E F ≫ x).left * h (ιE R E F ≫ x').left *
      h (ιE R E F ≫ y).left * (h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹)
      (fun z J => (th D z J (ιE R E F ≫ x) (ιE R E F ≫ x') (ιE R E F ≫ y)).val) 1 :=
  (he_gen (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.isGen
    (lift x (lift x' y)).left (r := (lift (ιE R E F ≫ x) (lift (ιE R E F ≫ x') (ιE R E F ≫ y))).left)
    (by rw [← Over.comp_left, comp_lift, comp_lift])).congr (fun U _ h => prod_cub _ _ _ h)
    (fun _ _ _ => rfl)

theorem exists_gt (g : GtPtF D F) (b₁ : TF (R := R) E ⟶ D.P.A) (hb : ιE R E F ≫ b₁ = g.b) :
    ∃ (x : D.X → F) (S : Finset F), (∀ χ, HE R E F D.P.L (fun _ _ h => ∏ i, h (DegPre.gtφ D F g.b χ i) ^ DegPre.gtε i)
      (fun z J => (val (g.s χ) (𝟙 _) z J).val) (x χ)) ∧
      ∀ K : Subfield F, (∀ a, algebraMap E F a ∈ K) → (S : Set F) ⊆ K → ∀ χ, x χ ∈ K := by
  classical
  have hL := D.P.isLB
  choose x hx0 hx using fun χ => exists_he (R := R) (E := E) (F := F) hL (g.isGen χ) (fun i => by
    fin_cases i
    · refine ⟨(cP D _ χ * b₁).left, ?_⟩
      show (cP D _ χ * g.b).left = _
      rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hb]
    · refine ⟨(cP D _ χ).left, ?_⟩
      show (cP D _ χ).left = _
      rw [← Over.comp_left, comp_cP]
    · refine ⟨b₁.left, ?_⟩
      show g.b.left = _
      rw [← Over.comp_left, hb]
    · refine ⟨(1 : TF (R := R) E ⟶ D.P.A).left, ?_⟩
      show (1 : TF (R := R) F ⟶ D.P.A).left = _
      rw [← Over.comp_left, MonObj.comp_one])
  have hadd : ∀ χ χ', ∃ a : E, x (χ + χ') = x χ * x χ' * algebraMap E F a := fun χ χ' => by
    have C := he_cub (F := F) (cP D _ χ) (cP D _ χ') b₁
    rw [comp_cP, comp_cP, hb] at C
    obtain ⟨a, ha⟩ := ((hx χ).mul (hx χ')).ratio hL ((hx (χ + χ')).mul C) (fun U _ h => by
      rw [prod_gt, prod_gt, prod_gt, cPoint_add]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    obtain ⟨z⟩ := exists_pt (R := R) (F := F)
    obtain ⟨J, hJ⟩ := exists_good' hL z
    have e := gt_mul (𝟙 (TF (R := R) F)) hJ g χ χ'
    rw [Category.id_comp, Over.id_left] at e
    have e' := ha z J hJ
    rw [← Units.val_mul, ← Units.val_mul, e, Units.mul_left_inj, _root_.mul_one, cst_eq, cst_eq] at e'
    exact ⟨a, cstH_inj z e'⟩
  obtain ⟨T, hT⟩ : (⊤ : Submodule ℤ D.X).FG := Module.Finite.fg_top
  refine ⟨x, T.image x, hx, fun K hK hS χ => ?_⟩
  have h0 : x 0 ∈ K := by
    obtain ⟨a, ha⟩ := hadd 0 0
    rw [add_zero, _root_.mul_assoc, left_eq_mul₀ (hx0 0)] at ha
    rw [eq_inv_of_mul_eq_one_left ha]
    exact inv_mem (hK a)
  let G : AddSubgroup D.X :=
    { carrier := {χ | x χ ∈ K}
      zero_mem' := h0
      add_mem' := fun {χ χ'} h h' => by
        obtain ⟨a, ha⟩ := hadd χ χ'
        show x _ ∈ K
        rw [ha]; exact mul_mem (mul_mem h h') (hK a)
      neg_mem' := fun {χ} h => by
        obtain ⟨a, ha⟩ := hadd χ (-χ)
        rw [add_neg_cancel] at ha
        have ha0 : algebraMap E F a ≠ 0 := fun h0 => hx0 0 (by rw [ha, h0, MulZeroClass.mul_zero])
        have e : x (-χ) = x 0 * (x χ)⁻¹ * (algebraMap E F a)⁻¹ := by
          have := hx0 χ
          rw [ha]; field_simp
        show x _ ∈ K
        rw [e]; exact mul_mem (mul_mem h0 (inv_mem h)) (inv_mem (hK a)) }
  have hle : Submodule.span ℤ (T : Set D.X) ≤ G.toIntSubmodule :=
    Submodule.span_le.2 fun t ht => hS (by simpa using ⟨t, ht, rfl⟩)
  exact hle (hT ▸ Submodule.mem_top)

theorem fe_at (hG : GlobalFnsSt) {k : ℕ} (s : Fam D F k) (b : TF (R := R) F ⟶ D.P.A) (b₁ : TF (R := R) E ⟶ D.P.A)
    (hb : ιE R E F ≫ b₁ = b) (α mu : D.X) :
    ∃ f, HE R E F D.P.L (fun _ _ h => (h b.left ^ ((k : ℤ) - 1) * h (cP D _ (α + k • mu) * b).left *
        (h (cP D _ (α + k • mu)).left)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left) *
        (h (b * cP D _ mu).left ^ ((k : ℤ) - 1) * h (cP D _ α * (b * cP D _ mu)).left *
        (h (cP D _ α).left)⁻¹ * h (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹) f 1 ∧
      ∀ z J, Good D.P.L z J → sval (s.s (α + k • mu)) (lift (𝟙 (TF (R := R) F)) b).left z J =
        sval (s.s α) (lift (𝟙 (TF (R := R) F)) (b * cP D _ mu)).left z J * f z J := by
  have hL := D.P.isLB
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D) (F := F) hG k mu α
  obtain ⟨⟨u', hu', hc'⟩, hv'⟩ := gen_fe (D := D) (F := E) hG k mu α
  let ρ' : TF (R := R) F ⟶ DegPre.BF D E := lift (ιE R E F) b
  have hρ : (ιE R E F).left ≫ (lift (𝟙 (TF (R := R) E)) b₁).left = ρ'.left := by
    rw [← Over.comp_left, comp_lift, Category.comp_id, hb]
  have p₁ : ρ' ≫ DegPre.prB D E = b := lift_snd _ _
  have p₂ : (ρ' ≫ DegPre.trF D E mu) ≫ DegPre.prB D E = b * cP D _ mu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, p₁, comp_cP, comp_cP]
  refine ⟨fun z J => (val u' ρ'.left z J).val, (he_gen hu' _ hρ).congr (fun U _ h => ?_) (fun _ _ _ => rfl),
    fun z J hJ => ?_⟩
  · have q₁ := prod_fam D E ρ' (α + k • mu) k h
    have q₂ := prod_fam D E (ρ' ≫ DegPre.trF D E mu) α k h
    rw [p₁] at q₁
    rw [p₂] at q₂
    rw [← q₁, ← prod_neg _ _ q₂, Fintype.prod_sum_type]
    rfl
  · have e := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (s.fe mu α u hu hc) _ (lift (𝟙 (TF (R := R) F)) b).left z J hJ
    have t : lift (𝟙 (TF (R := R) F)) b ≫ DegPre.trF D F mu = lift (𝟙 (TF (R := R) F)) (b * cP D _ mu) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, trF_eq, tr_fst, lift_fst, lift_fst]
      · rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, lift_snd, lift_snd, comp_cP, comp_cP]
    rw [← Over.comp_left, t] at e
    refine e.trans (congrArg₂ (· * ·) rfl (congrArg Units.val ?_))
    rw [hv u hu hc _ (lift (𝟙 (TF (R := R) F)) b) z J hJ, hv' u' hu' hc' _ ρ' z J hJ, val_famMult _ hJ,
      val_famMult _ hJ, uVal, uVal, p₁, lift_snd, lift_fst, lift_fst, comp_cP, comp_cP, comp_cP, comp_cP]
    have j : (ιE R E F).left ≫ jFK (R := R) E = Over.Hom.left (𝟙 (TF (R := R) F)) ≫ jFK (R := R) F :=
      (comp_jFK R E F).trans (Category.id_comp _).symm
    rw [j]

theorem exists_finset_of_point (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (s : Fam D F k) (g : GtPtF D F)
    {w : Frm D F k g.b} (hw : w.IsGen) (b₁ : TF (R := R) E ⟶ D.P.A) (hb : ιE R E F ≫ b₁ = g.b)
    (hs : ∀ α, ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (σF i)
        (D.famφB α) (DegPre.famε k) (σ i) (DegPre.prB D F).left 1) ∧
      ∀ j, (s.s α).f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) :
    ∃ S : Finset F, ∀ K : Subfield F, (∀ a, algebraMap E F a ∈ K) → (S : Set F) ⊆ K → ∀ χ, coef s g w χ ∈ K := by
  classical
  have hL := D.P.isLB
  obtain ⟨x, S, hx, hS⟩ := exists_gt g b₁ hb
  obtain ⟨ω, -, hω⟩ := exists_he (R := R) (E := E) (F := F) hL hw (fun i => by
    fin_cases i
    · refine ⟨(1 : TF (R := R) E ⟶ D.P.A).left, ?_⟩
      show (1 : TF (R := R) F ⟶ D.P.A).left = _
      rw [← Over.comp_left, MonObj.comp_one]
    · refine ⟨b₁.left, ?_⟩
      show g.b.left = _
      rw [← Over.comp_left, hb])
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.X k hk
  choose n a σ σF hσ hsum using hs
  have Rg := (he_gen (R := R) (E := E) (F := F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1)
    D.rig_gen (TF (R := R) E).hom (Over.w (ιE R E F))).pow k
  refine ⟨insert ω (S ∪ Finset.univ.biUnion fun i => Finset.univ.image (a (e i))), fun K hK hSK χ => ?_⟩
  obtain ⟨i₀, ⟨mu, rfl⟩, -⟩ := he χ
  set α := e i₀ with hα
  obtain ⟨f, hf, hfe⟩ := fe_at (E := E) hG s g.b b₁ hb α mu
  have key : ∀ i, ∃ c : F, c ∈ K ∧ ∀ z J, Good D.P.L z J →
      sval (σ α i) (g.b * cP D _ mu).left z J * f z J * (val (g.s (α + k • mu)) (𝟙 _) z J).val * (val w (𝟙 _) z J).val =
        cst F z c * (rigV D (TF (R := R) F).hom z J).val ^ k := fun i => by
    obtain ⟨y, A⟩ := he_sec (R := R) (E := E) (F := F) hL (σ α i) (b₁ * cP D _ mu).left (r := (g.b * cP D _ mu).left)
      (by rw [← Over.comp_left, MonObj.comp_mul, comp_cP, hb])
    obtain ⟨c, hc⟩ := (((A.mul hf).mul (hx (α + k • mu))).mul hω).ratio hL Rg (fun U _ h => by
      have e₀ : (TF (R := R) F).hom ≫ eSec D.P.A = (1 : TF (R := R) F ⟶ D.P.A).left := rfl
      have e₁ : SectionScalarValuation.cQ D (TF (R := R) F) α = cP D _ α := rfl
      rw [SectionScalarValuation.prod_famB, prod_gt, prod_line, Fintype.prod_unique, e₀, e₁, mul_comm _ (cP D _ α)]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    refine ⟨_, mul_mem (mul_mem (mul_mem (mul_mem (hK y) (one_mem K))
      (hS K hK (fun t ht => hSK (by simp [show t ∈ S from ht])) (α + k • mu))) (show ω ∈ K from hSK (by simp))) (hK c),
      fun z J hJ => ?_⟩
    have := hc z J hJ
    rw [one_pow, cst_eq, map_one, _root_.one_mul] at this
    exact this
  choose c hcK hc using key
  have E₀ : coef s g w (α + k • mu) = ∑ i, a α i * c i := coef_eq fun z J hJ => by

    rw [hfe z J hJ, SectionScalarValuation.sval_lin (fun i => gF D F (a α i)) (σF α) (fun j => hsum α j) _ z hJ, cst_eq, map_sum,
    Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have b : gs (lift (𝟙 (TF (R := R) F)) (g.b * cP D _ mu)).left z ⊤ (gF D F (a α i)) = cst F z (a α i) := by
      refine (gs_pull _ (fst (TF (R := R) F) D.P.A).left z ⊤ trivial _).trans ?_
      rw [← Over.comp_left, lift_fst]; rfl
    have e₂ := SectionScalarValuation.secScal_sval (hσ α i) (lift (𝟙 (TF (R := R) F)) (g.b * cP D _ mu)).left z hJ
    rw [← Over.comp_left, lift_snd] at e₂
    rw [b, map_mul, ← cst_eq, ← cst_eq, _root_.mul_assoc, ← hc i z J hJ, ← e₂]
    ring
  rw [E₀]
  exact sum_mem fun i _ => mul_mem (hSK (by
    simp only [Finset.coe_insert, Finset.coe_union, Set.mem_insert_iff, Set.mem_union, Finset.mem_coe,
      Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨i₀, i, rfl⟩))) (hcK i)

theorem exists_finset (hG : GlobalFnsSt) {k : ℕ} (hk : 1 ≤ k) (s : Fam D F k) (g : GtPtF D F)
    {w : Frm D F k g.b} (hw : w.IsGen)
    (hs : ∀ α, ∃ (n : ℕ) (a : Fin n → F) (σ : Fin n → D.SecB k α)
      (σF : Fin n → LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε k))),
      (∀ i, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (σF i)
        (D.famφB α) (DegPre.famε k) (σ i) (DegPre.prB D F).left 1) ∧
      ∀ j, (s.s α).f j = ∑ i, DegPre.constBF D F (a i) _ * (σF i).f j) :
    ∃ S : Finset F, ∀ K : Subfield F, (∀ a, algebraMap (FractionRing R) F a ∈ K) → (S : Set F) ⊆ K →
      ∀ χ, coef s g w χ ∈ K := by
  classical
  have := D.P.isAb.proper
  obtain ⟨T, b₁, hb⟩ := exists_adjoin D.P.A g.b
  obtain ⟨S, hS⟩ := exists_finset_of_point hG hk s g hw b₁ hb hs
  refine ⟨S ∪ T, fun K hK hST => hS K (fun a => ?_) fun t ht => hST (by simp [show t ∈ S from ht])⟩
  have hle : IntermediateField.adjoin (FractionRing R) (T : Set F) ≤ K.toIntermediateField hK :=
    IntermediateField.adjoin_le_iff.2 fun t ht => hST (by simp [show t ∈ T from ht])
  exact hle a.2

end GlobalTheory.UT.CoefField
end
end
end
