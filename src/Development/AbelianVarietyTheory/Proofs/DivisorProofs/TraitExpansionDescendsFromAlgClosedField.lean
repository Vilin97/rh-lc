module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointFlatOfModificationOfDomain
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatingConstantMemTraitFractionField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.RatConst

open scoped TensorProduct

theorem mem_range_of_tmul_eq {K F O : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup O] [Module K O]
    {t u : O} {c : F} (ht : t ≠ 0) (h : (1 : F) ⊗ₜ[K] t = c ⊗ₜ[K] u) : ∃ x : K, algebraMap K F x = c := by
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_eq_one K ht
  have e := congrArg (fun v => TensorProduct.rid K F (LinearMap.lTensor F l v)) h
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hl, one_smul, Algebra.smul_def] at e
  refine ⟨(l u)⁻¹, ?_⟩
  rw [map_inv₀]
  exact inv_eq_of_mul_eq_one_right (by simpa using e.symm)

theorem gs_spec {A B : CommRingCat.{0}} (h : A ⟶ B) (y : Spec B) (x : A) :
    gs (Spec.map h) y ⊤ ((Scheme.ΓSpecIso A).inv.hom x) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom x)) := by
  have e := congrArg (fun q => q.hom x) (Scheme.ΓSpecIso_inv_naturality h)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e]
  exact ((gs_pull (𝟙 _) (Spec.map h) y ⊤ trivial _).trans (by rw [Category.id_comp])).symm

theorem mem_of_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (y : Spec (Z.presheaf.stalk z)) :
    f (Z.fromSpecStalk z y) ∈ U := by
  have : Z.fromSpecStalk z y ⤳ z := by
    have := Set.mem_range_self (f := Z.fromSpecStalk z) y
    rwa [Scheme.range_fromSpecStalk] at this
  exact (this.map f.continuous).mem_open U.isOpen hz

theorem gs_stalk {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (U : X.Opens) (hz : f z ∈ U) (a : Γ(X, U)) {B : CommRingCat.{0}}
    (h : Z.presheaf.stalk z ⟶ B) (y : Spec B) :
    gs (Spec.map h ≫ Z.fromSpecStalk z ≫ f) y U a = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso B).inv.hom (h.hom (gs f z U a))) := by
  have m := mem_of_stalk f z U hz (Spec.map h y)
  rw [← gs_spec, ← Category.assoc, ← gs_pull _ f y U m, ← gs_pull _ (Z.fromSpecStalk z) y _ m,
    Scheme.fromSpecStalk_app (U := f ⁻¹ᵁ U) hz, gs_eq f z U hz]
  exact gs_res (Spec.map h) y le_top m _

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (c : F), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → (∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0) → ∃ x : FractionRing W, algebraMap (FractionRing W) F x = c := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s c H ⟨Z, p, p', h₁, h₂, z, J, hJ, hne⟩
  let O := Z.presheaf.stalk z
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of F ⟶ O,
      Spec.map ρ = Z.fromSpecStalk z ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left := ⟨Spec.preimage _, Spec.map_preimage _⟩
  letI : Algebra (FractionRing W) O := (ρ.hom.comp (algebraMap (FractionRing W) F)).toAlgebra
  let B := CommRingCat.of (F ⊗[FractionRing W] O)
  let iL : CommRingCat.of F ⟶ B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom
  let iR : O ⟶ B := CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).toRingHom
  have hK : ∀ x : FractionRing W, iR.hom (ρ.hom (algebraMap _ F x)) = iL.hom (algebraMap _ F x) := fun x =>
    ((Algebra.TensorProduct.includeRight (R := FractionRing W) (A := F) (B := O)).commutes x).trans rfl
  let g : Spec B ⟶ Z := Spec.map iR ≫ Z.fromSpecStalk z
  have hg : g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map (ρ ≫ iR) := by
    rw [Spec.map_comp, hρ, Category.assoc]
  have w : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom = Spec.map iL ≫ jFK (R := R) F := by
    have e : (snd (TFK (R := R) F) C.A.A).left ≫ C.A.A.hom = (fst (TFK (R := R) F) C.A.A).left ≫ jFK (R := R) F :=
      (Over.w _).trans (Over.w (fst (TFK (R := R) F) C.A.A)).symm
    have e' : (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.A.A.hom =
        (g ≫ p' ≫ (fst (TFK (R := R) F) C.A.A).left) ≫ jFK (R := R) F := by simp only [Category.assoc, e]
    rw [e', hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    refine CommRingCat.hom_ext (IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_))
    exact (congrArg (fun q => iR.hom (ρ.hom q)) (hF r)).trans ((hK _).trans (congrArg iL.hom (hF r).symm))
  obtain ⟨q, q₁, q₂⟩ : ∃ q : Spec B ⟶ (TFK (R := R) F ⊗ C.A.A).left,
      q ≫ (fst (TFK (R := R) F) C.A.A).left = Spec.map iL ∧
      q ≫ (snd (TFK (R := R) F) C.A.A).left = g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left := by
    let T' : Over (Sp (FractionRing R)) := Over.mk (Spec.map iL ≫ jFK (R := R) F)
    let a : T' ⟶ TFK (R := R) F := Over.homMk (Spec.map iL) rfl
    let b : T' ⟶ C.A.A := Over.homMk (g ≫ p' ≫ (snd (TFK (R := R) F) C.A.A).left) w
    exact ⟨(lift a b).left, congrArg (·.left) (lift_fst a b), congrArg (·.left) (lift_snd a b)⟩
  have k₁ : (g ≫ p) ≫ T.β = q ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
    rw [← Category.assoc q, q₂, Category.assoc, h₁]; simp only [Category.assoc]
  have k₂ : (g ≫ p) ≫ T.G.hom = q ≫ (fst (TFK (R := R) F) C.A.A).left ≫
      spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    rw [← Category.assoc q, q₁, Category.assoc, h₂, ← Category.assoc p', ← Category.assoc g, hg]
    refine (Spec.map_comp _ _).symm.trans (Eq.trans (congrArg Spec.map ?_) (Spec.map_comp _ _))
    exact CommRingCat.hom_ext (RingHom.ext fun r => hK _)
  let u : O := sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J
  let t : O := sval σ p z J
  have key : iR.hom t = iL.hom c * iR.hom u := by
    apply (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨J', hJ', e⟩ := exists_good C.P.L.L C.P.L.isLB y (K := Unit) (fun _ => (g ≫ p) ≫ T.β) (fun _ => J (p ≫ T.β))
      (fun _ _ _ => rfl) (fun _ => mem_of_stalk (p ≫ T.β) z _ (hJ _) (Spec.map iR y))
    have e := e ()
    have := H _ (g ≫ p) q k₁ k₂ y J' hJ'
    rw [sval_of σ _ y J' (fun _ => J (p ≫ T.β)) (fun _ => e),
      sval_of s _ y J' (fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) (fun _ => by
        rw [Category.assoc, ← k₁, Category.assoc p', ← h₁]; exact e), q₁, q₂] at this
    have a₁ := gs_stalk p z _ (hJ.mem (fun _ : Fin 1 => T.β) p) (σ.f fun _ => J (p ≫ T.β)) iR y
    have a₂ := gs_stalk (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z _
      (hJ.mem (fun _ : Fin 1 => C.α) (p' ≫ (snd (TFK (R := R) F) C.A.A).left))
      (s.f fun _ => J ((p' ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α)) iR y
    have a₃ := gs_spec iL y c
    simp only [g, Category.assoc] at this a₁ a₂
    refine a₁.symm.trans (this.trans (Eq.trans (congrArg₂ (· * ·) a₃ a₂) ?_))
    refine (gs_mul _ y ⊤ trivial _ _).symm.trans (congrArg _ ?_)
    simp only [u, sval, Category.assoc]
    exact (map_mul _ _ _).symm
  refine mem_range_of_tmul_eq (O := O) (t := t) (u := u) hne (key.trans ?_)
  exact (Algebra.TensorProduct.tmul_mul_tmul c 1 1 u).trans (by rw [_root_.mul_one, _root_.one_mul])

end GlobalTheory.Mum.RatConst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelatingConstantMemTraitFractionFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.relatingConstant_mem_traitFractionField : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (c : F), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → (∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0) → ∃ x : FractionRing W, algebraMap (FractionRing W) F x = c := by
  first | exact @GlobalTheory.Mum.RatConst.main | exact GlobalTheory.Mum.RatConst.main | (intros; apply GlobalTheory.Mum.RatConst.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValuesIdentityDescendsToFibreProduct

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ValDescent

theorem spMap_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : A →+* B) (g : B →+* C') :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem eq_of_comp_jK {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} {f g : X ⟶ Sp (FractionRing R)}
    (h : f ≫ jK R = g ≫ jK R) : f = g := by
  haveI : Mono (jK R) := Scheme.Spec.map_mono (CommRingCat.ofHom (algebraMap R (FractionRing R))).op
  exact (cancel_mono (jK R)).1 h

theorem desc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (w : W), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s p' z J := by
  intro R _ _ _ _ D C k W _ _ _ T F _ _ _ hF σ s w H Z p p' hpp z J hJ
  have := C.semi.smooth
  haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance
  haveI : Flat C.gp := Modif.flat_gp R C.toModif
  haveI : Flat C.α := MorphismProperty.of_isPullback (P := @Flat) C.α_cart.1.flip inferInstance
  haveI : Flat (pullback.fst T.β C.α) :=
    MorphismProperty.of_isPullback (P := @Flat) (IsPullback.of_hasPullback T.β C.α).flip inferInstance
  set q₁ : pullback T.β C.α ⟶ T.G.left := pullback.fst T.β C.α with hq₁
  set q₂ : pullback T.β C.α ⟶ C.A.A.left := pullback.snd T.β C.α with hq₂
  have hq : q₁ ≫ T.β = q₂ ≫ C.α := pullback.condition
  set ρ : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hρ
  have hρi : Function.Injective ρ := (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  set d : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ pullback T.β C.α := pullback.fst _ _ with hd
  set t : pullback (q₁ ≫ T.G.hom) (spMap ρ) ⟶ Sp F := pullback.snd _ _ with ht
  have hdt : d ≫ q₁ ≫ T.G.hom = t ≫ spMap ρ := pullback.condition
  have hinj : ∀ V, Function.Injective (d.app V) := by
    intro V
    have : IsDominant (spMap ρ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 hρi).le.trans bot_le)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant (spMap ρ)
    have : IsSchemeTheoreticallyDominant d :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip
    have : QuasiCompact d := MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback (q₁ ≫ T.G.hom) (spMap ρ)).flip inferInstance
    exact d.app_injective V

  have hover : t ≫ jFK (R := R) F = d ≫ q₂ ≫ C.A.A.hom := by
    apply ValDescent.eq_of_comp_jK
    have e₁ : jFK (R := R) F ≫ jK R = spMap ρ ≫ spMap T.φ := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      exact RingHom.ext hF
    have e₂ : T.G.hom ≫ spMap T.φ = T.β ≫ C.G.hom ≫ C.π := by
      rw [← T.ξ_π, ← Category.assoc, ← T.cart.1.w, Category.assoc]
    have e₃ : C.α ≫ C.G.hom ≫ C.π = C.A.A.hom ≫ jK R := by
      rw [← Category.assoc, C.α_cart.1.w, Category.assoc, C.gp_π]
    rw [Category.assoc, e₁, ← Category.assoc, ← hdt, Category.assoc, Category.assoc, e₂, ← Category.assoc q₁,
      hq, Category.assoc, e₃]
    simp only [Category.assoc]
  let P' : Over (Sp (FractionRing R)) := Over.mk (d ≫ q₂ ≫ C.A.A.hom)
  let ℓ : P' ⟶ TFK (R := R) F ⊗ C.A.A := lift (Over.homMk t hover) (Over.homMk (d ≫ q₂) (Category.assoc _ _ _))
  have hfst : ℓ.left ≫ (fst (TFK (R := R) F) C.A.A).left = t := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hsnd : ℓ.left ≫ (snd (TFK (R := R) F) C.A.A).left = d ≫ q₂ := by
    rw [← Over.comp_left, lift_snd]; rfl

  have hL : C.P.L.L.IsLB := C.P.L.isLB
  set i := J (p ≫ T.β) with hi
  set Vβ := LB.wchart C.P.L.L (fun _ : Fin 1 => T.β) (fun _ => i) with hVβ
  set Vα := LB.wchart C.P.L.L (fun _ : Fin 1 => C.α) (fun _ => i) with hVα
  set V : (pullback T.β C.α).Opens := q₁ ⁻¹ᵁ Vβ ⊓ q₂ ⁻¹ᵁ Vα with hV
  have l₀ : V ≤ q₁ ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let a : Γ(pullback T.β C.α, V) :=
    ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_left : V ≤ q₁ ⁻¹ᵁ Vβ)).op).hom ((q₁.app Vβ).hom (σ.f fun _ => i))
  let b : Γ(pullback T.β C.α, V) :=
    ((pullback T.β C.α).presheaf.map (homOfLE l₀).op).hom ((q₁.app ⊤).hom (scal T.G.hom w)) *
    ((pullback T.β C.α).presheaf.map (homOfLE (inf_le_right : V ≤ q₂ ⁻¹ᵁ Vα)).op).hom ((q₂.app Vα).hom (s.f fun _ => i))
  have ka : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V),
      J₀ ((r ≫ q₁) ≫ T.β) = i → gs r z₀ V a = sval σ (r ≫ q₁) z₀ J₀ := by
    intro Z₀ r z₀ J₀ hr hJ₀
    rw [sval_of σ (r ≫ q₁) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]
    exact (gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ Vβ hr.1 _)
  have kb : ∀ (Z₀ : Scheme.{0}) (r : Z₀ ⟶ pullback T.β C.α) (z₀ : Z₀) (J₀ : (Z₀ ⟶ C.G.left) → C.P.L.L.ι) (hr : r z₀ ∈ V),
      J₀ ((r ≫ q₂) ≫ C.α) = i → gs r z₀ V b = gs (r ≫ q₁) z₀ ⊤ (scal T.G.hom w) * sval s (r ≫ q₂) z₀ J₀ := by
    intro Z₀ r z₀ J₀ hr hJ₀
    rw [sval_of s (r ≫ q₂) z₀ J₀ (fun _ => i) (fun _ => hJ₀)]
    exact (gs_mul r z₀ V hr _ _).trans (congrArg₂ (· * ·) ((gs_res r z₀ _ hr _).trans (gs_pull r q₁ z₀ ⊤ trivial _))
      ((gs_res r z₀ _ hr _).trans (gs_pull r q₂ z₀ Vα hr.2 _)))
  have hab : a = b := by
    apply hinj V
    refine fn_ext fun x hx => ?_
    rw [gs_pull (𝟙 _) d x V hx, gs_pull (𝟙 _) d x V hx, Category.id_comp]
    have hmem : ((d ≫ q₁) ≫ T.β) x ∈ C.P.L.L.U i := Set.mem_iInter.1 hx.1 0
    obtain ⟨J', hJ', eJ'⟩ := exists_good C.P.L.L hL x (fun _ : Fin 1 => (d ≫ q₁) ≫ T.β) (fun _ => i) (fun _ _ _ => rfl)
      (fun _ => hmem)
    have e₁ : J' ((d ≫ q₁) ≫ T.β) = i := eJ' 0
    have e₂ : J' ((d ≫ q₂) ≫ C.α) = i := by rw [Category.assoc, ← hq, ← Category.assoc]; exact e₁
    rw [ka _ d x J' hx e₁, kb _ d x J' hx e₂]
    have h₁ : (d ≫ q₁) ≫ T.β = ℓ.left ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α := by
      rw [← Category.assoc, hsnd, Category.assoc, Category.assoc, hq]
    have h₂ : (d ≫ q₁) ≫ T.G.hom = ℓ.left ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ρ := by
      rw [← Category.assoc, hfst, Category.assoc, hdt]
    have := H _ (d ≫ q₁) ℓ.left h₁ h₂ x J' hJ'
    rw [hsnd] at this
    exact this

  set u : Z ⟶ pullback T.β C.α := pullback.lift p p' hpp with hu
  have hu₁ : u ≫ q₁ = p := pullback.lift_fst _ _ _
  have hu₂ : u ≫ q₂ = p' := pullback.lift_snd _ _ _
  have hz : u z ∈ V := by
    refine ⟨Set.mem_iInter.2 fun _ => ?_, Set.mem_iInter.2 fun _ => ?_⟩
    · have h : (p ≫ T.β) z ∈ C.P.L.L.U i := hJ (p ≫ T.β)
      rw [← hu₁] at h
      exact h
    · have h : (p ≫ T.β) z ∈ C.P.L.L.U i := hJ (p ≫ T.β)
      rw [hpp, ← hu₂] at h
      exact h
  have A := ka Z u z J hz (by rw [hu₁])
  have B := kb Z u z J hz (by rw [hu₂, ← hpp])
  rw [hu₁] at A B
  rw [hu₂] at B
  rw [hab] at A
  exact A.symm.trans B

end GlobalTheory.Mum.ValDescent
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValuesIdentityDescendsToFibreProductStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (w : W), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p z ⊤ (scal T.G.hom w) * sval s p' z J := by
  first | exact @GlobalTheory.Mum.ValDescent.desc | exact GlobalTheory.Mum.ValDescent.desc | (intros; apply GlobalTheory.Mum.ValDescent.desc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionDescendsFromAlgClosedField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitDescent

theorem gs_one {Y Z : Scheme.{0}} (p : Z ⟶ Y) (z : Z) : gs p z ⊤ (1 : Γ(Y, ⊤)) = 1 := by
  rw [gs_eq p z ⊤ trivial, map_one, map_one]

theorem scal_mul {A : Type} [CommRing A] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) (a b : A) :
    scal g (a * b) = scal g a * scal g b := by
  unfold scal; rw [map_mul, map_mul]

theorem scal_one {A : Type} [CommRing A] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A)) : scal g 1 = 1 := by
  unfold scal; rw [map_one, map_one]

theorem gs_scal_eq {A F : Type} [CommRing A] [Field F] {Y Z : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of A))
    (io : A →+* F) (p : Z ⟶ Y) (q : Z ⟶ Spec (CommRingCat.of F)) (h : p ≫ g = q ≫ spMap io) (z : Z) (w : A) :
    gs p z ⊤ (scal g w) = gs q z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (io w)) := by
  have e1 := gs_pull p g z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom w)
  have e2 := gs_pull q (spMap io) z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom w)
  have e3 : ((spMap io).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom w) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (io w) := by
    have := congrArg (fun f => f.hom w) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom io))
    exact this.symm
  unfold scal
  rw [← e3]
  exact e1.trans (h ▸ e2.symm)

end GlobalTheory.Mum.TraitDescent

noncomputable section
namespace GlobalTheory.Mum.TraitDescent

theorem sval_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (c : Γ(Y, ⊤)) (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale c s) r z J = gs r z ⊤ c * sval s r z J :=
  (gs_mul r z _ (hJ.mem φ r) _ _).trans (congrArg (· * _) (gs_res r z le_top (hJ.mem φ r) c))

theorem expBy_scale {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (u a : W) {k : ℕ}
    {σ : SecK C.P.L.L T.β k} {F₀ : IntFam (maximalIdeal R) D.toPre k} (h : T.ExpBy u σ F₀) :
    ∃ σ₂ : SecK C.P.L.L T.β k, T.ExpBy (a * u) σ₂ F₀ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) z J,
      Good C.P.L.L z J → sval σ₂ r z J = gs r z ⊤ (scal T.G.hom a) * sval σ r z J := by
  obtain ⟨σ', f', hc, hp, he⟩ := h
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.G.left) z J, Good C.P.L.L z J →
      sval (ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secScale (scal T.G.hom a) σ) r z J = gs r z ⊤ (scal T.G.hom a) * sval σ r z J :=
    fun Z r z J hJ => sval_scale _ σ r z hJ
  refine ⟨_, ⟨σ', f', fun Z r z J J' hJ hJ' => ?_, hp, he⟩, hv⟩
  rw [hv Z r z J hJ, hc Z r z J J' hJ hJ', scal_mul, gs_mul r z ⊤ trivial]
  ring

end GlobalTheory.Mum.TraitDescent

noncomputable section
namespace GlobalTheory.Mum.TraitDescent

theorem exp_of_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre k → SecK C.P.L.L C.α k) (c : F), c ≠ 0 → (∀ F₀, ∃ σ : SecK C.P.L.L T.β k, T.ExpBy 1 σ F₀) → (∀ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J) → ∃ a b : W, a ≠ 0 ∧ b ≠ 0 ∧ ∀ F₀, T.Exp a b (Φ F₀) F₀ := by
  intro R _ _ _ hR D C k W _ _ _ T F _ _ _ _ hF Φ c hc h1 h2
  by_cases hB : ∃ (F₀ : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), T.ExpBy 1 σ F₀ ∧ ∃ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (_ : p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α) (_ : p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _))) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J ∧ sval σ p z J ≠ 0
  · obtain ⟨F₀, σ, hσ, hw⟩ := hB
    obtain ⟨x, hx⟩ := GlobalTheory.T.relatingConstant_mem_traitFractionField R hR D C k W T F hF σ (Φ F₀) c (h2 F₀ σ hσ) hw
    have hx0 : x ≠ 0 := by rintro rfl; exact hc (by rw [← hx, map_zero])
    obtain ⟨⟨b, ⟨a, ha⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors W) x
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hb0 : b ≠ 0 := by rintro rfl; exact hx0 (by simp)
    have key : ((algebraMap (FractionRing W) F).comp (algebraMap W _)) a * c =
        ((algebraMap (FractionRing W) F).comp (algebraMap W _)) b := by
      rw [← hx, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, mul_comm]
      congr 1
      exact IsLocalization.mk'_spec (FractionRing W) b ⟨a, ha⟩
    refine ⟨b, a, hb0, ha0, fun F₁ => ?_⟩
    obtain ⟨σ₁, hσ₁⟩ := h1 F₁
    obtain ⟨σ₂, hσ₂, hv⟩ := expBy_scale T 1 a hσ₁
    rw [_root_.mul_one] at hσ₂
    refine ⟨σ₂, hσ₂, GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct R hR D C k W T F hF σ₂ (Φ F₁) b ?_⟩
    intro Z p p' e1 e2 z J hJ
    have e2' : p ≫ T.G.hom = (p' ≫ (fst (TFK (R := R) F) C.A.A).left) ≫
        spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by rw [e2, Category.assoc]
    have ga := gs_scal_eq T.G.hom ((algebraMap (FractionRing W) F).comp (algebraMap W _)) p _ e2' z a
    have gb := gs_scal_eq T.G.hom ((algebraMap (FractionRing W) F).comp (algebraMap W _)) p _ e2' z b
    rw [hv Z p z J hJ, h2 F₁ σ₁ hσ₁ Z p p' e1 e2 z J hJ, ga, gb, ← _root_.mul_assoc, ← gs_mul _ z ⊤ trivial, fnF, ← map_mul, key]
  · push_neg at hB
    refine ⟨1, 1, one_ne_zero, one_ne_zero, fun F₀ => ?_⟩
    obtain ⟨σ, hσ⟩ := h1 F₀
    refine ⟨σ, hσ, GlobalTheory.T.sectionValues_identity_descends_to_fibreProduct R hR D C k W T F hF σ (Φ F₀) 1 ?_⟩
    intro Z p p' e1 e2 z J hJ
    have h0 := hB F₀ σ hσ Z p p' e1 e2 z J hJ
    have e := h2 F₀ σ hσ Z p p' e1 e2 z J hJ
    rw [h0] at e
    rw [h0, scal_one, gs_one, _root_.one_mul]
    have hu : gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c⁻¹) *
        gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) = 1 := by
      rw [← gs_mul _ z ⊤ trivial, fnF, fnF, ← map_mul, inv_mul_cancel₀ hc, map_one, gs_one]
    rw [← _root_.one_mul (sval (Φ F₀) _ z J), ← hu, _root_.mul_assoc, ← e, mul_zero]

end GlobalTheory.Mum.TraitDescent
end
end
end
end
end
