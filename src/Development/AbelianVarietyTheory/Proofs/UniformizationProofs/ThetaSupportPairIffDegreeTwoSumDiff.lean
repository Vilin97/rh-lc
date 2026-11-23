module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Uniformization.FinrankComplexReal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaAlgClosureWithExpansionsStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsNeZeroIffSvalGenericPointNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSumTmulLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsIntegralTensorLeftOfSmoothGrpObj
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
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorFullLeftSupportStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOneDimStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleSectionsTorusTorsionWeightSpacesStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIff
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.GroupTheory.FiniteAbelian.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorAbelianPartNeZeroIff

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory

theorem isUnit_scal_comp_specMap {R F : Type} [CommRing R] [CommRing F] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of F)) (φ : R →+* F) (r : R) (h : IsUnit (φ r)) :
    IsUnit (scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r) := by
  have e : scal (p ≫ Spec.map (CommRingCat.ofHom φ)) r = scal p (φ r) := by
    have := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    unfold scal
    rw [this]
    rfl
  rw [e]
  exact (h.map _).map _

theorem sval_eq_zero_of_forall_eq_zero {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans ?_
  unfold gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem exists_lift_pair {S : Scheme.{0}} (T₀ B : Over S) {T : Scheme.{0}} (r₁ r₂ : T ⟶ (T₀ ⊗ B).left)
    (h : r₁ ≫ (fst T₀ B).left = r₂ ≫ (fst T₀ B).left) :
    ∃ (q : T ⟶ S) (ρ : Over.mk q ⟶ T₀) (x y : Over.mk q ⟶ B), (lift ρ x).left = r₁ ∧ (lift ρ y).left = r₂ := by
  have w : r₂ ≫ (T₀ ⊗ B).hom = r₁ ≫ (T₀ ⊗ B).hom := by
    rw [← Over.w (fst T₀ B), ← Category.assoc, ← Category.assoc, h]
  let u₁ : Over.mk (r₁ ≫ (T₀ ⊗ B).hom) ⟶ T₀ ⊗ B := Over.homMk r₁ rfl
  let u₂ : Over.mk (r₁ ≫ (T₀ ⊗ B).hom) ⟶ T₀ ⊗ B := Over.homMk r₂ w
  have e : u₁ ≫ fst T₀ B = u₂ ≫ fst T₀ B := Over.OverMorphism.ext h
  refine ⟨_, u₁ ≫ fst T₀ B, u₁ ≫ snd T₀ B, u₂ ≫ snd T₀ B, ?_, ?_⟩
  · rw [lift_comp_fst_snd]; rfl
  · rw [e, lift_comp_fst_snd]; rfl

theorem addB_tensor_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by
  intro R _ _ D F _ _ s₀ r n s s' hr hA
  have := D.P.isAb.proper
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : IsProper (fst (TF (R := R) F) D.P.A).left :=
    inferInstanceAs (IsProper (pullback.fst (TF (R := R) F).hom D.P.A.hom))
  have : IsIntegral (TF (R := R) F).left := inferInstanceAs (IsIntegral (Spec (CommRingCat.of F)))
  have : IsIntegral (TF (R := R) F ⊗ D.P.A).left := isIntegral_tensor_left_of_smooth_grpObj _ _ _
  have key := fun α β : D.X => GlobalTheory.tensor_sections_eq_zero_iff F _ D.P.L D.P.isLB _ _ (fst (TF (R := R) F) D.P.A).left
    (fst (TF (R := R) F) D.P.A).left _ _ (DegPre.famφ D F α) (DegPre.famε 2) (DegPre.famφ D F β) (DegPre.famε 2) n
    (fun i => SecMod.mk _ (s i α)) (fun i => SecMod.mk _ (s' i β))
  refine ⟨fun a b => ⟨fun hne => ?_, fun ⟨ha, hb⟩ h0 => ?_⟩, fun α β hαβ => ?_⟩
  · by_contra hc
    refine hne ((key _ _).2 fun T r₁ r₂ h z J hJ => ?_)
    obtain ⟨q, ρ, x, y, rfl, rfl⟩ := exists_lift_pair _ _ r₁ r₂ h
    refine ((hA (Over.mk q) ρ x y z J hJ).1 a b _ _ rfl rfl).trans ?_
    rcases not_and_or.1 hc with hc | hc
    · have := sval_eq_zero_of_forall_eq_zero (s₀ a) (fun j => by_contra fun hj => hc ⟨j, hj⟩)
        (lift ρ (x * y)).left z J
      exact (congrArg (_ * ·) ((congrArg (· * _) this).trans (zero_mul _))).trans (mul_zero _)
    · have := sval_eq_zero_of_forall_eq_zero (s₀ b) (fun j => by_contra fun hj => hc ⟨j, hj⟩)
        (lift ρ (x * y⁻¹)).left z J
      exact (congrArg (_ * ·) ((congrArg (_ * ·) this).trans (mul_zero _))).trans (mul_zero _)
  · let z := genericPoint (TF (R := R) F ⊗ D.P.A).left
    choose J hJ using fun χ : (TF (R := R) F ⊗ D.P.A).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have hG : Good D.P.L z J := hJ
    have h1 := (key _ _).1 h0 _ (lift (fst (TF (R := R) F) D.P.A) (snd _ _)).left
      (lift (fst (TF (R := R) F) D.P.A) (1 : _ ⟶ D.P.A)).left
      (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z J hG
    have h2 := ((hA (TF (R := R) F ⊗ D.P.A) (fst _ _) (snd _ _) 1 z J hG).1 a b _ _ rfl rfl).symm.trans h1
    rw [inv_one, _root_.mul_one, lift_fst_snd] at h2
    have hu : IsUnit (scal (TF (R := R) F ⊗ D.P.A).hom r) := by
      have e : (TF (R := R) F ⊗ D.P.A).hom = (fst (TF (R := R) F) D.P.A).left ≫ Spec.map (CommRingCat.ofHom
          ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))) := by
        rw [← Over.w (fst (TF (R := R) F) D.P.A), CommRingCat.ofHom_comp, Spec.map_comp]; rfl
      rw [e]
      refine isUnit_scal_comp_specMap _ _ r (IsUnit.mk0 _ ?_)
      exact (map_ne_zero (algebraMap (FractionRing R) F)).2 ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr)
    have hu' : IsUnit (gs (𝟙 _) z ⊤ (scal (TF (R := R) F ⊗ D.P.A).hom r)) := by
      rw [gs_eq _ z ⊤ trivial]
      exact (hu.map _).map _
    exact mul_ne_zero (mul_ne_zero hu'.ne_zero (Units.ne_zero _))
      (mul_ne_zero ((exists_ne_zero_iff_sval_ne_zero (s₀ a) hG).1 ha)
        ((exists_ne_zero_iff_sval_ne_zero (s₀ b) hG).1 hb)) h2
  · refine (key _ _).2 fun T r₁ r₂ h z J hJ => ?_
    obtain ⟨q, ρ, x, y, rfl, rfl⟩ := exists_lift_pair _ _ r₁ r₂ h
    exact (hA (Over.mk q) ρ x y z J hJ).2 α β hαβ

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionTensorAbelianPartNeZeroIffStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.additionTensor_abelianPart_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (s₀ : Raw D F 1) (r : R) (n : ℕ) (s s' : Fin n → Raw D F 2), r ≠ 0 → AddB D (TF (R := R) F) s₀ r s s' → (∀ a b : D.X, (∑ i, TensorProduct.tmul F (SecMod.mk _ (s i (a + b)) : WB D F 2 (a + b)) (SecMod.mk _ (s' i (a - b)) : WB D F 2 (a - b)) ≠ 0 ↔ (∃ j, (s₀ a).f j ≠ 0) ∧ ∃ j, (s₀ b).f j ≠ 0)) ∧ ∀ α β : D.X, (¬ ∃ a b, α = a + b ∧ β = a - b) → ∑ i, TensorProduct.tmul F (SecMod.mk _ (s i α) : WB D F 2 α) (SecMod.mk _ (s' i β) : WB D F 2 β) = 0 := by
  first | exact @GlobalTheory.addB_tensor_ne_zero_iff | exact GlobalTheory.addB_tensor_ne_zero_iff | (intros; apply GlobalTheory.addB_tensor_ne_zero_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearFourierJacobiExpansionFamilyStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.exists_linear_fourierJacobi_expansion_family : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∃ ex : ∀ α : D.X, EA A (jFK (R := V) F) k →ₗ[F] WB D F k α, (∀ t, U.ExpF F k t.sec (fun α => (ex α t).sec)) ∧ (∀ t s, U.ExpF F k t s → ∀ α, s α = (ex α (SecMod.mk _ t)).sec) ∧ (∀ t, (∀ α, ex α t = 0) → t = 0) ∧ ∀ α, (U.Supp F k α ↔ ex α ≠ 0)) := by
  first | exact @GlobalTheory.UU.ExpLinMap.exists_expansion_linear | exact GlobalTheory.UU.ExpLinMap.exists_expansion_linear | (intros; apply GlobalTheory.UU.ExpLinMap.exists_expansion_linear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullbackSectionFamilyNeZeroIffStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.pullbackSectionFamily_ne_zero_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (f : ∀ α, SecBT D (𝟙_ _) k α) (s : Raw D F k), PullB D F (toUnit _) k f s → ∀ α, ((∃ j, (s α).f j ≠ 0) ↔ ∃ j, (f α).f j ≠ 0) := by
  first | exact @GlobalTheory.pullB_ne_zero_iff | exact GlobalTheory.pullB_ne_zero_iff | (intros; apply GlobalTheory.pullB_ne_zero_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TensorComponentNeZeroIff

section

@[expose] public section

namespace GlobalTheory

theorem tensor_component_ne_zero_iff (F : Type) [Field F] (X C : Type) [Finite C] (cl : X → C)
    (E : Type) [AddCommGroup E] [Module F E] (W : X → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module F (W a)] (ex : ∀ a, E →ₗ[F] W a)
    (hsep : ∀ s, (∀ a, ex a s = 0) → s = 0)
    (hcut : ∀ (c : C) (s : E), ∃ s' : E, ∀ a,
      (cl a = c → ex a s' = ex a s) ∧ (cl a ≠ c → ex a s' = 0))
    (hinj : ∀ a, ex a ≠ 0 → ∀ s, (∀ b, cl b ≠ cl a → ex b s = 0) → ex a s = 0 → s = 0)
    (w : TensorProduct F E E)
    (hfull : ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E →ₗ[F] E) w = 0 → π = 0)
    (hoff : ∀ a b, cl a ≠ cl b → TensorProduct.map (ex a) (ex b) w = 0)
    (a b : X) (hab : cl a = cl b) :
    TensorProduct.map (ex a) (ex b) w ≠ 0 ↔ ex a ≠ 0 ∧ ex b ≠ 0 := by
  classical
  have := Fintype.ofFinite C
  choose p hp using hcut
  have hext : ∀ s t : E, (∀ x, ex x s = ex x t) → s = t := fun s t h =>
    sub_eq_zero.mp (hsep _ fun x => by rw [map_sub, h x, sub_self])
  let π : C → E →ₗ[F] E := fun c =>
    { toFun := p c
      map_add' := fun s t => hext _ _ fun x => by
        by_cases hx : cl x = c
        · rw [map_add (f := _), (hp c _ x).1 hx, (hp c _ x).1 hx, (hp c _ x).1 hx, map_add (f := _)]
        · rw [map_add (f := _), (hp c _ x).2 hx, (hp c _ x).2 hx, (hp c _ x).2 hx, add_zero]
      map_smul' := fun r s => hext _ _ fun x => by
        by_cases hx : cl x = c
        · rw [RingHom.id_apply, map_smul, (hp c _ x).1 hx, (hp c _ x).1 hx, map_smul]
        · rw [RingHom.id_apply, map_smul, (hp c _ x).2 hx, (hp c _ x).2 hx, smul_zero] }
  have h1 : ∀ c s x, cl x = c → ex x (π c s) = ex x s := fun c s x h => (hp c s x).1 h
  have h0 : ∀ c s x, cl x ≠ c → ex x (π c s) = 0 := fun c s x h => (hp c s x).2 h
  have hsum : ∑ c, π c = LinearMap.id := by
    refine LinearMap.ext fun s => hext _ _ fun x => ?_

    rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single (cl x)]
    · exact h1 _ s x rfl
    · intro c _ hc
      exact h0 c s x (Ne.symm hc)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hfac : ∀ x, ex x ≠ 0 → ∃ r : W x →ₗ[F] E, r ∘ₗ ex x = π (cl x) := by
    intro x hx
    have hk : LinearMap.ker (ex x ∘ₗ (LinearMap.range (π (cl x))).subtype) = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      rintro ⟨_, s, rfl⟩ hs
      exact Subtype.ext (hinj x hx _ (fun y hy => h0 _ s y hy) hs)
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hk
    refine ⟨(LinearMap.range (π (cl x))).subtype ∘ₗ g, LinearMap.ext fun s => ?_⟩
    have h2 := congrArg Subtype.val
      (LinearMap.congr_fun hg ⟨π (cl x) s, LinearMap.mem_range_self _ s⟩)
    rw [LinearMap.comp_apply, ← h1 (cl x) s x rfl]
    exact h2
  have hpass : ∀ x y, ex x ≠ 0 → ex y ≠ 0 → TensorProduct.map (ex x) (ex y) w = 0 →
      TensorProduct.map (π (cl x)) (π (cl y)) w = 0 := by
    intro x y hx hy h
    obtain ⟨r, hr⟩ := hfac x hx
    obtain ⟨t, ht⟩ := hfac y hy
    rw [← hr, ← ht, TensorProduct.map_comp, LinearMap.comp_apply, h, map_zero]
  constructor
  · intro h
    constructor
    · intro ha
      apply h
      rw [ha, TensorProduct.map_zero_left, LinearMap.zero_apply]
    · intro hb
      apply h
      rw [hb, TensorProduct.map_zero_right, LinearMap.zero_apply]
  · rintro ⟨ha, hb⟩ h
    have hall : ∀ c, TensorProduct.map (π (cl a)) (π c) w = 0 := by
      intro c
      by_cases hc : cl b = c
      · rw [← hc]
        exact hpass a b ha hb h
      by_cases hy : ∃ y, cl y = c ∧ ex y ≠ 0
      · obtain ⟨y, rfl, hy⟩ := hy
        exact hpass a y ha hy (hoff a y (hab ▸ hc))
      · have hz : π c = 0 := by
          refine LinearMap.ext fun s => hsep _ fun y => ?_
          by_cases hyc : cl y = c
          · have : ex y = 0 := by
              by_contra hne
              exact hy ⟨y, hyc, hne⟩
            rw [this, LinearMap.zero_apply]
          · exact h0 c s y hyc
        rw [hz, TensorProduct.map_zero_right, LinearMap.zero_apply]
    have hz : π (cl a) = 0 := by
      apply hfull
      have e : TensorProduct.map (π (cl a)) (∑ c, π c) =
          ∑ c, TensorProduct.map (π (cl a)) (π c) :=
        map_sum (TensorProduct.mapBilinear (RingHom.id F) E E E E (π (cl a))) π Finset.univ
      rw [← hsum, e, LinearMap.sum_apply]
      exact Finset.sum_eq_zero fun c _ => hall c
    apply ha
    refine LinearMap.ext fun s => ?_
    rw [← h1 (cl a) s a rfl, hz, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaSupportPairIffDegreeTwoSumDiff

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
namespace GlobalTheory.UU.SuppRel

theorem component_ne_zero_iff_mod_two (F : Type) [Field F] (X : Type) [AddCommGroup X] [Module.Finite ℤ X]
    (E : Type) [AddCommGroup E] [Module F E] (W : X → Type) [∀ a, AddCommGroup (W a)]
    [∀ a, Module F (W a)] (ex : ∀ a, E →ₗ[F] W a)
    (hsep : ∀ s, (∀ a, ex a s = 0) → s = 0)
    (hcut : ∀ (α : X) (s : E), ∃ s' : E, ∀ β,
      ((∃ mu, β = α + 2 • mu) → ex β s' = ex β s) ∧ ((¬ ∃ mu, β = α + 2 • mu) → ex β s' = 0))
    (hinj : ∀ α, ex α ≠ 0 → ∀ s, (∀ β, (¬ ∃ mu, β = α + 2 • mu) → ex β s = 0) → ex α s = 0 → s = 0)
    (w : TensorProduct F E E)
    (hfull : ∀ π : E →ₗ[F] E, TensorProduct.map π (LinearMap.id : E →ₗ[F] E) w = 0 → π = 0)
    (hoff : ∀ α β, (¬ ∃ a b, α = a + b ∧ β = a - b) → TensorProduct.map (ex α) (ex β) w = 0)
    (a b : X) :
    TensorProduct.map (ex (a + b)) (ex (a - b)) w ≠ 0 ↔ ex (a + b) ≠ 0 ∧ ex (a - b) ≠ 0 := by
  let H : AddSubgroup X := (nsmulAddMonoidHom 2 : X →+ X).range
  have hfg : AddGroup.FG X := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hH : H.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg X two_ne_zero
  have hfin : Finite (X ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  have hcl : ∀ α β : X, (QuotientAddGroup.mk β : X ⧸ H) = QuotientAddGroup.mk α ↔ ∃ mu, β = α + 2 • mu := by
    intro α β
    rw [eq_comm, QuotientAddGroup.eq]
    constructor
    · rintro ⟨mu, h⟩
      exact ⟨mu, by rw [nsmulAddMonoidHom_apply] at h; rw [h]; abel⟩
    · rintro ⟨mu, h⟩
      exact ⟨mu, by rw [nsmulAddMonoidHom_apply, h]; abel⟩
  refine GlobalTheory.tensor_component_ne_zero_iff F X (X ⧸ H) QuotientAddGroup.mk E W ex hsep ?_ ?_ w hfull ?_ _ _ ?_
  · intro c s
    obtain ⟨α, rfl⟩ := QuotientAddGroup.mk_surjective c
    obtain ⟨s', hs'⟩ := hcut α s
    exact ⟨s', fun β => ⟨fun h => (hs' β).1 ((hcl α β).1 h), fun h => (hs' β).2 fun h' => h ((hcl α β).2 h')⟩⟩
  · intro α hα s hs h0
    exact hinj α hα s (fun β hβ => hs β fun h => hβ ((hcl α β).1 h)) h0
  · intro α β h
    refine hoff α β ?_
    rintro ⟨x, y, rfl, rfl⟩
    exact h ((hcl _ _).2 ⟨y, by rw [two_nsmul]; abel⟩)
  · exact (hcl _ _).2 ⟨b, by rw [two_nsmul]; abel⟩

theorem supp_rel : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ a b : D.X, ((∃ j, (f a).f j ≠ 0) ∧ ∃ j, (f b).f j ≠ 0) ↔ (U.Supp (Kbar V) 2 (a + b) ∧ U.Supp (Kbar V) 2 (a - b))) := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ a b
  obtain ⟨hG, hB⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 1
  obtain ⟨th, hth, -⟩ := hG θ
  obtain ⟨s₀, hs₀, -⟩ := hB f
  obtain ⟨r, n, t, t', s, s', hr, hexp, hA, hAB⟩ := GlobalTheory.T.additionFormula_algClosure_with_expansions hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  obtain ⟨hth0, -, -⟩ := GlobalTheory.T.expF_of_theta_degree_one hL hL2 V hV D A G U θ f hθ th s₀ hth hs₀
  obtain ⟨ex, hex, huniq, hsep, hsupp⟩ := GlobalTheory.T.exists_linear_fourierJacobi_expansion_family hL hL2 V hV D A G U (Kbar V) 2 (by norm_num)
  obtain ⟨hcut, -, hinj⟩ := GlobalTheory.T.lineBundleSections_torusTorsion_weightSpaces hL hL2 V hV D A G U 2 (by norm_num)
  obtain ⟨hon, hoff⟩ := GlobalTheory.T.additionTensor_abelianPart_ne_zero_iff V D (Kbar V) s₀ r n s s' hr hAB
  have hcV : CharZero V := hV.2.2
  have hchar : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  have h2 : (2 : Kbar V) ≠ 0 := two_ne_zero
  let u : Fin n → EA A (jFK (R := V) (Kbar V)) 2 := fun i => SecMod.mk _ (t i)
  let u' : Fin n → EA A (jFK (R := V) (Kbar V)) 2 := fun i => SecMod.mk _ (t' i)
  have hfull := GlobalTheory.T.additionTensor_full_left_support hL hL2 _ A (Kbar V) (jFK (R := V) (Kbar V)) h2 (SecMod.mk _ th) n u u' hA
    (fun h => by
      obtain ⟨j, hj⟩ := hth0
      exact hj ((SecMod.eq_zero_iff _).1 h j))
  have hmap : ∀ α β : D.X, TensorProduct.map (ex α) (ex β) (∑ i, TensorProduct.tmul (Kbar V) (u i) (u' i)) =
      ∑ i, TensorProduct.tmul (Kbar V) (SecMod.mk _ (s i α) : WB D (Kbar V) 2 α)
        (SecMod.mk _ (s' i β) : WB D (Kbar V) 2 β) := by
    intro α β

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.map_tmul, huniq _ _ (hexp i).1 α, huniq _ _ (hexp i).2 β]
    rfl
  have key := component_ne_zero_iff_mod_two (Kbar V) D.X (EA A (jFK (R := V) (Kbar V)) 2)
    (fun α => WB D (Kbar V) 2 α) ex hsep ?_ ?_ _ hfull (fun α β h => (hmap α β).trans (hoff α β h)) a b
  · rw [hsupp, hsupp, ← key, hmap, hon, GlobalTheory.T.pullbackSectionFamily_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ a,
      GlobalTheory.T.pullbackSectionFamily_ne_zero_iff V D (Kbar V) 1 f s₀ hs₀ b]
  · intro α v
    obtain ⟨v', p, hp, hβ⟩ := hcut α _ _ (hex v)
    refine ⟨SecMod.mk _ v', fun β => ⟨fun h => ?_, fun h => ?_⟩⟩
    · rcases hβ β with h' | h'
      · exact (huniq _ _ hp β).symm.trans h'.2
      · exact absurd h h'.1
    · rcases hβ β with h' | h'
      · exact absurd h'.1 h
      · refine (SecMod.eq_zero_iff _).2 fun j => ?_
        rw [← huniq _ _ hp β]
        exact h'.2 j
  · intro α hα v hv h0
    exact (SecMod.eq_zero_iff _).2 (hinj α ((hsupp α).2 hα) _ _ (hex v)
      (fun β hβ => (SecMod.eq_zero_iff _).1 (hv β hβ)) ((SecMod.eq_zero_iff _).1 h0))

end GlobalTheory.UU.SuppRel
end
end
