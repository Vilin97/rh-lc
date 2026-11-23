module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
public import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
public import Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeAffineSectionsSubalgebraTensor
public import Mathlib.Tactic.ENatToNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import GroundTheory.FunctionField.PlaceDefs
public import Mathlib.AlgebraicGeometry.Properties
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsChartAffineSectionsOfIsCurve
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsCurvePullbackOfIsCurveBaseChange
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsDedekindDomainAffineSectionsOfIsCurve
public import GroundTheory.FunctionField.PlaceDefs
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveFunctionField
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AutomorphicArithmetic.CommutativeAlgebra.SurjectiveOfIsPullbackSpecFieldExt
public import Development.AutomorphicArithmetic.CommutativeAlgebra.TensorFractionRingExistsMulEqOfDenominator
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeFunctionFieldHomGenericPointComp

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.baseChange_functionField_hom_genericPoint_comp :
    ∀ (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u → ∃ f : L →+* X.functionField, (∀ r : k, f (algebraMap k L r) = φ (algebraMap k C.functionField r)) ∧ ∀ (V : X.Opens) [Nonempty V] (l : L), X.germToFunctionField V (x.appLE ⊤ V le_top ((Scheme.ΓSpecIso (CommRingCat.of L)).inv l)) = f l := by
  intro k L _ _ _ C X _ _ c u x hpb _ hc φ hφ
  let F : CommRingCat.of L ⟶ X.functionField :=
    (Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial
  have hx : X.fromSpecStalk (genericPoint X) ≫ x = Spec.map F := by
    have h1 := Scheme.toSpecΓ_naturality x
    have h2 : x = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ x.appTop) := by
      rw [Spec.map_comp, ← Category.assoc, ← h1, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    rw [h2, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
    simp only [F, Category.assoc]
  have key : ∀ (V : X.Opens) (hV : genericPoint X ∈ V),
      x.appLE ⊤ V le_top ≫ X.presheaf.germ V (genericPoint X) hV =
        x.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial := by
    intro V hV
    rw [← x.appLE_map (V := ⊤) (V' := V) le_top (homOfLE le_top).op, Category.assoc,
      X.presheaf.germ_res, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨F.hom, ?_, ?_⟩
  · intro r
    have hsq : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField) ≫ CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap k L) ≫ F) := by
      rw [Spec.map_comp, Spec.map_comp, hc, ← Category.assoc, hφ, Category.assoc, hpb.w,
        ← Category.assoc, hx]
    have := congrArg (fun g => g.hom r) (Spec.map_injective hsq)
    simpa using this.symm
  · intro V _ l
    have hV : genericPoint X ∈ V :=
      ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
    have := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of L)).inv.hom l)) (key V hV)
    simpa [F] using this
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFiniteNonemptyAffineCoverOfIntegral

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_finite_nonempty_affine_cover_of_integral :
    ∀ (C : Scheme.{0}) [CompactSpace C] [IsIntegral C], ∃ (n : ℕ) (U : Fin n → C.Opens), (∀ i, IsAffineOpen (U i)) ∧ (∀ i, Nonempty (U i)) ∧ (0 < n) ∧ ∀ y : C, ∃ i, y ∈ U i := by
  intro C _ _
  have hex : ∀ y : C, ∃ W : C.Opens, IsAffineOpen W ∧ y ∈ W := fun y => by
    obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
    exact ⟨W, hW, hy⟩
  choose W hWa hyW using hex
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set C))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩)
  obtain ⟨y0⟩ := (inferInstance : Nonempty C)
  have htne : t.Nonempty := by
    obtain ⟨i, hi, -⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y0))
    exact ⟨i, hi⟩
  refine ⟨t.card, fun i => W (t.equivFin.symm i), fun i => hWa _,
    fun i => ⟨⟨_, hyW _⟩⟩, Finset.card_pos.2 htne, fun y => ?_⟩
  obtain ⟨i, hi, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  refine ⟨t.equivFin ⟨i, hi⟩, ?_⟩
  simpa using hy
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsFunctionFieldHomGermOfSurjective

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_functionField_hom_germ_of_surjective :
    ∀ {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X] (u : X ⟶ C), Surjective u → ∃ φ : C.functionField →+* X.functionField, Spec.map (CommRingCat.ofHom φ) ≫ C.fromSpecStalk (genericPoint C) = X.fromSpecStalk (genericPoint X) ≫ u ∧ ∀ (W : C.Opens) [Nonempty W] [Nonempty (u ⁻¹ᵁ W)] (a : Γ(C, W)), φ (C.germToFunctionField W a) = X.germToFunctionField (u ⁻¹ᵁ W) (u.app W a) := by
  intro C X _ _ u hu
  have hgX : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hcl : closure ({u (genericPoint X)} : Set C) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    have h1 := image_closure_subset_closure_image (s := ({genericPoint X} : Set X)) u.continuous
    rw [Set.image_singleton, hgX, Set.image_univ,
      (Surjective.surj (f := u)).range_eq] at h1
    exact h1
  have hsp : u (genericPoint X) ⤳ genericPoint C := by
    rw [specializes_iff_mem_closure, hcl]
    trivial
  refine ⟨(C.presheaf.stalkSpecializes hsp ≫ u.stalkMap (genericPoint X)).hom, ?_, ?_⟩
  · rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  · intro W _ _ a
    have hmem : u (genericPoint X) ∈ W :=
      ((genericPoint_spec X).mem_open_set_iff (u ⁻¹ᵁ W).isOpen).mpr (by simpa using ‹Nonempty (u ⁻¹ᵁ W)›)
    change (u.stalkMap (genericPoint X)).hom ((C.presheaf.stalkSpecializes hsp).hom
      ((C.presheaf.germ W (genericPoint C) _).hom a)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply (hy := _) (h := hsp)]
    exact Scheme.Hom.germ_stalkMap_apply u W (genericPoint X) hmem a
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSubalgebraEqRangeGermToFunctionField

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.exists_subalgebra_eq_range_germToFunctionField :
    ∀ (k : Type) [Field k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k) [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → ∀ (W : C.Opens) [Nonempty W], ∃ B : Subalgebra k C.functionField, (B : Set C.functionField) = Set.range (C.germToFunctionField W) := by
  intro k _ C _ c _ h W _
  have hη : genericPoint C ∈ (⊤ : C.Opens) := trivial
  have key : CommRingCat.ofHom (algebraMap k C.functionField) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ c.appTop ≫ C.presheaf.germ ⊤ (genericPoint C) hη := by
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of k)).hom, ← Scheme.ΓSpecIso_naturality, h]
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Iso.hom_inv_id_assoc]
    congr 1
    rw [Scheme.fromSpecStalk_appTop]
    have e1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk (genericPoint C))).Opens) ≤ ⊤)) = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [e1, op_id, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
    exact congrArg (C.presheaf.germ ⊤ (genericPoint C) _ ≫ ·) (Iso.inv_hom_id _) |>.trans
      (Category.comp_id _)
  refine ⟨{ (C.germToFunctionField W).hom.range with algebraMap_mem' := ?_ }, ?_⟩
  · intro r
    refine ⟨C.presheaf.map (homOfLE le_top).op (c.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r)), ?_⟩
    have hr := congrArg (fun f => f.hom r) key
    simp only [CommRingCat.hom_ofHom, CommRingCat.comp_apply] at hr
    rw [hr]
    exact C.presheaf.germ_res_apply (homOfLE le_top) _ _ _
  · rfl
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldOfDedekindFiniteTypeFractionRing

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

theorem UpperTheory.isFunctionField_of_dedekind_finiteType_fractionRing :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (B : Subalgebra k K), IsDedekindDomain B → Algebra.FiniteType k B → ¬ IsField B → IsFractionRing B K → IsFunctionField k K := by
  intro k K _ _ _ B hD hF hB hFr
  have hdim : ringKrullDim B = 1 := by
    apply eq_of_le_of_not_lt ?_ fun h' ↦ hB ?_
    · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
      infer_instance
    · have h'' : ringKrullDim B ≤ 0 := Order.le_of_lt_succ h'
      rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
      exact Ring.KrullDimLE.isField_of_isDomain
  exact GroundTheory.Arith.SchemeCoh.isFunctionField_of_ringKrullDim_eq_one k B K hdim
end
end

-- Source module: Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldAndChartCoverOfIsCurve

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

private theorem exists_tensor_lift {k L K M : Type} [Field k] [Field L] [Field K] [CommRing M] [Algebra k L] [Algebra k K]
    (f : L →+* M) (g : K →+* M) (h : ∀ r : k, f (algebraMap k L r) = g (algebraMap k K r)) :
    ∃ θ : L ⊗[k] K →+* M, ∀ l a, θ (l ⊗ₜ[k] a) = f l * g a := by
  letI : Algebra k M := (g.comp (algebraMap k K)).toAlgebra
  let f' : L →ₐ[k] M := { f with commutes' := fun r => h r }
  let g' : K →ₐ[k] M := { g with commutes' := fun r => rfl }
  exact ⟨(Algebra.TensorProduct.productMap f' g').toRingHom, fun l a => by simp [f', g']⟩

private theorem core (k L : Type) [Field k] [Field L] [Algebra k L] {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]
    (c : C ⟶ Sp k) (u : X ⟶ C) (x : X ⟶ Sp L)
    (hpb : IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    [Algebra k C.functionField]
    (hK : Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c)
    {n : ℕ} (U : Fin n → C.Opens) (hUa : ∀ i, IsAffineOpen (U i)) [hne : ∀ i, Nonempty (U i)]
    (hUc : ∀ y : C, ∃ i, y ∈ U i) (hn : 0 < n)
    (B : Fin n → Subalgebra k C.functionField)
    (hB : ∀ i, (B i : Set C.functionField) = Set.range (C.germToFunctionField (U i)))
    (hfr : ∀ i, IsFractionRing (B i) C.functionField) :
    ∃ θ : L ⊗[k] C.functionField →+* X.functionField,
      Spec.map (CommRingCat.ofHom (θ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u ∧ Function.Injective θ ∧ (∀ h : X.functionField, ∃ a b, b ≠ 0 ∧ h * θ b = θ a) ∧ ∀ y : X, ∃ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsPrime ∧ ∀ s ∉ m, ∃ w : (X.presheaf.stalk y)ˣ, algebraMap (X.presheaf.stalk y) X.functionField w = θ (inc L (B i) s) := by
  have hsurj := UpperTheory.surjective_of_isPullback_spec_field_ext k L c u x hpb
  obtain ⟨φ, hφgen, hφgerm⟩ := UpperTheory.exists_functionField_hom_germ_of_surjective u hsurj
  obtain ⟨f, hfk, hfx⟩ := UpperTheory.baseChange_functionField_hom_genericPoint_comp k L c u x hpb hK φ hφgen
  obtain ⟨θ, hθ⟩ := exists_tensor_lift f φ hfk
  have hne' : ∀ i, Nonempty (u ⁻¹ᵁ U i) := by
    intro i
    obtain ⟨⟨z, hz⟩⟩ := hne i
    obtain ⟨y, rfl⟩ := hsurj.surj z
    exact ⟨⟨y, hz⟩⟩
  have chart : ∀ i, IsAffineOpen (u ⁻¹ᵁ U i) ∧ ∃ e : L ⊗[k] B i ≃+* Γ(X, u ⁻¹ᵁ U i),
      ∀ s, θ (inc L (B i) s) = X.germToFunctionField (u ⁻¹ᵁ U i) (e s) := by
    intro i
    haveI := hne' i
    obtain ⟨hV, e, he1, he2⟩ := UpperTheory.baseChange_affine_sections_subalgebra_tensor k L c u x hpb hK (U i) (hUa i) (B i) (hB i)
    refine ⟨hV, e, fun s => ?_⟩
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul l b =>
      obtain ⟨a, ha⟩ : (b : C.functionField) ∈ Set.range (C.germToFunctionField (U i)) := by
        rw [← hB i]
        exact b.2
      have hsplit : l ⊗ₜ[k] b = (l ⊗ₜ[k] (1 : B i)) * ((1 : L) ⊗ₜ[k] b) := by
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [show inc L (B i) (l ⊗ₜ[k] b) = l ⊗ₜ[k] (b : C.functionField) from rfl, hθ, hsplit,
        map_mul, map_mul, he1 a b ha.symm, he2 l, hfx, ← hφgerm (U i) a, ha]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]
  have hcomp : θ.comp Algebra.TensorProduct.includeRight.toRingHom = φ := by
    ext a
    simp [Algebra.TensorProduct.includeRight_apply, hθ]
  have hinj : Function.Injective θ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨hV0, e0, he0⟩ := chart ⟨0, hn⟩
    haveI := hne' ⟨0, hn⟩
    obtain ⟨s, β, hβ, hs⟩ := UpperTheory.tensor_fractionRing_exists_mul_eq_of_denominator k L C.functionField (B ⟨0, hn⟩) (hfr _) t
    have h1 : θ (inc L (B ⟨0, hn⟩) s) = 0 := by rw [← hs, map_mul, ht, zero_mul]
    rw [he0] at h1
    have h2 : e0 s = 0 :=
      X.germToFunctionField_injective _ (h1.trans (map_zero _).symm)
    have h3 : s = 0 := e0.injective (h2.trans (map_zero e0).symm)
    rw [h3, map_zero] at hs
    have hβ' : (β : C.functionField) ≠ 0 := fun h => hβ (Subtype.ext h)
    have hu : IsUnit ((1 : L) ⊗ₜ[k] (β : C.functionField)) := by
      refine ⟨⟨1 ⊗ₜ[k] (β : C.functionField), 1 ⊗ₜ[k] (β : C.functionField)⁻¹, ?_, ?_⟩, rfl⟩
      · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hβ']
        rfl
      · rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hβ']
        rfl
    exact hu.mul_left_eq_zero.mp hs
  refine ⟨θ, by rw [hcomp]; exact hφgen, hinj, ?_, ?_⟩
  · intro h
    obtain ⟨hV, e, he⟩ := chart ⟨0, hn⟩
    haveI := hne' ⟨0, hn⟩
    haveI := functionField_isFractionRing_of_isAffineOpen X _ hV
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, u ⁻¹ᵁ U ⟨0, hn⟩)) h
    refine ⟨inc L (B ⟨0, hn⟩) (e.symm p), inc L (B ⟨0, hn⟩) (e.symm q), ?_, ?_⟩
    · intro h0
      have h4 := congrArg θ h0
      rw [he, map_zero, e.apply_symm_apply] at h4
      have h5 : (q : Γ(X, u ⁻¹ᵁ U ⟨0, hn⟩)) = 0 :=
        X.germToFunctionField_injective _ (h4.trans (map_zero _).symm)
      exact nonZeroDivisors.coe_ne_zero q h5
    · rw [he, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hpq
  · intro y
    obtain ⟨i, hi⟩ := hUc (u y)
    haveI := hne' i
    obtain ⟨hV, e, he⟩ := chart i
    have hy : y ∈ u ⁻¹ᵁ U i := hi
    refine ⟨i, (hV.primeIdealOf ⟨y, hy⟩).asIdeal.comap e.toRingHom, inferInstance, fun s hs => ?_⟩
    have hsP : e s ∉ (hV.primeIdealOf ⟨y, hy⟩).asIdeal := hs
    letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hy⟩
    haveI := hV.isLocalization_stalk ⟨y, hy⟩
    refine ⟨(IsLocalization.map_units (X.presheaf.stalk y)
      (⟨e s, hsP⟩ : (hV.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)).unit, ?_⟩
    rw [he]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hy (e s)

theorem UpperTheory.isFunctionField_and_chart_cover_of_isCurve :
    ∀ (k : Type) [Field k] [IsAlgClosed k] {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → IsFunctionField k C.functionField ∧ ∃ (n : ℕ) (B : Fin n → Subalgebra k C.functionField), (∀ i, IsChart (B i)) ∧ ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra k L], ∃ (X : Scheme.{0}) (_ : IsIntegral X) (u : X ⟶ C) (x : X ⟶ Sp L) (θ : L ⊗[k] C.functionField →+* X.functionField), IsPullback u x c (Spec.map (CommRingCat.ofHom (algebraMap k L))) ∧ (∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y)) ∧ Spec.map (CommRingCat.ofHom (θ.comp Algebra.TensorProduct.includeRight.toRingHom)) ≫ (C.fromSpecStalk (genericPoint C)) = (X.fromSpecStalk (genericPoint X)) ≫ u ∧ Function.Injective θ ∧ (∀ h : X.functionField, ∃ a b, b ≠ 0 ∧ h * θ b = θ a) ∧ ∀ y : X, ∃ (i : Fin n) (m : Ideal (L ⊗[k] B i)), m.IsPrime ∧ ∀ s ∉ m, ∃ w : (X.presheaf.stalk y)ˣ, algebraMap (X.presheaf.stalk y) X.functionField w = θ (inc L (B i) s) := by
  intro k _ _ C _ c hcurve _ hK
  have hprop : IsProper c := hcurve.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨n, U, hUa, hUne, hn, hUc⟩ := UpperTheory.exists_finite_nonempty_affine_cover_of_integral C
  haveI : ∀ i, Nonempty (U i) := hUne
  have hex : ∀ i, ∃ B : Subalgebra k C.functionField,
      (B : Set C.functionField) = Set.range (C.germToFunctionField (U i)) :=
    fun i => UpperTheory.exists_subalgebra_eq_range_germToFunctionField k c hK (U i)
  choose B hB using hex
  have hchart : ∀ i, IsChart (B i) :=
    fun i => UpperTheory.isChart_affine_sections_of_isCurve k c hcurve hK (U i) (hUa i) (B i) (hB i)
  refine ⟨UpperTheory.isFunctionField_of_dedekind_finiteType_fractionRing k C.functionField (B ⟨0, hn⟩) (hchart _).2.1 (hchart _).1
    (hchart _).2.2.1 (hchart _).2.2.2.1, n, B, hchart, ?_⟩
  intro L _ _ _
  let g := Spec.map (CommRingCat.ofHom (algebraMap k L))
  have hpb : IsPullback (pullback.fst c g) (pullback.snd c g) c g := IsPullback.of_hasPullback c g
  have hcurve' := UpperTheory.isCurve_pullback_of_isCurve_baseChange k L c hcurve
  haveI hXint : IsIntegral (pullback c g) := hcurve'.1
  have hstalk := (UpperTheory.isDedekindDomain_affine_sections_of_isCurve L (pullback.snd c g) hcurve').2
  obtain ⟨θ, h1, h2, h3, h4⟩ := core k L c (pullback.fst c g) (pullback.snd c g) hpb hK U hUa hUc hn
    B hB (fun i => (hchart i).2.2.2.1)
  exact ⟨pullback c g, hXint, pullback.fst c g, pullback.snd c g, θ, hpb, hstalk, h1, h2, h3, h4⟩
end
end
