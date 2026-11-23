module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
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
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAppOfIsAffineHomFlatSurjective

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory

theorem faithfullyFlat_app_of_isAffineHom_flat_surjective :
    ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (V : Y.Opens), IsAffineHom p → Flat p → Surjective p →
      IsAffineOpen V → (p.app V).hom.FaithfullyFlat := by
  intro X Y p V _ _ _ hV
  have hpre : IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
  have : IsAffine V := hV
  have : IsAffine (p ⁻¹ᵁ V) := hpre
  have : Flat (p ∣_ V) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict p V).flip ‹Flat p›
  have : Surjective (p ∣_ V) := IsZariskiLocalAtTarget.restrict ‹Surjective p› V
  have hff := (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (p ∣_ V)).mp
    ⟨inferInstance, inferInstance⟩
  rw [morphismRestrict_appTop] at hff
  have hff' := (RingHom.FaithfullyFlat.respectsIso.cancel_right_isIso
    (p.app (V.ι ''ᵁ ⊤)) (X.presheaf.map (eqToHom (image_morphismRestrict_preimage p V ⊤)).op)).mp hff
  rwa [Scheme.Opens.ι_image_top] at hff'

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAppOfIsAffineHomFlatSurjectiveStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.GlobalTheory.T.faithfullyFlat_app_of_isAffineHom_flat_surjective' : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (V : Y.Opens), IsAffineHom p → Flat p → Surjective p → IsAffineOpen V → (p.app V).hom.FaithfullyFlat := by
  first | exact @GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective | exact GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective | (intros; apply GlobalTheory.faithfullyFlat_app_of_isAffineHom_flat_surjective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyTrivialUnitCocycleFaithfullyFlat

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory

namespace UnitCocycle

section Tensor

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]


variable (R B) in
noncomputable def m₁₂ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id R B) Algebra.TensorProduct.includeLeft


variable (R B) in
noncomputable def m₁₃ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.map (AlgHom.id R B) Algebra.TensorProduct.includeRight


variable (R B) in
noncomputable def m₂₃ : B ⊗[R] B →ₐ[R] B ⊗[R] (B ⊗[R] B) :=
  Algebra.TensorProduct.includeRight

noncomputable def datum (c : B ⊗[R] B) : B →ₗ[B] B ⊗[R] B :=
  LinearMap.toSpanSingleton B _ c

theorem datum_apply (c : B ⊗[R] B) (x : B) : datum c x = c * (x ⊗ₜ[R] (1 : B)) := by
  rw [datum, LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_comm]
  rfl

theorem lmul'_eq_one {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) : Algebra.TensorProduct.lmul' R c = (1 : B) := by
  let μ : B ⊗[R] B →ₐ[R] B := Algebra.TensorProduct.lmul' R
  let ν : B ⊗[R] (B ⊗[R] B) →ₐ[R] B :=
    μ.comp (Algebra.TensorProduct.map (AlgHom.id R B) μ)
  have h12 : ν.comp (m₁₂ R B) = μ := by ext <;> simp [ν, μ, m₁₂, Algebra.TensorProduct.one_def]
  have h13 : ν.comp (m₁₃ R B) = μ := by ext <;> simp [ν, μ, m₁₃, Algebra.TensorProduct.one_def]
  have h23 : ν.comp (m₂₃ R B) = μ := by ext <;> simp [ν, μ, m₂₃, Algebra.TensorProduct.one_def]
  have h' := congrArg ν h
  rw [map_mul, ← AlgHom.comp_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, h12, h13, h23] at h'
  exact (hu.map μ).mul_left_cancel (by rw [mul_one]; exact h'.symm)

theorem isDescentDatum {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) : GlobalTheory.FlatDescent.IsDescentDatum (datum c) := by
  have ha : ∀ z : B ⊗[R] B, GlobalTheory.FlatDescent.act (A := R) (B := B) (N := B) z = Algebra.TensorProduct.lmul' R z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul b m => simp
  have h1 : ∀ z : B ⊗[R] B,
      ((datum c).restrictScalars R).lTensor B z = m₁₂ R B z * m₂₃ R B c := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_mul]
    | tmul b m => simp [datum_apply, m₁₂, m₂₃, mul_comm]
  have h2 : ∀ z : B ⊗[R] B, (TensorProduct.mk R B B 1).lTensor B z = m₁₃ R B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul b m => simp [m₁₃]
  constructor
  · intro n
    rw [ha, datum_apply, map_mul, lmul'_eq_one hu h]
    simp
  · intro n
    rw [h1, h2, datum_apply, map_mul, map_mul, h, mul_right_comm]
    congr 1

theorem exists_local_tensor [Module.FaithfullyFlat R B] {c : B ⊗[R] B} (hu : IsUnit c)
    (h : m₁₃ R B c = m₁₂ R B c * m₂₃ R B c) (P : Ideal R) (hP : P ≠ ⊤) :
    ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = algebraMap R B s ∧
      (1 : B) ⊗ₜ[R] x = c * (x ⊗ₜ[R] (1 : B)) := by
  have hd := isDescentDatum hu h
  have hI := hd.invertible_invariants
  let I := GlobalTheory.FlatDescent.invariants (datum c)
  obtain ⟨φ, m, hm⟩ : ∃ (φ : Module.Dual R I) (m : I), φ m ∉ P := by
    by_contra hcon
    push_neg at hcon
    apply hP
    rw [Ideal.eq_top_iff_one]
    obtain ⟨z, hz⟩ := hI.bijective.2 1
    rw [← hz]
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _)]; exact P.add_mem hx hy
    | tmul b m => simpa using hcon b m
  let e := LinearEquiv.ofBijective _ hd.bijective_extend
  let Φ : B →ₗ[B] B :=
    (AlgebraTensorModule.rid R B B).toLinearMap ∘ₗ LinearMap.baseChange B φ ∘ₗ e.symm.toLinearMap
  have h1 : e.symm (m : B) = 1 ⊗ₜ m := by
    rw [LinearEquiv.symm_apply_eq]
    simp [e]
  refine ⟨φ m, hm, m, Φ 1, ?_, ?_⟩
  · rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
    simp [Φ, h1, Algebra.algebraMap_eq_smul_one]
  · rw [← datum_apply]
    exact (GlobalTheory.FlatDescent.mem_invariants.1 m.2).symm

end Tensor

theorem exists_local (R B C D : CommRingCat.{0}) (f : R ⟶ B) (j₁ j₂ : B ⟶ C) (d₁₂ d₂₃ d₁₃ : C ⟶ D)
    (hC : IsPushout f f j₁ j₂) (hD : IsPushout j₂ j₁ d₁₂ d₂₃) (h₁ : j₁ ≫ d₁₃ = j₁ ≫ d₁₂)
    (h₂ : j₂ ≫ d₁₃ = j₂ ≫ d₂₃) (hf : f.hom.FaithfullyFlat) (c : Cˣ)
    (hc : d₁₃.hom (c : C) = d₁₂.hom (c : C) * d₂₃.hom (c : C)) (P : Ideal R) (hP : P.IsPrime) :
    ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = f.hom s ∧ j₂.hom x = (c : C) * j₁.hom x := by
  letI : Algebra R B := f.hom.toAlgebra
  haveI : Module.FaithfullyFlat R B := hf
  have hT := CommRingCat.isPushout_tensorProduct R B B
  let e : C ≅ CommRingCat.of (B ⊗[R] B) := hC.isoIsPushout _ _ hT
  have e1 : j₁ ≫ e.hom = _ := hC.inl_isoIsPushout_hom _ _ hT
  have e2 : j₂ ≫ e.hom = _ := hC.inr_isoIsPushout_hom _ _ hT
  have e1' : ∀ x : B, e.hom.hom (j₁.hom x) = x ⊗ₜ[R] (1 : B) := fun x =>
    congrArg (fun q => q.hom x) e1
  have e2' : ∀ x : B, e.hom.hom (j₂.hom x) = (1 : B) ⊗ₜ[R] x := fun x =>
    congrArg (fun q => q.hom x) e2
  let n₁₂ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₁₂ R B).toRingHom
  let n₁₃ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₁₃ R B).toRingHom
  let n₂₃ : C ⟶ CommRingCat.of (B ⊗[R] (B ⊗[R] B)) := e.hom ≫ CommRingCat.ofHom (m₂₃ R B).toRingHom
  have w : j₂ ≫ n₁₂ = j₁ ≫ n₂₃ := by
    ext x
    change m₁₂ R B (e.hom.hom (j₂.hom x)) = m₂₃ R B (e.hom.hom (j₁.hom x))
    rw [e1', e2']
    simp [m₁₂, m₂₃]
  let ψ := hD.desc n₁₂ n₂₃ w
  have p12 : d₁₂ ≫ ψ = n₁₂ := hD.inl_desc _ _ _
  have p23 : d₂₃ ≫ ψ = n₂₃ := hD.inr_desc _ _ _
  have p13 : d₁₃ ≫ ψ = n₁₃ := by
    apply hC.hom_ext
    · rw [← Category.assoc, h₁, Category.assoc, p12]
      ext x
      change m₁₂ R B (e.hom.hom (j₁.hom x)) = m₁₃ R B (e.hom.hom (j₁.hom x))
      rw [e1']
      simp [m₁₂, m₁₃, Algebra.TensorProduct.one_def]
    · rw [← Category.assoc, h₂, Category.assoc, p23]
      ext x
      change m₂₃ R B (e.hom.hom (j₂.hom x)) = m₁₃ R B (e.hom.hom (j₂.hom x))
      rw [e2']
      simp [m₂₃, m₁₃]
  have hco : m₁₃ R B (e.hom.hom c) = m₁₂ R B (e.hom.hom c) * m₂₃ R B (e.hom.hom c) := by
    have h' := congrArg ψ.hom hc
    rw [map_mul] at h'
    have q12 : ψ.hom (d₁₂.hom c) = m₁₂ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p12
    have q13 : ψ.hom (d₁₃.hom c) = m₁₃ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p13
    have q23 : ψ.hom (d₂₃.hom c) = m₂₃ R B (e.hom.hom c) := congrArg (fun q => q.hom (c : C)) p23
    rwa [q12, q13, q23] at h'
  obtain ⟨s, hs, x, y, hxy, hx⟩ :=
    exists_local_tensor (c.isUnit.map e.hom.hom) hco P hP.ne_top
  refine ⟨s, hs, x, y, hxy, ?_⟩
  apply e.commRingCatIsoToRingEquiv.injective
  change e.hom.hom _ = e.hom.hom _
  rw [map_mul, e1', e2']
  exact hx

end UnitCocycle

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyTrivialUnitCocycleFaithfullyFlatStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits

theorem _root_.GlobalTheory.T.locally_trivial_unit_cocycle_faithfully_flat : ∀ (R B C D : CommRingCat.{0}) (f : R ⟶ B) (j₁ j₂ : B ⟶ C) (d₁₂ d₂₃ d₁₃ : C ⟶ D), IsPushout f f j₁ j₂ → IsPushout j₂ j₁ d₁₂ d₂₃ → j₁ ≫ d₁₃ = j₁ ≫ d₁₂ → j₂ ≫ d₁₃ = j₂ ≫ d₂₃ → f.hom.FaithfullyFlat → ∀ c : Cˣ, d₁₃.hom (c : C) = d₁₂.hom (c : C) * d₂₃.hom (c : C) → ∀ P : Ideal R, P.IsPrime → ∃ s : R, s ∉ P ∧ ∃ x y : B, x * y = f.hom s ∧ j₂.hom x = (c : C) * j₁.hom x := by
  first | exact @GlobalTheory.UnitCocycle.exists_local | exact GlobalTheory.UnitCocycle.exists_local | (intros; apply GlobalTheory.UnitCocycle.exists_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyTrivialUnitCocycleScheme

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CharKer

theorem appLE_eq_of_eq' {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

theorem app_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.app U).hom x) = (f.appLE U V h).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]

theorem appLE_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V V' : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ V) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((f.appLE U V h).hom x) = (f.appLE U V' (h'.trans h)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

theorem map_app_map_eq_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} (hU : U' ≤ U)
    (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U') (h' : V ≤ f ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.app U').hom ((Y.presheaf.map (homOfLE hU).op).hom x)) =
      (f.appLE U V h').hom x := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
    ← Category.assoc, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem appLE_map_top {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
    (x : Γ(Y, ⊤)) :
    (f.appLE U V e).hom ((Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom x) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (f.appTop.hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 2
  simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
  rw [Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  rfl

theorem map_map_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U)
    (x : Γ(X, U)) : (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom x) =
      (X.presheaf.map (homOfLE h₃).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.CharKer

namespace GlobalTheory.CharKer

theorem exists_local_charUnit : ∀ (X Y Z W : Scheme.{0}) (p : X ⟶ Y) (a b : Z ⟶ X) (m₁₂ m₂₃ m₁₃ : W ⟶ Z) (χ : Γ(Z, ⊤)ˣ), IsAffineHom p → Flat p → Surjective p → IsPullback b a p p → IsPullback m₁₂ m₂₃ a b → m₁₃ ≫ b = m₁₂ ≫ b → m₁₃ ≫ a = m₂₃ ≫ a → pullTop m₁₃ χ = pullTop m₁₂ χ * pullTop m₂₃ χ → ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ e : Γ(X, p ⁻¹ᵁ V)ˣ, ∀ (W' : Z.Opens) (h₁ : W' ≤ a ⁻¹ᵁ (p ⁻¹ᵁ V)) (h₂ : W' ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V)), res h₁ (pullU a _ e) = res le_top χ * res h₂ (pullU b _ e) := by
  intro X Y Z W p a b m₁₂ m₂₃ m₁₃ χ hpA hpF hpS sq₁ sq₂ e₁₃b e₁₃a hχ y
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  have ha : IsAffineHom a := MorphismProperty.of_isPullback (P := @IsAffineHom) sq₁ hpA
  have hab : a ⁻¹ᵁ (p ⁻¹ᵁ V) = b ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq₁.w]
  have h12 : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ m₁₂ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage m₁₂ a, sq₂.w, Scheme.Hom.comp_preimage, ← hab]
  have h13 : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ m₁₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := by
    rw [← Scheme.Hom.comp_preimage m₁₃ a, e₁₃a, Scheme.Hom.comp_preimage]
  have hV₀ : IsAffineOpen (p ⁻¹ᵁ V) := hV.preimage p
  have hV₁ : IsAffineOpen (a ⁻¹ᵁ (p ⁻¹ᵁ V)) := hV₀.preimage a
  have P₁ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq₁ hpA hV hV₀ le_rfl hab.le
  rw [Scheme.Hom.appLE_eq_app] at P₁
  have P₂ := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq₂ ha hV₀ hV₁ hab.le h12
  have E₁ : b.appLE (p ⁻¹ᵁ V) (a ⁻¹ᵁ (p ⁻¹ᵁ V)) hab.le ≫ m₁₃.appLE _ _ h13 =
      b.appLE (p ⁻¹ᵁ V) (a ⁻¹ᵁ (p ⁻¹ᵁ V)) hab.le ≫ m₁₂.appLE _ _ h12 := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq' e₁₃b _ _ _ _
  have E₂ : a.app (p ⁻¹ᵁ V) ≫ m₁₃.appLE _ _ h13 = a.app (p ⁻¹ᵁ V) ≫ m₂₃.app _ := by
    rw [Scheme.Hom.app_eq_appLE a, Scheme.Hom.app_eq_appLE m₂₃, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    exact appLE_eq_of_eq' e₁₃a _ _ _ _
  have FF := GlobalTheory.T.faithfullyFlat_app_of_isAffineHom_flat_surjective' X Y p V hpA hpF hpS hV
  let c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))ˣ := res le_top χ
  have hc : (m₁₃.appLE _ _ h13).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) =
      (m₁₂.appLE _ _ h12).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) * (m₂₃.app _).hom (c : Γ(Z, a ⁻¹ᵁ (p ⁻¹ᵁ V))) := by
    have := congrArg (fun u => ((res (le_top : m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V)) ≤ ⊤) u : Γ(W, _)ˣ) :
      Γ(W, m₂₃ ⁻¹ᵁ (a ⁻¹ᵁ (p ⁻¹ᵁ V))))) hχ
    simp only [map_mul, Units.val_mul, res, pullTop, Units.coe_map, MonoidHom.coe_coe] at this
    rw [Scheme.Hom.app_eq_appLE m₂₃]
    simp only [c, res, Units.coe_map, MonoidHom.coe_coe]
    rw [appLE_map_top, appLE_map_top, appLE_map_top]
    exact this
  obtain ⟨s, hs, x, x', hxx', hx⟩ := GlobalTheory.T.locally_trivial_unit_cocycle_faithfully_flat _ _ _ _ (p.app V) _ _ _ _ _ P₁ P₂ E₁ E₂ FF c hc
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal inferInstance
  have hyS : y ∈ Y.basicOpen s := by
    have h0 : hV.primeIdealOf ⟨y, hyV⟩ ∈ hV.fromSpec ⁻¹ᵁ Y.basicOpen s := by
      rw [hV.fromSpec_preimage_basicOpen]; exact hs
    have h1 := hV.fromSpec_primeIdealOf ⟨y, hyV⟩
    have h0' : hV.fromSpec (hV.primeIdealOf ⟨y, hyV⟩) ∈ Y.basicOpen s := h0
    rwa [h1] at h0'
  refine ⟨Y.basicOpen s, hyS, ?_⟩
  have hle : p ⁻¹ᵁ Y.basicOpen s ≤ p ⁻¹ᵁ V := fun z hz => Y.basicOpen_le s hz
  have hpre := Scheme.preimage_basicOpen p s
  have hu : IsUnit ((X.presheaf.map (homOfLE hle).op).hom x) := by
    apply isUnit_of_mul_isUnit_left (y := (X.presheaf.map (homOfLE hle).op).hom x')
    rw [← map_mul, hxx']
    have h2 := RingedSpace.isUnit_res_basicOpen X.toRingedSpace ((p.app V).hom s)
    have h3 := h2.map (X.presheaf.map (homOfLE hpre.le).op).hom
    rw [← map_map_apply (X.basicOpen_le ((p.app V).hom s)) hpre.le hle]
    exact h3
  refine ⟨hu.unit, fun W' h₁ h₂ => ?_⟩
  have hW : W' ≤ a ⁻¹ᵁ (p ⁻¹ᵁ V) := fun z hz => hle (h₁ hz)
  have hWb : W' ≤ b ⁻¹ᵁ (p ⁻¹ᵁ V) := hW.trans hab.le
  apply Units.ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, IsUnit.unit_spec, Units.val_mul]
  rw [map_app_map_eq_appLE a hle W' h₁ hW, map_app_map_eq_appLE b hle W' h₂ hWb]
  have := congrArg (Z.presheaf.map (homOfLE hW).op).hom hx
  rw [map_mul, app_map_eq_appLE, appLE_map_eq_appLE] at this
  rw [this]
  congr 1
  simp only [c, res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.CharKer
end
end
end
