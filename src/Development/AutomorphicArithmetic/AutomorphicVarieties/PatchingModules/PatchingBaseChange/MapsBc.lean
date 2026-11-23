module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SinfRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ExistsFiniteSpanningTaylorWilesTensor
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Lift
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SpFin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilSp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilMod

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ExistsSemilinearEquivBaseChangeTensor

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.exists_semilinear_equiv_baseChange_tensor :
    ∀ (B P B' P₁ P' : Type) [CommRing B] [CommRing P] [CommRing B'] [CommRing P₁] [CommRing P'] [Algebra B P] [Algebra B B'] [Algebra P P₁] [Algebra B' P'] (τ : P₁ ≃+* P') (M M' : Type) [AddCommGroup M] [Module B M] [AddCommGroup M'] [Module B' M'] (_μ : B' ⊗[B] M ≃ₗ[B'] M'), (∀ b, τ (algebraMap P P₁ (algebraMap B P b)) = algebraMap B' P' (algebraMap B B' b)) → ∃ e : P₁ ⊗[P] (P ⊗[B] M) ≃+ P' ⊗[B'] M', ∀ z w, e (z • w) = τ z • e w := by
  intro B P B' P₁ P' _ _ _ _ _ _ _ _ _ τ M M' _ _ _ _ μ h
  letI : Algebra P₁ P' := τ.toRingHom.toAlgebra
  letI : Algebra P P' := (τ.toRingHom.comp (algebraMap P P₁)).toAlgebra
  letI : Algebra B P' := ((algebraMap B' P').comp (algebraMap B B')).toAlgebra
  haveI : IsScalarTower P P₁ P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B B' P' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower B P P' := IsScalarTower.of_algebraMap_eq (fun b => (h b).symm)
  let t : P₁ ≃ₗ[P₁] P' :=
    { τ.toAddEquiv with
      map_smul' := fun a b => by
        show τ (a * b) = τ a * τ b
        exact map_mul τ a b }
  let e1 : P₁ ⊗[P] (P ⊗[B] M) ≃ₗ[P₁] P' ⊗[P] (P ⊗[B] M) :=
    TensorProduct.AlgebraTensorModule.congr t (LinearEquiv.refl P _)
  let e2 : P' ⊗[P] (P ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B P P' P' M
  let e3 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B B' P' P' M
  let e4 : P' ⊗[B'] (B' ⊗[B] M) ≃ₗ[P'] P' ⊗[B'] M' :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl P' P') μ
  let f := e2.trans (e3.symm.trans e4)
  refine ⟨e1.toAddEquiv.trans f.toAddEquiv, fun z w => ?_⟩
  show f (e1 (z • w)) = τ z • f (e1 w)
  rw [map_smul, ← map_smul f]
  rfl
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.QuotBc

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.quot_bc :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) (I' : Ideal R'), I' = I.map (algebraMap R R') → Nonempty (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)) ≃ₗ[R'] (R' ⊗[R] M) ⧸ (I' • ⊤ : Submodule R' (R' ⊗[R] M))) := by
  intro R R' _ _ _ M _ _ I I' hI
  subst hI
  have hker : ∀ i ∈ I, ∀ y : R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M)), i • y = 0 := by
    intro i hi y
    induction y using TensorProduct.induction_on with
    | zero => exact smul_zero _
    | tmul a q =>
      induction q using Submodule.Quotient.induction_on with
      | H m =>
        rw [← TensorProduct.tmul_smul, ← Submodule.Quotient.mk_smul,
          (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hi Submodule.mem_top),
          TensorProduct.tmul_zero]
    | add y z hy hz => rw [smul_add, hy, hz, add_zero]
  have hann : I.map (algebraMap R R') ≤ Module.annihilator R' (R' ⊗[R] (M ⧸ (I • ⊤ : Submodule R M))) :=
    Ideal.map_le_iff_le_comap.2 fun i hi => Module.mem_annihilator.2 fun y => by
      rw [algebraMap_smul]
      exact hker i hi y
  let ψ : M ⧸ (I • ⊤ : Submodule R M) →ₗ[R]
      (R' ⊗[R] M) ⧸ (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)) :=
    (I • ⊤ : Submodule R M).liftQ
      (((I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).mkQ.restrictScalars R) ∘ₗ
        TensorProduct.mk R R' M 1) (by
      rw [Submodule.smul_le]
      intro i hi m _
      rw [LinearMap.mem_ker, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, TensorProduct.tmul_smul,
        ← algebraMap_smul R' i ((1 : R') ⊗ₜ[R] m)]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hi) Submodule.mem_top)
  let φ := ψ.liftBaseChange R'
  let χ := (I.map (algebraMap R R') • ⊤ : Submodule R' (R' ⊗[R] M)).liftQ
    (LinearMap.baseChange R' (I • ⊤ : Submodule R M).mkQ) (by
      rw [Submodule.smul_le]
      intro r hr x _
      rw [LinearMap.mem_ker, map_smul]
      exact Module.mem_annihilator.1 (hann hr) _)
  refine ⟨LinearEquiv.ofLinear φ χ ?_ ?_⟩
  · apply Submodule.linearMap_qext
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    simp [φ, χ, ψ]
    rw [← Submodule.Quotient.mk_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · apply TensorProduct.AlgebraTensorModule.ext
    intro a q
    induction q using Submodule.Quotient.induction_on with
    | H m => simp [φ, χ, ψ, TensorProduct.smul_tmul']
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.XmapsBc

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.xmaps_bc :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (R P : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] [CommRing P] [Algebra O P] [IsNoetherianRing P] (θ : R →ₐ[O] P) (X X0 : Type) [AddCommGroup X] [Module R X] [AddCommGroup X0] [Module P X0] (f : R) (φ : X0 →+ X) (ψ : X →+ X0), (∃ s : Finset X0, ∀ z, ∃ c : X0 → R, z = ∑ g ∈ s, θ (c g) • g) → (∀ (t : R) z, φ (θ t • z) = t • φ z) → (∀ (t : R) z, ψ (t • z) = θ t • ψ z) → (∀ z, φ (ψ z) = f • z) → (∀ z, ψ (φ z) = θ f • z) → ∃ (φ' : Til O O' P ⊗[P] X0 →+ Til O O' R ⊗[R] X) (ψ' : Til O O' R ⊗[R] X →+ Til O O' P ⊗[P] X0), (∀ t z, φ' (Til.map O' θ t • z) = t • φ' z) ∧ (∀ t z, ψ' (t • z) = Til.map O' θ t • ψ' z) ∧ (∀ z, φ' (ψ' z) = Til.ι O O' R f • z) ∧ ∀ z, ψ' (φ' z) = Til.map O' θ (Til.ι O O' R f) • z := by
  intro O O' _ _ _ _ R P _ _ _ _ _ _ θ X X0 _ _ _ _ f φ ψ hgen hφ hψ hφψ hψφ
  letI : Module R X0 := Module.compHom X0 θ.toRingHom
  haveI : Module.Finite R X0 := by
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hgen
    refine ⟨s, ?_⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨c, hc⟩ := hs z
    rw [hc]
    refine Submodule.sum_mem _ (fun g hg => ?_)
    exact Submodule.smul_mem _ (c g) (Submodule.subset_span hg)
  obtain ⟨e, he1, he2⟩ := BC.til_mod O O' R P θ X0 (fun a m => rfl)
  let φL : X0 →ₗ[R] X :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun t z => hφ t z }
  let ψL : X →ₗ[R] X0 :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := fun t z => hψ t z }
  let A := Til O O' R
  let Φ := LinearMap.baseChange A φL
  let Ψ := LinearMap.baseChange A ψL
  have hsc : ∀ (M : Type) [AddCommGroup M] [Module R M] (g : M →ₗ[R] M) (r : R), (∀ m, g m = r • m) →
      ∀ w : A ⊗[R] M, LinearMap.baseChange A g w = Til.ι O O' R r • w := by
    intro M _ _ g r hg w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, hg, ← Til.algebraMap_eq, ← TensorProduct.smul_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
    | add x y hx hy => rw [map_add (f := _), hx, hy, smul_add]
  have heinv : ∀ (t : A) (z : Til O O' P ⊗[P] X0), e.symm (Til.map O' θ t • z) = t • e.symm z := by
    intro t z
    apply e.injective
    rw [he2, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  refine ⟨Φ.toAddMonoidHom.comp e.symm.toAddMonoidHom, e.toAddMonoidHom.comp Ψ.toAddMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro t z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [heinv, LinearMap.map_smul]
  · intro t z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [LinearMap.map_smul, he2]
  · intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe, AddEquiv.symm_apply_apply]
    have := hsc X (φL ∘ₗ ψL) f (fun m => hφψ m) z
    rw [LinearMap.baseChange_comp] at this
    exact this
  · intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    have := hsc X0 (ψL ∘ₗ φL) f (fun m => hψφ m) (e.symm z)
    rw [LinearMap.baseChange_comp] at this
    change e (Ψ (Φ (e.symm z))) = _
    rw [show Ψ (Φ (e.symm z)) = Til.ι O O' R f • e.symm z from this, he2, AddEquiv.apply_symm_apply]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.MapsBc

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem mb_comp {O O' R R' R'' : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] [CommRing R''] [Algebra O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (a : Til O O' R) :
    Til.map O' (g.comp f) a = Til.map O' g (Til.map O' f a) := by
  refine PowerSeries.ext fun k => ?_
  show Algebra.TensorProduct.map _ _ (Til.coeff O O' R k a) =
    Algebra.TensorProduct.map _ _ (Algebra.TensorProduct.map _ _ (Til.coeff O O' R k a))
  induction Til.coeff O O' R k a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem mb_sp (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O']
    (B : Type) [CommRing B] [Algebra O B] (q n : ℕ) (P : Fin q → Polynomial B) (ut : Fin q → Fin n → B)
    (P' : Fin q → Polynomial (Til O O' B)) (ut' : Fin q → Fin n → Til O O' B)
    (hP : P' = fun j => (P j).map (Til.ι O O' B)) (hu : ut' = fun j i => Til.ι O O' B (ut j i)) :
    ∃ τ : Til O O' (Sp P ut) ≃ₐ[O'] Sp P' ut',
      (∀ a, τ (Til.map O' (IsScalarTower.toAlgHom O B (Sp P ut)) a) = algebraMap (Til O O' B) _ a) ∧
      ∀ j i, τ (Til.ι O O' _ (Sp.u P ut j i)) = Sp.u _ _ j i := by
  subst hP hu
  exact UpperTheory.V.Pa.BC.til_sp O O' B q n P ut

private theorem mb_quot {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
    [Module R' M'] (ρ : R ≃+* R') (ν : M ≃+ M') (hν : ∀ (t : R) m, ν (t • m) = ρ t • ν m) (I : Ideal R) (I' : Ideal R')
    (hI : I' = I.map (ρ : R →+* R')) :
    ∃ e : (M ⧸ (I • ⊤ : Submodule R M)) ≃+ (M' ⧸ (I' • ⊤ : Submodule R' M')), ∀ (t : R) m, e (t • m) = ρ t • e m := by
  have he : (I • ⊤ : Submodule R M).toAddSubgroup.map (ν : M →+ M') = (I' • ⊤ : Submodule R' M').toAddSubgroup := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      show ν x ∈ (I' • ⊤ : Submodule R' M')
      refine Submodule.smul_induction_on (p := fun x => ν x ∈ (I' • ⊤ : Submodule R' M')) hx (fun a ha m _ => ?_)
        (fun x y hx hy => ?_)
      · rw [hν]
        exact Submodule.smul_mem_smul (hI ▸ Ideal.mem_map_of_mem _ ha) trivial
      · rw [map_add (f := _)]
        exact Submodule.add_mem _ hx hy
    · intro y hy
      refine Submodule.smul_induction_on
        (p := fun y => y ∈ (I • ⊤ : Submodule R M).toAddSubgroup.map (ν : M →+ M')) hy (fun a ha m _ => ?_)
        (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
      rw [hI] at ha
      obtain ⟨c, hc, rfl⟩ := (Ideal.mem_map_iff_of_surjective (ρ : R →+* R') ρ.surjective).1 ha
      refine ⟨c • ν.symm m, Submodule.smul_mem_smul hc trivial, ?_⟩
      show ν _ = ρ c • m
      rw [hν, ν.apply_symm_apply]
  refine ⟨QuotientAddGroup.congr _ _ ν he, fun t m => ?_⟩
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  show (Submodule.Quotient.mk (ν (t • m)) : M' ⧸ (I' • ⊤ : Submodule R' M')) = ρ t • Submodule.Quotient.mk (ν m)
  rw [hν, Submodule.Quotient.mk_smul]

private theorem mb_kill {R T R' M M' : Type} [CommRing R] [CommRing T] [Algebra R T] [CommRing R'] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R' M'] (ρ : T → R') (ν : T ⊗[R] M ≃+ M')
    (hν : ∀ (t : T) m, ν (t • m) = ρ t • ν m) (x : R) (hx : ∀ m : M, x • m = 0) (m : M') :
    ρ (algebraMap R T x) • m = 0 := by
  obtain ⟨w, rfl⟩ := ν.surjective m
  rw [← hν, algebraMap_smul, map_eq_zero_iff ν ν.injective]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => rw [← TensorProduct.tmul_smul, hx, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

private theorem mb_fEl {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {q n : ℕ} (Nq : Fin q → ℕ)
    (U : Fin q → Fin n → R) : fEl Nq (fun j i => f (U j i)) = f (fEl Nq U) := by
  simp [fEl, map_prod]

private theorem map_quadratic_element_one {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (f : R →+* R') {n : ℕ} (ph : G)
    (U : Fin n → R) : q1El ph (fun i => f (U i)) = MonoidAlgebra.mapRingHom G f (q1El ph U) := by
  rw [q1El, q1El, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  simp

private theorem map_quadratic_element_two {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (f : R →+* R') {n : ℕ} (ph ta : G)
    (U : Fin n → R) (i : Fin n) (y : R) :
    q2El ph ta (fun i => f (U i)) i (f y) = MonoidAlgebra.mapRingHom G f (q2El ph ta U i y) := by
  rw [q2El, q2El, map_mul, map_list_prod, List.map_ofFn]
  congr 1
  · congr 2
    funext k
    by_cases h : k = i <;> simp [h]
  · simp

private theorem mb_tr {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (f : R →+* R') {n : ℕ} (D : GDet n R G)
    (g : G) (y : MonoidAlgebra R G) :
    (D.map f).tr (MonoidAlgebra.single g 1 * MonoidAlgebra.mapRingHom G f y) = f (D.tr (MonoidAlgebra.single g 1 * y)) := by
  rw [GDet.tr, GDet.tr, ← ((UpperTheory.V.CA.d_gmap D).2.2.1 f _).2 1, map_mul, MonoidAlgebra.mapRingHom_single, map_one]

private theorem mb_move {T P R' P' X X0 X' X0' : Type} [CommRing T] [CommRing P] [CommRing R'] [CommRing P']
    [AddCommGroup X] [Module T X] [AddCommGroup X0] [Module P X0] [AddCommGroup X'] [Module R' X'] [AddCommGroup X0']
    [Module P' X0'] (ρ : T ≃+* R') (τ : P → P') (θ : T → P) (θ' : R' → P') (hθ : ∀ t, θ' (ρ t) = τ (θ t))
    (e : X ≃+ X') (he : ∀ (t : T) z, e (t • z) = ρ t • e z) (e0 : X0 ≃+ X0') (he0 : ∀ (t : P) z, e0 (t • z) = τ t • e0 z)
    (f : T) (φ : X0 →+ X) (ψ : X →+ X0) (h1 : ∀ t z, φ (θ t • z) = t • φ z) (h2 : ∀ (t : T) z, ψ (t • z) = θ t • ψ z)
    (h3 : ∀ z, φ (ψ z) = f • z) (h4 : ∀ z, ψ (φ z) = θ f • z) :
    ∃ (φ' : X0' →+ X') (ψ' : X' →+ X0'), (∀ t z, φ' (θ' t • z) = t • φ' z) ∧ (∀ (t : R') z, ψ' (t • z) = θ' t • ψ' z) ∧
      (∀ z, φ' (ψ' z) = ρ f • z) ∧ ∀ z, ψ' (φ' z) = θ' (ρ f) • z := by
  refine ⟨e.toAddMonoidHom.comp (φ.comp e0.symm.toAddMonoidHom), e0.toAddMonoidHom.comp (ψ.comp e.symm.toAddMonoidHom),
    fun t z => ?_, fun t z => ?_, fun z => ?_, fun z => ?_⟩
  · obtain ⟨t, rfl⟩ := ρ.surjective t
    obtain ⟨z, rfl⟩ := e0.surjective z
    show e (φ (e0.symm _)) = _ • e (φ (e0.symm _))
    rw [hθ, ← he0, e0.symm_apply_apply, e0.symm_apply_apply, h1, he]
  · obtain ⟨t, rfl⟩ := ρ.surjective t
    obtain ⟨z, rfl⟩ := e.surjective z
    show e0 (ψ (e.symm _)) = _ • e0 (ψ (e.symm _))
    rw [hθ, ← he, e.symm_apply_apply, e.symm_apply_apply, h2, he0]
  · obtain ⟨z, rfl⟩ := e.surjective z
    show e (φ (e0.symm (e0 (ψ (e.symm _))))) = _
    rw [e.symm_apply_apply, e0.symm_apply_apply, h3, he]
  · obtain ⟨z, rfl⟩ := e0.surjective z
    show e0 (ψ (e.symm (e (φ (e0.symm _))))) = _
    rw [e.symm_apply_apply, e0.symm_apply_apply, h4, he0, hθ]

private theorem mb_det {n : ℕ} {R R' P P' B B' G G0 : Type} [CommRing R] [CommRing R'] [CommRing P] [CommRing P']
    [CommRing B] [CommRing B'] [Group G] [Group G0] (p : G →* G0) (D : GDet n R G) (D' : GDet n R' G) (E : GDet n B G0)
    (E' : GDet n B' G0) (κ : R →+* R') (i : B →+* B') (θ : R →+* P) (θ' : R' →+* P') (a : B →+* P) (a' : B' →+* P')
    (lp : P →+* P') (h1 : θ'.comp κ = lp.comp θ) (h2 : lp.comp a = a'.comp i) (hD : D' = D.map κ) (hE : E.map i = E')
    (h : D.map θ = (E.comap p).map a) : D'.map θ' = (E'.comap p).map a' := by
  rw [hD, (UpperTheory.V.CA.d_gmap D).2.1, h1, ← (UpperTheory.V.CA.d_gmap D).2.1, h, (UpperTheory.V.CA.d_gmap _).2.1, h2,
    ← (UpperTheory.V.CA.d_gmap _).2.1, ← hE]
  rfl

theorem UpperTheory.V.Pa.BC.maps_bc :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (O O' : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [CommRing O'] [IsLocalRing O'] [Algebra ℤ_[l] O'] [Algebra O O'] [IsScalarTower ℤ_[l] O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] [Module.Free O O'] (r : Resid G0.frame O n) (r' : Resid G0.frame O' n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsCO O' (Til O O' B)] (u : Pair r B) (u' : Pair r' (Til O O' B)) (J : Ideal B) (D : ℕ) (b : TWBase u J Empty D) (b' : TWBase u' (J.map (Til.ι O O' B)) Unit D) (τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D) (G : Glob l L) (h : G.Hom G0) (q : ℕ) (ut : Fin q → Fin n → O) (N : ℕ) (τS : Til O O' (Sinf O Empty D q n) ≃ₐ[O'] Sinf O' Unit D q n) (A : TWRing b h ut N) (A' : TWRing b' h (fun j i => algebraMap O O' (ut j i)) N) (Nq : Fin q → ℕ) (ph ta : Fin q → G.G₀) (ex : ℕ) (_m : TWMaps Nq ph ta A ex), RBC r r' → u.Maps (Til.ι O O' B) u'.D u'.ψ → Nonempty (BaseRel b b' τ) → SinfRel l τ τS → Nonempty (RingRel A A' τS) → Nonempty (TWMaps Nq ph ta A' ex) := by
  intro l _ L G0 n O O' _ _ _ _ _ _ _ _ _ _ _ _ _ r r' B _ _ _ _ u u' J D b b' τ G h q ut N τS A A' Nq ph ta ex m
    _ hu ⟨hb⟩ hS ⟨hA⟩
  obtain ⟨τp, hp1, hp2⟩ := mb_sp O O' B q n (fun j => u.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1))
    (fun j i => algebraMap O B (ut j i)) (fun j => u'.D.chi (MonoidAlgebra.single (h.p₀ (ph j)) 1))
    (fun j i => algebraMap O' (Til O O' B) (algebraMap O O' (ut j i)))
    (funext fun j => by
      rw [← hu.1, ← ((UpperTheory.V.CA.d_gmap u.D).2.2.1 _ _).1, MonoidAlgebra.mapRingHom_single, map_one])
    (funext fun j => funext fun i => (Til.ι_algebraMap O O' B (ut j i)).symm)
  haveI : IsNoetherianRing (SpAt u (fun j => h.p₀ (ph j)) ut) := (UpperTheory.V.Pa.BC.sp_fin B q n _ _).2
  let θ' : A'.R →ₐ[O'] SpAt u' (fun j => h.p₀ (ph j)) (fun j i => algebraMap O O' (ut j i)) :=
    (τp.toAlgHom.comp (Til.map O' m.θ)).comp hA.ρ.symm.toAlgHom
  have hθ : ∀ t, θ' (hA.ρ t) = τp (Til.map O' m.θ t) := fun t =>
    congrArg (fun x => τp (Til.map O' m.θ x)) (hA.ρ.symm_apply_apply t)
  have hB : ∀ x : B, τp (Til.ι O O' _ (algebraMap B (SpAt u (fun j => h.p₀ (ph j)) ut) x)) =
      algebraMap (Til O O' B) _ (Til.ι O O' B x) := fun x => by
    rw [← hp1, Til.map_ι]
    rfl
  let κ : A.R →+* A'.R := (hA.ρ.toRingEquiv : _ →+* A'.R).comp (Til.ι O O' A.R)
  have hκ : ∀ x, κ x = hA.ρ (Til.ι O O' A.R x) := fun _ => rfl
  let lp : SpAt u (fun j => h.p₀ (ph j)) ut →+* SpAt u' (fun j => h.p₀ (ph j)) (fun j i => algebraMap O O' (ut j i)) :=
    (τp.toRingEquiv : _ →+* _).comp (Til.ι O O' _)
  have hc1 : θ'.toRingHom.comp κ = lp.comp m.θ.toRingHom := RingHom.ext fun x => by
    show θ' (hA.ρ (Til.ι O O' A.R x)) = τp (Til.ι O O' _ (m.θ x))
    rw [hθ, Til.map_ι]
  have hc2 : lp.comp (algebraMap B _) = (algebraMap (Til O O' B) _).comp (Til.ι O O' B) := RingHom.ext hB
  have hX : ∀ p, A'.s (MvPowerSeries.X p) = κ (A.s (MvPowerSeries.X p)) := fun p => by
    rw [← hS.X, hA.s, Til.map_ι, hκ]
  have hU : A'.U = fun j i => κ (A.U j i) := funext fun j => funext fun i => hA.U j i
  have hf : fEl Nq A'.U = κ (fEl Nq A.U) := by rw [hU, mb_fEl]
  have hD : A'.p.D = A.p.D.map κ := hA.maps.1.symm
  have hkill : ∀ x : A.R, (∀ z : A.M, x • z = 0) → ∀ z : A'.M, κ x • z = 0 := fun x hx z =>
    mb_kill (fun t => hA.ρ t) hA.ν hA.ν_smul x hx z
  obtain ⟨φ1, ψ1, h1, h2, h3, h4⟩ := UpperTheory.V.Pa.BC.xmaps_bc O O' A.R _ m.θ A.X _ (fEl Nq A.U) m.φ m.ψ
    (UpperTheory.V.Pa.BC.exists_finite_spanning_taylorWiles_tensor l L G0 n O r B u J Empty D b G h q ut N A Nq ph ta ex m) m.φ_smul m.ψ_smul m.φψ m.ψφ
  obtain ⟨e0, he0⟩ := UpperTheory.V.Pa.BC.exists_semilinear_equiv_baseChange_tensor B (SpAt u (fun j => h.p₀ (ph j)) ut) (Til O O' B) (Til O O' _)
    (SpAt u' (fun j => h.p₀ (ph j)) (fun j i => algebraMap O O' (ut j i))) τp.toRingEquiv b.M b'.M hb.μ hB
  obtain ⟨e1⟩ := UpperTheory.V.Pa.BC.quot_bc A.R (Til O O' A.R) A.M
    (Ideal.span (Set.range fun p => A.s (MvPowerSeries.X p))) _ rfl
  obtain ⟨e2, he2⟩ := mb_quot hA.ρ.toRingEquiv hA.ν hA.ν_smul
    ((Ideal.span (Set.range fun p => A.s (MvPowerSeries.X p))).map (algebraMap A.R (Til O O' A.R)))
    (Ideal.span (Set.range fun p => A'.s (MvPowerSeries.X p))) (by
      rw [Ideal.map_map, Ideal.map_span, ← Set.range_comp]
      congr 2
      exact funext hX)
  obtain ⟨φ', ψ', k1, k2, k3, k4⟩ := mb_move hA.ρ.toRingEquiv (fun x => τp x) (fun t => Til.map O' m.θ t)
    (fun t => θ' t) hθ (e1.toAddEquiv.trans e2) (fun t z => by
      show e2 (e1 (t • z)) = _ • e2 (e1 z)
      rw [map_smul, he2]) e0 he0 (Til.ι O O' A.R (fEl Nq A.U)) φ1 ψ1 h1 h2 h3 h4
  refine ⟨⟨θ', ⟨?_, fun v i => ?_⟩, fun z => ?_, fun j i => ?_, φ', ψ', k1, k2, fun z => ?_, fun z => ?_,
    fun j g z => ?_, fun j i g z => ?_⟩⟩
  · exact mb_det h.p₀ A.p.D A'.p.D u.D u'.D κ (Til.ι O O' B) m.θ.toRingHom θ'.toRingHom _ _ lp hc1 hc2 hD hu.1 m.θ_pair.1
  · refine MonoidHom.ext fun g => Units.ext ?_
    have a1 : ((A'.p.ψ v i g : A'.Rˣ) : A'.R) = κ (A.p.ψ v i g) := by rw [← hA.maps.2 v i]; rfl
    have a2 : ((u'.ψ v i g : (Til O O' B)ˣ) : Til O O' B) = Til.ι O O' B (u.ψ v i g) := by rw [← hu.2 v i]; rfl
    have a3 : m.θ (A.p.ψ v i g) = algebraMap B _ ((u.ψ v i g : Bˣ) : B) :=
      congrArg (fun χ => ((χ g : _ˣ) : SpAt u (fun j => h.p₀ (ph j)) ut)) (m.θ_pair.2 v i)
    show θ' (A'.p.ψ v i g) = algebraMap (Til O O' B) _ ((u'.ψ v i g : (Til O O' B)ˣ) : Til O O' B)
    rw [a1, a2, hκ, hθ, Til.map_ι, a3, hB]
  · obtain ⟨z, rfl⟩ := τS.surjective z
    let c : Sinf O Empty D q n →ₐ[O] abelian₂ O Empty D :=
      { (MvPowerSeries.constantCoeff : Sinf O Empty D q n →+* abelian₂ O Empty D) with
        commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
    have hc : m.θ.comp A.s = (IsScalarTower.toAlgHom O B _).comp (b.lam.comp c) := AlgHom.ext m.theta_coefficientMap_eq
    rw [hA.s, hθ, hS.cc c (fun _ => rfl), hb.lam, ← hp1, ← mb_comp, hc, mb_comp, mb_comp]
  · rw [hA.U, hθ, Til.map_ι, m.θ_U, hp2]
  · rw [hf]
    exact k3 z
  · rw [hf]
    exact k4 z
  · rw [hf, hD, hU, map_quadratic_element_one, mb_tr, ← map_mul, ← map_pow]
    exact hkill _ (m.rel1 j g) z
  · rw [hf, hD, hX, hU, map_quadratic_element_two, mb_tr, ← map_mul, ← map_pow]
    exact hkill _ (m.rel2 j i g) z
end
end
