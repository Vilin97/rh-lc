module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOver
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Field
public import GroundTheory.Brauer.TensorSimple
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Mathlib.RingTheory.TotallySplit

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicEmbeddingLiesOverOrComplexConjLiesOverStatement

section

@[expose] public section

open GlobalTheory.LKTrip

theorem _root_.GlobalTheory.T.padicEmbedding_liesOver_or_complexConj_liesOver : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (τ : G.F →+* PadicAlgCl p), LiesOver G.Kq G.u τ ∨ LiesOver G.Kq G.u (τ.comp (conjQ G.F).toRingHom) := by
  first | exact @GlobalTheory.HTGroupOver.liesOver_or_conj | exact GlobalTheory.HTGroupOver.liesOver_or_conj | (intros; apply GlobalTheory.HTGroupOver.liesOver_or_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSigmaLiftW

section

@[expose] public section

open GlobalTheory.LKTrip

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.MaxIdealTensorPadic

variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

theorem conjT_conjT (y : ℚ_[p] ⊗[ℚ] G.F) : conjT G.F ℚ_[p] (conjT G.F ℚ_[p] y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [conjT_tmul, NumberField.IsCMField.complexConj_apply_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem eq_sigma_liftW (f : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p)
    (hf : ∀ a : ℚ_[p], f (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a)
    (i : Fin G.m) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (h : ∀ x : G.F, f (1 ⊗ₜ x) = σ (G.emb i x)) (y : ℚ_[p] ⊗[ℚ] G.F) :
    f y = σ ((G.liftW i y : G.Fw i) : PadicAlgCl p) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have e : (a ⊗ₜ[ℚ] x : ℚ_[p] ⊗[ℚ] G.F) = (a ⊗ₜ 1) * (1 ⊗ₜ x) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e, map_mul, hf, h, map_mul, MulMemClass.coe_mul, map_mul]
    congr 1
    · simp [HTGroup.liftW, Algebra.TensorProduct.lift_tmul, HTGroup.embW]
    · congr 1
      simp only [HTGroup.liftW, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
  | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), AddMemClass.coe_add, map_add (f := _)]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (M : Ideal (TensorProduct ℚ ℚ_[p] G.F)), M.IsMaximal →
    ∃ i : Fin G.m, M = RingHom.ker (G.liftW i) ∨
      M = RingHom.ker ((G.liftW i).toRingHom.comp (conjT G.F ℚ_[p])) := by
  intro p _ G M hM
  letI : Field ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite ℚ_[p] ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℚ_[p] M).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Algebra.IsAlgebraic ℚ_[p] ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) := Algebra.IsAlgebraic.of_finite _ _
  let ι : ((ℚ_[p] ⊗[ℚ] G.F) ⧸ M) →ₐ[ℚ_[p]] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let f : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p := (ι.comp (Ideal.Quotient.mkₐ ℚ_[p] M)).toRingHom
  have hker : ∀ y, y ∈ M ↔ f y = 0 := by
    intro y
    show y ∈ M ↔ ι (Ideal.Quotient.mk M y) = 0
    rw [map_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
  have hf : ∀ a : ℚ_[p], f (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a := fun a =>
    (ι.comp (Ideal.Quotient.mkₐ ℚ_[p] M)).commutes a
  let τ : G.F →+* PadicAlgCl p := f.comp (Algebra.TensorProduct.includeRight : G.F →ₐ[ℚ] _).toRingHom
  rcases GlobalTheory.T.padicEmbedding_liesOver_or_complexConj_liesOver p G τ with hτ | hτ
  · obtain ⟨i, σ, hσ⟩ := G.emb_all τ hτ
    refine ⟨i, Or.inl ?_⟩
    have h : ∀ x : G.F, f (1 ⊗ₜ x) = σ (G.emb i x) := fun x => RingHom.congr_fun hσ x
    ext y
    rw [hker, RingHom.mem_ker, eq_sigma_liftW G f hf i σ h y, map_eq_zero_iff _ σ.injective]
    exact ZeroMemClass.coe_eq_zero
  · obtain ⟨i, σ, hσ⟩ := G.emb_all _ hτ
    refine ⟨i, Or.inr ?_⟩
    let g : ℚ_[p] ⊗[ℚ] G.F →+* PadicAlgCl p := f.comp (conjT G.F ℚ_[p])
    have hg : ∀ a : ℚ_[p], g (a ⊗ₜ 1) = algebraMap ℚ_[p] (PadicAlgCl p) a := fun a => by
      simp only [g, RingHom.comp_apply, conjT_tmul, map_one, hf]
    have h : ∀ x : G.F, g (1 ⊗ₜ x) = σ (G.emb i x) := fun x => RingHom.congr_fun hσ x
    ext y
    have e : f y = g (conjT G.F ℚ_[p] y) := by simp only [g, RingHom.comp_apply, conjT_conjT]
    rw [hker, e, eq_sigma_liftW G g hg i σ h, map_eq_zero_iff _ σ.injective, RingHom.mem_ker]
    exact ZeroMemClass.coe_eq_zero

end GlobalTheory.MaxIdealTensorPadic
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicTensorNumberFieldIsReduced

section

@[expose] public section

open GlobalTheory.LKTrip

namespace GlobalTheory

theorem padic_tensor_numberField_isReduced :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F],
      IsReduced (TensorProduct ℚ ℚ_[p] F) := by
  intro p _ F _ _
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℚ_[p] (TensorProduct ℚ ℚ_[p] F) :=
    Algebra.FormallyUnramified.base_change ℚ_[p]
  exact Algebra.FormallyUnramified.isReduced_of_field ℚ_[p] (TensorProduct ℚ ℚ_[p] F)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMapInjectivity

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.HTGroupLocInj
variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

noncomputable def iotaZ : ℚ_[p] ⊗[ℚ] G.F →ₐ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (IsScalarTower.toAlgHom ℚ G.F G.C)

theorem locW_iotaZ (i : Fin G.m) (z : ℚ_[p] ⊗[ℚ] G.F) :
    G.locW i (iotaZ G z) = algebraMap (G.Fw i) (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (G.liftW i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    change (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) a) * (G.rho i (algebraMap G.F G.C y)) =
      algebraMap (G.Fw i) _ (algebraMap ℚ_[p] (G.Fw i) a * G.embW i y)
    rw [G.rho_F, Algebra.ofId_apply, map_mul, ← IsScalarTower.algebraMap_apply]
    congr 1
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem starT_iotaZ (z : ℚ_[p] ⊗[ℚ] G.F) :
    (starT G.star ℚ_[p] (iotaZ G z)).unop = iotaZ G (conjT G.F ℚ_[p] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp [iotaZ, starT_tmul, G.star_F]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem inj_Z (z : ℚ_[p] ⊗[ℚ] G.F) (h1 : ∀ i, G.liftW i z = 0) (h2 : ∀ i, G.liftW i (conjT G.F ℚ_[p] z) = 0) :
    z = 0 := by
  have hJ : z ∈ (⊥ : Ideal (ℚ_[p] ⊗[ℚ] G.F)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    obtain ⟨i, hi | hi⟩ := GlobalTheory.MaxIdealTensorPadic.main p G M hM <;> rw [hi, RingHom.mem_ker]
    · exact h1 i
    · exact h2 i
  haveI : IsArtinianRing (ℚ_[p] ⊗[ℚ] G.F) := IsArtinianRing.of_finite ℚ_[p] _
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := ℚ_[p] ⊗[ℚ] G.F)
  have hk0 : z ^ k = 0 := by
    have := Ideal.pow_mem_pow hJ k
    rw [hk] at this
    simpa using this
  haveI := GlobalTheory.padic_tensor_numberField_isReduced p G.F
  exact IsReduced.eq_zero _ ⟨k, hk0⟩

theorem iotaZ_comm (d : ℚ_[p] ⊗[ℚ] G.C) (z : ℚ_[p] ⊗[ℚ] G.F) : Commute d (iotaZ G z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _)]; exact hx.add_right hy
  | tmul a y =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => exact hx.add_left hy
    | tmul b c =>
      simp only [iotaZ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      show (b ⊗ₜ c) * (a ⊗ₜ algebraMap G.F G.C y) = (a ⊗ₜ algebraMap G.F G.C y) * (b ⊗ₜ c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm b a,
        Algebra.commutes]

theorem locW_inj (x : ℚ_[p] ⊗[ℚ] G.C) (h1 : ∀ i, G.locW i x = 0)
    (h2 : ∀ i, G.locW i (starT G.star ℚ_[p] x).unop = 0) : x = 0 := by
  classical
  letI algD : Algebra G.F (ℚ_[p] ⊗[ℚ] G.C) :=
    RingHom.toAlgebra' ((iotaZ G).toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom)) (by
      intro c d
      show iotaZ G ((1 : ℚ_[p]) ⊗ₜ c) * d = d * iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)
      exact (iotaZ_comm G d _).symm.eq)
  letI algZ : Algebra G.F (ℚ_[p] ⊗[ℚ] G.F) := Algebra.TensorProduct.rightAlgebra
  let f : G.C →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C :=
    { (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] ℚ_[p] ⊗[ℚ] G.C).toRingHom with
      commutes' := fun c => by
        show (1 : ℚ_[p]) ⊗ₜ algebraMap G.F G.C c = iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)
        simp [iotaZ] }
  let g : (ℚ_[p] ⊗[ℚ] G.F) →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C :=
    { (iotaZ G).toRingHom with
      commutes' := fun c => rfl }
  let Φ := Algebra.TensorProduct.lift f g (fun c z => iotaZ_comm G _ _)
  have hΦ1 : ∀ z, Φ ((1 : G.C) ⊗ₜ z) = iotaZ G z := fun z => by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have hΦs : Function.Surjective Φ := by
    intro d
    induction d using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a c =>
      refine ⟨c ⊗ₜ (a ⊗ₜ (1 : G.F)), ?_⟩
      rw [Algebra.TensorProduct.lift_tmul]
      show ((1 : ℚ_[p]) ⊗ₜ c) * iotaZ G (a ⊗ₜ 1) = a ⊗ₜ c
      simp [iotaZ, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
  let ψ : ℚ_[p] ⊗[ℚ] G.C →+* ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) ×
      ((i : Fin G.m) → (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ᵐᵒᵖ) :=
    RingHom.prod (RingHom.pi fun i => (G.locW i).toRingHom)
      (RingHom.pi fun i => (RingHom.op (G.locW i).toRingHom).comp (starT G.star ℚ_[p]))
  have hψ : ∀ d, ψ d = 0 ↔ (∀ i, G.locW i d = 0) ∧ ∀ i, G.locW i (starT G.star ℚ_[p] d).unop = 0 := by
    intro d
    simp only [ψ, Prod.ext_iff, funext_iff, RingHom.prod_apply, Pi.ringHom_apply, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply, RingHom.comp_apply]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    rw [← MulOpposite.unop_inj]
    rfl
  let J : TwoSidedIdeal (G.C ⊗[G.F] (ℚ_[p] ⊗[ℚ] G.F)) := TwoSidedIdeal.ker (ψ.comp Φ.toRingHom)
  have hJ : J = ⊥ := by
    by_contra hne
    obtain ⟨z, hz0, hz⟩ := GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot J hne
    apply hz0
    rw [TwoSidedIdeal.mem_ker, RingHom.comp_apply] at hz
    change ψ (Φ ((1 : G.C) ⊗ₜ z)) = 0 at hz
    rw [hΦ1, hψ] at hz
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    apply inj_Z G z
    · intro i
      have := hz.1 i
      rw [locW_iotaZ] at this
      exact (FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)
    · intro i
      have := hz.2 i
      rw [starT_iotaZ, locW_iotaZ] at this
      exact (FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)
  obtain ⟨y, rfl⟩ := hΦs x
  have hy : y ∈ J := by
    rw [TwoSidedIdeal.mem_ker]
    exact (hψ _).2 ⟨h1, h2⟩
  rw [hJ, TwoSidedIdeal.mem_bot] at hy
  rw [hy, map_zero]

end GlobalTheory.HTGroupLocInj
end
end
