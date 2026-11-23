module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Mathlib.RingTheory.TensorProduct.Basic
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
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharZero
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqMulFinrankMatrixAlgebraHomEqFinrankMulStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionFactorThroughTensorCharacter

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem tensor_action_factors (k : Type) [Field k] (C O B : Type) [CommRing C] [Ring O] [Algebra C O]
    [Algebra C k] [Ring B] [Algebra k B] (e : (k ⊗[C] O) ≃ₐ[k] B) (X : Type) [AddCommGroup X]
    [Module k X] (σX : O →+* Module.End k X)
    (hσ : ∀ c, σX (algebraMap C O c) = algebraMap C k c • 1) :
    ∃ ρX : B →ₐ[k] Module.End k X, ∀ o, ρX (e (1 ⊗ₜ[C] o)) = σX o := by
  letI : Algebra C (Module.End k X) :=
    ((algebraMap k (Module.End k X)).comp (algebraMap C k)).toAlgebra'
      (fun c f => Algebra.commutes (algebraMap C k c) f)
  haveI : IsScalarTower C k (Module.End k X) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let g : O →ₐ[C] Module.End k X :=
    { σX with
      commutes' := fun c => by
        change σX (algebraMap C O c) = algebraMap k (Module.End k X) (algebraMap C k c)
        rw [hσ]; exact (Algebra.algebraMap_eq_smul_one _).symm }
  let F : (k ⊗[C] O) →ₐ[k] Module.End k X :=
    Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k X)) g
      (fun x y => Algebra.commutes x (g y))
  refine ⟨F.comp e.symm.toAlgHom, fun o => ?_⟩
  show F (e.symm (e (1 ⊗ₜ[C] o))) = σX o
  rw [e.symm_apply_apply]
  rw [show F (1 ⊗ₜ[C] o) = Algebra.ofId k (Module.End k X) 1 * g o from
    Algebra.TensorProduct.lift_tmul _ _ _ _ _, map_one, one_mul]
  rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionFactorThroughTensorCharacterStatement

section

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_action_factor_through_tensor_character : ∀ (k : Type) [Field k] (C O B : Type) [CommRing C] [Ring O] [Algebra C O] [Algebra C k] [Ring B] [Algebra k B] (e : (k ⊗[C] O) ≃ₐ[k] B) (X : Type) [AddCommGroup X] [Module k X] (σX : O →+* Module.End k X), (∀ c, σX (algebraMap C O c) = algebraMap C k c • 1) → ∃ ρX : B →ₐ[k] Module.End k X, ∀ o, ρX (e (1 ⊗ₜ[C] o)) = σX o := by
  first | (exact @GlobalTheory.tensor_action_factors) | (exact GlobalTheory.tensor_action_factors) | (intros; apply GlobalTheory.tensor_action_factors  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharP

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CharPMatrix

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]

def redHom : ℤ_[p] →+* k := (ZMod.castHom (dvd_refl p) k).comp PadicInt.toZMod

lemma exists_nat_add (z : ℤ_[p]) : ∃ n : ℕ, ∃ w : ℤ_[p], z = n + p * w := by
  have h := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨PadicInt.zmodRepr z, w, by rw [mul_comm, hw]; ring⟩

variable (B : Type) [Ring B] [Algebra k B]

def tensorPadicEquiv : B ⊗[ℤ] ℤ_[p] ≃ₐ[k] B :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (AlgHom.id k B)
      (((algebraMap k B).comp (redHom p k)).toIntAlgHom)
      (by intro x y; exact Algebra.commute_algebraMap_right _ _))
    Algebra.TensorProduct.includeLeft
    (by ext b; simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply]; erw [Algebra.TensorProduct.lift_tmul]; simp)
    (by
      apply Algebra.TensorProduct.ext'
      intro b z
      obtain ⟨n, w, rfl⟩ := exists_nat_add p z
      have hp : (p : B) = 0 := by
        rw [← map_natCast (algebraMap k B), CharP.cast_eq_zero, map_zero]
      simp [redHom, Algebra.TensorProduct.lift_tmul]
      have h1 : b ⊗ₜ[ℤ] ((p : ℤ_[p]) * w) = 0 := by
        rw [show ((p : ℤ_[p]) * w) = (p : ℤ) • w by simp, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, eq_intCast, Int.cast_natCast, hp, zero_mul,
          TensorProduct.zero_tmul]
      have h2 : b ⊗ₜ[ℤ] (n : ℤ_[p]) = (b * n) ⊗ₜ[ℤ] 1 := by
        rw [show (n : ℤ_[p]) = (n : ℤ) • (1 : ℤ_[p]) by simp, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, eq_intCast, Int.cast_natCast, Nat.cast_comm]
      rw [TensorProduct.tmul_add, h1, h2, add_zero])

def matrixBaseChange (R : Type) [CommRing R] (K : Type) [CommRing K] [Algebra R K]
    (n : Type) [Fintype n] [DecidableEq n] : K ⊗[R] Matrix n n R ≃ₐ[K] Matrix n n K :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n R K).symm.toRingEquiv) (by
    intro c
    simp only [AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Algebra.algebraMap_eq_smul_one])

end GlobalTheory.CharPMatrix

namespace GlobalTheory.UPel.HT


open GlobalTheory.CharPMatrix in
theorem Datum.charP_tensor_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k]
    [CharP k p] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  intro p _ D k _ _ _
  obtain ⟨e⟩ := D.splitP
  have E0 : k ⊗[𝓞 D.F] (𝓞 D.F ⊗[ℤ] ℤ_[p]) ≃ₐ[k] k :=
    (Algebra.TensorProduct.cancelBaseChange ℤ (𝓞 D.F) k k ℤ_[p]).trans (tensorPadicEquiv p k k)
  have E1 := (Algebra.TensorProduct.assoc ℤ (𝓞 D.F) (𝓞 D.F) D.O (𝓞 D.F) ℤ_[p]).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid (𝓞 D.F) (𝓞 D.F) D.O) (AlgEquiv.refl (R := ℤ) (A₁ := ℤ_[p])))
  have E2 := E1.trans e
  exact ⟨(Algebra.TensorProduct.congr E0.symm (AlgEquiv.refl (R := 𝓞 D.F) (A₁ := D.O))).trans
    ((Algebra.TensorProduct.assoc (𝓞 D.F) (𝓞 D.F) k k (𝓞 D.F ⊗[ℤ] ℤ_[p]) D.O).trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl
      ((Algebra.TensorProduct.comm (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]) D.O).trans
        (E2.trans (matrixEquivTensor (Fin D.m) (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]))))).trans
    ((Algebra.TensorProduct.assoc (𝓞 D.F) (𝓞 D.F) k k (𝓞 D.F ⊗[ℤ] ℤ_[p])
      (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F))).symm.trans
    ((Algebra.TensorProduct.congr E0 AlgEquiv.refl).trans
    (matrixBaseChange (𝓞 D.F) k (Fin D.m))))))⟩

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharPStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charP : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [CharP k p] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  first | (exact @GlobalTheory.UPel.HT.Datum.charP_tensor_matrix) | (exact GlobalTheory.UPel.HT.Datum.charP_tensor_matrix) | (intros; apply GlobalTheory.UPel.HT.Datum.charP_tensor_matrix  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTensorOrderAlgEquivMatrixCharZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charZero : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  first | (exact @GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix) | (exact GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix) | (intros; apply GlobalTheory.UPel.HT.MoritaChar0.tensor_order_algEquiv_matrix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanOneTmulEqTopAlt

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory.OneTensorSpanTop

theorem span_one_tmul_eq_top (k : Type) [Field k] (C O : Type) [CommRing C] [Ring O]
    [Algebra C O] [Algebra C k] :
    Submodule.span k (Set.range fun (o : O) ↦ (1 : k) ⊗ₜ[C] o) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a o =>
    have h : a ⊗ₜ[C] o = a • ((1 : k) ⊗ₜ[C] o) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨o, rfl⟩)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

end GlobalTheory.OneTensorSpanTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHomHarrisTaylorOrderMorita

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

namespace GlobalTheory.HTRho

theorem span_one_tmul (k : Type) [Field k] (C O : Type) [CommRing C] [Ring O] [Algebra C O] [Algebra C k] :
    Submodule.span k (Set.range fun o : O => (1 : k) ⊗ₜ[C] o) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top
  | exact _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top
  | (apply _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneTensorSpanTop.span_one_tmul_eq_top ..)

theorem finrank_homO_morita : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] [IsAlgClosed k], (∀ n : ℕ, n.Coprime p → (n : k) ≠ 0) → ∀ (χ : 𝓞 D.F →+* k) (X Y : Type) [AddCommGroup X] [Module k X] [FiniteDimensional k X] [AddCommGroup Y] [Module k Y] [FiniteDimensional k Y] (σX : D.O →+* Module.End k X) (σY : D.O →+* Module.End k Y), (∀ c, σX (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → (∀ c, σY (algebraMap (𝓞 D.F) D.O c) = χ c • 1) → D.m ^ 2 * Module.finrank k (GlobalTheory.HTRho.homO σX σY) = Module.finrank k X * Module.finrank k Y := by
  intro p _ D k _ _ hk χ X Y _ _ _ _ _ _ σX σY hX hY
  letI : Algebra (𝓞 D.F) k := χ.toAlgebra
  have hiso : Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
    obtain ⟨q, hq⟩ := CharP.exists k
    rcases CharP.char_is_prime_or_zero k q with hq' | rfl
    · by_cases hqp : q = p
      · subst hqp; exact GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charP q D k
      · exfalso
        exact hk q ((Nat.coprime_primes hq' (Fact.out)).2 hqp) (CharP.cast_eq_zero k q)
    · haveI : CharZero k := CharP.charP_to_charZero k
      exact GlobalTheory.T.harrisTaylor_tensor_order_algEquiv_matrix_charZero p D k
  obtain ⟨e⟩ := hiso
  obtain ⟨ρX, hρX⟩ := GlobalTheory.T.exists_action_factor_through_tensor_character k (𝓞 D.F) D.O _ e X σX hX
  obtain ⟨ρY, hρY⟩ := GlobalTheory.T.exists_action_factor_through_tensor_character k (𝓞 D.F) D.O _ e Y σY hY
  have heq : GlobalTheory.HTRho.homO σX σY = GlobalTheory.HTRho.homO ρX.toRingHom ρY.toRingHom := by
    ext T
    rw [GlobalTheory.HTRho.mem_homO, GlobalTheory.HTRho.mem_homO]
    constructor
    · intro h b
      have hb : b ∈ Submodule.span k (Set.range fun o : D.O => e ((1 : k) ⊗ₜ[𝓞 D.F] o)) := by
        have hr : (Set.range fun o : D.O => e ((1 : k) ⊗ₜ[𝓞 D.F] o)) =
            (e.toLinearMap) '' Set.range (fun o : D.O => (1 : k) ⊗ₜ[𝓞 D.F] o) := by
          rw [← Set.range_comp]; rfl
        rw [hr, Submodule.span_image, span_one_tmul, Submodule.map_top,
          LinearMap.range_eq_top.2 e.surjective]
        trivial
      induction hb using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨o, rfl⟩ := hz
        intro x; simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hρX, hρY]; exact h o x
      | zero => intro x; simp
      | add a b _ _ ha hb =>
        intro x
        have h1 := ha x
        have h2 := hb x
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), LinearMap.add_apply] at h1 h2 ⊢
        rw [h1, h2]
      | smul c a _ ha =>
        intro x
        have h1 := ha x
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_smul, LinearMap.smul_apply] at h1 ⊢
        rw [h1]
    · intro h o x
      have := h (e (1 ⊗ₜ o)) x
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hρX, hρY] using this
  rw [heq]
  exact GlobalTheory.T.sq_mul_finrank_matrixAlgebra_hom_eq_finrank_mul k D.m X Y ρX ρY

end GlobalTheory.HTRho
end
end
