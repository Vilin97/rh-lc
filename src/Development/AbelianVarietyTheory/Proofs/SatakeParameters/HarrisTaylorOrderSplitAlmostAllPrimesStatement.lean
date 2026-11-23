module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinLocalOrderTensorPadicMatrixAlmostAllStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSimpleRingOfCentralIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingOfIntegersTensorPadicEquivAdjoinStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentreCompat
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraMapFCoe

section

@[expose] public section

noncomputable section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.UPel.HT.Gen.SplitAE

variable (G : GDatum)

def toCenter : 𝓞 G.F →+* Subring.center (ℚ ⊗[ℤ] G.O) where
  toFun c := ⟨(1 : ℚ) ⊗ₜ[ℤ] algebraMap (𝓞 G.F) G.O c, Subring.mem_center_iff.mpr fun g => by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | tmul q o => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
        Algebra.commutes]
    | add x y hx hy => rw [add_mul, mul_add, hx, hy]⟩
  map_one' := by ext; simp [Algebra.TensorProduct.one_def]
  map_mul' a b := by ext; simp [Algebra.TensorProduct.tmul_mul_tmul]
  map_zero' := by ext; simp
  map_add' a b := by ext; simp [TensorProduct.tmul_add]

theorem toCenter_isUnit (c : nonZeroDivisors (𝓞 G.F)) : IsUnit (toCenter G c) := by
  have hc0 : (c : 𝓞 G.F) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have hI := Ideal.comap_ne_bot_of_integral_mem hc0 (Ideal.mem_span_singleton_self (c : 𝓞 G.F))
    (Algebra.IsIntegral.isIntegral (R := ℤ) (c : 𝓞 G.F))
  obtain ⟨k, hk, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hk
  obtain ⟨d, hd⟩ := hk
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
  have hu : IsUnit ((k : Subring.center (ℚ ⊗[ℤ] G.O))) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap ℚ _ (k : ℚ)⁻¹,
      Subring.mem_center_iff.mpr fun g => (Algebra.commutes _ g).symm⟩, ?_⟩
    apply Subtype.ext
    show ((k : Subring.center (ℚ ⊗[ℤ] G.O)) : ℚ ⊗[ℤ] G.O) * algebraMap ℚ _ (k : ℚ)⁻¹ = 1
    rw [Subring.coe_intCast, ← map_intCast (algebraMap ℚ (ℚ ⊗[ℤ] G.O)), ← map_mul, mul_inv_cancel₀ hk', map_one]
  have hm : toCenter G d * toCenter G c = (k : Subring.center (ℚ ⊗[ℤ] G.O)) := by
    rw [← map_mul, hd, eq_intCast (algebraMap ℤ (𝓞 G.F)) k, map_intCast]
  exact isUnit_of_mul_isUnit_right (hm ▸ hu)

def fMap : G.F →+* ℚ ⊗[ℤ] G.O :=
  (Subring.center (ℚ ⊗[ℤ] G.O)).subtype.comp
    (IsLocalization.lift (M := nonZeroDivisors (𝓞 G.F)) (S := G.F) (toCenter_isUnit G))

theorem fMap_mem_center (x : G.F) : fMap G x ∈ Subring.center (ℚ ⊗[ℤ] G.O) :=
  (IsLocalization.lift (M := nonZeroDivisors (𝓞 G.F)) (S := G.F) (toCenter_isUnit G) x).2

instance instAlgebraF : Algebra G.F (ℚ ⊗[ℤ] G.O) :=
  (fMap G).toAlgebra' fun x y => ((Subring.mem_center_iff.mp (fMap_mem_center G x)) y).symm

theorem algebraMap_F_coe (c : 𝓞 G.F) :
    algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F) = (1 : ℚ) ⊗ₜ[ℤ] algebraMap (𝓞 G.F) G.O c := by
  show fMap G (algebraMap (𝓞 G.F) G.F c) = _
  simp only [fMap, RingHom.comp_apply, IsLocalization.lift_eq]
  rfl

instance instTowerF : IsScalarTower ℚ G.F (ℚ ⊗[ℤ] G.O) :=
  IsScalarTower.of_algebraMap_eq fun q => by
    have := RingHom.ext_rat (algebraMap ℚ (ℚ ⊗[ℤ] G.O)) ((algebraMap G.F (ℚ ⊗[ℤ] G.O)).comp (algebraMap ℚ G.F))
    exact congrArg (fun f : ℚ →+* ℚ ⊗[ℤ] G.O => f q) this

def ordB : Subring (ℚ ⊗[ℤ] G.O) := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := G.O)).toRingHom.range

end GlobalTheory.UPel.HT.Gen.SplitAE
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTensorPadicIntEquivAdjoinOfFreeFinite

section

@[expose] public section

open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

namespace GlobalTheory.LocIso

theorem tensor_padicInt_equiv_locOrder : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (ℓ : ℕ) [Fact ℓ.Prime], ∃ ι : O ⊗[ℤ] ℤ_[ℓ] ≃+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range, ∀ o : O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
  intro O _ _ _ ℓ _
  let g1 : O →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O) :=
    ((Algebra.TensorProduct.includeRight : (ℚ ⊗[ℤ] O) →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom).toIntAlgHom
  let g2 : ℤ_[ℓ] →ₐ[ℤ] ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O) :=
    ((Algebra.TensorProduct.includeLeftRingHom (R := ℚ) (A := ℚ_[ℓ]) (B := ℚ ⊗[ℤ] O)).comp
      PadicInt.Coe.ringHom).toIntAlgHom
  have hg1 : ∀ x, g1 x = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) := fun _ => rfl
  have hg2 : ∀ y : ℤ_[ℓ], g2 y = (y : ℚ_[ℓ]) ⊗ₜ[ℚ] (1 : ℚ ⊗[ℤ] O) := fun _ => rfl
  have hg : ∀ x y, Commute (g1 x) (g2 y) := by
    intro x y
    simp only [hg1, hg2, Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  let f := Algebra.TensorProduct.lift g1 g2 hg
  have hf : ∀ (o : O) (a : ℤ_[ℓ]), f (o ⊗ₜ a) = (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
    intro o a
    simp only [f, Algebra.TensorProduct.lift_tmul, hg1, hg2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hinj : Function.Injective f := by
    have hl : Function.Injective (LinearMap.lTensor O (PadicInt.Coe.ringHom (p := ℓ)).toIntAlgHom.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (fun a b h => Subtype.ext h)
    have heq : (f : O ⊗[ℤ] ℤ_[ℓ] → ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) =
        (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ℚ ℚ_[ℓ] ℚ_[ℓ] O).symm ∘
          (TensorProduct.comm ℤ O ℚ_[ℓ]) ∘
          (LinearMap.lTensor O (PadicInt.Coe.ringHom (p := ℓ)).toIntAlgHom.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul o a =>
        simp only [Function.comp_apply, LinearMap.lTensor_tmul, TensorProduct.comm_tmul,
          TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, hf]
        rfl
      | add x y hx hy =>
        simp only [Function.comp_apply, map_add (f := _)] at hx hy ⊢
        rw [hx, hy]
    rw [heq]
    exact (LinearEquiv.injective _).comp ((LinearEquiv.injective _).comp hl)
  have hmem : ∀ x, f x ∈ locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o a =>
      rw [hf]
      have h1 : (a : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) =
          algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) a * ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rfl
      rw [h1]
      refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (Algebra.subset_adjoin ?_)
      exact ⟨(1 : ℚ) ⊗ₜ[ℤ] o, ⟨o, rfl⟩, rfl⟩
    | add x y hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  let g : O ⊗[ℤ] ℤ_[ℓ] →+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range :=
    (f.toRingHom).codRestrict _ hmem
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range).toSubring := hy
    rw [locOrder, Algebra.adjoin_eq_ring_closure] at hy'
    have hle : Subring.closure (Set.range (algebraMap ℤ_[ℓ] (ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O))) ∪
        ((fun b => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b) '' ((Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range : Set (ℚ ⊗[ℤ] O)))) ≤ f.toRingHom.range := by
      rw [Subring.closure_le]
      rintro _ (⟨a, rfl⟩ | ⟨_, ⟨o, rfl⟩, rfl⟩)
      · refine ⟨(1 : O) ⊗ₜ a, ?_⟩
        change f _ = _
        rw [hf, Algebra.TensorProduct.algebraMap_apply]
        rfl
      · refine ⟨o ⊗ₜ (1 : ℤ_[ℓ]), ?_⟩
        change f _ = _
        rw [hf]
        simp
    obtain ⟨x, hx⟩ := hle hy'
    exact ⟨x, Subtype.ext hx⟩
  refine ⟨RingEquiv.ofBijective g ⟨fun x y h => hinj (congrArg Subtype.val h), hsurj⟩, fun o => ?_⟩
  change f (o ⊗ₜ 1) = _
  rw [hf]
  simp

end GlobalTheory.LocIso
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTensorPadicIntEquivAdjoinOfFreeFiniteStatement

section

@[expose] public section

open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_tensorPadicInt_equiv_adjoin_of_free_finite : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (ℓ : ℕ) [Fact ℓ.Prime], ∃ ι : O ⊗[ℤ] ℤ_[ℓ] ≃+* locOrder ℓ (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := O)).toRingHom.range, ∀ o : O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[ℓ] ⊗[ℚ] (ℚ ⊗[ℤ] O)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) := by
  first | (exact @GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder) | (exact GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder) | (intros; apply GlobalTheory.LocIso.tensor_padicInt_equiv_locOrder  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimes

section

@[expose] public section

namespace GlobalTheory.UPel.HT.Gen.SplitAE
open NumberField GlobalTheory.LKInvGood
open scoped TensorProduct

theorem finrank_eq (G : GDatum) : Module.finrank G.F (ℚ ⊗[ℤ] G.O) = G.m ^ 2 := by
  haveI := G.freeO
  haveI := G.finO
  have h1 : Module.finrank ℚ (ℚ ⊗[ℤ] G.O) = Module.finrank ℤ G.O := Module.finrank_baseChange
  haveI : Module.Finite ℚ (ℚ ⊗[ℤ] G.O) := inferInstance
  haveI : Module.Finite G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _
  have h2 := Module.finrank_mul_finrank ℚ G.F (ℚ ⊗[ℤ] G.O)
  rw [h1, G.rankO] at h2
  have hd : 0 < Module.finrank ℚ G.F := Module.finrank_pos
  have : Module.finrank ℚ G.F * Module.finrank G.F (ℚ ⊗[ℤ] G.O) = Module.finrank ℚ G.F * G.m ^ 2 := by
    rw [h2, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left hd this

theorem isCentral (G : GDatum) : Algebra.IsCentral G.F (ℚ ⊗[ℤ] G.O) := by
  refine ⟨fun z hz => ?_⟩
  rw [Subalgebra.mem_center_iff] at hz
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G z
  have hxc : ∀ y : G.O, x * y = y * x := by
    intro y
    apply GDatum.tmul_one_injective G
    have e1 : (1:ℚ) ⊗ₜ[ℤ] (x*y) = N • (z * (1 ⊗ₜ y)) := by
      rw [← smul_mul_assoc, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e2 : (1:ℚ) ⊗ₜ[ℤ] (y*x) = N • ((1 ⊗ₜ y) * z) := by
      rw [← mul_smul_comm, hx, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    show (1:ℚ) ⊗ₜ[ℤ] (x*y) = (1:ℚ) ⊗ₜ[ℤ] (y*x)
    rw [e1, e2, hz]
  obtain ⟨c, e, he, hec⟩ := G.central x hxc
  have hM : ((e * N : ℤ) : ℚ) • z = algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F) := by
    rw [algebraMap_F_coe, ← hec, Int.cast_smul_eq_zsmul, mul_smul, hx, TensorProduct.tmul_smul]
  have hq : ((e * N : ℤ) : ℚ) ≠ 0 := by exact_mod_cast mul_ne_zero he hN
  refine ⟨((e * N : ℤ) : ℚ)⁻¹ • (c : G.F), ?_⟩
  show algebraMap G.F (ℚ ⊗[ℤ] G.O) (((e * N : ℤ) : ℚ)⁻¹ • (c : G.F)) = z
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, ← hM, smul_smul, inv_mul_cancel₀ hq, one_smul]

theorem ordB_finite (G : GDatum) : Module.Finite ℤ (ordB G) := by
  haveI := G.finO
  let f := (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := G.O)).toRingHom
  exact Module.Finite.of_surjective f.rangeRestrict.toIntAlgHom.toLinearMap f.rangeRestrict_surjective

theorem ordB_denom (G : GDatum) (b : ℚ ⊗[ℤ] G.O) : ∃ n : ℕ, 0 < n ∧ (n : ℚ ⊗[ℤ] G.O) * b ∈ ordB G := by
  obtain ⟨N, hN, x, hx⟩ := GDatum.exists_smul_eq_tmul G b
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg N
  · refine ⟨n, by omega, x, ?_⟩
    show (1 : ℚ) ⊗ₜ[ℤ] x = _
    rw [← hx, natCast_zsmul, nsmul_eq_mul]
  · refine ⟨n, by omega, -x, ?_⟩
    show (1 : ℚ) ⊗ₜ[ℤ] (-x) = _
    rw [TensorProduct.tmul_neg, ← hx, neg_smul, neg_neg, natCast_zsmul, nsmul_eq_mul]

theorem splitAE : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M →
    Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  intro G
  haveI := G.freeO
  haveI := G.finO
  haveI := isCentral G
  haveI := GDatum.isSimpleRing G
  haveI : FiniteDimensional G.F (ℚ ⊗[ℤ] G.O) := Module.Finite.of_restrictScalars_finite ℚ G.F _
  obtain ⟨N, hN, hloc⟩ := GlobalTheory.T.adjoinLocalOrderTensorPadic_matrix_almost_all G.F (ℚ ⊗[ℤ] G.O) G.m (finrank_eq G) (ordB G) (ordB_finite G) (ordB_denom G)
  refine ⟨N, hN, fun p _ hp => ?_⟩
  obtain ⟨ψ, hψ⟩ := hloc p hp
  obtain ⟨ι, hι⟩ : ∃ ι : G.O ⊗[ℤ] ℤ_[p] ≃+* locOrder p (ordB G),
      ∀ o : G.O, (ι (o ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) = (1 : ℚ_[p]) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] o) :=
    GlobalTheory.T.exists_tensorPadicInt_equiv_adjoin_of_free_finite G.O p
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_ringOfIntegersTensorPadic_equiv_adjoin G.F p
  let Φ : G.O ⊗[ℤ] ℤ_[p] ≃+* Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p]) :=
    ι.trans (ψ.toRingEquiv.trans κ.symm.mapMatrix)
  refine ⟨AlgEquiv.ofRingEquiv (f := Φ) fun c => ?_⟩
  obtain ⟨h, hh⟩ := hψ (κ (c ⊗ₜ[ℤ] 1))
  have e1 : ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) = ⟨_, h⟩ := by
    apply Subtype.ext
    show (ι (algebraMap (𝓞 G.F) (G.O ⊗[ℤ] ℤ_[p]) c) : ℚ_[p] ⊗[ℚ] (ℚ ⊗[ℤ] G.O)) =
      cenMap p G.F (ℚ ⊗[ℤ] G.O) (κ (c ⊗ₜ[ℤ] 1) : ℚ_[p] ⊗[ℚ] G.F)
    rw [Algebra.TensorProduct.algebraMap_apply, hι, hκ, cenMap, Algebra.TensorProduct.map_tmul]
    show _ = (1 : ℚ_[p]) ⊗ₜ[ℚ] algebraMap G.F (ℚ ⊗[ℤ] G.O) (c : G.F)
    rw [algebraMap_F_coe]
  show κ.symm.mapMatrix (ψ (ι _)) = _
  rw [e1]
  erw [hh]
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.algebraMap_eq_diagonal]
  split_ifs <;> simp [RingEquiv.symm_apply_apply]

end GlobalTheory.UPel.HT.Gen.SplitAE
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.HarrisTaylorOrderSplitAlmostAllPrimesStatement

section

@[expose] public section

open NumberField
open GlobalTheory.UPel.HT.Gen
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harrisTaylorOrder_split_almost_all_primes : ∀ (G : GDatum), ∃ M : ℕ, 0 < M ∧ ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → Nonempty ((G.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 G.F] Matrix (Fin G.m) (Fin G.m) (𝓞 G.F ⊗[ℤ] ℤ_[p])) := by
  first | (exact @GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (exact GlobalTheory.UPel.HT.Gen.SplitAE.splitAE) | (intros; apply GlobalTheory.UPel.HT.Gen.SplitAE.splitAE  <;> assumption)
end
end
