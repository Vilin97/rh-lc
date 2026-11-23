module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorPowerSplit
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBaseChangeEquiv

section

@[expose] public section

open TensorProduct

namespace GlobalTheory.CompanionTheory.ExteriorBase

theorem exists_baseChange_equiv (A R M : Type) [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module A M] (a : ℕ) :
    ∃ e : R ⊗[A] (⋀[A]^a M) ≃ₗ[R] ⋀[R]^a (R ⊗[A] M), ∀ (r : R) (m : Fin a → M),
      e (r ⊗ₜ exteriorPower.ιMulti A a m) =
        r • exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] m k) := by
  have h := GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange A M R) a
  refine ⟨h.equiv, fun r m => ?_⟩
  rw [h.equiv_tmul, GlobalTheory.exteriorPowerMapOver_ιMulti]
  rfl

end GlobalTheory.CompanionTheory.ExteriorBase
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerPushoutSplit

section

@[expose] public section

open TensorProduct

namespace GlobalTheory.CompanionTheory.KaehlerPushout

open KaehlerDifferential

theorem exists_retraction (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K B A R] :
    ∃ r : Ω[R⁄K] →ₗ[R] R ⊗[A] Ω[A⁄K],
      (∀ x, r (KaehlerDifferential.mapBaseChange K A R x) = x) ∧
      (∀ y, r (KaehlerDifferential.mapBaseChange K B R y) = 0) := by
  let e := KaehlerDifferential.tensorKaehlerEquiv K B A R
  refine ⟨e.symm.toLinearMap ∘ₗ KaehlerDifferential.map K B R R, ?_, ?_⟩
  · intro x
    have key : KaehlerDifferential.map K B R R (KaehlerDifferential.mapBaseChange K A R x) = e x := by
      induction x with
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul s w =>
        have hw : w ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A)) := by
          rw [KaehlerDifferential.span_range_derivation]; trivial
        induction hw using Submodule.span_induction generalizing s with
        | mem w hw =>
          obtain ⟨a, rfl⟩ := hw
          simp [e, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
        | zero => simp
        | add u v _ _ hu hv => simp only [tmul_add, map_add (f := _), hu, hv]
        | smul a u _ hu =>
          rw [← TensorProduct.smul_tmul]
          exact hu _
    simp [key]
  · intro y
    induction y with
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]
    | tmul s w =>
      have hw : w ∈ Submodule.span B (Set.range (KaehlerDifferential.D K B)) := by
        rw [KaehlerDifferential.span_range_derivation]; trivial
      induction hw using Submodule.span_induction generalizing s with
      | mem w hw =>
        obtain ⟨b, rfl⟩ := hw
        simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
      | zero => simp
      | add u v _ _ hu hv => simp only [tmul_add, map_add (f := _), hu, hv, add_zero]
      | smul b u _ hu =>
        rw [← TensorProduct.smul_tmul]
        exact hu _

theorem range_sup_range (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [h : Algebra.IsPushout K A B R] :
    LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔
      LinearMap.range (KaehlerDifferential.mapBaseChange K B R) = ⊤ := by
  set S := LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔
      LinearMap.range (KaehlerDifferential.mapBaseChange K B R) with hS
  have hA : ∀ a : A, KaehlerDifferential.D K R (algebraMap A R a) ∈ S := fun a =>
    Submodule.mem_sup_left ⟨1 ⊗ₜ KaehlerDifferential.D K A a, by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩
  have hB : ∀ b : B, KaehlerDifferential.D K R (algebraMap B R b) ∈ S := fun b =>
    Submodule.mem_sup_right ⟨1 ⊗ₜ KaehlerDifferential.D K B b, by
      simp [KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]⟩
  have hD : ∀ r : R, KaehlerDifferential.D K R r ∈ S := by
    intro r
    induction r using h.out.inductionOn with
    | tmul b => exact hB b
    | smul a y hy =>
      rw [Algebra.smul_def, Derivation.leibniz]
      exact S.add_mem (S.smul_mem _ hy) (S.smul_mem _ (hA a))
    | add x y hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  exact hD r

theorem kaehler_pushout_split : ∀ (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R] [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R] [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K A B R], ∃ (r : Ω[R⁄K] →ₗ[R] R ⊗[A] Ω[A⁄K]) (π : Ω[R⁄K] →ₗ[R] R ⊗[B] Ω[B⁄K]), (∀ x, r (KaehlerDifferential.mapBaseChange K A R x) = x) ∧ (∀ y, r (KaehlerDifferential.mapBaseChange K B R y) = 0) ∧ (∀ x, π (KaehlerDifferential.mapBaseChange K A R x) = 0) ∧ (∀ y, π (KaehlerDifferential.mapBaseChange K B R y) = y) ∧ LinearMap.range (KaehlerDifferential.mapBaseChange K A R) ⊔ LinearMap.range (KaehlerDifferential.mapBaseChange K B R) = ⊤ := by
  intro K A B R _ _ _ _ _ _ _ _ _ _ _ h
  haveI hs : Algebra.IsPushout K B A R := h.symm
  obtain ⟨r, hr₁, hr₂⟩ := exists_retraction K A B R
  obtain ⟨π, hπ₁, hπ₂⟩ := exists_retraction K B A R
  exact ⟨r, π, hr₁, hr₂, hπ₂, hπ₁, range_sup_range K A B R⟩

end GlobalTheory.CompanionTheory.KaehlerPushout
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorEquivBaseChangeTensor

section

@[expose] public section

open TensorProduct

namespace GlobalTheory.CompanionTheory.TensorPushout

theorem tensor_equiv_baseChange_tensor :
    ∀ (K A B R X Y : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R] [Algebra K A]
      [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R] [IsScalarTower K A R]
      [IsScalarTower K B R] [Algebra.IsPushout K A B R] [AddCommGroup X] [Module K X] [Module A X]
      [IsScalarTower K A X] [AddCommGroup Y] [Module K Y] [Module B Y] [IsScalarTower K B Y],
      ∃ t : X ⊗[K] Y ≃ₗ[K] (R ⊗[A] X) ⊗[R] (R ⊗[B] Y),
        ∀ x y, t (x ⊗ₜ y) = ((1 : R) ⊗ₜ[A] x) ⊗ₜ[R] ((1 : R) ⊗ₜ[B] y) := by
  intro K A B R X Y
  intros
  refine ⟨((TensorProduct.AlgebraTensorModule.cancelBaseChange K A A X Y).symm.restrictScalars K).trans <|
    (((Algebra.IsPushout.cancelBaseChange K A B R Y).symm.lTensor X).restrictScalars K).trans <|
    ((TensorProduct.comm A X (R ⊗[B] Y)).restrictScalars K).trans <|
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R R (R ⊗[B] Y) X).symm.restrictScalars K).trans <|
    ((TensorProduct.comm R (R ⊗[B] Y) (R ⊗[A] X)).restrictScalars K), fun x y => ?_⟩
  simp only [LinearEquiv.trans_apply, LinearEquiv.restrictScalars_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearEquiv.lTensor_tmul,
    Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one, TensorProduct.comm_tmul]

end GlobalTheory.CompanionTheory.TensorPushout
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiCongrRightSingle

section

@[expose] public section

open TensorProduct CrystallineSemistableComparison.Onto

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.OmKun

theorem piCongrRight_single {K ι : Type} [CommRing K] [DecidableEq ι] {X Y : ι → Type}
    [∀ i, AddCommGroup (X i)] [∀ i, Module K (X i)] [∀ i, AddCommGroup (Y i)] [∀ i, Module K (Y i)]
    (f : ∀ i, X i ≃ₗ[K] Y i) (a : ι) (x : X a) :
    LinearEquiv.piCongrRight f (Pi.single a x) = Pi.single a (f a x) := by
  funext b
  by_cases h : b = a
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem omKun_pushout (K A B R : Type) [CommRing K] [CommRing A] [CommRing B] [CommRing R]
    [Algebra K A] [Algebra K B] [Algebra K R] [Algebra A R] [Algebra B R]
    [IsScalarTower K A R] [IsScalarTower K B R] [Algebra.IsPushout K A B R] (c : ℕ) :
    ∃ e : (∀ a : Fin (c + 1), TensorProduct K (Om K A a) (Om K B (c - a))) ≃ₗ[K] Om K R c,
      ∀ (a : Fin (c + 1)) (g₀ : A) (g : Fin a → A) (h₀ : B) (h : Fin (c - a) → B),
        e (Pi.single a (form K g₀ g ⊗ₜ form K h₀ h)) = form K (algebraMap A R g₀ * algebraMap B R h₀)
          (Fin.append (fun k => algebraMap A R (g k)) (fun k => algebraMap B R (h k)) ∘
            Fin.cast (by have := a.2; omega)) := by
  obtain ⟨r, π, h1, h2, h3, h4, h5⟩ := GlobalTheory.CompanionTheory.KaehlerPushout.kaehler_pushout_split K A B R
  obtain ⟨E, hE⟩ := GlobalTheory.CompanionTheory.TopExtSplit.exteriorPower_split R _ _ _ _ _ r π h1 h2 h3 h4 h5 c
  choose bA hbA using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv A R (Ω[A⁄K]) a
  choose bB hbB using fun a : ℕ => GlobalTheory.CompanionTheory.ExteriorBase.exists_baseChange_equiv B R (Ω[B⁄K]) a
  choose t ht using fun a : Fin (c + 1) => GlobalTheory.CompanionTheory.TensorPushout.tensor_equiv_baseChange_tensor K A B R (Om K A a) (Om K B (c - a))
  refine ⟨LinearEquiv.piCongrRight (fun a => t a ≪≫ₗ
    (TensorProduct.congr (bA a) (bB (c - a))).restrictScalars K) ≪≫ₗ E.restrictScalars K, ?_⟩
  intro a g₀ g h₀ h
  have hA : bA a ((1 : R) ⊗ₜ[A] form K g₀ g) = algebraMap A R g₀ •
      exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) := by
    unfold form
    rw [← TensorProduct.smul_tmul, hbA, Algebra.smul_def, mul_one]
  have hB : bB (c - a) ((1 : R) ⊗ₜ[B] form K h₀ h) = algebraMap B R h₀ •
      exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k)) := by
    unfold form
    rw [← TensorProduct.smul_tmul, hbB, Algebra.smul_def, mul_one]
  have hmain : (TensorProduct.congr (bA a) (bB (c - a))) (((1 : R) ⊗ₜ[A] form K g₀ g) ⊗ₜ[R]
      ((1 : R) ⊗ₜ[B] form K h₀ h)) = (algebraMap A R g₀ * algebraMap B R h₀) •
        (exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] KaehlerDifferential.D K A (g k)) ⊗ₜ[R]
        exteriorPower.ιMulti R (c - a) (fun k => (1 : R) ⊗ₜ[B] KaehlerDifferential.D K B (h k))) := by
    rw [TensorProduct.congr_tmul, hA, hB, TensorProduct.smul_tmul_smul]
  simp only [LinearEquiv.trans_apply, piCongrRight_single, LinearEquiv.restrictScalars_apply, ht,
    hmain, Pi.single_smul, map_smul, hE]
  unfold form
  congr 2
  funext k
  simp only [Function.comp_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]
  generalize Fin.cast _ k = j
  induction j using Fin.addCases with
  | left j => simp [KaehlerDifferential.mapBaseChange_tmul]
  | right j => simp [KaehlerDifferential.mapBaseChange_tmul]

theorem omKun : CrystallineSemistableComparison.Onto.OmKun := by
  intro K A B _ _ _ _ _ c
  let _ : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower K B (A ⊗[K] B) := Algebra.TensorProduct.right_isScalarTower
  obtain ⟨e, he⟩ := omKun_pushout K A B (A ⊗[K] B) c
  refine ⟨e, fun a g₀ g h₀ h => ?_⟩
  rw [he]
  congr 1
  change g₀ ⊗ₜ[K] (1 : B) * (1 : A) ⊗ₜ[K] h₀ = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

end GlobalTheory.CompanionTheory.OmKun
end
end
