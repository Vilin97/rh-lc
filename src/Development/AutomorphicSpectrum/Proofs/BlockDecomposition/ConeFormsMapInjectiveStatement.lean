module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMulPowEqIncl
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyEqPolyEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ToConeSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerFreeConeRing

section

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem free_of_formallyEtale (K A B : Type) [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Algebra A B] [IsScalarTower K A B] [Algebra.FormallyEtale A B] [Module.Free A Ω[A⁄K]] :
    Module.Free B Ω[B⁄K] :=
  (KaehlerDifferential.isBaseChange_of_formallyEtale K A B).free

theorem free_of_bijective {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    (φ : A →ₐ[K] B) (hφ : Function.Bijective φ) [Module.Free A Ω[A⁄K]] : Module.Free B Ω[B⁄K] := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  haveI : Algebra.FormallyEtale A B :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofBijective (Algebra.ofId A B) hφ)
  exact free_of_formallyEtale K A B

variable {K : Type} [Field K] {n d : ℕ}

theorem free_Bp : Module.Free (Bp K n d) Ω[Bp K n d⁄K] :=
  Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis K (E n d))

def cS (k : Fin d) (S : Finset (Fin d)) : Gam n d := ∑ j ∈ S, ratE k j

theorem ratE_inl (k j : Fin d) (l : Fin n) : (ratE k j : Gam n d) (Sum.inl l) = 0 := by
  simp [ratE, oneE]

theorem ratE_inr (k j j' : Fin d) :
    (ratE k j : Gam n d) (Sum.inr j') = (if j' = j then 1 else 0) - (if j' = k then 1 else 0) := by
  simp [ratE, oneE, Pi.single_apply]

theorem cS_inl (k : Fin d) (S : Finset (Fin d)) (l : Fin n) : (cS k S : Gam n d) (Sum.inl l) = 0 := by
  simp [cS, Finset.sum_apply, ratE_inl]

theorem cS_inr (k : Fin d) (S : Finset (Fin d)) {j : Fin d} (hj : j ≠ k) :
    (cS k S : Gam n d) (Sum.inr j) = if j ∈ S then 1 else 0 := by
  simp [cS, Finset.sum_apply, ratE_inr, hj]

theorem tdeg_cS (k : Fin d) (S : Finset (Fin d)) : tdeg (cS k S : Gam n d) = 0 := by
  unfold cS tdeg
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  exact ChartBij.tdeg_ratE k j

theorem cS_mem (k : Fin d) (S : Finset (Fin d)) : (cS k S : Gam n d) ∈ (cone {k} : AddSubmonoid (Gam n d)) :=
  AddSubmonoid.sum_mem _ fun j _ => ratE_mem (Finset.mem_singleton_self k) j

theorem neg_cS_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) :
    -(cS k S : Gam n d) ∈ (cone S : AddSubmonoid (Gam n d)) := by
  refine ⟨fun l => by simp [cS_inl], fun j hj => ?_, ?_⟩
  · have hne : j ≠ k := fun h => hj (h ▸ hk)
    simp [cS_inr k S hne, hj]
  · have h := tdeg_add (cS k S : Gam n d) (-cS k S)
    rw [add_neg_cancel, tdeg_cS] at h
    have h0 : tdeg (0 : Gam n d) = 0 := by simp [tdeg]
    rw [h0] at h
    linarith

theorem exists_add_nsmul_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) (g : Gam n d)
    (hg : g ∈ (cone S : AddSubmonoid (Gam n d))) :
    ∃ N : ℕ, g + N • (cS k S : Gam n d) ∈ (cone {k} : AddSubmonoid (Gam n d)) := by
  refine ⟨∑ j, (g (Sum.inr j)).natAbs, fun l => ?_, fun j hj => ?_, ?_⟩
  · simpa [cS_inl] using hg.1 l
  · have hne : j ≠ k := by simpa using hj
    have hle : (g (Sum.inr j)).natAbs ≤ ∑ j, (g (Sum.inr j)).natAbs :=
      Finset.single_le_sum (f := fun j => (g (Sum.inr j)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [Pi.add_apply, Pi.smul_apply, cS_inr k S hne]
    by_cases hS : j ∈ S
    · simp only [hS, if_true, nsmul_eq_mul, mul_one]
      omega
    · simpa [hS] using hg.2.1 j hS
  · rw [tdeg_add]
    have h : tdeg ((∑ j, (g (Sum.inr j)).natAbs) • (cS k S : Gam n d)) = 0 := by
      have hs : ∀ N : ℕ, tdeg (N • (cS k S : Gam n d)) = 0 := fun N => by
        induction N with
        | zero => simp [tdeg]
        | succ N ih => rw [succ_nsmul, tdeg_add, ih, tdeg_cS, add_zero]
      exact hs _
    rw [h, add_zero]
    exact hg.2.2

theorem free_singleton (k : Fin d) : Module.Free (R0 K n d {k}) Ω[R0 K n d {k}⁄K] := by
  haveI : Module.Free (Bp K n d) Ω[Bp K n d⁄K] := free_Bp
  exact free_of_bijective _ (ChartBij.chart_bijective (K := K) (n := n) k)

theorem free_of_mem {k : Fin d} {S : Finset (Fin d)} (hk : k ∈ S) :
    Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  have hle : (cone {k} : AddSubmonoid (Gam n d)) ≤ cone S :=
    cone_mono (Finset.singleton_subset_iff.2 hk)
  letI : Algebra (R0 K n d {k}) (R0 K n d S) := (incl (K := K) hle).toRingHom.toAlgebra
  haveI : IsScalarTower K (R0 K n d {k}) (R0 K n d S) := IsScalarTower.of_algHom (incl (K := K) hle)
  haveI : IsLocalization.Away (mon K (cS k S) (cS_mem k S)) (R0 K n d S) :=
    Away.isLocalization_away hle (cS k S) (cS_mem k S) (neg_cS_mem hk) fun g hg => exists_add_nsmul_mem hk g hg
  haveI : Algebra.FormallyEtale (R0 K n d {k}) (R0 K n d S) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (mon K (cS k S) (cS_mem k S)))
  haveI : Module.Free (R0 K n d {k}) Ω[R0 K n d {k}⁄K] := free_singleton k
  exact free_of_formallyEtale K (R0 K n d {k}) (R0 K n d S)

theorem free_om : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)),
    Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  intro K _ n d S
  rcases S.eq_empty_or_nonempty with rfl | ⟨k, hk⟩
  · haveI : Module.Free (Bp K n d) Ω[Bp K n d⁄K] := free_Bp
    exact free_of_bijective _ (PolyBij.poly_bijective (K := K) (n := n) (d := d))
  · exact free_of_mem hk

end GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerFreeConeRingStatement

section

@[expose] public section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.kaehler_free_cone_ring : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)), Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjective

section

@[expose] public section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj
open scoped TensorProduct
open GlobalTheory.TopForm

def allE (n d : ℕ) : Gam n d := ∑ e, oneE e

theorem allE_apply {n d : ℕ} (e : E n d) : allE n d e = 1 := by
  classical
  simp [allE, oneE, Finset.sum_apply, Pi.single_apply]

theorem allE_mem {n d : ℕ} (S : Finset (Fin d)) : allE n d ∈ (cone S : AddSubmonoid (Gam n d)) :=
  sum_mem fun e _ => oneE_mem S e

theorem exists_add_nsmul_mem {n d : ℕ} (S : Finset (Fin d)) (g : Gam n d) :
    ∃ N : ℕ, g + N • allE n d ∈ (cone S : AddSubmonoid (Gam n d)) := by
  refine ⟨(∑ e, |g e|).toNat, ?_⟩
  have hall : ∀ e, 0 ≤ (g + (∑ e, |g e|).toNat • allE n d) e := by
    intro e
    have h1 : |g e| ≤ ∑ e, |g e| :=
      Finset.single_le_sum (f := fun e => |g e|) (fun _ _ => abs_nonneg _) (Finset.mem_univ e)
    have h2 : ((∑ e, |g e|).toNat : ℤ) = ∑ e, |g e| :=
      Int.toNat_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    have h3 := neg_abs_le (g e)
    rw [Pi.add_apply, Pi.smul_apply, allE_apply, nsmul_eq_mul, mul_one, h2]
    linarith
  exact ⟨fun _ => hall _, fun _ _ => hall _, Finset.sum_nonneg fun _ _ => hall _⟩

theorem injective_of_isBaseChange {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module.Flat A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] {f : M →ₗ[A] N} (hf : IsBaseChange B f)
    (hinj : Function.Injective (algebraMap A B)) : Function.Injective f := by
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap A B) hinj
  intro x y hxy
  have h3 : (1 : B) ⊗ₜ[A] x = (1 : B) ⊗ₜ[A] y := by
    apply hf.equiv.injective
    simp [IsBaseChange.equiv_tmul, hxy]
  have h4 : (1 : A) ⊗ₜ[A] x = (1 : A) ⊗ₜ[A] y := by
    apply h2
    simpa using h3
  simpa using congrArg (TensorProduct.lid A M) h4

theorem omMap_incl_injective : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ),
    Function.Injective (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) := by
  intro K _ n d S a
  letI : Algebra (R0 K n d S) (Lr K n d) :=
    (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)).toRingHom.toAlgebra
  haveI : IsScalarTower K (R0 K n d S) (Lr K n d) :=
    IsScalarTower.of_algHom (incl (K := K) (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤))
  haveI hl : IsLocalization.Away (mon K (allE n d) (allE_mem S)) (Lr K n d) :=
    Away.isLocalization_away le_top (allE n d) (allE_mem S) (AddSubmonoid.mem_top _)
      (fun g _ => exists_add_nsmul_mem S g)
  haveI : Algebra.FormallyEtale (R0 K n d S) (Lr K n d) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (mon K (allE n d) (allE_mem S)))
  have hb := KaehlerDifferential.isBaseChange_of_formallyEtale K (R0 K n d S) (Lr K n d)
  have hE := GlobalTheory.TopForm.isBaseChange_exteriorPower hb a
  haveI : Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := GlobalTheory.T.kaehler_free_cone_ring S
  have hinj := injective_of_isBaseChange hE (Away.incl_injective le_top)
  have heq : ∀ ω, omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a ω =
      exteriorPowerMapOver (Lr K n d) a (KaehlerDifferential.map K K (R0 K n d S) (Lr K n d)) ω := by
    intro ω
    have hs : ω ∈ (⊤ : Submodule (R0 K n d S) (Om K (R0 K n d S) a)) := trivial
    rw [← exteriorPower.ιMulti_span] at hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [omMap_ιMulti, exteriorPowerMapOver_ιMulti]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [omMap_smul, hx, map_smul]
      exact algebraMap_smul (Lr K n d) c _
  intro x y hxy
  exact hinj (by rw [← heq, ← heq, hxy])

end GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeFormsMapInjectiveStatement

section

@[expose] public section

open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

theorem _root_.GlobalTheory.T.cone_forms_map_injective : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (a : ℕ), Function.Injective (omMap (K := K) (incl (le_top : (cone S : AddSubmonoid (Gam n d)) ≤ ⊤)) a) := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.OmlInj.omMap_incl_injective <;> assumption)
end
end
