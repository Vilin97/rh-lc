module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebungStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopfStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

theorem _root_.GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  first | exact @GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | exact GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective | (intros; apply GlobalTheory.PDiv.comap_map_eq_self_of_hopf_injective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimsLeHeight

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup.CotDim

theorem quot_finrank_le {k A : Type} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {I J : Ideal A} (hIJ : I ≤ J) : Module.finrank k (A ⧸ J) ≤ Module.finrank k (A ⧸ I) := by
  let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top] at this

theorem finrank_level_one {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) :
    Module.finrank k (G.A 1) = p ^ G.height := by
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have h := G.rank_eq 1 q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  simpa using h

end GlobalTheory.PDivGroup.CotDim
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZero

section

@[expose] public section

set_option autoImplicit false

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDivGroup

theorem mulP_mem_kerIdeal_of_verschiebung_eq_zero (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (a : G.A 1) (ha : (verschiebung h G).app 1 a = 0) :
    G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) := by
  let f := (G.mulP 1).comp ((relFrob h G).app 1)
  let K := kerIdeal f
  let x := Ideal.Quotient.mkₐ R K
  have hx := (kerIdeal_le_ker_iff f x).1
    fun c hc => Ideal.Quotient.eq_zero_iff_mem.2 hc
  let y := x.comp ((relFrob h G).app 2 : (frobTwist h G).A 2 →ₐ[R] G.A 2)
  have hy : torsionIdeal (R := R) (A := (frobTwist h G).A 2) p ≤ RingHom.ker y :=
    (kerIdeal_le_ker_iff (mulBy R ((frobTwist h G).A 2) p) y).2 fun z => by
      change x ((relFrob h G).app 2 (mulBy R ((frobTwist h G).A 2) p z)) = _
      rw [← (frobTwist h G).mulP_res 1 z, PDivGroup.app_mulP (relFrob h G)]
      simpa only [f, BialgHom.coe_comp, Function.comp_apply, CoalgHomClass.counit_comp_apply]
        using hx ((frobTwist h G).res 1 z)
  obtain ⟨b, rfl⟩ := G.res_surjective 1 a
  rw [← PDivGroup.res_app (verschiebung h G)] at ha
  have hb : (verschiebung h G).app 2 b ∈ torsionIdeal (R := R) (A := (frobTwist h G).A 2) p := by
    have : (verschiebung h G).app 2 b ∈ torsionIdeal (R := R) (A := (frobTwist h G).A 2) (p ^ 1) := by
      rw [← (frobTwist h G).ker_res 1]
      exact ha
    rwa [pow_one] at this
  have h1 : x ((relFrob h G).app 2 ((verschiebung h G).app 2 b)) = 0 := hy hb
  rw [relFrob_app_verschiebung_app] at h1
  rw [mulP_res]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1

end GlobalTheory.PDivGroup
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZeroStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
      (G : PDivGroup p R) (a : G.A 1),
      (verschiebung h G).app 1 a = 0 →
        G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) :=
  @GlobalTheory.PDivGroup.mulP_mem_kerIdeal_of_verschiebung_eq_zero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIdeStatement

section

@[expose] public section

open GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) :
    kerIdeal ((PDivGroup.relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) :=
  kerIdeal_relFrob_le_frobKerIdeal p R h G n
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimAddDualCotangentDimLeHeight

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.PDivGroup.CotDim in
theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] (hp : (p : k) = 0) (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  letI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hp
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((PDivGroup.relFrob hp Γ.dual).app 1)
  have hcot (G : PDivGroup p k) :
      p ^ Module.finrank k (Cot k (G.A 1)) ≤
        Module.finrank k (G.A 1 ⧸ kerIdeal ((PDivGroup.relFrob hp G).app 1)) :=
    (FrobKerOrder.pow_finrank_cot_le (p := p) (k := k) (H := G.A 1)).trans
      (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp G 1))

  have hker : LinearMap.ker ((PDivGroup.verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (PDivGroup.frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((PDivGroup.relFrob hp Γ).app 1)).restrictScalars k := by
    intro a ha
    have h := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h
    change a ∈ kerIdeal ((PDivGroup.relFrob hp Γ).app 1)
    rw [← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP
      (kerIdeal ((PDivGroup.relFrob hp Γ).app 1))]
    exact h
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((PDivGroup.relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((PDivGroup.relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((PDivGroup.relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((PDivGroup.relFrob hp Γ.dual).app 1 :
        (PDivGroup.frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1
  change _ ≤ p ^ Γ.dual.height
  rw [pow_add, mul_comm, ← hdimD, hord]
  exact Nat.mul_le_mul (hcot Γ.dual) ((hcot Γ).trans hrD)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimAddDualCotangentDimLeHeightStatement

section

@[expose] public section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.cotangent_dim_add_dual_cotangent_dim_le_height : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) ≤ G.height := by
  first | exact @GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero | exact GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero | (intros; apply GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero <;> assumption)
end
end
