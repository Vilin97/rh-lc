module

public import Formalism.CharacterColumnKernels.StatementPsi
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SmulYGenEqZero
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.WachLatticeTwists.CoprimeLiftBounds.SelmerInjColumnPlace

section

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

def SelmerInjTensorForm : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (D : Type*) [Group D] (L V M : Type*) [AddCommGroup L] [Module O L] [AddCommGroup V]
    [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    [AddCommGroup M] [Module O M]
    (ρL : Representation O D L) (ρV : Representation (FractionRing O) D V)
    (ρM : Representation O D M) (i : L →ₗ[O] V) (q : V →ₗ[O] M)
    (tens : L →ₗ[O] KO O →ₗ[O] M),
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = q (x • i v)) →
    Function.Injective i → Function.Surjective q → LinearMap.ker q = LinearMap.range i →
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range i) →
    (∀ g v, i (ρL g v) = ρV g (i v)) → (∀ g v, q (ρV g v) = ρM g (q v)) →
    ∀ (Ff : Submodule O (H1z ρL)) (j : ℕ) (κ : Fin j → coZ1s ρL),
    (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff → z ∈ Ff) →
    (∀ a, (Submodule.mkQ _ (κ a) : H1z ρL) ∈ Ff) →
    (∀ z ∈ Ff, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL)) = 0) →
    (∀ (b : Fin j → O) (c : O), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) = 0 → b = 0) →
    ∀ (x : Fin j → KO O) (m : M),
      (∀ g, ∑ a, tens ((κ a : D → L) g) (x a) = ρM g m - m) → ∀ a, x a = 0

def SelmerInjColumnPlace : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (V : Type*) [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [SMulCommClass A (FractionRing O) V]
    (r : G →* A) (χ : G →* T'ˣ) (Dl : Subgroup G) (i : L →ₗ[O] V) (q : V →ₗ[O] M)
    (tens : L →ₗ[O] KO O →ₗ[O] M),
    (∀ (a : A) v, i (a • v) = a • i v) → (∀ (a : A) v, q (a • v) = a • q v) →
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = q (x • i v)) →
    Function.Injective i → Function.Surjective q → LinearMap.ker q = LinearMap.range i →
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range i) →
    ∀ (Ff : Submodule O (H1z (resRep (uRep O (M := L) r χ) Dl))) (j : ℕ) (κ : Fin j → G → L)
      (κz : Fin j → coZ1s (resRep (uRep O (M := L) r χ) Dl)),
    (∀ a (g : Dl), (κz a : Dl → L) g = κ a g) →
    (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff → z ∈ Ff) →
    (∀ a, Submodule.mkQ _ (κz a) ∈ Ff) →
    (∀ z ∈ Ff, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κz a) : H1z (resRep (uRep O (M := L) r χ) Dl))) = 0) →
    (∀ (b : Fin j → O) (c : O), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (κz a) : H1z (resRep (uRep O (M := L) r χ) Dl)) = 0 →
      b = 0) →
    ∀ x : Fin j → KO O, (fun g : Dl => ∑ a, tens (κ a g) (x a)) ∈
      LinearMap.range (colDO (O := O) (M := M) r χ Dl) → ∀ a, x a = 0

end Formalism.RepresentationBoundsCohomology.BR
end
end
end

-- Source module: Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.Imports

section

@[expose] public section

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem c3 : SelmerFInjective := by
  intro O _ _ _ D _ L V M _ _ _ _ _ _ _ _ ρL ρV ρM i q hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4
    x m hx

  obtain ⟨⟨c, hc⟩, hcx⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin j)) x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcx' : ∀ a, ∃ t : O, algebraMap O (FractionRing O) t = c • x a :=
    fun a => RingHom.mem_rangeS.mp (hcx a (Finset.mem_univ a))
  choose y hy using hcx'
  obtain ⟨v, rfl⟩ := hq m
  obtain ⟨d, hd0, hw'⟩ := hsat (c • v)
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hw'
  have he0 : d * c ≠ 0 := mul_ne_zero hd0 hc0
  have hK0 : algebraMap O (FractionRing O) (d * c) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr he0

  have cancelV : ∀ u u' : V, (d * c) • u = (d * c) • u' → u = u' := by
    intro u u' h
    rw [← algebraMap_smul (FractionRing O) (d * c) u, ← algebraMap_smul (FractionRing O) (d * c) u'] at h
    exact smul_right_injective V hK0 h
  have cancelL : ∀ a b : L, (d * c) • a = (d * c) • b → a = b := by
    intro a b h
    apply hi
    apply cancelV
    have h' := congrArg i h
    rwa [map_smul, map_smul] at h'

  have hf : ∀ g : D, ∃ zg : L, i zg = ∑ a, x a • i ((κ a : D → L) g) - (ρV g v - v) := by
    intro g
    have hmem : ∑ a, x a • i ((κ a : D → L) g) - (ρV g v - v) ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, map_sub, hx g, hqρ]
      exact sub_self _
    rw [hker] at hmem
    exact LinearMap.mem_range.mp hmem
  choose z hz using hf
  obtain ⟨Y, hYdef⟩ : ∃ Y : coZ1s ρL, Y = ∑ a, (d * y a) • κ a - cobZ ρL w := ⟨_, rfl⟩
  have hYg : ∀ g, (Y : D → L) g = ∑ a, (d * y a) • (κ a : D → L) g - (ρL g w - w) := by
    intro g
    rw [hYdef, Submodule.coe_sub, Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply]
    rfl
  have hY : ∀ g, (d * c) • z g = (Y : D → L) g := by
    intro g
    apply hi

    rw [hYg g, map_smul, hz g, map_sub, map_sub, map_sum, hiρ, hw, smul_sub, smul_sub, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, mul_smul, mul_smul, ← smul_assoc c (x a), ← hy a, algebraMap_smul]
    · rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, mul_smul, mul_smul]

  have hzc : z ∈ coZ1s ρL := by
    show ∀ g h, z (g * h) = z g + ρL g (z h)
    intro g h
    apply cancelL
    rw [smul_add, ← map_smul, hY, hY, hY]
    exact Y.2 g h
  have hZY : (d * c) • (⟨z, hzc⟩ : coZ1s ρL) = Y := Subtype.ext (funext hY)
  have hYcl : (Submodule.mkQ _ Y : H1z ρL) = ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) := by

    rw [hYdef, map_sub, mkQ_cobZ, sub_zero, map_sum]
    simp only [map_smul]
  have h2 : (d * c) • (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) =
      ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    rw [← map_smul, hZY, hYcl]
  have hZF : (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) ∈ Ff := by
    apply hF1 (d * c) _ he0
    rw [h2]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hF2 a)
  obtain ⟨b, c', hc'0, hc'⟩ := hF3 _ hZF
  have h1 : c' • (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) =
      c' • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    rw [smul_sub, sub_eq_zero] at hc'
    exact hc'
  have hsplit : ∑ a, (d * y a - d * c * b a) • (Submodule.mkQ _ (κ a) : H1z ρL) =
      ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) -
        (d * c) • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, Finset.smul_sum]
  have h3 : c' • ∑ a, (d * y a - d * c * b a) • (Submodule.mkQ _ (κ a) : H1z ρL) = 0 := by
    rw [hsplit, ← h2, smul_sub, smul_comm c' (d * c), h1, smul_comm c' (d * c), sub_self]
  have hb := hF4 (fun a => d * y a - d * c * b a) c' hc'0 h3
  intro a
  have h4 : d * y a - d * c * b a = 0 := congrFun hb a
  have h5 : y a = c * b a := by
    apply mul_left_cancel₀ hd0
    rw [← mul_assoc]
    exact sub_eq_zero.mp h4
  have hc'' : algebraMap O (FractionRing O) c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hc0
  rw [Submodule.mem_one]
  refine ⟨b a, ?_⟩
  apply mul_left_cancel₀ hc''
  rw [← map_mul, ← h5, hy a, Algebra.smul_def]

end Formalism.RepresentationBoundsCohomology.BR
end
end
end

-- Source module: Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SelmerInjColumnPlace

section

@[expose] public section

open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem selmer_inj_tensor_form : SelmerInjTensorForm := by
  intro O _ _ _ D _ L V M _ _ _ _ _ _ _ _ ρL ρV ρM i q tens htens hi hq hker hsat hiρ hqρ Ff j κ
    hF1 hF2 hF3 hF4 x m hx a
  choose y hy using fun b => Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (x b)
  have hsum : ∀ g, q (∑ b, y b • i ((κ b : D → L) g)) = ρM g m - m := by
    intro g

    rw [← hx g, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hy b, htens]
  have key := c3 O D L V M ρL ρV ρM i q hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4 y m hsum a
  rw [← hy a]
  exact (Submodule.Quotient.mk_eq_zero _).mpr key

theorem selmer_inj_column_place : SelmerInjColumnPlace := by
  intro O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ _ V _ _ _ _ _ _ r χ Dl i q tens hiA hqA htens hi hq
    hker hsat Ff j κ κz hκ hF1 hF2 hF3 hF4 x hx
  obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hx
  refine selmer_inj_tensor_form O Dl L V M (resRep (uRep O (M := L) r χ) Dl)
    (resRep (uRep (FractionRing O) (M := V) r χ) Dl) (resRep (uRep O (M := M) r χ) Dl) i q tens
    htens hi hq hker hsat ?_ ?_ Ff j κz hF1 hF2 hF3 hF4 x m ?_
  · intro g v
    exact hiA (uElt r χ (g : G)) v
  · intro g v
    exact hqA (uElt r χ (g : G)) v
  · intro g
    have h1 := congrFun hm g
    simp only [hκ]
    exact h1.symm

end Formalism.RepresentationBoundsCohomology.BR
end
end
end
