module

public import Formalism.LogFactorialIndices.StatementIdx
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
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Formalism.IncomingBounds.IndexLastStep

section

@[expose] public section

noncomputable section

namespace Formalism.IncomingBounds

open Module

def IndexLastStep : Prop :=
  ∀ (O K X : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]
    [FiniteDimensional K X] (ϖ : O), Irreducible ϖ →
    ∀ (e : ℤ) (M Θ : Submodule O X), Formalism.LatticeIndexTer.IsLat O K X M → Formalism.LatticeIndexTer.IsLat O K X Θ →
      ∀ W : Submodule K X,
        Formalism.LatticeIndexTer.idx O X (M ⊓ W.restrictScalars O) (Θ ⊓ W.restrictScalars O) ≤
          e * (finrank K W : ℤ) +
            ((Formalism.LatticeIndexTer.qlen O X
              (M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O) ⊔ Θ)
              Θ).toNat : ℤ)

end Formalism.IncomingBounds
end
end
end

-- Source module: Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndex

section

@[expose] public section

open scoped Pointwise

noncomputable section

namespace Formalism.LatticeIndexTer.subgroupData

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

theorem length_le_of_le {S T A B : Submodule O X} (hST : S ≤ T) (hBA : B ≤ A)
    (hSA : S ⊓ A ≤ B) :
    Module.length O (S ⧸ B.comap S.subtype) ≤ Module.length O (T ⧸ A.comap T.subtype) := by
  let f : (S ⧸ B.comap S.subtype) →ₗ[O] (T ⧸ A.comap T.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hST) (fun x hx => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_inclusion] at hx ⊢
      exact hBA hx)
  apply Module.length_le_of_injective f
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [f, Submodule.mapQ_apply] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  simp only [Submodule.mem_comap, Submodule.coe_subtype, map_sub, Submodule.coe_inclusion]
    at hxy ⊢
  exact hSA (Submodule.mem_inf.mpr ⟨S.sub_mem x.2 y.2, hxy⟩)

theorem qlen_eq_zero {A B : Submodule O X} (h : A ≤ B) : qlen O X A B = 0 := by
  unfold qlen
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.Quotient.eq]
  exact h (a - b).2

end Formalism.LatticeIndexTer.subgroupData

namespace Formalism.LatticeIndexTer

open Formalism.LatticeIndexTer.subgroupData

end Formalism.LatticeIndexTer
end
end
end

-- Source module: Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndexSigned

section

@[expose] public section

noncomputable section

open Module
open scoped Pointwise

namespace Formalism.LatticeIndexTer.LatticeIndexValuation

theorem length_map_inj {O Y X : Type} [CommRing O] [AddCommGroup Y] [Module O Y]
    [AddCommGroup X] [Module O X] (ι : Y →ₗ[O] X) (hι : Function.Injective ι)
    (P Q : Submodule O Y) :
    Module.length O (P ⧸ Q.comap P.subtype) =
      Module.length O (P.map ι ⧸ (Q.map ι).comap (P.map ι).subtype) := by
  have e : (Q.comap P.subtype).map (Submodule.equivMapOfInjective ι hι P).toLinearMap =
      (Q.map ι).comap (P.map ι).subtype := by
    ext ⟨z, hz⟩
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hz
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨⟨w, hw⟩, hwQ, hwe⟩
      refine ⟨w, hwQ, ?_⟩
      have := congrArg Subtype.val hwe
      first
        | exact this
        | simpa using this
    · rintro ⟨w, hwQ, hwe⟩
      refine ⟨⟨y, hy⟩, ?_, ?_⟩
      · have : w = y := hι hwe
        simpa [this] using hwQ
      · ext
        rfl
  exact (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective ι hι P) e).length_eq

end Formalism.LatticeIndexTer.LatticeIndexValuation

namespace Formalism.LatticeIndexTer.LatticeIndexValuation

section Sub

variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]

theorem isLat_comap (A : Submodule O X) (hA : IsLat O K X A) (W : Submodule K X) :
    IsLat O K W (A.comap ((W.subtype).restrictScalars O)) := by
  let ι : W →ₗ[O] X := (W.subtype).restrictScalars O
  have hι : Function.Injective ι := Subtype.val_injective
  constructor
  · have : Module.Finite O A := Module.Finite.iff_fg.mpr hA.1
    have hle : (A.comap ι).map ι ≤ A := Submodule.map_comap_le ι A
    have : IsNoetherian O ((A.comap ι).map ι) := isNoetherian_of_le hle
    have hfg : ((A.comap ι).map ι).FG := Module.Finite.iff_fg.mp inferInstance
    exact Submodule.fg_of_fg_map_injective ι hι hfg
  · rw [eq_top_iff]
    rintro w -
    obtain ⟨d, hd, hdw⟩ := LatticeIndexLength.exists_smul_mem_of_span (K := K) A hA.2 (w : X)
    have hdK : algebraMap O K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hd
    have hmem : d • w ∈ Submodule.span K (A.comap ι : Set W) := by
      apply Submodule.subset_span
      show ((d • w : W) : X) ∈ A
      rw [Submodule.coe_smul_of_tower]
      exact hdw
    have hw : w = (algebraMap O K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, smul_smul, inv_mul_cancel₀ hdK, one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ hmem

end Sub

end Formalism.LatticeIndexTer.LatticeIndexValuation

namespace Formalism.LatticeIndexTer

open LatticeIndexValuation

end Formalism.LatticeIndexTer
end
end
end

-- Source module: Formalism.IncomingBounds.FlowDegreeBounds.IndexLastReductionHolds

section

@[expose] public section

noncomputable section

open Module
open scoped Pointwise

namespace Formalism.IncomingBounds.LatticeIndexAlt

open Formalism.LatticeIndexTer

variable {O K X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X]
  [IsScalarTower O K X]

theorem map_comap_sub (W : Submodule K X) (A : Submodule O X) :
    (A.comap ((W.subtype).restrictScalars O)).map ((W.subtype).restrictScalars O) =
      A ⊓ W.restrictScalars O := by
  ext x
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_inf, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.2⟩
  · rintro ⟨hx, hW⟩
    exact ⟨⟨x, hW⟩, hx, rfl⟩

theorem qlen_comap (W : Submodule K X) (A B : Submodule O X) :
    qlen O W (A.comap ((W.subtype).restrictScalars O)) (B.comap ((W.subtype).restrictScalars O)) =
      qlen O X (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) := by
  unfold qlen
  have hinj : Function.Injective ((W.subtype).restrictScalars O) := fun a b h => Subtype.ext h
  let e : ↥(A.comap ((W.subtype).restrictScalars O)) ≃ₗ[O] ↥(A ⊓ W.restrictScalars O) :=
    (Submodule.equivMapOfInjective _ hinj _).trans (LinearEquiv.ofEq _ _ (map_comap_sub W A))
  refine LinearEquiv.length_eq (Submodule.Quotient.equiv _ _ e ?_)
  ext z
  rw [Submodule.mem_map_equiv]
  have key : (((e.symm z : ↥(A.comap ((W.subtype).restrictScalars O))) : W) : X) = (z : X) :=
    congrArg Subtype.val (e.apply_symm_apply z)
  have hzW : (z : X) ∈ W := (Submodule.mem_inf.mp z.2).2
  constructor
  · intro h
    have h' : (((e.symm z : ↥(A.comap ((W.subtype).restrictScalars O))) : W) : X) ∈ B := h
    rw [key] at h'
    show (z : X) ∈ B ⊓ W.restrictScalars O
    exact Submodule.mem_inf.mpr ⟨h', hzW⟩
  · intro h
    have h2 : (z : X) ∈ B ⊓ W.restrictScalars O := h
    have h' : (z : X) ∈ B := (Submodule.mem_inf.mp h2).1
    rw [← key] at h'
    exact h'

theorem idx_comap (W : Submodule K X) (A B : Submodule O X) :
    idx O W (A.comap ((W.subtype).restrictScalars O)) (B.comap ((W.subtype).restrictScalars O)) =
      idx O X (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) := by
  unfold idx
  rw [qlen_comap W A B, qlen_comap W B A]


omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem isLat_scale {Y : Type} [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y]
    (c : K) (hc : c ≠ 0) (A : Submodule O Y) (hA : IsLat O K Y A) :
    IsLat O K Y (A.map ((c • LinearMap.id : Y →ₗ[K] Y).restrictScalars O)) := by
  unfold IsLat at hA ⊢
  refine ⟨hA.1.map _, ?_⟩
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hA.2, Submodule.map_top,
    LinearMap.range_eq_top]
  intro x
  refine ⟨c⁻¹ • x, ?_⟩
  simp [smul_smul, hc]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
theorem isLat_sup {Y : Type} [AddCommGroup Y] [Module K Y] [Module O Y] [IsScalarTower O K Y]
    (A B : Submodule O Y) (hA : A.FG) (hB : IsLat O K Y B) : IsLat O K Y (A ⊔ B) := by
  unfold IsLat at hB ⊢
  refine ⟨hA.sup hB.1, ?_⟩
  rw [eq_top_iff, ← hB.2]
  exact Submodule.span_mono (fun x hx => Submodule.mem_sup_right hx)

end Formalism.IncomingBounds.LatticeIndexAlt

namespace Formalism.IncomingBounds

open Formalism.LatticeIndexTer LatticeIndexAlt

theorem index_last_reduction_holds : IndexLastStep := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ e M Θ hM hΘ W
  rw [← idx_comap W M Θ]
  have hc : (algebraMap O K ϖ) ^ e ≠ 0 :=
    zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero)
  have hNl := isLat_sup (K := K)
    (M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O)) Θ
    (hM.1.map _) hΘ
  generalize hN : M.map ((((algebraMap O K ϖ) ^ e) • LinearMap.id : X →ₗ[K] X).restrictScalars O)
    ⊔ Θ = N at hNl ⊢
  have hMN : ∀ x ∈ M, (algebraMap O K ϖ) ^ e • x ∈ N := by
    intro x hx
    rw [← hN]
    exact Submodule.mem_sup_left ⟨x, hx, by simp⟩
  have hΘN : Θ ≤ N := hN ▸ le_sup_right
  let ι : W →ₗ[O] X := (W.subtype).restrictScalars O
  have hι : Function.Injective ι := Subtype.val_injective
  let fW : W →ₗ[O] W := ((((algebraMap O K ϖ) ^ e) • LinearMap.id : W →ₗ[K] W).restrictScalars O)
  have hA₀ : IsLat O K W (M.comap ι) := LatticeIndexValuation.isLat_comap M hM W
  have hB₀ : IsLat O K W (Θ.comap ι) := LatticeIndexValuation.isLat_comap Θ hΘ W
  have hN₀ : IsLat O K W (N.comap ι) := LatticeIndexValuation.isLat_comap N hNl W
  have hS₀ : IsLat O K W ((M.comap ι).map fW) := isLat_scale _ hc _ hA₀
  have hadd1 := lattice_index_add O K W (M.comap ι) ((M.comap ι).map fW) (Θ.comap ι) hA₀ hS₀ hB₀
  have hadd2 := lattice_index_add O K W ((M.comap ι).map fW) (N.comap ι) (Θ.comap ι) hS₀ hN₀ hB₀
  have h1 : idx O W (M.comap ι) ((M.comap ι).map fW) = e * (finrank K W : ℤ) := by
    have hs := lattice_index_scale O K W ϖ hϖ (-e) (M.comap ι) hA₀
    rw [neg_neg] at hs
    exact hs
  have hSN : (M.comap ι).map fW ≤ N.comap ι := by
    rintro _ ⟨y, hy, rfl⟩
    have := hMN _ hy
    simpa [ι, fW] using this
  have h2 : idx O W ((M.comap ι).map fW) (N.comap ι) ≤ 0 := by
    unfold idx
    rw [subgroupData.qlen_eq_zero hSN]
    simp
  have hle : qlen O W (N.comap ι) (Θ.comap ι) ≤ qlen O X N Θ := by
    unfold qlen
    rw [LatticeIndexValuation.length_map_inj ι hι]
    refine subgroupData.length_le_of_le (Submodule.map_comap_le ι N) (Submodule.map_comap_le ι Θ) ?_
    intro x hx
    obtain ⟨⟨w, -, rfl⟩, hxΘ⟩ := Submodule.mem_inf.mp hx
    exact ⟨w, hxΘ, rfl⟩
  have h3 : idx O W (N.comap ι) (Θ.comap ι) ≤ ((qlen O X N Θ).toNat : ℤ) := by
    have h4 : (qlen O W (N.comap ι) (Θ.comap ι)).toNat ≤ (qlen O X N Θ).toNat :=
      ENat.toNat_le_toNat hle (lattice_quotient_finite O K X N Θ hNl hΘ)
    unfold idx
    omega
  linarith

end Formalism.IncomingBounds
end
end
end
