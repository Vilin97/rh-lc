module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LastRescaleOf
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsBasisLocF
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DetUnitOfSelfdual
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueInlInl
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SpanPowMulLe
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsLocUnif
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NondegOnOfCompl
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFSubspace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SmulMemLocFOfSP
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EquivFunEquivOfMatrixSymm

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LinIndOrth

section

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.NormUnitsOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def NU (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (x : K) : Prop :=
  ∃ l : K, l ≠ 0 ∧ x * (l * star l) ∈ SP K 𝔭 ∧ (x * (l * star l))⁻¹ ∈ SP K 𝔭

variable {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime]

theorem NU.of_unit {u : K} (h1 : u ∈ SP K 𝔭) (h2 : u⁻¹ ∈ SP K 𝔭) : NU 𝔭 u :=
  ⟨1, one_ne_zero, by simpa using h1, by simpa using h2⟩

theorem NU.mul {x y : K} (hx : NU 𝔭 x) (hy : NU 𝔭 y) : NU 𝔭 (x * y) := by
  obtain ⟨a, ha, ha1, ha2⟩ := hx
  obtain ⟨b, hb, hb1, hb2⟩ := hy
  have e : x * y * (a * b * star (a * b)) = (x * (a * star a)) * (y * (b * star b)) := by
    rw [star_mul']
    ring
  refine ⟨a * b, mul_ne_zero ha hb, ?_, ?_⟩
  · rw [e]
    exact (SP K 𝔭).mul_mem ha1 hb1
  · rw [e, mul_inv]
    exact (SP K 𝔭).mul_mem ha2 hb2

theorem NU.inv {x : K} (hx : NU 𝔭 x) : NU 𝔭 x⁻¹ := by
  obtain ⟨a, ha, h1, h2⟩ := hx
  have hs : star a⁻¹ = (star a)⁻¹ := by
    first | exact star_inv₀ a | exact star_inv' a | simp
  have e : x⁻¹ * (a⁻¹ * star a⁻¹) = (x * (a * star a))⁻¹ := by
    rw [hs, mul_inv, mul_inv]
  refine ⟨a⁻¹, inv_ne_zero ha, ?_, ?_⟩
  · rw [e]
    exact h2
  · rw [e, inv_inv]
    exact h1

theorem NU.of_mul_left {x y : K} (hxy : NU 𝔭 (x * y)) (hy : NU 𝔭 y) (hy0 : y ≠ 0) : NU 𝔭 x := by
  have h := NU.mul hxy (NU.inv hy)
  rwa [mul_assoc, mul_inv_cancel₀ hy0, mul_one] at h

theorem NU.norm_mul {u z : K} (h1 : u ∈ SP K 𝔭) (h2 : u⁻¹ ∈ SP K 𝔭) (hz : z ≠ 0) :
    NU 𝔭 (star z * u * z) := by
  have hs : star z⁻¹ = (star z)⁻¹ := by
    first | exact star_inv₀ z | exact star_inv' z | simp
  have hsz : star z ≠ 0 := by
    first | exact star_ne_zero.2 hz | simpa using hz
  have e : star z * u * z * (z⁻¹ * star z⁻¹) = u := by
    rw [hs]
    calc star z * u * z * (z⁻¹ * (star z)⁻¹) = u * (z * z⁻¹) * (star z * (star z)⁻¹) := by ring
      _ = u := by rw [mul_inv_cancel₀ hz, mul_inv_cancel₀ hsz, mul_one, mul_one]
  refine ⟨z⁻¹, inv_ne_zero hz, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e]
    exact h2

theorem NU.prod {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, NU 𝔭 (f i)) :
    NU 𝔭 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (NU 𝔭) (fun _ _ ha hb => NU.mul ha hb)
    (NU.of_unit (SP K 𝔭).one_mem (by rw [inv_one]; exact (SP K 𝔭).one_mem)) hf

theorem NU.pair {A C : K} (hA : A ≠ 0) (hAs : star A = A) (h1 : C * A⁻¹ ∈ SP K 𝔭)
    (h2 : A * C⁻¹ ∈ SP K 𝔭) : NU 𝔭 (A * C) := by
  have hs : star A⁻¹ = (star A)⁻¹ := by
    first | exact star_inv₀ A | exact star_inv' A | simp
  have e : A * C * (A⁻¹ * star A⁻¹) = C * A⁻¹ := by
    rw [hs, hAs]
    calc A * C * (A⁻¹ * A⁻¹) = C * A⁻¹ * (A * A⁻¹) := by ring
      _ = C * A⁻¹ := by rw [mul_inv_cancel₀ hA, mul_one]
  refine ⟨A⁻¹, inv_ne_zero hA, ?_, ?_⟩
  · rw [e]
    exact h1
  · rw [e, mul_inv, inv_inv, mul_comm]
    exact h2

section Vec

variable {V : Type} [AddCommGroup V] [Module K V]

theorem linInd_orth {ι : Type} {h : V →ₗ⋆[K] V →ₗ[K] K} (g : ι → V)
    (ho : ∀ s t, s ≠ t → h (g s) (g t) = 0) (hn : ∀ s, h (g s) (g s) ≠ 0) : LinearIndependent K g := by
  rw [linearIndependent_iff']
  intro s c hs i hi
  have key := congrArg (h (g i)) hs

  rw [map_sum, map_zero, Finset.sum_eq_single i] at key
  · rw [map_smul, smul_eq_mul] at key
    exact (mul_eq_zero.1 key).resolve_right (hn i)
  · intro j _ hji
    rw [map_smul, ho i j (Ne.symm hji), smul_zero]
  · intro hi'
    exact absurd hi hi'

end Vec

end Formalism.L2.SG.Pf.NormUnitsOrthogonality
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NormUnits

section

@[expose] public section

open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions
  Formalism.L2.SG.Pf.GluedFormOrthogonality Formalism.L2.SG.Pf.NormUnitsOrthogonality

theorem last_unit_holds : LastUnit := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hCM hFix h hS hN U hUc _ hΛ M _ _ 𝔭 h𝔭 b a hJ _ π w c τ hG j hj
  classical
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨hwU, hwo, hwn, hτinj, ⟨s₀, hU0⟩, hpair, hτlt, hfree⟩ := hG
  obtain ⟨hbU, hbloc, hbo, hbn, ha0⟩ := hJ
  obtain ⟨Λ₀, hΛlat, hΛu⟩ := hΛ
  have hA0 : ∀ i, algebraMap F K (a i : F) ≠ 0 := fun i => by
    rw [map_ne_zero]
    exact_mod_cast ha0 i
  have hC0 : ∀ k, algebraMap F K (c k) ≠ 0 := fun k => by
    rw [map_ne_zero]
    exact (hwn k).2
  have hπ0 : π ≠ 0 := fun e => hU0.notMem (e ▸ Submodule.zero_mem _)
  have hP0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hπ0
  have hSPπ : algebraMap F K (π : F) ∈ SP K 𝔭 := by
    have := mem_SP_of_inP (K := K) hU0 (inP_of_mem_pow (K := K) (k := 0) (t := π) (by simp))
    simpa using this
  have hcard : Fintype.card (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) = finrank K V := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Submodule.finrank_add_eq_of_isCompl hUc]
  haveI : Nonempty (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) := ⟨Sum.inr j⟩
  let g : Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) → V := Sum.elim b w
  have horth : ∀ s t, s ≠ t → h (g s) (g t) = 0 := by
    rintro (i|i) (k|k) hst
    · exact hbo i k (fun e => hst (congrArg Sum.inl e))
    · exact form_U_orth (hbU i) (hwU k)
    · exact form_orth_U hS (hbU k) (hwU i)
    · exact hwo i k (fun e => hst (congrArg Sum.inr e))
  have hnorm : ∀ s, h (g s) (g s) ≠ 0 := by
    rintro (i|i)
    · show h (b i) (b i) ≠ 0
      rw [hbn i]
      exact hA0 i
    · show h (w i) (w i) ≠ 0
      rw [(hwn i).1]
      exact hC0 i
  have hli : LinearIndependent K g := linInd_orth g horth hnorm
  let γ := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hγ : ∀ s, γ s = g s := fun s =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) s
  have hdetγ : (gramK h γ).det =
      (∏ i, algebraMap F K (a i : F)) * ∏ k, algebraMap F K (c k) := by
    rw [gram_det_orth h γ (fun s t hst => by rw [hγ, hγ]; exact horth s t hst), Fintype.prod_sum_type]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => by rw [hγ]; exact hbn i)
    · exact Finset.prod_congr rfl (fun k _ => by rw [hγ]; exact (hwn k).1)
  have hfull : Submodule.IsFullLattice K Λ₀ := by
    refine { toIsLattice := hΛlat, span_eq_top := ?_ }
    obtain ⟨S, hS⟩ := hΛlat.fg
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors (𝓞 K)) (Finset.image (fun p : V × _ => h p.1 (γ p.2)) (S ×ˢ Finset.univ))
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      exact fun e => (nonZeroDivisors.ne_zero hd) (IsFractionRing.injective (𝓞 K) K (by simpa using e))
    have hmem : ∀ i, d • γ i ∈ Λ₀ := by
      intro i
      rw [← hΛu]
      simp only [HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf,
        Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
      intro y hy
      have key : ∀ y ∈ Submodule.span (𝓞 K) (S : Set V),
          ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = h y (d • γ i) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨r, hr⟩ := hint (h y (γ i)) (Finset.mem_image.mpr ⟨(y, i), Finset.mem_product.mpr ⟨hy, Finset.mem_univ _⟩, rfl⟩)
          refine ⟨r, ?_⟩
          rw [← algebraMap_smul K d, LinearMap.map_smul, smul_eq_mul]
          exact hr
        | zero => exact ⟨0, by simp⟩
        | add x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          exact ⟨a + b, by simp only [map_add, LinearMap.add_apply, ha, hb]⟩
        | smul a x _ hx =>
          obtain ⟨b, hb⟩ := hx
          obtain ⟨a', ha'⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range a
          refine ⟨a' * b, ?_⟩
          rw [map_mul, ha', hb, ← algebraMap_smul K a x, LinearMap.map_smulₛₗ₂]
          simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
      exact key y (by rw [hS]; exact hy)
    rw [eq_top_iff]
    intro x _
    rw [← γ.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi : γ i ∈ Submodule.span K (Λ₀ : Set V) := by
      have : γ i = (algebraMap (𝓞 K) K d)⁻¹ • (d • γ i) := by
        rw [← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hdK, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem i))
    exact Submodule.smul_mem _ _ hi
  obtain ⟨β, -, hβ⟩ := LocalSpans.exists_basis_locF hfull h𝔭
  let e : Fin (finrank K V) ≃ Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard])
  let β' := β.reindex e
  have hsp : spanO β' = Submodule.span (𝓞 K) (Set.range β) := by
    show Submodule.span (𝓞 K) (Set.range ⇑(β.reindex e)) = _
    rw [Basis.range_reindex]
  have hsd : dualF h 𝔭 (locF 𝔭 (spanO β')) = locF 𝔭 (spanO β') := by
    rw [hsp, hβ, ← G7.locF_dual hFix h hΛlat.fg h𝔭.isPrime, (hΛu : HermitianLatticesTheory.dual h Λ₀ = Λ₀)]
  obtain ⟨hu1, hu2⟩ := det_unit_of_selfdual hFix hS hN β' hsd
  have hd : (β'.toMatrix γ).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip β' γ)
  have hNUγ : NU 𝔭 (gramK h γ).det := by
    rw [gram_det_change h β' γ]
    exact NU.norm_mul hu1 hu2 hd
  have hunitA : ∀ i, vF 𝔭 (a i) = 0 → NU 𝔭 (algebraMap F K (a i : F)) := by
    intro i hv
    apply NU.of_unit
    · have := mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))
      rw [hv] at this
      simpa using this
    · have := unit_part hCM hFix h𝔭 hU0 (ha0 i)
      rw [hv] at this
      simpa using this
  have hunitC : ∀ k : Fin (finrank K (orthK h U)), (k : ℕ) + 1 < finrank K (orthK h U) →
      (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ k) → NU 𝔭 (algebraMap F K (c k)) := by
    intro k hk hk'
    obtain ⟨h1, h2⟩ := hfree k hk hk'
    apply NU.of_unit
    · simpa using mem_SP_of_inP (K := K) hU0 h1
    · simpa using mem_SP_of_inP (K := K) hU0 h2
  have hpairNU : ∀ i, vF 𝔭 (a i) ≠ 0 →
      NU 𝔭 (algebraMap F K (a i : F) * algebraMap F K (c (τ i))) := by
    intro i hv
    obtain ⟨-, hCu⟩ := unit_part_c hCM hFix h𝔭 hU0 (ha0 i) hv (hpair i hv)
    have hAu := unit_part hCM hFix h𝔭 hU0 (ha0 i)
    have hAd := mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))
    have hs := mem_SP_of_inP (K := K) hU0 (hpair i hv)
    rw [map_add (f := _)] at hs
    set A := algebraMap F K (a i : F)
    set C := algebraMap F K (c (τ i))
    set P := algebraMap F K (π : F)
    set v := vF 𝔭 (a i)
    have e1 : P ^ v * P⁻¹ ^ v = 1 := by rw [← mul_pow, mul_inv_cancel₀ hP0, one_pow]
    have hCd : P⁻¹ ^ v * C ∈ SP K 𝔭 := by
      have e2 : P⁻¹ ^ v * C = P ^ v * (P⁻¹ ^ (2 * v) * (A + C)) - P⁻¹ ^ v * A := by
        rw [two_mul, pow_add]
        linear_combination (-(P⁻¹ ^ v * (A + C))) * e1
      rw [e2]
      exact sub_mem (mul_mem (pow_mem hSPπ _) hs) hAd
    apply NU.pair (hA0 i) (star_fix hFix _)
    · have e3 : C * A⁻¹ = (P⁻¹ ^ v * C) * (A⁻¹ * P ^ v) := by
        linear_combination (-(C * A⁻¹)) * e1
      rw [e3]
      exact mul_mem hCd hAu
    · have e3 : A * C⁻¹ = (P⁻¹ ^ v * A) * (C⁻¹ * P ^ v) := by
        linear_combination (-(A * C⁻¹)) * e1
      rw [e3]
      exact mul_mem hAd hCu
  let T := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0)
  let S := T.image τ
  have hSj : S ⊆ Finset.univ.erase j := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro e
    have := hτlt i (Finset.mem_filter.mp hi).2
    rw [e] at this
    omega
  have hinjT : Set.InjOn τ T := fun i hi k hk e =>
    hτinj i k (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hk).2 e
  have hCprod : ∏ k, algebraMap F K (c k) = algebraMap F K (c j) *
      ((∏ i ∈ T, algebraMap F K (c (τ i))) * ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => algebraMap F K (c k)) (Finset.mem_univ j),
      ← Finset.prod_sdiff hSj, Finset.prod_image hinjT]
    ring
  have hAprod : ∏ i, algebraMap F K (a i : F) = (∏ i ∈ T, algebraMap F K (a i : F)) *
      ∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have htot : (gramK h γ).det = algebraMap F K (c j) *
      ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    rw [hdetγ, hAprod, hCprod, Finset.prod_mul_distrib]
    ring
  have hX : NU 𝔭 ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    refine NU.mul (NU.mul ?_ ?_) ?_
    · exact NU.prod _ _ fun i hi => hpairNU i (Finset.mem_filter.mp hi).2
    · exact NU.prod _ _ fun i hi => hunitA i (by simpa using (Finset.mem_filter.mp hi).2)
    · refine NU.prod _ _ fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk1).1
      apply hunitC k
      · have h1 := k.isLt
        have h2 := Fin.val_ne_of_ne hkj
        omega
      · intro i hi e
        exact hk2 (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, e⟩)
  have hX0 : (∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    · exact mul_ne_zero (hA0 i) (hC0 _)
    · exact hA0 i
    · exact hC0 i
  rw [htot] at hNUγ
  exact NU.of_mul_left hNUγ hX hX0

end Formalism.L2.SG.Pf.Cnt
end
end
end
