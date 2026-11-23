module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.PolarLatticePairs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm
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

-- Source module: Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormEqRelIndexMul

section

@[expose] public section

noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

namespace Dx

variable {K : Type} [Field K] [NumberField K]

theorem absNorm_eq_relIndex_mul (J J' : FractionalIdeal (𝓞 K)⁰ K) (hJ' : J' ≠ 0) (hle : J' ≤ J) :
    FractionalIdeal.absNorm J' = ((J' : Submodule (𝓞 K) K).toAddSubgroup.relIndex
      (J : Submodule (𝓞 K) K).toAddSubgroup : ℚ) * FractionalIdeal.absNorm J := by
  have hJ : J ≠ 0 := by rintro rfl; exact hJ' (FractionalIdeal.le_zero_iff.1 hle)
  have hX : J' * J⁻¹ ≤ 1 := by
    calc J' * J⁻¹ ≤ J * J⁻¹ := mul_le_mul' hle le_rfl
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨X, hX'⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hX
  have hdec : J' = J * (X : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hX', mul_comm J', ← mul_assoc, mul_inv_cancel₀ hJ, one_mul]
  obtain ⟨c, P, hc, hP⟩ := FractionalIdeal.exists_eq_spanSingleton_mul J
  let φ : 𝓞 K →+ K := (AddMonoidHom.mulLeft ((algebraMap (𝓞 K) K c)⁻¹)).comp (algebraMap (𝓞 K) K).toAddMonoidHom
  have hc' : (algebraMap (𝓞 K) K c)⁻¹ ≠ 0 :=
    inv_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hc)
  have hφ : Function.Injective φ := by
    intro r s h
    have h' : (algebraMap (𝓞 K) K c)⁻¹ * algebraMap (𝓞 K) K r = (algebraMap (𝓞 K) K c)⁻¹ * algebraMap (𝓞 K) K s := h
    exact IsFractionRing.injective (𝓞 K) K (mul_left_cancel₀ hc' h')
  have hmap : ∀ Q : Ideal (𝓞 K), ((FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)⁻¹ *
      (Q : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).toAddSubgroup =
      Q.toAddSubgroup.map φ := by
    intro Q
    ext x
    simp only [Submodule.mem_toAddSubgroup, FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton,
      Submodule.mem_span_singleton_mul, AddSubgroup.mem_map]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨r, hr, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
      exact ⟨r, hr, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨algebraMap (𝓞 K) K r, (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩, rfl⟩
  have hJ'P : J' = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K c)⁻¹ *
      ((P * X : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hdec, hP, FractionalIdeal.coeIdeal_mul, mul_assoc]
  have hrel : (J' : Submodule (𝓞 K) K).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      (P * X).toAddSubgroup.relIndex P.toAddSubgroup := by
    rw [hJ'P, hmap, hP, hmap, AddSubgroup.relIndex_map_map_of_injective _ _ hφ]
  have hPX : P * X ≤ P := by simpa [mul_comm] using (Ideal.mul_le_right : X * P ≤ P)
  have htow := AddSubgroup.relIndex_mul_relIndex (P * X).toAddSubgroup P.toAddSubgroup ⊤ hPX le_top
  rw [AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right] at htow
  have hn : ∀ Q : Ideal (𝓞 K), Ideal.absNorm Q = Q.toAddSubgroup.index := fun Q => by
    rw [Ideal.absNorm_apply]; rfl
  have hmul : Ideal.absNorm (P * X) = Ideal.absNorm P * Ideal.absNorm X := map_mul _ _ _
  rw [hn, hn, hn] at hmul
  have hP0 : P.toAddSubgroup.index ≠ 0 := by
    rw [← hn]
    intro h
    apply hJ
    rw [hP, Ideal.absNorm_eq_zero_iff.1 h, FractionalIdeal.coeIdeal_bot, mul_zero]
  have hidx : (P * X).toAddSubgroup.relIndex P.toAddSubgroup = Ideal.absNorm X := by
    rw [hn X]
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hP0)
    rw [htow, hmul, mul_comm]
  rw [hrel, hidx, hdec, map_mul, FractionalIdeal.coeIdeal_absNorm, mul_comm]

end Dx

end Formalism.L2.LamCM
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardLatticeQuotIdeal

section

@[expose] public section

open NumberField IsDedekindDomain Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.IndefiniteRowSideFullHecke.PolarLatticePairs
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MatrixLatticeIndex

theorem card_matIn (D : D7) (a d : ℕ) (A B : Submodule (𝓞 D.host.E) D.host.E) :
    Nat.card (matIn D a d A ⧸ (matIn D a d B).addSubgroupOf (matIn D a d A)) =
      (B.toAddSubgroup.relIndex A.toAddSubgroup) ^ (a * d) := by
  let Q := A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup
  let f : matIn D a d A →+ (Fin d → Fin a → Q) :=
    { toFun := fun z i j => QuotientAddGroup.mk (⟨z.1 i j, z.2 i j⟩ : A.toAddSubgroup)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := by
    intro y
    refine ⟨⟨fun i j => ((y i j).out : A.toAddSubgroup), fun i j => (y i j).out.2⟩, ?_⟩
    funext i j
    exact QuotientAddGroup.out_eq' (y i j)
  have hker : f.ker = (matIn D a d B).addSubgroupOf (matIn D a d A) := by
    ext z
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h i j
      exact (QuotientAddGroup.eq_zero_iff _).1 (congrFun (congrFun h i) j)
    · intro h
      funext i j
      exact (QuotientAddGroup.eq_zero_iff _).2 (h i j)
  rw [← hker, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a), Nat.card_eq_fintype_card (α := Fin d),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl

theorem relIndex_smul {K : Type} [Field K] [NumberField K]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hJ : J ≠ 0) (q : Ideal (𝓞 K)) (hq : q ≠ ⊥) :
    (q • (J : Submodule (𝓞 K) K)).toAddSubgroup.relIndex (J : Submodule (𝓞 K) K).toAddSubgroup =
      Ideal.absNorm q := by
  have hq' : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hq
  have hle : (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ J := by
    calc (q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J ≤ 1 * J :=
          mul_le_mul' FractionalIdeal.coeIdeal_le_one le_rfl
      _ = J := one_mul J
  have h := Formalism.L2.LamCM.Dx.absNorm_eq_relIndex_mul J _ (mul_ne_zero hq' hJ) hle
  have he : (((q : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) * J :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) = q • (J : Submodule (𝓞 K) K) := by
    apply le_antisymm
    · rw [FractionalIdeal.coe_mul]
      refine Submodule.mul_le.2 fun x hx y hy => ?_
      obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem_smul hb hy
    · refine Submodule.smul_le.2 fun b hb y hy => ?_
      rw [Algebra.smul_def]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ hb) hy
  rw [he, map_mul, FractionalIdeal.coeIdeal_absNorm] at h
  have h0 : FractionalIdeal.absNorm J ≠ 0 := fun h' => hJ (FractionalIdeal.absNorm_eq_zero_iff.1 h')
  exact_mod_cast (mul_right_cancel₀ h0 h).symm


open GlobalTheory.NormSum.MovedLattice in
theorem coefLat_eq (D : D7) (cc : Ideal (𝓞 D.host.K)) :
    coefLat D cc = ((ext D cc * D.host.AA0 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨c, hc, m, hm, rfl⟩
    exact FractionalIdeal.mul_mem_mul (mem_ext D hc) hm
  · rw [FractionalIdeal.coe_mul]
    refine Submodule.mul_le.2 fun x hx y hy => ?_
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    clear hx
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨c, hc, rfl⟩ := hb
      exact Submodule.subset_span ⟨c, hc, y, hy, rfl⟩
    | zero => rw [map_zero, zero_mul]; exact zero_mem _
    | add b b' _ _ hb hb' => rw [map_add (f := _), add_mul]; exact add_mem hb hb'
    | smul r b _ hb =>
      rw [smul_eq_mul, map_mul, mul_assoc, ← Algebra.smul_def]
      exact Submodule.smul_mem _ r hb

end GlobalTheory.MatrixLatticeIndex
end
end
end
