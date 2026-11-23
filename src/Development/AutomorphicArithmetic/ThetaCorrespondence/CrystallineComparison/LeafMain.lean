module

public import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Comparison
public import Development.WeilBound.CoreStatements.PeriodRingComparison.PadicPeriodAlgebraMaps.CPAlgebraMapPadic
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.EqZeroOfPMulEqZero
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LeafDefs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.IotaBounded
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.GammaEqDpow
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.AcrisNAlgebraMapAinf

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.EqToBdRPlusOfBounded

section

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open Reformulated.AutPerF Ideal

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Fact ¬IsUnit (p : R)]
  [IsAdicComplete (span {(p : R)}) R] [IsDomain R] [ValuationRing R] [CharZero R]
  [IsAlgClosed (FractionRing R)]

theorem eq_toBdRPlus_of_bounded (j : Acris p R →+* BdRPlus p R)
    (h0 : ∀ a : AcrisZero p R, j (algebraMap (AcrisZero p R) (Acris p R) a) =
      algebraMap (AinfInv p R) (BdRPlus p R) (a : AinfInv p R))
    (hb : ∀ n : ℕ, ∃ N : ℕ, ∀ x : Acris p R, ∃ a : Ainf p R,
      BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * j x) = Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) a)) :
    j = Acris.toBdRPlus p R := by
  ext x
  apply BdRPlus.ext_eval
  intro n
  obtain ⟨N, hN⟩ := hb n
  set T := (AcrisZero.toQuot p R n).range
  have key : ∀ k : ℕ, ∃ c : Ainf p R, BdRPlus.eval p R n (j x) - BdRPlus.eval p R n (Acris.toBdRPlus p R x) =
      (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) c) := by
    intro k
    obtain ⟨a0, z, hz⟩ := Acris.exists_eq_add (N + n + k) x
    obtain ⟨az, haz⟩ := hN z
    obtain ⟨bz, hbz⟩ := AcrisZero.exists_p_pow_mul_eq n (Acris.toRange p R n z)
    have hbz' := congrArg Subtype.val hbz
    simp only [Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast, RingHom.coe_rangeRestrict] at hbz'
    have hy2 : j x = algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * j z := by
      rw [hz, map_add (f := _), map_mul, map_pow, map_natCast, h0 a0]
    have hx2 : Acris.toBdRPlus p R x =
        algebraMap (AinfInv p R) (BdRPlus p R) (a0 : AinfInv p R) + (p : BdRPlus p R) ^ (N + n + k) * Acris.toBdRPlus p R z := by
      rw [hz, map_add (f := _), map_mul, map_pow, map_natCast, Acris.toBdRPlus_algebraMap_zero]
    refine ⟨(p : Ainf p R) ^ n * az - (p : Ainf p R) ^ N * bz, ?_⟩
    have e1 : BdRPlus.eval p R n ((p : BdRPlus p R) ^ N * j z) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) az) := haz
    have e2 : (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z) =
        Ideal.Quotient.mk _ (algebraMap (Ainf p R) (AinfInv p R) bz) := by
      rw [Acris.eval_toBdRPlus, hbz']
      rfl
    rw [map_mul, map_pow, map_natCast] at e1
    rw [hy2, hx2]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, map_sub]
    rw [add_sub_add_left_eq_sub, ← mul_sub]
    calc (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ (N + n + k) * (BdRPlus.eval p R n (j z) - BdRPlus.eval p R n (Acris.toBdRPlus p R z))
        = (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ k *
            ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * BdRPlus.eval p R n (j z))
              - (p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ N * ((p : AinfInv p R ⧸ AinfInv.kerTheta p R ^ n) ^ n * BdRPlus.eval p R n (Acris.toBdRPlus p R z))) := by
          ring
      _ = _ := by rw [e1, e2]
  have hmem : ∀ c : Ainf p R, Ideal.Quotient.mk (AinfInv.kerTheta p R ^ n) (algebraMap (Ainf p R) (AinfInv p R) c) ∈ T :=
    fun c => ⟨algebraMap (Ainf p R) (AcrisZero p R) c, rfl⟩
  obtain ⟨c0, hc0⟩ := key 0
  rw [pow_zero, one_mul] at hc0
  have hH : IsHausdorff (span {(p : T)}) T := inferInstance
  have h0' : (⟨_, hmem c0⟩ : T) = 0 := by
    apply hH.haus
    intro k
    obtain ⟨c, hc⟩ := key k
    have hx : (⟨_, hmem c0⟩ : T) = ((p : T) ^ k) • (⟨_, hmem c⟩ : T) := by
      apply Subtype.ext
      simp only [smul_eq_mul, Subring.coe_mul, Subring.coe_pow, Subring.coe_natCast]
      rw [← hc0, hc]
    rw [SModEq.zero, hx]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) Submodule.mem_top
  have h1 := congrArg Subtype.val h0'
  simp only [ZeroMemClass.coe_zero] at h1
  rw [← hc0] at h1
  exact sub_eq_zero.1 h1

end Formalism.BasicNotions.CmpTie.Incl
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.JOCBounded

section

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem jOC_bounded (n : ℕ) : ∃ N : ℕ, ∀ x : Reformulated.AutPerF.Acris l (Cmp6.OC l), ∃ a : Reformulated.AutPerF.Ainf l (Cmp6.OC l),
    Reformulated.AutPerF.BdRPlus.eval l (Cmp6.OC l) n (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) ^ N * jOC l x) =
      Ideal.Quotient.mk _ (algebraMap (Reformulated.AutPerF.Ainf l (Cmp6.OC l)) (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) a) := by
  obtain ⟨N, hN⟩ := iota_bounded l n
  refine ⟨N, fun x => ?_⟩
  obtain ⟨a, ha⟩ := hN (Cmp6.cA l x)
  refine ⟨Reformulated.AutPerF.Ainf.map l (Cmp6.e l).symm.toRingHom a, ?_⟩
  have hsymm : ∀ z : Formalism.Per6.BdRp l,
      (Cmp6.cP l).symm z = Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom z := by
    intro z
    rw [RingEquiv.symm_apply_eq]
    show z = Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).toRingHom
      (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom z)
    erw [Reformulated.AutPerF.BdRPlus.map_map, RingEquiv.toRingHom_comp_symm_toRingHom, Reformulated.AutPerF.BdRPlus.map_id]
  show Reformulated.AutPerF.BdRPlus.eval l (Cmp6.OC l) n
      (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (Cmp6.OC l)) ^ N * (Cmp6.cP l).symm (iotaP l (Cmp6.cA l x))) = _
  erw [hsymm]
  rw [← map_natCast (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom) l, ← map_pow]
  have hm := map_mul (Reformulated.AutPerF.BdRPlus.map l (Cmp6.e l).symm.toRingHom)
    (((l : ℕ) : Reformulated.AutPerF.BdRPlus l (NC l)) ^ N) (iotaF l (Cmp6.cA l x))
  erw [← hm, Reformulated.AutPerF.BdRPlus.eval_map]
  erw [ha]
  rw [Ideal.quotientMap_mk, Reformulated.AutPerF.AinfInv.map_algebraMap]

end Formalism.BasicNotions.CmpTie.Incl
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.ZeroEquiv

section

@[expose] public section

noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]

theorem zt1 (y : Reformulated.AutPerF.AcrisZero l (NC l)) :
    ((Cmp6.zeroEquiv l y : ACris.ACrisZero ℂ_[l] l) : Localization.Away ((l : ℕ) : AInf ℂ_[l] l)) =
      ((y : Reformulated.AutPerF.AcrisZero l (NC l)) : Reformulated.AutPerF.AinfInv l (NC l)) := by
  simp only [Cmp6.zeroEquiv, AlgEquiv.coe_ringEquiv, Subalgebra.equivOfEq_apply]
end Formalism.BasicNotions.CmpTie.Incl
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Zt2

section

@[expose] public section

noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]

theorem zt2 (z : Reformulated.AutPerF.AinfInv l (NC l)) :
    toBDeRhamPlus (↥(normInteger ℂ_[l])) l z = algebraMap (Reformulated.AutPerF.AinfInv l (NC l)) (Reformulated.AutPerF.BdRPlus l (NC l)) z := rfl
end Formalism.BasicNotions.CmpTie.Incl
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.Zt3

section

@[expose] public section

noncomputable section
namespace Formalism.BasicNotions.CmpTie.Incl
open GroundTheory.PAdicHodge
variable (l : ℕ) [Fact l.Prime]

theorem zt3 (a : Reformulated.AutPerF.AcrisZero l (Cmp6.OC l)) :
    ((Reformulated.AutPerF.AcrisZero.map (p := l) (Cmp6.e l).toRingHom a : Reformulated.AutPerF.AcrisZero l (NC l)) : Reformulated.AutPerF.AinfInv l (NC l)) =
      Reformulated.AutPerF.AinfInv.map l (Cmp6.e l).toRingHom (a : Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) :=
  Reformulated.AutPerF.AcrisZero.coe_map _ _
end Formalism.BasicNotions.CmpTie.Incl
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.JOCZero

section

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]


theorem jOC_zero (a : Reformulated.AutPerF.AcrisZero l (Cmp6.OC l)) :
    jOC l (algebraMap _ (Reformulated.AutPerF.Acris l (Cmp6.OC l)) a) =
      algebraMap (Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) _ (a : Reformulated.AutPerF.AinfInv l (Cmp6.OC l)) := by
  show (Cmp6.cP l).symm (iotaP l (Cmp6.cA l (algebraMap _ _ a))) = _
  rw [RingEquiv.symm_apply_eq, Cmp6.cA_apply, Reformulated.AutPerF.Acris.map_algebraMap_zero, Cmp6.acrisNHom_algebraMap]
  erw [ACris.iota_of]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  erw [zt1, zt2, zt3]

end Formalism.BasicNotions.CmpTie.Incl
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LeafMain

section

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.CmpTie.Incl

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem comparison_toBdRPlus (x : Reformulated.AutPerF.Acris l (Cmp6.OC l)) :
    Cmp6.cP l (Reformulated.AutPerF.Acris.toBdRPlus l (Cmp6.OC l) x) = ACris.iota ℂ_[l] l (Cmp6.cA l x) := by
  have h := eq_toBdRPlus_of_bounded (jOC l) (jOC_zero l) (jOC_bounded l)
  rw [← h]
  show Cmp6.cP l ((Cmp6.cP l).symm (iotaP l (Cmp6.cA l x))) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

end Formalism.BasicNotions.CmpTie.Incl
end
end
end
