module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapTP
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddGen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChainPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnDatumBd
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapNrmW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChainPf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalProof
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLines
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfBdd

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapAsm

section

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jABddKapQQ_of_kapRealiser (hR : KapRealiser) : JABddKapQQ := by
  obtain ⟨K, hK, hR⟩ := hR
  refine ⟨K, hK, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  obtain ⟨κ, rfl⟩ := hb
  obtain ⟨c, ca, hadj, hc, hca, he, hea, hbc, hbca, hbig⟩ :=
    hR Cc Cb hCc hCb E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ κ
  refine ⟨SSn.orderZeroDifferentialOperator S v c ca hadj, SSn.order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩
  · intro Tm hTm
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    exact ⟨hc, hca⟩
  · intro p hp f' _ g hg
    rw [SSn.order_zero_operator_apply, SSn.order_zero_operator_apply]
    exact he p hp g hg.1 _
  · intro Tm hTm ε hε m
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    obtain ⟨C1, h1⟩ := hbc ε hε m
    obtain ⟨C2, h2⟩ := hbca ε hε m
    refine ⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · rw [SSn.order_zero_operator_apply]; exact SSn.equivariant_coefficient_preserves_forms hc he hJ
  · rw [SSn.order_zero_operator_adjoint]; exact SSn.equivariant_coefficient_preserves_forms hca hea hJ
  · rw [SSn.order_zero_operator_apply]
    exact trJ_kap_of_bigCell S T v e κ c hbig J

theorem jABddKapQQ_of_typeProj (hB : DatumBd) (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_kapRealiser (kapRealiser_of_typeProj hB hG hP)

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapFinal

section

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem datum_bound_holds : DatumBd := datumBd_of_chain SSn.ChainPf.chain_bound_holds

theorem jABddKapQQ_of_leaves (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_typeProj datum_bound_holds hG hP

theorem jABddKapQQ_of_cut (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) (hNW : NrmWFacts) : JABddKapQQ :=
  jABddKapQQ_of_leaves hG (typeProj_of hPE hGL hDU hNW)

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapShared

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jABddKapQQ_of_shared (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) : JABddKapQQ :=
  jABddKapQQ_of_cut hG hPE hGL hDU weighted_norm_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnAsm

section

@[expose] public section

open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open NumberField Formalism.FourierDecayAlt.P.CutMP

theorem sSnAssemble_of (hC : JA.DatumCompose) : SSnAssemble := by
  intro hG hR
  obtain ⟨K1, hK1, hG⟩ := hG
  obtain ⟨K2, hK2, hR⟩ := hR
  refine ⟨max K1 K2, le_max_of_le_left hK1, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  obtain ⟨a, a', ι, hD⟩ := hG Cc Cb (le_trans (le_max_left _ _) hCc) (le_trans (le_max_left _ _) hCb)
    E Wp Wq S T f χ ν' m₀ top A₀ hB v
  obtain ⟨Φ, Φa, hΦ⟩ := hR Cc (le_trans (le_max_right _ _) hCc) E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  have hCb0 : 0 ≤ Cb := le_trans (le_max_of_le_left hK1) hCb
  have hBg : 0 ≤ Cb * ((S.G.r : ℝ) + 1) := mul_nonneg hCb0 (by positivity)
  obtain ⟨c, ca, hadj, hc, hca, he, hea, hb, hba, hcv⟩ :=
    hC E Wp Wq S T v _ a a' ι Φ Φa hBg hD ⟨hΦ.1, hΦ.2.1, hΦ.2.2.1, hΦ.2.2.2.1⟩
  refine ⟨c, ca, hadj, hc, hca, he, hea, hb, hba, ?_⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Formalism.QuantumDeterminants.Tz S.G.k S.G.r (T v).base.z * Formalism.QuantumDeterminants.Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  intro q hq ρ π
  have hqD : q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hq.1, hTT ▸ hq.2⟩
  have hG' := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hqD
  have hpos : B.gq (T v).base q ∈ B.GPos (T v).base := ⟨hG'.1, hG'.2.2⟩
  obtain ⟨h1, h2, h3⟩ := hD.2.2.2.2.2.2.2 q hq
  rw [hcv _ hpos, h1, h2, h3]
  exact hΦ.2.2.2.2 q hq ρ π

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnFinal

section

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

theorem sSnRealiser_of (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : SSnRealiser :=
  sSnAssemble_of (JA.datumCompose_of (JA.datumBd_of_chain hCh)) hG hR

theorem jABddSSnQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnQQ :=
  jABddSSnQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

theorem jABddSSnStarQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnStarQQ :=
  jABddSSnStarQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddDone

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem kappa_quadratic_bound_holds : JABddKapQQ :=
  jABddKapQQ_of_shared second_shift_geometry_holds rho_projection_existence gauge_lines_holds SSn.Rep.datum_unit_norm_holds

theorem jABddOpQQ_of_ssnRep (h : SSn.SSnRep) : JABddOpQQ :=
  jABddOpQQ_of_bddLeaves bounded_scalar_transfer_holds kappa_quadratic_bound_holds
    (SSn.jABddSSnQQ_of_leaves SSn.ChainPf.chain_bound_holds second_shift_geometry_holds h)
    (SSn.jABddSSnStarQQ_of_leaves SSn.ChainPf.chain_bound_holds second_shift_geometry_holds h)

end Formalism.FourierDecayAlt.P.CutMP.JA

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_ssnRep (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_bdd hJ hG (JA.jABddOpQQ_of_ssnRep h)

end Formalism.FourierDecayAlt.P.CutMP
end
end
