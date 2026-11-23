module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddOp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutRegFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAStarOp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQAsm
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMP2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCV
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCap
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjFrom
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERCapAdjS
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBesselFold
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnBetaFrame
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVInCC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFoldRev
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCFinal
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.JAdjTrQQOfThree

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDQQAsm

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem jDecayTrQQ_of_open (h2 : JDHatOpQQ) : JDecayTrQQ := jDecayTrQQd_of_open h2

end Formalism.FourierDecayAlt.P.CutMP
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutERAsm

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP.ER

theorem energyReal_of_capAdj (hA : CapAdj) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_leaves hA capacity_theta_facts coefficient_vector_smoothness coefficient_vector_in_class coefficient_vector_support coefficient_vector_congr coefficient_vector_commutation
    beta_form_congr_holds

theorem energyReal_of_capAdjInt (hI : CapAdjInt) : Formalism.FourierDecayAlt.P.CutMP.EnergyReal :=
  energyReal_of_capAdj (capAdj_of_int hI)

end Formalism.FourierDecayAlt.P.CutMP.ER
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnergyReal

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem energy_reality_holds : EnergyReal :=
  ER.energyReal_of_capAdjInt (ER.capAdjInt_of_scalar ER.capacity_adjoint_scalar)

end Formalism.FourierDecayAlt.P.CutMP
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAdmLen

section

@[expose] public section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem admissible_length_holds : AdmLen := by
  intro E _ _ _ Wp Wq _ _ _ _ S v a ha
  obtain ⟨w, rfl⟩ := ha
  exact le_trans (Finset.le_sup (f := fun v => (w.1 v).length) (Finset.mem_univ v)) w.2.2

end Formalism.FourierDecayAlt.P.CutMP.En
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.L2BoundAtBuiltPlaceHolds

section

@[expose] public section

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem inCC_fold (hC : CVInCC) {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (s : ℂ)
    (F : B.Mat k r → E) : ∀ (b : List C.Letter) (m : ℕ),
      B.InCC A (m + (2 * r + k + 1) * b.length) F → B.InCC A m (foldCV k r s b F)
  | [], m, h => by rw [foldCV_nil]; simpa using h
  | x :: b, m, h => by
    rw [foldCV_cons]
    refine hC k r E A m _ (x.2 : ℂ) s ?_
    refine inCC_fold hC A s F b (m + (2 * r + k + 1)) ?_
    have e : m + (2 * r + k + 1) + (2 * r + k + 1) * b.length = m + (2 * r + k + 1) * (x :: b).length := by
      simp [List.length_cons]; ring
    rw [e]; exact h

theorem weight_budget_L2_inequality (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k) (j : ℕ) (hj : j ≤ 5)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀)
    (ℓ : ℕ) (hℓ : ℓ ≤ N) :
    B.AB k r + 2 * ((r : ℝ) + 1) * ((j + (2 * r + k + 1) * ℓ : ℕ) : ℝ) ≤ A₀ := by
  unfold B.AB
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast hj
  have hℓ' : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hcast : ((j + (2 * r + k + 1) * ℓ : ℕ) : ℝ) = j + n * ℓ := by rw [hn]; push_cast; ring
  rw [hcast]
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; linarith
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have h4 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
    nlinarith

  have hkr : 2 * ((k : ℝ) + r) ≤ 2 * n := by rw [hn]; linarith
  have hb : 2 * ((k : ℝ) + r) + 1 + 2 * (j + n * ℓ) ≤ 100 * ((N : ℝ) * n ^ 2 + n ^ 3) := by
    have h1 : 2 * n * ℓ ≤ (N : ℝ) * n ^ 2 := by
      have : (ℓ : ℝ) * (2 * n) ≤ N * (n * n) := by
        apply mul_le_mul hℓ' (by nlinarith) (by positivity) (by positivity)
      nlinarith
    have h2 : 2 * n + 1 + 10 ≤ 100 * n ^ 3 := by nlinarith
    have hNn : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
    nlinarith
  have hpos : 0 ≤ 100 * ((N : ℝ) * n ^ 2 + n ^ 3) := by positivity
  calc 2 * ((k : ℝ) + r) * ((r : ℝ) + 1) + 1 + 2 * ((r : ℝ) + 1) * (j + n * ℓ)
      ≤ ((r : ℝ) + 1) * (2 * ((k : ℝ) + r) + 1 + 2 * (j + n * ℓ)) := by nlinarith
    _ ≤ ((r : ℝ) + 1) * (100 * ((N : ℝ) * n ^ 2 + n ^ 3)) := by gcongr
    _ ≤ ((r : ℝ) + 1) ^ 4 * (100 * ((N : ℝ) * n ^ 2 + n ^ 3)) := by gcongr
    _ = 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * n ^ 2 + n ^ 3) := by ring
    _ ≤ A₀ := hA

theorem l2BoundAtBuiltPlace_of_cvInCC (hC : CVInCC) : L2BoundAtTowerPlace := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v ε hε a hlen
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨hχ, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, _⟩ := hv v
  have hF : ∀ j ≤ 5, B.InCC (B.AB S.G.k S.G.r) (j + (2 * S.G.r + S.G.k + 1) * a.length)
      (D.cutF (T v).base χ (f v) ε) := fun j hj =>
    Formalism.FourierDecayAlt.P.PBE.cutF_inCC (T v).base hχ hCC hε _ _ (weight_budget_L2_inequality S.G.k S.G.r S.Ntop A₀ hk2 j hj hA a.length hlen)
  have h5 := inCC_fold hC (B.AB S.G.k S.G.r) (M.sgn (D.parOf S v) (S.l + 1)) _ a 5 (hF 5 le_rfl)
  have h4 := inCC_fold hC (B.AB S.G.k S.G.r) (M.sgn (D.parOf S v) (S.l + 1)) _ a 4 (hF 4 (by norm_num))
  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base
    (B.AB S.G.k S.G.r) le_rfl
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨c4, hc4⟩ := h4
  exact (hC0 _ _ c4 c4 h5 h5 hc4 hc4).1

theorem L2_bound_at_built_place_holds : L2BoundAtTowerPlace := l2BoundAtBuiltPlace_of_cvInCC coefficient_vector_in_L2_class

end Formalism.FourierDecayAlt.P.CutMP.En
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnergyTr

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem En.bessel_folding_at_built_place : En.BesselFoldBuilt := En.besselFoldBuilt_of En.coefficient_vector_in_L2_class

theorem energyTr_of_betaFrame (h : En.BetaFrame) : EnergyTr :=
  En.energyTr_of_parts En.folding_reversal_holds En.admissible_length_holds En.bessel_folding_at_built_place En.L2_bound_at_built_place_holds h

theorem energy_trace_identity_holds : EnergyTr := energyTr_of_betaFrame En.beta_frame_identity_holds

end Formalism.FourierDecayAlt.P.CutMP
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTop

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_genTransfer (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer)
    (hD : JDecayTrQQ) (hA : JAdjTrQQ) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_openQQ hJ (Gauge.GC.gCore_of_genTransfer hG) energy_trace_identity_holds energy_reality_holds hD hA

end Formalism.FourierDecayAlt.P.CutMP
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfHat

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_hat (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer)
    (hHat : JDHatOpQQ) (hBdd : JA.JABddOpQQ) : Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_genTransfer hJ hG (jDecayTrQQ_of_open hHat) (JA.jAdjTrQQ_of_three hHat hBdd JA.star_operator_transfer_holds)

end Formalism.FourierDecayAlt.P.CutMP
end
end
