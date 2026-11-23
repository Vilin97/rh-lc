module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ActsAwayNbar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompAway
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FTfact
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GCSch
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussD
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussN
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GramXDiag
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenC
import Mathlib.Tactic.Polynomial.Basic
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocMul
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.TensInjOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VacKOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IteratedDerivMulConst
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocFactPf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WopTop

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LawNbarA

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.NbarH

variable {m n : ℕ}

theorem ftLoc_const_mul (ε : Fin m → Bool) (s : ℝ) (k : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) (u : Fin m → Fin n → ℂ) :
    ftLoc ε s (fun v => k * g v) u = k * ftLoc ε s g u := by
  unfold ftLoc
  simp_rw [mul_assoc]
  exact MeasureTheory.integral_const_mul k _

theorem ftLoc_const_mul' (ε : Fin m → Bool) (s : ℝ) (k : ℂ) (g : (Fin m → Fin n → ℂ) → ℂ) :
    ftLoc ε s (fun v => k * g v) = fun u => k * ftLoc ε s g u := funext fun u => ftLoc_const_mul ε s k g u

theorem sigR_sq (ε : Fin m → Bool) (a : Fin m) : (VacC.sigR ε a : ℂ) ^ 2 = 1 := by
  unfold VacC.sigR; split_ifs <;> norm_num

theorem ftLoc_vac (ε : Fin m → Bool) (t c s : ℝ) (hc : 0 < c) (hs : s ^ 2 = c ^ 2) :
    ftLoc ε s (vac ε t c) = fun u => ((Real.pi : ℂ) / c) ^ (m * n) * vac (n := n) ε t c u := by
  funext u
  have hs' : (s : ℂ) ^ 2 = (c : ℂ) ^ 2 := by exact_mod_cast hs
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [VacC.ftLoc_eq, VacC.vac_eq, VacS.ftG_DG _ _ _ _ (fun a j => by simpa using hc)]
  have hγ : (fun (a : Fin m) (j : Fin n) => (s : ℂ) ^ 2 * ((VacC.sigR ε a : ℝ) : ℂ) ^ 2 / (c : ℂ)) = fun _ _ => (c : ℂ) := by
    funext a j
    rw [sigR_sq, hs']
    field_simp
  rw [hγ]
  simp only [VacS.DG, Finset.prod_const, Finset.card_univ, Fintype.card_fin, one_mul]
  rw [← pow_mul, mul_comm n m]

end PositivityTheory.Rg.Sw.Glob.NbarH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LawNbar

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open NbarH GaussH

theorem lawNbar_of (hU : UnipTau) (hW : WEx) (hF : FTfact) (hTI : TensInj) (hLNe : LNe) : LawNbar := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL y c hc hyc f hf
  have htc : |tLoc l τ| = cLoc l τ := abs_tLoc l τ
  have hc0 : 0 < cLoc l τ := by
    unfold cLoc
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hC.hψ hC.hθ hC.hl τ))
  have hsq : (tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [← htc, sq_abs]
  have hsq' : (-tLoc l τ) ^ 2 = (cLoc l τ) ^ 2 := by rw [neg_sq, hsq]
  obtain ⟨w, hw⟩ := hW D n
  have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
  obtain ⟨yn, hyn⟩ := OG.exists_nU n (-c) hc'
  have hιy : ι y = w * ι yn * w⁻¹ := by rw [OG.iota_conj hC.hθ hC.hι w hw y yn c hyc hyn]; group
  obtain ⟨κ, A, A', hκ, hFT⟩ := hF D n V ψ χ θ μ ω H l s ν τ ε fr ι hC w hw
  have hvS : IsSch (vac (n := n) ε (tLoc l τ) (cLoc l τ)) := gZSch V.rank n ε _ _ hc0 htc _ isSiegel_I
  set K : ℂ := ((Real.pi : ℂ) / (cLoc l τ)) ^ (V.rank * n) with hK
  have hK0 : K ≠ 0 := pow_ne_zero _ (div_ne_zero (by exact_mod_cast Real.pi_pos.ne') (by exact_mod_cast hc0.ne'))
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  obtain ⟨hAΨ, hA'Ψ, hFΨ⟩ := hFT Ψ hΨ
  have kA := hFT (A' Ψ) hA'Ψ

  have hid : ∀ g (hg : IsSch g), tens θ τ fr g Ψ =
      tens θ τ fr (fun u => κ * ftLoc ε (tLoc l τ) (fun v => κ⁻¹ * ftLoc ε (-tLoc l τ) g v) u) (A (A' Ψ)) := by
    intro g hg
    have h1 : ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ =
        ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) g u) (A' Ψ), hA'Ψ.2 _ ((hFΨ g hg).2.1)⟩ :=
      Subtype.ext (hFΨ g hg).2.2.2
    have h2 := (kA.2.2 _ ((hFΨ g hg).2.1)).2.2.1
    have h3 : ω w (ω w⁻¹ ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩) = ⟨tens θ τ fr g Ψ, hΨ.2 g hg⟩ := by
      rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
    rw [h1] at h3
    rw [← h2, h3]
  have hAA : ∀ x, A (A' Ψ) x = (K * K)⁻¹ * Ψ x := by
    intro x
    have h := congrFun (hid _ hvS) x
    simp only [tens, ftLoc_vac ε _ _ _ hc0 hsq', ftLoc_const_mul', ftLoc_vac ε _ _ _ hc0 hsq] at h
    have hv0 : vac (n := n) ε (tLoc l τ) (cLoc l τ) (fr⁻¹ * compAt θ τ x) ≠ 0 := Complex.exp_ne_zero _
    have hκ' : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
    field_simp at h
    rw [h, hK]
    field_simp

  rw [← hL.2 y Ψ hΨ f hf]
  have hE : IsSch (fun u => chN ε (tLoc l τ) (-c) u * (κ⁻¹ * ftLoc ε (-tLoc l τ) f u)) :=
    (schOps V.rank n).2.2.2.1 ε (tLoc l τ) (-c) _ hc' (hFΨ f hf).2.1
  have s1 : ω w⁻¹ ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ =
      ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ), hA'Ψ.2 _ ((hFΨ f hf).2.1)⟩ :=
    Subtype.ext (hFΨ f hf).2.2.2
  have s2 : ω (ι yn) ⟨tens θ τ fr (fun u => κ⁻¹ * ftLoc ε (-tLoc l τ) f u) (A' Ψ), hA'Ψ.2 _ ((hFΨ f hf).2.1)⟩ =
      ⟨tens θ τ fr (fun u => chN ε (tLoc l τ) (-c) u * (κ⁻¹ * ftLoc ε (-tLoc l τ) f u)) (A' Ψ), hA'Ψ.2 _ hE⟩ := by
    apply Subtype.ext
    funext x
    rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC yn (-c) hc' hyn]
    simp only [tens, chN, mul_assoc]
  have s3 := (kA.2.2 _ hE).2.2.1
  rw [hιy, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, s1, s2, s3]
  funext x
  simp only [tens]
  rw [hAA x]
  have hKK : ((|tLoc l τ| / Real.pi : ℝ) : ℂ) ^ (2 * V.rank * n) = (K * K)⁻¹ := by
    rw [hK, htc, ← pow_two, ← pow_mul, ← inv_pow, inv_div]
    push_cast
    ring_nf
  rw [hKK]
  have hκ' : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ
  have e : (fun v => chN ε (tLoc l τ) (-c) v * (κ⁻¹ * ftLoc ε (-tLoc l τ) f v)) =
      fun v => κ⁻¹ * (chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v) := by funext v; ring
  rw [e, ftLoc_const_mul']
  linear_combination (ftLoc ε (tLoc l τ) (fun v => chN ε (tLoc l τ) (-c) v * ftLoc ε (-tLoc l τ) f v)
    (fr⁻¹ * compAt θ τ x)) * (K * K)⁻¹ * Ψ x * hκ'

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussFinal

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem gaussian_law_of_weil (hW : WEx) (hF : FTfact) : GaussLaw :=
  gaussLaw_of' (vacK_of gZSch (lawN_of unipTau (tensInj_of awayIn))
    (lawNbar_of unipTau hW hF (tensInj_of awayIn) lNe) (locMul_of (tensInj_of awayIn)) lNe) gZSch

end PositivityTheory.Rg.Sw.Glob
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussClosed

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem gaussLaw : GaussLaw := gaussian_law_of_weil wEx fTfact

end PositivityTheory.Rg.Sw.Glob
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WlocTop

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem awayAct_gen (hG : GenA) : AwayAct := awayAct_of hG fTfact decompAway

theorem locFact : LocFact := locFact_of decomp (opGen_of fTfact)

theorem localRepresentationL2 : LocalL2Isometry := local_L2_isometry fTfact

theorem gIdil_gen (h : GlobalTheory.Published.WeilThetaConvergence) (hG : GenA) : GIdil :=
  gIdil_of h gZSch decompAway (awayAct_gen hG) locFact gaussLaw awayIn localRepresentationL2

end PositivityTheory.Rg.Sw.Glob
end
end
