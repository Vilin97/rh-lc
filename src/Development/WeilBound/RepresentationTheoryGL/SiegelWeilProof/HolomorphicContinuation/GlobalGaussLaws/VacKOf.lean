module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRCosSubSin
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetMMUnitary
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LevFUnitary
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.IsSchwartzSmul
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetNeOfInG
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.CoordGamma
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRConjTranspose
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DRCosSubSin
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DetMMUnitary
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LevFUnitary
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RhoTSq
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RotDG
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.RhoTSq
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussScalar
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GramXDiag

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ProdF

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacK

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF PositivityTheory.Rg.Sw.Glob.VacG PositivityTheory.Rg.Sw.Glob.VacH
  PositivityTheory.Rg.Sw.Glob.VacI PositivityTheory.Rg.Sw.Glob.VacJ

theorem prodF {m n : ℕ} (t : ℝ) (ε : Fin m → Bool) (φ : Fin n → ℝ) :
    ∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT t ε a : ℂ) * (Real.sin (φ j) : ℂ)) =
      (∏ j, Complex.exp (Complex.I * (φ j : ℂ))) ^ (cnt (epsT t ε) true) *
        ((∏ j, Complex.exp (Complex.I * (φ j : ℂ)))⁻¹) ^ (cnt (epsT t ε) false) := by
  have inner : ∀ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (rhoT t ε a : ℂ) * (Real.sin (φ j) : ℂ)) =
      if epsT t ε a = true then ∏ j, Complex.exp (Complex.I * (φ j : ℂ))
      else (∏ j, Complex.exp (Complex.I * (φ j : ℂ)))⁻¹ := by
    intro a
    by_cases h : epsT t ε a = true
    · rw [if_pos h]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [rhoT, if_pos h]
      rw [show Complex.I * (φ j : ℂ) = (φ j : ℂ) * Complex.I by ring, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
      push_cast
      ring
    · rw [if_neg h, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [rhoT, if_neg h]
      rw [← Complex.exp_neg, show -(Complex.I * (φ j : ℂ)) = (-(φ j : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
        Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      push_cast
      ring
  rw [Finset.prod_congr rfl (fun a _ => inner a), Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp only [cnt, Bool.not_eq_true]

theorem alg (a a' X : ℂ) (ha : a ≠ 0) (ha' : a' ≠ 0) (hX : X ≠ 0) (e : ℤ) (p q : ℕ) :
    1 * (a' ^ e * (a'⁻¹) ^ (((p + q : ℕ) : ℤ) - e)) * (X ^ p * (X⁻¹) ^ q) * (a ^ e * (a⁻¹) ^ (((p + q : ℕ) : ℤ) - e)) =
      (a * a * (a' * a')) ^ e * (a * X⁻¹ * a') ^ (-(p : ℤ)) * (a * X * a') ^ (-(q : ℤ)) := by
  rw [inv_zpow', inv_zpow', neg_sub, zpow_sub₀ ha, zpow_sub₀ ha']
  simp only [zpow_neg, zpow_natCast, mul_zpow, inv_pow, mul_pow]
  have hA : a ^ e ≠ 0 := zpow_ne_zero e ha
  have hA' : a' ^ e ≠ 0 := zpow_ne_zero e ha'
  have hXp : X ^ p ≠ 0 := pow_ne_zero p hX
  have hXq : X ^ q ≠ 0 := pow_ne_zero q hX
  field_simp
  ring

end PositivityTheory.Rg.Sw.Glob.VacK
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VacKOf

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

open PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF
  PositivityTheory.Rg.Sw.Glob.VacG PositivityTheory.Rg.Sw.Glob.VacH PositivityTheory.Rg.Sw.Glob.VacI PositivityTheory.Rg.Sw.Glob.VacJ PositivityTheory.Rg.Sw.Glob.VacK

private theorem cnt_true_add_cnt_false {m : ℕ} (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem vacK_of : GZSch → LawN → LawNbar → LocMul → LNe → VacK := by
  intro hGZ hN hNb hLM hLNe
  unfold PositivityTheory.Rg.Sw.Glob.VacK
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL e hlev k hk
  have hl0 : l τ ≠ 0 := hLNe D ψ θ l hC.hψ hC.hθ hC.hl τ
  have hc0 : 0 < cLoc l τ := VacF.cpos hl0
  have hSch : ∀ K : ℂ, IsSch (DG (m := V.rank) (n := n) K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) :=
    fun K => VacE.isSch_DG hGZ ε (tLoc l τ) (cLoc l τ) hc0 VacF.tabs K
  obtain ⟨u, u', φ, hu, hu', hφ, hkm⟩ := VacG.kak (mR k) hk
  have hdu : IsUnit u.det := Matrix.isUnit_det_of_left_inverse hu
  have hdu' : IsUnit u'.det := Matrix.isUnit_det_of_left_inverse hu'
  have hk_eq : k = VacB.mkG (mM u) (VacB.inG_mM u hdu) * VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1 *
      VacB.mkG (mM u') (VacB.inG_mM u' hdu') := by
    apply Subtype.ext
    apply Units.ext
    change mR k = mR (VacB.mkG (mM u) (VacB.inG_mM u hdu)) * mR (VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1) *
      mR (VacB.mkG (mM u') (VacB.inG_mM u' hdu'))
    rw [VacB.mR_mkG, VacB.mR_mkG, VacB.mR_mkG]
    exact hkm
  have hLM' := hLM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC L hL
  have h1 : L (VacB.mkG (mM u') (VacB.inG_mM u' hdu')) (DG 1 (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    rw [hlev _ u' hdu' (VacB.mR_mkG _ _) _ (hSch 1)]
    exact VacH.levF_unitary e u' hu' 1 _
  have h2 := VacJ.rot_gen hC hl0 hN hNb hLM hGZ L hL e hlev φ hφ
    (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)))
  have h3 : ∀ K : ℂ, L (VacB.mkG (mM u) (VacB.inG_mM u hdu)) (DG K (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (K * (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    intro K
    rw [hlev _ u hdu (VacB.mR_mkG _ _) _ (hSch K)]
    exact VacH.levF_unitary e u hu K _
  have hLk : L k (DG 1 (fun _ _ => ((cLoc l τ : ℝ) : ℂ))) =
      DG (1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)) *
        (∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (VacE.rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ))) *
        (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e))) (fun _ _ => ((cLoc l τ : ℝ) : ℂ)) := by
    rw [hk_eq, hLM' (VacB.mkG (mM u) (VacB.inG_mM u hdu) * VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1)
      (VacB.mkG (mM u') (VacB.inG_mM u' hdu')) _ (hSch 1), h1,
      hLM' (VacB.mkG (mM u) (VacB.inG_mM u hdu)) (VacB.mkG (VacB.kth φ) (VacB.inK_kth φ).1) _ (hSch _), h2, h3]
  have hsu : star u.det = u.det⁻¹ := by
    have h := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    exact eq_inv_of_mul_eq_one_left h
  have hsu' : star u'.det = u'.det⁻¹ := by
    have h := congrArg Matrix.det hu'
    rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at h
    exact eq_inv_of_mul_eq_one_left h
  have hm : (V.rank : ℤ) = ((cnt (epsT (tLoc l τ) ε) true + cnt (epsT (tLoc l τ) ε) false : ℕ) : ℤ) := by
    rw [cnt_true_add_cnt_false]
  have hX : (∏ j, Complex.exp (Complex.I * (φ j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => Complex.exp_ne_zero _
  have hXinv : ∏ j, Complex.exp (-(Complex.I * (φ j : ℂ))) = (∏ j, Complex.exp (Complex.I * (φ j : ℂ)))⁻¹ := by
    simp only [Complex.exp_neg, Finset.prod_inv_distrib]
  have hK : 1 * (u'.det ^ e * (star u'.det) ^ ((V.rank : ℤ) - e)) *
      (∏ a, ∏ j, ((Real.cos (φ j) : ℂ) + Complex.I * (VacE.rhoT (tLoc l τ) ε a : ℂ) * (Real.sin (φ j) : ℂ))) *
      (u.det ^ e * (star u.det) ^ ((V.rank : ℤ) - e)) =
      jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) k (Complex.I • 1) := by
    rw [VacI.jF_kak e _ _ k u u' φ hu hu' hφ hkm, VacK.prodF, hsu, hsu', hm, hXinv]
    exact VacK.alg _ _ _ hdu.ne_zero hdu'.ne_zero hX e _ _
  rw [VacC.vac_eq, hLk]
  funext v
  rw [VacC.dg_const, VacC.dg_const, hK]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end
end
