module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayIn
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussD
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussF
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
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
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Tactic.ReduceModChar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussM
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussN
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussO
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussA
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocMul
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.TensInjOf
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FinitePartAdelicPointMatrix
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLaw
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawD
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.BlockMatrixDiagonalOneEqOne

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussG

section

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem conj_half_smul (Z : Matrix (Fin n) (Fin n) ℂ) : ((1 / 2 : ℂ) • (Z + Zᴴ))ᴴ = (1 / 2 : ℂ) • (Z + Zᴴ) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp [Complex.ext_iff]

theorem exists_sqrt {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y.PosDef) : ∃ S : Matrix (Fin n) (Fin n) ℂ, S * Sᴴ = Y ∧ IsUnit S.det := by
  classical
  have hH := hY.1
  let U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  let d : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ))
  have hd : d * dᴴ = diagonal (RCLike.ofReal ∘ hH.eigenvalues) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Function.comp_apply]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hY.eigenvalues_pos i).le]
    rfl
  have hS : U * d * (U * d)ᴴ = Y := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc d, hd]
    conv_rhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    simp [U, Matrix.star_eq_conjTranspose, Matrix.mul_assoc]
  refine ⟨U * d, hS, ?_⟩
  have hYu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hY.isUnit
  rw [← hS, Matrix.det_mul] at hYu
  exact isUnit_of_mul_isUnit_left hYu

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussI

section

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

variable {n : ℕ}

theorem siegelOrb : SiegelOrb := by
  intro n Z hZ
  obtain ⟨S, hSS, hSu⟩ := exists_sqrt (show ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef from hZ)
  set X : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (Z + Zᴴ) with hXdef
  have hX : Xᴴ = X := conj_half_smul Z
  have hSu' : IsUnit Sᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hSu.star
  refine ⟨mkGR (nU X) (by rw [det_nU]; exact one_ne_zero) (inG_nU hX) * mkGR (mM S) (det_mM hSu) (inG_mM hSu), ?_, ?_⟩
  · rw [mR_mul, mR_mkGR, mR_mkGR, toBlocks₂₁_mul]
    simp [nU, mM]
  · unfold actZ
    rw [mR_mul, mR_mkGR, mR_mkGR, toBlocks₁₁_mul, toBlocks₁₂_mul, toBlocks₂₁_mul, toBlocks₂₂_mul]
    simp only [nU, mM, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero]
    rw [Matrix.nonsing_inv_nonsing_inv _ hSu', Matrix.add_mul, Matrix.mul_assoc X, Matrix.nonsing_inv_mul _ hSu',
      Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hSS, hXdef, smul_smul]
    have hc : Complex.I * -(Complex.I / 2) = 1 / 2 := by
      rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I]
      norm_num
    rw [hc, ← smul_add, show Z - Zᴴ + (Z + Zᴴ) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]
    norm_num

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussP

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {D : D7} {n : ℕ}

theorem pLaw (hN : LawN) (hMul : LocMul) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
    {θ : InfFam D} {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}
    (hcx : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) {L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)}
    (hL : IsLocFact ω τ fr ι L) {e : ℤ}
    (hLev : ∀ (y : GR n) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → mR y = mM a → ∀ f, IsSch f → L y f = levF e a f)
    (q : GR n) (hq : (mR q).toBlocks₂₁ = 0) (Z : Matrix (Fin n) (Fin n) ℂ)
    (hG : IsSch (gZf ε (tLoc l τ) (cLoc l τ) Z)) :
    L q (gZf ε (tLoc l τ) (cLoc l τ) Z) = fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) q Z *
      gZf ε (tLoc l τ) (cLoc l τ) (actZ q Z) u := by
  obtain ⟨hA, hDd, hb⟩ := siegelP_data q hq
  have hAh : IsUnit ((mR q).toBlocks₁₁ᴴ).det := by rw [Matrix.det_conjTranspose]; exact hA.star
  set q1 := mkGR (nU ((mR q).toBlocks₁₂ * (mR q).toBlocks₁₁ᴴ)) (by rw [det_nU]; exact one_ne_zero) (inG_nU hb)
  set q2 := mkGR (mM (mR q).toBlocks₁₁) (det_mM hA) (inG_mM hA)
  have hq12 : q = q1 * q2 := by
    apply GR_ext
    rw [mR_mul, mR_mkGR, mR_mkGR]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (mR q), hq, hDd]
    unfold nU mM
    rw [Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hAh]
  have h2 := hLev q2 (mR q).toBlocks₁₁ hA (mR_mkGR _ _ _) _ hG
  have hs2 : IsSch (levF e (mR q).toBlocks₁₁ (gZf ε (tLoc l τ) (cLoc l τ) Z)) := by rw [← h2]; exact hL.1 q2 _ hG
  have h1 := hN D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL q1 _ hb (mR_mkGR _ _ _) _ hs2
  have hm := hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL q1 q2 _ hG
  rw [hq12, hm, h2, h1, ← hq12]
  funext u
  simp only [levF, gZf_mul]
  rw [siegelP_actZ q hq Z, siegelP_jF q hq, cnt_add, ← chN_mul_gZf ε (abs_tLoc l τ) _ _ hb u]
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLawOf

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

open GaussH

theorem gaussLaw_of : TensInj → LawN → LawM → VacK → LocMul → GZSch → LNe → GaussLaw := by
  intro hTI hN hM hV hMul hGZ hLNe D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  obtain ⟨e, hLev⟩ := hM D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL
  refine ⟨e, fun y Z hZ => ?_⟩
  have hc : 0 < cLoc l τ := by
    unfold cLoc
    exact mul_pos (mul_pos two_pos Real.pi_pos) (abs_pos.2 (hLNe D ψ θ l hcx.hψ hcx.hθ hcx.hl τ))
  have hI := isSiegel_I (n := n)
  have hGi : IsSch (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) := hGZ V.rank n ε _ _ hc (abs_tLoc l τ) _ hI
  obtain ⟨q, hq21, hqZ⟩ := siegelOrb n Z hZ
  obtain ⟨p0, k, hyq, hp0, hk⟩ := iwaGR n (y * q)
  have e1 := pLaw hN hMul hcx hL hLev q hq21 (Complex.I • 1) hGi
  rw [hqZ] at e1
  set p := cnt (epsT (tLoc l τ) ε) true
  set p' := cnt (epsT (tLoc l τ) ε) false
  have hjq : jF e p p' q (Complex.I • 1) ≠ 0 := by
    rw [siegelP_jF q hq21]
    obtain ⟨hA, -, -⟩ := siegelP_data q hq21
    exact mul_ne_zero (zpow_ne_zero _ hA.ne_zero) (zpow_ne_zero _ (hA.star).ne_zero)
  have hGZeq : gZf ε (tLoc l τ) (cLoc l τ) Z =
      fun u => (jF e p p' q (Complex.I • 1))⁻¹ * L q (gZf ε (tLoc l τ) (cLoc l τ) (Complex.I • 1)) u := by
    funext u
    rw [e1]
    field_simp
  have hVk := hV D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL e hLev k hk
  simp only [vac] at hVk
  rw [hGZeq, locLin hTI hcx hL y _ (hL.1 q _ hGi),
    ← hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL y q _ hGi, hyq,
    hMul D n V ψ χ θ μ ω H l s ν τ ε fr ι hcx L hL p0 k _ hGi, hVk, locLin hTI hcx hL p0 _ hGi,
    pLaw hN hMul hcx hL hLev p0 hp0 (Complex.I • 1) hGi]
  have cy := (cocycleZ n e p p' y q (Complex.I • 1) hI).2.2.2
  have cp := (cocycleZ n e p p' p0 k (Complex.I • 1) hI).2.2.2
  rw [hqZ] at cy
  rw [actZ_K hk] at cp
  rw [hyq] at cy
  have hact : actZ p0 (Complex.I • 1) = actZ y Z := cp.1.symm.trans cy.1
  have hrel : jF e p p' y Z * jF e p p' q (Complex.I • 1) = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) :=
    cy.2.symm.trans cp.2
  have hjy : jF e p p' y Z = jF e p p' p0 (Complex.I • 1) * jF e p p' k (Complex.I • 1) * (jF e p p' q (Complex.I • 1))⁻¹ := by
    rw [← hrel]; field_simp
  funext u
  rw [hact, hjy]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussJ

section

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem mul_I_smul_one (X : Matrix (Fin n) (Fin n) ℂ) : X * (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) = Complex.I • X := by
  rw [Matrix.mul_smul, Matrix.mul_one]

theorem conj_I_smul_one : (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = -(Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_I, neg_smul]

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WeightFactorEqAutomorphy

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {n : ℕ}

theorem weight_factor_eq_automorphy (p q : ℕ) (e : ℤ) (y : GR n) : F0 p q e y = jF e p q y (Complex.I • 1) := by
  simp only [F0, f0, jF, u1, u2, conj_I_smul_one, Matrix.mul_neg, mul_I_smul_one]
  push_cast
  ring

end PositivityTheory.Rg.Sw.Glob.GaussH

namespace PositivityTheory.Rg.Sw.Glob

open GaussH

theorem lawM_of : TensInj → LawM := by
  intro hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  obtain ⟨k, ⟨j, hj⟩, hk⟩ := LocLawH.chi_exp hC.hθ hC.hχ hC.hη τ
  refine ⟨k - j, fun y a ha hy f hf => ?_⟩
  set A : GL (Fin n) ℂ := Matrix.GeneralLinearGroup.mkOfDetNeZero a ha.ne_zero with hAdef
  have hAv : A.1 = a := rfl
  have hAi : (A⁻¹).1 = a⁻¹ := by rw [Matrix.coe_units_inv, hAv]
  have hyA : y = LocLawH.mOf A := by
    apply GR_ext
    rw [hy, LocLawH.mR_mOf, hAv, hAi, Matrix.conjTranspose_nonsing_inv]
    rfl
  have hy0 : (mR (LocLawH.mOf A)).toBlocks₂₁ = 0 := by simp [LocLawH.mR_mOf]
  have haOf : LocLawH.aOf (LocLawH.mOf A) hy0 = A := Units.ext (by rw [LocLawH.aOf_val, LocLawH.mR_mOf]; simp)
  have hsc := LocLawH.scal hC.hθ hσ k j hk hj (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false)
    (cnt_add _) (LocLawH.mOf A) hy0
  rw [haOf] at hsc
  refine hTI D n V ψ χ θ μ ω H l s ν τ ε fr ι hC _ _ fun Ψ hΨ => ?_
  rw [← hL.2 y Ψ hΨ f hf]
  funext x
  rw [hyA, hC.hω.levi _ (LocLawH.unitAt hσ τ A) (LocLawH.mat_mOf hσ hC.hι A), hsc, weight_factor_eq_automorphy,
    siegelP_jF _ hy0, cnt_add]
  have hbl : (mR (LocLawH.mOf A)).toBlocks₁₁ = a := by rw [LocLawH.mR_mOf]; simp [hAv]
  rw [hbl]
  have hΨx : Ψ (HMul.hMul x (LocLawH.unitAt hσ τ A).1 : Mx D V.rank n) = Ψ x := by
    refine hΨ.1 _ _ (fun τ' h => ?_) ?_
    · rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_ne hσ h, Matrix.mul_one]
    · rw [LocLawH.unitAt_val, Matrix.map_mul, LocLawH.finite_part_adelic_point_matrix hσ, Matrix.mul_one]
  simp only [tens, hΨx, levF]
  rw [LocLawH.unitAt_val, LocLawH.compAt_mulM, LocLawH.component_adelic_point_matrix hσ, hAv, ← Matrix.mul_assoc]
  have hof : (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) = fr⁻¹ * compAt θ τ x := rfl
  rw [hof]
  ring

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussTop

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem gaussLaw_of' (hV : VacK) (hG : GZSch) : GaussLaw := by
  have hT : TensInj := tensInj_of awayIn
  exact gaussLaw_of hT (lawN_of unipTau hT) (lawM_of hT) hV (locMul_of hT) hG lNe

end PositivityTheory.Rg.Sw.Glob
end
end
