module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivOne
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasTemperateGrowthEvalPoly
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellTop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInst
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvac
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLaw
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousWeilSchrodingerStandardUnnEvalZero
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawA
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL
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
import Mathlib.Tactic.Linter.Style
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawL
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocRho
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacD
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.VanishTop2

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocLawB

section

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

theorem lIlin : LIlin := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hC.hθ
  have hfr : IsUnit fr.det := hC.hfr.1
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have mem : ∀ P, tens θ τ fr (fP (cLoc l τ) P) (LocLawH.psi0 θ V n l s τ) ∈ schwartzA θ V.rank n := fun P =>
    (hT D n V θ l s τ ε fr hC.hθ (LocLawH.cx_lne hC) hC.hs hC.hfr _ hΨ P).1
  refine ⟨fun y a P Q => ?_, fun P => ?_⟩
  · apply LocLawH.tens_cancel hσ V l s τ hfr
    have hlin : phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (a • P + Q) =
        a • phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P + phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) Q := by
      apply Subtype.ext
      rw [LocLawH.phiS_val (mem _), Submodule.coe_add, Submodule.coe_smul, LocLawH.phiS_val (mem P), LocLawH.phiS_val (mem Q)]
      funext x
      simp only [tens, fP, evX, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), MvPolynomial.smul_eval]
      ring
    rw [← hL y _ hΨ (a • P + Q), hlin, map_add (f := _), map_smul, Submodule.coe_add, Submodule.coe_smul, hL y _ hΨ P,
      hL y _ hΨ Q]
    funext x
    simp only [tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    show a * (L y (fP (cLoc l τ) P) _ * _) + L y (fP (cLoc l τ) Q) _ * _ =
      (a * L y (fP (cLoc l τ) P) _ + L y (fP (cLoc l τ) Q) _) * _
    ring
  · apply LocLawH.tens_cancel hσ V l s τ hfr
    have e := hL 1 _ hΨ P
    rw [map_one, map_one, Module.End.one_apply, LocLawH.phiS_val (mem P)] at e
    exact e.symm

theorem lIcont : LIcont := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL P
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have key : sLd L (cLoc l τ) P = fun y => (ω (ι y) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).1 0 := by
    funext y
    rw [hL y _ hΨ P, LocLawH.tens_zero, LocLawH.cmTraceAdditiveCharacter_zero, mul_one]
    rfl
  rw [key]
  obtain ⟨𝓕, h𝓕⟩ := hC.hμ
  exact (GlobalTheory.StdUnn.weilSch_apply_zero_continuous D n V ψ hC.hψ χ hC.hχ hC.hη θ hC.hθ μ 𝓕 h𝓕 ω hC.hω
    (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).comp hC.hι.1

theorem lIkact : LIkact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC hT L hL ρ hρ P g k hk
  have hΨ := LocLawH.unitaryFinitePointsToGLFiniteAdeles_isUnitary θ V n l s τ
  have mem : ∀ P, tens θ τ fr (fP (cLoc l τ) P) (LocLawH.psi0 θ V n l s τ) ∈ schwartzA θ V.rank n := fun P =>
    (hT D n V θ l s τ ε fr hC.hθ (LocLawH.cx_lne hC) hC.hs hC.hfr _ hΨ P).1
  have hk' : ω (ι k) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P) =
      phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (ρ k P) := by
    apply Subtype.ext
    rw [hL k _ hΨ P, hρ k P hk, LocLawH.phiS_val (mem _)]
  have e : (ω (ι (g * k)) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) P)).1 0 =
      (ω (ι g) (phiS θ τ fr (cLoc l τ) (LocLawH.psi0 θ V n l s τ) (ρ k P))).1 0 := by
    rw [map_mul, map_mul, Module.End.mul_apply, hk']
  rw [hL (g * k) _ hΨ P, hL g _ hΨ (ρ k P), LocLawH.tens_zero, LocLawH.tens_zero, LocLawH.cmTraceAdditiveCharacter_zero, mul_one, mul_one] at e
  exact e

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVacC

section

@[expose] public section

noncomputable section

open Matrix Filter Topology Polynomial
open scoped ComplexConjugate

namespace PositivityTheory.Rg.Sw.Glob.Vac

variable {n : ℕ}

theorem inG_JJ : InG (JJ n) := by
  unfold InG
  rw [JJ_conjTranspose, Matrix.mul_assoc, JJ_sq, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, neg_neg]

theorem nU_mul (b c : Matrix (Fin n) (Fin n) ℂ) : nU b * nU c = nU (b + c) := by
  simp [nU, fromBlocks_multiply, add_comm]

theorem nU_zero : nU (0 : Matrix (Fin n) (Fin n) ℂ) = 1 := by simp [nU, fromBlocks_one]

theorem inG_nU {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) : InG (nU b) := by
  unfold InG; simp [nU, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, hb.eq]

def jjE : GR n := ⟨⟨JJ n, -JJ n, by rw [Matrix.mul_neg, JJ_sq, neg_neg], by rw [Matrix.neg_mul, JJ_sq, neg_neg]⟩, inG_JJ⟩

def nuE (b : Matrix (Fin n) (Fin n) ℂ) (hb : b.IsHermitian) : GR n :=
  ⟨⟨nU b, nU (-b), by rw [nU_mul, add_neg_cancel, nU_zero], by rw [nU_mul, neg_add_cancel, nU_zero]⟩, inG_nU hb⟩

def nbar (s : ℝ) : M2 n := fromBlocks 1 0 ((s : ℂ) • 1) 1

theorem nbar_mul (s t : ℝ) : nbar (n := n) s * nbar t = nbar (s + t) := by
  simp [nbar, fromBlocks_multiply, add_smul, add_comm]

theorem nbar_zero : nbar (n := n) 0 = 1 := by simp [nbar, fromBlocks_one]

theorem inG_nbar (s : ℝ) : InG (nbar (n := n) s) := by
  unfold InG
  simp [nbar, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.conjTranspose_smul, Complex.conj_ofReal]

def nbE (s : ℝ) : GR n :=
  ⟨⟨nbar s, nbar (-s), by rw [nbar_mul, add_neg_cancel, nbar_zero], by rw [nbar_mul, neg_add_cancel, nbar_zero]⟩, inG_nbar s⟩

theorem nbE_zero : nbE (n := n) 0 = 1 := Subtype.ext (Units.ext nbar_zero)

theorem cont_nbar : Continuous (nbar (n := n)) := by
  unfold nbar
  exact Continuous.matrix_fromBlocks continuous_const continuous_const
    (Complex.continuous_ofReal.smul continuous_const) continuous_const

theorem cont_nbE : Continuous (nbE (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  refine Units.continuous_iff.mpr ⟨cont_nbar, ?_⟩
  exact cont_nbar.comp continuous_neg

theorem lower_left_block_mul_lowering (g : GR n) (s : ℝ) :
    (mR (g * nbE s)).toBlocks₂₁ = (mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂ := by
  rw [mR_mul]
  conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
  show (fromBlocks _ _ _ _ * nbar s).toBlocks₂₁ = _
  simp [nbar, fromBlocks_multiply]

theorem finite_bad (g : GR n) :
    {s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0}.Finite := by
  set C := (mR g).toBlocks₂₁
  set D := (mR g).toBlocks₂₂
  set P : Polynomial ℂ := det (C.map Polynomial.C + (Polynomial.X : Polynomial ℂ) • D.map Polynomial.C) with hP
  have hev : ∀ z : ℂ, P.eval z = (C + z • D).det := by
    intro z
    rw [hP, ← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp
    ring
  have hP0 : P ≠ 0 := by
    intro h0
    have hz := hev Complex.I
    rw [h0, Polynomial.eval_zero] at hz
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hz.symm
    apply hv
    apply vec_zero g (-Complex.I) (by simp) v
    have hm : (-Complex.I) • C + D = (-Complex.I) • (C + Complex.I • D) := by
      rw [smul_add, smul_smul]
      simp
    rw [hm, Matrix.vecMul_smul, hv0, smul_zero]
  apply ((P.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn).subset
  intro s hs
  simp only [Set.mem_setOf_eq] at hs
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP0,
    Polynomial.IsRoot, hev]
  exact hs

theorem dense_cell : Dense {g : GR n | ((mR g).toBlocks₂₁).det ≠ 0} := by
  intro g
  have hT : Tendsto (fun s : ℝ => g * nbE s) (𝓝[≠] 0) (𝓝 g) := by
    have hc : Continuous fun s : ℝ => g * nbE s := continuous_const.mul cont_nbE
    have h := hc.tendsto 0
    rw [nbE_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  have hfin := finite_bad g
  have hZ : IsClosed ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) :=
    (hfin.subset Set.sdiff_subset).isClosed
  have h0 : (0 : ℝ) ∉ ({s : ℝ | ((mR g).toBlocks₂₁ + (s : ℂ) • (mR g).toBlocks₂₂).det = 0} \ {0}) := by simp
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hZ.isOpen_compl.mem_nhds h0), self_mem_nhdsWithin] with s hs hs0
  show ((mR (g * nbE s)).toBlocks₂₁).det ≠ 0
  rw [lower_left_block_mul_lowering]
  intro hdet
  exact hs ⟨hdet, hs0⟩

theorem bigcell (g : GR n) (hγ : ((mR g).toBlocks₂₁).det ≠ 0) :
    ∃ (y h : GR n) (b : Matrix (Fin n) (Fin n) ℂ), (mR y).toBlocks₂₁ = 0 ∧ b.IsHermitian ∧ mR h = JJ n * nU b ∧
      g = y * h := by
  set C := (mR g).toBlocks₂₁ with hC
  set D := (mR g).toBlocks₂₂ with hD
  have hu : IsUnit C.det := isUnit_iff_ne_zero.mpr hγ
  have huH : IsUnit Cᴴ.det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hγ)
  have hb : (C⁻¹ * D).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc Dᴴ * Cᴴ⁻¹ = C⁻¹ * (C * Dᴴ) * Cᴴ⁻¹ := by rw [nonsing_inv_mul_cancel_left C _ hu]
      _ = C⁻¹ * (D * Cᴴ) * Cᴴ⁻¹ := by rw [hC, hD, lagr g]
      _ = C⁻¹ * D := by rw [← Matrix.mul_assoc, mul_nonsing_inv_cancel_right Cᴴ _ huH]
  refine ⟨g * (jjE * nuE (C⁻¹ * D) hb)⁻¹, jjE * nuE (C⁻¹ * D) hb, C⁻¹ * D, ?_, hb, ?_, by group⟩
  · have hinv : mR (jjE * nuE (C⁻¹ * D) hb)⁻¹ = nU (-(C⁻¹ * D)) * (-JJ n) := by
      rw [_root_.mul_inv_rev, mR_mul]
      rfl
    rw [mR_mul, hinv]
    conv_lhs => rw [← fromBlocks_toBlocks (mR g)]
    simp [nU, JJ, fromBlocks_multiply, fromBlocks_neg, ← hC, ← hD]
    rw [mul_nonsing_inv_cancel_left C D hu, neg_add_cancel]
  · rw [mR_mul]
    rfl

end PositivityTheory.Rg.Sw.Glob.Vac
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocVac

section

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.Glob

open Vac

theorem lIvac : LIvac := by
  intro m n ε c t p q e hc hpq S C hS h1 hy hcell
  have hα : ((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)) ≠ 0 := by
    apply mul_ne_zero <;> apply zpow_ne_zero <;> apply pow_ne_zero <;> simp
  have key : ∀ g : GR n, (toBlocks₂₁ (mR g)).det ≠ 0 →
      S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g hg
    obtain ⟨y, h, b, hy0, hb, hh, rfl⟩ := bigcell g hg
    rw [hy y h hy0, hcell h b hb hh, secN_eval ε c t p q hc hpq b hb, vacuum_section_mul_parabolic p q e y h hy0,
      vacuum_section_big_cell p q e h b hh, mul_zpow, mul_zpow]
    field_simp
  have hall : ∀ g, S g = (C * ((Real.pi : ℂ) ^ n / (c : ℂ) ^ n) ^ (p + q) /
        (((-Complex.I) ^ n) ^ (-(p : ℤ)) * (Complex.I ^ n) ^ (-(q : ℤ)))) * F0 p q e g := by
    intro g
    exact congrFun (Continuous.ext_on dense_cell hS (continuous_const.mul (continuous_vacuum_section p q e)) key) g
  have hlam := hall 1
  rw [h1, weight_factor_one, mul_one] at hlam
  intro g
  rw [hall g, ← hlam, one_mul]

end PositivityTheory.Rg.Sw.Glob
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstTop

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem locInst_of_cell_kvac (hc : LIcell) (hk : LIkvac) (hT : TensMem) : LocInst :=
  locInst_of hT lIl lIlin lIlaw hc lIcont lIrho lIkact lIvac hk

theorem locInst_of_cell (hc : LIcell) (hT : TensMem) : LocInst := locInst_of_cell_kvac hc lIkvac hT

theorem locInst_of_away (hA : AwayAct) (hT : TensMem) : LocInst :=
  locInst_of_cell (lIcell_of' hA lIcont lIlaw lIvac) hT

end PositivityTheory.Rg.Sw.Glob
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Top4

section

@[expose] public section

namespace PositivityTheory.Rg.Sw.Glob

theorem top5 (hLF : LocFact) (hAA : AwayAct) (hLC : LieComm) (hDO : DerivOne) (hId : GIdil) (hC : PositivityTheory.PfSWUS.CoefND) :
    ∀ D n V ψ χ θ μ ω H l s ν Φ, PositivityTheory.PfSWUS.Std D n V ψ χ θ μ ω H l s ν Φ → PositivityTheory.PfSWUS.InRange V n → 1 ≤ n →
      ∀ g, GlobalTheory.Cont.HolValueAt (PositivityTheory.PfSWUS.eis ω H Φ g) (GlobalTheory.StdUnn.s0 V n) (GlobalTheory.StdUnn.thetaInt ω ν Φ g) :=
  top3 hLF hAA (locInst_of_away hAA tensMem) hLC hDO hId hC

end PositivityTheory.Rg.Sw.Glob
end
end
