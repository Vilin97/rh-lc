module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXCC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InvMulOfUnitri
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.EmbVHomInjective
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MemHermitianStandardLatticeIffPairingIntegral
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibOnto
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibCut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AdmNPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianSumFrames
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealFramesCharacters
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealHermitianForms
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibRat
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ThetaIntMem

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatF

section

@[expose] public section

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace LatF

open Alg

variable {D : D7}

local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

theorem mem_mul_inv_of {I J : FI} (hI : I ≠ 0) {x : D.host.E} (h : ∀ c ∈ I, c * x ∈ J) : x ∈ J * I⁻¹ := by
  have h1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * I ≤ J := by
    rw [FractionalIdeal.mul_le]
    intro s hs c hc
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hs
    rw [Algebra.smul_def, mul_assoc, mul_comm x c]
    exact LatA.fi_smul_mem (h c hc) z
  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x ≤ J * I⁻¹ := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * I * I⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ J * I⁻¹ := FractionalIdeal.mul_le.mpr fun i hi j hj => FractionalIdeal.mul_mem_mul (h1 hi) hj
  exact h2 (FractionalIdeal.mem_spanSingleton_self _ x)

theorem mul_mem_cancel {I J K : FI} (hK : K ≠ 0) {x y : D.host.E} (hx : x ∈ I * K⁻¹) (hy : y ∈ K * J) :
    x * y ∈ I * J := by
  have h := FractionalIdeal.mul_mem_mul hx hy
  have e : I * K⁻¹ * (K * J) = I * J := by
    calc I * K⁻¹ * (K * J) = I * J * (K⁻¹ * K) := by ring
      _ = I * J := by rw [inv_mul_cancel₀ hK, mul_one]
  rwa [e] at h

variable (X : HidaSetting D)

theorem aa_ne (Y : HidaSetting D) (a : Fin D.R.rS) : aaD D a ≠ 0 := Formalism.L2.SG.Pf.NcReal.JX.CovB.aaD_ne_zero Y a

theorem e_mem {a : Fin D.R.rS} {c : D.host.E} (hc : c ∈ aaD D a) : c • X.eX a ∈ (VS D).L0 := by
  rw [X.Lam_split]
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, c, hc, rfl⟩))

theorem f_mem {a : Fin D.R.rS} {c : D.host.E} (hc : c ∈ (aaD D a)⁻¹) : c • X.fY a ∈ (VS D).L0 := by
  rw [X.Lam_split]
  exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, c, hc, rfl⟩)

variable {X}

theorem lattice_map_preserves_base {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    {y : (VS D).V} (hy : y ∈ (VS D).L0) : m y ∈ (VS D).L0 := by
  rw [← hL]; exact ⟨y, hy, rfl⟩

theorem gmap_symm {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0) :
    Formalism.HermitianLatticesTheory.gmap m.symm (VS D).L0 = (VS D).L0 := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hL] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    show m.symm (m w) ∈ (VS D).L0
    simpa using hw
  · intro hy
    exact ⟨m y, lattice_map_preserves_base hL hy, by simp⟩

theorem ex_shape {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    (b d : Fin D.R.rS) : (VS D).hT (X.fY b) (m (X.eX d)) ∈ aaD D b * (aaD D d)⁻¹ := by
  refine mem_mul_inv_of (aa_ne X d) fun c hc => ?_
  have h := Formalism.L2.SG.Pf.LatDict.coefficient_mem_fractional_ideal X b (lattice_map_preserves_base hL (e_mem X hc))
  rw [map_smul, map_smul, smul_eq_mul] at h
  exact h

theorem fa_shape {m : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hL : Formalism.HermitianLatticesTheory.gmap m (VS D).L0 = (VS D).L0)
    (b a : Fin D.R.rS) : (VS D).hT (X.fY b) (m (X.fY a)) ∈ aaD D b * aaD D a := by
  have hne : (aaD D a)⁻¹ ≠ 0 := inv_ne_zero (aa_ne X a)
  have := mem_mul_inv_of hne (J := aaD D b) (x := (VS D).hT (X.fY b) (m (X.fY a))) fun c hc => by
    have h := Formalism.L2.SG.Pf.LatDict.coefficient_mem_fractional_ideal X b (lattice_map_preserves_base hL (f_mem X hc))
    rw [map_smul, map_smul, smul_eq_mul] at h
    exact h
  rwa [inv_inv] at this

variable {u : D.what₂.Word} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}

theorem Xinv (hn : NFl X u n) : Xq X n.symm * Xq X n = 1 := by
  refine Matrix.ext fun b a => ?_
  simp only [Matrix.mul_apply, Xq]
  rw [Finset.sum_congr rfl fun d _ => mul_comm _ _, ← hT_sumR]
  have e : ∑ d, (VS D).hT (X.fY d) (n (X.eX a)) • n.symm (X.eX d) = n.symm (n (X.eX a)) := by
    conv_rhs => rw [Xq_expand hn a]

    rw [map_sum]
    simp only [map_smul, Xq]
  rw [e, LinearEquiv.symm_apply_apply, hfe, Matrix.one_apply]

theorem rows_mem (hL : Formalism.HermitianLatticesTheory.gmap n (VS D).L0 = (VS D).L0) (b : Fin D.R.rS) : xq X n b ∈ aaLb X b := by
  have hβ : ∀ β ∈ (aaD D b)⁻¹, β • xq X n b ∈ X.Lb := by
    intro β hβ
    have h := lattice_map_preserves_base (gmap_symm hL) (f_mem X hβ)
    rw [map_smul] at h
    have := ((LatA.mem_hermitianStandardLattice_iff_pairing_integral X _).1 h).2.2
    rwa [pW_smul] at this
  have h1 : (1 : D.host.E) ∈ aaD D b * (aaD D b)⁻¹ := by
    rw [mul_inv_cancel₀ (aa_ne X b)]; exact FractionalIdeal.one_mem_one _
  have key : ∀ t ∈ ((aaD D b * (aaD D b)⁻¹ : FI) : Submodule (𝓞 D.host.E) D.host.E),
      t • xq X n b ∈ aaLb X b := by
    intro t ht
    rw [FractionalIdeal.coeToSubmodule_mul] at ht
    refine Submodule.mul_induction_on ht (fun α hα β hβ' => ?_) (fun s t hs ht => ?_)
    · rw [mul_smul]
      exact Submodule.subset_span ⟨α, hα, β • xq X n b, hβ β hβ', rfl⟩
    · rw [add_smul]; exact add_mem hs ht
  simpa using key 1 h1

end LatF


open Alg LatF in
theorem dictLatF_holds : DictLatF := by
  intro D X u n hn hL
  refine ⟨fun b a _ => ex_shape hL b a, fun b => rows_mem hL b, fun b a => ?_⟩
  have hinv : (Xq X n)⁻¹ = Xq X n.symm := Matrix.inv_eq_left_inv (Xinv hn)
  show ((Xq X n)⁻¹ * Aq X n) b a ∈ _
  rw [hinv, Matrix.mul_apply]
  refine Submodule.sum_mem _ fun d _ => ?_
  exact mul_mem_cancel (aa_ne X d) (ex_shape (gmap_symm hL) b d) (fa_shape hL d a)

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibPl

section

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pl

variable {D : D7} (X : HidaSetting D)

theorem umat_rv {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hRL : RatLink X x n) (v : InfinitePlace X.B.I.F)
    (y : (VS D).V) : uMat (x.1 v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd (n y)) := by
  obtain ⟨M, -, hv, -, hcrd⟩ := hRL
  rw [hv v, Formalism.L2.SG.Pf.rv_mulVec, ← hcrd]

theorem inv_map_emb {m : ℕ} {K L : Type*} [Field K] [Field L] (f : K →+* L) (A : Matrix (Fin m) (Fin m) K) :
    (A.map f)⁻¹ = A⁻¹.map f := by
  have h1 : (A.map f).det = f A.det := (f.map_det A).symm
  have h2 : (A.map f).adjugate = A.adjugate.map f := (f.map_adjugate A).symm
  rw [Matrix.inv_def, Matrix.inv_def, h1, h2, Ring.inverse_eq_inv', Ring.inverse_eq_inv', ← map_inv₀]
  ext i j
  simp [Matrix.smul_apply]

theorem hJ_span_ef (v : InfinitePlace X.B.I.F) (α β : Fin D.R.rS → D.host.E) (w : Fin X.B.I.n → ℂ)
    (he : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) w = 0)
    (hf : ∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) w = 0) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.crd (∑ c, α c • X.eX c + ∑ c, β c • X.fY c))) w = 0 := by
  rw [Formalism.L2.SG.NormCut.crd_add', Formalism.L2.SG.NormCut.crd_sum', Formalism.L2.SG.NormCut.crd_sum']
  simp only [Formalism.L2.SG.NormCut.crd_smul']
  have rv_add (a b : Fin X.B.I.n → X.B.I.E) : rv X.B.I v (a + b) = rv X.B.I v a + rv X.B.I v b := by
    unfold rv
    rw [← Matrix.mulVec_add]
    congr 1
    ext i
    simp
  rw [rv_add, Formalism.L2.SG.RealObj.RealFramesCharacters.rv_sum, Formalism.L2.SG.RealObj.RealFramesCharacters.rv_sum,
    Formalism.L2.SG.RealObj.InfCut.ProductExactness.hJ_add_l, Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames.hJ_sum_left,
    Formalism.L2.SG.RealObj.HermitianSumRootCoordinateFrames.hJ_sum_left]
  simp only [he, hf, mul_zero, Finset.sum_const_zero, add_zero]

end Pl

section Main

theorem dictionary_place_holds : DictPlace := by
  intro D X u x n hRL hNF
  set ψ : InfinitePlace X.B.I.F → D.host.E →+* ℂ := fun v => embS D (X.pl v) with hψ
  have hxM : ∀ v, LsNc5.xMat X v x.1 = (Xq X n).map (ψ v) := fun v => by
    ext b a
    simp only [LsNc5.xMat, LsNc5.fV, LsNc5.eV, Matrix.map_apply]
    rw [show X.eR a = X.crd (X.eX a) from rfl, umat_rv X hRL v, show X.fR b = X.crd (X.fY b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX]
    rfl
  have haM : ∀ v, LsNc5.aMat X v x.1 = (Aq X n).map (ψ v) := fun v => by
    ext b a
    simp only [LsNc5.aMat, LsNc5.fV, Matrix.map_apply]
    rw [show X.fR a = X.crd (X.fY a) from rfl, umat_rv X hRL v, show X.fR b = X.crd (X.fY b) from rfl,
      Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX]
    rfl
  have hmM : ∀ v, LsNc5.mMat X v x.1 = (Mq X n).map (ψ v) := fun v => by
    unfold LsNc5.mMat Mq
    rw [hxM, haM, inv_map_emb, Matrix.map_mul]

  have hrow : ∀ v b (w : Fin X.B.I.n → ℂ), (∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) w = 0) →
      (∀ c, hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) w = 0) →
      hJ (X.B.I.ε v) (LsNc5.fV X v b) (uMat (x.1 v) *ᵥ w) = hJ (X.B.I.ε v) (rv X.B.I v (X.crd (xq X n b))) w := by
    intro v b w he hf
    have h1 := Formalism.L2.SG.RealObj.InfCut.RealHermitianForms.hJ_inv_r (X.B.I.ε v) (x.1 v)⁻¹ (LsNc5.fV X v b) w
    rw [inv_inv] at h1
    rw [h1]
    have h2 : uMat (x.1 v)⁻¹ *ᵥ LsNc5.fV X v b = rv X.B.I v (X.crd (n.symm (X.fY b))) :=
      umat_rv X (Formalism.L2.SG.TermOp.Vanish.ratLink_inv X hRL) v (X.fY b)
    rw [h2]
    have hy : n.symm (X.fY b) = xq X n b + (∑ c, (VS D).hT (X.fY c) (n.symm (X.fY b)) • X.eX c +
        ∑ c, (VS D).hT (X.eX c) (n.symm (X.fY b)) • X.fY c) := by
      simp only [xq, pW]; abel
    have rv_add (a b : Fin X.B.I.n → X.B.I.E) : rv X.B.I v (a + b) = rv X.B.I v a + rv X.B.I v b := by
      unfold rv
      rw [← Matrix.mulVec_add]
      congr 1
      ext i
      simp
    rw [hy, Formalism.L2.SG.NormCut.crd_add', rv_add, Formalism.L2.SG.RealObj.InfCut.ProductExactness.hJ_add_l,
      hJ_span_ef X v _ _ w he hf, add_zero]
  funext p
  rcases p with ((p | b) | (p | a))
  · funext v
    show LsNc5.xMat X v x.1 p.1.1 p.1.2 = embS D (X.pl v) (Xq X n p.1.1 p.1.2)
    rw [hxM]; rfl
  · funext v j
    show (if h : j.val < D.R.k then LsNc5.phiMat X u v x.1 b ⟨j.val, h⟩ else LsNc5.yVec X u v x.1 b) =
      rowV X u (xq X n b) v j
    unfold rowV
    split_ifs with h
    · exact hrow v b _ (fun c => ((X.wfr_perp u v ⟨j.val, h⟩).1 c).1) (fun c => ((X.wfr_perp u v ⟨j.val, h⟩).1 c).2)
    · refine hrow v b _ (fun c => ?_) (fun c => ?_)
      · show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX c))) (rv X.B.I v (X.crd (X.zu u))) = 0
        rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u c).1, map_zero]
      · show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.fY c))) (rv X.B.I v (X.crd (X.zu u))) = 0
        rw [Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.hJ_rvX, (X.zu_orth u c).2, map_zero]
  · funext v
    show (LsNc5.mMat X v x.1 p.1.1 p.1.2 - star (LsNc5.mMat X v x.1 p.1.2 p.1.1)) / 2 =
      (embS D (X.pl v) (Mq X n p.1.1 p.1.2) - star (embS D (X.pl v) (Mq X n p.1.2 p.1.1))) / 2
    rw [hmM]; rfl
  · funext v
    show (LsNc5.mMat X v x.1 a a).im = (embS D (X.pl v) (Mq X n a a)).im
    rw [hmM]; rfl

end Main

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAsm

section

@[expose] public section

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

theorem nofibLat_of_rest (hL : DictLat) (hE : DictEx) (hF : FibQ) (hO : FibOnto) : NOfibLat := by
  have hR : NOratC := by first | exact @noratC_holds | exact @noratC_proved | exact @noratC | exact @nOratC_holds | exact @noratC_of | exact @NOratC_holds
  have hG : DictGram := by first | exact @dictGram_holds | exact @dictGram_proved | exact @dictGram | exact @DictGram_holds | exact @dictGram_of
  have hP : DictPlace := by first | exact @dictionary_place_holds | exact @dictPlace_holds | exact @dictPlace_proved | exact @dictPlace | exact @DictPlace_holds | exact @dictPlace_of
  exact @nofibLat_of hR hG hL hE hP hF hO

theorem nofib_of_rest (hL : DictLat) (hE : DictEx) (hF : FibQ) (hO : FibOnto) : NOfib := @Formalism.L2.SG.Pf.NcReal.JX.nofib_of (@nofibLat_of_rest hL hE hF hO)

theorem nOfib_of_dict_fib (hB : DictLatB) (hF : FibQ) (hO : FibOnto) : NOfib := by
  have hLF : DictLatF := by first | exact @dictLatF_proof | exact @dictLatF_holds | exact @dictLatF_proved | exact @dictLatF | exact @DictLatF_holds | exact @dictLatF_of
  have hL : DictLat := @dictLat_of hLF hB
  have hE : DictEx := @Ex.dictEx_holds
  exact @nofib_of_rest hL hE hF hO

theorem nofib_of_fib (hF : FibQ) (hO : FibOnto) : NOfib := by
  have hB : DictLatB := by first | exact @dictLatB_proof | exact @dictLatB_holds | exact @dictLatB_proved | exact @dictLatB | exact @DictLatB_holds | exact @dictLatB_of
  exact @nOfib_of_dict_fib hB hF hO

theorem nofib_of_fibQ (hF : FibQ) : NOfib := by
  have hO : FibOnto := by first | exact @fibOnto_proof | exact @fibOnto_holds | exact @fibOnto_proved | exact @fibOnto | exact @FibOnto_holds | exact @fibOnto_of
  exact @nofib_of_fib hF hO

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibFibC

section

@[expose] public section

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

theorem nofib_holds : Formalism.L2.SG.Pf.NcReal.JX.NOfib := nofib_of_fibQ fibQ_holds

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end
