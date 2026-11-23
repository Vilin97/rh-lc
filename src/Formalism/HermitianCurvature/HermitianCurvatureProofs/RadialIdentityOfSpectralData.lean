module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfQuadratic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDGqRes
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDJNice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDResRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterpolationInverseMatrixSumIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
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
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVpic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TriangleInequalityAtPlace
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfWaveQQ
import Mathlib.Tactic.TypeStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermMulVecMulVec
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocOpAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellZetaMinors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SiteZeroMatrixEntry

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDStartCoord

section

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_start_coordinates : RDStartCoord := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hL, hQ, -⟩ := hD
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  have ht : ∀ Y (a b : Fin 2) l (i : Fin 6), Commute (X.t Y a b) (X.op l i) :=
    fun Y a b l i => Formalism.FourierDecayAlt.P.NFx1.TC.t_op_comm X Y a b l i
  intro Y a b l x hx
  have hm : Commute (X.QQ Y a b) x := by
    rw [Formalism.FourierDecayAlt.P.NFx3.QQ_apply]
    simp only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 0) (ht (star Y) b a l 3).neg_right
    · rw [hpb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 3) (ht (star Y) b a l 0).neg_right
    · rw [hc l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 1) (ht (star Y) b a l 4)
    · rw [hci l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 2) (ht (star Y) b a l 5)
    · rw [hcb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 4) (ht (star Y) b a l 1)
    · rw [hcbi l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (ht Y a b l 5) (ht (star Y) b a l 2)
  rw [hQ Y, Matrix.smul_apply]
  exact hm.smul_left _

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDWaveFF

section

@[expose] public section

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section WaveFF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem rdb_one_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, 1, (nSubgroup k r).1, by simp⟩

theorem rdb_n_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {n : Mx k r} (hn : n ∈ Nlev k r 0) : n ∈ Sset k r z :=
  ⟨1, Formalism.FourierDecayAlt.P.TBBx2.one_mem_UW k r z, n, hn.1, by simp⟩

theorem rdb_h_mem_Sset (z : Fin (2 * r + k + 1) → ℂ) {h : Mx k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, (nSubgroup k r).1, by simp⟩

theorem rdb_fsv_dmin_contDiff (z z' : Fin (2 * r + k + 1) → ℂ) (s : ℂ) (h1 : 1 < r + 2) :
    ContDiff ℝ ∞ (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) := by
  have e : (fun g : Mx k r => fsv s (Dmin k r z z' g ⟨1, h1⟩)) = fun g =>
      Complex.exp (Formalism.FourierDecayAlt.P.PBFV.phaseL s (Formalism.FourierDecayAlt.P.JCx2.mnLinHerm (fvec k r z' 0) (fvec k r z 0)) g) :=
    funext fun g => Formalism.FourierDecayAlt.P.PBFV.fsv_dmin_one s z z' g h1
  rw [e]
  exact Complex.contDiff_exp.comp (ContinuousLinearMap.contDiff _)

theorem rdb_wvG_mem_FFl {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (s : ℂ)
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {Dm : Set (Mx k r)} {J : Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ FFl k r z z' π π' 0 Dm) : wvG z z' s J ∈ FFl k r z z' π π' 0 Dm := by
  have h1 : 1 < r + 2 := by omega
  have inv : ∀ {a b : Mx k r}, a ∈ Sset k r z → b ∈ Sset k r z' → ∀ g : Mx k r,
      Dmin k r z z' (a * g * b) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ :=
    fun ha hb g => dInv k r z z' hz hz' _ ha _ hb g _
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hFJ⟩ := hS g₀ hg₀
    refine ⟨U, fun g => fsv s (Dmin k r z z' g ⟨1, h1⟩) • F g, hU, hgU,
      (rdb_fsv_dmin_contDiff z z' s h1).contDiffOn.smul hF, fun g hgU hgG => ?_⟩
    show fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g = _
    rw [hFJ g hgU hgG]
  · intro g hg n hn
    have e : Dmin k r z z' (n * g) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ := by
      have := inv (rdb_n_mem_Sset z hn) (rdb_one_mem_Sset z') g
      simpa using this
    show fsv s (Dmin k r z z' (n * g) ⟨1, h1⟩) • J (n * g) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)
    rw [e, hL g hg n hn, smul_comm]
  · intro g hg n hn
    have e : Dmin k r z z' (g * n) ⟨1, h1⟩ = Dmin k r z z' g ⟨1, h1⟩ := by
      have := inv (rdb_one_mem_Sset z) (rdb_n_mem_Sset z' hn) g
      simpa using this
    show fsv s (Dmin k r z z' (g * n) ⟨1, h1⟩) • J (g * n) = _ • (fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g)
    rw [e, hR g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    show fsv s (Dmin k r z z' (h * g * h') ⟨1, h1⟩) • J (h * g * h') =
      (π h).comp ((fsv s (Dmin k r z z' g ⟨1, h1⟩) • J g).comp (π' h'))
    rw [inv (rdb_h_mem_Sset z hh) (rdb_h_mem_Sset z' hh') g, hU g hg h hh h' hh',
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

end WaveFF

theorem radial_wave_function_field : RDWaveFF := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hr s hD J hJ
  have hz : inWb P.k P.r z := hD.1.2.1
  have hz' : inWb P.k P.r z' := hD.1.2.2.1
  have h1 : 1 < P.r + 2 := by omega
  refine ⟨rdb_wvG_mem_FFl hz hz' s hJ, fun x hx => ?_⟩
  simp only [resG, wvG]
  rw [Formalism.FourierDecayAlt.P.PBFV.first_minor_cell_eq_coord hz hz' hr x.1 hx.2.1 h1]
  exact smul_comm _ _ _

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDWaveRad

section

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5
open scoped ComplexConjugate

section PairSub

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem rdw_sub_fst (a b : Pr V) : (a - b).1 = a.1 - b.1 := rfl
theorem rdw_sub_snd (a b : Pr V) : (a - b).2.unop = a.2.unop - b.2.unop := rfl

end PairSub

theorem radial_wave_radial : RDWaveRad := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hr s hD Wv Wv' hW hW'
  obtain ⟨-, -, hL, hQ, -⟩ := hD
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hG, hGi, -⟩ := hL
  obtain ⟨hWave, hWc, hWci, hWp⟩ := waveSiteAll Wp Wq P z z' π π' X L hL' ⟨0, hr⟩ s Wv Wv' hW hW'
  have hW1 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv s (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW
  have hW2 : ∀ (Φ : RadSp P.k P.r z z' π π') c g, (Wv' Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
      fsv (-s) (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g := hW'
  have hop : ∀ (l : Fin P.r) i (Φ : RadSp P.k P.r z z' π π'),
      (X.op l i Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) :=
    fun l i Φ => X.op_apply l i Φ
  have hcomm : ∀ (W : Module.End ℂ (RadSp P.k P.r z z' π π')) (u : ℂ → ℂ),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        u (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ i : Fin 6, (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5) → Commute W (X.op ⟨0, hr⟩ i) := by
    intro W u hWu i hi
    show W * X.op ⟨0, hr⟩ i = X.op ⟨0, hr⟩ i * W
    apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
    simp only [Module.End.mul_apply, hWu, hop, crd]
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp only [opL, cOp, ciOp, cbOp, cbiOp] <;> exact smul_comm _ _ _
  have hoth : ∀ (t : ℂ) (W : Module.End ℂ (RadSp P.k P.r z z' π π')),
      (∀ (Φ : RadSp P.k P.r z z' π π') c g, (W Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        fsv t (c ⟨0, hr⟩) • (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g) →
      ∀ l : Fin P.r, l ≠ ⟨0, hr⟩ → ∀ i : Fin 6, Commute W (X.op l i) :=
    fun t W hWt l hl i => mulOp_comm_op X W t ⟨0, hr⟩ hWt hl i
  refine ⟨hWave, hWc, hWci, ?_, ?_, hWp, ?_, ?_, ?_, ?_⟩
  · rw [hcb]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hcomm Wv _ hW1 4 (by decide)) (hcomm Wv' _ hW2 1 (by decide))
  · rw [hcbi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hcomm Wv _ hW1 5 (by decide)) (hcomm Wv' _ hW2 2 (by decide))
  · rw [hpb, hcb]
    refine pr_ext ?_ ?_
    · change X.op ⟨0, hr⟩ 3 * Wv = Wv * X.op ⟨0, hr⟩ 3 -
        algebraMap ℂ _ (starRingEnd ℂ s) * Wv * X.op ⟨0, hr⟩ 4
      apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
      obtain ⟨hd, h0⟩ := radSp_regular Φ g c
      simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
        Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply, hop, crd, hW1, opL]
      have e := pbOp_fsv_smul (-s) ⟨0, hr⟩ _ c hd h0
      simp only [neg_neg] at e
      rw [e]
      simp only [cbOp, map_neg]
      module
    · change Wv' * (-X.op ⟨0, hr⟩ 0) = (-X.op ⟨0, hr⟩ 0) * Wv' -
        X.op ⟨0, hr⟩ 1 * Wv' * algebraMap ℂ _ (starRingEnd ℂ (starRingEnd ℂ s))
      apply LinearMap.ext; intro Φ; apply Subtype.ext; funext c g
      obtain ⟨hd, h0⟩ := radSp_regular Φ g c
      simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
        Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_smul, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, hop,
        crd, hW2, opL]
      rw [pOp_fsv_smul (-s) ⟨0, hr⟩ _ c hd h0]
      simp only [cOp, Complex.conj_conj]
      module
  · intro l hl x hx
    simp only [coordOps, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hp l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 0) (hoth (-s) Wv' hW2 l hl 3).neg_right
    · rw [hpb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 3) (hoth (-s) Wv' hW2 l hl 0).neg_right
    · rw [hc l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 1) (hoth (-s) Wv' hW2 l hl 4)
    · rw [hci l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 2) (hoth (-s) Wv' hW2 l hl 5)
    · rw [hcb l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 4) (hoth (-s) Wv' hW2 l hl 1)
    · rw [hcbi l]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hoth s Wv hW1 l hl 5) (hoth (-s) Wv' hW2 l hl 2)
  · have hf : ∀ j : Fin 6, Commute Wv (X.fn j) ∧ Commute Wv' (X.fn j) := fun j =>
      ⟨TwistedTransfer.mulOp_comm_fn X Wv _ hW j, TwistedTransfer.mulOp_comm_fn X Wv' _ hW' j⟩
    intro x hx
    simp only [Fr.zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hz]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 0).1 (hf 2).2
    · rw [hzi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 1).1 (hf 3).2
    · rw [hzb]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 2).1 (hf 0).2
    · rw [hzbi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 3).1 (hf 1).2
    · rw [hG]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 4).1 (hf 4).2
    · rw [hGi]; exact Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (hf 5).1 (hf 5).2
  · intro Y a b
    rw [hQ Y, Matrix.smul_apply, Formalism.FourierDecayAlt.P.NFx3.QQ_apply]
    exact (Formalism.FourierDecayAlt.P.NFx3.mkPair_commute (comm_xt_of_fsv_smul_endomorphism X Wv s ⟨0, hr⟩ hW1 Y a b)
      (comm_xt_of_fsv_smul_endomorphism X Wv' (-s) ⟨0, hr⟩ hW2 (star Y) b a)).smul_right _

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialOperatorLocality

section

@[expose] public section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem radial_operator_locality : RDOpLocal := by
  intro k r Wp Wq _ _ _ _ _ _ D Θ f₁ f₂ h g hg
  have hO := Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus (k := k) (r := r) D.z D.z'
  have h' : ∀ x ∈ B.GV k r, x ∈ Q.OmPlus k r D.z D.z' → f₁ x = f₂ x := fun x hx hxO => h x ⟨hx, hxO⟩
  exact ⟨Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opApply_congr_GV Θ hO h' g hg.1 hg.2,
    Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opAdj_congr_GV Θ hO h' g hg.1 hg.2⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialWaveOrbital

section

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

theorem radial_wave_orbital : RDWaveJ := by
  intro k r Wp Wq _ _ _ _ _ _ D s H _ g _
  unfold wvG
  exact PBFV.JF_mul_inv D _ (fun p hp x => by rw [BigCellZetaMinors.dmin_sgs D hp]) H g

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialIdentityOfSpectralData

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem radial_identity_of_spectral_data : RDRadIdOfSpec :=
  rDRadIdOfSpec_of_grpId_theta
    (rDGrpIdOfSpec_of_radIdAlg (rDRadIdAlg_of_collapse_gauge_rearr radial_collapse radial_gauge_identity radial_rearrangement)
      radial_start_coordinates radial_wave_radial Formalism.FourierDecayAlt.P5.waveCExists radial_residue_formula radial_wave_function_field radial_operator_function_field radial_group_residue)
    (Formalism.FourierDecayAlt.P.CutMP.JA.LT.thetaJ_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds)
    radial_orbital_niceness radial_wave_orbital radial_operator_locality

theorem radDecay_of_spec (h : RDIdentSpec) : RadDecay :=
  radDecay_of_ABQ (rDIdentABQ_of_spec h radial_identity_of_spectral_data)

end Formalism.FourierDecayAlt.P.CutSE
end
end
