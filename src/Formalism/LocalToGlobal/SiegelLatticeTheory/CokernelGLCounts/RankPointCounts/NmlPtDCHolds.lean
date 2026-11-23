module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnitaryNormalVectorCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FlagOfUpUni
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FrameZEqLinZu
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfCoefficients
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaUniqueness.Lemmas
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
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupMUIndep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.EqZeroOfMulVec
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Tactic.TypeStar
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ToPtsInj
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemXflagMapLF

section

@[expose] public section

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp



namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_Xa_mapFlag {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (j : ℕ) (x : S.V) :
    x ∈ (mapFlag γ hγ F).Xa j ↔ γ.symm x ∈ F.Xa j := by
  have h1 : (mapFlag γ hγ F).Xa j = (F.Xa j).map (γ : S.V →ₗ[E] S.V) := by
    unfold FlagG.Xa
    rw [Submodule.map_span, ← Set.image_comp]
    rfl
  rw [h1]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨γ.symm x, h, by simp⟩

theorem mem_Xflag_mapLF {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}
    (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) (x : S.V) :
    x ∈ Xflag (mapLF γ F) j ↔ γ.symm x ∈ Xflag F j := by
  unfold Xflag mapLF
  rw [dite_eq_left hγ]
  exact mem_Xa_mapFlag γ hγ F.fl j x

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem NLam_SRat {T : D.host.E} {Λ : Submodule (𝓞 D.host.E) (VS D).V} {F : LFlag (D.sp.Y 0) D.R.rS T}
    {n : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hn : n ∈ NLam Λ F) : n ∈ SRat F := by
  obtain ⟨hA, hf, hp⟩ := hn
  refine ⟨hA.1, hf, hp _ ?_⟩
  refine (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth _).2 fun x hx => ?_
  rw [hT_swap F.fl.z x, hT_z_X F.fl hx, star_zero]

theorem NLam_transport (t : TauC Y u u') {Λ : Submodule (𝓞 D.host.E) (VS D).V} {m : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hm : m ∈ NLam Λ t.frame) : t.lin⁻¹ * m * t.lin ∈ SRat (lf D (X.Fu u')) := by
  have hγ : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hS := NLam_SRat hm
  obtain ⟨hmi, hmf, hmz⟩ := hS
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem hγ) hmi) hγ,
    fun j x hx => ?_, ?_⟩
  · have hx' : t.lin x ∈ Xflag t.frame (j + 1) :=
      (mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) (j + 1) _).2 (by rw [LinearEquiv.symm_apply_apply]; exact hx)
    have h := hmf j _ hx'
    have h' := (mem_Xflag_mapLF t.lin hγ (lf D (X.Fu u')) j _).1 h
    rw [map_sub, LinearEquiv.symm_apply_apply] at h'
    exact h'
  · have h2 : m t.frame.fl.z - t.frame.fl.z ∈ t.frame.fl.X := hmz
    have h3 := (mem_frameX Y t _).1 h2
    rw [map_sub, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply] at h3
    show t.lin.symm (m (t.lin (X.Fu u').z)) - (X.Fu u').z ∈ _
    exact h3

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SameCell

section

@[expose] public section

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

section Sg

variable {K : Type*} [Field K] {r : ℕ}

def Sg (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K := Matrix.diagonal fun b => (-1) ^ (r - b.val)

theorem Sg_mul_Sg : (Sg r : Matrix (Fin (r + 1)) (Fin (r + 1)) K) * Sg r = 1 := by
  rw [Sg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem zhatOM_eq (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ZhatOM Z = Z * Sg r := by
  ext a b
  rw [Sg, Matrix.mul_diagonal]
  show (-1) ^ (r - b.val) * Z a b = _
  ring

theorem upUni_Sg {U : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni U) : IsUpUni (Sg r * U * Sg r) := by
  intro i j
  simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hji => by rw [(h i j).1 hji]; ring, fun hij => ?_⟩
  subst hij
  rw [(h i i).2 rfl, mul_one, ← pow_add, ← two_mul, pow_mul]
  simp

end Sg

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem same_cell (F : FlagG S r T) (F1 F2 : FlagG S r T') (hG1 : Gflag F F1 ≠ 0) (hG2 : Gflag F F2 ≠ 0)
    (w : Point E (r + 1)) (h1 : IsInCell (ZhatOM (Zhat F F1)) w) (h2 : IsInCell (ZhatOM (Zhat F F2)) w) :
    ∃ g : S.V ≃ₗ[E] S.V, g ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧
      (∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni M ∧ ∀ b, g.symm (F.fvec b) = ∑ c, M c b • F.fvec c) ∧
      ∃ U : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUpUni U ∧ ∀ b, g (∑ c, U c b • F1.fvec c) = F2.fvec b := by
  obtain ⟨L1, U1, hL1, hU1, e1⟩ := h1
  obtain ⟨L2, U2, hL2, hU2, e2⟩ := h2
  rw [zhatOM_eq] at e1 e2
  have hL1d : IsUnit L1.det := by rw [loUni_det hL1]; exact isUnit_one
  have hU1d : IsUnit U1.det := by rw [upUni_det hU1]; exact isUnit_one
  set L := L2 * L1⁻¹ with hL
  set U := Sg r * (U1⁻¹ * U2) * Sg r with hU
  have hLl : IsLoUni L := loUni_mul hL2 (loUni_inv hL1)
  have hUu : IsUpUni U := upUni_Sg (upUni_mul (upUni_inv hU1) hU2)
  have hZ : Zhat F F2 = L * Zhat F F1 * U := by
    have z1 : Zhat F F1 = L1 * ptMat w * U1 * Sg r := by
      rw [← e1, Matrix.mul_assoc, Sg_mul_Sg, Matrix.mul_one]
    have z2 : Zhat F F2 = L2 * ptMat w * U2 * Sg r := by
      rw [← e2, Matrix.mul_assoc, Sg_mul_Sg, Matrix.mul_one]
    rw [z2, z1, hL, hU]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Sg r) (Sg r), Sg_mul_Sg, Matrix.one_mul, ← Matrix.mul_assoc U1 U1⁻¹,
      Matrix.mul_nonsing_inv _ hU1d, Matrix.one_mul, ← Matrix.mul_assoc L1⁻¹ L1,
      Matrix.nonsing_inv_mul _ hL1d, Matrix.one_mul]
  set M := Lᴴ with hM
  have hMu : IsUpUni M := loUni_iff_ct.1 hLl
  have hZ' : Zhat F F2 = Mᴴ * Zhat F F1 * U := by rw [hM, conjTranspose_conjTranspose]; exact hZ
  obtain ⟨g, hg, hgx⟩ := witt_tuple (tupMU F F1 M U) (Sum.elim F.fvec F2.fvec) (tupMU_indep F F1 M U hMu hUu hG1)
    (PI.PairCorankPos.W.linIndep F F2 hG2) (gram_moved F F1 F2 M U hMu hUu hZ')
  refine ⟨g, hg, ⟨M, hMu, fun b => ?_⟩, U, hUu, fun b => hgx (Sum.inr b)⟩
  have := hgx (Sum.inl b)
  simp only [tupMU, Sum.elim_inl] at this
  rw [← this, LinearEquiv.symm_apply_apply]

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlPtDCHolds

section

@[expose] public section

noncomputable section

open scoped Classical
open Module Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.TermOp



namespace Formalism.L2.SG.NGCut.NormalVectorPairings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (Y : Full X) {u u' : D.what₂.Word}

theorem rep_at_pt (t : TauC Y u u') (hG : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t)) :
    ∃ F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E), Gval (lf D (X.Fu u)) F' ≠ 0 ∧
      IsInCell (ZhatOM (Zhat (X.Fu u) F'.fl)) (Formalism.L2.SG.PairVal.ptOf t.toTerm) ∧
      ∃ n ∈ SRat (lf D (X.Fu u)), ∃ m ∈ SRat (lf D (X.Fu u')),
        ∀ a, F'.fl.fvec a = (n * t.lin * m) ((X.Fu u').fvec a) := by
  obtain ⟨F', ⟨hP, hmk⟩, hGv, hcell⟩ := at_ptOf Y t hG
  refine ⟨F', hGv, hcell, ?_⟩
  have hrow := (Y.rowsOK u).1 t.lam t.mem
  have hmk' : Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩ = Formalism.L2.SG.TermDef.mk _ _ _ ⟨F', hP⟩ := hmk.symm
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t.lam hrow _ _).1 hmk'
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hrel
  refine ⟨n, NLam_SRat hn, t.lin⁻¹ * m * t.lin, NLam_transport Y t hm, fun a => ?_⟩
  have := hfr a
  show F'.fl.fvec a = n (t.lin (t.lin.symm (m (t.lin ((X.Fu u').fvec a)))))
  rw [LinearEquiv.apply_symm_apply]
  rw [← frame_fvec Y t a]
  exact this

theorem ptdc_core (t1 t2 : TauC Y u u') (hN1 : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t1))
    (hp : ptPN t1 = ptPN t2) :
    ∃ σ ∈ SRat (lf D (X.Fu u)), ∃ s' ∈ SRat (lf D (X.Fu u')), t2.lin = σ * t1.lin * s' := by
  have hN2 : 1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) (ptPN t2) := by rw [← hp]; exact hN1
  obtain ⟨F1, hG1, hc1, n1, hn1, m1, hm1, hF1⟩ := rep_at_pt Y t1 hN1
  obtain ⟨F2, hG2, hc2, n2, hn2, m2, hm2, hF2⟩ := rep_at_pt Y t2 hN2
  have hw : Formalism.L2.SG.PairVal.ptOf t1.toTerm = Formalism.L2.SG.PairVal.ptOf t2.toTerm := toPts_inj _ _ hp
  rw [hw] at hc1
  obtain ⟨g, hg, ⟨M, hM, hgM⟩, U, hU, hgU⟩ := same_cell (X.Fu u) F1.fl F2.fl hG1 hG2 _ hc1 hc2

  have hgs : g.symm ∈ SRat (lf D (X.Fu u)) := by
    obtain ⟨hf, hz⟩ := flag_of_upUni (X.Fu u) (g.symm : (VS D).V →ₗ[D.host.E] (VS D).V) M hM hgM
    exact ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hg, hf, hz⟩
  have hgS : g ∈ SRat (lf D (X.Fu u)) := by simpa using SRat_inv (lf D (X.Fu u)) hgs
  set ρ1 := n1 * t1.lin * m1 with hρ1
  set ρ2 := n2 * t2.lin * m2 with hρ2
  set s'' := ρ2⁻¹ * g * ρ1 with hs''
  have hs''v : ∀ b, s''.symm ((X.Fu u').fvec b) = ∑ c, U c b • (X.Fu u').fvec c := by
    intro b
    apply s''.injective
    rw [LinearEquiv.apply_symm_apply, hs'']
    show (X.Fu u').fvec b = ρ2.symm (g (ρ1 (∑ c, U c b • (X.Fu u').fvec c)))

    rw [map_sum]
    simp only [map_smul]
    have e1 : ∀ c, ρ1 ((X.Fu u').fvec c) = F1.fl.fvec c := fun c => (hF1 c).symm
    simp only [e1]
    rw [hgU b, hF2 b]
    simp
  have hs''S : s'' ∈ SRat (lf D (X.Fu u')) := by
    have hs''i : s'' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
      refine (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).inv_mem ?_) hg) ?_
      · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hn2.1 t2.rep.2.2.1) hm2.1
      · exact (Formalism.HermitianLatticesTheory.isom _).mul_mem ((Formalism.HermitianLatticesTheory.isom _).mul_mem hn1.1 t1.rep.2.2.1) hm1.1
    obtain ⟨hf, hz⟩ := flag_of_upUni (X.Fu u') (s''.symm : (VS D).V →ₗ[D.host.E] (VS D).V) U hU hs''v
    have : s''.symm ∈ SRat (lf D (X.Fu u')) := ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem hs''i, hf, hz⟩
    simpa using SRat_inv (lf D (X.Fu u')) this
  refine ⟨n2⁻¹ * g * n1, SRat_mul _ (SRat_mul _ (SRat_inv _ hn2) hgS) hn1,
    m1 * s''⁻¹ * m2⁻¹, SRat_mul _ (SRat_mul _ hm1 (SRat_inv _ hs''S)) (SRat_inv _ hm2), ?_⟩
  have e : ρ2 = g * ρ1 * s''⁻¹ := by rw [hs'']; group
  rw [hρ2, hρ1] at e
  calc t2.lin = n2⁻¹ * (n2 * t2.lin * m2) * m2⁻¹ := by group
    _ = n2⁻¹ * (g * (n1 * t1.lin * m1) * s''⁻¹) * m2⁻¹ := by rw [e]
    _ = n2⁻¹ * g * n1 * t1.lin * (m1 * s''⁻¹ * m2⁻¹) := by group

theorem NmlPtDC_holds : NmlPtDC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' _ γ hγ t1 t2 _ _ h1 h2 _ => ?_⟩
  subst h1
  exact ptdc_core Y t1 t2 hγ h2.symm

theorem NmlSep_holds : NmlSep := nmlSep_of NmlPtDC_holds normalsLemmaG3_holds

end Formalism.L2.SG.NGCut.NormalVectorPairings
end
end
end
