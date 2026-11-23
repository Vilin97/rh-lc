module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieTwRecOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FinXRowOfGap
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteTOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GapClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AdmissibleOfTransported

section

@[expose] public section

open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.KerJoinS Formalism.L2.SG.KerSideCut Formalism.IndefR.Cx Formalism.L2.Indef

namespace Formalism.L2.SG.JoinSI
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Twist

variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (s : Bool) (σ : K →+* ℂ)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj s] P.EE)

theorem kernelJoin_of_multiplicity (hs : ∀ a, Bs.v0.embedding a = Formalism.IndefR.Links.cj s (σ a)) (hM : P.MIstar2 eV sEE)
    (hC : ChainTieT (P := P) (σ := σ) (m := m) (cφ := cφ) (cF := cF))
    (hV : GoodPartHasComplexCoordinates (P := P) (fc := fc) (cF := cF))
    (hR : RowTieT (P := P) (fc := fc) (eV := eV) (s := s) (σ := σ) (cF := cF) (eR := eR))
    (hN : ColNormT (P := P) (s := s) (m := m) (cφ := cφ))
    (hP : PairTieT (X := X) (G := G) (j := j) (Tr := Tr) (hK := hK) (Dt := Dt) (P := P) (fc := fc) (sEE := sEE) (s := s) (m := m)
      (cφ := cφ) (eR := eR)) :
    KerJoinS X G j Tr hK Dt := by
  classical
  obtain ⟨d, hUn, hI, hA⟩ := hM
  obtain ⟨V1, hV1⟩ := exists_conj_op (P := P) (fc := fc) (eV := eV) (s := s) (σ := σ) (cF := cF) (eR := eR) hR d.V (fun e he => (hUn.1 e he).1)
  obtain ⟨hRin, -, ⟨c, hc, hcn⟩, lam, hlam, hRΘ⟩ := hR
  have hV1n : ∀ F, ‖V1 F‖ = ‖F‖ := by
    intro F
    have h1 : c * ‖V1 F‖ = c * ‖F‖ := by
      rw [← hcn, ← hcn, hV1]
      exact (hUn.1 _ (hRin F)).2
    exact mul_left_cancel₀ hc.ne' h1
  let V1i : D.what₂.EE →ₗᵢ[ℂ] D.what₂.EE := { toLinearMap := V1, norm_map' := hV1n }
  refine ⟨V1i.toLinearIsometryEquiv rfl, fun u => ?_⟩
  obtain ⟨κ, hκ, hPu⟩ := hP u
  obtain ⟨cu, hcu, hcun⟩ := hN u
  let Mu := d.U (m u)
  let U1 : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u :=
    { toFun := fun φ => (cφ u).symm (cjv s (Mu.mulVec (cjv s (cφ u φ))))
      map_add' := fun φ ψ => by
        simp only [map_add (f := _), cjv_add, Matrix.mulVec_add]
      map_smul' := fun r φ => by
        simp only [map_smul, cjv_smul, Matrix.mulVec_smul, Formalism.IndefR.Links.cj_cj, RingHom.id_apply] }
  have hU1 : ∀ φ, cjv s (cφ u (U1 φ)) = Mu.mulVec (cjv s (cφ u φ)) := by
    intro φ
    show cjv s (cφ u ((cφ u).symm _)) = _
    rw [LinearEquiv.apply_symm_apply, cjv_cjv]
  have hU1n : ∀ φ, ‖U1 φ‖ = ‖φ‖ := by
    intro φ
    have h1 : cu * ‖U1 φ‖ = cu * ‖φ‖ := by
      rw [← hcun, ← hcun, hU1]
      exact hUn.2.1 (m u) (cjv s (cφ u φ))
    exact mul_left_cancel₀ hcu.ne' h1
  let U1i : D.what₂.Mu u →ₗᵢ[ℂ] D.what₂.Mu u := { toLinearMap := U1, norm_map' := hU1n }
  have hcjne : Formalism.IndefR.Links.cj s (d.a (m u) * lam) ≠ 0 := (map_ne_zero _).2 (mul_ne_zero (hA (m u)) hlam)
  refine ⟨Formalism.IndefR.Links.cj s (d.a (m u) * lam) * κ, mul_ne_zero hcjne hκ, U1i.toLinearIsometryEquiv rfl,
    fun φ F hF T hT => ?_⟩
  let S : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) → (fc P.zs).Sp.HH :=
    fun y => sEE (d.V (eR (D.what₂.iota D.what₂.mu0 (cF y))))
  let Q : (Fin ((fc P.zs).Dc.a (m u)) → ℂ) → (fc P.zs).Sp.HH := fun x => (fc P.zs).Sp.Pu (m u) (Mu.mulVec (cjv s x))
  let B2 : (Fin ((fc P.zs).Dc.a (m u)) → ℂ) →ₗ[ℂ] (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun x y => Formalism.IndefR.Links.cj s (d.a (m u) * lam * ⟪S y, Q x⟫_ℂ))
      (fun x x' y => by
        simp only [Q, cjv_add, Matrix.mulVec_add, map_add (f := _), inner_add_right, mul_add])
      (fun r x y => by
        simp only [Q, cjv_smul, Matrix.mulVec_smul, map_smul, inner_smul_right, smul_eq_mul, map_mul,
          Formalism.IndefR.Links.cj_cj]
        ring)
      (fun x y y' => by
        simp only [S, map_add (f := _), inner_add_left, mul_add])
      (fun r x y => by
        simp only [S, map_smul, LinearMap.map_smulₛₗ, inner_smul_left, smul_eq_mul, map_mul,
          Formalism.IndefR.Links.cj_cj, starRingEnd_self_apply]
        ring)
  let B1 : (Fin ((fc P.zs).Dc.a (m u)) → ℂ) →ₗ[ℂ] (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] ℂ :=
    (perColL D u).compl₁₂ (cφ u).symm.toLinearMap cF
  have hbas : ∀ (i : Fin ((fc P.zs).Dc.a (m u))) (k : Fin ((fc P.zs).Df1.nV Bs.μ0)),
      B1 (Pi.single i 1) (Pi.single k 1) = B2 (Pi.single i 1) (Pi.single k 1) := by
    intro i k
    have hx := Formalism.IndefR.Cx.cpt_single σ i
    have hy := Formalism.IndefR.Cx.cpt_single σ k
    have hx0 := Formalism.IndefR.Cx.cpt_single Bs.v0.embedding i
    show perColL D u ((cφ u).symm (Pi.single i 1)) (cF (Pi.single k 1)) =
      Formalism.IndefR.Links.cj s (d.a (m u) * lam * ⟪sEE (d.V (eR (D.what₂.iota D.what₂.mu0 (cF (Pi.single k 1))))),
        (fc P.zs).Sp.Pu (m u) (Mu.mulVec (cjv s (Pi.single i 1)))⟫_ℂ)
    have L : perColL D u ((cφ u).symm (Pi.single i 1)) (cF (Pi.single k 1)) =
        σ ((fc P.zs).Dc.Pt (m u) Bs.μ0 (Pi.single i 1) (Pi.single k 1)) := by
      rw [perColL_apply]
      have h0 := hC u (Pi.single i 1) (Pi.single k 1)
      rwa [hx, hy] at h0
    have Rr : eR (D.what₂.iota D.what₂.mu0 (cF (Pi.single k 1))) =
        lam⁻¹ • P.Θ Bs.μ0 (P.jR Bs.μ0 (eV Bs.μ0 (Pi.single k 1))) := by
      have h0 := hRΘ (Pi.single k 1)
      rw [hy] at h0
      rw [h0, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    have hin : ∀ (z : P.EE) (w : (fc P.zs).Sp.HH), ⟪sEE (d.V (lam⁻¹ • z)), w⟫_ℂ = lam⁻¹ * ⟪sEE (d.V z), w⟫_ℂ := by
      intro z w
      rw [map_smul, LinearMap.map_smulₛₗ, inner_smul_left, starRingEnd_self_apply]
    rw [L, Rr, hin, mul_assoc (d.a (m u)), mul_inv_cancel_left₀ hlam, cjv_single, ← hx0]
    have h := hI (m u) Bs.μ0 (Pi.single i 1) (Pi.single k 1)
    rw [hUn.2.2.2 (m u), one_mul] at h
    rw [← h, hs, Formalism.IndefR.Links.cj_cj]
  have hall : ∀ x y, B1 x y = B2 x y := by
    intro x y
    rw [Formalism.IndefR.Cx.bil_expand B1, Formalism.IndefR.Cx.bil_expand B2]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hbas i k]
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 (hV hF)
  have hT' := hPu (V1 (D.what₂.iota D.what₂.mu0 (cF y))) (U1 φ) T hT
  have e1 : D.what₂.perCol u D.what₂.mu0 φ (cF y) = B2 (cφ u φ) y := by
    rw [← hall]
    show _ = perColL D u ((cφ u).symm (cφ u φ)) (cF y)
    rw [LinearEquiv.symm_apply_apply, perColL_apply]
  rw [e1]
  show Formalism.IndefR.Links.cj s (d.a (m u) * lam * ⟪sEE (d.V (eR (D.what₂.iota D.what₂.mu0 (cF y)))),
      (fc P.zs).Sp.Pu (m u) (Mu.mulVec (cjv s (cφ u φ)))⟫_ℂ) = _
  rw [← hV1, ← hU1, hT', map_mul (Formalism.IndefR.Links.cj s) (d.a (m u) * lam), Formalism.IndefR.Links.cj_cj, mul_assoc]
  rfl

end Twist

section At

variable {D : D7}

variable {X : HidaSetting D} {G : GoodOp X} {Y : Formalism.L2.SG.Full.Full X} {j : FinX Y → (D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)}
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} {Tr : ∀ u, Transport X u (Fm u)}
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {P : CxData A} {fc : DefSub A → DefFace Bs}
  {eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH}
  {s : Bool} {σ : K →+* ℂ}

theorem kerJoinS_of_joinAt2 (hM : P.MIstar2 eV sEE) (J : JoinAt X G Y j Tr P fc eV sEE s σ) (hF : FinX Y) :
    KerJoinS X G (j hF) Tr Y.hK Y.Dt :=
  kernelJoin_of_multiplicity X G (j hF) Tr Y.hK Y.Dt P eV sEE s σ J.m J.cφ J.cF J.eR J.twist hM
    J.chainTie J.v0Surjective J.rowTie J.colNorm (J.pairTie hF)

theorem adm13_of_colJoin (hM : P.MIstar2 eV sEE) (J : JoinAt X G Y j Tr P fc eV sEE s σ) (hF : FinX Y)
    (I : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF))
    (hRow : ∀ F, I.eHH (D.sEE F) = conjHH X G (j hF F)) (hCol : ColJoinS hF I Tr) (hB : Formalism.BasicNotions.Rows.BuDefQ D.what₂)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  besselId_of_joins hF I Tr G (j hF) hRow hCol (kerJoinS_of_joinAt2 hM J hF) hB hon

end At

section Ties

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : Formalism.L2.RecT ex}

end Ties

section Real

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

variable {R : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : Formalism.IndefR.RealT R P Dcf Spf Zscf S Ks}

end Real

end Formalism.L2.SG.JoinSI
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleOfTransported

section

@[expose] public section



section
open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.KerJoinS Formalism.L2.SG.KerSideCut Formalism.IndefR.Cx Formalism.L2.Indef
namespace Formalism.L2.SG.JoinSI
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Twist
variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (s : Bool) (σ : K →+* ℂ)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj s] P.EE)
end Twist
section At
variable {D : D7}
variable {X : HidaSetting D} {G : GoodOp X} {Y : Formalism.L2.SG.Full.Full X} {j : FinX Y → (D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)}
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} {Tr : ∀ u, Transport X u (Fm u)}
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {P : CxData A} {fc : DefSub A → DefFace Bs}
  {eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH}
  {s : Bool} {σ : K →+* ℂ}
end At
section Ties
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}
theorem adm13_of_transported_join (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R)
    {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    {P' : CxData A} {fc : DefSub A → DefFace Bs}
    {eV : ∀ t, (Fin ((fc P'.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P'.EE →ₗ⋆[ℂ] (fc P'.zs).Sp.HH} {s : Bool} {σ : K →+* ℂ}
    (hM : P'.MIstar2 eV sEE) (J : JoinAt S.X S.G S.Y (_root_.Formalism.L2.SG.JoinSI.spectralRowIsometry S) S.tr P' fc eV sEE s σ) (hF : FinX S.Y)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  adm13_of_colJoin hM J hF (S.hI hF) (_root_.Formalism.L2.SG.JoinSI.eHH_sEE_eq_conjHH_isometryOfJoin S hF) (_root_.Formalism.L2.SG.JoinSI.colJoinS_of_spectral_ties_real S hF) R.pin.buDef hon
end Ties
section Real
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
variable {R : _root_.Formalism.L2.RecTAlt ex} {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks}
theorem adm13_of_kernel_join (hM : (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).MIstar2 (Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) Q.sEE) (J : _root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin R S Q) (hF : FinX S.Y)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  _root_.Formalism.L2.SG.JoinSI.adm13_of_transported_join S hM J.toJoinAt hF hon
end Real
end Formalism.L2.SG.JoinSI
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibilityClosed

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Top4 Formalism.L2.SG.JoinSI Formalism.L2.SG.PackageTie2
namespace Formalism.L2.SG.JoinSISel
section At
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
def IndefiniteRealisationMultiplicityCondition {R : _root_.Formalism.L2.RecTAlt ex} {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation R P Dcf Spf Zscf S Ks) : Prop :=
  (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).MIstar2 (Q.F.eV (_root_.Formalism.L2.SG.JoinSI.complexRealisationJoinData Q).zs) Q.sEE
end At
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel} {selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK}
theorem complementFive_closed_of_image_v0 (selJ : _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationSelection 𝒜 sel selS selP selDH selC selK selI)
    (hM : Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc fun x hx h i => _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationMultiplicityCondition (selI Fm hc x hx h i))
    (hFX : Closed 𝒜 fun Fm _ => ∀ hc : 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc fun x hx h i => FinX (selS Fm hc x hx h i).Y)
    (hon : Closed 𝒜 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, BaseVectorImageFull (Fm.D x i)) :
    Closed 𝒜 fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm := by
  obtain ⟨ε1, hε1, H⟩ := (hM.and hFX).and hon
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK⟩ := H eps he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨hM', hF'⟩, ⟨y0, hY⟩⟩ := hK Fm CH hc hL
  obtain ⟨a0, hA⟩ := hM' hc
  obtain ⟨b0, hB⟩ := hF' hc
  refine ⟨max (max a0 b0) (max y0 (max (sel Fm hc).1 (Fm.x1 + 1))), fun x hxge i => ?_⟩
  have h1 : max a0 b0 ≤ x := le_trans (le_max_left _ _) hxge
  have h2 : max y0 (max (sel Fm hc).1 (Fm.x1 + 1)) ≤ x := le_trans (le_max_right _ _) hxge
  have hx : Fm.x1 < x := by
    have := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) h2)
    linarith
  have h : (sel Fm hc).1 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) h2)
  exact _root_.Formalism.L2.SG.JoinSI.adm13_of_kernel_join (hA x hx h (le_trans (le_max_left _ _) h1) i) (selJ Fm hc x hx h i)
    (hB x hx h (le_trans (le_max_right _ _) h1) i) (hY x (le_trans (le_max_left _ _) h2) i)
end Formalism.L2.SG.JoinSISel
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelectionClosedOfWuDecay

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT Formalism.L2.Top3 Formalism.L2.Top4

theorem GlobalTheory.Top.selection_closed_of_wu_decay_alt : ∀ (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hWu : Formalism.L2.SG.Pf.WuDecayOfGap)
    (hRF : Formalism.L2.SG.RowsDef.RowsFinDim)
    (selJ : _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationSelection 𝒜 sel selS selP selDH selC (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (jOn : Closed (D3 3 𝒜) fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.L2.SG.JoinSISel.BaseVectorImageFull (Fm.D x i))
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH), Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm := by
  intro 𝒜 sel selS selP selDH selC selB hWu hRF selJ jOn rRows
  have jGap : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm,
      _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm (d3_a hc) fun x _ _ i => Formalism.L2.SG.ConcreteSettingExists.GapHyp (Fm.D x i) :=
    (Formalism.L2.SG.GapClosed.gapEv_closed_of (D3 3 𝒜) fun _ hc => hc.2.2.1).imp fun Fm _ _ h hc => by
      obtain ⟨y, hy⟩ := h hc
      exact ⟨y, fun x _ _ hxy i => hy x hxy i⟩
  have hM : Closed (D3 3 𝒜) fun Fm _ => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.EventuallyAlongSelection (fun Fm hc => sel Fm (d3_a hc)) Fm hc fun x hx h i =>
      _root_.Formalism.L2.SG.JoinSISel.IndefiniteRealisationMultiplicityCondition ((_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc) x hx h i) :=
    rRows.imp fun Fm CH _ h hc => by
      obtain ⟨C, _, x0, H⟩ := h hc
      exact ⟨x0, fun x hx hs hx0 i => (H x hx hs hx0 i).1.miStar⟩
  have hFX := _root_.Formalism.L2.SG.JoinSISel.closed_finX_of_gapHyp (𝒜 := D3 3 𝒜) (sel := fun Fm hc => sel Fm (d3_a hc))
    (selS := fun Fm hc => selS Fm (d3_a hc)) (Formalism.L2.SG.Pf.finXC_of hWu hRF)
    jGap
  have hC5 : Closed (D3 3 𝒜) fun Fm _ => Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm :=
    _root_.Formalism.L2.SG.JoinSISel.complementFive_closed_of_image_v0 (𝒜 := D3 3 𝒜) (sel := fun Fm hc => sel Fm (d3_a hc))
      (selS := fun Fm hc => selS Fm (d3_a hc)) (selP := fun Fm hc => selP Fm (d3_a hc)) (selDH := fun Fm hc => selDH Fm (d3_a hc))
      (selC := fun Fm hc => selC Fm (d3_a hc)) (selK := fun Fm hc => (_root_.Formalism.L2.Top4.kernelChoiceOfSelection selB) Fm (d3_a hc)) (selI := fun Fm hc => (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm (d3_a hc))
      (fun Fm hc => selJ Fm (d3_a hc)) hM hFX jOn
  exact hC5
end
end
end
