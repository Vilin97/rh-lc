module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DIVColPins
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeOfEqSpanFracSmul
public import Formalism.LocalToGlobal.Divisibility.NumbersLink
public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnsMemberRowsOfLogLevelLeStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvIpAtLeNormAtSqStatement
import Formalism.LocalToGlobal.Divisibility.RowLatLemmas

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfNumReads

section

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.NumReads

open Formalism.LatticeIndexTer (ph)

theorem ph_zero : ph 0 = 0 := by simp [ph]

theorem N_pred_le (N : NumDatum) (j : ℕ) (hj : j < N.R.m) : N.R.N ((j + 1) - 1) ≤ N.Nm := by
  unfold NumDatum.Nm Ranks.N
  rw [Nat.add_sub_cancel]
  have := Nat.mul_le_mul_right (N.R.t + 1) hj.le
  omega

theorem ofNum_reads : ∀ (N : NumDatum) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (δ : Code N) (T : ℕ)
    (Nc lam0 C0 ce Ch Sw C1 : ℝ) (H : N.NumFacts δ Nc lam0 C0 ce Ch Sw C1),
    Reads N eJ δ T (RecNums.ofNum N eJ δ T Nc lam0 C0 ce Ch Sw C1 H) := by
  intro N J _ eJ δ T Nc lam0 C0 ce Ch Sw C1 H
  refine ⟨?_, ?_, rfl, ?_, ?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  · intro z
    exact N.mem_topsPl z
  · intro t _
    rfl
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, ph (N.nuPad δ ((eJ j).1 + 1) z i) = _
    unfold NumDatum.nuPad
    have e : ∀ i : Fin N.Nm, ph (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) =
        (if i.1 < N.R.N ((eJ j).1 + 1 - 1) then ph ((N.nu δ ((eJ j).1 + 1) z i.1 : ℚ) : ℝ) else 0) := by
      intro i
      split_ifs
      · rfl
      · exact ph_zero
    rw [Finset.sum_congr rfl (fun i _ => e i),
      NumDatum.sum_pad (fun i => ph ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle, Nat.add_sub_cancel]
  · intro j z
    have hle := N_pred_le N (eJ j).1 (eJ j).2
    show ∑ i : Fin N.Nm, N.nuPad δ ((eJ j).1 + 1) z i = _
    unfold NumDatum.nuPad NumDatum.nuAbs
    rw [NumDatum.sum_pad (fun i => ((N.nu δ ((eJ j).1 + 1) z i : ℚ) : ℝ)) hle]
    push_cast
    rfl

end GlobalTheory.ColRows.NumReads
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberRowsOfKernelDatumSizes

section

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem rowsBody_of_kerTies : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) [_root_.NumberField.IsTotallyComplex t.X.K] (W : Formalism.L2.Col.Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (hX : t.X.Ok) (Bs : DefBase t.X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 t.X.E t.Pr.vGs D.R.r → t.X.K)) (tup : Bs.Tup → D.what₂.Tup) (hP : ∀ τ, (mtildeGSD W t.Ch t.sel (t.tup (tup τ)) (rPsymF (R := D.R) t.Ch)).Ok) (b : ∀ τ, D.what₂.Word → (t.idx (tup τ)).β (t.m2 + 1)) (hY : ∀ τ x, YbHyp (R := D.R) t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) (t.word x) t.m2 (b τ x)) (hK : ∀ τ x, KerEquivC W t.Ch t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) t.amb (t.word x) t.m2 (b τ x) (hY τ x) (rPsymF (R := D.R) t.Ch)) (hF : ∀ τ x j, (chF W t.sel (t.tup (tup τ)) (t.idx (tup τ)) (t.word x) j).Ok) (hE : ∀ x, (evGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch) (t.word x)).Ok) (ev : ∀ τ, (Fin (Df.nV τ) → t.X.K) →ₗ[t.X.K] V0X W t.Ch t.sel (t.tup (tup τ)) Xg (rPsymF (R := D.R) t.Ch)) (u : D.what₂.Word) (eJ : Bs.J ≃ Fin D.R.m) (Nc lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) Nc lam0 c0 ce Ch Sw C1), tup Bs.μ0 = D.what₂.mu0 → KerTies t W Del h0 → KerSizes t W Del h0 CY CT → C0 ≤ Ch → (∀ v : InfinitePlace t.X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun t.X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) (fun τ => t.idx_ok (tup τ)) hP D.what₂.Word t.word b hY (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK) hF ev) u (memQ (A := (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK)) (hF := hF) hE (x := u)) (colsIn W t.Ch hX t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.idx (tup Bs.μ0)) (t.idx_ok (tup Bs.μ0)) (t.word u)) (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) ∧ ∀ v, IsUnit ((MramH W t.Ch hX (t.word u)).X v).det := by
  intro CY CT hCT
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.columnsMemberRows_of_logLevel_le CY CT hCT
  refine ⟨C0, fun D L hT Gi Gl K Y cX ex t _ W Del h0 hX Bs Df Xg tup hP b hY hK hF hE ev u eJ Nc lam0 c0 ce Ch Sw C1 H hmu hTi hS hC hPD hFr => ?_⟩
  obtain ⟨pl, hpl⟩ := hTi.wts
  have hmu0 : t.tup (tup Bs.μ0) = 1 := hmu ▸ hTi.mu0
  have hsh : (t.cst (tup Bs.μ0)).sharp = true := by rw [hmu]; exact hTi.sharp
  have hfld : FieldOfDefinition W t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.word u) t.amb := by
    rw [hmu]; exact hTi.fld u
  have hlog : Real.log (t.Pr.T (t.word u) : ℝ) ≤ CT * D.R.m * L.sc.L := by rw [t.T_rec u]; exact hS.logT u
  have hRd : Reads (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (t.Pr.T (t.word u))
      (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) := by
    rw [t.T_rec u]; exact NumReads.ofNum_reads _ _ eJ _ _ Nc lam0 c0 ce Ch Sw C1 H
  have hm2 := hTi.m2
  have hcc := t.cc_rec
  have hsz := hS.sizes
  have hrw := hS.what₂ u
  have hho := hTi.host
  have hch := hTi.chr
  have han := hTi.an
  have hwt := hpl u
  clear hTi hS hpl
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, X, seam, seam_ok, Pr, pr_ok, g_rec, ChT, sel, S, word, T_rec, tupT, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  dsimp only at *
  subst hm2
  subst hcc
  exact hC0 D (ofRecord D L Del h0) X seam Pr W ChT glob sel S hX Bs Df Xg (fun τ => tupT (tup τ)) (fun τ => cst (tup τ))
    (fun τ => idx (tup τ)) (fun τ => idx_ok (tup τ)) hP D.what₂.Word word b hY δ B χ cD hK hF hE ev pl u (letterOf D L Del h0 u) eJ _
    hho hwt hch han hmu0 hsh hfld hsz hrw hlog hRd hC hPD hFr

end GlobalTheory.ColRows
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberRowsOfKernelDatumSizesStatement

section

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.memberRows_of_kernelDatum_sizes : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) [_root_.NumberField.IsTotallyComplex t.X.K] (W : Formalism.L2.Col.Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (hX : t.X.Ok) (Bs : DefBase t.X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 t.X.E t.Pr.vGs D.R.r → t.X.K)) (tup : Bs.Tup → D.what₂.Tup) (hP : ∀ τ, (mtildeGSD W t.Ch t.sel (t.tup (tup τ)) (rPsymF (R := D.R) t.Ch)).Ok) (b : ∀ τ, D.what₂.Word → (t.idx (tup τ)).β (t.m2 + 1)) (hY : ∀ τ x, YbHyp (R := D.R) t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) (t.word x) t.m2 (b τ x)) (hK : ∀ τ x, KerEquivC W t.Ch t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) t.amb (t.word x) t.m2 (b τ x) (hY τ x) (rPsymF (R := D.R) t.Ch)) (hF : ∀ τ x j, (chF W t.sel (t.tup (tup τ)) (t.idx (tup τ)) (t.word x) j).Ok) (hE : ∀ x, (evGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch) (t.word x)).Ok) (ev : ∀ τ, (Fin (Df.nV τ) → t.X.K) →ₗ[t.X.K] V0X W t.Ch t.sel (t.tup (tup τ)) Xg (rPsymF (R := D.R) t.Ch)) (u : D.what₂.Word) (eJ : Bs.J ≃ Fin D.R.m) (Nc lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) Nc lam0 c0 ce Ch Sw C1), tup Bs.μ0 = D.what₂.mu0 → KerTies t W Del h0 → KerSizes t W Del h0 CY CT → C0 ≤ Ch → (∀ v : InfinitePlace t.X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun t.X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) (fun τ => t.idx_ok (tup τ)) hP D.what₂.Word t.word b hY (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK) hF ev) u (memQ (A := (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK)) (hF := hF) hE (x := u)) (colsIn W t.Ch hX t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.idx (tup Bs.μ0)) (t.idx_ok (tup Bs.μ0)) (t.word u)) (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) ∧ ∀ v, IsUnit ((MramH W t.Ch hX (t.word u)).X v).det := by
  first | exact @GlobalTheory.ColRows.rowsBody_of_kerTies | exact GlobalTheory.ColRows.rowsBody_of_kerTies | (intros; apply GlobalTheory.ColRows.rowsBody_of_kerTies <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsUOfColPins

section

@[expose] public section



section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder
namespace GlobalTheory.ColRows

theorem rowsU_of_colPins_alt : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) (W : Formalism.L2.Col.Wts T.ker.X T.ker.Pr.Word D.R) (Del h0 : ℕ), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → HEq K.c.W W → KerTies T.ker W Del h0 → KerSizes T.ker W Del h0 CY CT → DV.NprimeDef D L → D.NuFull → (∀ u, 0 < (D.div.Nu u).rank) → ∀ (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (cf : ConvFace P.A3.fam3.base3) (Cl CHl : ℝ) (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs K.c.face K.Sp Zsc) cf Cl CHl), Pk.Zs = P.Zs → ∀ (u : D.what₂.Word) (lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 c0 ce Ch Sw C1) (w : (K.c.face Pk.Zs).Mem) (e : (Fin ((K.c.face Pk.Zs).a w) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), HEq w u → C0 ≤ Ch → ∃ (ch : ColChain (K.c.face Pk.Zs) w) (Tc : ChainTie ch (K.c.memQ w)), FirstCols K.c.hE Tc ∧ ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ) (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding) (hn : HtNums (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) (D.mem u).A.T L.Nc lam0 c0 ce Ch Sw C1 H) (InfinitePlace D.what₂.LL)) (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn) (cb : CBData ch.X ch.Kj), (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧ (∀ v, IsUnit ((K.c.face Pk.Zs).Xc w v).det) ∧ 0 < (K.c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) := by
  intro CY CT hCT
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.memberRows_of_kernelDatum_sizes CY CT hCT
  refine ⟨C0, ?_⟩
  intro D L hT Gi Gl Kc Y cX ex _ T P K W Del h0 hPins hW hKT hKS hN hNu hrk Zsc cf Cl CHl Pk hZs u lam0 c0 ce Ch Sw C1 H w e hwu hCh
  have hmu0 : P.I.tup P.A3.fam3.base3.μ0 = D.what₂.mu0 := P.tied.div.tup.mu0
  have hpos : ∀ v : InfinitePlace D.what₂.LL, (((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding).PosDef :=
    fun v => Formalism.L2.DIV.BlockDat.HV_pos (ℓ := P.A3.fam3.F.lvl P.Ps P.ψs) K.ok1.ok2.conj (K.ok1.ok2.what₂ _) K.ok1.ok2.irr v
  have hlat : Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) :=
    nuLat_comap_isLattice D L hN u ⟨(hNu u).1, by
      intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli⟩ _ e
  have ha : 0 < (K.c.face Pk.Zs).a w := by
    have h := hrk u
    change 0 < Module.finrank D.what₂.LL (Submodule.span D.what₂.LL ((D.div.Nu u).L : Set (D.div.Nu u).V)) at h
    rw [(hNu u).2, finrank_top, ← e.finrank_eq, Module.finrank_fin_fun] at h
    exact h
  have hev := _root_.GlobalTheory.T.frames_tilde_gamma_values_alt D L hT Gi Gl Kc Y cX ex T P K hPins
  rw [← hZs] at hev
  clear hPins hrk hNu
  obtain ⟨X, e', c, Sp, colTie, kerTie, wTie, lvTie, sgTie, v0, TU, xiVal, trIv, famEq, gEq, plEq, i0Eq, tEq, muTie, ok1⟩ := K
  obtain ⟨toS, ker, crd, crd_gram, crd_lat, ker_sharp, ker_frm⟩ := T
  obtain ⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, kX, seam, seam_ok, kPr, pr_ok, g_rec, kCh, ksel, kS, kword, T_rec, ktup, Q_rec, kcst, kidx, km2, kglob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩ := ker
  obtain ⟨Pr, Rk, W', Ch', sel, Sg, hX, Lv, Xg, m2, Gc, mu, cst, Li, hL, hP, Mem, wd, b, hY, Am, hK, hF, hE, ev⟩ := c
  have hXe : kX = fieldsLL D X e' := kerTie.1
  subst hXe
  have hRk : Rk = D.R := kerTie.2.1
  subst hRk
  have hPr : Pr = kPr := eq_of_heq kerTie.2.2.1
  subst hPr
  have hChE : Ch' = kCh := eq_of_heq kerTie.2.2.2.1
  subst hChE
  have hsel : sel = ksel := eq_of_heq kerTie.2.2.2.2.1
  subst hsel
  have hSg : Sg = kS := eq_of_heq kerTie.2.2.2.2.2.1
  subst hSg
  have hmu : mu = fun t => ktup (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.1
  subst hmu
  have hcst : cst = fun t => kcst (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.2.1
  subst hcst
  have hLi : Li = fun t => kidx (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.2.2.1
  subst hLi
  have hm2 : m2 = km2 := kerTie.2.2.2.2.2.2.2.2.2.1
  subst hm2
  have hGc : Gc = kglob := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.1
  subst hGc
  have hAm : Am = Formalism.L2.Ker.ambOf seam B χ cD := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.2.1
  subst hAm
  have hMem : Mem = D.what₂.Word := kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1
  subst hMem
  have hwd : wd = kword := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.2.2.2
  subst hwd
  have hW' : W' = W := eq_of_heq hW
  subst hW'
  have hLv : Lv = Formalism.L2.Col.rPsymF (R := D.R) Ch' := lvTie
  subst hLv
  have hwu' : w = u := eq_of_heq hwu
  subst hwu'
  have hmuOne : ktup (P.I.tup P.A3.fam3.base3.μ0) = 1 := by rw [hmu0]; exact hKT.mu0
  have hev' := hev hmuOne
  dsimp only at hev'
  have key := hC0 D L hT Gi Gl Kc Y cX ex
    (⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, fieldsLL D X e', seam, seam_ok, Pr, pr_ok, g_rec, Ch',
      sel, Sg, wd, T_rec, ktup, Q_rec, kcst, kidx, m2, Gc, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th,
      unf, ent, ent_lam, kf, kf_un, served⟩ : Formalism.L2.Ker.KerEntTied ex) W' Del h0 hX P.A3.fam3.base3
    (P.A3.side3 P.Ps P.ψs Pk.Zs) Xg P.I.tup hP b hY hK hF hE (ev Pk.Zs) w (Equiv.refl _) L.Nc lam0 c0 ce Ch Sw C1 H hmu0
    hKT hKS hCh hpos hev'
  dsimp only at key ha hlat ⊢
  obtain ⟨⟨ch, Tc, h1, X0, hX0, hn, hop, cb, hcb⟩, hXc⟩ := key
  exact ⟨ch, Tc, h1, X0, hX0, hn, hop, cb, hcb, hXc, ha, hlat⟩
end GlobalTheory.ColRows
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsUOfColPinsStatement

section

@[expose] public section



section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows

theorem _root_.GlobalTheory.T.kernel_columns_from_ties_alt : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) (W : Formalism.L2.Col.Wts T.ker.X T.ker.Pr.Word D.R) (Del h0 : ℕ), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → HEq K.c.W W → KerTies T.ker W Del h0 → KerSizes T.ker W Del h0 CY CT → DV.NprimeDef D L → D.NuFull → (∀ u, 0 < (D.div.Nu u).rank) → ∀ (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (cf : ConvFace P.A3.fam3.base3) (Cl CHl : ℝ) (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs K.c.face K.Sp Zsc) cf Cl CHl), Pk.Zs = P.Zs → ∀ (u : D.what₂.Word) (lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 c0 ce Ch Sw C1) (w : (K.c.face Pk.Zs).Mem) (e : (Fin ((K.c.face Pk.Zs).a w) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), HEq w u → C0 ≤ Ch → ∃ (ch : ColChain (K.c.face Pk.Zs) w) (Tc : ChainTie ch (K.c.memQ w)), FirstCols K.c.hE Tc ∧ ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ) (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding) (hn : HtNums (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) (D.mem u).A.T L.Nc lam0 c0 ce Ch Sw C1 H) (InfinitePlace D.what₂.LL)) (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn) (cb : CBData ch.X ch.Kj), (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧ (∀ v, IsUnit ((K.c.face Pk.Zs).Xc w v).det) ∧ 0 < (K.c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) := by
  first | exact @_root_.GlobalTheory.ColRows.rowsU_of_colPins_alt | exact _root_.GlobalTheory.ColRows.rowsU_of_colPins_alt | (intros; apply _root_.GlobalTheory.ColRows.rowsU_of_colPins_alt <;> assumption)
end
end
end
