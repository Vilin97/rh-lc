module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Mathlib.RingTheory.Coalgebra.CoassocSimps

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatLocHomRe

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem datLoc_homRe : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (M : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin b' → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a' b' → ℂ), HEq N M → HEq N' M' → DatLoc D cc SS cl M M' Ξ → DatLoc D cc SS cl N N' (fun z => Ξ (homRe ha hb z)) := by
  intro D cc SS cl a b a' b' ha hb N N' M M' Ξ hN hN' h
  subst ha hb
  cases eq_of_heq hN
  cases eq_of_heq hN'
  have hx : (fun z => Ξ (homRe rfl rfl z)) = Ξ := by
    funext z
    congr 1
  rw [hx]
  exact h

end GlobalTheory.TwU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedPairDatumEqAdelicDatum

section

@[expose] public section

noncomputable section

namespace GlobalTheory.TwV

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem inFr_symm_inFr_cancel {E : Type} [Field E] {a b : ℕ} (g : Formalism.L2.Col.Sp E a ≃ₗ[E] Formalism.L2.Col.Sp E a)
    (g' : Formalism.L2.Col.Sp E b ≃ₗ[E] Formalism.L2.Col.Sp E b) (z : Formalism.L2.Col.HomE E a b) :
    Formalism.L2.Col.inFr g.symm g'.symm (Formalism.L2.Col.inFr g g' z) = z := by
  refine LinearMap.ext fun x => ?_
  simp [Formalism.L2.Col.inFr]



theorem moved_pair_datum_eq_adelic_datum_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (Xi : AdDatum J.St) j (hj : j + 1 ≤ D.R.m) (h1 : ((sysS H X std).Pj j).m + 1 = D.R.N j) (h2 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, xiM (sysS H X std) (J.fd std) (J.xi0 std Xi) j La La' z = Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J Xi j hj h1 h2 La La' z
  unfold GlobalTheory.TwU.xiM Formalism.L2.PairingIndexBounds.F.movD Joint.xi0
  rw [dite_eq_left ⟨hj, h1, h2⟩, inFr_symm_inFr_cancel]

end GlobalTheory.TwV

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedPairDatumEqAdelicDatumStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.moved_pair_datum_eq_adelic_datum : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ (Xi : AdDatum J.St) j (hj : j + 1 ≤ D.R.m) (h1 : ((sysS H X std).Pj j).m + 1 = D.R.N j) (h2 : ((sysS H X std).Pj (j + 1)).m + 1 = D.R.N (j + 1)) (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)) z, xiM (sysS H X std) (J.fd std) (J.xi0 std Xi) j La La' z = Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La) (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
  first | exact @GlobalTheory.TwV.moved_pair_datum_eq_adelic_datum_alt | exact GlobalTheory.TwV.moved_pair_datum_eq_adelic_datum_alt | (intros; apply GlobalTheory.TwV.moved_pair_datum_eq_adelic_datum_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedPairDatumDependsOnlyOnLevel

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar


namespace GlobalTheory.TwU

theorem xiM_datLoc : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J S hD j hjm La La' hLa hLa'
  have hm : (sysS H X std).mm = D.R.m := by
    first | rfl | exact X.fl_m
  have hj : j + 1 ≤ D.R.m := by omega
  obtain ⟨⟨h1, -⟩, -, hK1, -⟩ := hD j (Nat.le_of_succ_le hj) La hLa
  obtain ⟨⟨h2, -⟩, -, hK2, -⟩ := hD (j + 1) hj La' hLa'
  have hx : xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = fun z =>
      S.Xi j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
        (J.pt std (j + 1) hj La') (homRe h1 h2 z) := by
    funext z
    exact GlobalTheory.T.moved_pair_datum_eq_adelic_datum t std J S.Xi j hj h1 h2 La La' z
  rw [hx]
  exact datLoc_homRe D t.cc (ssRec t u μ) (t.rd u μ).lev h1 h2 _ _ _ _ _ hK1 hK2
    (S.law.loc j hj (J.chart std j (Nat.le_of_succ_le hj) La) (J.chart std (j + 1) hj La') (J.pt std j (Nat.le_of_succ_le hj) La)
      (J.pt std (j + 1) hj La'))

end GlobalTheory.TwU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedPairDatumDependsOnlyOnReaderLevelStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.movedPairDatum_congr : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X) (S : J.At std), J.Dict std → ∀ j < (sysS H X std).mm, ∀ (La : (sysS H X std).Lt j) (La' : (sysS H X std).Lt (j + 1)), ((sysS H X std).Pj j).IsLatTup La.2 → ((sysS H X std).Pj (j + 1)).IsLatTup La'.2 → DatLoc D t.cc (ssRec t u μ) (t.rd u μ).lev ((J.fd std).kerN j La) ((J.fd std).kerN (j + 1) La') (xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La') := by
  first | exact @GlobalTheory.TwU.xiM_datLoc | exact GlobalTheory.TwU.xiM_datLoc | (intros; apply GlobalTheory.TwU.xiM_datLoc <;> assumption)
end
end
