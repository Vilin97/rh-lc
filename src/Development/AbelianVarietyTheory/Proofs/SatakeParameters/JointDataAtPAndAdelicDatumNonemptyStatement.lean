module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicDatumWithLawsAtJoint
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
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SigWSubPowDvd
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdelicDatumWithLawsAtJointStatement

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_adelicDatum_with_laws_at_joint : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∃ Xi muT, AdLawAt J.A J.dtU J.a Xi muT := by
  first | exact @GlobalTheory.TwV.exists_adLawAt_joint | exact GlobalTheory.TwV.exists_adLawAt_joint | (intros; apply GlobalTheory.TwV.exists_adLawAt_joint <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldEmbMemAlgebraicClosure

section

@[expose] public section

namespace GlobalTheory

open IntermediateField

theorem numberField_emb_mem_algebraicClosure {LL : Type} [Field LL] [NumberField LL]
    (e : LL →+* ℂ) (z : LL) : e z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  have hz : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
  simpa using hz.algHom e.toRatAlgHom

theorem padic_emb_extends_algebraicClosure (p : ℕ) [Fact p.Prime] (LL : Type) [Field LL]
    [NumberField LL] (e : LL →+* ℂ) (i : LL →+* ℂ_[p]) :
    ∃ lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p],
      ∀ (z : LL) (hz : e z ∈ algebraicClosure ℚ ℂ), i z = lam ⟨e z, hz⟩ := by
  let e' : LL →+* algebraicClosure ℚ ℂ :=
    (e.codRestrict (algebraicClosure ℚ ℂ).toSubring
      (fun z => numberField_emb_mem_algebraicClosure e z))
  letI : Algebra LL (algebraicClosure ℚ ℂ) := e'.toAlgebra
  letI : Algebra LL ℂ_[p] := i.toAlgebra
  haveI : IsScalarTower ℚ LL (algebraicClosure ℚ ℂ) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (RingHom.congr_fun (Subsingleton.elim ((algebraMap LL (algebraicClosure ℚ ℂ)).comp
        (algebraMap ℚ LL)) (algebraMap ℚ (algebraicClosure ℚ ℂ))) x).symm)
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic LL (algebraicClosure ℚ ℂ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) LL
  let lamA : algebraicClosure ℚ ℂ →ₐ[LL] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨lamA.toRingHom, fun z hz => ?_⟩
  have h1 : (⟨e z, hz⟩ : algebraicClosure ℚ ℂ) = algebraMap LL (algebraicClosure ℚ ℂ) z := rfl
  rw [h1]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCEmbCLam

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV



theorem exists_cEmbC_lam : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∃ (E : CEmbC (sysS H X std).G) (lam : TaylorLogMetric.Qbar →+* ℂ_[D.what₂.places.resChar w]), ∀ (z : D.what₂.LL) (hz : D.what₂.embLL z ∈ algebraicClosure ℚ ℂ), E.iK (ex.cmp.embW u w hg z) = lam ⟨D.what₂.embLL z, hz⟩ := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  have hV : 0 < (sysS H X std).G.P.nV := (Gl.vOf u w hg 0).pos
  obtain ⟨E⟩ := GlobalTheory.TwU.nonempty_cEmbC _ (sysS H X std).G hV
  obtain ⟨lam, hlam⟩ := GlobalTheory.padic_emb_extends_algebraicClosure (D.what₂.places.resChar w) D.what₂.LL D.what₂.embLL
    (E.iK.comp (ex.cmp.embW u w hg))
  exact ⟨E, lam, fun z hz => hlam z hz⟩

end GlobalTheory.TwV
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinsetRepsOfCls

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.TwV.exists_finset_reps_of_cls {T Γ C : Type} [Finite C] (P : T → Prop) (sm : Γ → T → T) (cls : T → C)
    (h : ∀ L L', P L → P L' → cls L = cls L' → ∃ γ, L' = sm γ L) :
    ∃ R : Finset T, (∀ L ∈ R, P L) ∧ ∀ L, P L → ∃ L₀ ∈ R, ∃ γ : Γ, L = sm γ L₀ := by
  classical
  let S : Set C := {x | ∃ L, P L ∧ cls L = x}
  have hS : ∀ x : S, ∃ L, P L ∧ cls L = x.1 := fun x => x.2
  choose f hf using hS
  haveI : Fintype S := Fintype.ofFinite S
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro L hL
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hL
    exact (hf x).1
  · intro L hL
    let x : S := ⟨cls L, L, hL, rfl⟩
    exact ⟨f x, Finset.mem_image_of_mem f (Finset.mem_univ x), h (f x) L (hf x).1 hL (hf x).2⟩



theorem GlobalTheory.TwV.finClasses_sysS : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), ∀ j c, ((sysS H X std).Lv.lev j c).FinClasses := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J j c
  change (Lv.lev j c).FinClasses
  by_cases hj : j ≤ D.R.m
  · exact GlobalTheory.TwV.exists_finset_reps_of_cls (C := (D.chTw u μ).cls j) _ (Lv.lev j c).smul ((labAt X H).cls j c)
      (fun L L' hL hL' e => (((labAt X H).cls_iff j hj c c L L' hL hL').1 e).2)
  · exact (J.empty j (by omega)).elim c
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinStabSite

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV



theorem finStab_site : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), FinStab (sysS H X std).Lv := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  show FinStab Lv
  intro j c La hLa
  by_cases hj : j ≤ D.R.m
  · exact Nat.finite_of_card_ne_zero ((labAt X H).stab_dvd j hj c La hLa).1.ne'
  · exact (J.empty j (by omega)).elim c

end GlobalTheory.TwV
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointDataAtPAndAdelicDatumNonempty

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

namespace GlobalTheory.TwV



theorem joint_at_nonempty : Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), Nonempty (J.At std) := by
  intro hC D L hT Gi Gl Kc Dx cX ex t u μ w hg Lv I H X _ std J
  obtain ⟨E, lam, hK⟩ := GlobalTheory.TwV.exists_cEmbC_lam t std J
  have hin := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  obtain ⟨g, hLT, curve⟩ := hC D t.cc t.δ t.B t.χ t.cc_ok t.δ_ok t.χ_ok (D.what₂.places.resChar w) J.cop hin.1 hin.2.1 lam
  obtain ⟨Xi, muT, law⟩ := GlobalTheory.T.exists_adelicDatum_with_laws_at_joint t std J
  exact ⟨{ E := E, lam := lam, hK := hK, g := g, hLT := hLT, curve := curve, hfin := GlobalTheory.TwV.finClasses_sysS t std J, hst := GlobalTheory.TwV.finStab_site t std J, Xi := Xi, muT := muT, law := law }⟩

end GlobalTheory.TwV
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointDataAtPAndAdelicDatumNonemptyStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.KerInert GlobalTheory.TwV

theorem _root_.GlobalTheory.T.jointData_at_p_and_adelicDatum_nonempty : Lt.CurveEx → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl} {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X), Nonempty (J.At std) := by
  first | exact @GlobalTheory.TwV.joint_at_nonempty | exact GlobalTheory.TwV.joint_at_nonempty | (intros; apply GlobalTheory.TwV.joint_at_nonempty <;> assumption)
end
end
